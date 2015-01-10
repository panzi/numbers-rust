#![feature(box_syntax)]

extern crate collections;
extern crate core;

use std::os;
use std::hash::Hash;
use std::sync::mpsc::{channel, Sender};
use std::usize;
use std::fmt::Formatter;
use std::thread::Thread;
use core::fmt::String;
use std::num::Float;

use std::collections::HashSet;
use std::hash::{Writer, Hasher};

use self::Op::*;

static HAS_ROOM: usize = 1 << 0;
static ADD_A_B:  usize = 1 << 1;
static ADD_B_A:  usize = 1 << 2;
static SUB_A_B:  usize = 1 << 3;
static SUB_B_A:  usize = 1 << 4;
static MUL_A_B:  usize = 1 << 5;
static MUL_B_A:  usize = 1 << 6;
static DIV_A_B:  usize = 1 << 7;
static DIV_B_A:  usize = 1 << 8;

enum Op {
	Add(*const Expr,*const Expr),
	Sub(*const Expr,*const Expr),
	Mul(*const Expr,*const Expr),
	Div(*const Expr,*const Expr),
	Val(usize)
}

struct Expr {
	op: Op,
	value: usize,
	used: u64
}

struct Solver {
	exprs: Box<Vec<Box<Expr>>>
}

unsafe impl Send for *const Expr {}

impl Expr {
	fn precedence(&self) -> usize {
		match self.op {
			Add(_,_) => 0,
			Sub(_,_) => 1,
			Mul(_,_) => 3,
			Div(_,_) => 2,
			Val(_)   => 4
		}
	}
}

impl<S: Writer + Hasher> Hash<S> for Expr {
	#[inline]
	fn hash(&self, state: &mut S) {
		match self.op {
			Add(left, right) => unsafe {
				('+' as u8).hash(state);
				(*left).hash(state);
				(*right).hash(state);
			},
			Sub(left, right) => unsafe {
				('-' as u8).hash(state);
				(*left).hash(state);
				(*right).hash(state);
			},
			Mul(left, right) => unsafe {
				('*' as u8).hash(state);
				(*left).hash(state);
				(*right).hash(state);
			},
			Div(left, right) => unsafe {
				('/' as u8).hash(state);
				(*left).hash(state);
				(*right).hash(state);
			},
			Val(_) => {
				('#' as u8).hash(state);
				self.value.hash(state);
			}
		}
	}
}

impl PartialEq for Expr {
	fn eq(&self, other: &Expr) -> bool {
		match self.op {
			Add(left, right) => match other.op {
				Add(oleft, oright) => unsafe { *left == *oleft && *right == *oright },
				_ => false
			},
			Sub(left, right) => match other.op {
				Sub(oleft, oright) => unsafe { *left == *oleft && *right == *oright },
				_ => false
			},
			Mul(left, right) => match other.op {
				Mul(oleft, oright) => unsafe { *left == *oleft && *right == *oright },
				_ => false
			},
			Div(left, right) => match other.op {
				Div(oleft, oright) => unsafe { *left == *oleft && *right == *oright },
				_ => false
			},
			Val(_) => match other.op {
				Val(_) => self.value == other.value,
				_ => false
			}
		}
	}
}

impl Eq for Expr {}

macro_rules! fmt_expr {
	($f:expr, $expr:expr, $op:expr, $left:expr, $right:expr) => ({
		let p = $expr.precedence();
		let lp = ($left).precedence();
		let rp = ($right).precedence();

		if p > lp {
			if p > rp {
				write!($f, "({}) {} ({})", $left, $op, $right)
			}
			else {
				write!($f, "({}) {} {}", $left, $op, $right)
			}
		}
		else {
			if p > rp {
				write!($f, "{} {} ({})", $left, $op, $right)
			}
			else {
				write!($f, "{} {} {}", $left, $op, $right)
			}
		}
	})
}

impl core::fmt::String for Expr {
	fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
		match self.op {
			Add(left, right) => unsafe {
				fmt_expr!(f, self, '+', *left, *right)
			},
			Sub(left, right) => unsafe {
				fmt_expr!(f, self, '-', *left, *right)
			},
			Mul(left, right) => unsafe {
				fmt_expr!(f, self, '*', *left, *right)
			},
			Div(left, right) => unsafe {
				fmt_expr!(f, self, '/', *left, *right)
			},
			Val(_) => {
				write!(f, "{}", self.value)
			}
		}
	}
}

impl Solver {
	#[inline]
	fn new() -> Solver {
		Solver { exprs: box Vec::new() }
	}

	#[inline]
	fn expr(&mut self, op: Op, value: usize, used: u64) -> *const Expr {
		let expr = box Expr { op: op, value: value, used: used };
		let ptr: *const Expr = &*expr;
		self.exprs.push(expr);
		return ptr;
	}

	#[inline]
	fn val(&mut self, value: usize, index: usize) -> *const Expr {
		self.expr(Val(index), value, 1u64 << index)
	}

	#[inline]
	unsafe fn add(&mut self, left: *const Expr, right: *const Expr) -> *const Expr {
		let used = (*left).used | (*right).used;
		let value = (*left).value + (*right).value;
		self.expr(Add(left, right), value, used)
	}

	#[inline]
	unsafe fn sub(&mut self, left: *const Expr, right: *const Expr) -> *const Expr {
		let used = (*left).used | (*right).used;
		let value = (*left).value - (*right).value;
		self.expr(Sub(left, right), value, used)
	}

	#[inline]
	unsafe fn mul(&mut self, left: *const Expr, right: *const Expr) -> *const Expr {
		let used = (*left).used | (*right).used;
		let value = (*left).value * (*right).value;
		self.expr(Mul(left, right), value, used)
	}

	#[inline]
	unsafe fn div(&mut self, left: *const Expr, right: *const Expr) -> *const Expr {
		let used = (*left).used | (*right).used;
		let value = (*left).value / (*right).value;
		self.expr(Div(left, right), value, used)
	}
	
	unsafe fn make<F: FnMut(*const Expr)>(&mut self, what: usize, a: *const Expr, b: *const Expr, mut f: F) {
		if (what & ADD_A_B) != 0 {
			f(self.add(a,b));
		}
		else if (what & ADD_B_A) != 0 {
			f(self.add(a,b));
		}

		if (what & MUL_A_B) != 0 {
			f(self.mul(a,b));
		}
		else if (what & MUL_B_A) != 0 {
			f(self.mul(b,a));
		}

		if (what & SUB_A_B) != 0 {
			f(self.sub(a,b));
		}
		else if (what & SUB_B_A) != 0 {
			f(self.sub(b,a));
		}

		if (what & DIV_A_B) != 0 {
			f(self.div(a,b));
		}
		else if (what & DIV_B_A) != 0 {
			f(self.div(b,a));
		}
	}
}

unsafe fn make(a: *const Expr, b: *const Expr) -> usize {
	let mut what = 0;

	if is_normalized_add(a,b) {
		what = ADD_A_B;
	}
	else if is_normalized_add(b,a) {
		what = ADD_B_A;
	}

	if (*a).value != 1 && (*b).value != 1 {
		if is_normalized_mul(a,b) {
			what |= MUL_A_B;
		}
		else if is_normalized_mul(b,a) {
			what |= MUL_B_A;
		}
	}

	if (*a).value > (*b).value {
		if is_normalized_sub(a,b) {
			what |= SUB_A_B;
		}

		if (*b).value != 1 && ((*a).value % (*b).value) == 0 && is_normalized_div(a,b) {
			what |= DIV_A_B;
		}
	}
	else if (*b).value > (*a).value {
		if is_normalized_sub(b,a) {
			what |= SUB_B_A;
		}

		if (*a).value != 1 && ((*b).value % (*a).value) == 0 && is_normalized_div(b,a) {
			what |= DIV_B_A;
		}
	}
	else if (*b).value != 1 {
		if is_normalized_div(a,b) {
			what |= DIV_A_B;
		}
		else if is_normalized_div(b,a) {
			what |= DIV_B_A;
		}
	}

	return what;
}

unsafe fn is_normalized_add(left: *const Expr, right: *const Expr) -> bool {
	match (*right).op {
		Add(_,_) | Sub(_,_) => return false,
		_ => {
			match (*left).op {
				Add(_,lright) => return (*lright).value <= (*right).value,
				Sub(_,_) => return false,
				_ => return (*left).value <= (*right).value
			}
		}
	}
}

unsafe fn is_normalized_sub(left: *const Expr, right: *const Expr) -> bool {
	match (*right).op {
		Add(_,_) | Sub(_,_) => return false,
		_ => {
			match (*left).op {
				Sub(_,lright) => return (*lright).value <= (*right).value,
				_ => return true
			}
		}
	}
}

unsafe fn is_normalized_mul(left: *const Expr, right: *const Expr) -> bool {
	match (*right).op {
		Mul(_,_) | Div(_,_) => return false,
		_ => {
			match (*left).op {
				Mul(_,lright) => return (*lright).value <= (*right).value,
				Div(_,_) => return false,
				_ => return (*left).value <= (*right).value
			}
		}
	}
}

unsafe fn is_normalized_div(left: *const Expr, right: *const Expr) -> bool {
	match (*right).op {
		Mul(_,_) | Div(_,_) => return false,
		_ => {
			match (*left).op {
				Div(_,lright) => return (*lright).value <= (*right).value,
				_ => return true
			}
		}
	}
}

fn solutions<F: FnMut(&Expr)>(tasks: u32, target: usize, numbers: Box<Vec<usize>>, mut f: F) {
	struct Helper {
		exprs: Box<Vec<*const Expr>>
	}

	unsafe impl Send for *const Helper {}

	let numcnt = numbers.len();
	let full_usage = !(!0u64 << numcnt);
	let mut solver = Solver::new();
	let mut h = Helper { exprs: box Vec::new() };
	let mut uniq_solutions = HashSet::new();

	unsafe {
		for (i, numref) in numbers.iter().enumerate() {
			let num = *numref;
			let expr = solver.val(num,i);
			let ptr: *const Expr = &*expr;
			h.exprs.push(ptr);
		}

		for expr in h.exprs.iter() {
			if (**expr).value == target {
				f(&**expr);
				break;
			}
		}

		let mut lower = 0;
		let mut upper = numcnt;
		let (chan, port) = channel();

		while lower < upper {
			let mut workers = 0us;
			let mut new_exprs = Vec::new();
			let x0 = lower;
			let xn = upper;
			let mut x_last = x0;
			let mut i = 1us;
			let x0_sq = x0*x0;
			let area = (xn*xn - x0_sq) as f64 / tasks as f64;

			{
				let unsafe_h: *const Helper = &h;

				while x_last < xn || workers == 0 {
					let xi = (i as f64 * area + x0_sq as f64).sqrt().round() as usize;
					let xi = if xi > xn { xn } else { xi };

					if xi > x_last {
						let xim1 = x_last;
						let chan_clone = chan.clone();

						Thread::spawn(move || work(xim1, xi, &*(*unsafe_h).exprs, full_usage, &chan_clone));

						x_last = xi;
						workers += 1;
					}

					i += 1;
				}

				while workers > 0 {
					let pair = port.recv().unwrap();
					match pair {
						None => workers -= 1,
						Some((flags, aexpr, bexpr)) => {
							solver.make(flags, aexpr, bexpr, |&mut: expr| {
								if (*expr).value == target {
									if uniq_solutions.insert(&*expr) {
										f(&*expr);
									}
								}
								else if (flags & HAS_ROOM) != 0 {
									new_exprs.push(expr);
								}
							});
						}
					}
				}
			}

			for expr in new_exprs.iter() {
				h.exprs.push(*expr);
			}

			lower = upper;
			upper = h.exprs.len();
		}
	}
}

fn work (lower: usize, upper: usize, exprs: &Vec<*const Expr>, full_usage: u64, chan: &Sender<Option<(usize,*const Expr,*const Expr)>>) {
	for b in range(lower,upper) {
		let bexpr = *exprs.get(b).unwrap();

		for a in range(0,b) {
			unsafe {
				let aexpr = *exprs.get(a).unwrap();

				if ((*aexpr).used & (*bexpr).used) == 0 {
					let mut flags = make(aexpr,bexpr);
					if flags != 0 {
						if ((*aexpr).used | (*bexpr).used) != full_usage {
							flags |= HAS_ROOM;
						}
						chan.send(Some((flags, aexpr, bexpr)));
					}
				}
			}
		}
	}
	chan.send(None);
}

fn main () {
	let args = os::args();
	if args.len() < 4 {
		panic!("not enough arguments");
	}
	let tasks:u32 = args.get(1).unwrap().parse().expect("number of tasks is not a number or out of range");
	let target:usize = args.get(2).unwrap().parse().expect("target is not a number or out of range");
	let mut numbers: Vec<usize> = args.slice(3,args.len()).iter().map(|arg| {
		let num:usize = (*arg).parse().expect(format!("argument is not a number or out of range: {}",*arg).as_slice());
		if num == 0 { panic!(format!("illegal argument value: {}",*arg)); }
		num
	}).collect();
	if tasks == 0 {
		panic!("number of tasks has to be >= 1");
	}
	if numbers.len() > usize::BITS {
		panic!("only up to {} numbers supported", usize::BITS);
	}
	numbers.sort();

	println!("target  = {}", target);
	println!("numbers = {}", numbers.iter().map(|v| { v.to_string() }).collect::<Vec<_>>().connect(", "));

	println!("solutions:");
	let mut i = 1us;
	solutions(tasks, target, box numbers, |&mut: expr| {
		println!("{:3}: {}", i, expr);
		i += 1;
	});
}
