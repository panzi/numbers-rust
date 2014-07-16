#![feature(macro_rules)]
#![feature(default_type_params)]

extern crate collections;

use std::os;
use std::hash::Hash;
use std::comm::{channel, Sender};
use std::uint;
use std::fmt::{Show, Formatter};

use std::collections::hashmap::HashSet;
use std::hash::Writer;

static HAS_ROOM: uint = 1 << 0;
static ADD_A_B:  uint = 1 << 1;
static ADD_B_A:  uint = 1 << 2;
static SUB_A_B:  uint = 1 << 3;
static SUB_B_A:  uint = 1 << 4;
static MUL_A_B:  uint = 1 << 5;
static MUL_B_A:  uint = 1 << 6;
static DIV_A_B:  uint = 1 << 7;
static DIV_B_A:  uint = 1 << 8;

enum Op {
	Add(*const Expr,*const Expr),
	Sub(*const Expr,*const Expr),
	Mul(*const Expr,*const Expr),
	Div(*const Expr,*const Expr),
	Val(uint)
}

struct Expr {
	op: Op,
	value: uint,
	used: u64
}

struct Solver {
	exprs: Box<Vec<Box<Expr>>>
}

impl Expr {
	fn precedence(&self) -> uint {
		match self.op {
			Add(_,_) => 0,
			Sub(_,_) => 1,
			Mul(_,_) => 3,
			Div(_,_) => 2,
			Val(_)   => 4
		}
	}
}

impl<S: Writer> Hash<S> for Expr {
	#[inline]
	fn hash(&self, state: &mut S) {
		match self.op {
			Add(left, right) => unsafe {
				state.write(['+' as u8]);
				(*left).hash(state);
				(*right).hash(state);
			},
			Sub(left, right) => unsafe {
				state.write(['-' as u8]);
				(*left).hash(state);
				(*right).hash(state);
			},
			Mul(left, right) => unsafe {
				state.write(['*' as u8]);
				(*left).hash(state);
				(*right).hash(state);
			},
			Div(left, right) => unsafe {
				state.write(['/' as u8]);
				(*left).hash(state);
				(*right).hash(state);
			},
			Val(_) => {
				state.write(['#' as u8]);
				state.write(unsafe { std::mem::transmute::<uint,[u8, ..uint::BYTES]>(self.value) });
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

macro_rules! fmt_expr(
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
)

impl Show for Expr {
	fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
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
	fn expr(&mut self, op: Op, value: uint, used: u64) -> *const Expr {
		let expr = box Expr { op: op, value: value, used: used };
		let ptr: *const Expr = &*expr;
		self.exprs.push(expr);
		return ptr;
	}

	#[inline]
	fn val(&mut self, value: uint, index: uint) -> *const Expr {
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
	
	unsafe fn make(&mut self, what: uint, a: *const Expr, b: *const Expr, f: |*const Expr|) {
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

unsafe fn make(a: *const Expr, b: *const Expr) -> uint {
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

fn solutions(tasks: u32, target: uint, mut numbers: Box<Vec<uint>>, f: |&Expr|) {
	struct Helper {
		exprs: Box<Vec<*const Expr>>
	}

	let numcnt = numbers.len();
	let full_usage = !(!0u64 << numcnt);
	let mut solver = Solver::new();
	let mut h = Helper { exprs: box Vec::new() };
	let mut uniq_solutions = HashSet::new();
	numbers.sort();

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
			let mut workers = 0u;
			let mut new_exprs = Vec::new();
			let x0 = lower;
			let xn = upper;
			let mut x_last = x0;
			let mut i = 1u;
			let x0_sq = x0*x0;
			let area = (xn*xn - x0_sq) as f64 / tasks as f64;

			{
				let unsafe_h: *const Helper = &h;

				while x_last < xn || workers == 0 {
					let xi = (i as f64 * area + x0_sq as f64).sqrt().round() as uint;
					let xi = if xi > xn { xn } else { xi };

					if xi > x_last {
						let xim1 = x_last;
						let chan_clone = chan.clone();

						spawn(proc() work(xim1, xi, (*unsafe_h).exprs, full_usage, &chan_clone));

						x_last = xi;
						workers += 1;
					}

					i += 1;
				}

				while workers > 0 {
					let pair = port.recv();
					match pair {
						None => workers -= 1,
						Some((flags, aexpr, bexpr)) => {
							solver.make(flags, aexpr, bexpr, |expr| {
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

fn work (lower: uint, upper: uint, exprs: &Vec<*const Expr>, full_usage: u64, chan: &Sender<Option<(uint,*const Expr,*const Expr)>>) {
	for b in range(lower,upper) {
		let bexpr = *exprs.get(b);

		for a in range(0,b) {
			unsafe {
				let aexpr = *exprs.get(a);

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
		fail!("not enough arguments");
	}
	let tasks:u32 = from_str(args.get(1).as_slice()).expect("number of tasks is not a number or out of range");
	let target:uint = from_str(args.get(2).as_slice()).expect("target is not a number or out of range");
	let mut numbers: Vec<uint> = args.slice(3,args.len()).iter().map(|arg| {
		let num:uint = from_str((*arg).as_slice()).expect(format!("argument is not a number or out of range: {}",*arg).as_slice());
		if num == 0 { fail!(format!("illegal argument value: {}",*arg)); }
		num
	}).collect();
	if tasks == 0 {
		fail!("number of tasks has to be >= 1");
	}
	if numbers.len() > uint::BITS {
		fail!("only up to {} numbers supported", uint::BITS);
	}
	numbers.sort();

	println!("target  = {}", target);
	println!("numbers = {}", numbers);

	println!("solutions:");
	let mut i = 1u;
	solutions(tasks, target, box numbers, |expr| {
		println!("{:3u}: {}", i, expr);
		i += 1;
	});
}
