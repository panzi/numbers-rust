extern mod extra;

use std::{uint,os};
use std::hashmap::HashSet;
use std::num::sqrt;
use std::task::spawn_with;
use std::comm::SharedChan;
use extra::sort::quick_sort3;

macro_rules! send(
	($($arg:expr),*) => (if !f($($arg),*) { return false; })
)

enum Op {
	Add(*Expr,*Expr),
	Sub(*Expr,*Expr),
	Mul(*Expr,*Expr),
	Div(*Expr,*Expr),
	Val(uint)
}

struct Expr {
	priv op: Op,
	priv value: uint,
	priv used: u64
}

struct NumericHashedExpr {
	priv expr: *Expr
}

struct Solver {
	priv exprs: ~[~Expr]
}

macro_rules! bin_numeric_iter_bytes(
	($op:expr) => (unsafe {
		$op.iter_bytes(             lsb0, |buf| { f(buf) }) &&
		(*left).numeric_iter_bytes( lsb0, |buf| { f(buf) }) &&
		(*right).numeric_iter_bytes(lsb0, |buf| { f(buf) })
	})
)

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
	
	fn to_str_under(&self,precedence: uint) -> ~str {
//		match self.op {
//			Val(_) => self.value.to_str(),
//			_      => fmt!("(%s)", self.to_str())
//		}
		if (precedence > self.precedence()) {
			return fmt!("(%s)", self.to_str());
		}
		else {
			return self.to_str();
		}
	}

	fn numeric_iter_bytes(&self, lsb0: bool, f: std::to_bytes::Cb) -> bool {
		match self.op {
			Add(left, right) => bin_numeric_iter_bytes!('+'),
			Sub(left, right) => bin_numeric_iter_bytes!('-'),
			Mul(left, right) => bin_numeric_iter_bytes!('*'),
			Div(left, right) => bin_numeric_iter_bytes!('/'),
			Val(_)           => self.value.iter_bytes(lsb0,f)
		}
	}
	
	fn numeric_eq(&self, other: &Expr) -> bool {
		match self.op {
			Add(left, right) => match other.op {
				Add(oleft, oright) => unsafe { (*left).numeric_eq(&*oleft) && (*right).numeric_eq(&*oright) },
				_ => false
			},
			Sub(left, right) => match other.op {
				Sub(oleft, oright) => unsafe { (*left).numeric_eq(&*oleft) && (*right).numeric_eq(&*oright) },
				_ => false
			},
			Mul(left, right) => match other.op {
				Mul(oleft, oright) => unsafe { (*left).numeric_eq(&*oleft) && (*right).numeric_eq(&*oright) },
				_ => false
			},
			Div(left, right) => match other.op {
				Div(oleft, oright) => unsafe { (*left).numeric_eq(&*oleft) && (*right).numeric_eq(&*oright) },
				_ => false
			},
			Val(_) => match other.op {
				Val(_) => self.value == other.value,
				_ => false
			}
		}
	}
}

macro_rules! bin_iter_bytes(
	($op:expr) => (unsafe {
		$op.iter_bytes(     lsb0, |buf| { f(buf) }) &&
		(*left).iter_bytes( lsb0, |buf| { f(buf) }) &&
		(*right).iter_bytes(lsb0, |buf| { f(buf) })
	})
)

impl IterBytes for Expr {
	fn iter_bytes(&self, lsb0: bool, f: std::to_bytes::Cb) -> bool {
		match self.op {
			Add(left, right) => bin_iter_bytes!('+'),
			Sub(left, right) => bin_iter_bytes!('-'),
			Mul(left, right) => bin_iter_bytes!('*'),
			Div(left, right) => bin_iter_bytes!('/'),
			Val(index)       => index.iter_bytes(lsb0,f)
		}
	}
}

impl IterBytes for NumericHashedExpr {
	fn iter_bytes(&self, lsb0: bool, f: std::to_bytes::Cb) -> bool {
		unsafe { (*(self.expr)).numeric_iter_bytes(lsb0,f) }
	}
}

impl Eq for Expr {
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
			Val(index) => match other.op {
				Val(oindex) => index == oindex,
				_ => false
			}
		}
	}
}

impl Eq for NumericHashedExpr {
	fn eq(&self, other: &NumericHashedExpr) -> bool {
		unsafe { (*(self.expr)).numeric_eq(&*other.expr) }
	}
}

impl ToStr for Expr {
	fn to_str(&self) -> ~str {
		let p = self.precedence();
		match self.op {
			Add(left, right) => unsafe { fmt!("%s + %s", (*left).to_str_under(p), (*right).to_str_under(p)) },
			Sub(left, right) => unsafe { fmt!("%s - %s", (*left).to_str_under(p), (*right).to_str_under(p)) },
			Mul(left, right) => unsafe { fmt!("%s * %s", (*left).to_str_under(p), (*right).to_str_under(p)) },
			Div(left, right) => unsafe { fmt!("%s / %s", (*left).to_str_under(p), (*right).to_str_under(p)) },
			Val(_)           => self.value.to_str()
		}
	}
}

impl Solver {
	#[inline]
	fn new() -> Solver {
		Solver { exprs: ~[] }
	}

	#[inline]
	fn expr(&mut self, op: Op, value: uint, used: u64) -> *Expr {
		let expr = ~Expr { op: op, value: value, used: used };
		let ptr: *Expr = &*expr;
		self.exprs.push(expr);
		return ptr;
	}

	#[inline]
	fn val(&mut self, value: uint, index: uint) -> *Expr {
		self.expr(Val(index), value, 1u64 << index)
	}

	#[inline]
	unsafe fn add(&mut self, left: *Expr, right: *Expr) -> *Expr {
		let used = (*left).used | (*right).used;
		let value = (*left).value + (*right).value;
		self.expr(Add(left, right), value, used)
	}

	#[inline]
	unsafe fn sub(&mut self, left: *Expr, right: *Expr) -> *Expr {
		let used = (*left).used | (*right).used;
		let value = (*left).value - (*right).value;
		self.expr(Sub(left, right), value, used)
	}

	#[inline]
	unsafe fn mul(&mut self, left: *Expr, right: *Expr) -> *Expr {
		let used = (*left).used | (*right).used;
		let value = (*left).value * (*right).value;
		self.expr(Mul(left, right), value, used)
	}

	#[inline]
	unsafe fn div(&mut self, left: *Expr, right: *Expr) -> *Expr {
		let used = (*left).used | (*right).used;
		let value = (*left).value / (*right).value;
		self.expr(Div(left, right), value, used)
	}
	
	unsafe fn make(&mut self, a: *Expr, b: *Expr, f: &fn(*Expr) -> bool) -> bool {
		if is_normalized_add(a,b) {
			send!(self.add(a,b));
		}
		else if is_normalized_add(b,a) {
			send!(self.add(a,b));
		}

		if (*a).value != 1 && (*b).value != 1 {
			if is_normalized_mul(a,b) {
				send!(self.mul(a,b));
			}
			else if is_normalized_mul(b,a) {
				send!(self.mul(b,a));
			}
		}

		if (*a).value > (*b).value {
			if is_normalized_sub(a,b) {
				send!(self.sub(a,b));
			}

			if (*b).value != 1 && ((*a).value % (*b).value) == 0 && is_normalized_div(a,b) {
				send!(self.div(a,b));
			}
		}
		else if (*b).value > (*a).value {
			if is_normalized_sub(b,a) {
				send!(self.sub(b,a));
			}

			if (*a).value != 1 && ((*b).value % (*a).value) == 0 && is_normalized_div(b,a) {
				send!(self.div(b,a));
			}
		}
		else if (*b).value != 1 {
			if is_normalized_div(a,b) {
				send!(self.div(a,b));
			}
			else if is_normalized_div(b,a) {
				send!(self.div(b,a));
			}
		}

		return true;
	}
}

unsafe fn is_normalized_add(left: *Expr, right: *Expr) -> bool {
	match (*right).op {
		Add(_,_) => {},
		Sub(_,_) => {},
		_ => {
			match (*left).op {
				Add(_,lright) => return (*lright).value <= (*right).value,
				Sub(_,_) => {},
				_ => return (*left).value <= (*right).value
			}
		}
	}
	return false;
}

unsafe fn is_normalized_sub(left: *Expr, right: *Expr) -> bool {
	match (*right).op {
		Add(_,_) => {},
		Sub(_,_) => {},
		_ => {
			match (*left).op {
				Sub(_,lright) => return (*lright).value <= (*right).value,
				_ => return true
			}
		}
	}
	return false;
}

unsafe fn is_normalized_mul(left: *Expr, right: *Expr) -> bool {
	match (*right).op {
		Mul(_,_) => {},
		Div(_,_) => {},
		_ => {
			match (*left).op {
				Mul(_,lright) => return (*lright).value <= (*right).value,
				Div(_,_) => {},
				_ => return (*left).value <= (*right).value
			}
		}
	}
	return false;
}

unsafe fn is_normalized_div(left: *Expr, right: *Expr) -> bool {
	match (*right).op {
		Mul(_,_) => {},
		Div(_,_) => {},
		_ => {
			match (*left).op {
				Div(_,lright) => return (*lright).value <= (*right).value,
				_ => return true
			}
		}
	}
	return false;
}

fn solutions(target: uint, mut numbers: ~[uint], f: &fn(&Expr) -> bool) -> bool {
	struct Helper {
		exprs: ~[*Expr]
	}

	let numcnt = numbers.len();
	let full_usage = !(!0u64 << numcnt);
	let mut solver = Solver::new();
	let mut h = Helper { exprs: ~[] };
	let mut uniq_solutions = HashSet::new();
	quick_sort3(numbers);

	unsafe {
		for (i, numref) in numbers.iter().enumerate() {
			let num = *numref;
			let expr = solver.val(num,i);
			let ptr: *Expr = &*expr;
			h.exprs.push(ptr);
		}

		for expr in h.exprs.iter() {
			if (**expr).value == target {
				send!(&**expr);
				break;
			}
		}

		let mut lower = 0;
		let mut upper = numcnt;
		let (port, chan) = stream();
		let chan = SharedChan::new(chan);

		while lower < upper {
			let mid: uint = sqrt((upper*upper + lower*lower) as float/2.0).round() as uint;
			let mut workers = 2;
			let mut new_exprs = ~[];

			{
				let unsafe_h: *Helper = &h;
				let chan_clone = chan.clone();
				do spawn_with(lower) |lower| {
					work(lower, mid, (*unsafe_h).exprs, full_usage, &chan_clone);
				}

				let chan_clone = chan.clone();
				do spawn_with(upper) |upper| {
					work(mid, upper, (*unsafe_h).exprs, full_usage, &chan_clone);
				}

				while workers > 0 {
					let pair = port.recv();
					match pair {
						None => workers -= 1,
						Some((hasroom, aexpr, bexpr)) => {
							if !solver.make(aexpr, bexpr, |expr| {
								let mut ok = true;
								if (*expr).value == target {
									let wrapped = NumericHashedExpr { expr: expr };
									if !uniq_solutions.contains(&wrapped) {
										uniq_solutions.insert(wrapped);
										ok = f(&*expr);
									}
								}
								else if hasroom {
									new_exprs.push(expr);
								}

								ok
							}) {
								// TODO: stop all tasks
								return false;
							}
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

	return true;
}

fn work (lower: uint, upper: uint, exprs: &[*Expr], full_usage: u64, chan: &SharedChan<Option<(bool,*Expr,*Expr)>>) {
	for b in range(lower,upper) {
		let bexpr = exprs[b];

		for a in range(0,b) {
			unsafe {
				let aexpr = exprs[a];

				if ((*aexpr).used & (*bexpr).used) == 0 {
					let hasroom = ((*aexpr).used | (*bexpr).used) != full_usage;
					chan.send(Some((hasroom, aexpr, bexpr)));
				}
			}
		}
	}
	chan.send(None);
}

fn main () {
	let args = os::args();
	if args.len() < 3 {
		fail!("not enough arguments");
	}
	let target = uint::from_str(args[1]).expect("target is not a number");
	let mut numbers = args.slice(2,args.len()).map(|arg| {
		let num = uint::from_str(*arg).expect(fmt!("argument is not a number: %s",*arg));
		if num == 0 { fail!(fmt!("illegal argument value: %s",*arg)); }
		num
	});
	if (numbers.len() > 64) {
		fail!("only up to 64 numbers supported");
	}
	quick_sort3(numbers);

	println(fmt!("target  = %u", target));
	println(fmt!("numbers = [%s]", numbers.map(|num| num.to_str()).connect(", ")));

	println("solutions:");
	let mut i = 1;
	solutions(target, numbers, |expr| {
		println(fmt!("%3d: %s", i, expr.to_str()));
		i += 1;
		true
	});
}
