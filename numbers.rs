extern mod extra;

use std::{uint,os};
use std::hashmap::HashSet;
use extra::sort::quick_sort3;

enum Op {
	Add(@Expr,@Expr),
	Sub(@Expr,@Expr),
	Mul(@Expr,@Expr),
	Div(@Expr,@Expr),
	Val(uint)
}

struct Expr {
	op: Op,
	value: uint,
	used: u64
}

struct NumericHashedExpr {
	expr: @Expr
}

macro_rules! bin_numeric_iter_bytes(
	($op:expr) => (
		$op.iter_bytes(          lsb0, |buf| { f(buf) }) &&
		left.numeric_iter_bytes( lsb0, |buf| { f(buf) }) &&
		right.numeric_iter_bytes(lsb0, |buf| { f(buf) })
	)
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
				Add(oleft, oright) => left.numeric_eq(oleft) && right.numeric_eq(oright),
				_ => false
			},
			Sub(left, right) => match other.op {
				Sub(oleft, oright) => left.numeric_eq(oleft) && right.numeric_eq(oright),
				_ => false
			},
			Mul(left, right) => match other.op {
				Mul(oleft, oright) => left.numeric_eq(oleft) && right.numeric_eq(oright),
				_ => false
			},
			Div(left, right) => match other.op {
				Div(oleft, oright) => left.numeric_eq(oleft) && right.numeric_eq(oright),
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
	($op:expr) => (
		$op.iter_bytes(  lsb0, |buf| { f(buf) }) &&
		left.iter_bytes( lsb0, |buf| { f(buf) }) &&
		right.iter_bytes(lsb0, |buf| { f(buf) })
	)
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
		self.expr.numeric_iter_bytes(lsb0,f)
	}
}

impl Eq for Expr {
	fn eq(&self, other: &Expr) -> bool {
		match self.op {
			Add(left, right) => match other.op {
				Add(oleft, oright) => left == oleft && right == oright,
				_ => false
			},
			Sub(left, right) => match other.op {
				Sub(oleft, oright) => left == oleft && right == oright,
				_ => false
			},
			Mul(left, right) => match other.op {
				Mul(oleft, oright) => left == oleft && right == oright,
				_ => false
			},
			Div(left, right) => match other.op {
				Div(oleft, oright) => left == oleft && right == oright,
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
		self.expr.numeric_eq(other.expr)
	}
}

impl ToStr for Expr {
	fn to_str(&self) -> ~str {
		let p = self.precedence();
		match self.op {
			Add(left, right) => fmt!("%s + %s", left.to_str_under(p), right.to_str_under(p)),
			Sub(left, right) => fmt!("%s - %s", left.to_str_under(p), right.to_str_under(p)),
			Mul(left, right) => fmt!("%s * %s", left.to_str_under(p), right.to_str_under(p)),
			Div(left, right) => fmt!("%s / %s", left.to_str_under(p), right.to_str_under(p)),
			Val(_)           => self.value.to_str()
		}
	}
}

#[inline]
fn val(value: uint, index: uint) -> @Expr {
	@Expr { op: Val(index), value: value, used: 1u64 << index }
}

#[inline]
fn add(left: @Expr, right: @Expr) -> @Expr {
	let used = left.used | right.used;
	let value = left.value + right.value;
	@Expr { op: Add(left, right), value: value, used: used }
}

fn is_normalized_add(left: @Expr, right: @Expr) -> bool {
	match right.op {
		Add(_,_) => {},
		Sub(_,_) => {},
		_ => {
			match left.op {
				Add(_,lright) => return lright.value <= right.value,
				Sub(_,_) => {},
				_ => return left.value <= right.value
			}
		}
	}
	return false;
}

#[inline]
fn sub(left: @Expr, right: @Expr) -> @Expr {
	let used = left.used | right.used;
	let value = left.value - right.value;
	@Expr { op: Sub(left, right), value: value, used: used }
}

fn is_normalized_sub(left: @Expr, right: @Expr) -> bool {
	match right.op {
		Add(_,_) => {},
		Sub(_,_) => {},
		_ => {
			match left.op {
				Sub(_,lright) => return lright.value <= right.value,
				_ => return true
			}
		}
	}
	return false;
}

#[inline]
fn mul(left: @Expr, right: @Expr) -> @Expr {
	let used = left.used | right.used;
	let value = left.value * right.value;
	@Expr { op: Mul(left, right), value: value, used: used }
}

fn is_normalized_mul(left: @Expr, right: @Expr) -> bool {
	match right.op {
		Mul(_,_) => {},
		Div(_,_) => {},
		_ => {
			match left.op {
				Mul(_,lright) => return lright.value <= right.value,
				Div(_,_) => {},
				_ => return left.value <= right.value
			}
		}
	}
	return false;
}

#[inline]
fn div(left: @Expr, right: @Expr) -> @Expr {
	let used = left.used | right.used;
	let value = left.value / right.value;
	@Expr { op: Div(left, right), value: value, used: used }
}

fn is_normalized_div(left: @Expr, right: @Expr) -> bool {
	match right.op {
		Mul(_,_) => {},
		Div(_,_) => {},
		_ => {
			match left.op {
				Div(_,lright) => return lright.value <= right.value,
				_ => return true
			}
		}
	}
	return false;
}

macro_rules! yield(
	($($arg:expr),*) => (if !f($($arg),*) { return false; })
)

fn solutions(target: uint, mut numbers: ~[uint], f: &fn(@Expr) -> bool) -> bool {
	let numcnt = numbers.len();
	let full_usage = !(!0u64 << numcnt);
	let mut exprs = ~[];
	let mut uniq_solutions = HashSet::new();
	quick_sort3(numbers);
	for (i, numref) in numbers.iter().enumerate() {
		let num = *numref;
		let expr = val(num,i);
		exprs.push(expr);
	}

	for expr in exprs.iter() {
		if expr.value == target {
			yield!(*expr);
			break;
		}
	}

	let mut lower = 0;
	let mut upper = numcnt;
	while lower < upper {
		for b in range(lower,upper) {
			for a in range(0,b) {
				let aexpr = exprs[a];
				let bexpr = exprs[b];

				if aexpr.used & bexpr.used == 0 {
					let hasroom = (aexpr.used | bexpr.used) != full_usage;

					if !make(aexpr, bexpr, |expr| {
						let mut ok = true;
						if expr.value == target {
							let wrapped = NumericHashedExpr { expr: expr };
							if !uniq_solutions.contains(&wrapped) {
								uniq_solutions.insert(wrapped);
								ok = f(expr);
							}
						}
						else if hasroom {
							exprs.push(expr);
						}

						ok
					}) { return false; }
				}
			}
		}

		lower = upper;
		upper = exprs.len();
	}

	return true;
}

fn make(a: @Expr, b: @Expr, f: &fn(@Expr) -> bool) -> bool {
	if is_normalized_add(a,b) {
		yield!(add(a,b));
	}
	else if is_normalized_add(b,a) {
		yield!(add(b,a));
	}

	if a.value != 1 && b.value != 1 {
		if is_normalized_mul(a,b) {
			yield!(mul(a,b));
		}
		else if is_normalized_mul(b,a) {
			yield!(mul(b,a));
		}
	}

	if a.value > b.value {
		if is_normalized_sub(a,b) {
			yield!(sub(a,b));
		}

		if b.value != 1 && a.value % b.value == 0 && is_normalized_div(a,b) {
			yield!(div(a,b));
		}
	}
	else if b.value > a.value {
		if is_normalized_sub(b,a) {
			yield!(sub(b,a));
		}

		if a.value != 1 && b.value % a.value == 0 && is_normalized_div(b,a) {
			yield!(div(b,a));
		}
	}
	else if b.value != 1 {
		if is_normalized_div(a,b) {
			yield!(div(a,b));
		}
		else if is_normalized_div(b,a) {
			yield!(div(b,a));
		}
	}

	return true;
}

fn main() {
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
