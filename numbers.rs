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
			Val(_)           => self.value.iter_bytes(lsb0,f)
		}
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
			Val(_) => match other.op {
				Val(_) => self.value == other.value,
				_ => false
			}
		}
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
		Add(_,_) | Sub(_,_) => return false,
		_ => {
			match left.op {
				Add(_,lright) => return lright.value <= right.value,
				Sub(_,_) => return false,
				_ => return left.value <= right.value
			}
		}
	}
}

#[inline]
fn sub(left: @Expr, right: @Expr) -> @Expr {
	let used = left.used | right.used;
	let value = left.value - right.value;
	@Expr { op: Sub(left, right), value: value, used: used }
}

fn is_normalized_sub(left: @Expr, right: @Expr) -> bool {
	match right.op {
		Add(_,_) | Sub(_,_) => return false,
		_ => {
			match left.op {
				Sub(_,lright) => return lright.value <= right.value,
				_ => return true
			}
		}
	}
}

#[inline]
fn mul(left: @Expr, right: @Expr) -> @Expr {
	let used = left.used | right.used;
	let value = left.value * right.value;
	@Expr { op: Mul(left, right), value: value, used: used }
}

fn is_normalized_mul(left: @Expr, right: @Expr) -> bool {
	match right.op {
		Mul(_,_) | Div(_,_) => return false,
		_ => {
			match left.op {
				Mul(_,lright) => return lright.value <= right.value,
				Div(_,_) => return false,
				_ => return left.value <= right.value
			}
		}
	}
}

#[inline]
fn div(left: @Expr, right: @Expr) -> @Expr {
	let used = left.used | right.used;
	let value = left.value / right.value;
	@Expr { op: Div(left, right), value: value, used: used }
}

fn is_normalized_div(left: @Expr, right: @Expr) -> bool {
	match right.op {
		Mul(_,_) | Div(_,_) => return false,
		_ => {
			match left.op {
				Div(_,lright) => return lright.value <= right.value,
				_ => return true
			}
		}
	}
}

fn solutions(target: uint, mut numbers: ~[uint], f: &fn(@Expr)) {
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
			f(*expr);
			break;
		}
	}

	let mut lower = 0;
	let mut upper = numcnt;
	while lower < upper {
		for b in range(lower,upper) {
			let bexpr = exprs[b];

			for a in range(0,b) {
				let aexpr = exprs[a];

				if (aexpr.used & bexpr.used) == 0 {
					let hasroom = (aexpr.used | bexpr.used) != full_usage;

					make(aexpr, bexpr, |expr| {
						if expr.value == target {
							if !uniq_solutions.contains(&expr) {
								uniq_solutions.insert(expr);
								f(expr);
							}
						}
						else if hasroom {
							exprs.push(expr);
						}
					});
				}
			}
		}

		lower = upper;
		upper = exprs.len();
	}
}

fn make(a: @Expr, b: @Expr, f: &fn(@Expr)) {
	if is_normalized_add(a,b) {
		f(add(a,b));
	}
	else if is_normalized_add(b,a) {
		f(add(b,a));
	}

	if a.value != 1 && b.value != 1 {
		if is_normalized_mul(a,b) {
			f(mul(a,b));
		}
		else if is_normalized_mul(b,a) {
			f(mul(b,a));
		}
	}

	if a.value > b.value {
		if is_normalized_sub(a,b) {
			f(sub(a,b));
		}

		if b.value != 1 && (a.value % b.value) == 0 && is_normalized_div(a,b) {
			f(div(a,b));
		}
	}
	else if b.value > a.value {
		if is_normalized_sub(b,a) {
			f(sub(b,a));
		}

		if a.value != 1 && (b.value % a.value) == 0 && is_normalized_div(b,a) {
			f(div(b,a));
		}
	}
	else if b.value != 1 {
		if is_normalized_div(a,b) {
			f(div(a,b));
		}
		else if is_normalized_div(b,a) {
			f(div(b,a));
		}
	}
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
	});
}
