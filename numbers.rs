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
	used: ~[bool]
}

impl Expr {
	fn precedence(&self) -> uint {
		match self.op {
			Add(_,_) => 0,
			Sub(_,_) => 0,
			Mul(_,_) => 2,
			Div(_,_) => 1,
			Val(_)   => 3
		}
	}
	
	fn order(&self) -> (uint, uint) {
		match self.op {
			Val(index) => (0, index),
			Add(_,_)   => (1, self.value),
			Sub(_,_)   => (2, self.value),
			Mul(_,_)   => (3, self.value),
			Div(_,_)   => (4, self.value)
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
			Val(index)       => index.iter_bytes(lsb0,f)
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
			Val(index) => match other.op {
				Val(oindex) => index == oindex,
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

fn val(value: uint, index: uint, numcnt: uint) -> @Expr {
	let mut used = std::vec::from_elem(numcnt, false);
	used[index] = true;
	@Expr { op: Val(index), value: value, used: used }
}

fn join_usage(left: &Expr, right: &Expr) -> ~[bool] {
	let mut used = left.used.to_owned();
	for i in range(0, right.used.len()) {
		if (right.used[i]) {
			used[i] = true;
		}
	}
	return used;
}

fn add(left: @Expr, right: @Expr) -> @Expr {
	let used = join_usage(left,right);
	let value = left.value + right.value;
	@Expr { op: Add(left, right), value: value, used: used }
}

fn sub(left: @Expr, right: @Expr) -> @Expr {
	let used = join_usage(left,right);
	let value = left.value - right.value;
	@Expr { op: Sub(left, right), value: value, used: used }
}

fn mul(left: @Expr, right: @Expr) -> @Expr {
	let used = join_usage(left,right);
	let value = left.value * right.value;
	@Expr { op: Mul(left, right), value: value, used: used }
}

fn div(left: @Expr, right: @Expr) -> @Expr {
	let used = join_usage(left,right);
	let value = left.value / right.value;
	@Expr { op: Div(left, right), value: value, used: used }
}

macro_rules! yield(
	($($arg:expr),*) => (if !f($($arg),*) { return false; })
)

fn uniq(xs: &[uint]) -> ~[uint] {
	let mut uniq_xs = HashSet::new();
	let mut ys = ~[];

	for x in xs.iter() {
		if !uniq_xs.contains(x) {
			uniq_xs.insert(*x);
			ys.push(*x);
		}
	}

	return ys;
}

fn solutions(target: uint, mut numbers: ~[uint], f: &fn(@Expr) -> bool) -> bool {
	let numcnt = numbers.len();
	let mut exprs = ~[];
	let mut uniq_exprs = HashSet::new();
	quick_sort3(numbers);
	for (i, numref) in numbers.iter().enumerate() {
		let num = *numref;
		let expr = val(num,i,numcnt);
		uniq_exprs.insert(expr);
		exprs.push(expr);
	}

	for expr in exprs.iter() {
		if expr.value == target {
			yield!(*expr);
		}
	}

	let mut lower = 0;
	let mut upper = numcnt;
	while lower < upper {
		if (!combinations_slice(lower, upper, |a, b| {
			let aexpr = exprs[a];
			let bexpr = exprs[b];
			let mut fits = true;
			let mut ok   = true;

			for i in range(0, numcnt) {
				if aexpr.used[i] && bexpr.used[i] {
					fits = false;
					break;
				}
			}

			if fits {
				let mut hasroom = false;
				for i in range(0, numcnt) {
					if !aexpr.used[i] || !bexpr.used[i] {
						hasroom = true;
						break;
					}
				}

				ok = make(aexpr, bexpr, |expr| {
					let mut ok = true;
					if !uniq_exprs.contains(&expr) {
						uniq_exprs.insert(expr);
						if expr.value == target {
							ok = f(expr);
						}
						if hasroom && expr.value != target {
							exprs.push(expr);
						}
					}

					ok
				});
			}

			ok
		})) { return false; }

		lower = upper;
		upper = exprs.len();
	}

	return true;
}

fn combinations_slice(lower: uint, upper: uint, f: &fn(uint,uint) -> bool) -> bool {
	if lower >= upper { return true; }

	let mut i = lower;
	while i < upper {
		let mut a = 0;
		let mut b = i;
		while b > a && b >= lower {
			yield!(a, b);
			b -= 1;
			a += 1;
		}
		i += 1;
	}

	i = 1;
	while i < upper {
		let mut a = i;
		let mut b = upper - 1;
		while b > a && b >= lower {
			yield!(a, b);
			b -= 1;
			a += 1;
		}
		i += 1;
	}

	return true;
}

fn make(a: @Expr, b: @Expr, f: &fn(@Expr) -> bool) -> bool {
	// bring commutative operations in normalized order
	// TODO: proper normalization of expressions
	if a.value > b.value {
		yield!(add(a,b));

		if a.value != 1 && b.value != 1 {
			yield!(mul(a,b));
		}

		yield!(sub(a,b));

		if b.value != 1 && a.value % b.value == 0 {
			yield!(div(a,b));
		}
	}
	else if b.value > a.value {
		yield!(add(b,a));

		if b.value != 1 && a.value != 1 {
			yield!(mul(b,a));
		}

		yield!(sub(b,a));

		if a.value != 1 && b.value % a.value == 0 {
			yield!(div(b,a));
		}
	}
	else if a.order() > b.order() {
		yield!(add(a,b));

		if a.value != 1 && b.value != 1 {
			yield!(mul(a,b));
		}

		if b.value != 1 {
			yield!(div(a,b));
		}
	}
	else {
		yield!(add(b,a));

		if b.value != 1 && a.value != 1 {
			yield!(mul(b,a));
		}

		if a.value != 1 {
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
