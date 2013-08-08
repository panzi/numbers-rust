extern mod extra;

use std::{uint,os};
use std::hashmap::HashSet;
use extra::sort::quick_sort3;

macro_rules! printf(
	($fmt:expr, $($arg:expr),*) => (
		print(fmt!($fmt, $($arg),*))
	)
)

enum Op {
	Add(~Expr,~Expr),
	Sub(~Expr,~Expr),
	Mul(~Expr,~Expr),
	Div(~Expr,~Expr),
	Val
}

struct Expr {
	op: Op,
	value: uint,
	used: ~[uint]
}

impl Expr {
	fn precedence(&self) -> uint {
		match self.op {
			Add(_,_) => 0,
			Sub(_,_) => 0,
			Mul(_,_) => 2,
			Div(_,_) => 1,
			Val => 3
		}
	}
	
	fn to_str_under(&self,precedence: uint) -> ~str {
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
			Add(ref left, ref right) => bin_iter_bytes!('+'),
			Sub(ref left, ref right) => bin_iter_bytes!('-'),
			Mul(ref left, ref right) => bin_iter_bytes!('*'),
			Div(ref left, ref right) => bin_iter_bytes!('/'),
			Val => self.value.iter_bytes(lsb0,f)
		}
	}
}

impl Clone for Op {
	fn clone(&self) -> Op {
		match *self {
			Add(ref left, ref right) => Add(left.clone(), right.clone()),
			Sub(ref left, ref right) => Sub(left.clone(), right.clone()),
			Mul(ref left, ref right) => Mul(left.clone(), right.clone()),
			Div(ref left, ref right) => Div(left.clone(), right.clone()),
			Val => Val
		}
	}
}

impl Clone for Expr {
	fn clone(&self) -> Expr {
		Expr { op: self.op.clone(), value: self.value, used: self.used.clone() }
	}
}

impl Eq for Expr {
	fn eq(&self, other: &Expr) -> bool {
		match self.op {
			Add(ref left, ref right) => match other.op {
				Add(ref oleft, ref oright) => left == oleft && right == oright,
				_ => false
			},
			Sub(ref left, ref right) => match other.op {
				Sub(ref oleft, ref oright) => left == oleft && right == oright,
				_ => false
			},
			Mul(ref left, ref right) => match other.op {
				Mul(ref oleft, ref oright) => left == oleft && right == oright,
				_ => false
			},
			Div(ref left, ref right) => match other.op {
				Div(ref oleft, ref oright) => left == oleft && right == oright,
				_ => false
			},
			Val => match other.op {
				Val => self.value == other.value,
				_ => false
			},
		}
	}
}

impl ToStr for Expr {
	fn to_str(&self) -> ~str {
		let p = self.precedence();
		match self.op {
			Add(ref left, ref right) => fmt!("%s + %s", left.to_str_under(p), right.to_str_under(p)),
			Sub(ref left, ref right) => fmt!("%s - %s", left.to_str_under(p), right.to_str_under(p)),
			Mul(ref left, ref right) => fmt!("%s * %s", left.to_str_under(p), right.to_str_under(p)),
			Div(ref left, ref right) => fmt!("%s / %s", left.to_str_under(p), right.to_str_under(p)),
			Val => self.value.to_str()
		}
	}
}

fn val(value: uint, index: uint, numcnt: uint) -> ~Expr {
	let mut used = std::vec::from_elem(numcnt, 0u);
	used[index] = 1;
	~Expr { op: Val, value: value, used: used }
}

fn join_usage(left: &Expr, right: &Expr) -> ~[uint] {
	let mut used = left.used.to_owned();
	let n = right.used.len();
	let mut i = 0;
	while i < n {
		used[i] += right.used[i];
		i += 1;
	}
	return used;
}

fn add(left: ~Expr, right: ~Expr) -> ~Expr {
	let used = join_usage(left,right);
	let value = left.value + right.value;
	~Expr { op: Add(left, right), value: value, used: used }
}

fn sub(left: ~Expr, right: ~Expr) -> ~Expr {
	let used = join_usage(left,right);
	let value = left.value - right.value;
	~Expr { op: Sub(left, right), value: value, used: used }
}

fn mul(left: ~Expr, right: ~Expr) -> ~Expr {
	let used = join_usage(left,right);
	let value = left.value * right.value;
	~Expr { op: Mul(left, right), value: value, used: used }
}

fn div(left: ~Expr, right: ~Expr) -> ~Expr {
	let used = join_usage(left,right);
	let value = left.value / right.value;
	~Expr { op: Div(left, right), value: value, used: used }
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

// TODO: reduce the awefully high number of clones using @ thruout the program
fn solutions(target: uint, numbers: &[uint], f: &fn(&Expr) -> bool) -> bool {
	let mut uniq_nums = uniq(numbers);
	quick_sort3(uniq_nums);
	let numcnt = uniq_nums.len();
	let mut exprs = ~[];
	let mut avail = ~[];
	let mut uniq_exprs = HashSet::new();
	for (i, numref) in uniq_nums.iter().enumerate() {
		let num = *numref;
		let expr = val(num,i,numcnt);
		uniq_exprs.insert(expr.clone());
		exprs.push(expr);
		avail.push(numbers.iter().count(|x| { *x == num }));
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
			let aexpr = exprs[a].clone();
			let bexpr = exprs[b].clone();
			let mut used = std::vec::from_elem(numcnt, 0u);
			let mut fits = true;
			let mut ok   = true;

			for i in range(0, numcnt) {
				let u = aexpr.used[i] + bexpr.used[i];
				used[i] = u;
				if avail[i] < u {
					fits = false;
				}
			}

			if fits {
				let mut hasroom = false;
				for i in range(0, numcnt) {
					if avail[i] != used[i] {
						hasroom = true;
						break;
					}
				}

				ok = make(aexpr, bexpr, |expr| {
					let mut ok = true;
					if !uniq_exprs.contains(&expr) {
						uniq_exprs.insert(expr.clone());
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

fn bounded_combinations(n: uint, f: &fn(uint,uint) -> bool) -> bool {
	let mut i = 0;
	while i < n {
		let mut a = 0;
		let mut b = i;
		while b > a {
			yield!(a, b);
			b -= 1;
			a += 1;
		}
		i += 1;
	}

	i = 1;
	while i < n {
		let mut a = i;
		let mut b = n - 1;
		while b > a {
			yield!(a, b);
			b -= 1;
			a += 1;
		}
		i += 1;
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

fn make(a: &Expr, b: &Expr, f: &fn(~Expr) -> bool) -> bool {
	yield!(add(~a.clone(),~b.clone()));

	if a.value != 1 && b.value != 1 {
		yield!(mul(~a.clone(),~b.clone()));
	}

	if a.value > b.value {
		yield!(sub(~a.clone(),~b.clone()));

		if b.value != 1 && a.value % b.value == 0 {
			yield!(div(~a.clone(),~b.clone()));
		}
	}
	else if b.value > a.value {
		yield!(sub(~b.clone(),~a.clone()));

		if a.value != 1 && b.value % a.value == 0 {
			yield!(div(~b.clone(),~a.clone()));
		}
	}
	else if b.value != 1 {
		yield!(div(~a.clone(),~b.clone()));
	}

	return true;
}

fn main() {
	let args = os::args();
	if args.len() < 3 {
		fail!("not enough arguments");
	}
	let target = uint::from_str(args[1]).expect("target is not a number");
	let numbers = args.slice(2,args.len()).map(|arg|
		uint::from_str(*arg).expect(fmt!("argument is not a number: %s",*arg)));

/*
	let n = 20;
	let mut tbl = std::vec::from_elem(n, std::vec::from_elem(n, 0u));
	let mut counter = 1;
	combinations_slice(10, n, |x, y| {
		tbl[y][x] = counter;
		counter += 1;
		true
	});
	let mut x = 0;
	print("   ");
	while x < n {
		print(fmt!(" %3u", x+1));
		x += 1;
	}
	print("\n");
	let mut y = 0;
	while y < n {
		print(fmt!("%3u", y+1));
		x = 0;
		while x < n {
			let v = tbl[y][x];
			if (v == 0) {
				print("    ");
			}
			else {
				print(fmt!(" %3u", v));
			}
			x += 1;
		}
		print("\n");
		y += 1;
	}
*/

//	println(fmt!("%?", add(mul(val(2,0,6),val(3,1,6)),val(4,2,6)) == add(mul(val(2,3,6),val(3,4,6)),val(4,5,6))));
	println(fmt!("target   = %u", target));
	println(fmt!("numbers  = %s", numbers.map(|num| num.to_str()).connect(", ")));
//	println(fmt!("solution = %s", solve(target, numbers).to_str()));

	println("solutions:");
	let mut i = 1;
	solutions(target, numbers, |expr| {
		println(fmt!("%3d: %s", i, expr.to_str()));
		i += 1;
		true
	});

//	let expr = mul(add(div(val(9),val(3)),val(2)),sub(val(2),val(3)));
//	println(fmt!("%s = %d", expr.to_str(), expr.val()));
}
