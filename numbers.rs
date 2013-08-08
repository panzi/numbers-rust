use std::{uint,os};
use std::hashmap::HashSet;
use std::iterator::FromIterator;

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

/*
macro_rules! compr(
    ($o:expr : $v:ident <- $i:expr $(,$p:expr)+) =>
        ($i.$(filtered(|&$v| { $p })).*.map(|&$v| { $o }));
    ($o:expr : $v:ident <- $i:expr) =>
        ($i.map(|&$v| { $o }))
)
*/

fn solutions(target: uint, numbers: &[uint], f: &fn(&Expr) -> bool) -> bool {
	let mut uniq_nums = HashSet::new();
	for num in numbers.iter() {
		uniq_nums.insert(num);
	}
//	let uniq_nums = FromIterator::from_iterator::<HashSet<uint>>(numbers.iter());
	let numcnt = uniq_nums.len();
	// TODO: sort
	let mut exprs = ~[];
	let mut avail = ~[];
	for (i, num) in uniq_nums.iter().enumerate() {
		exprs.push(val(**num,i,numcnt));
		avail.push(numbers.count(**num));
	}

	for expr in exprs.iter() {
		if expr.value == target {
			yield!(*expr);
		}
	}

	// TODO

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

/*
fn solve(target: uint, numbers: &[uint]) -> ~Expr {
	// TODO

	~Val(0)
}
*/
fn main() {
	let args = os::args();
	if args.len() < 3 {
		fail!("not enough arguments");
	}
	let target = uint::from_str(args[1]).expect("target is not a number");
	let numbers = args.slice(2,args.len()).map(|arg|
		uint::from_str(*arg).expect(fmt!("argument is not a number: %s",*arg)));

//	println(fmt!("%?", add(mul(val(2,0,6),val(3,1,6)),val(4,2,6)) == add(mul(val(2,3,6),val(3,4,6)),val(4,5,6))));
	println(fmt!("target   = %u", target));
	println(fmt!("numbers  = %s", numbers.map(|num| num.to_str()).connect(", ")));
//	println(fmt!("solution = %s", solve(target, numbers).to_str()));

//	let expr = mul(add(div(val(9),val(3)),val(2)),sub(val(2),val(3)));
//	println(fmt!("%s = %d", expr.to_str(), expr.val()));
}
