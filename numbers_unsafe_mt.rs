extern mod extra;

use std::{uint,os};
use std::hashmap::HashSet;
use std::util::swap;
use extra::sort::quick_sort3;

macro_rules! yield(
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
	priv used: ~[bool]
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

/*
impl IterBytes for *Expr {
	fn iter_bytes(&self, lsb0: bool, f: std::to_bytes::Cb) -> bool {
		unsafe { (*self).iter_bytes(lsb0, f) }
	}
}
*/

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

/*
impl Eq for *Expr {
	fn eq(&self, other: &*Expr) -> bool {
		unsafe { (*self) == (*other)  }
	}
}
*/

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

unsafe fn join_usage(left: *Expr, right: *Expr) -> ~[bool] {
	let mut used = (*left).used.to_owned();
	for i in range(0, (*right).used.len()) {
		if (*right).used[i] {
			used[i] = true;
		}
	}
	return used;
}

unsafe fn split_add_sub(mut node: *Expr) -> (~[*Expr], ~[*Expr]) {
	let mut adds = ~[];
	let mut subs = ~[];

	loop {
		match (*node).op {
			Add(left,right) => {
				adds.push(right);
				node = left;
			},
			Sub(left,right) => {
				subs.push(right);
				node = left;
			},
			_ => break
		}
	}
	adds.push(node);

	return (adds, subs);
}

unsafe fn split_mul_div(mut node: *Expr) -> (~[*Expr], ~[*Expr]) {
	let mut muls = ~[];
	let mut divs = ~[];

	loop {
		match (*node).op {
			Mul(left,right) => {
				muls.push(right);
				node = left;
			},
			Div(left,right) => {
				divs.push(right);
				node = left;
			},
			_ => break
		}
	}
	muls.push(node);

	return (muls, divs);
}

// merge and reverse
unsafe fn merge(mut left: ~[*Expr], mut right: ~[*Expr]) -> ~[*Expr] {
	let n = left.len();
	let m = right.len();

	if n > 0 && m > 0 {
		let mut lst = ~[];
		let mut i = n - 1;
		let mut j = m - 1;

		loop {
			let x = left[i];
			let y = right[j];

			if (*x).value <= (*y).value {
				lst.push(x);
				
				if i == 0 {
					loop {
						lst.push(right[j]);
						if j == 0 { break; }
						j -= 1;
					}
					break;
				}
				i -= 1;
			}
			else {
				lst.push(y);

				if j == 0 {
					loop {
						lst.push(left[i]);
						if i == 0 { break; }
						i -= 1;
					}
					break;
				}
				j -= 1;
			}
		}

		return lst;
	}
	else if n > 0 {
		left.reverse();
		return left;
	}
	else {
		right.reverse();
		return right;
	}
}

impl Solver {
	#[inline]
	fn new() -> Solver {
		Solver { exprs: ~[] }
	}

	#[inline]
	fn expr(&mut self, op: Op, value: uint, used: ~[bool]) -> *Expr {
		let expr = ~Expr { op: op, value: value, used: used };
		let ptr: *Expr = &*expr;
		self.exprs.push(expr);
		return ptr;
	}

	#[inline]
	fn val(&mut self, value: uint, index: uint, numcnt: uint) -> *Expr {
		let mut used = std::vec::from_elem(numcnt, false);
		used[index] = true;
		self.expr(Val(index), value, used)
	}

	#[inline]
	unsafe fn _add(&mut self, left: *Expr, right: *Expr) -> *Expr {
		let used = join_usage(left,right);
		let value = (*left).value + (*right).value;
		self.expr(Add(left, right), value, used)
	}

	unsafe fn add(&mut self, mut left: *Expr, mut right: *Expr) -> *Expr {
		if (*left).value > (*right).value {
			swap(&mut left, &mut right);
		}

		// don't run normalization algorithm if already normalized
		match (*right).op {
			Add(_,_) => {},
			Sub(_,_) => {},
			_ => {
				match (*left).op {
					Add(_,lright) => {
						if (*lright).value <= (*right).value {
							return self._add(left, right);
						}
					},
					Sub(_,_) => {},
					_ => return self._add(left, right)
				}
			}
		}

		let (left_adds,  left_subs)  = split_add_sub(left);
		let (right_adds, right_subs) = split_add_sub(right);

		let adds = merge(left_adds, right_adds);
		let subs = merge(left_subs, right_subs);
		let mut node = adds[0];
		for i in range(1,adds.len()) {
			node = self._add(node,adds[i]);
		}
		for right in subs.iter() {
			node = self._sub(node,*right);
		}
		return node;
	}

	#[inline]
	unsafe fn _sub(&mut self, left: *Expr, right: *Expr) -> *Expr {
		let used = join_usage(left,right);
		let value = (*left).value - (*right).value;
		self.expr(Sub(left, right), value, used)
	}

	unsafe fn sub(&mut self, left: *Expr, right: *Expr) -> *Expr {
		// don't run normalization algorithm if already normalized
		match (*right).op {
			Add(_,_) => {},
			Sub(_,_) => {},
			_ => {
				match (*left).op {
					Sub(_,lright) => {
						if (*lright).value <= (*right).value {
							return self._sub(left, right);
						}
					},
					_ => return self._sub(left, right)
				}
			}
		}

		let (left_adds,  left_subs)  = split_add_sub(left);
		let (right_subs, right_adds) = split_add_sub(right);

		let adds = merge(left_adds, right_adds);
		let subs = merge(left_subs, right_subs);
		let mut node = adds[0];
		for i in range(1,adds.len()) {
			node = self._add(node,adds[i]);
		}
		for right in subs.iter() {
			node = self._sub(node,*right);
		}
		return node;
	}

	#[inline]
	unsafe fn _mul(&mut self, left: *Expr, right: *Expr) -> *Expr {
		let used = join_usage(left,right);
		let value = (*left).value * (*right).value;
		self.expr(Mul(left, right), value, used)
	}

	unsafe fn mul(&mut self, mut left: *Expr, mut right: *Expr) -> *Expr {
		if (*left).value > (*right).value {
			swap(&mut left, &mut right);
		}

		// don't run normalization algorithm if already normalized
		match (*right).op {
			Mul(_,_) => {},
			Div(_,_) => {},
			_ => {
				match (*left).op {
					Mul(_,lright) => {
						if (*lright).value <= (*right).value {
							return self._mul(left, right);
						}
					},
					Div(_,_) => {},
					_ => return self._mul(left, right)
				}
			}
		}

		let (left_muls,  left_divs)  = split_mul_div(left);
		let (right_muls, right_divs) = split_mul_div(right);

		let muls = merge(left_muls, right_muls);
		let divs = merge(left_divs, right_divs);
		let mut node = muls[0];
		for i in range(1,muls.len()) {
			node = self._mul(node,muls[i]);
		}
		for right in divs.iter() {
			node = self._div(node,*right);
		}
		return node;
	}

	#[inline]
	unsafe fn _div(&mut self, left: *Expr, right: *Expr) -> *Expr {
		let used = join_usage(left,right);
		let value = (*left).value / (*right).value;
		self.expr(Div(left, right), value, used)
	}

	unsafe fn div(&mut self, left: *Expr, right: *Expr) -> *Expr {
		// don't run normalization algorithm if already normalized
		match (*right).op {
			Mul(_,_) => {},
			Div(_,_) => {},
			_ => {
				match (*left).op {
					Div(_,lright) => {
						if (*lright).value <= (*right).value {
							return self._div(left, right);
						}
					},
					_ => return self._div(left, right)
				}
			}
		}

		let (left_muls,  left_divs)  = split_mul_div(left);
		let (right_divs, right_muls) = split_mul_div(right);

		let muls = merge(left_muls, right_muls);
		let divs = merge(left_divs, right_divs);
		let mut node = muls[0];
		for i in range(1,muls.len()) {
			node = self._mul(node,muls[i]);
		}
		for right in divs.iter() {
			node = self._div(node,*right);
		}
		return node;
	}
	
	unsafe fn make(&mut self, a: *Expr, b: *Expr, f: &fn(*Expr) -> bool) -> bool {
		yield!(self.add(a,b));

		if (*a).value != 1 && (*b).value != 1 {
			yield!(self.mul(a,b));
		}

		if (*a).value > (*b).value {
			yield!(self.sub(a,b));

			if (*b).value != 1 && (*a).value % (*b).value == 0 {
				yield!(self.div(a,b));
			}
		}
		else if (*b).value > (*a).value {
			yield!(self.sub(b,a));

			if (*a).value != 1 && (*b).value % (*a).value == 0 {
				yield!(self.div(b,a));
			}
		}
		else if (*b).value != 1 {
			yield!(self.div(a,b));
		}

		return true;
	}
}

fn solutions(target: uint, mut numbers: ~[uint], f: &fn(&Expr) -> bool) -> bool {
	let numcnt = numbers.len();
	let mut solver = Solver::new();
	let mut exprs: ~[*Expr] = ~[];
	let mut uniq_exprs: HashSet<&Expr> = HashSet::new();
	let mut uniq_solutions = HashSet::new();
	quick_sort3(numbers);

	unsafe {
		for (i, numref) in numbers.iter().enumerate() {
			let num = *numref;
			let expr = solver.val(num,i,numcnt);
			let ptr: *Expr = &*expr;
			uniq_exprs.insert(&*expr);
			exprs.push(ptr);
		}

		for expr in exprs.iter() {
			if (**expr).value == target {
				yield!(&**expr);
			}
		}

		let mut lower = 0;
		let mut upper = numcnt;
		while lower < upper {
			for b in range(lower,upper) {
				for a in range(0,b) {
					let aexpr = exprs[a];
					let bexpr = exprs[b];
					let mut fits = true;

					for i in range(0, numcnt) {
						if (*aexpr).used[i] && (*bexpr).used[i] {
							fits = false;
							break;
						}
					}

					if fits {
						let mut hasroom = false;
						for i in range(0, numcnt) {
							if !(*aexpr).used[i] || !(*bexpr).used[i] {
								hasroom = true;
								break;
							}
						}

						if !solver.make(aexpr, bexpr, |expr| {
							let mut ok = true;
							if !uniq_exprs.contains(& &*expr) {
								uniq_exprs.insert(&*expr);
								if (*expr).value == target {
									let wrapped = NumericHashedExpr { expr: expr };
									if !uniq_solutions.contains(&wrapped) {
										uniq_solutions.insert(wrapped);
										ok = f(&*expr);
									}
								}
								else if hasroom {
									exprs.push(expr);
								}
							}

							ok
						}) { return false; }
					}
				}
			}

			lower = upper;
			upper = exprs.len();
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
