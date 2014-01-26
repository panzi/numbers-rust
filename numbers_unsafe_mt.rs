#[feature(macro_rules)];

extern mod extra;

use std::os;
use std::hashmap::HashSet;
use std::num::sqrt;
use std::comm::SharedChan;
use std::uint;

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
//			_      => format!("({})", self.to_str())
//		}
		if (precedence > self.precedence()) {
			return format!("({})", self.to_str());
		}
		else {
			return self.to_str();
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
			Val(_)           => self.value.iter_bytes(lsb0,f)
		}
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
			Add(left, right) => unsafe { format!("{} + {}", (*left).to_str_under(p), (*right).to_str_under(p)) },
			Sub(left, right) => unsafe { format!("{} - {}", (*left).to_str_under(p), (*right).to_str_under(p)) },
			Mul(left, right) => unsafe { format!("{} * {}", (*left).to_str_under(p), (*right).to_str_under(p)) },
			Div(left, right) => unsafe { format!("{} / {}", (*left).to_str_under(p), (*right).to_str_under(p)) },
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
	
	unsafe fn make(&mut self, what: uint, a: *Expr, b: *Expr, f: |*Expr|) {
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

unsafe fn make(a: *Expr, b: *Expr) -> uint {
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

unsafe fn is_normalized_add(left: *Expr, right: *Expr) -> bool {
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

unsafe fn is_normalized_sub(left: *Expr, right: *Expr) -> bool {
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

unsafe fn is_normalized_mul(left: *Expr, right: *Expr) -> bool {
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

unsafe fn is_normalized_div(left: *Expr, right: *Expr) -> bool {
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

fn solutions(tasks: u32, target: uint, mut numbers: ~[uint], f: |&Expr|) {
	struct Helper {
		exprs: ~[*Expr]
	}

	let numcnt = numbers.len();
	let full_usage = !(!0u64 << numcnt);
	let mut solver = Solver::new();
	let mut h = Helper { exprs: ~[] };
	let mut uniq_solutions = HashSet::new();
	numbers.sort();

	unsafe {
		for (i, numref) in numbers.iter().enumerate() {
			let num = *numref;
			let expr = solver.val(num,i);
			let ptr: *Expr = &*expr;
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
		let (port, chan) = SharedChan::new();

		while lower < upper {
			let mut workers = 0;
			let mut new_exprs = ~[];
			let x0 = lower;
			let xn = upper;
			let mut x_last = x0;
			let mut i = 1;
			let x0_sq = x0*x0;
			let A = (xn*xn - x0_sq) as f64 / tasks as f64;

			{
				let unsafe_h: *Helper = &h;

				while x_last < xn || workers == 0 {
					let xi = sqrt(i as f64 * A + x0_sq as f64).round() as uint;
					let xi = if xi > xn { xn } else { xi };

					if xi > x_last {
						let xim1 = x_last;
						let chan_clone = chan.clone();

						do spawn {
							work(xim1, xi, (*unsafe_h).exprs, full_usage, &chan_clone);
						}

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
									if !uniq_solutions.contains(& &*expr) {
										uniq_solutions.insert(&*expr);
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

fn work (lower: uint, upper: uint, exprs: &[*Expr], full_usage: u64, chan: &SharedChan<Option<(uint,*Expr,*Expr)>>) {
	for b in range(lower,upper) {
		let bexpr = exprs[b];

		for a in range(0,b) {
			unsafe {
				let aexpr = exprs[a];

				if ((*aexpr).used & (*bexpr).used) == 0 {
					let mut flags = make(aexpr,bexpr);
					if (flags != 0) {
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
	let tasks:u32 = from_str(args[1]).expect("number of tasks is not a number or out of range");
	let target:uint = from_str(args[2]).expect("target is not a number or out of range");
	let mut numbers = args.slice(3,args.len()).map(|arg| {
		let num:uint = from_str(*arg).expect(format!("argument is not a number or out of range: {}",*arg));
		if num == 0 { fail!(format!("illegal argument value: {}",*arg)); }
		num
	});
	if tasks == 0 {
		fail!("number of tasks has to be >= 1");
	}
	if numbers.len() > uint::bits {
		fail!("only up to {} numbers supported", uint::bits);
	}
	numbers.sort();

	println(format!("target  = {}", target));
	println(format!("numbers = [{}]", numbers.map(|num| num.to_str()).connect(", ")));

	println("solutions:");
	let mut i = 1;
	solutions(tasks, target, numbers, |expr| {
		println(format!("{:3d}: {}", i, expr.to_str()));
		i += 1;
	});
}
