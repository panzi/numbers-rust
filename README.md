numbers-rust
============

**NOTE:** This needs a rewrite. It doesn't compile with current Rust and is
not very idiomatic.

Countdown numbers game solver written in Rust.

Compile:

```
rustc --opt-level=3 numbers.rs
rustc --opt-level=3 numbers_unsafe_mt.rs
```

Usage:

```
./numbers <target> [<number>...]
./numbers_unsafe_mt <threads> <target> [<number>...]
```

Same program in other languages:
* https://github.com/panzi/numbers-c
* https://github.com/panzi/numbers-python
* https://github.com/panzi/numbers-js

C program using a much better strategy:
* https://github.com/panzi/numbers
