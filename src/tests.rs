//! Testing specific to `num-primitive`
//!
//! NOTE: we're not attempting much functional testing in this crate, because we're not actually
//! *implementing* much of anything, just connecting to existing inherent items on the primitive
//! types. If those are wrong, that's an issue for the standard library.
//!
//! The use of forwarding macros with the same name mostly eliminates the chance of typos
//! referencing the wrong things, and the `unconditional-recursion` lint makes sure we're calling
//! something other than ourself.
//!
//! We should still write tests for issues that are unique to us though. An example from early
//! experiments is that the `TryFrom` error types were not constrained, so even a simple
//! `Result::unwrap` wouldn't work -- so now we have `PrimitiveError` and some tests for that.

extern crate alloc;

use alloc::boxed::Box;
use core::error::Error;

use crate::{PrimitiveError, PrimitiveInteger, PrimitiveNumber};

fn check_result<'a, T: PrimitiveNumber, E: PrimitiveError>(r: Result<T, E>, ok: T) {
    // Cloning and equating results requires `E: Clone + PartialEq`
    assert_eq!(r.clone(), Ok(ok));

    // Unwrapping requires `E: Debug`
    assert_eq!(r.clone().unwrap(), ok);

    // `?`-convert to a boxed error
    let result: Result<T, Box<dyn Error + 'a>> = (|| Ok(r.clone()?))();
    assert_eq!(result.unwrap(), ok);

    // `?`-convert to a boxed thread-safe error
    let result: Result<T, Box<dyn Error + Send + Sync + 'a>> = (|| Ok(r.clone()?))();
    assert_eq!(result.unwrap(), ok);
}

#[test]
fn parse() {
    fn check<T: PrimitiveNumber>(s: &str, ok: T) {
        check_result(s.parse(), ok);
    }
    check("0", 0u32);
}

#[test]
fn try_from() {
    fn check<T: PrimitiveInteger>(x: i32, ok: T) {
        check_result(T::try_from(x), ok);
    }
    check(0i32, 0u32);
}

#[test]
fn try_into() {
    fn check<T: PrimitiveInteger>(x: T, ok: u32) {
        check_result(x.try_into(), ok);
    }
    check(0i32, 0u32);
}

// The following tests use `#![feature(min_generic_const_args)]`

#[test]
fn bytes1() {
    // Return a value with the most significant bit set
    fn msb<T: PrimitiveNumber>() -> T {
        let mut bytes = [0; T::BYTES];
        bytes[0] = 0x80;
        T::from_be_bytes(bytes)
    }

    assert_eq!(msb::<i64>(), i64::MIN);
    assert_eq!(msb::<u16>(), 1u16 << 15);
    assert!(msb::<f64>().total_cmp(&-0.0).is_eq());
}

#[test]
fn bytes2() {
    // Return a value with all bits set
    fn all_ones<T: PrimitiveNumber>() -> T {
        T::from_ne_bytes(core::array::repeat(0xff))
    }

    assert_eq!(all_ones::<i32>(), -1);
    assert_eq!(all_ones::<usize>(), usize::MAX);
    assert!(all_ones::<f64>().is_nan());
}

#[test]
fn bytes3() {
    // This also needs `#![feature(associated_const_equality)]`
    fn rust<T: PrimitiveNumber<BYTES = 4>>() -> T {
        T::from_be_bytes(*b"Rust")
    }

    assert_eq!(rust::<i32>(), 0x52_75_73_74_i32);
    assert_eq!(rust::<u32>(), 0x52_75_73_74_u32);
    assert_eq!(rust::<f32>(), 2.63551e11);
}
