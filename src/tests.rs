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

use crate::{PrimitiveError, PrimitiveFloatToInt, PrimitiveInteger, PrimitiveNumber};

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

#[test]
fn to_int_unchecked() {
    fn pi<T: PrimitiveFloatToInt<Int>, Int>() -> Int {
        // SAFETY: π is finite, and truncated to 3 fits any int
        unsafe { T::PI.to_int_unchecked() }
    }
    assert_eq!(pi::<f32, i64>(), 3i64);
    assert_eq!(pi::<f64, u8>(), 3u8);
}
