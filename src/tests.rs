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
use core::convert::Infallible;
use core::error::Error;
use core::num::{ParseFloatError, ParseIntError};

use crate::{
    PrimitiveError, PrimitiveFloat, PrimitiveInteger, PrimitiveNumber, PrimitiveSigned,
    PrimitiveUnsigned,
};

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
    // `PrimitiveNumber` is not specific about the `FromStr` error type,
    // only constraining that it implements `PrimitiveError`.
    fn check<T: PrimitiveNumber>(s: &str, ok: T) {
        check_result(s.parse(), ok);
    }
    check("0", 0u32);
}

#[test]
fn parse_float() {
    // `PrimitiveFloat` is specific about the `FromStr` error type.
    fn check<T: PrimitiveFloat>(s: &str, ok: T) {
        let r: Result<T, ParseFloatError> = s.parse();
        assert_eq!(r, Ok(ok));
    }
    check("0", 0f32);
}

#[test]
fn parse_int() {
    // `PrimitiveInteger` is specific about the `FromStr` error type.
    fn check<T: PrimitiveInteger>(s: &str, ok: T) {
        let r: Result<T, ParseIntError> = s.parse();
        assert_eq!(r, Ok(ok));
    }
    check("0", 0u32);
}

#[test]
fn try_from() {
    // `PrimitiveInteger` is not specific about the `TryFrom` error type,
    // only constraining that it implements `PrimitiveError`.
    fn check<T: PrimitiveInteger>(x: i32, ok: T) {
        check_result(T::try_from(x), ok);
    }
    check(0i32, 0u32);
}

#[test]
fn try_from_signed() {
    // `PrimitiveSigned` is specific that `TryFrom<i8>` is infallible.
    // (implied by `From<i8>`, but we still need an explicit constraint)
    fn check<T: PrimitiveSigned>(x: i8, ok: T) {
        let r: Result<T, Infallible> = T::try_from(x);
        assert_eq!(r, Ok(ok));
    }
    check(0i8, 0i32);
}

#[test]
fn try_from_unsigned() {
    // `PrimitiveUnsigned` is specific that `TryFrom<u8>` is infallible.
    // (implied by `From<u8>`, but we still need an explicit constraint)
    fn check<T: PrimitiveUnsigned>(x: u8, ok: T) {
        let r: Result<T, Infallible> = T::try_from(x);
        assert_eq!(r, Ok(ok));
    }
    check(0u8, 0u32);
}

#[test]
fn try_into() {
    // `PrimitiveInteger` is not specific about the `TryInto` error type,
    // only constraining that it implements `PrimitiveError`.
    fn check<T: PrimitiveInteger>(x: T, ok: u32) {
        check_result(x.try_into(), ok);
    }
    check(0i32, 0u32);
}
