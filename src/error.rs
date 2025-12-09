use core::error::Error;

trait Sealed {}

/// Trait for errors that may be returned in numeric conversions.
///
/// In particular, this is used as a bound for the associated error types of
/// [`FromStr`][core::str::FromStr], [`TryFrom`], and [`TryInto`] in the supertraits of other
/// primitive traits in this crate. This is not exhaustive of everything these errors have in
/// common, but it's sufficient for:
///
/// * `Result::clone()`
/// * `Result::eq()` (i.e. `PartialEq`)
/// * `Result::unwrap()` (i.e. `Debug`)
/// * `From<E> for Box<dyn Error + 'a>`
/// * `From<E> for Box<dyn Error + Send + Sync + 'a>`
///
/// This trait is sealed with a private trait to prevent downstream implementations, so we may
/// continue to expand along with the standard library without worrying about breaking changes for
/// implementors.
#[expect(private_bounds)]
pub trait PrimitiveError: 'static + Sealed + Clone + PartialEq + Error + Send + Sync {}

impl Sealed for core::convert::Infallible {}
impl PrimitiveError for core::convert::Infallible {}

impl Sealed for core::num::ParseIntError {}
impl PrimitiveError for core::num::ParseIntError {}

impl Sealed for core::num::ParseFloatError {}
impl PrimitiveError for core::num::ParseFloatError {}

impl Sealed for core::num::TryFromIntError {}
impl PrimitiveError for core::num::TryFromIntError {}
