use crate::{PrimitiveBytes, PrimitiveError};

trait Sealed {}
struct SealedToken;

/// Trait for all primitive [numeric types].
///
/// This encapsulates trait implementations and inherent methods that are common among all of the
/// primitive numeric types: [`f32`], [`f64`], [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
/// [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and [`usize`]. Unstable types like
/// [`f16`] and [`f128`] will be added once they are stabilized.
///
/// See the corresponding items on the individual types for more documentation and examples.
///
/// This trait is sealed with a private trait to prevent downstream implementations, so we may
/// continue to expand along with the standard library without worrying about breaking changes for
/// implementors.
///
/// [numeric types]: https://doc.rust-lang.org/reference/types/numeric.html
///
/// # Examples
///
/// ```
/// use num_primitive::{PrimitiveNumber, PrimitiveNumberRef};
///
/// fn dot_product<T: PrimitiveNumber>(a: &[T], b: &[T]) -> T {
///     assert_eq!(a.len(), b.len());
///     // Note that we have to dereference to use `T: Mul<&T>`
///     core::iter::zip(a, b).map(|(a, b)| (*a) * b).sum()
/// }
///
/// fn dot_product_ref<T>(a: &[T], b: &[T]) -> T
/// where
///     T: PrimitiveNumber,
///     for<'a> &'a T: PrimitiveNumberRef<T>,
/// {
///     assert_eq!(a.len(), b.len());
///     // In this case we can use `&T: Mul`
///     core::iter::zip(a, b).map(|(a, b)| a * b).sum()
/// }
///
/// assert_eq!(dot_product::<i32>(&[1, 3, -5], &[4, -2, -1]), 3);
/// assert_eq!(dot_product_ref::<f64>(&[1., 3., -5.], &[4., -2., -1.]), 3.);
/// ```
#[expect(private_bounds)]
pub trait PrimitiveNumber:
    'static
    + Sealed
    + PrimitiveNumberAs<f32>
    + PrimitiveNumberAs<f64>
    + PrimitiveNumberAs<i8>
    + PrimitiveNumberAs<i16>
    + PrimitiveNumberAs<i32>
    + PrimitiveNumberAs<i64>
    + PrimitiveNumberAs<i128>
    + PrimitiveNumberAs<isize>
    + PrimitiveNumberAs<u8>
    + PrimitiveNumberAs<u16>
    + PrimitiveNumberAs<u32>
    + PrimitiveNumberAs<u64>
    + PrimitiveNumberAs<u128>
    + PrimitiveNumberAs<usize>
    + core::cmp::PartialEq
    + core::cmp::PartialOrd
    + core::convert::From<bool>
    + core::default::Default
    + core::fmt::Debug
    + core::fmt::Display
    + core::fmt::LowerExp
    + core::fmt::UpperExp
    + core::iter::Product<Self>
    + core::iter::Sum<Self>
    + core::marker::Copy
    + core::marker::Send
    + core::marker::Sync
    + core::marker::Unpin
    + core::ops::Add<Self, Output = Self>
    + core::ops::AddAssign<Self>
    + core::ops::Div<Self, Output = Self>
    + core::ops::DivAssign<Self>
    + core::ops::Mul<Self, Output = Self>
    + core::ops::MulAssign<Self>
    + core::ops::Rem<Self, Output = Self>
    + core::ops::RemAssign<Self>
    + core::ops::Sub<Self, Output = Self>
    + core::ops::SubAssign<Self>
    + core::panic::RefUnwindSafe
    + core::panic::UnwindSafe
    + core::str::FromStr<Err: PrimitiveError>
    + for<'a> core::iter::Product<&'a Self>
    + for<'a> core::iter::Sum<&'a Self>
    + for<'a> core::ops::Add<&'a Self, Output = Self>
    + for<'a> core::ops::AddAssign<&'a Self>
    + for<'a> core::ops::Div<&'a Self, Output = Self>
    + for<'a> core::ops::DivAssign<&'a Self>
    + for<'a> core::ops::Mul<&'a Self, Output = Self>
    + for<'a> core::ops::MulAssign<&'a Self>
    + for<'a> core::ops::Rem<&'a Self, Output = Self>
    + for<'a> core::ops::RemAssign<&'a Self>
    + for<'a> core::ops::Sub<&'a Self, Output = Self>
    + for<'a> core::ops::SubAssign<&'a Self>
{
    /// An array of bytes used by methods like [`from_be_bytes`][Self::from_be_bytes] and
    /// [`to_be_bytes`][Self::to_be_bytes]. It is effectively `[u8; size_of::<Self>()]`.
    type Bytes: PrimitiveBytes;

    /// Creates a number from its representation as a byte array in big endian.
    fn from_be_bytes(bytes: Self::Bytes) -> Self;

    /// Creates a number from its representation as a byte array in little endian.
    fn from_le_bytes(bytes: Self::Bytes) -> Self;

    /// Creates a number from its representation as a byte array in native endian.
    fn from_ne_bytes(bytes: Self::Bytes) -> Self;

    /// Calculates the midpoint (average) between `self` and `other`.
    fn midpoint(self, other: Self) -> Self;

    /// Returns the memory representation of this number as a byte array in little-endian order.
    fn to_be_bytes(self) -> Self::Bytes;

    /// Returns the memory representation of this number as a byte array in big-endian order.
    fn to_le_bytes(self) -> Self::Bytes;

    /// Returns the memory representation of this number as a byte array in native-endian order.
    fn to_ne_bytes(self) -> Self::Bytes;

    /// Creates a number using a type cast, `value as Self`.
    ///
    /// Note: unlike other `num-primitive` methods, there is no inherent method by this name on the
    /// actual types.
    fn as_from<T>(value: T) -> Self
    where
        Self: PrimitiveNumberAs<T>,
    {
        <Self as PrimitiveNumberAs<T>>::__as_from(value, SealedToken)
    }

    /// Converts this number with a type cast, `self as T`.
    ///
    /// Note: unlike other `num-primitive` methods, there is no inherent method by this name on the
    /// actual types.
    fn as_to<T>(self) -> T
    where
        Self: PrimitiveNumberAs<T>,
    {
        <Self as PrimitiveNumberAs<T>>::__as_to(self, SealedToken)
    }
}

/// Trait for references to primitive numbers ([`PrimitiveNumber`]).
///
/// This enables traits like the standard operators in generic code,
/// e.g. `where &T: PrimitiveNumberRef<T>`.
#[expect(private_bounds)]
pub trait PrimitiveNumberRef<T>:
    Sealed
    + core::borrow::Borrow<T>
    + core::cmp::PartialEq
    + core::cmp::PartialOrd
    + core::fmt::Debug
    + core::fmt::Display
    + core::fmt::LowerExp
    + core::fmt::UpperExp
    + core::marker::Copy
    + core::marker::Send
    + core::marker::Sync
    + core::marker::Unpin
    + core::ops::Add<T, Output = T>
    + core::ops::Deref<Target = T>
    + core::ops::Div<T, Output = T>
    + core::ops::Mul<T, Output = T>
    + core::ops::Rem<T, Output = T>
    + core::ops::Sub<T, Output = T>
    + core::panic::RefUnwindSafe
    + core::panic::UnwindSafe
    + for<'a> core::ops::Add<&'a T, Output = T>
    + for<'a> core::ops::Div<&'a T, Output = T>
    + for<'a> core::ops::Mul<&'a T, Output = T>
    + for<'a> core::ops::Rem<&'a T, Output = T>
    + for<'a> core::ops::Sub<&'a T, Output = T>
{
}

/// Trait for numeric conversions supported by the [`as`] keyword.
///
/// This is effectively the same as the [type cast] expression `self as N`, implemented for all
/// combinations of [`PrimitiveNumber`].
///
/// [`as`]: https://doc.rust-lang.org/std/keyword.as.html
/// [type cast]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions
///
/// # Examples
///
/// `PrimitiveNumberAs<{number}>` is a supertrait of [`PrimitiveNumber`] for all primitive floats
/// and integers, so you do not need to use this trait directly when converting concrete types.
///
/// ```
/// use num_primitive::PrimitiveNumber;
///
/// // Clamp any number to the interval 0..=100, unless it is NaN.
/// fn clamp_percentage<Number: PrimitiveNumber>(x: Number) -> Number {
///     let clamped = x.as_to::<f64>().clamp(0.0, 100.0);
///     Number::as_from(clamped)
/// }
///
/// assert_eq!(clamp_percentage(-42_i8), 0_i8);
/// assert_eq!(clamp_percentage(42_u128), 42_u128);
/// assert_eq!(clamp_percentage(1e100_f64), 100_f64);
/// assert!(clamp_percentage(f32::NAN).is_nan());
/// ```
///
/// However, if the other type is also generic, an explicit type constraint is needed.
///
/// ```
/// use num_primitive::{PrimitiveNumber, PrimitiveNumberAs};
///
/// fn clamp_any<Number, Limit>(x: Number, min: Limit, max: Limit) -> Number
/// where
///     Number: PrimitiveNumber + PrimitiveNumberAs<Limit>,
///     Limit: PartialOrd,
/// {
///     assert!(min <= max);
///     let y = x.as_to::<Limit>();
///     if y <= min {
///         Number::as_from(min)
///     } else if y >= max {
///         Number::as_from(max)
///     } else {
///         x
///     }
/// }
///
/// assert_eq!(clamp_any(1.23, 0_i8, 10_i8), 1.23);
/// assert_eq!(clamp_any(1.23, -1_i8, 1_i8), 1.0);
/// assert_eq!(clamp_any(i128::MAX, 0.0, 1e100), i128::MAX);
/// ```
pub trait PrimitiveNumberAs<T> {
    #[doc(hidden)]
    #[expect(private_interfaces)]
    fn __as_from(x: T, _: SealedToken) -> Self;

    #[doc(hidden)]
    #[expect(private_interfaces)]
    fn __as_to(x: Self, _: SealedToken) -> T;
}

macro_rules! impl_primitive {
    ($($Number:ident),+) => {$(
        impl Sealed for $Number {}
        impl Sealed for &$Number {}

        impl PrimitiveNumber for $Number {
            type Bytes = [u8; size_of::<Self>()];

            forward! {
                fn from_be_bytes(bytes: Self::Bytes) -> Self;
                fn from_le_bytes(bytes: Self::Bytes) -> Self;
                fn from_ne_bytes(bytes: Self::Bytes) -> Self;
            }
            forward! {
                fn midpoint(self, other: Self) -> Self;
                fn to_be_bytes(self) -> Self::Bytes;
                fn to_le_bytes(self) -> Self::Bytes;
                fn to_ne_bytes(self) -> Self::Bytes;
            }
        }

        impl PrimitiveNumberRef<$Number> for &$Number {}

        impl_primitive!($Number as f32, f64);
        impl_primitive!($Number as i8, i16, i32, i64, i128, isize);
        impl_primitive!($Number as u8, u16, u32, u64, u128, usize);
    )+};

    ($Number:ident as $($Other:ident),+) => {$(
        impl PrimitiveNumberAs<$Other> for $Number {
            #[inline]
            #[expect(private_interfaces)]
            fn __as_from(x: $Other, _: SealedToken) -> Self {
                x as Self
            }

            #[inline]
            #[expect(private_interfaces)]
            fn __as_to(x: Self, _: SealedToken) -> $Other {
                x as $Other
            }
        }
    )+}
}

impl_primitive!(f32, f64);
impl_primitive!(i8, i16, i32, i64, i128, isize);
impl_primitive!(u8, u16, u32, u64, u128, usize);
