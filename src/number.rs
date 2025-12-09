use crate::PrimitiveError;

trait Sealed {}

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
    type Bytes: core::borrow::Borrow<[u8]> + core::borrow::BorrowMut<[u8]>;

    /// Creates a value from its representation as a byte array in big endian.
    fn from_be_bytes(bytes: Self::Bytes) -> Self;

    /// Creates a value from its representation as a byte array in little endian.
    fn from_le_bytes(bytes: Self::Bytes) -> Self;

    /// Creates a value from its representation as a byte array in native endian.
    fn from_ne_bytes(bytes: Self::Bytes) -> Self;

    /// Returns the memory representation of this number as a byte array in little-endian order.
    fn to_be_bytes(self) -> Self::Bytes;

    /// Returns the memory representation of this number as a byte array in big-endian order.
    fn to_le_bytes(self) -> Self::Bytes;

    /// Returns the memory representation of this number as a byte array in native-endian order.
    fn to_ne_bytes(self) -> Self::Bytes;
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

macro_rules! impl_primitive {
    ($($Number:ident),*) => {$(
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
                fn to_be_bytes(self) -> Self::Bytes;
                fn to_le_bytes(self) -> Self::Bytes;
                fn to_ne_bytes(self) -> Self::Bytes;
            }
        }

        impl PrimitiveNumberRef<$Number> for &$Number {}
    )*}
}

impl_primitive!(f32, f64);
impl_primitive!(i8, i16, i32, i64, i128, isize);
impl_primitive!(u8, u16, u32, u64, u128, usize);
