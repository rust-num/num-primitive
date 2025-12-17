use core::array::TryFromSliceError;

trait Sealed {}

/// Trait for arrays of bytes that may be used in numeric conversions.
///
/// In particular, this is used as a bound for the associated type
/// [`PrimitiveNumber::Bytes`][crate::PrimitiveNumber::Bytes] for converting numbers to and from an
/// array of bytes in various endian orders. It is simply `[u8; size_of::<Self>()]` for every
/// primitive number type, but there's no way yet to write that directly in the trait.
///
/// This trait is not exhaustive of everything byte arrays can do, but it's enough to be useful for
/// generically constructing bytes and dealing with them as slices.
///
/// This trait is sealed with a private trait to prevent downstream implementations, so we may
/// continue to expand along with the standard library without worrying about breaking changes for
/// implementors.
///
/// # Examples
///
/// The supertraits of `PrimitiveBytes` can be used without importing this trait directly:
///
/// ```
/// use num_primitive::PrimitiveNumber;
///
/// // Return a value with the most significant bit set
/// fn msb<T: PrimitiveNumber>() -> T {
///     let mut bytes = T::Bytes::default(); // prelude `Default`
///     bytes[0] = 0x80;                     // operator `IndexMut`
///     T::from_be_bytes(bytes)
/// }
///
/// assert_eq!(msb::<i64>(), i64::MIN);
/// assert_eq!(msb::<u16>(), 1u16 << 15);
/// assert!(msb::<f64>().total_cmp(&-0.0).is_eq());
/// ```
///
/// However, this trait must be imported to use its own methods like [`repeat`][Self::repeat]:
///
/// ```
/// use num_primitive::{PrimitiveBytes, PrimitiveNumber};
///
/// // Return a value with all bits set
/// fn all_ones<T: PrimitiveNumber>() -> T {
///     T::from_ne_bytes(T::Bytes::repeat(0xff))
/// }
///
/// assert_eq!(all_ones::<i32>(), -1);
/// assert_eq!(all_ones::<usize>(), usize::MAX);
/// assert!(all_ones::<f64>().is_nan());
/// ```
///
/// In cases where the size is known, you can use that as a constraint and then work with byte
/// arrays directly, regardless of this trait.
///
/// ```
/// use num_primitive::PrimitiveNumber;
///
/// fn rust<T: PrimitiveNumber<Bytes = [u8; 4]>>() -> T {
///     T::from_be_bytes(*b"Rust")
/// }
///
/// assert_eq!(rust::<i32>(), 0x52_75_73_74_i32);
/// assert_eq!(rust::<u32>(), 0x52_75_73_74_u32);
/// assert_eq!(rust::<f32>(), 2.63551e11);
/// ```
#[expect(private_bounds)]
pub trait PrimitiveBytes:
    'static
    + Sealed
    + core::borrow::Borrow<[u8]>
    + core::borrow::BorrowMut<[u8]>
    + core::cmp::Eq
    + core::cmp::Ord
    + core::cmp::PartialEq<[u8]>
    + core::convert::AsRef<[u8]>
    + core::convert::AsMut<[u8]>
    + core::default::Default
    + core::fmt::Debug
    + core::hash::Hash
    + core::marker::Copy
    + core::marker::Send
    + core::marker::Sync
    + core::marker::Unpin
    + core::ops::Index<usize, Output = u8>
    + core::ops::IndexMut<usize>
    + core::panic::RefUnwindSafe
    + core::panic::UnwindSafe
    + for<'a> core::cmp::PartialEq<&'a [u8]>
    + for<'a> core::cmp::PartialEq<&'a mut [u8]>
    + for<'a> core::convert::TryFrom<&'a [u8], Error = TryFromSliceError>
    + for<'a> core::convert::TryFrom<&'a mut [u8], Error = TryFromSliceError>
{
    /// Creates an array of bytes where each byte is produced by calling `f`
    /// with that element's index while walking forward through the array.
    ///
    /// See the [`core::array::from_fn`] function.
    fn from_fn<F>(f: F) -> Self
    where
        F: FnMut(usize) -> u8;

    /// Creates an array of bytes with a repeat expression, `[value; N]`.
    fn repeat(value: u8) -> Self;
}

macro_rules! impl_bytes {
    ($($N:literal),+) => {$(
        impl Sealed for [u8; $N] {}

        impl PrimitiveBytes for [u8; $N] {
            #[inline]
            fn from_fn<F>(f: F) -> Self
            where
                F: FnMut(usize) -> u8
            {
                core::array::from_fn(f)
            }

            #[inline]
            fn repeat(value: u8) -> Self {
                // We don't need to forward to `array::repeat` for cloning,
                // since we can construct it directly with `u8` copies.
                [value; $N]
            }
        }
    )+}
}

impl_bytes!(1, 2, 4, 8, 16);
