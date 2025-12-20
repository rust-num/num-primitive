use core::num::ParseIntError;

use crate::{PrimitiveError, PrimitiveNumber, PrimitiveNumberRef};

/// Trait for all primitive [integer types], including the supertrait [`PrimitiveNumber`].
///
/// This encapsulates trait implementations, constants, and inherent methods that are common among
/// all of the primitive integer types: [`i8`], [`i16`], [`i32`], [`i64`], [`i128`], [`isize`],
/// [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and [`usize`].
///
/// See the corresponding items on the individual types for more documentation and examples.
///
/// This trait is sealed with a private trait to prevent downstream implementations, so we may
/// continue to expand along with the standard library without worrying about breaking changes for
/// implementors.
///
/// [integer types]: https://doc.rust-lang.org/reference/types/numeric.html#r-type.numeric.int
///
/// # Examples
///
/// ```
/// use num_primitive::PrimitiveInteger;
///
/// fn div_rem<T: PrimitiveInteger>(a: T, b: T) -> (T, T) {
///     (a / b, a % b)
/// }
///
/// fn div_rem_euclid<T: PrimitiveInteger>(a: T, b: T) -> (T, T) {
///     (a.div_euclid(b), a.rem_euclid(b))
/// }
///
/// assert_eq!(div_rem::<u8>(48, 18), (2, 12));
/// assert_eq!(div_rem::<i8>(-48, 18), (-2, -12));
///
/// assert_eq!(div_rem_euclid::<u8>(48, 18), (2, 12));
/// assert_eq!(div_rem_euclid::<i8>(-48, 18), (-3, 6));
/// ```
///
pub trait PrimitiveInteger:
    PrimitiveNumber
    + core::cmp::Eq
    + core::cmp::Ord
    + core::convert::TryFrom<i8, Error: PrimitiveError>
    + core::convert::TryFrom<i16, Error: PrimitiveError>
    + core::convert::TryFrom<i32, Error: PrimitiveError>
    + core::convert::TryFrom<i64, Error: PrimitiveError>
    + core::convert::TryFrom<i128, Error: PrimitiveError>
    + core::convert::TryFrom<isize, Error: PrimitiveError>
    + core::convert::TryFrom<u8, Error: PrimitiveError>
    + core::convert::TryFrom<u16, Error: PrimitiveError>
    + core::convert::TryFrom<u32, Error: PrimitiveError>
    + core::convert::TryFrom<u64, Error: PrimitiveError>
    + core::convert::TryFrom<u128, Error: PrimitiveError>
    + core::convert::TryFrom<usize, Error: PrimitiveError>
    + core::convert::TryInto<i8, Error: PrimitiveError>
    + core::convert::TryInto<i16, Error: PrimitiveError>
    + core::convert::TryInto<i32, Error: PrimitiveError>
    + core::convert::TryInto<i64, Error: PrimitiveError>
    + core::convert::TryInto<i128, Error: PrimitiveError>
    + core::convert::TryInto<isize, Error: PrimitiveError>
    + core::convert::TryInto<u8, Error: PrimitiveError>
    + core::convert::TryInto<u16, Error: PrimitiveError>
    + core::convert::TryInto<u32, Error: PrimitiveError>
    + core::convert::TryInto<u64, Error: PrimitiveError>
    + core::convert::TryInto<u128, Error: PrimitiveError>
    + core::convert::TryInto<usize, Error: PrimitiveError>
    + core::fmt::Binary
    + core::fmt::LowerHex
    + core::fmt::Octal
    + core::fmt::UpperHex
    + core::hash::Hash
    + core::ops::BitAnd<Self, Output = Self>
    + core::ops::BitAndAssign<Self>
    + core::ops::BitOr<Self, Output = Self>
    + core::ops::BitOrAssign<Self>
    + core::ops::BitXor<Self, Output = Self>
    + core::ops::BitXorAssign<Self>
    + core::ops::Not<Output = Self>
    + core::ops::Shl<Self, Output = Self>
    + core::ops::Shl<i8, Output = Self>
    + core::ops::Shl<i16, Output = Self>
    + core::ops::Shl<i32, Output = Self>
    + core::ops::Shl<i64, Output = Self>
    + core::ops::Shl<i128, Output = Self>
    + core::ops::Shl<isize, Output = Self>
    + core::ops::Shl<u8, Output = Self>
    + core::ops::Shl<u16, Output = Self>
    + core::ops::Shl<u32, Output = Self>
    + core::ops::Shl<u64, Output = Self>
    + core::ops::Shl<u128, Output = Self>
    + core::ops::Shl<usize, Output = Self>
    + core::ops::ShlAssign<Self>
    + core::ops::ShlAssign<i8>
    + core::ops::ShlAssign<i16>
    + core::ops::ShlAssign<i32>
    + core::ops::ShlAssign<i64>
    + core::ops::ShlAssign<i128>
    + core::ops::ShlAssign<isize>
    + core::ops::ShlAssign<u8>
    + core::ops::ShlAssign<u16>
    + core::ops::ShlAssign<u32>
    + core::ops::ShlAssign<u64>
    + core::ops::ShlAssign<u128>
    + core::ops::ShlAssign<usize>
    + core::ops::Shr<Self, Output = Self>
    + core::ops::Shr<i8, Output = Self>
    + core::ops::Shr<i16, Output = Self>
    + core::ops::Shr<i32, Output = Self>
    + core::ops::Shr<i64, Output = Self>
    + core::ops::Shr<i128, Output = Self>
    + core::ops::Shr<isize, Output = Self>
    + core::ops::Shr<u8, Output = Self>
    + core::ops::Shr<u16, Output = Self>
    + core::ops::Shr<u32, Output = Self>
    + core::ops::Shr<u64, Output = Self>
    + core::ops::Shr<u128, Output = Self>
    + core::ops::Shr<usize, Output = Self>
    + core::ops::ShrAssign<Self>
    + core::ops::ShrAssign<i8>
    + core::ops::ShrAssign<i16>
    + core::ops::ShrAssign<i32>
    + core::ops::ShrAssign<i64>
    + core::ops::ShrAssign<i128>
    + core::ops::ShrAssign<isize>
    + core::ops::ShrAssign<u8>
    + core::ops::ShrAssign<u16>
    + core::ops::ShrAssign<u32>
    + core::ops::ShrAssign<u64>
    + core::ops::ShrAssign<u128>
    + core::ops::ShrAssign<usize>
    + for<'a> core::ops::BitAnd<&'a Self, Output = Self>
    + for<'a> core::ops::BitAndAssign<&'a Self>
    + for<'a> core::ops::BitOr<&'a Self, Output = Self>
    + for<'a> core::ops::BitOrAssign<&'a Self>
    + for<'a> core::ops::BitXor<&'a Self, Output = Self>
    + for<'a> core::ops::BitXorAssign<&'a Self>
    + for<'a> core::ops::Shl<&'a Self, Output = Self>
    + for<'a> core::ops::Shl<&'a i8, Output = Self>
    + for<'a> core::ops::Shl<&'a i16, Output = Self>
    + for<'a> core::ops::Shl<&'a i32, Output = Self>
    + for<'a> core::ops::Shl<&'a i64, Output = Self>
    + for<'a> core::ops::Shl<&'a i128, Output = Self>
    + for<'a> core::ops::Shl<&'a isize, Output = Self>
    + for<'a> core::ops::Shl<&'a u8, Output = Self>
    + for<'a> core::ops::Shl<&'a u16, Output = Self>
    + for<'a> core::ops::Shl<&'a u32, Output = Self>
    + for<'a> core::ops::Shl<&'a u64, Output = Self>
    + for<'a> core::ops::Shl<&'a u128, Output = Self>
    + for<'a> core::ops::Shl<&'a usize, Output = Self>
    + for<'a> core::ops::ShlAssign<&'a Self>
    + for<'a> core::ops::ShlAssign<&'a i8>
    + for<'a> core::ops::ShlAssign<&'a i16>
    + for<'a> core::ops::ShlAssign<&'a i32>
    + for<'a> core::ops::ShlAssign<&'a i64>
    + for<'a> core::ops::ShlAssign<&'a i128>
    + for<'a> core::ops::ShlAssign<&'a isize>
    + for<'a> core::ops::ShlAssign<&'a u8>
    + for<'a> core::ops::ShlAssign<&'a u16>
    + for<'a> core::ops::ShlAssign<&'a u32>
    + for<'a> core::ops::ShlAssign<&'a u64>
    + for<'a> core::ops::ShlAssign<&'a u128>
    + for<'a> core::ops::ShlAssign<&'a usize>
    + for<'a> core::ops::Shr<&'a Self, Output = Self>
    + for<'a> core::ops::Shr<&'a i8, Output = Self>
    + for<'a> core::ops::Shr<&'a i16, Output = Self>
    + for<'a> core::ops::Shr<&'a i32, Output = Self>
    + for<'a> core::ops::Shr<&'a i64, Output = Self>
    + for<'a> core::ops::Shr<&'a i128, Output = Self>
    + for<'a> core::ops::Shr<&'a isize, Output = Self>
    + for<'a> core::ops::Shr<&'a u8, Output = Self>
    + for<'a> core::ops::Shr<&'a u16, Output = Self>
    + for<'a> core::ops::Shr<&'a u32, Output = Self>
    + for<'a> core::ops::Shr<&'a u64, Output = Self>
    + for<'a> core::ops::Shr<&'a u128, Output = Self>
    + for<'a> core::ops::Shr<&'a usize, Output = Self>
    + for<'a> core::ops::ShrAssign<&'a Self>
    + for<'a> core::ops::ShrAssign<&'a i8>
    + for<'a> core::ops::ShrAssign<&'a i16>
    + for<'a> core::ops::ShrAssign<&'a i32>
    + for<'a> core::ops::ShrAssign<&'a i64>
    + for<'a> core::ops::ShrAssign<&'a i128>
    + for<'a> core::ops::ShrAssign<&'a isize>
    + for<'a> core::ops::ShrAssign<&'a u8>
    + for<'a> core::ops::ShrAssign<&'a u16>
    + for<'a> core::ops::ShrAssign<&'a u32>
    + for<'a> core::ops::ShrAssign<&'a u64>
    + for<'a> core::ops::ShrAssign<&'a u128>
    + for<'a> core::ops::ShrAssign<&'a usize>
{
    /// The size of this integer type in bits.
    const BITS: u32;

    /// The largest value that can be represented by this integer type.
    const MAX: Self;

    /// The smallest value that can be represented by this integer type.
    const MIN: Self;

    /// Checked integer addition. Computes `self + rhs`, returning `None` if overflow occurred.
    fn checked_add(self, rhs: Self) -> Option<Self>;

    /// Checked integer division. Computes `self / rhs`, returning `None` if `rhs == 0` or the
    /// division results in overflow.
    fn checked_div(self, rhs: Self) -> Option<Self>;

    /// Checked Euclidean division. Computes `self.div_euclid(rhs)`, returning `None` if `rhs == 0`
    /// or the division results in overflow.
    fn checked_div_euclid(self, rhs: Self) -> Option<Self>;

    /// Returns the logarithm of the number with respect to an arbitrary base, rounded down.
    /// Returns `None` if the number is negative or zero, or if the base is not at least 2.
    fn checked_ilog(self, base: Self) -> Option<u32>;

    /// Returns the base 10 logarithm of the number, rounded down. Returns `None` if the number is
    /// negative or zero.
    fn checked_ilog10(self) -> Option<u32>;

    /// Returns the base 2 logarithm of the number, rounded down. Returns `None` if the number is
    /// negative or zero.
    fn checked_ilog2(self) -> Option<u32>;

    /// Checked integer multiplication. Computes `self * rhs`, returning `None` if overflow
    /// occurred.
    fn checked_mul(self, rhs: Self) -> Option<Self>;

    /// Checked negation. Computes -self, returning `None` if `self == MIN`.
    fn checked_neg(self) -> Option<Self>;

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None` if overflow occurred.
    fn checked_pow(self, exp: u32) -> Option<Self>;

    /// Checked integer remainder. Computes `self % rhs`, returning `None` if `rhs == 0` or the
    /// division results in overflow.
    fn checked_rem(self, rhs: Self) -> Option<Self>;

    /// Checked Euclidean remainder. Computes `self.rem_euclid(rhs)`, returning `None` if `rhs ==
    /// 0` or the division results in overflow.
    fn checked_rem_euclid(self, rhs: Self) -> Option<Self>;

    /// Checked shift left. Computes `self << rhs`, returning `None` if `rhs` is larger than or
    /// equal to the number of bits in `self`.
    fn checked_shl(self, rhs: u32) -> Option<Self>;

    /// Checked shift right. Computes `self >> rhs`, returning `None` if `rhs` is larger than or
    /// equal to the number of bits in `self`.
    fn checked_shr(self, rhs: u32) -> Option<Self>;

    /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow occurred.
    fn checked_sub(self, rhs: Self) -> Option<Self>;

    /// Returns the number of ones in the binary representation of `self`.
    fn count_ones(self) -> u32;

    /// Returns the number of zeros in the binary representation of `self`.
    fn count_zeros(self) -> u32;

    /// Calculates the quotient of Euclidean division of `self` by `rhs`. This computes the integer
    /// `q` such that `self = q * rhs + r`, with `r = self.rem_euclid(rhs)` and `0 <= r <
    /// abs(rhs)`.
    fn div_euclid(self, rhs: Self) -> Self;

    /// Converts an integer from big endian to the target's endianness.
    fn from_be(value: Self) -> Self;

    /// Converts an integer from little endian to the target's endianness.
    fn from_le(value: Self) -> Self;

    /// Parses an integer from a string slice with digits in a given base.
    fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError>;

    /// Returns the logarithm of the number with respect to an arbitrary base, rounded down.
    fn ilog(self, base: Self) -> u32;

    /// Returns the base 10 logarithm of the number, rounded down.
    fn ilog10(self) -> u32;

    /// Returns the base 2 logarithm of the number, rounded down.
    fn ilog2(self) -> u32;

    /// Returns the square root of the number, rounded down.
    fn isqrt(self) -> Self;

    /// Returns the number of leading ones in the binary representation of `self`.
    fn leading_ones(self) -> u32;

    /// Returns the number of leading zeros in the binary representation of `self`.
    fn leading_zeros(self) -> u32;

    /// Calculates `self + rhs`. Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur.
    fn overflowing_add(self, rhs: Self) -> (Self, bool);

    /// Calculates the divisor when `self` is divided by `rhs`. Returns a tuple of the divisor
    /// along with a boolean indicating whether an arithmetic overflow would occur.
    fn overflowing_div(self, rhs: Self) -> (Self, bool);

    /// Calculates the quotient of Euclidean division `self`.div_euclid(rhs). Returns a tuple of
    /// the divisor along with a boolean indicating whether an arithmetic overflow would occur.
    fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool);

    /// Calculates the multiplication of `self` and `rhs`. Returns a tuple of the multiplication
    /// along with a boolean indicating whether an arithmetic overflow would occur.
    fn overflowing_mul(self, rhs: Self) -> (Self, bool);

    /// Negates self, overflowing if this is equal to the minimum value. Returns a tuple of the
    /// negated version of `self` along with a boolean indicating whether an overflow happened.
    fn overflowing_neg(self) -> (Self, bool);

    /// Raises `self` to the power of `exp`, using exponentiation by squaring. Returns a tuple of
    /// the exponentiation along with a bool indicating whether an overflow happened.
    fn overflowing_pow(self, exp: u32) -> (Self, bool);

    /// Calculates the remainder when `self` is divided by `rhs`. Returns a tuple of the remainder
    /// after dividing along with a boolean indicating whether an arithmetic overflow would occur.
    fn overflowing_rem(self, rhs: Self) -> (Self, bool);

    /// Overflowing Euclidean remainder. Calculates `self`.rem_euclid(rhs). Returns a tuple of the
    /// remainder after dividing along with a boolean indicating whether an arithmetic overflow
    /// would occur.
    fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool);

    /// Shifts `self` left by `rhs` bits. Returns a tuple of the shifted version of `self` along
    /// with a boolean indicating whether the shift value was larger than or equal to the number of
    /// bits.
    fn overflowing_shl(self, rhs: u32) -> (Self, bool);

    /// Shifts `self` right by `rhs` bits. Returns a tuple of the shifted version of `self` along
    /// with a boolean indicating whether the shift value was larger than or equal to the number of
    /// bits.
    fn overflowing_shr(self, rhs: u32) -> (Self, bool);

    /// Calculates `self - rhs`. Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur.
    fn overflowing_sub(self, rhs: Self) -> (Self, bool);

    /// Raises `self` to the power of `exp`, using exponentiation by squaring.
    fn pow(self, exp: u32) -> Self;

    /// Calculates the least nonnegative remainder of `self (mod rhs)`. This is done as if by the
    /// Euclidean division algorithm – given `r = self.rem_euclid(rhs)`, the result satisfies `self
    /// = rhs * self.div_euclid(rhs) + r` and `0 <= r < abs(rhs)`.
    fn rem_euclid(self, rhs: Self) -> Self;

    /// Reverses the order of bits in the integer.
    fn reverse_bits(self) -> Self;

    /// Shifts the bits to the left by a specified amount, n, wrapping the truncated bits to the
    /// end of the resulting integer.
    fn rotate_left(self, n: u32) -> Self;

    /// Shifts the bits to the right by a specified amount, n, wrapping the truncated bits to the
    /// beginning of the resulting integer.
    fn rotate_right(self, n: u32) -> Self;

    /// Saturating integer addition. Computes `self + rhs`, saturating at the numeric bounds
    /// instead of overflowing.
    fn saturating_add(self, rhs: Self) -> Self;

    /// Saturating integer division. Computes `self / rhs`, saturating at the numeric bounds
    /// instead of overflowing.
    fn saturating_div(self, rhs: Self) -> Self;

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at the numeric bounds
    /// instead of overflowing.
    fn saturating_mul(self, rhs: Self) -> Self;

    /// Saturating integer exponentiation. Computes `self.pow(exp)`, saturating at the numeric
    /// bounds instead of overflowing.
    fn saturating_pow(self, exp: u32) -> Self;

    /// Saturating integer subtraction. Computes `self - rhs`, saturating at the numeric bounds
    /// instead of overflowing.
    fn saturating_sub(self, rhs: Self) -> Self;

    /// Reverses the byte order of the integer.
    fn swap_bytes(self) -> Self;

    /// Converts `self` to big endian from the target's endianness.
    fn to_be(self) -> Self;

    /// Converts `self` to little endian from the target's endianness.
    fn to_le(self) -> Self;

    /// Returns the number of trailing ones in the binary representation of `self`.
    fn trailing_ones(self) -> u32;

    /// Returns the number of trailing zeros in the binary representation of `self`.
    fn trailing_zeros(self) -> u32;

    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the boundary of the
    /// type.
    fn wrapping_add(self, rhs: Self) -> Self;

    /// Wrapping (modular) division. Computes `self / rhs`, wrapping around at the boundary of the
    /// type.
    fn wrapping_div(self, rhs: Self) -> Self;

    /// Wrapping Euclidean division. Computes `self.div_euclid(rhs)`, wrapping around at the
    /// boundary of the type.
    fn wrapping_div_euclid(self, rhs: Self) -> Self;

    /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping around at the boundary
    /// of the type.
    fn wrapping_mul(self, rhs: Self) -> Self;

    /// Wrapping (modular) negation. Computes `-self`, wrapping around at the boundary of the type.
    fn wrapping_neg(self) -> Self;

    /// Wrapping (modular) exponentiation. Computes `self.pow(exp)`, wrapping around at the
    /// boundary of the type.
    fn wrapping_pow(self, exp: u32) -> Self;

    /// Wrapping (modular) remainder. Computes `self % rhs`, wrapping around at the boundary of the
    /// type.
    fn wrapping_rem(self, rhs: Self) -> Self;

    /// Wrapping Euclidean remainder. Computes `self.rem_euclid(rhs)`, wrapping around at the
    /// boundary of the type.
    fn wrapping_rem_euclid(self, rhs: Self) -> Self;

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`, where mask removes any
    /// high-order bits of `rhs` that would cause the shift to exceed the bitwidth of the type.
    fn wrapping_shl(self, rhs: u32) -> Self;

    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`, where mask removes any
    /// high-order bits of `rhs` that would cause the shift to exceed the bitwidth of the type.
    fn wrapping_shr(self, rhs: u32) -> Self;

    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around at the boundary of
    /// the type.
    fn wrapping_sub(self, rhs: Self) -> Self;

    /// Unchecked integer addition. Computes `self + rhs`, assuming overflow cannot occur.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior when `self + rhs > Self::MAX` or `self + rhs <
    /// Self::MIN`, i.e. when [`checked_add`][Self::checked_add] would return `None`.
    unsafe fn unchecked_add(self, rhs: Self) -> Self;

    /// Unchecked integer multiplication. Computes `self * rhs`, assuming overflow cannot occur.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior when `self * rhs > Self::MAX` or `self * rhs <
    /// Self::MIN`, i.e. when [`checked_mul`][Self::checked_mul] would return `None`.
    unsafe fn unchecked_mul(self, rhs: Self) -> Self;

    /// Unchecked integer subtraction. Computes `self - rhs`, assuming overflow cannot occur.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior when `self - rhs > Self::MAX` or `self - rhs <
    /// Self::MIN`, i.e. when [`checked_sub`][Self::checked_sub] would return `None`.
    unsafe fn unchecked_sub(self, rhs: Self) -> Self;
}

/// Trait for references to primitive integer types ([`PrimitiveInteger`]).
///
/// This enables traits like the standard operators in generic code,
/// e.g. `where &T: PrimitiveIntegerRef<T>`.
pub trait PrimitiveIntegerRef<T>:
    PrimitiveNumberRef<T>
    + core::cmp::Eq
    + core::cmp::Ord
    + core::fmt::Binary
    + core::fmt::LowerHex
    + core::fmt::Octal
    + core::fmt::UpperHex
    + core::hash::Hash
    + core::ops::BitAnd<T, Output = T>
    + core::ops::BitOr<T, Output = T>
    + core::ops::BitXor<T, Output = T>
    + core::ops::Not<Output = T>
    + core::ops::Shl<T, Output = T>
    + core::ops::Shl<i8, Output = T>
    + core::ops::Shl<i16, Output = T>
    + core::ops::Shl<i32, Output = T>
    + core::ops::Shl<i64, Output = T>
    + core::ops::Shl<i128, Output = T>
    + core::ops::Shl<isize, Output = T>
    + core::ops::Shl<u8, Output = T>
    + core::ops::Shl<u16, Output = T>
    + core::ops::Shl<u32, Output = T>
    + core::ops::Shl<u64, Output = T>
    + core::ops::Shl<u128, Output = T>
    + core::ops::Shl<usize, Output = T>
    + core::ops::Shr<T, Output = T>
    + core::ops::Shr<i8, Output = T>
    + core::ops::Shr<i16, Output = T>
    + core::ops::Shr<i32, Output = T>
    + core::ops::Shr<i64, Output = T>
    + core::ops::Shr<i128, Output = T>
    + core::ops::Shr<isize, Output = T>
    + core::ops::Shr<u8, Output = T>
    + core::ops::Shr<u16, Output = T>
    + core::ops::Shr<u32, Output = T>
    + core::ops::Shr<u64, Output = T>
    + core::ops::Shr<u128, Output = T>
    + core::ops::Shr<usize, Output = T>
    + for<'a> core::ops::BitAnd<&'a T, Output = T>
    + for<'a> core::ops::BitOr<&'a T, Output = T>
    + for<'a> core::ops::BitXor<&'a T, Output = T>
    + for<'a> core::ops::Shl<&'a T, Output = T>
    + for<'a> core::ops::Shl<&'a i8, Output = T>
    + for<'a> core::ops::Shl<&'a i16, Output = T>
    + for<'a> core::ops::Shl<&'a i32, Output = T>
    + for<'a> core::ops::Shl<&'a i64, Output = T>
    + for<'a> core::ops::Shl<&'a i128, Output = T>
    + for<'a> core::ops::Shl<&'a isize, Output = T>
    + for<'a> core::ops::Shl<&'a u8, Output = T>
    + for<'a> core::ops::Shl<&'a u16, Output = T>
    + for<'a> core::ops::Shl<&'a u32, Output = T>
    + for<'a> core::ops::Shl<&'a u64, Output = T>
    + for<'a> core::ops::Shl<&'a u128, Output = T>
    + for<'a> core::ops::Shl<&'a usize, Output = T>
    + for<'a> core::ops::Shr<&'a T, Output = T>
    + for<'a> core::ops::Shr<&'a i8, Output = T>
    + for<'a> core::ops::Shr<&'a i16, Output = T>
    + for<'a> core::ops::Shr<&'a i32, Output = T>
    + for<'a> core::ops::Shr<&'a i64, Output = T>
    + for<'a> core::ops::Shr<&'a i128, Output = T>
    + for<'a> core::ops::Shr<&'a isize, Output = T>
    + for<'a> core::ops::Shr<&'a u8, Output = T>
    + for<'a> core::ops::Shr<&'a u16, Output = T>
    + for<'a> core::ops::Shr<&'a u32, Output = T>
    + for<'a> core::ops::Shr<&'a u64, Output = T>
    + for<'a> core::ops::Shr<&'a u128, Output = T>
    + for<'a> core::ops::Shr<&'a usize, Output = T>
{
}

macro_rules! impl_integer {
    ($($Integer:ident),*) => {$(
        impl PrimitiveInteger for $Integer {
            use_consts!(Self::{
                BITS: u32,
                MAX: Self,
                MIN: Self,
            });

            forward! {
                fn from_be(value: Self) -> Self;
                fn from_le(value: Self) -> Self;
                fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError>;
            }
            forward! {
                fn checked_add(self, rhs: Self) -> Option<Self>;
                fn checked_div(self, rhs: Self) -> Option<Self>;
                fn checked_div_euclid(self, rhs: Self) -> Option<Self>;
                fn checked_ilog(self, base: Self) -> Option<u32>;
                fn checked_ilog10(self) -> Option<u32>;
                fn checked_ilog2(self) -> Option<u32>;
                fn checked_mul(self, rhs: Self) -> Option<Self>;
                fn checked_neg(self) -> Option<Self>;
                fn checked_pow(self, exp: u32) -> Option<Self>;
                fn checked_rem(self, rhs: Self) -> Option<Self>;
                fn checked_rem_euclid(self, rhs: Self) -> Option<Self>;
                fn checked_shl(self, rhs: u32) -> Option<Self>;
                fn checked_shr(self, rhs: u32) -> Option<Self>;
                fn checked_sub(self, rhs: Self) -> Option<Self>;
                fn count_ones(self) -> u32;
                fn count_zeros(self) -> u32;
                fn div_euclid(self, rhs: Self) -> Self;
                fn ilog(self, base: Self) -> u32;
                fn ilog10(self) -> u32;
                fn ilog2(self) -> u32;
                fn isqrt(self) -> Self;
                fn leading_ones(self) -> u32;
                fn leading_zeros(self) -> u32;
                fn overflowing_add(self, rhs: Self) -> (Self, bool);
                fn overflowing_div(self, rhs: Self) -> (Self, bool);
                fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool);
                fn overflowing_mul(self, rhs: Self) -> (Self, bool);
                fn overflowing_neg(self) -> (Self, bool);
                fn overflowing_pow(self, exp: u32) -> (Self, bool);
                fn overflowing_rem(self, rhs: Self) -> (Self, bool);
                fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool);
                fn overflowing_shl(self, rhs: u32) -> (Self, bool);
                fn overflowing_shr(self, rhs: u32) -> (Self, bool);
                fn overflowing_sub(self, rhs: Self) -> (Self, bool);
                fn pow(self, exp: u32) -> Self;
                fn rem_euclid(self, rhs: Self) -> Self;
                fn reverse_bits(self) -> Self;
                fn rotate_left(self, n: u32) -> Self;
                fn rotate_right(self, n: u32) -> Self;
                fn saturating_add(self, rhs: Self) -> Self;
                fn saturating_div(self, rhs: Self) -> Self;
                fn saturating_mul(self, rhs: Self) -> Self;
                fn saturating_pow(self, exp: u32) -> Self;
                fn saturating_sub(self, rhs: Self) -> Self;
                fn swap_bytes(self) -> Self;
                fn to_be(self) -> Self;
                fn to_le(self) -> Self;
                fn trailing_ones(self) -> u32;
                fn trailing_zeros(self) -> u32;
                fn wrapping_add(self, rhs: Self) -> Self;
                fn wrapping_div(self, rhs: Self) -> Self;
                fn wrapping_div_euclid(self, rhs: Self) -> Self;
                fn wrapping_mul(self, rhs: Self) -> Self;
                fn wrapping_neg(self) -> Self;
                fn wrapping_pow(self, exp: u32) -> Self;
                fn wrapping_rem(self, rhs: Self) -> Self;
                fn wrapping_rem_euclid(self, rhs: Self) -> Self;
                fn wrapping_shl(self, rhs: u32) -> Self;
                fn wrapping_shr(self, rhs: u32) -> Self;
                fn wrapping_sub(self, rhs: Self) -> Self;
            }
            forward! {
                unsafe fn unchecked_add(self, rhs: Self) -> Self;
                unsafe fn unchecked_mul(self, rhs: Self) -> Self;
                unsafe fn unchecked_sub(self, rhs: Self) -> Self;
            }
        }

        impl PrimitiveIntegerRef<$Integer> for &$Integer {}
    )*}
}

impl_integer!(i8, i16, i32, i64, i128, isize);
impl_integer!(u8, u16, u32, u64, u128, usize);
