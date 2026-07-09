use core::convert::Infallible;
use core::num::NonZero;

use crate::{
    NonZeroPrimitiveInteger, NonZeroPrimitiveUnsigned, PrimitiveInteger, PrimitiveIntegerRef,
    PrimitiveUnsigned,
};

/// Trait for all primitive [signed integer types], including the supertraits [`PrimitiveInteger`]
/// and [`PrimitiveNumber`][crate::PrimitiveNumber].
///
/// This encapsulates trait implementations and inherent methods that are common among all of the
/// primitive signed integer types: [`i8`], [`i16`], [`i32`], [`i64`], [`i128`], and [`isize`].
///
/// See the corresponding items on the individual types for more documentation and examples.
///
/// This trait is sealed with a private trait to prevent downstream implementations, so we may
/// continue to expand along with the standard library without worrying about breaking changes for
/// implementors.
///
/// [signed integer types]: https://doc.rust-lang.org/reference/types/numeric.html#r-type.numeric.int.signed
///
/// # Examples
///
/// ```
/// use num_primitive::PrimitiveSigned;
///
/// // GCD with Bézout coefficients (extended Euclidean algorithm)
/// fn extended_gcd<T: PrimitiveSigned>(a: T, b: T) -> (T, T, T) {
///     let zero = T::from(0i8);
///     let one = T::from(1i8);
///
///     let (mut old_r, mut r) = (a, b);
///     let (mut old_s, mut s) = (one, zero);
///     let (mut old_t, mut t) = (zero, one);
///
///     while r != zero {
///         let quotient = old_r.div_euclid(r);
///         (old_r, r) = (r, old_r - quotient * r);
///         (old_s, s) = (s, old_s - quotient * s);
///         (old_t, t) = (t, old_t - quotient * t);
///     }
///
///     let (gcd, x, y) = if old_r.is_negative() {
///         (-old_r, -old_s, -old_t)
///     } else {
///         (old_r, old_s, old_t)
///     };
///     assert_eq!(gcd, a * x + b * y);
///     (gcd, x, y)
/// }
///
/// assert_eq!(extended_gcd::<i8>(0, -42), (42, 0, -1));
/// assert_eq!(extended_gcd::<i8>(48, 18), (6, -1, 3));
/// assert_eq!(extended_gcd::<i16>(1071, -462), (21, -3, -7));
/// assert_eq!(extended_gcd::<i64>(6_700_417, 2_147_483_647), (1, 715_828_096, -2_233_473));
/// ```
pub trait PrimitiveSigned:
    PrimitiveInteger
    + core::convert::From<i8>
    + core::convert::TryFrom<i8, Error = Infallible>
    + core::ops::Neg<Output = Self>
{
    /// The unsigned integer type used by methods like [`abs_diff`][Self::abs_diff] and
    /// [`checked_add_unsigned`][Self::checked_add_unsigned].
    type Unsigned: PrimitiveUnsigned;

    /// Computes the absolute value of `self`.
    fn abs(self) -> Self;

    /// Computes the absolute difference between `self` and `other`.
    fn abs_diff(self, other: Self) -> Self::Unsigned;

    /// Returns the bit pattern of `self` reinterpreted as an unsigned integer of the same size.
    fn cast_unsigned(self) -> Self::Unsigned;

    /// Checked absolute value. Computes `self.abs()`, returning `None` if `self == MIN`.
    fn checked_abs(self) -> Option<Self>;

    /// Checked addition with an unsigned integer. Computes `self + rhs`, returning `None` if
    /// overflow occurred.
    fn checked_add_unsigned(self, rhs: Self::Unsigned) -> Option<Self>;

    /// Returns the square root of the number, rounded down. Returns `None` if `self` is negative.
    fn checked_isqrt(self) -> Option<Self>;

    /// Checked subtraction with an unsigned integer. Computes `self - rhs`, returning `None` if
    /// overflow occurred.
    fn checked_sub_unsigned(self, rhs: Self::Unsigned) -> Option<Self>;

    /// Returns true if `self` is negative and false if the number is zero or positive.
    fn is_negative(self) -> bool;

    /// Returns true if `self` is positive and false if the number is zero or negative.
    fn is_positive(self) -> bool;

    /// Computes the absolute value of `self`. Returns a tuple of the absolute version of `self`
    /// along with a boolean indicating whether an overflow happened.
    fn overflowing_abs(self) -> (Self, bool);

    /// Calculates `self + rhs` with an unsigned `rhs`. Returns a tuple of the addition along with
    /// a boolean indicating whether an arithmetic overflow would occur.
    fn overflowing_add_unsigned(self, rhs: Self::Unsigned) -> (Self, bool);

    /// Calculates `self - rhs` with an unsigned `rhs`. Returns a tuple of the subtraction along
    /// with a boolean indicating whether an arithmetic overflow would occur.
    fn overflowing_sub_unsigned(self, rhs: Self::Unsigned) -> (Self, bool);

    /// Saturating absolute value. Computes `self.abs()`, returning `MAX` if `self == MIN` instead
    /// of overflowing.
    fn saturating_abs(self) -> Self;

    /// Saturating addition with an unsigned integer. Computes `self + rhs`, saturating at the
    /// numeric bounds instead of overflowing.
    fn saturating_add_unsigned(self, rhs: Self::Unsigned) -> Self;

    /// Saturating integer negation. Computes `-self`, returning `MAX` if `self == MIN` instead of
    /// overflowing.
    fn saturating_neg(self) -> Self;

    /// Saturating subtraction with an unsigned integer. Computes `self - rhs`, saturating at the
    /// numeric bounds instead of overflowing.
    fn saturating_sub_unsigned(self, rhs: Self::Unsigned) -> Self;

    /// Returns a number representing sign of `self`.
    fn signum(self) -> Self;

    /// Strict absolute value. Computes `self.abs()`, panicking if `self == MIN`.
    fn strict_abs(self) -> Self;

    /// Strict addition with an unsigned integer. Computes `self + rhs`,
    /// panicking if overflow occurred.
    fn strict_add_unsigned(self, rhs: Self::Unsigned) -> Self;

    /// Strict subtraction with an unsigned integer. Computes `self - rhs`,
    /// panicking if overflow occurred.
    fn strict_sub_unsigned(self, rhs: Self::Unsigned) -> Self;

    /// Computes the absolute value of `self` without any wrapping or panicking.
    fn unsigned_abs(self) -> Self::Unsigned;

    /// Wrapping (modular) absolute value. Computes `self.abs()`, wrapping around at the boundary
    /// of the type.
    fn wrapping_abs(self) -> Self;

    /// Wrapping (modular) addition with an unsigned integer. Computes `self + rhs`, wrapping
    /// around at the boundary of the type.
    fn wrapping_add_unsigned(self, rhs: Self::Unsigned) -> Self;

    /// Wrapping (modular) subtraction with an unsigned integer. Computes `self - rhs`, wrapping
    /// around at the boundary of the type.
    fn wrapping_sub_unsigned(self, rhs: Self::Unsigned) -> Self;

    /// Unchecked negation. Computes `-self`, assuming overflow cannot occur.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior when `self == Self::MIN`, i.e. when
    /// [`checked_neg`][PrimitiveInteger::checked_neg] would return `None`.
    unsafe fn unchecked_neg(self) -> Self;
}

/// Trait for references to primitive signed integer types ([`PrimitiveSigned`]).
///
/// This enables traits like the standard operators in generic code,
/// e.g. `where &T: PrimitiveSignedRef<T>`.
pub trait PrimitiveSignedRef<T>: PrimitiveIntegerRef<T> + core::ops::Neg<Output = T> {}

/// Trait for [`NonZero`] primitive signed integers, including the supertrait
/// [`NonZeroPrimitiveInteger`].
///
/// This encapsulates trait implementations and inherent methods that are common among all of the
/// implementations of `NonZero<T>`, where `T` is a [`PrimitiveSigned`].
///
/// See the corresponding items on the individual types for more documentation and examples.
///
/// This trait is sealed with a private trait to prevent downstream implementations, so we may
/// continue to expand along with the standard library without worrying about breaking changes for
/// implementors.
///
/// # Examples
///
/// ```
/// use num_primitive::NonZeroPrimitiveSigned;
/// use core::num::NonZero;
///
/// fn sign_and_magnitude<T: NonZeroPrimitiveSigned>(n: T) -> (bool, T::NonZeroUnsigned) {
///     (n.is_negative(), n.unsigned_abs())
/// }
///
/// let n = NonZero::new(-42i16).unwrap();
/// assert_eq!(sign_and_magnitude(n), (true, NonZero::new(42u16).unwrap()));
/// ```
pub trait NonZeroPrimitiveSigned:
    NonZeroPrimitiveInteger<Integer: PrimitiveSigned>
    + core::convert::From<NonZero<i8>>
    + core::ops::Neg<Output = Self>
{
    /// The unsigned non-zero integer type used by methods like
    /// [`cast_unsigned`][Self::cast_unsigned].
    ///
    /// For `core::num::NonZero<T>`, this is `NonZero<T::Unsigned>`.
    type NonZeroUnsigned: NonZeroPrimitiveUnsigned;

    /// Computes the absolute value of self.
    fn abs(self) -> Self;

    /// Returns the bit pattern of `self` reinterpreted as an unsigned integer of the same size.
    fn cast_unsigned(self) -> Self::NonZeroUnsigned;

    /// Checked absolute value. Checks for overflow and returns [`None`] if `self == Self::MIN`.
    fn checked_abs(self) -> Option<Self>;

    /// Checked negation. Computes `-self`, returning `None` if `self == Self::MIN`.
    fn checked_neg(self) -> Option<Self>;

    /// Returns `true` if `self` is positive and `false` if the number is negative.
    fn is_positive(self) -> bool;

    /// Returns `true` if `self` is negative and `false` if the number is positive.
    fn is_negative(self) -> bool;

    /// Computes the absolute value of self, with overflow information.
    fn overflowing_abs(self) -> (Self, bool);

    /// Negates self, overflowing if this is equal to the minimum value.
    fn overflowing_neg(self) -> (Self, bool);

    /// Saturating absolute value.
    fn saturating_abs(self) -> Self;

    /// Saturating negation. Computes `-self`, returning `Self::MAX`
    /// if `self == Self::MIN` instead of overflowing.
    fn saturating_neg(self) -> Self;

    /// Computes the absolute value of self without any wrapping or panicking.
    fn unsigned_abs(self) -> Self::NonZeroUnsigned;

    /// Wrapping absolute value.
    fn wrapping_abs(self) -> Self;

    /// Wrapping (modular) negation. Computes `-self`, wrapping around at the boundary
    /// of the type.
    fn wrapping_neg(self) -> Self;
}

// TODO: consider a NonZero*Ref hierarchy, including Neg here.
// pub trait NonZeroPrimitiveSignedRef<NZ>: core::ops::Neg<Output = NZ> {}

macro_rules! impl_signed {
    ($Signed:ident, $Unsigned:ty) => {
        impl PrimitiveSigned for $Signed {
            type Unsigned = $Unsigned;

            forward! {
                fn abs(self) -> Self;
                fn abs_diff(self, other: Self) -> Self::Unsigned;
                fn cast_unsigned(self) -> Self::Unsigned;
                fn checked_abs(self) -> Option<Self>;
                fn checked_add_unsigned(self, rhs: Self::Unsigned) -> Option<Self>;
                fn checked_isqrt(self) -> Option<Self>;
                fn checked_sub_unsigned(self, rhs: Self::Unsigned) -> Option<Self>;
                fn is_negative(self) -> bool;
                fn is_positive(self) -> bool;
                fn overflowing_abs(self) -> (Self, bool);
                fn overflowing_add_unsigned(self, rhs: Self::Unsigned) -> (Self, bool);
                fn overflowing_sub_unsigned(self, rhs: Self::Unsigned) -> (Self, bool);
                fn saturating_abs(self) -> Self;
                fn saturating_add_unsigned(self, rhs: Self::Unsigned) -> Self;
                fn saturating_neg(self) -> Self;
                fn saturating_sub_unsigned(self, rhs: Self::Unsigned) -> Self;
                fn signum(self) -> Self;
                fn strict_abs(self) -> Self;
                fn strict_add_unsigned(self, rhs: Self::Unsigned) -> Self;
                fn strict_sub_unsigned(self, rhs: Self::Unsigned) -> Self;
                fn unsigned_abs(self) -> Self::Unsigned;
                fn wrapping_abs(self) -> Self;
                fn wrapping_add_unsigned(self, rhs: Self::Unsigned) -> Self;
                fn wrapping_sub_unsigned(self, rhs: Self::Unsigned) -> Self;
            }
            forward! {
                unsafe fn unchecked_neg(self) -> Self;
            }
        }

        impl PrimitiveSignedRef<$Signed> for &$Signed {}

        impl NonZeroPrimitiveSigned for NonZero<$Signed> {
            type NonZeroUnsigned = NonZero<$Unsigned>;

            forward! {
                fn abs(self) -> Self;
                fn cast_unsigned(self) -> Self::NonZeroUnsigned;
                fn checked_abs(self) -> Option<Self>;
                fn checked_neg(self) -> Option<Self>;
                fn is_negative(self) -> bool;
                fn is_positive(self) -> bool;
                fn overflowing_abs(self) -> (Self, bool);
                fn overflowing_neg(self) -> (Self, bool);
                fn saturating_abs(self) -> Self;
                fn saturating_neg(self) -> Self;
                fn unsigned_abs(self) -> Self::NonZeroUnsigned;
                fn wrapping_abs(self) -> Self;
                fn wrapping_neg(self) -> Self;
            }
        }
    };
}

impl_signed!(i8, u8);
impl_signed!(i16, u16);
impl_signed!(i32, u32);
impl_signed!(i64, u64);
impl_signed!(i128, u128);
impl_signed!(isize, usize);
