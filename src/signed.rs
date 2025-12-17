use crate::{PrimitiveInteger, PrimitiveIntegerRef, PrimitiveUnsigned};

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
pub trait PrimitiveSigned: PrimitiveInteger + From<i8> + core::ops::Neg<Output = Self> {
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

    /// Calculates the middle point of `self` and `other`.
    fn midpoint(self, other: Self) -> Self;

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
}

/// Trait for references to primitive signed integer types ([`PrimitiveSigned`]).
///
/// This enables traits like the standard operators in generic code,
/// e.g. `where &T: PrimitiveSignedRef<T>`.
pub trait PrimitiveSignedRef<T>: PrimitiveIntegerRef<T> + core::ops::Neg<Output = T> {}

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
                fn midpoint(self, other: Self) -> Self;
                fn overflowing_abs(self) -> (Self, bool);
                fn overflowing_add_unsigned(self, rhs: Self::Unsigned) -> (Self, bool);
                fn overflowing_sub_unsigned(self, rhs: Self::Unsigned) -> (Self, bool);
                fn saturating_abs(self) -> Self;
                fn saturating_add_unsigned(self, rhs: Self::Unsigned) -> Self;
                fn saturating_neg(self) -> Self;
                fn saturating_sub_unsigned(self, rhs: Self::Unsigned) -> Self;
                fn signum(self) -> Self;
                fn unsigned_abs(self) -> Self::Unsigned;
                fn wrapping_abs(self) -> Self;
                fn wrapping_add_unsigned(self, rhs: Self::Unsigned) -> Self;
                fn wrapping_sub_unsigned(self, rhs: Self::Unsigned) -> Self;
            }
        }

        impl PrimitiveSignedRef<$Signed> for &$Signed {}
    };
}

impl_signed!(i8, u8);
impl_signed!(i16, u16);
impl_signed!(i32, u32);
impl_signed!(i64, u64);
impl_signed!(i128, u128);
impl_signed!(isize, usize);
