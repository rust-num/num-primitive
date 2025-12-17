use crate::{PrimitiveInteger, PrimitiveIntegerRef, PrimitiveSigned};

/// Trait for all primitive [unsigned integer types], including the supertraits
/// [`PrimitiveInteger`] and [`PrimitiveNumber`][crate::PrimitiveNumber].
///
/// This encapsulates trait implementations and inherent methods that are common among all of the
/// primitive unsigned integer types: [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], and [`usize`].
///
/// See the corresponding items on the individual types for more documentation and examples.
///
/// This trait is sealed with a private trait to prevent downstream implementations, so we may
/// continue to expand along with the standard library without worrying about breaking changes for
/// implementors.
///
/// [unsigned integer types]: https://doc.rust-lang.org/reference/types/numeric.html#r-type.numeric.int.unsigned
///
/// # Examples
///
/// ```
/// use num_primitive::PrimitiveUnsigned;
///
/// // Greatest Common Divisor (Euclidean algorithm)
/// fn gcd<T: PrimitiveUnsigned>(mut a: T, mut b: T) -> T {
///     let zero = T::from(0u8);
///     while b != zero {
///         (a, b) = (b, a % b);
///     }
///     a
/// }
///
/// assert_eq!(gcd::<u8>(48, 18), 6);
/// assert_eq!(gcd::<u16>(1071, 462), 21);
/// assert_eq!(gcd::<u32>(6_700_417, 2_147_483_647), 1);
/// ```
pub trait PrimitiveUnsigned: PrimitiveInteger + From<u8> {
    /// The signed integer type used by methods like
    /// [`checked_add_signed`][Self::checked_add_signed].
    type Signed: PrimitiveSigned;

    /// Computes the absolute difference between `self` and `other`.
    fn abs_diff(self, other: Self) -> Self;

    /// Calculates `self` &minus; `rhs` &minus; `borrow` and returns a tuple
    /// containing the difference and the output borrow.
    fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool);

    /// Calculates `self` + `rhs` + `carry` and returns a tuple containing
    /// the sum and the output carry (in that order).
    fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool);

    /// Calculates the "full multiplication" `self * rhs + carry`
    /// without the possibility to overflow.
    fn carrying_mul(self, rhs: Self, carry: Self) -> (Self, Self);

    /// Calculates the "full multiplication" `self * rhs + carry + add`.
    fn carrying_mul_add(self, rhs: Self, carry: Self, add: Self) -> (Self, Self);

    /// Returns the bit pattern of `self` reinterpreted as a signed integer of the same size.
    fn cast_signed(self) -> Self::Signed;

    /// Checked addition with a signed integer. Computes `self + rhs`, returning `None` if overflow
    /// occurred.
    fn checked_add_signed(self, rhs: Self::Signed) -> Option<Self>;

    /// Calculates the smallest value greater than or equal to `self` that is a multiple of `rhs`.
    /// Returns `None` if `rhs` is zero or the operation would result in overflow.
    fn checked_next_multiple_of(self, rhs: Self) -> Option<Self>;

    /// Returns the smallest power of two greater than or equal to `self`. If the next power of two
    /// is greater than the type's maximum value, `None` is returned, otherwise the power of two is
    /// wrapped in Some.
    fn checked_next_power_of_two(self) -> Option<Self>;

    /// Checked integer subtraction. Computes `self - rhs` and checks if the result fits into a
    /// signed integer of the same size, returning `None` if overflow occurred.
    fn checked_signed_diff(self, rhs: Self) -> Option<Self::Signed>;

    /// Checked subtraction with a signed integer. Computes `self - rhs`,
    /// returning `None` if overflow occurred.
    fn checked_sub_signed(self, rhs: Self::Signed) -> Option<Self>;

    /// Calculates the quotient of `self` and rhs, rounding the result towards positive infinity.
    fn div_ceil(self, rhs: Self) -> Self;

    /// Returns `true` if `self` is an integer multiple of `rhs`, and false otherwise.
    fn is_multiple_of(self, rhs: Self) -> bool;

    /// Returns `true` if and only if `self == 2^k` for some `k`.
    fn is_power_of_two(self) -> bool;

    /// Calculates the smallest value greater than or equal to `self` that is a multiple of `rhs`.
    fn next_multiple_of(self, rhs: Self) -> Self;

    /// Returns the smallest power of two greater than or equal to `self`.
    fn next_power_of_two(self) -> Self;

    /// Calculates `self + rhs` with a signed `rhs`. Returns a tuple of the addition along with a
    /// boolean indicating whether an arithmetic overflow would occur.
    fn overflowing_add_signed(self, rhs: Self::Signed) -> (Self, bool);

    /// Calculates `self` - `rhs` with a signed `rhs`. Returns a tuple of the subtraction along
    /// with a boolean indicating whether an arithmetic overflow would occur.
    fn overflowing_sub_signed(self, rhs: Self::Signed) -> (Self, bool);

    /// Saturating addition with a signed integer. Computes `self + rhs`, saturating at the numeric
    /// bounds instead of overflowing.
    fn saturating_add_signed(self, rhs: Self::Signed) -> Self;

    /// Saturating integer subtraction. Computes `self` - `rhs`, saturating at
    /// the numeric bounds instead of overflowing.
    fn saturating_sub_signed(self, rhs: Self::Signed) -> Self;

    /// Strict addition with a signed integer. Computes `self + rhs`,
    /// panicking if overflow occurred.
    fn strict_add_signed(self, rhs: Self::Signed) -> Self;

    /// Strict subtraction with a signed integer. Computes `self - rhs`,
    /// panicking if overflow occurred.
    fn strict_sub_signed(self, rhs: Self::Signed) -> Self;

    /// Wrapping (modular) addition with a signed integer. Computes `self + rhs`, wrapping around
    /// at the boundary of the type.
    fn wrapping_add_signed(self, rhs: Self::Signed) -> Self;

    /// Wrapping (modular) subtraction with a signed integer. Computes
    /// `self - rhs`, wrapping around at the boundary of the type.
    fn wrapping_sub_signed(self, rhs: Self::Signed) -> Self;
}

/// Trait for references to primitive unsigned integer types ([`PrimitiveUnsigned`]).
///
/// This enables traits like the standard operators in generic code,
/// e.g. `where &T: PrimitiveUnsignedRef<T>`.
pub trait PrimitiveUnsignedRef<T>: PrimitiveIntegerRef<T> {}

macro_rules! impl_unsigned {
    ($Unsigned:ident, $Signed:ty) => {
        impl PrimitiveUnsigned for $Unsigned {
            type Signed = $Signed;

            forward! {
                fn abs_diff(self, other: Self) -> Self;
                fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool);
                fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool);
                fn carrying_mul(self, rhs: Self, carry: Self) -> (Self, Self);
                fn carrying_mul_add(self, rhs: Self, carry: Self, add: Self) -> (Self, Self);
                fn cast_signed(self) -> Self::Signed;
                fn checked_add_signed(self, rhs: Self::Signed) -> Option<Self>;
                fn checked_next_multiple_of(self, rhs: Self) -> Option<Self>;
                fn checked_next_power_of_two(self) -> Option<Self>;
                fn checked_signed_diff(self, rhs: Self) -> Option<Self::Signed>;
                fn checked_sub_signed(self, rhs: Self::Signed) -> Option<Self>;
                fn div_ceil(self, rhs: Self) -> Self;
                fn is_multiple_of(self, rhs: Self) -> bool;
                fn is_power_of_two(self) -> bool;
                fn next_multiple_of(self, rhs: Self) -> Self;
                fn next_power_of_two(self) -> Self;
                fn overflowing_add_signed(self, rhs: Self::Signed) -> (Self, bool);
                fn overflowing_sub_signed(self, rhs: Self::Signed) -> (Self, bool);
                fn saturating_add_signed(self, rhs: Self::Signed) -> Self;
                fn saturating_sub_signed(self, rhs: Self::Signed) -> Self;
                fn strict_add_signed(self, rhs: Self::Signed) -> Self;
                fn strict_sub_signed(self, rhs: Self::Signed) -> Self;
                fn wrapping_add_signed(self, rhs: Self::Signed) -> Self;
                fn wrapping_sub_signed(self, rhs: Self::Signed) -> Self;
            }
        }

        impl PrimitiveUnsignedRef<$Unsigned> for &$Unsigned {}
    };
}

impl_unsigned!(u8, i8);
impl_unsigned!(u16, i16);
impl_unsigned!(u32, i32);
impl_unsigned!(u64, i64);
impl_unsigned!(u128, i128);
impl_unsigned!(usize, isize);
