use crate::{PrimitiveNumber, PrimitiveNumberRef, PrimitiveUnsigned};

use core::cmp::Ordering;
use core::f32::consts as f32_consts;
use core::f64::consts as f64_consts;
use core::num::{FpCategory, ParseFloatError};

struct SealedToken;

/// Trait for all primitive [floating-point types], including the supertrait [`PrimitiveNumber`].
///
/// This encapsulates trait implementations, constants, and inherent methods that are common among
/// the primitive floating-point types, [`f32`] and [`f64`]. Unstable types [`f16`] and [`f128`]
/// will be added once they are stabilized.
///
/// See the corresponding items on the individual types for more documentation and examples.
///
/// This trait is sealed with a private trait to prevent downstream implementations, so we may
/// continue to expand along with the standard library without worrying about breaking changes for
/// implementors.
///
/// [floating-point types]: https://doc.rust-lang.org/reference/types/numeric.html#r-type.numeric.float
///
/// # Examples
///
/// This example requires the `std` feature for [`powi`][Self::powi] and [`sqrt`][Self::sqrt]:
///
#[cfg_attr(feature = "std", doc = "```")]
#[cfg_attr(not(feature = "std"), doc = "```ignore")]
/// use num_primitive::PrimitiveFloat;
///
/// // Euclidean distance, √(∑(aᵢ - bᵢ)²)
/// fn distance<T: PrimitiveFloat>(a: &[T], b: &[T]) -> T {
///     assert_eq!(a.len(), b.len());
///     core::iter::zip(a, b).map(|(a, b)| (*a - b).powi(2)).sum::<T>().sqrt()
/// }
///
/// assert_eq!(distance::<f32>(&[0., 0.], &[3., 4.]), 5.);
/// assert_eq!(distance::<f64>(&[0., 1., 2.], &[1., 3., 0.]), 3.);
/// ```
///
/// This example works without any features:
///
/// ```
/// use num_primitive::PrimitiveFloat;
///
/// // Squared Euclidean distance, ∑(aᵢ - bᵢ)²
/// fn distance_squared<T: PrimitiveFloat>(a: &[T], b: &[T]) -> T {
///     assert_eq!(a.len(), b.len());
///     core::iter::zip(a, b).map(|(a, b)| (*a - b)).map(|x| x * x).sum::<T>()
/// }
///
/// assert_eq!(distance_squared::<f32>(&[0., 0.], &[3., 4.]), 25.);
/// assert_eq!(distance_squared::<f64>(&[0., 1., 2.], &[1., 3., 0.]), 9.);
/// ```
pub trait PrimitiveFloat:
    PrimitiveNumber
    + PrimitiveFloatToInt<i8>
    + PrimitiveFloatToInt<i16>
    + PrimitiveFloatToInt<i32>
    + PrimitiveFloatToInt<i64>
    + PrimitiveFloatToInt<i128>
    + PrimitiveFloatToInt<isize>
    + PrimitiveFloatToInt<u8>
    + PrimitiveFloatToInt<u16>
    + PrimitiveFloatToInt<u32>
    + PrimitiveFloatToInt<u64>
    + PrimitiveFloatToInt<u128>
    + PrimitiveFloatToInt<usize>
    + core::convert::From<i8>
    + core::convert::From<u8>
    + core::ops::Neg<Output = Self>
    + core::str::FromStr<Err = ParseFloatError>
{
    /// Approximate number of significant digits in base 10.
    const DIGITS: u32;

    /// Machine epsilon value.
    const EPSILON: Self;

    /// Infinity (∞).
    const INFINITY: Self;

    /// Number of significant digits in base 2.
    const MANTISSA_DIGITS: u32;

    /// Largest finite value.
    const MAX: Self;

    /// Maximum _x_ for which 10<sup>_x_</sup> is normal.
    const MAX_10_EXP: i32;

    /// Maximum possible power of 2 exponent.
    const MAX_EXP: i32;

    /// Smallest finite value.
    const MIN: Self;

    /// Minimum _x_ for which 10<sup>_x_</sup> is normal.
    const MIN_10_EXP: i32;

    /// One greater than the minimum possible normal power of 2 exponent.
    const MIN_EXP: i32;

    /// Smallest positive normal value.
    const MIN_POSITIVE: Self;

    /// Not a Number (NaN).
    const NAN: Self;

    /// Negative infinity (−∞).
    const NEG_INFINITY: Self;

    /// The radix or base of the internal representation.
    const RADIX: u32;

    // The following are not inherent consts, rather from `core::{float}::consts`.

    /// Euler's number (e)
    const E: Self;

    /// 1/π
    const FRAC_1_PI: Self;

    /// 1/sqrt(2)
    const FRAC_1_SQRT_2: Self;

    /// 2/π
    const FRAC_2_PI: Self;

    /// 2/sqrt(π)
    const FRAC_2_SQRT_PI: Self;

    /// π/2
    const FRAC_PI_2: Self;

    /// π/3
    const FRAC_PI_3: Self;

    /// π/4
    const FRAC_PI_4: Self;

    /// π/6
    const FRAC_PI_6: Self;

    /// π/8
    const FRAC_PI_8: Self;

    /// ln(2)
    const LN_2: Self;

    /// ln(10)
    const LN_10: Self;

    /// log₂(10)
    const LOG2_10: Self;

    /// log₂(e)
    const LOG2_E: Self;

    /// log₁₀(2)
    const LOG10_2: Self;

    /// log₁₀(e)
    const LOG10_E: Self;

    /// Archimedes' constant (π)
    const PI: Self;

    /// sqrt(2)
    const SQRT_2: Self;

    /// The full circle constant (τ)
    const TAU: Self;

    /// An unsigned integer type used by methods [`from_bits`][Self::from_bits] and
    /// [`to_bits`][Self::to_bits].
    type Bits: PrimitiveUnsigned;

    /// Computes the absolute value of `self`.
    fn abs(self) -> Self;

    /// Restrict a value to a certain interval unless it is NaN.
    fn clamp(self, min: Self, max: Self) -> Self;

    /// Returns the floating point category of the number. If only one property is going to be
    /// tested, it is generally faster to use the specific predicate instead.
    fn classify(self) -> FpCategory;

    /// Returns a number composed of the magnitude of `self` and the sign of sign.
    fn copysign(self, sign: Self) -> Self;

    /// Raw transmutation from `Self::Bits`.
    fn from_bits(value: Self::Bits) -> Self;

    /// Returns `true` if this number is neither infinite nor NaN.
    fn is_finite(self) -> bool;

    /// Returns `true` if this value is positive infinity or negative infinity.
    fn is_infinite(self) -> bool;

    /// Returns `true` if this value is NaN.
    fn is_nan(self) -> bool;

    /// Returns `true` if the number is neither zero, infinite, subnormal, or NaN.
    fn is_normal(self) -> bool;

    /// Returns `true` if `self` has a negative sign, including `-0.0`, NaNs with negative sign bit
    /// and negative infinity.
    fn is_sign_negative(self) -> bool;

    /// Returns `true` if `self` has a positive sign, including `+0.0`, NaNs with positive sign bit
    /// and positive infinity.
    fn is_sign_positive(self) -> bool;

    /// Returns `true` if the number is subnormal.
    fn is_subnormal(self) -> bool;

    /// Returns the maximum of the two numbers, ignoring NaN.
    fn max(self, other: Self) -> Self;

    /// Returns the minimum of the two numbers, ignoring NaN.
    fn min(self, other: Self) -> Self;

    /// Returns the greatest number less than `self`.
    fn next_down(self) -> Self;

    /// Returns the least number greater than `self`.
    fn next_up(self) -> Self;

    /// Takes the reciprocal (inverse) of a number, `1/x`.
    fn recip(self) -> Self;

    /// Returns a number that represents the sign of `self`.
    fn signum(self) -> Self;

    /// Raw transmutation to `Self::Bits`.
    fn to_bits(self) -> Self::Bits;

    /// Converts radians to degrees.
    fn to_degrees(self) -> Self;

    /// Converts degrees to radians.
    fn to_radians(self) -> Self;

    /// Returns the ordering between `self` and `other`.
    fn total_cmp(&self, other: &Self) -> Ordering;

    /// Rounds toward zero and converts to any primitive integer type, assuming that the value is
    /// finite and fits in that type.
    ///
    /// # Safety
    ///
    /// The value must:
    ///
    /// * Not be `NaN`
    /// * Not be infinite
    /// * Be representable in the return type `Int`, after truncating off its fractional part
    unsafe fn to_int_unchecked<Int>(self) -> Int
    where
        Self: PrimitiveFloatToInt<Int>;

    /// Computes the arccosine of a number. Return value is in radians in the range [0, pi] or NaN
    /// if the number is outside the range [-1, 1].
    #[cfg(feature = "std")]
    fn acos(self) -> Self;

    /// Inverse hyperbolic cosine function.
    #[cfg(feature = "std")]
    fn acosh(self) -> Self;

    /// Computes the arcsine of a number. Return value is in radians in the range [-pi/2, pi/2] or
    /// NaN if the number is outside the range [-1, 1].
    #[cfg(feature = "std")]
    fn asin(self) -> Self;

    /// Inverse hyperbolic sine function.
    #[cfg(feature = "std")]
    fn asinh(self) -> Self;

    /// Computes the arctangent of a number. Return value is in radians in the range [-pi/2, pi/2];
    #[cfg(feature = "std")]
    fn atan(self) -> Self;

    /// Computes the four quadrant arctangent of `self` (`y`) and `other` (`x`) in radians.
    #[cfg(feature = "std")]
    fn atan2(self, other: Self) -> Self;

    /// Inverse hyperbolic tangent function.
    #[cfg(feature = "std")]
    fn atanh(self) -> Self;

    /// Returns the cube root of a number.
    #[cfg(feature = "std")]
    fn cbrt(self) -> Self;

    /// Returns the smallest integer greater than or equal to `self`.
    #[cfg(feature = "std")]
    fn ceil(self) -> Self;

    /// Computes the cosine of a number (in radians).
    #[cfg(feature = "std")]
    fn cos(self) -> Self;

    /// Hyperbolic cosine function.
    #[cfg(feature = "std")]
    fn cosh(self) -> Self;

    /// Calculates Euclidean division, the matching method for `rem_euclid`.
    #[cfg(feature = "std")]
    fn div_euclid(self, rhs: Self) -> Self;

    /// Returns `e^(self)`, (the exponential function).
    #[cfg(feature = "std")]
    fn exp(self) -> Self;

    /// Returns `2^(self)`.
    #[cfg(feature = "std")]
    fn exp2(self) -> Self;

    /// Returns `e^(self) - 1` in a way that is accurate even if the number is close to zero.
    #[cfg(feature = "std")]
    fn exp_m1(self) -> Self;

    /// Returns the largest integer less than or equal to `self`.
    #[cfg(feature = "std")]
    fn floor(self) -> Self;

    /// Returns the fractional part of `self`.
    #[cfg(feature = "std")]
    fn fract(self) -> Self;

    /// Compute the distance between the origin and a point (`x`, `y`) on the Euclidean plane.
    /// Equivalently, compute the length of the hypotenuse of a right-angle triangle with other
    /// sides having length `x.abs()` and `y.abs()`.
    #[cfg(feature = "std")]
    fn hypot(self, other: Self) -> Self;

    /// Returns the natural logarithm of the number.
    #[cfg(feature = "std")]
    fn ln(self) -> Self;

    /// Returns `ln(1+n)` (natural logarithm) more accurately than if the operations were performed
    /// separately.
    #[cfg(feature = "std")]
    fn ln_1p(self) -> Self;

    /// Returns the logarithm of the number with respect to an arbitrary base.
    #[cfg(feature = "std")]
    fn log(self, base: Self) -> Self;

    /// Returns the base 2 logarithm of the number.
    #[cfg(feature = "std")]
    fn log2(self) -> Self;

    /// Returns the base 10 logarithm of the number.
    #[cfg(feature = "std")]
    fn log10(self) -> Self;

    /// Fused multiply-add. Computes `(self * a) + b` with only one rounding error, yielding a more
    /// accurate result than an unfused multiply-add.
    #[cfg(feature = "std")]
    fn mul_add(self, a: Self, b: Self) -> Self;

    /// Raises a number to a floating point power.
    #[cfg(feature = "std")]
    fn powf(self, n: Self) -> Self;

    /// Raises a number to an integer power.
    #[cfg(feature = "std")]
    fn powi(self, n: i32) -> Self;

    /// Calculates the least nonnegative remainder of `self (mod rhs)`.
    #[cfg(feature = "std")]
    fn rem_euclid(self, rhs: Self) -> Self;

    /// Returns the nearest integer to `self`. If a value is half-way between two integers, round
    /// away from `0.0`.
    #[cfg(feature = "std")]
    fn round(self) -> Self;

    /// Returns the nearest integer to a number. Rounds half-way cases to the number with an even
    /// least significant digit.
    #[cfg(feature = "std")]
    fn round_ties_even(self) -> Self;

    /// Computes the sine of a number (in radians).
    #[cfg(feature = "std")]
    fn sin(self) -> Self;

    /// Simultaneously computes the sine and cosine of the number, `x`. Returns `(sin(x), cos(x))`.
    #[cfg(feature = "std")]
    fn sin_cos(self) -> (Self, Self);

    /// Hyperbolic sine function.
    #[cfg(feature = "std")]
    fn sinh(self) -> Self;

    /// Returns the square root of a number.
    #[cfg(feature = "std")]
    fn sqrt(self) -> Self;

    /// Computes the tangent of a number (in radians).
    #[cfg(feature = "std")]
    fn tan(self) -> Self;

    /// Hyperbolic tangent function.
    #[cfg(feature = "std")]
    fn tanh(self) -> Self;

    /// Returns the integer part of `self`. This means that non-integer numbers are always
    /// truncated towards zero.
    #[cfg(feature = "std")]
    fn trunc(self) -> Self;
}

/// Trait for references to primitive floating-point types ([`PrimitiveFloat`]).
///
/// This enables traits like the standard operators in generic code,
/// e.g. `where &T: PrimitiveFloatRef<T>`.
pub trait PrimitiveFloatRef<T>: PrimitiveNumberRef<T> + core::ops::Neg<Output = T> {}

/// Trait for conversions supported by [`PrimitiveFloat::to_int_unchecked`].
///
/// This is effectively the same as the unstable [`core::convert::FloatToInt`], implemented for all
/// combinations of [`PrimitiveFloat`] and [`PrimitiveInteger`][crate::PrimitiveInteger].
///
/// # Examples
///
/// `PrimitiveFloatToInt<{integer}>` is a supertrait of [`PrimitiveFloat`] for all primitive
/// integers, so you do not need to use this trait directly with concrete integer types.
///
/// ```
/// use num_primitive::PrimitiveFloat;
///
/// fn pi<Float: PrimitiveFloat>() -> i32 {
///     // SAFETY: π is finite, and truncated to 3 fits any int
///     unsafe { Float::PI.to_int_unchecked() }
/// }
///
/// assert_eq!(pi::<f32>(), 3i32);
/// assert_eq!(pi::<f64>(), 3i32);
/// ```
///
/// However, if the integer type is also generic, an explicit type constraint is needed.
///
/// ```
/// use num_primitive::{PrimitiveFloat, PrimitiveFloatToInt};
///
/// fn tau<Float, Int>() -> Int
/// where
///     Float: PrimitiveFloat + PrimitiveFloatToInt<Int>,
/// {
///     // SAFETY: τ is finite, and truncated to 6 fits any int
///     unsafe { Float::TAU.to_int_unchecked() }
/// }
///
/// assert_eq!(tau::<f32, i64>(), 6i64);
/// assert_eq!(tau::<f64, u8>(), 6u8);
/// ```
///
pub trait PrimitiveFloatToInt<Int> {
    #[doc(hidden)]
    #[expect(private_interfaces)]
    unsafe fn __to_int_unchecked(x: Self, _: SealedToken) -> Int;
}

macro_rules! impl_float {
    ($Float:ident, $consts:ident, $Bits:ty) => {
        impl PrimitiveFloat for $Float {
            use_consts!(Self::{
                DIGITS: u32,
                EPSILON: Self,
                INFINITY: Self,
                MANTISSA_DIGITS: u32,
                MAX: Self,
                MAX_10_EXP: i32,
                MAX_EXP: i32,
                MIN: Self,
                MIN_10_EXP: i32,
                MIN_EXP: i32,
                MIN_POSITIVE: Self,
                NAN: Self,
                NEG_INFINITY: Self,
                RADIX: u32,
            });

            use_consts!($consts::{
                E: Self,
                FRAC_1_PI: Self,
                FRAC_1_SQRT_2: Self,
                FRAC_2_PI: Self,
                FRAC_2_SQRT_PI: Self,
                FRAC_PI_2: Self,
                FRAC_PI_3: Self,
                FRAC_PI_4: Self,
                FRAC_PI_6: Self,
                FRAC_PI_8: Self,
                LN_2: Self,
                LN_10: Self,
                LOG2_10: Self,
                LOG2_E: Self,
                LOG10_2: Self,
                LOG10_E: Self,
                PI: Self,
                SQRT_2: Self,
                TAU: Self,
            });

            type Bits = $Bits;

            forward! {
                fn from_bits(value: Self::Bits) -> Self;
            }
            forward! {
                fn abs(self) -> Self;
                fn clamp(self, min: Self, max: Self) -> Self;
                fn classify(self) -> FpCategory;
                fn copysign(self, sign: Self) -> Self;
                fn is_finite(self) -> bool;
                fn is_infinite(self) -> bool;
                fn is_nan(self) -> bool;
                fn is_normal(self) -> bool;
                fn is_sign_negative(self) -> bool;
                fn is_sign_positive(self) -> bool;
                fn is_subnormal(self) -> bool;
                fn max(self, other: Self) -> Self;
                fn min(self, other: Self) -> Self;
                fn next_down(self) -> Self;
                fn next_up(self) -> Self;
                fn recip(self) -> Self;
                fn signum(self) -> Self;
                fn to_bits(self) -> Self::Bits;
                fn to_degrees(self) -> Self;
                fn to_radians(self) -> Self;
            }
            forward! {
                fn total_cmp(&self, other: &Self) -> Ordering;
            }

            // NOTE: This is still effectively forwarding, but we need some indirection
            // to avoid naming the unstable `core::convert::FloatToInt`.
            #[doc = forward_doc!(to_int_unchecked)]
            #[inline]
            unsafe fn to_int_unchecked<Int>(self) -> Int
            where
                Self: PrimitiveFloatToInt<Int>,
            {
                // SAFETY: we're just passing through here!
                unsafe { <Self as PrimitiveFloatToInt<Int>>::__to_int_unchecked(self, SealedToken) }
            }

            // --- std-only methods ---

            #[cfg(feature = "std")]
            forward! {
                fn acos(self) -> Self;
                fn acosh(self) -> Self;
                fn asin(self) -> Self;
                fn asinh(self) -> Self;
                fn atan(self) -> Self;
                fn atan2(self, other: Self) -> Self;
                fn atanh(self) -> Self;
                fn cbrt(self) -> Self;
                fn ceil(self) -> Self;
                fn cos(self) -> Self;
                fn cosh(self) -> Self;
                fn div_euclid(self, rhs: Self) -> Self;
                fn exp(self) -> Self;
                fn exp2(self) -> Self;
                fn exp_m1(self) -> Self;
                fn floor(self) -> Self;
                fn fract(self) -> Self;
                fn hypot(self, other: Self) -> Self;
                fn ln(self) -> Self;
                fn ln_1p(self) -> Self;
                fn log(self, base: Self) -> Self;
                fn log2(self) -> Self;
                fn log10(self) -> Self;
                fn mul_add(self, a: Self, b: Self) -> Self;
                fn powf(self, n: Self) -> Self;
                fn powi(self, n: i32) -> Self;
                fn rem_euclid(self, rhs: Self) -> Self;
                fn round(self) -> Self;
                fn round_ties_even(self) -> Self;
                fn sin(self) -> Self;
                fn sin_cos(self) -> (Self, Self);
                fn sinh(self) -> Self;
                fn sqrt(self) -> Self;
                fn tan(self) -> Self;
                fn tanh(self) -> Self;
                fn trunc(self) -> Self;
            }
        }

        impl PrimitiveFloatRef<$Float> for &$Float {}
    }
}

impl_float!(f32, f32_consts, u32);
impl_float!(f64, f64_consts, u64);

// NOTE: the extra module level here is to make sure that `PrimitiveFloat` isn't in scope, so we
// can be sure that we're not recursing. Elsewhere we rely on the normal `unconditional-recursion`
// lint, but that doesn't see through this level of trait indirection.
mod internal {
    macro_rules! impl_float_to_int {
        ($Float:ty => $($Int:ty),+) => {
            $(
                impl super::PrimitiveFloatToInt<$Int> for $Float {
                    #[inline]
                    #[expect(private_interfaces)]
                    unsafe fn __to_int_unchecked(x: Self, _: super::SealedToken) -> $Int {
                        // SAFETY: we're just passing through here!
                        unsafe { <$Float>::to_int_unchecked::<$Int>(x) }
                    }
                }
            )+
        }
    }

    impl_float_to_int!(f32 => u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
    impl_float_to_int!(f64 => u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
}
