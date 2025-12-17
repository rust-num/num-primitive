//! # num-primitive
//!
//! Traits for primitive numeric types in Rust.
//!
//! These traits provide a simple hierarchy for generic programming with Rust's
//! primitive floating-point and integer types:
//!
//! * [`PrimitiveNumber`]
//!   * [`PrimitiveFloat`]: `f32` and `f64`
//!   * [`PrimitiveInteger`]
//!     * [`PrimitiveSigned`]: `i8`, `i16`, `i32`, `i64`, `i128`, and `isize`
//!     * [`PrimitiveUnsigned`]: `u8`, `u16`, `u32`, `u64`, `u128`, and `usize`
//!
//! Each trait includes supertraits for everything implemented in common by these
//! types, as well as associated constants and methods matching their inherent
//! items. `PrimitiveFloat` also adds the contents of `core::{float}::consts`.
//!
//! It is not a goal of this crate to *add* any functionality to the primitive
//! types, only to expose what is already available in the standard library in a
//! more generic way. The traits are also [sealed] against downstream
//! implementations to allow expansion in a non-breaking way.
//!
//! For use-cases that include third-party types, along with features that go beyond
//! the standard library, consider crates like [`num-traits`] and [`num-integer`].
//!
//! [`num-integer`]: https://crates.io/crates/num-integer
//! [`num-traits`]: https://crates.io/crates/num-traits
//! [sealed]: https://rust-lang.github.io/api-guidelines/future-proofing.html#sealed-traits-protect-against-downstream-implementations-c-sealed
//!
//! ## Usage
//!
//! Add this to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! num-primitive = "0.3"
//! ```
//!
//! ## Features
//!
//! This crate can be used without the standard library (`#![no_std]`) by disabling
//! the default `std` feature. Use this in `Cargo.toml`:
//!
//! ```toml
//! [dependencies.num-primitive]
//! version = "0.3"
//! default-features = false
//! ```
//!
//! Some `PrimitiveFloat` methods are only available when the `std` feature is
//! enabled, just like when using those floating-point types directly.

#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(feature = "std")]
extern crate std;

#[macro_use]
mod macros;

mod bytes;
mod error;
mod float;
mod integer;
mod number;
mod signed;
mod unsigned;

#[cfg(test)]
mod tests;

pub use self::bytes::PrimitiveBytes;
pub use self::error::PrimitiveError;
pub use self::float::{PrimitiveFloat, PrimitiveFloatRef, PrimitiveFloatToInt};
pub use self::integer::{PrimitiveInteger, PrimitiveIntegerRef};
pub use self::number::{PrimitiveNumber, PrimitiveNumberAs, PrimitiveNumberRef};
pub use self::signed::{PrimitiveSigned, PrimitiveSignedRef};
pub use self::unsigned::{PrimitiveUnsigned, PrimitiveUnsignedRef};
