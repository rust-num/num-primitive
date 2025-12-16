# num-primitive

[![crate](https://img.shields.io/crates/v/num-primitive.svg)](https://crates.io/crates/num-primitive)
[![documentation](https://docs.rs/num-primitive/badge.svg)](https://docs.rs/num-primitive)
[![minimum rustc 1.85](https://img.shields.io/badge/rustc-1.85+-red.svg)](https://rust-lang.github.io/rfcs/2495-min-rust-version.html)
[![build status](https://github.com/rust-num/num-primitive/workflows/CI/badge.svg)](https://github.com/rust-num/num-primitive/actions)

Traits for primitive numeric types in Rust.

These traits provide a simple hierarchy for generic programming with Rust's
primitive floating-point and integer types:

* `PrimitiveNumber`
  * `PrimitiveFloat`: `f32` and `f64`
  * `PrimitiveInteger`
    * `PrimitiveSigned`: `i8`, `i16`, `i32`, `i64`, `i128`, and `isize`
    * `PrimitiveUnsigned`: `u8`, `u16`, `u32`, `u64`, `u128`, and `usize`

Each trait includes supertraits for everything implemented in common by these
types, as well as associated constants and methods matching their inherent
items. `PrimitiveFloat` also adds the contents of `core::{float}::consts`.

It is not a goal of this crate to *add* any functionality to the primitive
types, only to expose what is already available in the standard library in a
more generic way. The traits are also [sealed] against downstream
implementations to allow expansion in a non-breaking way.

For use-cases that include third-party types, along with features that go beyond
the standard library, consider crates like [`num-traits`] and [`num-integer`].

[`num-integer`]: https://crates.io/crates/num-integer
[`num-traits`]: https://crates.io/crates/num-traits
[sealed]: https://rust-lang.github.io/api-guidelines/future-proofing.html#sealed-traits-protect-against-downstream-implementations-c-sealed

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
num-primitive = "0.2"
```

## Features

This crate can be used without the standard library (`#![no_std]`) by disabling
the default `std` feature. Use this in `Cargo.toml`:

```toml
[dependencies.num-primitive]
version = "0.2"
default-features = false
```

Some `PrimitiveFloat` methods are only available when the `std` feature is
enabled, just like when using those floating-point types directly.

## Releases

Release notes are available in [RELEASES.md](RELEASES.md).

## Compatibility

The `num-primitive` crate is currently tested for Rust 1.85 and greater. This
minimum-supported Rust version (MSRV) may be increased at any time to add
support for newly-stabilized functionality from the standard library. Changes
will be documented prominently in the release notes.

If you have specific MSRV needs for your dependent crate, then take care when
choosing your `num-primitive` minimum version, and use Cargo's [version-aware
resolver] to automatically limit your maximum. This way you'll still leave it
open for further dependent projects that do want newer version for new features.

[version-aware resolver]: https://doc.rust-lang.org/cargo/reference/resolver.html#rust-version

## License

Licensed under either of

 * [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0)
 * [MIT license](http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
