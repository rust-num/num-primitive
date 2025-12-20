# Release 0.3.4 (2025-12-20)

- Added `PrimitiveInteger::from_str_radix`.
- Specified error types in `PrimitiveInteger: FromStr`, `PrimitiveSigned: TryFrom<i8>`,
  and `PrimitiveUnsigned: TryFrom<u8>`.

# Release 0.3.3 (2025-12-17)

- Added `PrimitiveBytes` to consolidate the constraints on `PrimitiveNumber::Bytes`
  - Extended with `IndexMut<usize>`, and `PartialEq` and `TryFrom` with slice refs.
  - Added array construction methods `from_fn` and `repeat`.

# Release 0.3.2 (2025-12-16)

- Updated to MSRV 1.91.
- Added `PrimitiveInteger::strict_{add,div,{div,rem}_euclid,mul,neg,pow,rem,shl,shr,sub}`
- Added `PrimitiveSigned::strict_{abs,{add,sub}_unsigned}`
- Added `PrimitiveUnsigned::strict_{abs,{add,sub}_signed}`
- Added `PrimitiveUnsigned::{borrowing_sub,carrying_{add,mul,mul_add},checked_signed_diff}`

# Release 0.3.1 (2025-12-16)

- Updated to MSRV 1.90.
- Added `PrimitiveUnsigned::{checked,overflowing,saturating,wrapping}_sub_signed`

# Release 0.3.0 (2025-12-16)

- Added `PrimitiveNumber::midpoint`
- Removed `Primitive{Float,Signed,Unsigned}::midpoint`

# Release 0.2.4 (2025-12-20)

- Backported `PrimitiveInteger::from_str_radix` from 0.3.4.

# Release 0.2.3 (2025-12-16)

- Updated to MSRV 1.87.
- Added `PrimitiveInteger::{unbounded_shl,unbounded_shr}`
- Added `PrimitiveSigned::{cast_unsigned,midpoint}`
- Added `PrimitiveUnsigned::{cast_signed,is_multiple_of}`

# Release 0.2.2 (2025-12-16)

- Updated to MSRV 1.86.
- Added `PrimitiveFloat::next_down` and `next_up`.

# Release 0.2.1 (2025-12-16)

- Doc-only, updated 0.1 references to 0.2.

# Release 0.2.0 (2025-12-15)

- `PrimitiveFloat` includes supertraits `PrimitiveFloatToInt` for all integers.
  However, `PrimitiveFloatToInt` lost its supertrait `PrimitiveFloat` in kind.
- `PrimitiveNumber` added type-casting methods `as_from` and `as_to`.
- `PrimitiveNumber::Bytes` added supertraits for its array representation.

# Release 0.1.2 (2025-12-20)

- Backported `PrimitiveInteger::from_str_radix` from 0.3.4.

# Release 0.1.1 (2025-12-11)

- Link documentation to inherent methods.

# Release 0.1.0 (2025-12-09)

- Initial release with MSRV 1.85.
