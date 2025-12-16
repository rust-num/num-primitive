# Release 0.2.1 (2025-12-16)

- Doc-only, updated 0.1 references to 0.2.

# Release 0.2.0 (2025-12-15)

- `PrimitiveFloat` includes supertraits `PrimitiveFloatToInt` for all integers.
  However, `PrimitiveFloatToInt` lost its supertrait `PrimitiveFloat` in kind.
- `PrimitiveNumber` added type-casting methods `as_from` and `as_to`.
- `PrimitiveNumber::Bytes` added supertraits for its array representation.

# Release 0.1.1 (2025-12-11)

- Link documentation to inherent methods.

# Release 0.1.0 (2025-12-09)

- Initial release with MSRV 1.85.
