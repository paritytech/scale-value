# Changelog

The format is based on [Keep a Changelog].

[Keep a Changelog]: http://keepachangelog.com/en/1.0.0/

## 0.7.0

The main change in this release is that it makes use of a new `scale-encode` crate and updated `scale-decode` crate for the SCALE encoding and decoding of Values.
- Values now implement `DecodeAsType` and `EncodeAsType`.
- Composites now implement `DecodeAsFields`.
- As a small breaking API change, the `TypeId` passed to the encode and decode methods is now a plain `u32` for simplicity, rather than a newtype struct.

It should be very straightforward to update to this release as the changes are mainly additive in nature.

### Changed

- Use latest `scale-decode` and new `scale-encode` crate for SCALE encoding and decoding Values. ([#25](https://github.com/paritytech/scale-value/pull/25))

## 0.6.0

Here we move to `scale_bits` from `bitvec` to handle our encode/decode logic and provide a simple type to decode bits into. We also now add a WASM CI test, and will expect this crate (potentially via features in the future) to be WASM compatible.

### Changed

- Use `scale-bits` for `BitSequence` decoding etc and enable WASM test. ([#24](https://github.com/paritytech/scale-value/pull/24))

## 0.5.0

The main user-facing change in this release is that the SCALE bytes for compact-encoded _structs_ previously decoded into `Composite` values with the same degree of nesting (ie if the compact encoded value was nested within 2 structs, it would be decoded into a value nested inside 2 `Composite`s). This nesting has now been removed, and the compact value is returned directly. This should have no impact on re-encoding the Value, since encoding into single-field composites will just delegrate to the inner field type as needed.

Internally, the SCALE decoding logic has mostly moved to `scale-decode`, simplifying the logic in this crate (and exposing a more general/lower level decoding interface via that crate).

Full list of changes:

### Changed

- Use `scale-decode` for `Value` decoding. ([#22](https://github.com/paritytech/scale-value/pull/22))

## 0.4.0

The main addition in this release is the `At` trait (and corresponding `.at()` method) for indexing into `Value`s. There are also various small breaking changes as a result of tidying up various constructors, which will hopefully in general allow you to construct `Value`s with a little less verbosity. The `uint`/`int` constructors have been made more consistent with their siblings and have been renamed to `u128` and `i128`.

Full list of changes:

### Added

- Index into values with at, and more generic/extra accessors/constructors. ([#19](https://github.com/paritytech/scale-value/pull/19))

## 0.3.0

This release introduces a small breaking change: `scale_value::scale::encode_value_as_type` now takes a reference to a value rather than ownership of it, since on the happy path this shouldnt affect performance, and it would often mean cloning the entire value before passing it in, anyway.

Full list of changes:

### Changed

- SCALE encoding now accepts a reference, and make encoding slightly more flexible w.r.t newtype wrappers. ([#17](https://github.com/paritytech/scale-value/pull/17))

## 0.2.1

### Fixed

- Fix compile error on 32-bit architectures owing to BitVec not supporting a store type of u64 on them. Also fix an internal naming mixup w.r.t bitvec types. ([#12](https://github.com/paritytech/scale-value/pull/12))

## 0.2.0

### Added

- Added a string syntax for values, and the ability to parse `Value`'s from strings or encode them into strings (see the new `stringify` module exposed at the crate root). Parsing from strings requires the `from_string` feature to be enabled. ([#7](https://github.com/paritytech/scale-value/pull/7))


## 0.1.0

The initial release.

### Added

- Added a `Value` type that can be SCALE encoded and decoded using a `scale_info::PortableRegistry`, as well as serialized and deserialized to things via `serde`. ([#1](https://github.com/paritytech/scale-value/pull/1))