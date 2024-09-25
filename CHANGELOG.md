# Changelog

The format is based on [Keep a Changelog].

[Keep a Changelog]: http://keepachangelog.com/en/1.0.0/

## 0.16.3 (2024-09-25)

This release exports `scale_value::scale::ValueVisitor<TypeResolver>`, allowing the values to be created from functions like `scale_decode::visitor::decode_with_visitor`.

## 0.16.2 (2024-08-08)

This release adds `scale_value::stringify::to_writer` and `scale_value::stringify::to_writer_custom` (to align with the already present `scale_value::stringify::from_str_custom`), and also exposes a new `scale_value::stringiy::custom_formatters` containing a formatter for displaying things as hex.

`scale_value::stringify::to_writer_custom` allows for custom formatting of values, including a "pretty" spaced/indented formatting and a "compact" formatting which removes all unnecessary spaces. It also allows customising of the indentation and for custom formatters to be applied, as well as displaying the contexts of values if desired.

See [#52](https://github.com/paritytech/scale-value/pull/52) for more information.

## 0.16.1 (2024-07-24)

This release:
- Adds a "tracing decoder" (via `scale_value::scale::tracing::{decode_as_type,*}`), which is like `scale_value::scale::decode_as_type`, but traces and hands back much more detail in case of a decoding failure, so that it's easier to track down where decoding failed. This is particularly useful when working with historic type information, which must be provided independently and could easily be misaligned with reality. ([#52](https://github.com/paritytech/scale-value/pull/52))

## 0.16.0 (2024-05-15)

This release:
- Bumps `scale-decode` to its latest version (0.13.0).

## 0.15.1 (2024-05-08)

### Fixed

- Fix an infinite loop when trying to encode Composite values of the wrong shape ((#48)[https://github.com/paritytech/scale-value/pull/48])

## 0.15.0 (2024-04-29)

This release bumps `scale-type-resolver`, `scale-encode`, `scale-decode` and `scale-bits` to their latest versions.

## 0.14.1 (2024-03-04)

### Added

A `scale_value::decode_as_fields` function was added that can decode a series of values from some bytes given an iterator of type ids. Previously it was only possible through the `scale_decode::DecodeAsFields` implementation of `scale_value::Composite<()>`. With the new function `scale_value::Composite<R::TypeId>`'s can be decoded for any type resolver `R`.

## 0.14.0 (2024-02-27)

### Changed

The crate now uses [`scale-type-resolver`](https://github.com/paritytech/scale-type-resolver) to be generic over the provider of type information that is used when encoding and decoding `Value`s.

One implication is that `scale_decode::IntoVisitor` is now only implemented for `Value<()>` and no longer for `Value<u32>`. So `Value::decode_from_type()` cannot be used anymore to create a `Value<u32>` that keeps type id information. Instead you now use `scale_value::scale::decode_as_type()` which can return the desired `Value<u32>`.

## 0.13.0 (2023-11-10)

This release:
- Bumps `scale-decode` to its latest version.

## 0.12.0 (2023-08-02)

Bumps `scale-encode` and `scale-decode` to their latest versions (0.5 and 0.9 respectively).

One effect that this has is that structs containing compact encoded values, after being encoded, now decode to composite types that better
reflect their original shape. For example, `Compact(MyWrapper { inner: 123 })`, when encoded, used to decode to `Value::u128(123)`,
but now it decodes to `Value::named_composite(vec![("inner", Value::u128(123))]).`

## 0.11.0 (2023-07-18)

### Added

- Adds support for `no_std` environments; disable the "std" feature flag for this. ([#38](https://github.com/paritytech/scale-value/pull/38))
  This PR makes a couple of small breaking changes:
  - The `from_string` feature flag is now `from-string`.
  - Some sub-`ErrorKind`'s in `from_string` no logner impl `std::error::Error`.
  - `ParseErrorKind::Custom` errors are now strings rather than boxed `std::error::Error`s to play nicer with `no_std`.
- Adds a `value!` macro to make constructing `Value`'s much easier; think `serde_json::value!`. ([#36](https://github.com/paritytech/scale-value/pull/36))

### Changed

- Bumps `scale-encode` and `scale-decode` to their latest versions (0.4 and 0.8 respectively).

## 0.10.0

This release:
- bumps `scale-encode` and `scale-decode` to their latest versions.

## 0.9.0

This release:
- bumps `scale-encode` and `scale-decode` to their latest versions.

## 0.8.1

This patch release:
- Changes how composite `Value`'s are encoded to improve the likelihood that values will encode correctly. ([#32](https://github.com/paritytech/scale-value/pull/32))

## 0.8.0

This release:
- Bumps to using `scale-info` 2.5.0 and uses field rather than method accessors as introduced by that change.
- Introduces `scale_value::stringify::from_str_custom()`, which allows you to construct a `Value` parser that can inject custom parsing logic while parsing strings into Values.
- Adds two new custom parsers in a new `stringify::custom_parsers` module for parsing hex values and ss58 addresses. These can be used in conjunction with the above.
- Fixes a small bug in stringifying so that field and enum idents are no longer quoted unless necessary; this will make the output prettier.

There should be no breaking API changes.

### Added

- Add hex and ss58 custom parsers. ([#29](https://github.com/paritytech/scale-value/pull/29))
- Improve stringifying and add support for custom parsers. ([#26](https://github.com/paritytech/scale-value/pull/26))

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
