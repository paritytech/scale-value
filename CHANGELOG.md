# Changelog

The format is based on [Keep a Changelog].

[Keep a Changelog]: http://keepachangelog.com/en/1.0.0/

## 0.2.1

### Fixed

- Fix compile error on 32-bit architectures owing to BitVec not supporting a store type of u64 on them. Also fix an internal naming mixup w.r.t bitvec types. ((#12)[https://github.com/paritytech/scale-value/pull/12])

## 0.2.0

### Added

- Added a string syntax for values, and the ability to parse `Value`'s from strings or encode them into strings (see the new `stringify` module exposed at the crate root). Parsing from strings requires the `from_string` feature to be enabled. ([#7](https://github.com/paritytech/scale-value/pull/7))


## 0.1.0

The initial release.

### Added

- Added a `Value` type that can be SCALE encoded and decoded using a `scale_info::PortableRegistry`, as well as serialized and deserialized to things via `serde`. ([#1](https://github.com/paritytech/scale-value/pull/1))