# scale-value &middot; [![CI Status][ci-badge]][ci] [![Latest Version on Crates.io][crates-badge]][crates] [![Released API docs][docs-badge]][docs]

This crate provides a `Value` type, which is a runtime representation that is compatible with [`scale_info::TypeDef`][scale-info-typedef]. It somewhat analogous to a `serde_json::Value`, which is a runtime representation of JSON values, but with a focus on SCALE encoded values instead of JSON encoded values. Unlike JSON however, SCALE encoding is not self describing, and so we need additional type information to tell us how to encode and decode values.

It is expected that this crate will commonly be used in conjunction with the [scale-info] and [frame-metadata] crates.

The [scale-info] crate allows us to define types and add them to a type registry, which in turn is used to tell us how to SCALE encode and decode `Value`s.

The [frame-metadata] crate contains all of the type information we need in order to be able to SCALE encode and decode `Value`s into the various parameters needed in extrinsics and such.

Crate features (enabled by default):
- `serde`: Allow `Value`s to be converted from and to static Rust types (where possible), or serialized and deserialized to other formats like JSON, via serde.
- `from_string`: Allow strings to be parsed into `Values` using the same format from which values can be converted to strings via `.to_string()`. Examples:
  - Boolean types parse from `true` and `false`.
  - Strings and chars are supported with `"Hello\n there"` and `'a'`.
  - Numbers like `1_234_567` and `-123` are supported.
  - Composite types (structs/tuples) look like `{ hello: 123, "there": true }` and `('a', 'b', true)`.
  - Finally, enum variants look like `Hello { foo: 1, bar: 2 }` and `Foo(1,2,3)`.

# Examples

Manually creating a type registry, and then using it to SCALE encode and decode some runtime constructed `Value` type to/from SCALE bytes.

```rust
// Turn a type into an ID and type registry using `scale-info`:
fn make_type<T: scale_info::TypeInfo + 'static>() -> (u32, scale_info::PortableRegistry) {
    let m = scale_info::MetaType::new::<T>();
    let mut types = scale_info::Registry::new();
    let id = types.register_type(&m);
    let portable_registry: scale_info::PortableRegistry = types.into();
    (id.id(), portable_registry)
}

// Some type which we have derived SCALE type information about:
#[derive(scale_info::TypeInfo)]
enum Foo {
    A { is_valid: bool, name: String }
}

// We can build a type registry containing just this type:
let (type_id, registry) = make_type::<Foo>();
use scale_value::Value;

// Next, we can construct a runtime value of a similar shape:
let value = Value::named_variant("A", vec![
    ("is_valid".into(), Value::bool(true)),
    ("name".into(), Value::string("James")),
]);

// Given the type registry and ID, we can try to convert our Value into SCALE bytes:
let mut bytes = Vec::new();
scale_value::scale::encode_as_type(value.clone(), type_id, &registry, &mut bytes).unwrap();

// We can also go the other way, and decode out bytes back into the same Value:
let new_value = scale_value::scale::decode_as_type(&mut &*bytes, type_id, &registry).unwrap();

// The two values should equal each other (`.remove_context()` just removes the additional
// type information handed back when the value is decoded):
assert_eq!(value, new_value.remove_context());
```

Using the `serde` feature to convert a `Value` to/from some rust type via serde:

```rust
use scale_value::Value;
use serde::{ Serialize, Deserialize };

// Some type we want to be able to serialize/deserialize:
#[derive(Serialize, Deserialize, PartialEq, Debug)]
enum Foo {
    A { is_valid: bool, name: String },
    B(u8, bool)
}

// First, serialize a Value into the rust type:
let value = Value::named_variant("A", vec![
    ("name".into(), Value::string("James")),
    ("is_valid".into(), Value::bool(true)),
]);
let foo1: Foo = scale_value::serde::from_value(value).unwrap();
assert_eq!(foo1, Foo::A { is_valid: true, name: "James".into() });

// Next, deserialize the rust type back into a Value:
let new_value = scale_value::serde::to_value(foo).unwrap();
assert_eq!(value, new_value);
```

Check out [the documentation][docs] for a full API reference and more examples.

[ci]: https://github.com/paritytech/scale-value/actions?query=workflow%3ARust+branch%3Amaster
[ci-badge]: https://github.com/paritytech/scale-value/workflows/Rust/badge.svg
[crates]: https://crates.io/crates/scale-value
[crates-badge]: https://img.shields.io/crates/v/scale-value.svg
[docs]: https://docs.rs/scale-value
[docs-badge]: https://docs.rs/scale-value/badge.svg
[scale-info]: https://github.com/paritytech/scale-info
[scale-info-typedef]: https://docs.rs/scale-info/latest/scale_info/enum.TypeDef.html
[frame-metadata]: https://github.com/paritytech/frame-metadata