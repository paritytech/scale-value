// Copyright (C) 2022-2023 Parity Technologies (UK) Ltd. (admin@parity.io)
// This file is a part of the scale-value crate.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//         http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/*!
This crate exposes the [`Value`] type and related subtypes, which are used as the runtime
representations of SCALE encoded data (much like `serde_json::Value` is a runtime representation
of JSON data).

[`Value`]'s can be:

- Encoded and decoded from SCALE bytes via [`::scale_encode::EncodeAsType`] and [`::scale_decode::DecodeAsType`]
  traits (or by calling [`crate::scale::decode_as_type`] and [`crate::scale::encode_as_type`]).
- Parsed to and from strings by calling [`crate::stringify::from_str`] and [`crate::stringify::to_string`]).
  Parsing from strings requires the `from_string` feature to be enabled.
- Serialized and deserialized via `serde` traits (for example, to and from JSON). They can also be serialized
  from and to other types with the relevant serde derives on. These require the `serde` feature to be enabled.
- Accessed ergonomically via the [`At`] trait.
*/
#![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod at;
mod macros;
mod prelude;
mod scale_impls;
#[cfg(feature = "serde")]
mod serde_impls;
mod string_impls;
mod value_type;

// Traits to allow indexing into values.
pub use at::{At, Location};

// The value definition.
pub use value_type::{BitSequence, Composite, Primitive, Value, ValueDef, Variant};

/// Serializing and deserializing a [`crate::Value`] into/from other types via serde.
#[cfg(feature = "serde")]
pub mod serde {
    use crate::prelude::*;
    pub use crate::serde_impls::{DeserializerError, SerializerError, ValueSerializer};

    /// Attempt to convert a [`crate::Value`] into another type via serde.
    ///
    /// # Examples
    ///
    /// Use serde to convert a value into a built-in type:
    ///
    /// ```rust
    /// use scale_value::Value;
    ///
    /// let value = Value::unnamed_composite(vec![
    ///     Value::u128(1),
    ///     Value::u128(2),
    ///     Value::u128(3),
    /// ]);
    ///
    /// let arr: [u8; 3] = scale_value::serde::from_value(value).unwrap();
    /// ```
    ///
    /// Converting values to a custom type:
    ///
    /// ```rust
    /// use scale_value::Value;
    /// use serde::{ Serialize, Deserialize };
    ///
    /// #[derive(Serialize, Deserialize, PartialEq, Debug)]
    /// enum Foo {
    ///     A { is_valid: bool, name: String },
    ///     B(u8, bool)
    /// }
    ///
    /// let value1 = Value::named_variant("A", [
    ///     ("name", Value::string("James")),
    ///     ("is_valid", Value::bool(true)),
    /// ]);
    /// let foo1: Foo = scale_value::serde::from_value(value1).unwrap();
    /// assert_eq!(foo1, Foo::A { is_valid: true, name: "James".into() });
    ///
    /// let value2 = Value::unnamed_variant("B", [
    ///     Value::u128(123),
    ///     Value::bool(true),
    /// ]);
    /// let foo2: Foo = scale_value::serde::from_value(value2).unwrap();
    /// assert_eq!(foo2, Foo::B(123, true));
    /// ```
    pub fn from_value<'de, Ctx, T: serde::Deserialize<'de>>(
        value: crate::Value<Ctx>,
    ) -> Result<T, DeserializerError> {
        T::deserialize(value)
    }

    /// Attempt to convert some type into a [`crate::Value`] via serde.
    ///
    /// # Examples
    ///
    /// Convert a built-in array of values into a [`crate::Value`]:
    ///
    /// ```rust
    /// use scale_value::Value;
    ///
    /// let arr = [1u8, 2u8, 3u8];
    ///
    /// let val = scale_value::serde::to_value(arr).unwrap();
    /// assert_eq!(val, Value::unnamed_composite([
    ///     Value::u128(1),
    ///     Value::u128(2),
    ///     Value::u128(3),
    /// ]));
    /// ```
    ///
    /// Converting some custom type to a [`crate::Value`]:
    ///
    /// ```rust
    /// use scale_value::Value;
    /// use serde::{ Serialize, Deserialize };
    ///
    /// #[derive(Serialize, Deserialize, PartialEq, Debug)]
    /// enum Foo {
    ///     A { is_valid: bool, name: String },
    ///     B(u8, bool)
    /// }
    ///
    /// let foo = Foo::A { is_valid: true, name: "James".into() };
    ///
    /// let value = scale_value::serde::to_value(foo).unwrap();
    /// assert_eq!(value, Value::named_variant("A", [
    ///     ("is_valid", Value::bool(true)),
    ///     ("name", Value::string("James")),
    /// ]));
    /// ```
    pub fn to_value<T: serde::Serialize>(ty: T) -> Result<crate::Value<()>, SerializerError> {
        ty.serialize(ValueSerializer)
    }
}

/// Encoding and decoding SCALE bytes into a [`crate::Value`].
///
/// # Exmaple
///
/// Given some known metadata type ID, encode and decode some [`crate::Value`]
/// to SCALE bytes.
///
/// ```rust
/// # fn make_type<T: scale_info::TypeInfo + 'static>() -> (u32, scale_info::PortableRegistry) {
/// #     let m = scale_info::MetaType::new::<T>();
/// #     let mut types = scale_info::Registry::new();
/// #     let id = types.register_type(&m);
/// #     let portable_registry: scale_info::PortableRegistry = types.into();
/// #     (id.id(), portable_registry)
/// # }
/// # let (type_id, registry) = make_type::<Foo>();
/// use scale_value::Value;
///
/// // Imagine we have a `registry` (of type [`scale_info::PortableRegistry`]) containing this type,
/// // and a `type_id` (a `u32`) pointing to it in the registry.
/// #[derive(scale_info::TypeInfo)]
/// enum Foo {
///     A { is_valid: bool, name: String }
/// }
///
/// // Given that, we can encode/decode something with that shape to/from SCALE bytes:
/// let value = Value::named_variant("A", [
///     ("is_valid", Value::bool(true)),
///     ("name", Value::string("James")),
/// ]);
///
/// // Encode the Value to bytes:
/// let mut bytes = Vec::new();
/// scale_value::scale::encode_as_type(&value, type_id, &registry, &mut bytes).unwrap();
///
/// // Decode the bytes back into a matching Value.
/// // This value contains contextual information about which type was used
/// // to decode each part of it, which we can throw away with `.remove_context()`.
/// let new_value = scale_value::scale::decode_as_type(&mut &*bytes, type_id, &registry).unwrap();
///
/// assert_eq!(value, new_value.remove_context());
/// ```
pub mod scale {
    use crate::prelude::*;
    use scale_encode::EncodeAsType;

    pub use crate::scale_impls::{DecodeError, TypeId};
    pub use scale_encode::Error as EncodeError;
    pub use scale_info::PortableRegistry;

    /// Attempt to decode some SCALE encoded bytes into a value, by providing a pointer
    /// to the bytes (which will be moved forwards as bytes are used in the decoding),
    /// a type ID, and a type registry from which we'll look up the relevant type information.
    pub fn decode_as_type(
        data: &mut &[u8],
        ty_id: TypeId,
        types: &PortableRegistry,
    ) -> Result<crate::Value<TypeId>, DecodeError> {
        crate::scale_impls::decode_value_as_type(data, ty_id, types)
    }

    /// Attempt to encode some [`crate::Value<T>`] into SCALE bytes, by providing a pointer to the
    /// type ID that we'd like to encode it as, a type registry from which we'll look
    /// up the relevant type information, and a buffer to encode the bytes to.
    pub fn encode_as_type<T: Clone>(
        value: &crate::Value<T>,
        ty_id: TypeId,
        types: &PortableRegistry,
        buf: &mut Vec<u8>,
    ) -> Result<(), EncodeError> {
        value.encode_as_type_to(ty_id, types, buf)
    }
}

/// Converting a [`crate::Value`] to or from strings.
pub mod stringify {
    use crate::prelude::*;

    #[cfg(feature = "from-string")]
    pub use crate::string_impls::{
        FromStrBuilder, ParseBitSequenceError, ParseCharError, ParseComplexError, ParseError,
        ParseErrorKind, ParseNumberError, ParseStringError,
    };

    /// This module provides custom parsers that work alongside [`crate::stringify::from_str_custom`]
    /// and extend the syntax to support parsing common formats into [`crate::Value`]'s. See
    /// [`crate::stringify::from_str_custom`] for a usage example.
    #[cfg(feature = "from-string")]
    pub mod custom_parsers {
        #[cfg(feature = "parser-ss58")]
        pub use crate::string_impls::parse_ss58;
        pub use crate::string_impls::{parse_hex, ParseHexError};
    }

    /// Attempt to parse a string into a [`crate::Value<()>`], returning a tuple
    /// consisting of a result (either the value or a [`ParseError`] containing
    /// location and error information) and the remainder of the string that wasn't
    /// parsed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use scale_value::Value;
    ///
    /// fn to_value(str: &str) -> Value {
    ///     scale_value::stringify::from_str(str).0.unwrap()
    /// }
    ///
    /// // Primitive values:
    /// assert_eq!(to_value("1"), Value::u128(1));
    /// assert_eq!(to_value("-1"), Value::i128(-1));
    /// assert_eq!(to_value("true"), Value::bool(true));
    /// assert_eq!(to_value("'a'"), Value::char('a'));
    /// assert_eq!(to_value("\"hi\""), Value::string("hi"));
    ///
    /// // Named composite values look a bit like rust structs:
    /// let value = to_value("{ a: true, b: \"hello\" }");
    /// assert_eq!(
    ///     value,
    ///     Value::named_composite(vec![
    ///         ("a", Value::bool(true)),
    ///         ("b", Value::string("hello"))
    ///     ])
    /// );
    ///
    /// // Unnamed composite values look a bit like rust tuples:
    /// let value = to_value("(true, \"hello\")");
    /// assert_eq!(
    ///     value,
    ///     Value::unnamed_composite(vec![
    ///         Value::bool(true),
    ///         Value::string("hello")
    ///     ])
    /// );
    ///
    /// // Variant values (named or unnamed) are just the above with a variant name
    /// // prefixed:
    /// let value = to_value("MyVariant { a: true, b: \"hello\" }");
    /// assert_eq!(
    ///     value,
    ///     Value::named_variant(
    ///         "MyVariant",
    ///         vec![
    ///             ("a", Value::bool(true)),
    ///             ("b", Value::string("hello"))
    ///         ]
    ///     )
    /// );
    ///
    /// // Bit sequences can be encoded from unnamed composites, but we have a
    /// // compact syntax for them too:
    /// assert_eq!(
    ///     to_value("<0101>"),
    ///     Value::bit_sequence(scale_bits::Bits::from_iter([false, true, false, true]))
    /// );
    /// ```
    #[cfg(feature = "from-string")]
    pub fn from_str(s: &str) -> (Result<crate::Value<()>, ParseError>, &str) {
        crate::string_impls::FromStrBuilder::new().parse(s)
    }

    /// This is similar to [`from_str`], except that it returns a [`FromStrBuilder`],
    /// which allows for some additional configuration in how strings are parsed.
    ///
    /// # Example
    ///
    /// ```rust
    /// # // Example only runs when parser-ss58 feature is enabled:
    /// # #[cfg(not(feature = "parser-ss58"))]
    /// # fn main() {}
    /// # #[cfg(feature = "parser-ss58")]
    /// # fn main() {
    /// #
    /// use scale_value::Value;
    /// use scale_value::stringify::custom_parsers;
    ///
    /// fn to_value(str: &str) -> Value {
    ///     scale_value::stringify::from_str_custom()
    ///         // You can write your own custom parser, but for
    ///         // this example, we just use some provided ones.
    ///         .add_custom_parser(custom_parsers::parse_hex)
    ///         // Requires the parser-ss58 feature:
    ///         .add_custom_parser(custom_parsers::parse_ss58)
    ///         .parse(str)
    ///         .0
    ///         .unwrap()
    /// }
    ///
    /// // Hex strings will now be parsed into unnamed composite types
    /// let value = to_value("(1,2,0x030405)");
    /// assert_eq!(
    ///     value,
    ///     Value::unnamed_composite(vec![
    ///         Value::u128(1),
    ///         Value::u128(2),
    ///         Value::unnamed_composite(vec![
    ///             Value::u128(3),
    ///             Value::u128(4),
    ///             Value::u128(5),
    ///         ])
    ///     ])
    /// );
    ///
    /// // ss58 addresses will also become unnamed composite types
    /// let value = to_value(r#"{
    ///     name: "Alice",
    ///     address: 5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty
    /// }"#);
    ///
    /// // Manually obtain and decode the hex value for the address:
    /// let addr: Vec<_> = hex::decode("8eaf04151687736326c9fea17e25fc5287613693c912909cb226aa4794f26a48")
    ///     .unwrap()
    ///     .into_iter()
    ///     .map(|b| Value::u128(b as u128))
    ///     .collect();
    ///
    /// assert_eq!(
    ///     value,
    ///     Value::named_composite(vec![
    ///         ("name", Value::string("Alice")),
    ///         ("address", Value::unnamed_composite(addr))
    ///     ])
    /// )
    /// #
    /// # }
    /// ```
    #[cfg(feature = "from-string")]
    pub fn from_str_custom() -> FromStrBuilder {
        crate::string_impls::FromStrBuilder::new()
    }

    /// Identical to calling `to_string()` on the [`crate::Value`], but here just
    /// to make it a little more obvious that this is the inverse of [`from_str`].
    ///
    /// # Panics
    ///
    /// Panics if a `Primitive::U256`/`Primitive::I256` are a part of the value,
    /// since we cannot properly format and parse those at the moment.
    pub fn to_string<T>(v: &crate::Value<T>) -> String {
        v.to_string()
    }
}
