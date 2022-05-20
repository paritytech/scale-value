// Copyright (C) 2022 Parity Technologies (UK) Ltd. (admin@parity.io)
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

//! This crate exposes the [`Value`] type and related subtypes, which are used as the runtime
//! representations of SCALE encoded data (much like `serde_json::Value` is a runtime representation
//! of JSON data).
//!
//! Use the [`crate::scale`] module to encode and decode [`Value`]s to SCALE bytes. In most cases, you'll
//! use this module in conjunction with node metadata so that you have access to a type registry and know
//! which type you'll want to try and encode or decode your [`Value`] into.
//!
//! With the serde feature enabled, you can also use the [`crate::serde`] module to convert rust types to
//! and from [`Value`]s, or serialize/deserialize them to/from other formats like JSON.

#![deny(missing_docs)]

mod scale_impls;
#[cfg(feature = "serde")]
mod serde_impls;
mod value;

pub use value::{BitSequence, Composite, Primitive, Value, ValueDef, Variant};

/// Serializing and deserializing a [`crate::Value`] into/from other types via serde.
#[cfg(feature = "serde")]
pub mod serde {
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
	///     Value::u8(1),
	///     Value::u8(2),
	///     Value::u8(3),
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
	/// let value1 = Value::named_variant("A", vec![
	///     ("name".into(), Value::string("James")),
	///     ("is_valid".into(), Value::bool(true)),
	/// ]);
	/// let foo1: Foo = scale_value::serde::from_value(value1).unwrap();
	/// assert_eq!(foo1, Foo::A { is_valid: true, name: "James".into() });
	///
	/// let value2 = Value::unnamed_variant("B", vec![
	///     Value::u8(123),
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
	/// assert_eq!(val, Value::unnamed_composite(vec![
	///     Value::u8(1),
	///     Value::u8(2),
	///     Value::u8(3),
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
	/// assert_eq!(value, Value::named_variant("A", vec![
	///     ("is_valid".into(), Value::bool(true)),
	///     ("name".into(), Value::string("James")),
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
/// Given some known metadata type ID, encode and desome some [`crate::Value`]
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
/// let value = Value::named_variant("A", vec![
///     ("is_valid".into(), Value::bool(true)),
///     ("name".into(), Value::string("James")),
/// ]);
///
/// // Encode the Value to bytes:
/// let mut bytes = Vec::new();
/// scale_value::scale::encode_as_type(value.clone(), type_id, &registry, &mut bytes).unwrap();
///
/// // Decode the bytes back into a matching Value.
/// // This value contains contextual information about which type was used
/// // to decode each part of it, which we can throw away with `.remove_context()`.
/// let new_value = scale_value::scale::decode_as_type(&mut &*bytes, type_id, &registry).unwrap();
///
/// assert_eq!(value, new_value.remove_context());
/// ```
pub mod scale {
	pub use crate::scale_impls::{BitSequenceError, DecodeError, EncodeError, TypeId};
	pub use scale_info::PortableRegistry;

	/// Attempt to decode some SCALE encoded bytes into a value, by providing a pointer
	/// to the bytes (which will be moved forwards as bytes are used in the decoding),
	/// a type ID, and a type registry from which we'll look up the relevant type information.
	pub fn decode_as_type<Id: Into<TypeId>>(
		data: &mut &[u8],
		ty_id: Id,
		types: &PortableRegistry,
	) -> Result<crate::Value<TypeId>, DecodeError> {
		crate::scale_impls::decode_value_as_type(data, ty_id, types)
	}

	/// Attempt to encode some [`crate::Value<T>`] into SCALE bytes, by providing a pointer to the
	/// type ID that we'd like to encode it as, a type registry from which we'll look
	/// up the relevant type information, and a buffer to encode the bytes to.
	pub fn encode_as_type<T, Id: Into<TypeId>>(
		value: crate::Value<T>,
		ty_id: Id,
		types: &PortableRegistry,
		buf: &mut Vec<u8>,
	) -> Result<(), EncodeError<T>> {
		crate::scale_impls::encode_value_as_type(value, ty_id, types, buf)
	}
}
