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

use crate::value::{Composite, Primitive, Value, ValueDef, Variant};
use scale_bits::Bits;
use scale_encode::error::ErrorKind;
use scale_encode::utils::{Composite as EncodeComposite, Variant as EncodeVariant};
use scale_encode::{EncodeAsType, Error};
use scale_info::form::PortableForm;
use scale_info::{PortableRegistry, TypeDef, TypeDefBitSequence};

impl<T> EncodeAsType for Value<T> {
	fn encode_as_type_to(
		&self,
		type_id: u32,
		types: &PortableRegistry,
		out: &mut Vec<u8>,
	) -> Result<(), Error> {
		match &self.value {
			ValueDef::Composite(val) => encode_composite(val, type_id, types, out),
			ValueDef::Variant(val) => encode_variant(val, type_id, types, out),
			ValueDef::Primitive(val) => encode_primitive(val, type_id, types, out),
			ValueDef::BitSequence(val) => encode_bitsequence(val, type_id, types, out),
		}
	}
}

fn encode_composite<T>(
	value: &Composite<T>,
	type_id: u32,
	types: &PortableRegistry,
	out: &mut Vec<u8>,
) -> Result<(), Error> {
	match value {
		Composite::Named(vals) => {
			let keyvals = vals.iter().map(|(key, val)| (Some(&**key), val as &dyn EncodeAsType));
			EncodeComposite(keyvals).encode_as_type_to(type_id, types, out)
		}
		Composite::Unnamed(vals) => {
			// special handling; "unnamed" sequences of bools/0/1 are an easy way to express/write bit sequences.
			// So, if the target type is a bit sequence, try to encode our unnamed sequence into it.
			let Some(ty) = types.resolve(type_id) else {
				return Err(Error::new(ErrorKind::TypeNotFound(type_id)))
			};
			if let TypeDef::BitSequence(bits) = ty.type_def() {
				return encode_vals_to_bitsequence(vals, bits, types, out);
			}

			let vals = vals.iter().map(|val| (None, val as &dyn EncodeAsType));
			EncodeComposite(vals).encode_as_type_to(type_id, types, out)
		}
	}
}

fn encode_vals_to_bitsequence<T>(
	vals: &[Value<T>],
	bits: &TypeDefBitSequence<PortableForm>,
	types: &PortableRegistry,
	out: &mut Vec<u8>,
) -> Result<(), Error> {
	let format = scale_bits::Format::from_metadata(bits, types).map_err(|e| Error::custom(e))?;
	let mut bools = Vec::with_capacity(vals.len());
	for (idx, value) in vals.iter().enumerate() {
		if let Some(v) = value.as_bool() {
			// support turning (true, false, true, true, false) into a bit sequence.
			bools.push(v);
		} else if let Some(v) = value.as_u128() {
			// support turning (1, 0, 1, 1, 0) into a bit sequence.
			if v == 0 || v == 1 {
				bools.push(if v == 0 { false } else { true })
			} else {
				return Err(Error::custom(
					"Cannot encode non-boolean/0/1 value into a bit sequence entry",
				)
				.at_idx(idx));
			}
		} else if let Some(v) = value.as_i128() {
			// support turning (1, 0, 1, 1, 0) into a bit sequence (if the number's are not unsigned it's still fine).
			if v == 0 || v == 1 {
				bools.push(if v == 0 { false } else { true })
			} else {
				return Err(Error::custom(
					"Cannot encode non-boolean/0/1 value into a bit sequence entry",
				)
				.at_idx(idx));
			}
		} else {
			// anything else is an error.
			return Err(Error::custom(
				"Cannot encode non-boolean/0/1 value into a bit sequence entry",
			)
			.at_idx(idx));
		}
	}

	scale_bits::encode_using_format_to(bools.into_iter(), format, out);
	Ok(())
}

fn encode_variant<T>(
	value: &Variant<T>,
	type_id: u32,
	types: &PortableRegistry,
	out: &mut Vec<u8>,
) -> Result<(), Error> {
	match &value.values {
		Composite::Named(vals) => {
			let keyvals = vals.iter().map(|(key, val)| (Some(&**key), val as &dyn EncodeAsType));
			EncodeVariant { name: &value.name, fields: EncodeComposite(keyvals) }
				.encode_as_type_to(type_id, types, out)
		}
		Composite::Unnamed(vals) => {
			let vals = vals.iter().map(|val| (None, val as &dyn EncodeAsType));
			EncodeVariant { name: &value.name, fields: EncodeComposite(vals) }
				.encode_as_type_to(type_id, types, out)
		}
	}
}

fn encode_primitive(
	value: &Primitive,
	type_id: u32,
	types: &PortableRegistry,
	bytes: &mut Vec<u8>,
) -> Result<(), Error> {
	match value {
		Primitive::Bool(val) => val.encode_as_type_to(type_id, types, bytes),
		Primitive::Char(val) => val.encode_as_type_to(type_id, types, bytes),
		Primitive::String(val) => val.encode_as_type_to(type_id, types, bytes),
		Primitive::U128(val) => val.encode_as_type_to(type_id, types, bytes),
		Primitive::I128(val) => val.encode_as_type_to(type_id, types, bytes),
		Primitive::U256(val) => val.encode_as_type_to(type_id, types, bytes),
		Primitive::I256(val) => val.encode_as_type_to(type_id, types, bytes),
	}
}

fn encode_bitsequence(
	value: &Bits,
	type_id: u32,
	types: &PortableRegistry,
	bytes: &mut Vec<u8>,
) -> Result<(), Error> {
	value.encode_as_type_to(type_id, types, bytes)
}

#[cfg(test)]
mod test {
	use super::*;
	use codec::{Compact, Encode};

	/// Given a type definition, return the PortableType and PortableRegistry
	/// that our decode functions expect.
	fn make_type<T: scale_info::TypeInfo + 'static>() -> (u32, PortableRegistry) {
		let m = scale_info::MetaType::new::<T>();
		let mut types = scale_info::Registry::new();
		let id = types.register_type(&m);
		let portable_registry: PortableRegistry = types.into();

		(id.id(), portable_registry)
	}

	// Attempt to SCALE encode a Value and expect it to match the standard Encode impl for the second param given.
	fn assert_can_encode_to_type<T: Encode + scale_info::TypeInfo + 'static>(
		value: Value<()>,
		ty: T,
	) {
		let expected = ty.encode();
		let mut buf = Vec::new();

		let (ty_id, types) = make_type::<T>();

		value.encode_as_type_to(ty_id, &types, &mut buf).expect("error encoding value as type");
		assert_eq!(expected, buf);
	}

	#[test]
	fn can_encode_basic_primitive_values() {
		assert_can_encode_to_type(Value::i128(123), 123i8);
		assert_can_encode_to_type(Value::i128(123), 123i16);
		assert_can_encode_to_type(Value::i128(123), 123i32);
		assert_can_encode_to_type(Value::i128(123), 123i64);
		assert_can_encode_to_type(Value::i128(123), 123i128);

		assert_can_encode_to_type(Value::u128(123), 123u8);
		assert_can_encode_to_type(Value::u128(123), 123u16);
		assert_can_encode_to_type(Value::u128(123), 123u32);
		assert_can_encode_to_type(Value::u128(123), 123u64);
		assert_can_encode_to_type(Value::u128(123), 123u128);

		assert_can_encode_to_type(Value::bool(true), true);
		assert_can_encode_to_type(Value::bool(false), false);

		assert_can_encode_to_type(Value::string("Hello"), "Hello");
		assert_can_encode_to_type(Value::string("Hello"), "Hello".to_string());
	}

	#[test]
	fn chars_encoded_like_numbers() {
		assert_can_encode_to_type(Value::char('j'), 'j' as u32);
		assert_can_encode_to_type(Value::char('j'), b'j');
	}

	#[test]
	fn can_encode_primitive_arrs_to_array() {
		use crate::Primitive;

		assert_can_encode_to_type(Value::primitive(Primitive::U256([12u8; 32])), [12u8; 32]);
		assert_can_encode_to_type(Value::primitive(Primitive::I256([12u8; 32])), [12u8; 32]);
	}

	#[test]
	fn can_encode_primitive_arrs_to_vecs() {
		use crate::Primitive;

		assert_can_encode_to_type(Value::primitive(Primitive::U256([12u8; 32])), vec![12u8; 32]);
		assert_can_encode_to_type(Value::primitive(Primitive::I256([12u8; 32])), vec![12u8; 32]);
	}

	#[test]
	fn can_encode_arrays() {
		let value = Value::unnamed_composite(vec![
			Value::u128(1),
			Value::u128(2),
			Value::u128(3),
			Value::u128(4),
		]);
		assert_can_encode_to_type(value, [1u16, 2, 3, 4]);
	}

	#[test]
	fn can_encode_variants() {
		#[derive(Encode, scale_info::TypeInfo)]
		enum Foo {
			Named { hello: String, foo: bool },
			Unnamed(u64, Vec<bool>),
		}

		let named_value = Value::named_variant(
			"Named",
			[
				// Deliverately a different order; order shouldn't matter:
				("foo", Value::bool(true)),
				("hello", Value::string("world")),
			],
		);
		assert_can_encode_to_type(named_value, Foo::Named { hello: "world".into(), foo: true });

		let unnamed_value = Value::unnamed_variant(
			"Unnamed",
			[
				Value::u128(123),
				Value::unnamed_composite(vec![
					Value::bool(true),
					Value::bool(false),
					Value::bool(true),
				]),
			],
		);
		assert_can_encode_to_type(unnamed_value, Foo::Unnamed(123, vec![true, false, true]));
	}

	#[test]
	fn can_encode_structs() {
		#[derive(Encode, scale_info::TypeInfo)]
		struct Foo {
			hello: String,
			foo: bool,
		}

		let named_value = Value::named_composite([
			// Deliverately a different order; order shouldn't matter:
			("foo", Value::bool(true)),
			("hello", Value::string("world")),
		]);
		assert_can_encode_to_type(named_value, Foo { hello: "world".into(), foo: true });
	}

	#[test]
	fn can_encode_tuples_from_named_composite() {
		let named_value =
			Value::named_composite([("hello", Value::string("world")), ("foo", Value::bool(true))]);
		assert_can_encode_to_type(named_value, ("world", true));
	}

	#[test]
	fn can_encode_tuples_from_unnamed_composite() {
		let unnamed_value = Value::unnamed_composite([Value::string("world"), Value::bool(true)]);
		assert_can_encode_to_type(unnamed_value, ("world", true));
	}

	#[test]
	fn can_encode_unnamed_composite_to_named_struct() {
		#[derive(Encode, scale_info::TypeInfo)]
		struct Foo {
			hello: String,
			foo: bool,
		}

		// This is useful because things like transaction calls are often named composites, but
		// we just want to be able to provide the correct values as simply as possible without
		// necessarily knowing the names.
		let unnamed_value = Value::unnamed_composite([Value::string("world"), Value::bool(true)]);
		assert_can_encode_to_type(unnamed_value, Foo { hello: "world".to_string(), foo: true });
	}

	#[test]
	fn can_encode_bitvecs() {
		use scale_bits::bits;

		// We have more thorough tests of bitvec encoding in scale-bits.
		// Here we just do a basic confirmation that bool composites or
		// bitsequences encode to the bits we'd expect.
		assert_can_encode_to_type(
			Value::bit_sequence(bits![0, 1, 1, 0, 0, 1]),
			bits![0, 1, 1, 0, 0, 1],
		);
		assert_can_encode_to_type(
			Value::unnamed_composite(vec![
				Value::bool(false),
				Value::bool(true),
				Value::bool(true),
				Value::bool(false),
				Value::bool(false),
				Value::bool(true),
			]),
			bits![0, 1, 1, 0, 0, 1],
		);
		assert_can_encode_to_type(
			Value::unnamed_composite(vec![
				Value::u128(0),
				Value::u128(1),
				Value::u128(1),
				Value::u128(0),
				Value::u128(0),
				Value::u128(1),
			]),
			bits![0, 1, 1, 0, 0, 1],
		);
		assert_can_encode_to_type(
			Value::unnamed_composite(vec![
				Value::i128(0),
				Value::i128(1),
				Value::i128(1),
				Value::i128(0),
				Value::i128(0),
				Value::i128(1),
			]),
			bits![0, 1, 1, 0, 0, 1],
		);
	}

	#[test]
	fn can_encode_to_compact_types() {
		assert_can_encode_to_type(Value::u128(123), Compact(123u64));
		assert_can_encode_to_type(Value::u128(123), Compact(123u64));
		assert_can_encode_to_type(Value::u128(123), Compact(123u64));
		assert_can_encode_to_type(Value::u128(123), Compact(123u64));

		// As a special case, as long as ultimately we have a primitive value, we can compact encode it:
		assert_can_encode_to_type(Value::unnamed_composite([Value::u128(123)]), Compact(123u64));
		assert_can_encode_to_type(
			Value::unnamed_composite([Value::named_composite([(
				"foo".to_string(),
				Value::u128(123),
			)])]),
			Compact(123u64),
		);
	}

	#[test]
	fn can_encode_skipping_newtype_wrappers() {
		// One layer of "newtype" can be ignored:
		#[derive(Encode, scale_info::TypeInfo)]
		struct Foo {
			inner: u32,
		}
		assert_can_encode_to_type(Value::u128(32), Foo { inner: 32 });

		// Two layers can be ignored:
		#[derive(Encode, scale_info::TypeInfo)]
		struct Bar(Foo);
		assert_can_encode_to_type(Value::u128(32), Bar(Foo { inner: 32 }));

		// Encoding a Composite to a Composite(Composite) shape is fine too:
		#[derive(Encode, scale_info::TypeInfo)]
		struct SomeBytes(Vec<u8>);
		assert_can_encode_to_type(
			Value::from_bytes(&[1, 2, 3, 4, 5]),
			SomeBytes(vec![1, 2, 3, 4, 5]),
		);
	}
}
