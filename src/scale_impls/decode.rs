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

use super::type_id::TypeId;
use crate::value::{Composite, Primitive, Value, ValueDef, Variant};
use scale_decode::visitor::CompactLocation;
use scale_info::PortableRegistry;

// This is emitted if something goes wrong decoding into a Value.
pub use scale_decode::visitor::DecodeError;

/// Decode data according to the [`TypeId`] provided.
/// The provided pointer to the data slice will be moved forwards as needed
/// depending on what was decoded.
pub fn decode_value_as_type<Id: Into<TypeId>>(
	data: &mut &[u8],
	ty_id: Id,
	types: &PortableRegistry,
) -> Result<Value<TypeId>, DecodeError> {
	scale_decode::decode(data, ty_id.into().id(), types, ValueVisitor)
}

// Sequences, Tuples and Arrays all have the same methods, so decode them in the same way:
macro_rules! to_unnamed_composite {
	($value:ident, $type_id:ident) => {{
		let mut vals = Vec::with_capacity($value.len());
		while let Some(val) = $value.decode_item(ValueVisitor)? {
			vals.push(val);
		}
		Ok(Value { value: ValueDef::Composite(Composite::Unnamed(vals)), context: $type_id.into() })
	}};
}

struct ValueVisitor;

impl scale_decode::visitor::Visitor for ValueVisitor {
	type Value = Value<TypeId>;
	type Error = DecodeError;

	fn visit_bool(
		self,
		value: bool,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		Ok(Value::bool(value).map_context(|_| type_id.into()))
	}
	fn visit_char(
		self,
		value: char,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		Ok(Value::char(value).map_context(|_| type_id.into()))
	}
	fn visit_u8(
		self,
		value: u8,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		self.visit_u128(value as u128, type_id)
	}
	fn visit_u16(
		self,
		value: u16,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		self.visit_u128(value as u128, type_id)
	}
	fn visit_u32(
		self,
		value: u32,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		self.visit_u128(value as u128, type_id)
	}
	fn visit_u64(
		self,
		value: u64,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		self.visit_u128(value as u128, type_id)
	}
	fn visit_u128(
		self,
		value: u128,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		Ok(Value::u128(value as u128).map_context(|_| type_id.into()))
	}
	fn visit_u256(
		self,
		value: &[u8; 32],
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		Ok(Value { value: ValueDef::Primitive(Primitive::U256(*value)), context: type_id.into() })
	}
	fn visit_i8(
		self,
		value: i8,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		self.visit_i128(value as i128, type_id)
	}
	fn visit_i16(
		self,
		value: i16,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		self.visit_i128(value as i128, type_id)
	}
	fn visit_i32(
		self,
		value: i32,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		self.visit_i128(value as i128, type_id)
	}
	fn visit_i64(
		self,
		value: i64,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		self.visit_i128(value as i128, type_id)
	}
	fn visit_i128(
		self,
		value: i128,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		Ok(Value::i128(value as i128).map_context(|_| type_id.into()))
	}
	fn visit_i256(
		self,
		value: &[u8; 32],
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		Ok(Value { value: ValueDef::Primitive(Primitive::U256(*value)), context: type_id.into() })
	}
	fn visit_sequence(
		self,
		value: &mut scale_decode::visitor::Sequence,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		to_unnamed_composite!(value, type_id)
	}
	fn visit_tuple(
		self,
		value: &mut scale_decode::visitor::Tuple,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		to_unnamed_composite!(value, type_id)
	}
	fn visit_array(
		self,
		value: &mut scale_decode::visitor::Array,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		to_unnamed_composite!(value, type_id)
	}
	fn visit_bitsequence(
		self,
		value: &mut scale_decode::visitor::BitSequence,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		Ok(Value {
			value: ValueDef::BitSequence(value.decode_bitsequence()?.to_u8_lsb0()),
			context: type_id.into(),
		})
	}
	fn visit_str(
		self,
		value: scale_decode::visitor::Str,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		Ok(Value::string(value.as_str()?).map_context(|_| type_id.into()))
	}
	fn visit_variant(
		self,
		value: &mut scale_decode::visitor::Variant,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		let values = visit_composite(value.fields())?;
		Ok(Value {
			value: ValueDef::Variant(Variant { name: value.name().to_owned(), values }),
			context: type_id.into(),
		})
	}
	fn visit_composite(
		self,
		value: &mut scale_decode::visitor::Composite,
		type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		Ok(Value { value: ValueDef::Composite(visit_composite(value)?), context: type_id.into() })
	}
	fn visit_compact_u8(
		self,
		value: scale_decode::visitor::Compact<u8>,
		_type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		visit_compact(value.value() as u128, value.locations())
	}
	fn visit_compact_u16(
		self,
		value: scale_decode::visitor::Compact<u16>,
		_type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		visit_compact(value.value() as u128, value.locations())
	}
	fn visit_compact_u32(
		self,
		value: scale_decode::visitor::Compact<u32>,
		_type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		visit_compact(value.value() as u128, value.locations())
	}
	fn visit_compact_u64(
		self,
		value: scale_decode::visitor::Compact<u64>,
		_type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		visit_compact(value.value() as u128, value.locations())
	}
	fn visit_compact_u128(
		self,
		value: scale_decode::visitor::Compact<u128>,
		_type_id: scale_decode::visitor::TypeId,
	) -> Result<Self::Value, Self::Error> {
		visit_compact(value.value(), value.locations())
	}
}

/// Visit a compact encoded value.
fn visit_compact(value: u128, locations: &[CompactLocation]) -> Result<Value<TypeId>, DecodeError> {
	let v = Primitive::U128(value as u128);
	Ok(value_from_compact_location(locations, v))
}

/// Given a compact location slice, build a value to represent said compact.
fn value_from_compact_location(loc: &[CompactLocation], value: Primitive) -> Value<TypeId> {
	let last_loc = loc
		.last()
		.expect("there should always be at least one location")
		.as_primitive()
		.expect("the last location is always primitive");

	fn nest_value(loc: &[CompactLocation], value: Value<TypeId>) -> Value<TypeId> {
		if let Some(last) = loc.last() {
			match last {
				CompactLocation::UnnamedComposite(type_id) => Value {
					value: ValueDef::Composite(Composite::Unnamed(vec![value])),
					context: (*type_id).into(),
				},
				CompactLocation::NamedComposite(type_id, name) => Value {
					value: ValueDef::Composite(Composite::Named(vec![((*name).to_owned(), value)])),
					context: (*type_id).into(),
				},
				// This is already handled:
				CompactLocation::Primitive(_) => value,
			}
		} else {
			value
		}
	}

	nest_value(
		&loc[..loc.len() - 1],
		Value { value: ValueDef::Primitive(value), context: last_loc.into() },
	)
}

/// Extract a named/unnamed Composite type out of scale_decode's Composite.
fn visit_composite(
	value: &mut scale_decode::visitor::Composite,
) -> Result<Composite<TypeId>, DecodeError> {
	let len = value.fields().len();
	let named = value.fields().get(0).map(|f| f.name().is_some()).unwrap_or(false);

	if named {
		let mut vals = Vec::with_capacity(len);
		while let Some((name, v)) = value.decode_item_with_name(ValueVisitor)? {
			vals.push((name.to_owned(), v));
		}
		Ok(Composite::Named(vals))
	} else {
		let mut vals = Vec::with_capacity(len);
		while let Some(v) = value.decode_item(ValueVisitor)? {
			vals.push(v);
		}
		Ok(Composite::Unnamed(vals))
	}
}

#[cfg(test)]
mod test {

	use super::*;
	use codec::{Compact, Encode};

	/// Given a type definition, return the PortableType and PortableRegistry
	/// that our decode functions expect.
	fn make_type<T: scale_info::TypeInfo + 'static>() -> (TypeId, PortableRegistry) {
		let m = scale_info::MetaType::new::<T>();
		let mut types = scale_info::Registry::new();
		let id = types.register_type(&m);
		let portable_registry: PortableRegistry = types.into();

		(id.into(), portable_registry)
	}

	/// Given a value to encode, and a representation of the decoded value, check that our decode functions
	/// successfully decodes the type to the expected value, based on the implicit SCALE type info that the type
	/// carries
	fn encode_decode_check<T: Encode + scale_info::TypeInfo + 'static>(val: T, exp: Value<()>) {
		encode_decode_check_explicit_info::<T, _>(val, exp)
	}

	/// Given a value to encode, a type to decode it back into, and a representation of
	/// the decoded value, check that our decode functions successfully decodes as expected.
	fn encode_decode_check_explicit_info<Ty: scale_info::TypeInfo + 'static, T: Encode>(
		val: T,
		ex: Value<()>,
	) {
		let encoded = val.encode();
		let encoded = &mut &*encoded;

		let (id, portable_registry) = make_type::<Ty>();

		// Can we decode?
		let val = decode_value_as_type(encoded, id, &portable_registry).expect("decoding failed");
		// Is the decoded value what we expected?
		assert_eq!(val.remove_context(), ex, "decoded value does not look like what we expected");
		// Did decoding consume all of the encoded bytes, as expected?
		assert_eq!(encoded.len(), 0, "decoding did not consume all of the encoded bytes");
	}

	#[test]
	fn decode_primitives() {
		encode_decode_check(true, Value::bool(true));
		encode_decode_check(false, Value::bool(false));
		encode_decode_check_explicit_info::<char, _>('a' as u32, Value::char('a'));
		encode_decode_check("hello", Value::string("hello"));
		encode_decode_check(
			"hello".to_string(), // String or &str (above) decode OK
			Value::string("hello"),
		);
		encode_decode_check(123u8, Value::u128(123));
		encode_decode_check(123u16, Value::u128(123));
		encode_decode_check(123u32, Value::u128(123));
		encode_decode_check(123u64, Value::u128(123));
		encode_decode_check(123u128, Value::u128(123));
		//// Todo [jsdw]: Can we test this if we need a TypeInfo param?:
		// encode_decode_check_explicit_info(
		// 	[123u8; 32], // Anything 32 bytes long will do here
		// 	Value::u256([123u8; 32]),
		// );
		encode_decode_check(123i8, Value::i128(123));
		encode_decode_check(123i16, Value::i128(123));
		encode_decode_check(123i32, Value::i128(123));
		encode_decode_check(123i64, Value::i128(123));
		encode_decode_check(123i128, Value::i128(123));
		//// Todo [jsdw]: Can we test this if we need a TypeInfo param?:
		// encode_decode_check_explicit_info(
		// 	[123u8; 32], // Anything 32 bytes long will do here
		// 	Value::i256([123u8; 32]),
		// );
	}

	#[test]
	fn decode_compact_primitives() {
		encode_decode_check(Compact(123u8), Value::u128(123));
		encode_decode_check(Compact(123u16), Value::u128(123));
		encode_decode_check(Compact(123u32), Value::u128(123));
		encode_decode_check(Compact(123u64), Value::u128(123));
		encode_decode_check(Compact(123u128), Value::u128(123));
	}

	#[test]
	fn decode_compact_named_wrapper_struct() {
		// A struct that can be compact encoded:
		#[derive(Encode, scale_info::TypeInfo)]
		struct MyWrapper {
			inner: u32,
		}
		impl From<Compact<MyWrapper>> for MyWrapper {
			fn from(val: Compact<MyWrapper>) -> MyWrapper {
				val.0
			}
		}
		impl codec::CompactAs for MyWrapper {
			type As = u32;

			fn encode_as(&self) -> &Self::As {
				&self.inner
			}
			fn decode_from(inner: Self::As) -> Result<Self, codec::Error> {
				Ok(MyWrapper { inner })
			}
		}

		encode_decode_check(
			Compact(MyWrapper { inner: 123 }),
			Value::named_composite(vec![("inner".to_string(), Value::u128(123))]),
		);
	}

	#[test]
	fn decode_compact_unnamed_wrapper_struct() {
		// A struct that can be compact encoded:
		#[derive(Encode, scale_info::TypeInfo)]
		struct MyWrapper(u32);
		impl From<Compact<MyWrapper>> for MyWrapper {
			fn from(val: Compact<MyWrapper>) -> MyWrapper {
				val.0
			}
		}
		impl codec::CompactAs for MyWrapper {
			type As = u32;

			// Node the requirement to return something with a lifetime tied
			// to self here. This means that we can't implement this for things
			// more complex than wrapper structs (eg `Foo(u32,u32,u32,u32)`) without
			// shenanigans, meaning that (hopefully) supporting wrapper struct
			// decoding and nothing fancier is sufficient.
			fn encode_as(&self) -> &Self::As {
				&self.0
			}
			fn decode_from(inner: Self::As) -> Result<Self, codec::Error> {
				Ok(MyWrapper(inner))
			}
		}

		encode_decode_check(
			Compact(MyWrapper(123)),
			Value::unnamed_composite(vec![Value::u128(123)]),
		);
	}

	#[test]
	fn decode_sequence_array_tuple_types() {
		encode_decode_check(
			vec![1i32, 2, 3],
			Value::unnamed_composite(vec![Value::i128(1), Value::i128(2), Value::i128(3)]),
		);
		encode_decode_check(
			[1i32, 2, 3], // compile-time length known
			Value::unnamed_composite(vec![Value::i128(1), Value::i128(2), Value::i128(3)]),
		);
		encode_decode_check(
			(1i32, true, 123456u128),
			Value::unnamed_composite(vec![Value::i128(1), Value::bool(true), Value::u128(123456)]),
		);
	}

	#[test]
	fn decode_variant_types() {
		#[derive(Encode, scale_info::TypeInfo)]
		enum MyEnum {
			Foo(bool),
			Bar { hi: String, other: u128 },
		}

		encode_decode_check(
			MyEnum::Foo(true),
			Value::unnamed_variant("Foo", vec![Value::bool(true)]),
		);
		encode_decode_check(
			MyEnum::Bar { hi: "hello".to_string(), other: 123 },
			Value::named_variant(
				"Bar",
				vec![
					("hi".to_string(), Value::string("hello".to_string())),
					("other".to_string(), Value::u128(123)),
				],
			),
		);
	}

	#[test]
	fn decode_composite_types() {
		#[derive(Encode, scale_info::TypeInfo)]
		struct Unnamed(bool, String, Vec<u8>);

		#[derive(Encode, scale_info::TypeInfo)]
		struct Named {
			is_valid: bool,
			name: String,
			bytes: Vec<u8>,
		}

		encode_decode_check(
			Unnamed(true, "James".into(), vec![1, 2, 3]),
			Value::unnamed_composite(vec![
				Value::bool(true),
				Value::string("James".to_string()),
				Value::unnamed_composite(vec![Value::u128(1), Value::u128(2), Value::u128(3)]),
			]),
		);
		encode_decode_check(
			Named { is_valid: true, name: "James".into(), bytes: vec![1, 2, 3] },
			Value::named_composite(vec![
				("is_valid", Value::bool(true)),
				("name", Value::string("James".to_string())),
				(
					"bytes",
					Value::unnamed_composite(vec![Value::u128(1), Value::u128(2), Value::u128(3)]),
				),
			]),
		);
	}

	#[test]
	fn decode_bit_sequence() {
		use bitvec::{
			bitvec,
			order::{Lsb0, Msb0},
		};

		encode_decode_check(
			bitvec![u8, Lsb0; 0, 1, 1, 0, 1, 0],
			Value::bit_sequence(bitvec![u8, Lsb0; 0, 1, 1, 0, 1, 0]),
		);
		encode_decode_check(
			bitvec![u8, Msb0; 0, 1, 1, 0, 1, 0],
			Value::bit_sequence(bitvec![u8, Lsb0; 0, 1, 1, 0, 1, 0]),
		);
		encode_decode_check(
			bitvec![u16, Lsb0; 0, 1, 1, 0, 1, 0],
			Value::bit_sequence(bitvec![u8, Lsb0; 0, 1, 1, 0, 1, 0]),
		);
		encode_decode_check(
			bitvec![u16, Msb0; 0, 1, 1, 0, 1, 0],
			Value::bit_sequence(bitvec![u8, Lsb0; 0, 1, 1, 0, 1, 0]),
		);
		encode_decode_check(
			bitvec![u32, Lsb0; 0, 1, 1, 0, 1, 0],
			Value::bit_sequence(bitvec![u8, Lsb0; 0, 1, 1, 0, 1, 0]),
		);
		encode_decode_check(
			bitvec![u32, Msb0; 0, 1, 1, 0, 1, 0],
			Value::bit_sequence(bitvec![u8, Lsb0; 0, 1, 1, 0, 1, 0]),
		);
		encode_decode_check(
			bitvec![u64, Lsb0; 0, 1, 1, 0, 1, 0],
			Value::bit_sequence(bitvec![u8, Lsb0; 0, 1, 1, 0, 1, 0]),
		);
		encode_decode_check(
			bitvec![u64, Msb0; 0, 1, 1, 0, 1, 0],
			Value::bit_sequence(bitvec![u8, Lsb0; 0, 1, 1, 0, 1, 0]),
		);
	}
}
