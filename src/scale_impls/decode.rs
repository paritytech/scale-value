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

use super::{
	bit_sequence::{get_bitsequence_details, BitOrderTy, BitSequenceError, BitStoreTy},
	type_id::TypeId,
	ScaleType as Type, ScaleTypeDef as TypeDef,
};
use crate::value::{BitSequence, Composite, Primitive, Value, ValueDef, Variant};
use bitvec::{
	order::{BitOrder, Lsb0, Msb0},
	store::BitStore,
	vec::BitVec,
};
use codec::{Compact, Decode};
use scale_info::{
	form::PortableForm, Field, PortableRegistry, TypeDefArray, TypeDefBitSequence, TypeDefCompact,
	TypeDefComposite, TypeDefPrimitive, TypeDefSequence, TypeDefTuple, TypeDefVariant,
};

/// An error decoding SCALE bytes into a [`Value`].
#[derive(Debug, Clone, thiserror::Error, PartialEq)]
pub enum DecodeError {
	/// Some error emitted from a [`codec::Decode`] impl.
	#[error("{0}")]
	CodecError(#[from] codec::Error),
	/// We could not convert the [`u32`] that we found into a valid [`char`].
	#[error("{0} is expected to be a valid char, but is not")]
	InvalidChar(u32),
	/// We could not find the type given in the type registry provided.
	#[error("Cannot find type with ID {0}")]
	TypeIdNotFound(u32),
	/// We expected more bytes to finish decoding, but could not find them.
	#[error("Ran out of data during decoding")]
	Eof,
	/// We found a variant that does not match with any in the type we're trying to decode from.
	#[error("Could not find variant with index {0} in {1:?}")]
	VariantNotFound(u8, scale_info::TypeDefVariant<PortableForm>),
	/// The type we're trying to decode is supposed to be compact encoded, but that is not possible.
	#[error("Could not decode compact encoded type into {0:?}")]
	CannotDecodeCompactIntoType(Type),
	/// We ran into an error trying to decode a bit sequence.
	#[error("Cannot decode bit sequence: {0}")]
	BitSequenceError(BitSequenceError),
}

/// Decode data according to the [`TypeId`] provided.
/// The provided pointer to the data slice will be moved forwards as needed
/// depending on what was decoded.
pub fn decode_value_as_type<Id: Into<TypeId>>(
	data: &mut &[u8],
	ty_id: Id,
	types: &PortableRegistry,
) -> Result<Value<TypeId>, DecodeError> {
	let ty_id = ty_id.into();
	let ty = types.resolve(ty_id.id()).ok_or_else(|| DecodeError::TypeIdNotFound(ty_id.id()))?;

	let value = match ty.type_def() {
		TypeDef::Composite(inner) => {
			decode_composite_value(data, inner, types).map(ValueDef::Composite)
		}
		TypeDef::Sequence(inner) => {
			decode_sequence_value(data, inner, types).map(ValueDef::Composite)
		}
		TypeDef::Array(inner) => decode_array_value(data, inner, types).map(ValueDef::Composite),
		TypeDef::Tuple(inner) => decode_tuple_value(data, inner, types).map(ValueDef::Composite),
		TypeDef::Variant(inner) => decode_variant_value(data, inner, types).map(ValueDef::Variant),
		TypeDef::Primitive(inner) => decode_primitive_value(data, inner).map(ValueDef::Primitive),
		TypeDef::Compact(inner) => decode_compact_value(data, inner, types),
		TypeDef::BitSequence(inner) => {
			decode_bit_sequence_value(data, inner, types).map(ValueDef::BitSequence)
		}
	}?;

	Ok(Value { value, context: ty_id })
}

fn decode_composite_value(
	data: &mut &[u8],
	ty: &TypeDefComposite<PortableForm>,
	types: &PortableRegistry,
) -> Result<Composite<TypeId>, DecodeError> {
	decode_fields(data, ty.fields(), types)
}

fn decode_variant_value(
	data: &mut &[u8],
	ty: &TypeDefVariant<PortableForm>,
	types: &PortableRegistry,
) -> Result<Variant<TypeId>, DecodeError> {
	let index = *data.get(0).ok_or(DecodeError::Eof)?;
	*data = &data[1..];

	// Does a variant exist with the index we're looking for?
	let variant = ty
		.variants()
		.iter()
		.find(|v| v.index() == index)
		.ok_or_else(|| DecodeError::VariantNotFound(index, ty.clone()))?;

	let fields = decode_fields(data, variant.fields(), types)?;
	Ok(Variant { name: variant.name().clone(), values: fields })
}

/// Variant and Composite types both have fields; this will decode them into values.
fn decode_fields(
	data: &mut &[u8],
	fields: &[Field<PortableForm>],
	types: &PortableRegistry,
) -> Result<Composite<TypeId>, DecodeError> {
	let are_named = fields.iter().any(|f| f.name().is_some());
	let named_field_vals = fields.iter().map(|f| {
		let name = f.name().cloned().unwrap_or_default();
		decode_value_as_type(data, f.ty(), types).map(|val| (name, val))
	});

	if are_named {
		let vals = named_field_vals.collect::<Result<_, _>>()?;
		Ok(Composite::Named(vals))
	} else {
		let vals = named_field_vals.map(|r| r.map(|(_, v)| v)).collect::<Result<_, _>>()?;
		Ok(Composite::Unnamed(vals))
	}
}

fn decode_sequence_value(
	data: &mut &[u8],
	ty: &TypeDefSequence<PortableForm>,
	types: &PortableRegistry,
) -> Result<Composite<TypeId>, DecodeError> {
	// We assume that the sequence is preceeded by a compact encoded length, so that
	// we know how many values to try pulling out of the data.
	let len = Compact::<u64>::decode(data)?;
	let values: Vec<_> = (0..len.0)
		.map(|_| decode_value_as_type(data, ty.type_param(), types))
		.collect::<Result<_, _>>()?;

	Ok(Composite::Unnamed(values))
}

fn decode_array_value(
	data: &mut &[u8],
	ty: &TypeDefArray<PortableForm>,
	types: &PortableRegistry,
) -> Result<Composite<TypeId>, DecodeError> {
	// The length is known based on the type we want to decode into, so we pull out the number of items according
	// to that, and don't need a length to exist in the SCALE encoded bytes
	let values: Vec<_> = (0..ty.len())
		.map(|_| decode_value_as_type(data, ty.type_param(), types))
		.collect::<Result<_, _>>()?;

	Ok(Composite::Unnamed(values))
}

fn decode_tuple_value(
	data: &mut &[u8],
	ty: &TypeDefTuple<PortableForm>,
	types: &PortableRegistry,
) -> Result<Composite<TypeId>, DecodeError> {
	let values: Vec<_> = ty
		.fields()
		.iter()
		.map(|f| decode_value_as_type(data, f, types))
		.collect::<Result<_, _>>()?;

	Ok(Composite::Unnamed(values))
}

fn decode_primitive_value(
	data: &mut &[u8],
	ty: &TypeDefPrimitive,
) -> Result<Primitive, DecodeError> {
	let val = match ty {
		TypeDefPrimitive::Bool => Primitive::Bool(bool::decode(data)?),
		TypeDefPrimitive::Char => {
			// Treat chars as u32's
			let val = u32::decode(data)?;
			Primitive::Char(char::from_u32(val).ok_or(DecodeError::InvalidChar(val))?)
		}
		TypeDefPrimitive::Str => Primitive::String(String::decode(data)?),
		TypeDefPrimitive::U8 => Primitive::u128(u8::decode(data)? as u128),
		TypeDefPrimitive::U16 => Primitive::u128(u16::decode(data)? as u128),
		TypeDefPrimitive::U32 => Primitive::u128(u32::decode(data)? as u128),
		TypeDefPrimitive::U64 => Primitive::u128(u64::decode(data)? as u128),
		TypeDefPrimitive::U128 => Primitive::u128(u128::decode(data)?),
		TypeDefPrimitive::U256 => Primitive::U256(<[u8; 32]>::decode(data)?),
		TypeDefPrimitive::I8 => Primitive::i128(i8::decode(data)? as i128),
		TypeDefPrimitive::I16 => Primitive::i128(i16::decode(data)? as i128),
		TypeDefPrimitive::I32 => Primitive::i128(i32::decode(data)? as i128),
		TypeDefPrimitive::I64 => Primitive::i128(i64::decode(data)? as i128),
		TypeDefPrimitive::I128 => Primitive::i128(i128::decode(data)? as i128),
		TypeDefPrimitive::I256 => Primitive::I256(<[u8; 32]>::decode(data)?),
	};
	Ok(val)
}

fn decode_compact_value(
	data: &mut &[u8],
	ty: &TypeDefCompact<PortableForm>,
	types: &PortableRegistry,
) -> Result<ValueDef<TypeId>, DecodeError> {
	fn decode_compact(
		data: &mut &[u8],
		inner: &Type,
		types: &PortableRegistry,
	) -> Result<ValueDef<TypeId>, DecodeError> {
		use TypeDefPrimitive::*;
		let val = match inner.type_def() {
			// It's obvious how to decode basic primitive unsigned types, since we have impls for them.
			TypeDef::Primitive(U8) => {
				ValueDef::Primitive(Primitive::u128(Compact::<u8>::decode(data)?.0 as u128))
			}
			TypeDef::Primitive(U16) => {
				ValueDef::Primitive(Primitive::u128(Compact::<u16>::decode(data)?.0 as u128))
			}
			TypeDef::Primitive(U32) => {
				ValueDef::Primitive(Primitive::u128(Compact::<u32>::decode(data)?.0 as u128))
			}
			TypeDef::Primitive(U64) => {
				ValueDef::Primitive(Primitive::u128(Compact::<u64>::decode(data)?.0 as u128))
			}
			TypeDef::Primitive(U128) => {
				ValueDef::Primitive(Primitive::u128(Compact::<u128>::decode(data)?.0 as u128))
			}
			// A struct with exactly 1 field containing one of the above types can be sensibly compact encoded/decoded.
			TypeDef::Composite(composite) => {
				if composite.fields().len() != 1 {
					return Err(DecodeError::CannotDecodeCompactIntoType(inner.clone()));
				}

				// What type is the 1 field that we are able to decode?
				let field = &composite.fields()[0];
				let field_type_id = field.ty().id();
				let inner_ty = types
					.resolve(field_type_id)
					.ok_or(DecodeError::TypeIdNotFound(field_type_id))?;

				// Decode this inner type via compact decoding. This can recurse, in case
				// the inner type is also a 1-field composite type.
				let inner_value = Value {
					value: decode_compact(data, inner_ty, types)?,
					context: field.ty().into(),
				};

				// Wrap the inner type in a representation of this outer composite type.
				let composite = match field.name() {
					Some(name) => Composite::Named(vec![(name.clone(), inner_value)]),
					None => Composite::Unnamed(vec![inner_value]),
				};

				ValueDef::Composite(composite)
			}
			// For now, we give up if we have been asked for any other type:
			_cannot_decode_from => {
				return Err(DecodeError::CannotDecodeCompactIntoType(inner.clone()))
			}
		};

		Ok(val)
	}

	// Pluck the inner type out and run it through our compact decoding logic.
	let inner = types
		.resolve(ty.type_param().id())
		.ok_or_else(|| DecodeError::TypeIdNotFound(ty.type_param().id()))?;
	decode_compact(data, inner, types)
}

fn decode_bit_sequence_value(
	data: &mut &[u8],
	ty: &TypeDefBitSequence<PortableForm>,
	types: &PortableRegistry,
) -> Result<BitSequence, DecodeError> {
	let details = get_bitsequence_details(ty, types).map_err(DecodeError::BitSequenceError)?;

	fn to_bit_sequence<S: BitStore, O: BitOrder>(bits: BitVec<S, O>) -> BitSequence {
		bits.iter().by_vals().collect()
	}

	// Decode the native BitSequence type easily, or else convert to it from the type given.
	let bits = match details {
		(BitStoreTy::U8, BitOrderTy::Lsb0) => BitVec::<u8, Lsb0>::decode(data)?,
		(BitStoreTy::U8, BitOrderTy::Msb0) => to_bit_sequence(BitVec::<u8, Msb0>::decode(data)?),
		(BitStoreTy::U16, BitOrderTy::Lsb0) => to_bit_sequence(BitVec::<u16, Lsb0>::decode(data)?),
		(BitStoreTy::U16, BitOrderTy::Msb0) => to_bit_sequence(BitVec::<u16, Msb0>::decode(data)?),
		(BitStoreTy::U32, BitOrderTy::Lsb0) => to_bit_sequence(BitVec::<u32, Lsb0>::decode(data)?),
		(BitStoreTy::U32, BitOrderTy::Msb0) => to_bit_sequence(BitVec::<u32, Msb0>::decode(data)?),
		// BitVec doesn't impl BitStore on u64 if pointer width isn't 64 bit, avoid using this store type here
		// in that case to avoid compile errors (see https://docs.rs/bitvec/1.0.0/src/bitvec/store.rs.html#184)
		#[cfg(not(feature = "32bit_target"))]
		(BitStoreTy::U64, BitOrderTy::Lsb0) => to_bit_sequence(BitVec::<u64, Lsb0>::decode(data)?),
		#[cfg(not(feature = "32bit_target"))]
		(BitStoreTy::U64, BitOrderTy::Msb0) => to_bit_sequence(BitVec::<u64, Msb0>::decode(data)?),
		#[cfg(feature = "32bit_target")]
		(BitStoreTy::U64, _) => {
			return Err(DecodeError::BitSequenceError(BitSequenceError::StoreTypeNotSupported(
				"u64 (pointer-width on this compile target is not 64)".into(),
			)))
		}
	};

	Ok(bits)
}

#[cfg(test)]
mod test {

	use super::*;
	use codec::Encode;

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
