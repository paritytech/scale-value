// Copyright 2019-2022 Parity Technologies (UK) Ltd.
// This file is part of subxt.
//
// subxt is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// subxt is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with subxt.  If not, see <http://www.gnu.org/licenses/>.

//! This [`Serializer`] impl allows types implementing `Serialize` to be converted
//! into [`Value`]s.

use crate::{Composite, Primitive, Value, ValueDef};
use serde::{
	ser::{
		SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant, SerializeTuple,
		SerializeTupleStruct, SerializeTupleVariant,
	},
	Serializer,
};

pub struct ValueSerializer;

#[derive(thiserror::Error, Debug, Clone, PartialEq)]
pub enum Error {
	#[error("{0}")]
	Custom(String),
	#[error("Floats do not have a SCALE compatible representation, and so cannot be serialized to Values")]
	CannotSerializeFloats,
	#[error("Map keys must be strings or string-like")]
	MapKeyMustBeStringlike,
}

impl serde::ser::Error for Error {
	fn custom<T>(msg: T) -> Self
	where
		T: std::fmt::Display,
	{
		Error::Custom(msg.to_string())
	}
}

macro_rules! serialize_prim {
	($name:ident $ty:ident) => {
		fn $name(self, v: $ty) -> Result<Self::Ok, Self::Error> {
			Ok(Value::$ty(v))
		}
	};
}

impl Serializer for ValueSerializer {
	type Ok = Value<()>;
	type Error = Error;

	type SerializeSeq = UnnamedCompositeSerializer;
	type SerializeTuple = UnnamedCompositeSerializer;
	type SerializeTupleStruct = UnnamedCompositeSerializer;
	type SerializeTupleVariant = UnnamedCompositeSerializer;
	type SerializeMap = NamedCompositeSerializer;
	type SerializeStruct = NamedCompositeSerializer;
	type SerializeStructVariant = NamedCompositeSerializer;

	serialize_prim!(serialize_bool bool);
	serialize_prim!(serialize_i8 i8);
	serialize_prim!(serialize_i16 i16);
	serialize_prim!(serialize_i32 i32);
	serialize_prim!(serialize_i64 i64);
	serialize_prim!(serialize_i128 i128);
	serialize_prim!(serialize_u8 u8);
	serialize_prim!(serialize_u16 u16);
	serialize_prim!(serialize_u32 u32);
	serialize_prim!(serialize_u64 u64);
	serialize_prim!(serialize_u128 u128);
	serialize_prim!(serialize_char char);

	fn serialize_f32(self, _v: f32) -> Result<Self::Ok, Self::Error> {
		Err(Error::CannotSerializeFloats)
	}
	fn serialize_f64(self, _v: f64) -> Result<Self::Ok, Self::Error> {
		Err(Error::CannotSerializeFloats)
	}

	fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
		Ok(Value::string(v.to_string()))
	}

	fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
		let bytes = v.iter().map(|b| Value::u8(*b)).collect();
		Ok(Value::unnamed_composite(bytes))
	}

	fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
		Ok(Value::variant("None".to_string(), Composite::Unnamed(Vec::new())))
	}

	fn serialize_some<T: ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error>
	where
		T: serde::Serialize,
	{
		let inner = value.serialize(ValueSerializer)?;
		Ok(Value::variant("Some".to_string(), Composite::Unnamed(vec![inner])))
	}

	fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
		Ok(Value::unnamed_composite(Vec::new()))
	}

	fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
		Ok(Value::unnamed_composite(Vec::new()))
	}

	fn serialize_unit_variant(
		self,
		_name: &'static str,
		_variant_index: u32,
		variant: &'static str,
	) -> Result<Self::Ok, Self::Error> {
		Ok(Value::variant(variant.to_string(), Composite::Unnamed(Vec::new())))
	}

	fn serialize_newtype_struct<T: ?Sized>(
		self,
		_name: &'static str,
		value: &T,
	) -> Result<Self::Ok, Self::Error>
	where
		T: serde::Serialize,
	{
		let inner = value.serialize(ValueSerializer)?;
		Ok(Value::unnamed_composite(vec![inner]))
	}

	fn serialize_newtype_variant<T: ?Sized>(
		self,
		_name: &'static str,
		_variant_index: u32,
		variant: &'static str,
		value: &T,
	) -> Result<Self::Ok, Self::Error>
	where
		T: serde::Serialize,
	{
		let inner = value.serialize(ValueSerializer)?;
		Ok(Value::variant(variant.to_string(), Composite::Unnamed(vec![inner])))
	}

	fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
		Ok(Self::SerializeSeq::new_composite())
	}

	fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
		Ok(Self::SerializeTuple::new_composite())
	}

	fn serialize_tuple_struct(
		self,
		_name: &'static str,
		_len: usize,
	) -> Result<Self::SerializeTupleStruct, Self::Error> {
		Ok(Self::SerializeTupleStruct::new_composite())
	}

	fn serialize_tuple_variant(
		self,
		_name: &'static str,
		_variant_index: u32,
		variant: &'static str,
		_len: usize,
	) -> Result<Self::SerializeTupleVariant, Self::Error> {
		Ok(Self::SerializeTupleVariant::new_variant(variant.into()))
	}

	fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
		Ok(Self::SerializeMap::new_composite())
	}

	fn serialize_struct(
		self,
		_name: &'static str,
		_len: usize,
	) -> Result<Self::SerializeStruct, Self::Error> {
		Ok(Self::SerializeStruct::new_composite())
	}

	fn serialize_struct_variant(
		self,
		_name: &'static str,
		_variant_index: u32,
		variant: &'static str,
		_len: usize,
	) -> Result<Self::SerializeStructVariant, Self::Error> {
		Ok(Self::SerializeStructVariant::new_variant(variant.into()))
	}
}

// Serializes anything that should end up as an unnamed composite value:
pub struct UnnamedCompositeSerializer {
	// Only present if the thing should be a variant:
	variant_name: Option<String>,
	values: Vec<Value<()>>,
}

impl UnnamedCompositeSerializer {
	fn new_composite() -> UnnamedCompositeSerializer {
		UnnamedCompositeSerializer { variant_name: None, values: Vec::new() }
	}

	fn new_variant(variant_name: String) -> UnnamedCompositeSerializer {
		UnnamedCompositeSerializer { variant_name: Some(variant_name), values: Vec::new() }
	}

	fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Error>
	where
		T: serde::Serialize,
	{
		let inner = value.serialize(ValueSerializer)?;
		self.values.push(inner);
		Ok(())
	}

	fn end(self) -> Result<Value<()>, Error> {
		match self.variant_name {
			Some(name) => Ok(Value::variant(name, Composite::Unnamed(self.values))),
			None => Ok(Value::unnamed_composite(self.values)),
		}
	}
}

impl SerializeSeq for UnnamedCompositeSerializer {
	type Ok = Value<()>;
	type Error = Error;

	fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
	where
		T: serde::Serialize,
	{
		self.serialize_element(value)
	}

	fn end(self) -> Result<Self::Ok, Self::Error> {
		self.end()
	}
}

impl SerializeTuple for UnnamedCompositeSerializer {
	type Ok = Value<()>;
	type Error = Error;

	fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
	where
		T: serde::Serialize,
	{
		self.serialize_element(value)
	}

	fn end(self) -> Result<Self::Ok, Self::Error> {
		self.end()
	}
}

impl SerializeTupleStruct for UnnamedCompositeSerializer {
	type Ok = Value<()>;
	type Error = Error;

	fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
	where
		T: serde::Serialize,
	{
		self.serialize_element(value)
	}

	fn end(self) -> Result<Self::Ok, Self::Error> {
		self.end()
	}
}

impl SerializeTupleVariant for UnnamedCompositeSerializer {
	type Ok = Value<()>;
	type Error = Error;

	fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
	where
		T: serde::Serialize,
	{
		self.serialize_element(value)
	}

	fn end(self) -> Result<Self::Ok, Self::Error> {
		self.end()
	}
}

// Serializes things into named composite types.
pub struct NamedCompositeSerializer {
	// Only present if the thing should be a variant:
	variant_name: Option<String>,
	values: Vec<(String, Value<()>)>,
	key: Option<String>,
}

impl NamedCompositeSerializer {
	fn new_composite() -> Self {
		NamedCompositeSerializer { variant_name: None, values: Vec::new(), key: None }
	}

	fn new_variant(variant_name: String) -> Self {
		NamedCompositeSerializer { variant_name: Some(variant_name), values: Vec::new(), key: None }
	}

	fn serialize_field<T: ?Sized>(&mut self, key: &str, value: &T) -> Result<(), Error>
	where
		T: serde::Serialize,
	{
		let key = key.to_string();
		let inner = value.serialize(ValueSerializer)?;
		self.values.push((key, inner));
		Ok(())
	}

	fn end(self) -> Result<Value<()>, Error> {
		match self.variant_name {
			Some(name) => Ok(Value::variant(name, Composite::Named(self.values))),
			None => Ok(Value::named_composite(self.values)),
		}
	}
}

impl SerializeMap for NamedCompositeSerializer {
	type Ok = Value<()>;
	type Error = Error;

	fn serialize_key<T: ?Sized>(&mut self, key: &T) -> Result<(), Self::Error>
	where
		T: serde::Serialize,
	{
		let inner = key.serialize(ValueSerializer)?;
		// Map keys must be stringish, because named composite values are strings
		// and will be matched with the corresponding field names on struct types
		// to SCALE encode/decode.
		let key = match inner.value {
			ValueDef::Primitive(Primitive::String(s)) => s,
			ValueDef::Primitive(Primitive::Char(c)) => c.to_string(),
			_ => return Err(Error::MapKeyMustBeStringlike),
		};
		self.key = Some(key);
		Ok(())
	}

	fn serialize_value<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
	where
		T: serde::Serialize,
	{
		let key = self.key.take().expect("serialize_key must be called prior to serialize_value");
		self.serialize_field(&key, value)
	}

	fn end(self) -> Result<Self::Ok, Self::Error> {
		self.end()
	}
}

impl SerializeStruct for NamedCompositeSerializer {
	type Ok = Value<()>;
	type Error = Error;

	fn serialize_field<T: ?Sized>(
		&mut self,
		key: &'static str,
		value: &T,
	) -> Result<(), Self::Error>
	where
		T: serde::Serialize,
	{
		self.serialize_field(key, value)
	}

	fn end(self) -> Result<Self::Ok, Self::Error> {
		self.end()
	}
}

impl SerializeStructVariant for NamedCompositeSerializer {
	type Ok = Value<()>;
	type Error = Error;

	fn serialize_field<T: ?Sized>(
		&mut self,
		key: &'static str,
		value: &T,
	) -> Result<(), Self::Error>
	where
		T: serde::Serialize,
	{
		self.serialize_field(key, value)
	}

	fn end(self) -> Result<Self::Ok, Self::Error> {
		self.end()
	}
}

#[cfg(test)]
mod test {
	use super::ValueSerializer;
	use crate::{Composite, Value};
	use serde::{Deserialize, Serialize};
	use std::fmt::Debug;

	// Make sure that things can serialize and deserialize back losslessly.
	fn assert_ser_de<T: Serialize + Deserialize<'static> + Debug + PartialEq>(val: T) {
		let actual = val.serialize(ValueSerializer).expect("can serialize");
		let actual = T::deserialize(actual).expect("can deserialize again");
		assert_eq!(val, actual, "value did not come deserialize back to the same");
	}

	// Make sure that things can serialize and deserialize back losslessly and to the expected Value.
	fn assert_ser_de_eq<T: Serialize + Deserialize<'static> + Debug + PartialEq>(
		val: T,
		value: Value<()>,
	) {
		// serialize and compare:
		let actual = val.serialize(ValueSerializer).expect("can serialize");
		assert_eq!(value, actual, "serializing mismatch");
		// deserialize back and check we get the same thing back out:
		let actual = T::deserialize(actual).expect("can deserialize again");
		assert_eq!(val, actual, "deserialing mismatch");
	}

	#[test]
	fn ser_de_primitives() {
		assert_ser_de_eq(123u8, Value::u8(123));
		assert_ser_de_eq(123u16, Value::u16(123));
		assert_ser_de_eq(123u32, Value::u32(123));
		assert_ser_de_eq(123u64, Value::u64(123));
		assert_ser_de_eq(123u128, Value::u128(123));

		assert_ser_de_eq(123i8, Value::i8(123));
		assert_ser_de_eq(123i16, Value::i16(123));
		assert_ser_de_eq(123i32, Value::i32(123));
		assert_ser_de_eq(123i64, Value::i64(123));
		assert_ser_de_eq(123i128, Value::i128(123));

		assert_ser_de_eq(true, Value::bool(true));
		assert_ser_de_eq(false, Value::bool(false));

		assert_ser_de_eq("hello".to_string(), Value::string("hello"));
		assert_ser_de_eq('a', Value::char('a'));
	}

	#[test]
	fn ser_de_optionals() {
		let val = Value::variant("Some".to_string(), Composite::Unnamed(vec![Value::u8(123)]));
		assert_ser_de_eq(Some(123u8), val);

		let val = Value::variant("None".to_string(), Composite::Unnamed(Vec::new()));
		assert_ser_de_eq(None as Option<u8>, val);
	}

	#[test]
	fn ser_de_unit_struct() {
		#[derive(Deserialize, Serialize, Debug, PartialEq)]
		struct Foo;

		let val = Value::unnamed_composite(vec![]);

		assert_ser_de_eq(Foo, val);
	}

	#[test]
	fn ser_de_named_struct() {
		#[derive(Deserialize, Serialize, Debug, PartialEq)]
		struct Foo {
			a: u8,
			b: bool,
		}

		let val = Value::named_composite(vec![
			("a".into(), Value::u8(123)),
			("b".into(), Value::bool(true)),
		]);

		assert_ser_de_eq(Foo { a: 123, b: true }, val);
	}

	#[test]
	fn ser_de_tuple_struct() {
		#[derive(Deserialize, Serialize, Debug, PartialEq)]
		struct Foo(u8, bool);

		let val = Value::unnamed_composite(vec![Value::u8(123), Value::bool(true)]);

		assert_ser_de_eq(Foo(123, true), val);
	}

	#[test]
	fn ser_de_sequences() {
		assert_ser_de_eq(
			vec![1, 2, 3, 4, 5u8],
			Value::unnamed_composite(vec![
				Value::u8(1),
				Value::u8(2),
				Value::u8(3),
				Value::u8(4),
				Value::u8(5),
			]),
		);

		assert_ser_de_eq(
			[1, 2, 3, 4, 5u8],
			Value::unnamed_composite(vec![
				Value::u8(1),
				Value::u8(2),
				Value::u8(3),
				Value::u8(4),
				Value::u8(5),
			]),
		);

		assert_ser_de_eq(
			(1u8, true, 'a', "hello".to_string()),
			Value::unnamed_composite(vec![
				Value::u8(1),
				Value::bool(true),
				Value::char('a'),
				Value::string("hello"),
			]),
		);
	}

	#[test]
	fn ser_de_variants() {
		#[derive(Debug, PartialEq, Serialize, Deserialize)]
		enum Foo {
			A(bool, u8),
			B,
			C { hello: String, value: i64 },
		}

		assert_ser_de_eq(
			Foo::A(true, 123),
			Value::variant("A", Composite::Unnamed(vec![Value::bool(true), Value::u8(123)])),
		);
		assert_ser_de_eq(Foo::B, Value::variant("B", Composite::Unnamed(vec![])));
		assert_ser_de_eq(
			Foo::C { hello: "World".to_string(), value: 123 },
			Value::variant(
				"C",
				Composite::Named(vec![
					("hello".to_string(), Value::string("World")),
					("value".to_string(), Value::i64(123)),
				]),
			),
		);
	}

	#[test]
	fn ser_de_maps() {
		use std::collections::HashMap;

		let m = {
			let mut m = HashMap::new();
			m.insert("a", 1u8);
			m.insert("b", 2u8);
			m.insert("c", 3u8);
		};
		assert_ser_de(m);

		// chars as keys are fine, too:
		let m = {
			let mut m = HashMap::new();
			m.insert('a', 1u8);
			m.insert('b', 2u8);
			m.insert('c', 3u8);
		};
		assert_ser_de(m);
	}
}