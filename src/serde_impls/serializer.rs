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

//! This [`Serializer`] impl allows types implementing `Serialize` to be converted
//! into [`Value`]s.

use crate::prelude::*;
use crate::{Composite, Primitive, Value, ValueDef};
use serde::{
    ser::{
        SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant, SerializeTuple,
        SerializeTupleStruct, SerializeTupleVariant,
    },
    Serializer,
};

/// This struct implements [`Serializer`] and knows how to map from the serde data model to a [`Value`] type.
pub struct ValueSerializer;

/// An error that can occur when attempting to serialize a type into a [`Value`].
#[derive(derive_more::Display, Debug, Clone, PartialEq, Eq)]
pub enum SerializerError {
    /// Some custom error string.
    Custom(String),
    /// SCALE does not support floating point values, and so we'll hit this error if we try to
    /// encode any floats.
    #[display(
        fmt = "Floats do not have a SCALE compatible representation, and so cannot be serialized to Values"
    )]
    CannotSerializeFloats,
    /// SCALE encoding is only designed to map from statically known structs to bytes. We use field names
    /// to figure out this mapping between named composite types and structs, so we don't support encoding
    /// maps with non-string keys into [`Value`]s.
    #[display(fmt = "Map keys must be strings or string-like")]
    MapKeyMustBeStringlike,
}

#[cfg(feature = "std")]
impl std::error::Error for SerializerError {}

impl serde::ser::Error for SerializerError {
    fn custom<T>(msg: T) -> Self
    where
        T: core::fmt::Display,
    {
        SerializerError::Custom(msg.to_string())
    }
}

macro_rules! serialize_prim {
    ($name:ident => $method:ident($ty:ident)) => {
        fn $name(self, v: $ty) -> Result<Self::Ok, Self::Error> {
            Ok(Value::$method(v.into()))
        }
    };
}

impl Serializer for ValueSerializer {
    type Ok = Value<()>;
    type Error = SerializerError;

    type SerializeSeq = UnnamedCompositeSerializer;
    type SerializeTuple = UnnamedCompositeSerializer;
    type SerializeTupleStruct = UnnamedCompositeSerializer;
    type SerializeTupleVariant = UnnamedCompositeSerializer;
    type SerializeMap = NamedCompositeSerializer;
    type SerializeStruct = NamedCompositeSerializer;
    type SerializeStructVariant = NamedCompositeSerializer;

    serialize_prim!(serialize_bool => bool(bool));
    serialize_prim!(serialize_i8 => i128(i8));
    serialize_prim!(serialize_i16 => i128(i16));
    serialize_prim!(serialize_i32 => i128(i32));
    serialize_prim!(serialize_i64 => i128(i64));
    serialize_prim!(serialize_i128 => i128(i128));
    serialize_prim!(serialize_u8 => u128(u8));
    serialize_prim!(serialize_u16 => u128(u16));
    serialize_prim!(serialize_u32 => u128(u32));
    serialize_prim!(serialize_u64 => u128(u64));
    serialize_prim!(serialize_u128 => u128(u128));
    serialize_prim!(serialize_char => char(char));

    fn serialize_f32(self, _v: f32) -> Result<Self::Ok, Self::Error> {
        Err(SerializerError::CannotSerializeFloats)
    }
    fn serialize_f64(self, _v: f64) -> Result<Self::Ok, Self::Error> {
        Err(SerializerError::CannotSerializeFloats)
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        Ok(Value::string(v.to_string()))
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        let bytes = v.iter().map(|&b| Value::u128(b as u128));
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

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), SerializerError>
    where
        T: serde::Serialize,
    {
        let inner = value.serialize(ValueSerializer)?;
        self.values.push(inner);
        Ok(())
    }

    fn end(self) -> Result<Value<()>, SerializerError> {
        match self.variant_name {
            Some(name) => Ok(Value::variant(name, Composite::Unnamed(self.values))),
            None => Ok(Value::unnamed_composite(self.values)),
        }
    }
}

impl SerializeSeq for UnnamedCompositeSerializer {
    type Ok = Value<()>;
    type Error = SerializerError;

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
    type Error = SerializerError;

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
    type Error = SerializerError;

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
    type Error = SerializerError;

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

    fn serialize_field<T: ?Sized>(&mut self, key: &str, value: &T) -> Result<(), SerializerError>
    where
        T: serde::Serialize,
    {
        let key = key.to_string();
        let inner = value.serialize(ValueSerializer)?;
        self.values.push((key, inner));
        Ok(())
    }

    fn end(self) -> Result<Value<()>, SerializerError> {
        match self.variant_name {
            Some(name) => Ok(Value::variant(name, Composite::Named(self.values))),
            None => Ok(Value::named_composite(self.values)),
        }
    }
}

impl SerializeMap for NamedCompositeSerializer {
    type Ok = Value<()>;
    type Error = SerializerError;

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
            _ => return Err(SerializerError::MapKeyMustBeStringlike),
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
    type Error = SerializerError;

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
    type Error = SerializerError;

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
    use super::*;
    use crate::{value, Value};
    use core::fmt::Debug;
    use serde::{Deserialize, Serialize};

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
        assert_ser_de_eq(123u8, Value::u128(123));
        assert_ser_de_eq(123u16, Value::u128(123));
        assert_ser_de_eq(123u32, Value::u128(123));
        assert_ser_de_eq(123u64, Value::u128(123));
        assert_ser_de_eq(123u128, Value::u128(123));

        assert_ser_de_eq(123i8, Value::i128(123));
        assert_ser_de_eq(123i16, Value::i128(123));
        assert_ser_de_eq(123i32, Value::i128(123));
        assert_ser_de_eq(123i64, Value::i128(123));
        assert_ser_de_eq(123i128, Value::i128(123));

        assert_ser_de_eq(true, Value::bool(true));
        assert_ser_de_eq(false, Value::bool(false));

        assert_ser_de_eq("hello".to_string(), Value::string("hello"));
        assert_ser_de_eq('a', Value::char('a'));
    }

    #[test]
    fn ser_de_optionals() {
        assert_ser_de_eq(Some(123u8), value!(Some(123u8)));
        assert_ser_de_eq(None as Option<u8>, value!(None()));
    }

    #[test]
    fn ser_de_unit_struct() {
        #[derive(Deserialize, Serialize, Debug, PartialEq)]
        struct Foo;

        assert_ser_de_eq(Foo, value!(()));
    }

    #[test]
    fn ser_de_named_struct() {
        #[derive(Deserialize, Serialize, Debug, PartialEq)]
        struct Foo {
            a: u8,
            b: bool,
        }

        let val = value!({a: 123u8, b: true});
        assert_ser_de_eq(Foo { a: 123, b: true }, val);
    }

    #[test]
    fn ser_de_tuple_struct() {
        #[derive(Deserialize, Serialize, Debug, PartialEq)]
        struct Foo(u8, bool);

        let val = value!((123u8, true));
        assert_ser_de_eq(Foo(123, true), val);
    }

    #[test]
    fn ser_de_sequences() {
        assert_ser_de_eq(vec![1, 2, 3, 4, 5u8], value!((1u8, 2u8, 3u8, 4u8, 5u8)));
        assert_ser_de_eq([1, 2, 3, 4, 5u8], value!((1u8, 2u8, 3u8, 4u8, 5u8)));

        assert_ser_de_eq((1u8, true, 'a', "hello".to_string()), value!((1u8, true, 'a', "hello")));
    }

    #[test]
    fn ser_de_variants() {
        #[derive(Debug, PartialEq, Serialize, Deserialize)]
        enum Foo {
            A(bool, u8),
            B,
            C { hello: String, value: i64 },
        }

        assert_ser_de_eq(Foo::A(true, 123), value!(A(true, 123u8)));
        assert_ser_de_eq(Foo::B, value!(B()));
        assert_ser_de_eq(
            Foo::C { hello: "World".to_string(), value: 123 },
            value!(C { hello: "World", value: 123 }),
        );
    }

    #[test]
    fn ser_de_maps() {
        use alloc::collections::BTreeMap;

        let m = {
            let mut m = BTreeMap::new();
            m.insert("a".to_string(), 1u8);
            m.insert("b".to_string(), 2u8);
            m.insert("c".to_string(), 3u8);
            m
        };
        assert_ser_de(m);

        // chars as keys are fine, too:
        let m = {
            let mut m = BTreeMap::new();
            m.insert('a', 1u8);
            m.insert('b', 2u8);
            m.insert('c', 3u8);
            m
        };
        assert_ser_de(m);
    }
}
