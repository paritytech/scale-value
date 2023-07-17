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

//! This [`Serialize`] impl allows [`Value`]s to be serialized to some format
//! (eg JSON); we do our best to hand the [`Serializer`] values which most
//! accurately represent what we've stored, but there is always some amount of
//! converstion between our [`Value`] type and the types supported by the
//! serde data model that we're serializing things into.

use super::bitvec_helpers;
use crate::prelude::*;
use crate::{Composite, Primitive, Value, ValueDef, Variant};
use serde::{
    ser::{SerializeMap, SerializeSeq},
    Serialize, Serializer,
};

impl<T> Serialize for Value<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.value.serialize(serializer)
    }
}

impl<T> Serialize for ValueDef<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            ValueDef::Composite(val) => val.serialize(serializer),
            ValueDef::Variant(val) => val.serialize(serializer),
            ValueDef::Primitive(val) => val.serialize(serializer),
            ValueDef::BitSequence(val) => bitvec_helpers::serialize_bitvec(val, serializer),
        }
    }
}

impl<T> Serialize for Composite<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Composite::Named(vals) => {
                let mut map = serializer.serialize_map(Some(vals.len()))?;
                for (key, val) in vals {
                    map.serialize_entry(key, val)?;
                }
                map.end()
            }
            Composite::Unnamed(vals) => {
                let mut seq = serializer.serialize_seq(Some(vals.len()))?;
                for val in vals {
                    seq.serialize_element(val)?;
                }
                seq.end()
            }
        }
    }
}

macro_rules! serialize_as_first_ok_type {
    ($serializer:ident $val:ident; $first:ident $($rest:ident)*) => {{
        let n: Result<$first,_> = $val.try_into();
        match n {
            Ok(n) => n.serialize($serializer),
            Err(_) => serialize_as_first_ok_type!($serializer $val; $($rest)*)
        }
    }};
    ($serializer:ident $val:ident;) => {{
        $val.serialize($serializer)
    }};
}

impl Serialize for Primitive {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Delegate to the serialization strategy used by the primitive types.
        match self {
            Primitive::Bool(v) => v.serialize(serializer),
            Primitive::Char(v) => v.serialize(serializer),
            Primitive::String(v) => v.serialize(serializer),
            Primitive::U128(v) => {
                // Serialize into the smallest type that fits, since formats like
                // JSON don't like u128's by default.
                let v = *v;
                serialize_as_first_ok_type!(serializer v; u8 u16 u32 u64 u128)
            }
            Primitive::U256(v) => v.serialize(serializer),
            Primitive::I128(v) => {
                // Serialize into the smallest type that fits, since formats like
                // JSON don't like i128's by default.
                let v = *v;
                serialize_as_first_ok_type!(serializer v; i8 i16 i32 i64 i128)
            }
            Primitive::I256(v) => v.serialize(serializer),
        }
    }
}

impl<T> Serialize for Variant<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // We can't use the enum serializing in the serde data model because that requires static
        // strs and enum indexes, which we don't have (since this is a runtime value), so we serialize
        // as a map with a type and a value, and make sure that we allow this format when attempting to
        // deserialize into a `Variant` type for a bit of symmetry (although note that if you try to deserialize
        // this into a `Value` type it'll have no choice but to deserialize straight into a `Composite::Named` map).
        let mut map = serializer.serialize_map(Some(2))?;
        map.serialize_entry("name", &self.name)?;
        map.serialize_entry("values", &self.values)?;
        map.end()
    }
}

#[cfg(test)]
mod test {
    use crate::value;

    use super::*;
    use serde_json::json;

    fn assert_value(value: Value<()>, expected: serde_json::Value) {
        let val = serde_json::to_value(value).expect("can serialize to serde_json::Value");
        assert_eq!(val, expected);
    }

    #[test]
    fn serialize_primitives() {
        // a subset of the primitives to sanity check that they are unwrapped:
        assert_value(Value::u128(1), json!(1));
        assert_value(Value::bool(true), json!(true));
        assert_value(Value::bool(false), json!(false));
    }

    #[test]
    fn serialize_composites() {
        assert_value(
            value!({
                a: true,
                b: "hello",
                c: 'c'
            }),
            json!({
                "a": true,
                "b": "hello",
                "c": 'c'
            }),
        );
        assert_value(value!((true, "hello", 'c')), json!([true, "hello", 'c']))
    }

    #[test]
    fn serialize_variants() {
        assert_value(
            value!(Foo { a: true, b: "hello", c: 'c' }),
            json!({
                "name": "Foo",
                "values": {
                    "a": true,
                    "b": "hello",
                    "c": 'c'
                }
            }),
        );
        assert_value(
            value!(Bar(true, "hello", 'c')),
            json!({
                "name": "Bar",
                "values": [
                    true,
                    "hello",
                    'c'
                ]
            }),
        )
    }

    #[test]
    fn serialize_bitsequences() {
        use scale_bits::bits;

        assert_value(
            Value::bit_sequence(bits![]),
            json!({
                "__bitvec__values__": []
            }),
        );
        assert_value(
            Value::bit_sequence(bits![0, 1, 1, 0, 1]),
            json!({
                "__bitvec__values__": [false, true, true, false, true]
            }),
        );
    }
}
