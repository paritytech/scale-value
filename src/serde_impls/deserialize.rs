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

//! This module implements the [`Deserialize`] (no R!) trait on our [`Value`] enum.
//!
//! The [`Deserialize`] trait is responsible for telling some deserializer (note the 'r')
//! what sorts of values we need back in order to construst an instance of our [`Value`] type.
//! Since the [`Value`] type accepts a range of possible values, it leans heavily on the
//! `deserialize_any` method; this means that the deserializer needs to know what structure it's
//! working with in order to be able to provide back the right values; we can't tell it what structure
//! we expect.
//!
//! One thing we aim for is to be able to losslessly deserialize a [`Value`] into a
//! [`Value`]. This would allow for partial type deserialization, for instance we might want to turn
//! only part of our input into a struct, say, and leave the rest as [`Value`] types until we know what
//! to do with them.

use crate::prelude::*;
use super::bitvec_helpers;
use crate::{Composite, Primitive, Value, ValueDef, Variant};
use serde::{
    self,
    de::{Error, Visitor},
    Deserialize, Deserializer,
};
use core::convert::TryInto;

impl<'de> Deserialize<'de> for Value<()> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let value = deserializer.deserialize_any(ValueDefVisitor)?;
        Ok(Value { value, context: () })
    }
}

impl<'de> Deserialize<'de> for ValueDef<()> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(ValueDefVisitor)
    }
}

impl<'de> Deserialize<'de> for Primitive {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(PrimitiveVisitor)
    }
}

impl<'de> Deserialize<'de> for Composite<()> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(CompositeVisitor)
    }
}

impl<'de> Deserialize<'de> for Variant<()> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(VariantVisitor)
    }
}

struct PrimitiveVisitor;

macro_rules! visit_prim {
    ($name:ident $ty:ident $variant:ident) => {
        fn $name<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            Ok(Primitive::$variant(v.into()))
        }
    };
}

impl<'de> Visitor<'de> for PrimitiveVisitor {
    type Value = Primitive;

    fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
        formatter.write_str("a type that can be decoded into a Primitive value")
    }

    visit_prim!(visit_bool bool Bool);
    visit_prim!(visit_i8 i8 I128);
    visit_prim!(visit_i16 i16 I128);
    visit_prim!(visit_i32 i32 I128);
    visit_prim!(visit_i64 i64 I128);
    visit_prim!(visit_i128 i128 I128);
    visit_prim!(visit_u8 u8 U128);
    visit_prim!(visit_u16 u16 U128);
    visit_prim!(visit_u32 u32 U128);
    visit_prim!(visit_u64 u64 U128);
    visit_prim!(visit_u128 u128 U128);
    visit_prim!(visit_char char Char);

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Primitive::String(v.into()))
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Primitive::String(v))
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        let val = v
            .try_into()
            .map_err(|_| serde::de::Error::invalid_type(serde::de::Unexpected::Bytes(v), &self))?;
        Ok(Primitive::U256(val))
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let mut vals = Vec::new();
        while let Some(el) = seq.next_element()? {
            vals.push(el)
        }
        let len = vals.len();
        let arr = vals
            .try_into()
            .map_err(|_| serde::de::Error::invalid_length(len, &"exactly 32 bytes"))?;
        Ok(Primitive::U256(arr))
    }
}

struct CompositeVisitor;

impl<'de> Visitor<'de> for CompositeVisitor {
    type Value = Composite<()>;

    fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
        formatter.write_str("a type that can be decoded into a Composite value")
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        let byte_values = v.iter().map(|&b| Value::u128(b as u128)).collect();
        Ok(Composite::Unnamed(byte_values))
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Composite::Unnamed(Vec::new()))
    }

    fn visit_newtype_struct<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        Composite::deserialize(deserializer)
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let mut values = Vec::with_capacity(seq.size_hint().unwrap_or(0));
        while let Some(value) = seq.next_element()? {
            values.push(value);
        }
        Ok(Composite::Unnamed(values))
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        let mut values = Vec::with_capacity(map.size_hint().unwrap_or(0));
        while let Some(key_val) = map.next_entry()? {
            values.push(key_val);
        }
        Ok(Composite::Named(values))
    }
}

struct VariantVisitor;

impl<'de> Visitor<'de> for VariantVisitor {
    type Value = Variant<()>;

    fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
        formatter.write_str("a type that can be decoded into an enum Variant")
    }

    fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::EnumAccess<'de>,
    {
        data.variant().and_then(|(name, variant_access)| {
            use serde::de::VariantAccess;
            // We have to ask for a particular enum type, but we don't know what type
            // of enum to expect (we support anything!). So, we just call the visitor method
            // that doesn't require any extra fields, and we know that this will just give back
            // whatever it can based on our impl (who knows about other impls though).
            let values = variant_access.newtype_variant()?;
            Ok(Variant { name, values })
        })
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        // Wrap "Some"-like things in a Some variant.
        // This aligns with how we serialize these back to optionals.
        let inner = Value::deserialize(deserializer)?;
        Ok(Variant { name: "Some".to_string(), values: Composite::Unnamed(vec![inner]) })
    }

    fn visit_none<E>(self) -> Result<Self::Value, E>
    where
        E: Error,
    {
        // If the thing is "none", wrap it in a None variant.
        // This aligns with how we serialize these back to optionals.
        Ok(Variant { name: "None".to_string(), values: Composite::Unnamed(Vec::new()) })
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        // We support deserializing from a map that looks like
        // { name: "VariantName", values: [1,2,3] } into Variant + Composite::Unnamed, or
        // { name: "VariantName", values: { "a": 1, "b": 2 }} into Variant + Composite::Named
        // to line up with our Serialize impl for the Value types.
        let mut name = None;
        let mut values = None;

        while let Some(k) = map.next_key::<String>()? {
            match &*k {
                "name" => {
                    name = Some(map.next_value()?);
                }
                "values" => {
                    values = Some(map.next_value()?);
                }
                other => return Err(A::Error::unknown_field(other, &["name", "values"])),
            }
        }

        if let (Some(name), Some(values)) = (name, values) {
            Ok(Variant { name, values })
        } else {
            Err(A::Error::custom(
                "map must contain 'name' and 'values' to deserialize to a Variant",
            ))
        }
    }
}

struct ValueDefVisitor;

// It gets repetitive writing out the visitor impls to delegate to the Value subtypes;
// this helper makes that a little easier:
macro_rules! delegate_visitor_fn {
    (
        $visitor:ident $mapping:path,
        $( $name:ident($($ty:ty)?) )+
    ) => {
        $(
            fn $name<E>(self, $(v: $ty)?) -> Result<Self::Value, E>
            where E: serde::de::Error {
                $visitor.$name($(v as $ty)?).map($mapping)
            }
        )+
    }
}

impl<'de> Visitor<'de> for ValueDefVisitor {
    type Value = ValueDef<()>;

    fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
        formatter.write_str("a type that can be decoded into a Value")
    }

    delegate_visitor_fn!(
        PrimitiveVisitor ValueDef::Primitive,
        visit_bool(bool)
        visit_i8(i8)
        visit_i16(i16)
        visit_i32(i32)
        visit_i64(i64)
        visit_i128(i128)
        visit_u8(u8)
        visit_u16(u16)
        visit_u32(u32)
        visit_u64(u64)
        visit_u128(u128)
        visit_char(char)
        visit_str(&str)
        visit_string(String)
    );

    delegate_visitor_fn!(
        CompositeVisitor ValueDef::Composite,
        visit_unit()
        visit_bytes(&[u8])
    );

    fn visit_none<E>(self) -> Result<Self::Value, E>
    where
        E: Error,
    {
        VariantVisitor.visit_none().map(ValueDef::Variant)
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        VariantVisitor.visit_some(deserializer).map(ValueDef::Variant)
    }

    fn visit_newtype_struct<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        ValueDef::deserialize(deserializer)
    }

    fn visit_seq<A>(self, seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        CompositeVisitor.visit_seq(seq).map(ValueDef::Composite)
    }

    fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        // Return a bitvec or a composite type depending on the map values.
        bitvec_helpers::MapOrBitSeqVisitor.visit_map(map)
    }

    fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::EnumAccess<'de>,
    {
        VariantVisitor.visit_enum(data).map(ValueDef::Variant)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use serde_json::json;

    use crate::value;

    use super::super::DeserializerError;

    /// Does a value deserialize to itself?
    fn assert_value_isomorphic<
        'de,
        V: Deserializer<'de> + Deserialize<'de> + PartialEq + core::fmt::Debug + Clone,
    >(
        val: V,
    ) {
        assert_value_to_value(val.clone(), val)
    }

    /// Does a value `a` deserialize to the expected value `b`?
    fn assert_value_to_value<'de, V1, V2>(a: V1, b: V2)
    where
        V1: Deserializer<'de>,
        V2: Deserialize<'de> + PartialEq + core::fmt::Debug + Clone,
    {
        let new_val = V2::deserialize(a).expect("Can deserialize");
        assert_eq!(b, new_val);
    }

    #[test]
    fn deserialize_primitives_isomorphic() {
        assert_value_isomorphic(Value::u128(123));
        assert_value_isomorphic(Value::i128(123));
        assert_value_isomorphic(Value::bool(true));
        assert_value_isomorphic(Value::char('a'));
        assert_value_isomorphic(Value::string("Hello!"));

        // Alas, I256 and U256 are both a sequence of bytes, which could equally be represented
        // by a composite sequence (as other sequences-of-things are). We could have a special case where
        // precisely 32 u8's is deserialized to one of U256 or I256, but for now we use our more general
        // composite type as the sequence catch-all:
        assert_value_to_value(
            ValueDef::<()>::Primitive(Primitive::I256([1; 32])),
            Value::unnamed_composite(vec![1u8; 32].into_iter().map(|b| Value::u128(b.into()))),
        );
        assert_value_to_value(
            ValueDef::<()>::Primitive(Primitive::U256([1; 32])),
            Value::unnamed_composite(vec![1u8; 32].into_iter().map(|b| Value::u128(b.into()))),
        );

        // .. that said; if you want a primitive value back, you can use that type directly to get it
        // (as long as we are given exactly 32 bytes):

        assert_value_to_value(
            ValueDef::<()>::Primitive(Primitive::I256([1; 32])),
            Primitive::U256([1; 32]),
        );
        assert_value_to_value(
            ValueDef::<()>::Primitive(Primitive::U256([1; 32])),
            Primitive::U256([1; 32]),
        );

        // Unwrapped versions also work:

        assert_value_isomorphic(Primitive::U128(123));
        assert_value_isomorphic(Primitive::U256([1; 32]));
        assert_value_isomorphic(Primitive::I128(123));
        assert_value_isomorphic(Primitive::Bool(true));
        assert_value_isomorphic(Primitive::Char('a'));
        assert_value_isomorphic(Primitive::String("Hello!".into()));
        assert_value_to_value(Primitive::I256([1; 32]), Primitive::U256([1; 32]));

        // We can also go from wrapped to unwrapped:

        assert_value_to_value(Value::u128(123), Primitive::u128(123));
        assert_value_to_value(Value::i128(123), Primitive::i128(123));

        // Or vice versa:

        assert_value_to_value(Primitive::u128(123), Value::u128(123));
        assert_value_to_value(Primitive::i128(123), Value::i128(123));
    }

    #[test]
    fn deserialize_composites_isomorphic() {
        assert_value_isomorphic(value!((123u8, true)));
        assert_value_isomorphic(value!({}));
        assert_value_isomorphic(value!({a: 123u8, b: true}));
        assert_value_isomorphic(value!({a: 123u8, b: { c: 123u8, d: "hello"}}));

        // unwrapped:

        assert_value_isomorphic(Composite::unnamed(vec![Value::u128(123), Value::bool(true)]));
        assert_value_isomorphic(Composite::unnamed(vec![]));
        assert_value_isomorphic(Composite::named(vec![
            ("a", Value::u128(123)),
            ("b", Value::bool(true)),
        ]));
        assert_value_isomorphic(Composite::named(vec![
            ("a", Value::u128(123)),
            ("b", value!({ c: 123u8, d: "hello"})),
        ]));
    }

    #[test]
    fn deserialize_variants_isomorphic() {
        assert_value_isomorphic(ValueDef::Variant(Variant::unnamed_fields(
            "Foo",
            [Value::u128(123), Value::bool(true)],
        )));
        assert_value_isomorphic(ValueDef::Variant(Variant::unnamed_fields("Foo", [])));
        assert_value_isomorphic(ValueDef::Variant(Variant::named_fields(
            "Foo",
            [("a", Value::u128(123)), ("b", Value::bool(true))],
        )));

        // unwrapped work as well:

        assert_value_isomorphic(Variant::unnamed_fields(
            "Foo",
            [Value::u128(123), Value::bool(true)],
        ));
        assert_value_isomorphic(Variant::unnamed_fields("Foo", vec![]));
        assert_value_isomorphic(Variant::named_fields(
            "Foo",
            [("a", Value::u128(123)), ("b", Value::bool(true))],
        ));
    }

    #[test]
    fn deserialize_bitsequences_isomorphic() {
        use scale_bits::bits;
        assert_value_isomorphic(ValueDef::BitSequence(bits![]));
        assert_value_isomorphic(ValueDef::BitSequence(bits![0]));
        assert_value_isomorphic(ValueDef::BitSequence(bits![0, 1, 1, 0, 1, 0, 1, 1, 1]));
    }

    #[test]
    fn deserialize_bitsequence_from_json() {
        use scale_bits::bits;

        let bits_json = json!({
            "__bitvec__values__": [true, false, true, true, false]
        });

        let val: Value = serde_json::from_value(bits_json).unwrap();
        assert_eq!(val.value, ValueDef::BitSequence(bits![true, false, true, true, false]));
    }

    #[test]
    fn sequence_to_value() {
        use serde::de::{value::SeqDeserializer, IntoDeserializer};

        let de: SeqDeserializer<_, DeserializerError> = vec![1u8, 2, 3, 4].into_deserializer();

        assert_value_to_value(de.clone(), value!((1u8, 2u8, 3u8, 4u8)));
        assert_value_to_value(
            de,
            Composite::Unnamed(vec![
                Value::u128(1),
                Value::u128(2),
                Value::u128(3),
                Value::u128(4),
            ]),
        );
    }

    #[test]
    fn sequence_to_primitive() {
        use serde::de::{value::SeqDeserializer, IntoDeserializer};

        let de: SeqDeserializer<_, DeserializerError> = vec![1u8; 32].into_deserializer();

        assert_value_to_value(de, Primitive::U256([1; 32]));
    }

    #[test]
    fn map_to_value() {
        use serde::de::{value::MapDeserializer, IntoDeserializer};
        use ::alloc::collections::BTreeMap;

        let map = {
            let mut map = BTreeMap::<&'static str, i32>::new();
            map.insert("a", 1i32);
            map.insert("b", 2i32);
            map.insert("c", 3i32);
            map
        };

        let de: MapDeserializer<_, DeserializerError> = map.into_deserializer();

        let value = ValueDef::deserialize(de).expect("should deserialize OK");
        if let ValueDef::Composite(Composite::Named(vals)) = value {
            // These could come back in any order so we need to search for them:
            assert!(vals.contains(&("a".into(), Value::i128(1))));
            assert!(vals.contains(&("b".into(), Value::i128(2))));
            assert!(vals.contains(&("c".into(), Value::i128(3))));
        } else {
            panic!("Map should deserialize into Composite::Named value but we have {value:?}");
        }
    }

    #[test]
    fn partially_deserialize_value() {
        let value = Value::named_composite(vec![
            ("a", Value::u128(123)),
            ("b", value!({c: 123u8, d: "hello", e: {}})),
        ]);

        #[derive(Deserialize, Debug, PartialEq)]
        struct Partial {
            a: Value<()>,
            b: PartialB,
        }

        #[derive(Deserialize, Debug, PartialEq)]
        struct PartialB {
            c: u128,
            d: String,
            e: Value<()>,
        }

        let partial = Partial::deserialize(value).expect("should work");

        assert_eq!(
            partial,
            Partial {
                a: Value::u128(123),
                b: PartialB { c: 123, d: "hello".into(), e: value!({}) }
            }
        )
    }

    #[test]
    fn deserialize_well_formed_map_to_unnamed_variant() {
        let v: Variant<()> = Variant::deserialize(serde_json::json!({
            "name": "Hello",
            "values": [1, 2, true]
        }))
        .unwrap();

        assert_eq!(v.name, "Hello".to_string());
        assert_eq!(
            v.values,
            Composite::Unnamed(vec![
                // All JSON numbers deserialize to U64 or I64 or F64 as necessary:
                Value::u128(1),
                Value::u128(2),
                Value::bool(true),
            ])
        )
    }

    #[test]
    fn deserialize_well_formed_map_to_named_variant() {
        let v: Variant<()> = Variant::deserialize(serde_json::json!({
            "name": "Hello",
            "values": { "a": 1, "b": 2, "c": true }
        }))
        .unwrap();

        assert_eq!(v.name, "Hello".to_string());
        assert_eq!(
            v.values,
            Composite::Named(vec![
                // All JSON numbers deserialize to U64 or I64 or F64 as necessary:
                ("a".into(), Value::u128(1)),
                ("b".into(), Value::u128(2)),
                ("c".into(), Value::bool(true)),
            ])
        )
    }

    #[test]
    fn cannot_deserialize_malformed_map_to_variant() {
        assert!(matches!(
            Variant::deserialize(serde_json::json!({
                "names": "Hello", // "names", not "name".
                "values": [1, 2, true]
            })),
            Err(..)
        ));
        assert!(matches!(
            Variant::deserialize(serde_json::json!({
                "name": "Hello",
                "values": [1, 2, true],
                "other": true // unexpected third prop.
            })),
            Err(..)
        ));
        assert!(matches!(
            Variant::deserialize(serde_json::json!({
                "names": "Hello",
                "values": 1 // incorrect type of values
            })),
            Err(..)
        ));
    }
}
