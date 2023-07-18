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

//! This module implements the [`Deserializer`] (note the 'r') trait on our Value enum.
//!
//! A deserializer is a thing which implements methods like `deserialize_i128`. Each of these
//! methods serves as a hint about what the thing calling it (probably a thing implementing
//! [`Deserialize`]) actually wants back. The methods are given a "visitor" which actually accepts
//! values back. We might not give the visitor back the value that it hinted that it wanted, but
//! it's up to the visitor to do its best to accept what it's handed, or reject it if it's simply
//! not going to work out.

use super::bitvec_helpers;
use crate::prelude::*;
use crate::{Composite, Primitive, Value, ValueDef, Variant};
use alloc::{borrow::Cow, fmt::Display};
use serde::{
    de::{self, EnumAccess, IntoDeserializer, VariantAccess},
    forward_to_deserialize_any, ser, Deserialize, Deserializer,
};

/// An opaque error to describe in human terms what went wrong.
/// Many internal serialization/deserialization errors are relayed
/// to this in string form, and so we use basic strings for custom
/// errors as well for simplicity.
#[derive(derive_more::Display, Debug, Clone, PartialEq, Eq)]
pub struct DeserializerError(Cow<'static, str>);

#[cfg(feature = "std")]
impl std::error::Error for DeserializerError {}

impl DeserializerError {
    fn from_string<S: Into<String>>(s: S) -> DeserializerError {
        DeserializerError(Cow::Owned(s.into()))
    }
    fn from_str(s: &'static str) -> DeserializerError {
        DeserializerError(Cow::Borrowed(s))
    }
}

impl de::Error for DeserializerError {
    fn custom<T: Display>(msg: T) -> Self {
        DeserializerError::from_string(msg.to_string())
    }
}
impl ser::Error for DeserializerError {
    fn custom<T: Display>(msg: T) -> Self {
        DeserializerError::from_string(msg.to_string())
    }
}

/// Spit out the simple deserialize methods to avoid loads of repetition.
macro_rules! deserialize_x {
    ($fn_name:ident) => {
        fn $fn_name<V>(self, visitor: V) -> Result<V::Value, Self::Error>
        where
            V: de::Visitor<'de>,
        {
            self.value.$fn_name(visitor)
        }
    };
}

// Our Value type has some context, which we ignore, and some definition, whose deserializer
// impl we forward to.
impl<'de, T> Deserializer<'de> for Value<T> {
    type Error = DeserializerError;

    deserialize_x!(deserialize_any);
    deserialize_x!(deserialize_bool);
    deserialize_x!(deserialize_i8);
    deserialize_x!(deserialize_i16);
    deserialize_x!(deserialize_i32);
    deserialize_x!(deserialize_i64);
    deserialize_x!(deserialize_i128);
    deserialize_x!(deserialize_u8);
    deserialize_x!(deserialize_u16);
    deserialize_x!(deserialize_u32);
    deserialize_x!(deserialize_u64);
    deserialize_x!(deserialize_u128);
    deserialize_x!(deserialize_f32);
    deserialize_x!(deserialize_f64);
    deserialize_x!(deserialize_char);
    deserialize_x!(deserialize_str);
    deserialize_x!(deserialize_string);
    deserialize_x!(deserialize_bytes);
    deserialize_x!(deserialize_byte_buf);
    deserialize_x!(deserialize_option);
    deserialize_x!(deserialize_unit);
    deserialize_x!(deserialize_seq);
    deserialize_x!(deserialize_map);
    deserialize_x!(deserialize_identifier);
    deserialize_x!(deserialize_ignored_any);

    fn deserialize_unit_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.value.deserialize_unit_struct(name, visitor)
    }

    fn deserialize_newtype_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.value.deserialize_newtype_struct(name, visitor)
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.value.deserialize_tuple(len, visitor)
    }

    fn deserialize_tuple_struct<V>(
        self,
        name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.value.deserialize_tuple_struct(name, len, visitor)
    }

    fn deserialize_struct<V>(
        self,
        name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.value.deserialize_struct(name, fields, visitor)
    }

    fn deserialize_enum<V>(
        self,
        name: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.value.deserialize_enum(name, variants, visitor)
    }
}

// Our ValueDef deserializer needs to handle BitSeq itself, but otherwise delegates to
// the inner implementations of things to handle. This macro makes that less repetitive
// to write by only requiring a bitseq impl.
macro_rules! delegate_except_bitseq {
    (
        $name:ident ( $self:ident, $($arg:ident),* ),
            $seq:pat => $expr:expr
    ) => {
        match $self {
            ValueDef::BitSequence($seq) => {
                $expr
            },
            ValueDef::Composite(composite) => {
                composite.$name( $($arg),* )
            },
            ValueDef::Variant(variant) => {
                variant.$name( $($arg),* )
            },
            ValueDef::Primitive(prim) => {
                prim.$name( $($arg),* )
            },
        }
    }
}

macro_rules! delegate_method {
    ($name:ident $ty:ident) => {
        fn $name<V>(self, visitor: V) -> Result<V::Value, Self::Error>
        where
            V: serde::de::Visitor<'de>,
        {
            delegate_except_bitseq! { $name(self, visitor),
                seq => {
                    let map = bitvec_helpers::map_access(seq);
                    visitor.visit_map(map)
                }
            }
        }
    };
}

// The goal here is simply to forward deserialization methods of interest to
// the relevant subtype. The exception is our BitSequence type, which doesn't
// have a sub type to forward to and so is handled here.
impl<'de, T> Deserializer<'de> for ValueDef<T> {
    type Error = DeserializerError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        delegate_except_bitseq! { deserialize_any(self, visitor),
            seq => {
                let map = bitvec_helpers::map_access(seq);
                visitor.visit_map(map)
            }
        }
    }

    delegate_method!(deserialize_u8 u8);
    delegate_method!(deserialize_u16 u16);
    delegate_method!(deserialize_u32 u32);
    delegate_method!(deserialize_u64 u64);
    delegate_method!(deserialize_u128 u128);
    delegate_method!(deserialize_i8 i8);
    delegate_method!(deserialize_i16 i16);
    delegate_method!(deserialize_i32 i32);
    delegate_method!(deserialize_i64 i64);
    delegate_method!(deserialize_i128 i128);
    delegate_method!(deserialize_bool bool);
    delegate_method!(deserialize_f32 f32);
    delegate_method!(deserialize_f64 f64);
    delegate_method!(deserialize_char char);
    delegate_method!(deserialize_str str);
    delegate_method!(deserialize_string String);

    fn deserialize_newtype_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        delegate_except_bitseq! { deserialize_newtype_struct(self, name, visitor),
            _ => {
                Err(DeserializerError::from_str("Cannot deserialize BitSequence into a newtype struct"))
            }
        }
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        delegate_except_bitseq! { deserialize_tuple(self, len, visitor),
            _ => {
                Err(DeserializerError::from_str("Cannot deserialize BitSequence into a tuple"))
            }
        }
    }

    fn deserialize_tuple_struct<V>(
        self,
        name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        delegate_except_bitseq! { deserialize_tuple_struct(self, name, len, visitor),
            _ => {
                Err(DeserializerError::from_str("Cannot deserialize BitSequence into a tuple struct"))
            }
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        delegate_except_bitseq! { deserialize_unit(self, visitor),
            _ => {
                Err(DeserializerError::from_str("Cannot deserialize BitSequence into a ()"))
            }
        }
    }

    fn deserialize_unit_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        delegate_except_bitseq! { deserialize_unit_struct(self, name, visitor),
            _ => {
                Err(DeserializerError::from_string(format!("Cannot deserialize BitSequence into the unit struct {name}")))
            }
        }
    }

    fn deserialize_enum<V>(
        self,
        name: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        delegate_except_bitseq! { deserialize_enum(self, name, variants, visitor),
            _ => {
                Err(DeserializerError::from_string(format!("Cannot deserialize BitSequence into the enum {name}")))
            }
        }
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        delegate_except_bitseq! { deserialize_bytes(self, visitor),
            _ => {
                Err(DeserializerError::from_str("Cannot deserialize BitSequence into raw bytes"))
            }
        }
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        delegate_except_bitseq! { deserialize_byte_buf(self, visitor),
            _ => {
                Err(DeserializerError::from_str("Cannot deserialize BitSequence into raw bytes"))
            }
        }
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        delegate_except_bitseq! { deserialize_seq(self, visitor),
            _ => {
                Err(DeserializerError::from_str("Cannot deserialize BitSequence into a sequence"))
            }
        }
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        delegate_except_bitseq! { deserialize_map(self, visitor),
            _ => {
                Err(DeserializerError::from_str("Cannot deserialize BitSequence into a map"))
            }
        }
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        // Special handling to turn a variant value of "Some" or "None" into an option.
        if let ValueDef::Variant(Variant { name, values: Composite::Unnamed(mut vs) }) = self {
            if name == "Some" && vs.len() == 1 {
                visitor.visit_some(vs.pop().expect("length checked"))
            } else if name == "None" && vs.is_empty() {
                visitor.visit_none()
            } else {
                // Reconstruct the variant and try to deserialize without the option hint:
                ValueDef::Variant(Variant { name, values: Composite::Unnamed(vs) })
                    .deserialize_any(visitor)
            }
        } else {
            // fall back to deserializing based on the value type if it doesn't look like an Option:
            self.deserialize_any(visitor)
        }
    }

    // None of the sub types particularly care about these, so we just allow them to forward to
    // deserialize_any and go from there.
    forward_to_deserialize_any! {
        struct identifier ignored_any
    }
}

impl<'de, T> IntoDeserializer<'de, DeserializerError> for Value<T> {
    type Deserializer = Value<T>;
    fn into_deserializer(self) -> Self::Deserializer {
        self
    }
}

impl<'de, T> Deserializer<'de> for Composite<T> {
    type Error = DeserializerError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Composite::Named(values) => {
                visitor.visit_map(de::value::MapDeserializer::new(values.into_iter()))
            }
            Composite::Unnamed(values) => {
                visitor.visit_seq(de::value::SeqDeserializer::new(values.into_iter()))
            }
        }
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        match self {
            Composite::Named(values) => visitor
                .visit_seq(de::value::SeqDeserializer::new(values.into_iter().map(|(_, v)| v))),
            Composite::Unnamed(values) => {
                visitor.visit_seq(de::value::SeqDeserializer::new(values.into_iter()))
            }
        }
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        match self {
            // A sequence of named values? just ignores the names:
            Composite::Named(values) => {
                if values.len() != len {
                    return Err(DeserializerError::from_string(format!(
                        "Cannot deserialize composite of length {} into tuple of length {}",
                        values.len(),
                        len
                    )));
                }
                visitor
                    .visit_seq(de::value::SeqDeserializer::new(values.into_iter().map(|(_, v)| v)))
            }
            // A sequence of unnamed values is ideal:
            Composite::Unnamed(values) => {
                if values.len() != len {
                    return Err(DeserializerError::from_string(format!(
                        "Cannot deserialize composite of length {} into tuple of length {}",
                        values.len(),
                        len
                    )));
                }
                visitor.visit_seq(de::value::SeqDeserializer::new(values.into_iter()))
            }
        }
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_tuple(len, visitor)
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        // 0 length composite types can be treated as the unit type:
        if self.is_empty() {
            visitor.visit_unit()
        } else {
            Err(DeserializerError::from_str(
                "Cannot deserialize non-empty Composite into a unit value",
            ))
        }
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_unit(visitor)
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_seq(de::value::SeqDeserializer::new(Some(self).into_iter()))
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        let bytes = self.into_values().map(|v| {
            match v.value {
                ValueDef::Primitive(Primitive::U128(n)) => {
                    n.try_into()
                     .map_err(|_| DeserializerError::from_str("Cannot deserialize composite that is not entirely U8's into bytes (number out of range)"))
                },
                _ => {
                    Err(DeserializerError::from_str(
                        "Cannot deserialize composite that is not entirely U8's into bytes (non-numeric values encountered)",
                    ))
                }
            }
        }).collect::<Result<Vec<u8>, _>>()?;
        visitor.visit_byte_buf(bytes)
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_byte_buf(visitor)
    }

    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        option struct map
        enum identifier ignored_any
    }
}

impl<'de, T> IntoDeserializer<'de, DeserializerError> for Composite<T> {
    type Deserializer = Composite<T>;
    fn into_deserializer(self) -> Self::Deserializer {
        self
    }
}

// Because composite types are used to represent variant fields, we allow
// variant accesses to be called on it, which just delegate to methods defined above.
impl<'de, T> VariantAccess<'de> for Composite<T> {
    type Error = DeserializerError;

    fn unit_variant(self) -> Result<(), Self::Error> {
        Deserialize::deserialize(self)
    }

    fn newtype_variant_seed<S>(self, seed: S) -> Result<S::Value, Self::Error>
    where
        S: de::DeserializeSeed<'de>,
    {
        seed.deserialize(self)
    }

    fn tuple_variant<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_tuple(len, visitor)
    }

    fn struct_variant<V>(
        self,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_any(visitor)
    }
}

impl<'de, T> Deserializer<'de> for Variant<T> {
    type Error = DeserializerError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_enum(self)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_enum(self)
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_seq(de::value::SeqDeserializer::new(Some(self).into_iter()))
    }

    // All of the below functions delegate to the Composite deserializing methods using the enum values.

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.values.deserialize_tuple(len, visitor)
    }

    fn deserialize_tuple_struct<V>(
        self,
        name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.values.deserialize_tuple_struct(name, len, visitor)
    }

    fn deserialize_unit_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.values.deserialize_unit_struct(name, visitor)
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.values.deserialize_unit(visitor)
    }

    fn deserialize_struct<V>(
        self,
        name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.values.deserialize_struct(name, fields, visitor)
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.values.deserialize_map(visitor)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.values.deserialize_seq(visitor)
    }

    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option identifier ignored_any
    }
}

impl<'de, T> IntoDeserializer<'de, DeserializerError> for Variant<T> {
    type Deserializer = Variant<T>;
    fn into_deserializer(self) -> Self::Deserializer {
        self
    }
}

// Variant types can be treated as serde enums. Here we just hand back
// the pair of name and values, where values is a composite type that impls
// VariantAccess to actually allow deserializing of those values.
impl<'de, T> EnumAccess<'de> for Variant<T> {
    type Error = DeserializerError;

    type Variant = Composite<T>;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant), Self::Error>
    where
        V: de::DeserializeSeed<'de>,
    {
        let name = self.name.into_deserializer();
        let values = self.values;
        seed.deserialize(name).map(|name| (name, values))
    }
}

macro_rules! deserialize_number {
    ($name:ident $visit_fn:ident) => {
        fn $name<V>(self, visitor: V) -> Result<V::Value, Self::Error>
        where
            V: de::Visitor<'de>,
        {
            match self {
                Primitive::U128(n) => match n.try_into() {
                    Ok(val) => visitor.$visit_fn(val),
                    Err(_) => self.deserialize_any(visitor),
                },
                Primitive::I128(n) => match n.try_into() {
                    Ok(val) => visitor.$visit_fn(val),
                    Err(_) => self.deserialize_any(visitor),
                },
                _ => self.deserialize_any(visitor),
            }
        }
    };
}

impl<'de> Deserializer<'de> for Primitive {
    type Error = DeserializerError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            Primitive::Bool(v) => visitor.visit_bool(v),
            Primitive::Char(v) => visitor.visit_char(v),
            Primitive::String(v) => visitor.visit_string(v),
            Primitive::U128(v) => visitor.visit_u128(v),
            Primitive::U256(v) => visitor.visit_bytes(&v),
            Primitive::I128(v) => visitor.visit_i128(v),
            Primitive::I256(v) => visitor.visit_bytes(&v),
        }
    }

    // if we're asked to deserialize into some numeric type,
    // we do our best to visit that same type with a value, but
    // if we can't coerce our value to it, we fall back to
    // deserialize_any.
    deserialize_number!(deserialize_u8 visit_u8);
    deserialize_number!(deserialize_u16 visit_u16);
    deserialize_number!(deserialize_u32 visit_u32);
    deserialize_number!(deserialize_u64 visit_u64);
    deserialize_number!(deserialize_u128 visit_u128);
    deserialize_number!(deserialize_i8 visit_i8);
    deserialize_number!(deserialize_i16 visit_i16);
    deserialize_number!(deserialize_i32 visit_i32);
    deserialize_number!(deserialize_i64 visit_i64);
    deserialize_number!(deserialize_i128 visit_i128);

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_seq(de::value::SeqDeserializer::new(Some(self).into_iter()))
    }

    forward_to_deserialize_any! {
        bool f32 f64 char str string
        bytes byte_buf option unit unit_struct seq tuple
        tuple_struct map struct enum identifier ignored_any
    }
}

impl<'de> IntoDeserializer<'de, DeserializerError> for Primitive {
    type Deserializer = Primitive;
    fn into_deserializer(self) -> Self::Deserializer {
        self
    }
}

#[cfg(test)]
mod test {
    use crate::value;

    use super::*;
    use serde::Deserialize;

    #[test]
    fn de_into_struct() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct Foo {
            a: u8,
            b: bool,
        }

        let val = ValueDef::Composite(Composite::Named(vec![
            // Order shouldn't matter; match on names:
            ("b".into(), Value::bool(true)),
            ("a".into(), Value::u128(123)),
        ]));

        assert_eq!(Foo::deserialize(val), Ok(Foo { a: 123, b: true }))
    }

    #[test]
    fn de_unwrapped_into_struct() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct Foo {
            a: u8,
            b: bool,
        }

        let val = Composite::Named(vec![
            // Order shouldn't matter; match on names:
            ("b".into(), Value::bool(true)),
            ("a".into(), Value::u128(123)),
        ]);

        assert_eq!(Foo::deserialize(val), Ok(Foo { a: 123, b: true }))
    }

    #[test]
    fn de_into_tuple_struct() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct Foo(u8, bool, String);

        let val = ValueDef::Composite(Composite::Unnamed(vec![
            Value::u128(123),
            Value::bool(true),
            Value::string("hello"),
        ]));

        assert_eq!(Foo::deserialize(val), Ok(Foo(123, true, "hello".into())))
    }

    #[test]
    fn de_unwrapped_into_tuple_struct() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct Foo(u8, bool, String);

        let val =
            Composite::Unnamed(vec![Value::u128(123), Value::bool(true), Value::string("hello")]);

        assert_eq!(Foo::deserialize(val), Ok(Foo(123, true, "hello".into())))
    }

    #[test]
    fn de_into_newtype_struct() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct FooStr(String);
        let val = ValueDef::<()>::Primitive(Primitive::String("hello".into()));
        assert_eq!(FooStr::deserialize(val), Ok(FooStr("hello".into())));
        let val = Value::string("hello");
        assert_eq!(FooStr::deserialize(val), Ok(FooStr("hello".into())));

        #[derive(Deserialize, Debug, PartialEq)]
        struct FooVecU8(Vec<u8>);
        let val = ValueDef::Composite(Composite::Unnamed(vec![
            Value::u128(1),
            Value::u128(2),
            Value::u128(3),
        ]));
        assert_eq!(FooVecU8::deserialize(val), Ok(FooVecU8(vec![1, 2, 3])));

        #[derive(Deserialize, Debug, PartialEq)]
        enum MyEnum {
            Foo(u8, u8, u8),
        }
        #[derive(Deserialize, Debug, PartialEq)]
        struct FooVar(MyEnum);
        let val = ValueDef::Variant(Variant {
            name: "Foo".into(),
            values: Composite::Unnamed(vec![Value::u128(1), Value::u128(2), Value::u128(3)]),
        });
        assert_eq!(FooVar::deserialize(val), Ok(FooVar(MyEnum::Foo(1, 2, 3))));
    }

    #[test]
    fn de_unwrapped_into_newtype_struct() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct FooStr(String);
        let val = Primitive::String("hello".into());
        assert_eq!(FooStr::deserialize(val), Ok(FooStr("hello".into())));

        #[derive(Deserialize, Debug, PartialEq)]
        struct FooVecU8(Vec<u8>);
        let val = Composite::Unnamed(vec![Value::u128(1), Value::u128(2), Value::u128(3)]);
        assert_eq!(FooVecU8::deserialize(val), Ok(FooVecU8(vec![1, 2, 3])));

        #[derive(Deserialize, Debug, PartialEq)]
        enum MyEnum {
            Foo(u8, u8, u8),
        }
        #[derive(Deserialize, Debug, PartialEq)]
        struct FooVar(MyEnum);
        let val = Variant {
            name: "Foo".into(),
            values: Composite::Unnamed(vec![Value::u128(1), Value::u128(2), Value::u128(3)]),
        };
        assert_eq!(FooVar::deserialize(val), Ok(FooVar(MyEnum::Foo(1, 2, 3))));
    }

    #[test]
    fn de_into_vec() {
        let val = ValueDef::Composite(Composite::Unnamed(vec![
            Value::u128(1),
            Value::u128(2),
            Value::u128(3),
        ]));
        assert_eq!(<Vec<u8>>::deserialize(val), Ok(vec![1, 2, 3]));

        let val = ValueDef::Composite(Composite::Unnamed(vec![
            Value::string("a"),
            Value::string("b"),
            Value::string("c"),
        ]));
        assert_eq!(<Vec<String>>::deserialize(val), Ok(vec!["a".into(), "b".into(), "c".into()]));
    }

    #[test]
    fn de_unwrapped_into_vec() {
        let val = Composite::Unnamed(vec![Value::u128(1), Value::u128(2), Value::u128(3)]);
        assert_eq!(<Vec<u8>>::deserialize(val), Ok(vec![1, 2, 3]));

        let val = Composite::Named(vec![
            ("a".into(), Value::u128(1)),
            ("b".into(), Value::u128(2)),
            ("c".into(), Value::u128(3)),
        ]);
        assert_eq!(<Vec<u8>>::deserialize(val), Ok(vec![1, 2, 3]));

        let val =
            Composite::Unnamed(vec![Value::string("a"), Value::string("b"), Value::string("c")]);
        assert_eq!(<Vec<String>>::deserialize(val), Ok(vec!["a".into(), "b".into(), "c".into()]));
    }

    #[test]
    fn de_into_map() {
        use alloc::collections::BTreeMap;

        let val = ValueDef::Composite(Composite::Named(vec![
            ("a".into(), Value::u128(1)),
            ("b".into(), Value::u128(2)),
            ("c".into(), Value::u128(3)),
        ]));
        assert_eq!(
            <BTreeMap<String, u8>>::deserialize(val),
            Ok(vec![("a".into(), 1), ("b".into(), 2), ("c".into(), 3)].into_iter().collect())
        );

        let val = ValueDef::Composite(Composite::Unnamed(vec![
            Value::u128(1),
            Value::u128(2),
            Value::u128(3),
        ]));
        <BTreeMap<String, u8>>::deserialize(val).expect_err("no names; can't be map");
    }

    #[test]
    fn de_into_tuple() {
        let val = ValueDef::Composite(Composite::Unnamed(vec![
            Value::string("hello"),
            Value::bool(true),
        ]));
        assert_eq!(<(String, bool)>::deserialize(val), Ok(("hello".into(), true)));

        // names will just be ignored:
        let val = ValueDef::Composite(Composite::Named(vec![
            ("a".into(), Value::string("hello")),
            ("b".into(), Value::bool(true)),
        ]));
        assert_eq!(<(String, bool)>::deserialize(val), Ok(("hello".into(), true)));

        // Enum variants are allowed! The variant name will be ignored:
        let val = ValueDef::Variant(Variant::unnamed_fields(
            "Foo",
            vec![Value::string("hello"), Value::bool(true)],
        ));
        assert_eq!(<(String, bool)>::deserialize(val), Ok(("hello".into(), true)));

        // Enum variants with names values are allowed! The variant name will be ignored:
        let val = ValueDef::Variant(Variant::named_fields(
            "Foo",
            [("a", Value::string("hello")), ("b", Value::bool(true))],
        ));
        assert_eq!(<(String, bool)>::deserialize(val), Ok(("hello".into(), true)));

        // Wrong number of values should fail:
        let val = ValueDef::Composite(Composite::Unnamed(vec![
            Value::string("hello"),
            Value::bool(true),
            Value::u128(123),
        ]));
        <(String, bool)>::deserialize(val).expect_err("Wrong length, should err");
    }

    #[test]
    fn de_unwrapped_into_tuple() {
        let val = Composite::Unnamed(vec![Value::string("hello"), Value::bool(true)]);
        assert_eq!(<(String, bool)>::deserialize(val), Ok(("hello".into(), true)));

        // names will just be ignored:
        let val = Composite::Named(vec![
            ("a".into(), Value::string("hello")),
            ("b".into(), Value::bool(true)),
        ]);
        assert_eq!(<(String, bool)>::deserialize(val), Ok(("hello".into(), true)));

        // Wrong number of values should fail:
        let val =
            Composite::Unnamed(vec![Value::string("hello"), Value::bool(true), Value::u128(123)]);
        <(String, bool)>::deserialize(val).expect_err("Wrong length, should err");
    }

    #[test]
    fn de_bitvec() {
        use scale_bits::bits;

        // If we deserialize a bitvec value into a value, it should come back out the same.
        let val = Value::bit_sequence(bits![0, 1, 1, 0, 1, 0, 1, 0, 1]);
        assert_eq!(Value::deserialize(val.clone()), Ok(val.clone()));

        // We can serialize a bitvec Value to something like JSON and deserialize it again, too.
        let json_val = serde_json::to_value(&val).expect("can encode to json");
        let new_val: Value<()> =
            serde_json::from_value(json_val).expect("can decode back from json");
        assert_eq!(new_val, val);
    }

    #[test]
    fn de_into_tuple_variant() {
        #[derive(Deserialize, Debug, PartialEq)]
        enum MyEnum {
            Foo(String, bool, u8),
        }

        let val = ValueDef::Variant(Variant {
            name: "Foo".into(),
            values: Composite::Unnamed(vec![
                Value::string("hello"),
                Value::bool(true),
                Value::u128(123),
            ]),
        });
        assert_eq!(MyEnum::deserialize(val), Ok(MyEnum::Foo("hello".into(), true, 123)));

        // it's fine to name the fields; we'll just ignore the names
        let val = ValueDef::Variant(Variant {
            name: "Foo".into(),
            values: Composite::Named(vec![
                ("a".into(), Value::string("hello")),
                ("b".into(), Value::bool(true)),
                ("c".into(), Value::u128(123)),
            ]),
        });
        assert_eq!(MyEnum::deserialize(val), Ok(MyEnum::Foo("hello".into(), true, 123)));
    }

    #[test]
    fn de_unwrapped_into_tuple_variant() {
        #[derive(Deserialize, Debug, PartialEq)]
        enum MyEnum {
            Foo(String, bool, u8),
        }

        let val = Variant {
            name: "Foo".into(),
            values: Composite::Unnamed(vec![
                Value::string("hello"),
                Value::bool(true),
                Value::u128(123),
            ]),
        };
        assert_eq!(MyEnum::deserialize(val), Ok(MyEnum::Foo("hello".into(), true, 123)));

        // it's fine to name the fields; we'll just ignore the names
        let val = Variant {
            name: "Foo".into(),
            values: Composite::Named(vec![
                ("a".into(), Value::string("hello")),
                ("b".into(), Value::bool(true)),
                ("c".into(), Value::u128(123)),
            ]),
        };
        assert_eq!(MyEnum::deserialize(val), Ok(MyEnum::Foo("hello".into(), true, 123)));
    }

    #[test]
    fn de_into_struct_variant() {
        #[derive(Deserialize, Debug, PartialEq)]
        enum MyEnum {
            Foo { hi: String, a: bool, b: u8 },
        }

        // If names given, order doesn't matter:
        let val = ValueDef::Variant(Variant {
            name: "Foo".into(),
            values: Composite::Named(vec![
                // Deliberately out of order: names should ensure alignment:
                ("b".into(), Value::u128(123)),
                ("a".into(), Value::bool(true)),
                ("hi".into(), Value::string("hello")),
            ]),
        });
        assert_eq!(
            MyEnum::deserialize(val),
            Ok(MyEnum::Foo { hi: "hello".into(), a: true, b: 123 })
        );

        // No names needed if order is OK:
        let val = ValueDef::Variant(Variant {
            name: "Foo".into(),
            values: Composite::Unnamed(vec![
                Value::string("hello"),
                Value::bool(true),
                Value::u128(123),
            ]),
        });
        assert_eq!(
            MyEnum::deserialize(val),
            Ok(MyEnum::Foo { hi: "hello".into(), a: true, b: 123 })
        );

        // Wrong order won't work if no names:
        let val = ValueDef::Variant(Variant {
            name: "Foo".into(),
            values: Composite::Unnamed(vec![
                Value::bool(true),
                Value::u128(123),
                Value::string("hello"),
            ]),
        });
        MyEnum::deserialize(val).expect_err("Wrong order shouldn't work");

        // Wrong names won't work:
        let val = ValueDef::Variant(Variant {
            name: "Foo".into(),
            values: Composite::Named(vec![
                ("b".into(), Value::u128(123)),
                // Whoops; wrong name:
                ("c".into(), Value::bool(true)),
                ("hi".into(), Value::string("hello")),
            ]),
        });
        MyEnum::deserialize(val).expect_err("Wrong names shouldn't work");

        // Too many names is OK; we can ignore fields we don't care about:
        let val = ValueDef::Variant(Variant {
            name: "Foo".into(),
            values: Composite::Named(vec![
                ("foo".into(), Value::u128(40)),
                ("b".into(), Value::u128(123)),
                ("a".into(), Value::bool(true)),
                ("bar".into(), Value::bool(false)),
                ("hi".into(), Value::string("hello")),
            ]),
        });
        assert_eq!(
            MyEnum::deserialize(val),
            Ok(MyEnum::Foo { hi: "hello".into(), a: true, b: 123 })
        );
    }

    #[test]
    fn de_into_unit_variants() {
        let val = value!(Foo {});

        let unwrapped_val = Variant::<()> { name: "Foo".into(), values: Composite::Named(vec![]) };

        #[derive(Deserialize, Debug, PartialEq)]
        enum MyEnum {
            Foo,
        }
        assert_eq!(MyEnum::deserialize(val.clone()), Ok(MyEnum::Foo));
        assert_eq!(MyEnum::deserialize(unwrapped_val.clone()), Ok(MyEnum::Foo));

        #[derive(Deserialize, Debug, PartialEq)]
        enum MyEnum2 {
            Foo(),
        }
        assert_eq!(MyEnum2::deserialize(val.clone()), Ok(MyEnum2::Foo()));
        assert_eq!(MyEnum2::deserialize(unwrapped_val.clone()), Ok(MyEnum2::Foo()));

        #[derive(Deserialize, Debug, PartialEq)]
        enum MyEnum3 {
            Foo {},
        }
        assert_eq!(MyEnum3::deserialize(val), Ok(MyEnum3::Foo {}));
        assert_eq!(MyEnum3::deserialize(unwrapped_val), Ok(MyEnum3::Foo {}));
    }
}
