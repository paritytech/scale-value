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

//! This module implements the [`serde::Deserializer`] (note the 'r') trait on our Value enum.
//!
//! A deserializer is a thing which implements methods like `deserialize_i128`. Each of these
//! methods serves as a hint about what the thing calling it (probably a thing implementing
//! [`serde::Deserialize`]) actually wants back. The methods are given a "visitor" which actually accepts
//! values back. We might not give the visitor back the value that it hinted that it wanted, but
//! it's up to the visitor to do its best to accept what it's handed, or reject it if it's simply
//! not going to work out.

use super::deserializer::DeserializerError;
use crate::prelude::*;
use crate::{BitSequence, Composite, ValueDef};
use serde::{
    de::{value::MapDeserializer, MapAccess, Visitor},
    ser::SerializeMap,
    Serializer,
};

/// We use this identifier in a map to uniquely identify a bitvec payload, so that it can
/// be differentiated from a standard [`ValueDef::Composite`] payload (which could also be a map).
pub static BITVEC_SERDE_IDENT: &str = "__bitvec__values__";

/// Serialize a bitvec so that the special deserializing is compatible with it.
pub fn serialize_bitvec<S>(seq: &BitSequence, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let mut map = serializer.serialize_map(Some(1))?;
    map.serialize_entry(BITVEC_SERDE_IDENT, seq)?;
    map.end()
}

/// Turn a [`BitSequence`] into a [`MapAccess`] impl that can be handed to a visitor to be consumed.
pub fn map_access<'de>(seq: BitSequence) -> impl MapAccess<'de, Error = DeserializerError> {
    let bools: Vec<bool> = seq.iter().collect();
    MapDeserializer::new([(BITVEC_SERDE_IDENT, bools)].into_iter())
}

/// This visits a map, and will extract from that either a [`ValueDef::Composite`] or a
/// [`ValueDef::BitSequence`] depending on the content of the map.
pub struct MapOrBitSeqVisitor;

impl<'de> Visitor<'de> for MapOrBitSeqVisitor {
    type Value = ValueDef<()>;

    fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
        formatter.write_str(
            "a map-like type that can be decoded into a Value::BitSequence or Value::Composite",
        )
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        // get the first key from the map:
        let first_key = match map.next_key::<String>()? {
            Some(key) => key,
            // No errors but the map appears to be empty; return an empty named composite.
            None => return Ok(ValueDef::Composite(Composite::Named(Vec::new()))),
        };

        // See whether the key identifies a bitvec payload:
        if first_key == BITVEC_SERDE_IDENT {
            // We should be able to decode a vec of bools as the value, then:
            let bits = map.next_value::<Vec<bool>>()?;
            // .. and we turn that into a bitvec to return:
            let mut bitvec = BitSequence::new();
            for bit in bits {
                bitvec.push(bit);
            }
            return Ok(ValueDef::BitSequence(bitvec));
        }

        // That didn't work, so decode the first value as a Value<()> instead:
        let mut values = Vec::with_capacity(map.size_hint().unwrap_or(0));
        values.push((first_key, map.next_value()?));

        // .. and then decode all of the other key-value pairs and add them too:
        while let Some(key_val) = map.next_entry()? {
            values.push(key_val);
        }
        Ok(ValueDef::Composite(Composite::Named(values)))
    }
}
