// Copyright (C) 2022-2024 Parity Technologies (UK) Ltd. (admin@parity.io)
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

use crate::prelude::*;

use super::error::TraceDecodingError;
use super::path::Path;
use crate::{Composite, Primitive, Value, ValueDef, Variant};
use core::marker::PhantomData;
use scale_decode::visitor::TypeIdFor;
use scale_type_resolver::TypeResolver;

/// A visitor that will attempt to decode some bytes into a [`crate::Value`],
/// returning a detailed error of where the decoding fails if it does.
pub struct TraceDecodingVisitor<Resolver> {
    path: Path,
    marker: PhantomData<Resolver>,
}

impl<Resolver> TraceDecodingVisitor<Resolver> {
    fn at_path(&self, path: Path) -> Self {
        TraceDecodingVisitor { path, marker: PhantomData }
    }
    fn at_idx(&self, idx: usize) -> Self {
        self.at_path(self.path.at_idx(idx))
    }
    fn at_field(&self, field: String) -> Self {
        self.at_path(self.path.at_field(field))
    }
}

impl<Resolver> Default for TraceDecodingVisitor<Resolver> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Resolver> TraceDecodingVisitor<Resolver> {
    /// Construct a new [`TraceDecodingVisitor`].
    pub fn new() -> Self {
        TraceDecodingVisitor { path: Path::new(), marker: PhantomData }
    }
}

macro_rules! to_unnamed_composite {
    ($self:ident, $value:ident) => {{
        let mut f = move || {
            let mut idx = 0;
            let mut vals = Vec::with_capacity($value.remaining());

            while let Some(val) = $value.decode_item($self.at_idx(idx)) {
                match val {
                    Err(e) => {
                        let merged_error = e.with_outer_context(
                            || $self.path.at_idx(idx),
                            || Composite::Unnamed(vals.clone()),
                            |inner_value| {
                                let mut vals = vals.clone();
                                vals.push(inner_value);
                                Composite::Unnamed(vals)
                            },
                        );
                        return Err(merged_error);
                    }
                    Ok(v) => {
                        vals.push(v);
                    }
                }

                idx += 1;
            }

            Ok::<_, TraceDecodingError<_>>(Composite::Unnamed(vals))
        };

        f()
    }};
}

macro_rules! to_unnamed_composite_value {
    ($self:ident, $value:ident, $type_id:ident) => {{
        let composite = to_unnamed_composite!($self, $value).map_err(|e| {
            e.map_decoded_so_far(|c| Value {
                value: ValueDef::Composite(c),
                context: $type_id.clone(),
            })
        })?;

        Ok(Value { value: ValueDef::Composite(composite), context: $type_id })
    }};
}

impl<Resolver> scale_decode::Visitor for TraceDecodingVisitor<Resolver>
where
    Resolver: TypeResolver,
{
    type Value<'scale, 'resolver> = Value<TypeIdFor<Self>>;
    type Error = TraceDecodingError<Value<TypeIdFor<Self>>>;
    type TypeResolver = Resolver;

    fn visit_bool<'scale, 'resolver>(
        self,
        value: bool,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        Ok(Value::with_context(ValueDef::Primitive(Primitive::Bool(value)), type_id))
    }

    fn visit_char<'scale, 'resolver>(
        self,
        value: char,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        Ok(Value::with_context(ValueDef::Primitive(Primitive::Char(value)), type_id))
    }

    fn visit_u8<'scale, 'resolver>(
        self,
        value: u8,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        self.visit_u128(value as u128, type_id)
    }

    fn visit_u16<'scale, 'resolver>(
        self,
        value: u16,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        self.visit_u128(value as u128, type_id)
    }

    fn visit_u32<'scale, 'resolver>(
        self,
        value: u32,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        self.visit_u128(value as u128, type_id)
    }

    fn visit_u64<'scale, 'resolver>(
        self,
        value: u64,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        self.visit_u128(value as u128, type_id)
    }

    fn visit_u128<'scale, 'resolver>(
        self,
        value: u128,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        Ok(Value::with_context(ValueDef::Primitive(Primitive::U128(value)), type_id))
    }

    fn visit_u256<'info>(
        self,
        value: &[u8; 32],
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'_, 'info>, Self::Error> {
        Ok(Value::with_context(ValueDef::Primitive(Primitive::U256(*value)), type_id))
    }

    fn visit_i8<'scale, 'resolver>(
        self,
        value: i8,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        self.visit_i128(value as i128, type_id)
    }

    fn visit_i16<'scale, 'resolver>(
        self,
        value: i16,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        self.visit_i128(value as i128, type_id)
    }

    fn visit_i32<'scale, 'resolver>(
        self,
        value: i32,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        self.visit_i128(value as i128, type_id)
    }

    fn visit_i64<'scale, 'resolver>(
        self,
        value: i64,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        self.visit_i128(value as i128, type_id)
    }

    fn visit_i128<'scale, 'resolver>(
        self,
        value: i128,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        Ok(Value::with_context(ValueDef::Primitive(Primitive::I128(value)), type_id))
    }

    fn visit_i256<'info>(
        self,
        value: &[u8; 32],
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'_, 'info>, Self::Error> {
        Ok(Value::with_context(ValueDef::Primitive(Primitive::I256(*value)), type_id))
    }

    fn visit_bitsequence<'scale, 'info>(
        self,
        value: &mut scale_decode::visitor::types::BitSequence<'scale>,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        let bits: Result<_, _> = value.decode()?.collect();
        Ok(Value::with_context(ValueDef::BitSequence(bits?), type_id))
    }

    fn visit_str<'scale, 'info>(
        self,
        value: &mut scale_decode::visitor::types::Str<'scale>,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        Ok(Value::with_context(
            ValueDef::Primitive(Primitive::String(value.as_str()?.to_owned())),
            type_id,
        ))
    }

    fn visit_sequence<'scale, 'resolver>(
        self,
        value: &mut scale_decode::visitor::types::Sequence<'scale, 'resolver, Self::TypeResolver>,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        to_unnamed_composite_value!(self, value, type_id)
    }

    fn visit_array<'scale, 'resolver>(
        self,
        value: &mut scale_decode::visitor::types::Array<'scale, 'resolver, Self::TypeResolver>,
        type_id: scale_decode::visitor::TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        to_unnamed_composite_value!(self, value, type_id)
    }

    fn visit_tuple<'scale, 'resolver>(
        self,
        value: &mut scale_decode::visitor::types::Tuple<'scale, 'resolver, Self::TypeResolver>,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        to_unnamed_composite_value!(self, value, type_id)
    }

    fn visit_variant<'scale, 'resolver>(
        self,
        value: &mut scale_decode::visitor::types::Variant<'scale, 'resolver, Self::TypeResolver>,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        let variant_name = value.name();
        let path = self.path.at_variant(variant_name.to_owned());
        let values = visit_composite(&self, value.fields());
        match values {
            Err(e) => {
                let merged_error = e.with_outer_context(
                    || path.clone(),
                    || Value {
                        value: ValueDef::Variant(Variant {
                            name: variant_name.to_owned(),
                            values: Composite::Unnamed(vec![]),
                        }),
                        context: type_id.clone(),
                    },
                    |inner_value| Value {
                        value: ValueDef::Variant(Variant {
                            name: variant_name.to_owned(),
                            values: inner_value,
                        }),
                        context: type_id.clone(),
                    },
                );
                Err(merged_error)
            }
            Ok(values) => Ok(Value {
                value: ValueDef::Variant(Variant { name: variant_name.to_owned(), values }),
                context: type_id,
            }),
        }
    }

    fn visit_composite<'scale, 'resolver>(
        self,
        value: &mut scale_decode::visitor::types::Composite<'scale, 'resolver, Self::TypeResolver>,
        type_id: TypeIdFor<Self>,
    ) -> Result<Self::Value<'scale, 'resolver>, Self::Error> {
        let composite_vals = visit_composite(&self, value).map_err(|e| {
            e.map_decoded_so_far(|c| Value {
                value: ValueDef::Composite(c),
                context: type_id.clone(),
            })
        })?;

        Ok(Value { value: ValueDef::Composite(composite_vals), context: type_id })
    }
}

fn visit_composite<R>(
    this: &TraceDecodingVisitor<R>,
    value: &mut scale_decode::visitor::types::Composite<'_, '_, R>,
) -> Result<Composite<R::TypeId>, TraceDecodingError<Composite<R::TypeId>>>
where
    R: TypeResolver,
{
    let len = value.remaining();

    // if no fields, we'll always assume unnamed.
    let named = len > 0 && !value.has_unnamed_fields();

    // if unnamed, treat like array/tuple/sequence.
    if !named {
        return to_unnamed_composite!(this, value);
    }

    // otherwise, treat as a named struct.
    let mut vals = Vec::with_capacity(len);
    let mut name = value.peek_name().unwrap_or("<unnamed>");

    while let Some(val) = value.decode_item(this.at_field(name.to_owned())) {
        match val {
            Err(e) => {
                let merged_error = e.with_outer_context(
                    || this.path.at_field(name.to_owned()),
                    || Composite::Named(vals.clone()),
                    |inner_value| {
                        let mut vals = vals.clone();
                        vals.push((name.to_owned(), inner_value));
                        Composite::Named(vals)
                    },
                );
                return Err(merged_error);
            }
            Ok(v) => {
                vals.push((name.to_owned(), v));
            }
        }

        name = value.peek_name().unwrap_or("<unnamed>");
    }

    Ok(Composite::Named(vals))
}
