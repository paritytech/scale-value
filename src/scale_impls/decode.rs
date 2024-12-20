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

use core::marker::PhantomData;

use crate::prelude::*;
use crate::value_type::{Composite, Primitive, Value, ValueDef, Variant};
use scale_decode::{FieldIter, TypeResolver};

// This is emitted if something goes wrong decoding into a Value.
pub use scale_decode::visitor::DecodeError;

/// A visitor that can be used to decode types into [`Value`]s.
pub type ValueVisitor<Resolver> = DecodeValueVisitor<Resolver, TypeIdContext>;

/// Attempt to decode some SCALE encoded bytes into a value, by providing a pointer
/// to the bytes (which will be moved forwards as bytes are used in the decoding),
/// a type ID, and a type registry from which we'll look up the relevant type information.
pub fn decode_value_as_type<R>(
    data: &mut &[u8],
    ty_id: R::TypeId,
    types: &R,
) -> Result<Value<R::TypeId>, DecodeError>
where
    R: TypeResolver,
    R::TypeId: Clone,
{
    scale_decode::visitor::decode_with_visitor(
        data,
        ty_id,
        types,
        DecodeValueVisitor::<R, TypeIdContext>::new(),
    )
}

/// Decode data into a [`Composite`] according to a series of fields.
/// Each field contains a type id and optionally a field name.
pub fn decode_composite_as_fields<'resolver, R>(
    input: &mut &[u8],
    fields: &mut dyn FieldIter<'resolver, R::TypeId>,
    types: &'resolver R,
) -> Result<Composite<R::TypeId>, DecodeError>
where
    R: TypeResolver,
    R::TypeId: Clone,
{
    // Build a Composite type to pass to a one-off visitor:
    let mut composite = scale_decode::visitor::types::Composite::new(
        core::iter::empty(),
        input,
        fields,
        types,
        false,
    );
    // Decode into a Composite value from this:
    let val = visit_composite::<R, TypeIdContext>(&mut composite)?;
    // Consume remaining bytes and update input cursor:
    composite.skip_decoding()?;
    *input = composite.bytes_from_undecoded();
    Ok(val)
}

// Sequences, Tuples and Arrays all have the same methods, so decode them in the same way:
macro_rules! to_unnamed_composite {
    ($value:ident, $type_id:ident) => {{
        let mut vals = Vec::with_capacity($value.remaining());
        while let Some(val) = $value.decode_item(DecodeValueVisitor::<R, F>::new()) {
            let val = val?;
            vals.push(val);
        }
        Ok(Value {
            value: ValueDef::Composite(Composite::Unnamed(vals)),
            context: F::context_from_type_id(&$type_id),
        })
    }};
}

// We can't implement this on `Value<TypeId>` because we have no TypeId to assign to the value.
impl scale_decode::DecodeAsFields for Composite<()> {
    fn decode_as_fields<'resolver, R: TypeResolver>(
        input: &mut &[u8],
        fields: &mut dyn FieldIter<'resolver, R::TypeId>,
        types: &'resolver R,
    ) -> Result<Self, scale_decode::Error> {
        // Build a Composite type to pass to a one-off visitor:
        let mut composite = scale_decode::visitor::types::Composite::new(
            core::iter::empty(),
            input,
            fields,
            types,
            false,
        );
        // Decode into a Composite value from this:
        let val = visit_composite::<R, EmptyContext>(&mut composite);
        // Consume remaining bytes and update input cursor:
        composite.skip_decoding()?;
        *input = composite.bytes_from_undecoded();
        val.map_err(From::from).map(|v| v.map_context(|_| {}))
    }
}

impl scale_decode::IntoVisitor for Value<()> {
    // Note: the DefaultMapper just removes all type ids here.
    type AnyVisitor<R: scale_decode::TypeResolver> =
        scale_decode::visitor::VisitorWithCrateError<DecodeValueVisitor<R, EmptyContext>>;

    fn into_visitor<R: scale_decode::TypeResolver>() -> Self::AnyVisitor<R> {
        scale_decode::visitor::VisitorWithCrateError(DecodeValueVisitor::new())
    }
}

/// We can use [`DecodeValueVisitor`] to decode values, but have two cases to handle:
///
/// - We need to be able to decode into [`Value<()>`] for our [`scale_decode::IntoVisitor`]
///   implementation above (because that trait is agnostic over which visitor is used, and thus
///   can't have any knowledge on the TypeId type).
/// - We need to be able to decode into [`Value<TypeId>`] via the [`decode_value_as_type`] fn
///   above.
///
/// This trait basically allows us to handle each case by having a function that is given a
/// `TypeId` and decides whether to hand back `()` or the `TypeId`.
pub trait ContextFromTypeId<TypeId> {
    type Output;
    fn context_from_type_id(type_id: &TypeId) -> Self::Output;
}

/// Return () for our value context.
pub struct EmptyContext;
impl<TypeId> ContextFromTypeId<TypeId> for EmptyContext {
    type Output = ();
    fn context_from_type_id(_type_id: &TypeId) {}
}

/// Return the type ID for our value context.
pub struct TypeIdContext;
impl<TypeId: Clone> ContextFromTypeId<TypeId> for TypeIdContext {
    type Output = TypeId;
    fn context_from_type_id(type_id: &TypeId) -> TypeId {
        type_id.clone()
    }
}

/// A [`scale_decode::Visitor`] implementation for decoding into [`Value`]s.
pub struct DecodeValueVisitor<R: TypeResolver, F> {
    resolver: PhantomData<(R, F)>,
}
impl<R: TypeResolver, F> Default for DecodeValueVisitor<R, F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<R: TypeResolver, F> DecodeValueVisitor<R, F> {
    pub fn new() -> Self {
        DecodeValueVisitor { resolver: PhantomData }
    }
}

impl<R, F> scale_decode::visitor::Visitor for DecodeValueVisitor<R, F>
where
    R: TypeResolver,
    F: ContextFromTypeId<R::TypeId>,
{
    type Value<'scale, 'info> = Value<F::Output>;
    type Error = DecodeError;
    type TypeResolver = R;

    fn visit_bool<'scale, 'info>(
        self,
        value: bool,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        Ok(Value::bool(value).map_context(|_| F::context_from_type_id(&type_id)))
    }
    fn visit_char<'scale, 'info>(
        self,
        value: char,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        Ok(Value::char(value).map_context(|_| F::context_from_type_id(&type_id)))
    }
    fn visit_u8<'scale, 'info>(
        self,
        value: u8,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        self.visit_u128(value as u128, type_id)
    }
    fn visit_u16<'scale, 'info>(
        self,
        value: u16,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        self.visit_u128(value as u128, type_id)
    }
    fn visit_u32<'scale, 'info>(
        self,
        value: u32,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        self.visit_u128(value as u128, type_id)
    }
    fn visit_u64<'scale, 'info>(
        self,
        value: u64,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        self.visit_u128(value as u128, type_id)
    }
    fn visit_u128<'scale, 'info>(
        self,
        value: u128,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        Ok(Value::u128(value).map_context(|_| F::context_from_type_id(&type_id)))
    }
    fn visit_u256<'info>(
        self,
        value: &[u8; 32],
        type_id: R::TypeId,
    ) -> Result<Self::Value<'_, 'info>, Self::Error> {
        Ok(Value {
            value: ValueDef::Primitive(Primitive::U256(*value)),
            context: F::context_from_type_id(&type_id),
        })
    }
    fn visit_i8<'scale, 'info>(
        self,
        value: i8,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        self.visit_i128(value as i128, type_id)
    }
    fn visit_i16<'scale, 'info>(
        self,
        value: i16,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        self.visit_i128(value as i128, type_id)
    }
    fn visit_i32<'scale, 'info>(
        self,
        value: i32,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        self.visit_i128(value as i128, type_id)
    }
    fn visit_i64<'scale, 'info>(
        self,
        value: i64,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        self.visit_i128(value as i128, type_id)
    }
    fn visit_i128<'scale, 'info>(
        self,
        value: i128,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        Ok(Value::i128(value).map_context(|_| F::context_from_type_id(&type_id)))
    }
    fn visit_i256<'info>(
        self,
        value: &[u8; 32],
        type_id: R::TypeId,
    ) -> Result<Self::Value<'_, 'info>, Self::Error> {
        Ok(Value {
            value: ValueDef::Primitive(Primitive::U256(*value)),
            context: F::context_from_type_id(&type_id),
        })
    }
    fn visit_sequence<'scale, 'info>(
        self,
        value: &mut scale_decode::visitor::types::Sequence<'scale, 'info, R>,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        to_unnamed_composite!(value, type_id)
    }
    fn visit_tuple<'scale, 'info>(
        self,
        value: &mut scale_decode::visitor::types::Tuple<'scale, 'info, R>,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        to_unnamed_composite!(value, type_id)
    }
    fn visit_array<'scale, 'info>(
        self,
        value: &mut scale_decode::visitor::types::Array<'scale, 'info, R>,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        to_unnamed_composite!(value, type_id)
    }
    fn visit_bitsequence<'scale, 'info>(
        self,
        value: &mut scale_decode::visitor::types::BitSequence<'scale>,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        let bits: Result<_, _> = value.decode()?.collect();
        Ok(Value {
            value: ValueDef::BitSequence(bits?),
            context: F::context_from_type_id(&type_id),
        })
    }
    fn visit_str<'scale, 'info>(
        self,
        value: &mut scale_decode::visitor::types::Str<'scale>,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        Ok(Value::string(value.as_str()?).map_context(|_| F::context_from_type_id(&type_id)))
    }
    fn visit_variant<'scale, 'info>(
        self,
        value: &mut scale_decode::visitor::types::Variant<'scale, 'info, R>,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        let values = visit_composite::<R, F>(value.fields())?;
        Ok(Value {
            value: ValueDef::Variant(Variant { name: value.name().to_owned(), values }),
            context: F::context_from_type_id(&type_id),
        })
    }
    fn visit_composite<'scale, 'info>(
        self,
        value: &mut scale_decode::visitor::types::Composite<'scale, 'info, R>,
        type_id: R::TypeId,
    ) -> Result<Self::Value<'scale, 'info>, Self::Error> {
        Ok(Value {
            value: ValueDef::Composite(visit_composite::<R, F>(value)?),
            context: F::context_from_type_id(&type_id),
        })
    }
}

/// Extract a named/unnamed Composite type out of scale_decode's Composite.
fn visit_composite<R, F>(
    value: &mut scale_decode::visitor::types::Composite<'_, '_, R>,
) -> Result<Composite<F::Output>, DecodeError>
where
    R: TypeResolver,
    F: ContextFromTypeId<R::TypeId>,
{
    let len = value.remaining();
    // if no fields, we'll always assume unnamed.
    let named = len > 0 && !value.has_unnamed_fields();

    if named {
        let mut vals = Vec::with_capacity(len);
        let mut name = value.peek_name();
        while let Some(v) = value.decode_item(DecodeValueVisitor::<R, F>::new()) {
            let v = v?;
            vals.push((name.expect("all fields should be named; we have checked").to_owned(), v));
            // get the next field name now we've decoded one.
            name = value.peek_name();
        }
        Ok(Composite::Named(vals))
    } else {
        let mut vals = Vec::with_capacity(len);
        while let Some(v) = value.decode_item(DecodeValueVisitor::<R, F>::new()) {
            let v = v?;
            vals.push(v);
        }
        Ok(Composite::Unnamed(vals))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::value;
    use codec::{Compact, Encode};
    use scale_info::PortableRegistry;

    /// Given a type definition, return the PortableType and PortableRegistry
    /// that our decode functions expect.
    fn make_type<T: scale_info::TypeInfo + 'static>() -> (u32, PortableRegistry) {
        let m = scale_info::MetaType::new::<T>();
        let mut types = scale_info::Registry::new();
        let id = types.register_type(&m);
        let portable_registry: PortableRegistry = types.into();

        (id.id, portable_registry)
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
        //     [123u8; 32], // Anything 32 bytes long will do here
        //     Value::u256([123u8; 32]),
        // );
        encode_decode_check(123i8, Value::i128(123));
        encode_decode_check(123i16, Value::i128(123));
        encode_decode_check(123i32, Value::i128(123));
        encode_decode_check(123i64, Value::i128(123));
        encode_decode_check(123i128, Value::i128(123));
        //// Todo [jsdw]: Can we test this if we need a TypeInfo param?:
        // encode_decode_check_explicit_info(
        //     [123u8; 32], // Anything 32 bytes long will do here
        //     Value::i256([123u8; 32]),
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
            Value::named_composite(vec![("inner", Value::u128(123))]),
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
        encode_decode_check(vec![1i32, 2, 3], value!((1, 2, 3)));
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
            value!(Bar { hi: "hello", other: 123u32 }),
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
            value!((true, "James", (1u8, 2u8, 3u8))),
        );
        encode_decode_check(
            Named { is_valid: true, name: "James".into(), bytes: vec![1, 2, 3] },
            value!({is_valid: true, name: "James", bytes: (1u8, 2u8, 3u8)}),
        );
    }

    #[test]
    fn decoding_zero_length_composites_always_unnamed() {
        // The scale-info repr is just a composite, so we don't really track
        // whether the thing was named or not. either Value will convert back ok anyway.
        #[derive(Encode, scale_info::TypeInfo)]
        struct Named {}
        #[derive(Encode, scale_info::TypeInfo)]
        struct Unnamed();

        encode_decode_check(Unnamed(), Value::unnamed_composite(vec![]));
        encode_decode_check(Named {}, Value::unnamed_composite(vec![]));
    }

    #[test]
    fn decode_bit_sequence() {
        use scale_bits::bits;

        // scale-decode already tests this more thoroughly:
        encode_decode_check(bits![0, 1, 1, 0, 1, 0], Value::bit_sequence(bits![0, 1, 1, 0, 1, 0]));
    }

    #[test]
    fn decode_composite_fields() {
        use codec::Encode;
        use scale_decode::DecodeAsFields;

        #[derive(Encode, scale_decode::DecodeAsType, scale_info::TypeInfo)]
        struct Foo {
            a: String,
            b: bool,
            c: u16,
        }

        // Get the fields we want to decode:
        let (id, types) = make_type::<Foo>();
        let scale_info::TypeDef::Composite(c) = &types.resolve(id).unwrap().type_def else {
            panic!("Couldn't get fields");
        };
        let mut fields = c.fields.iter().map(|f| scale_decode::Field::new(f.ty.id, f.name));

        // get some bytes to decode from:
        let foo = Foo { a: "Hello".to_owned(), b: true, c: 123 };
        let foo_bytes = foo.encode();
        let foo_bytes_cursor = &mut &*foo_bytes;

        // Decode and check that things line up:
        let out = Composite::decode_as_fields(foo_bytes_cursor, &mut fields, &types)
            .expect("can decode as fields")
            .map_context(|_| ());
        assert_eq!(
            out,
            Composite::named([
                ("a", Value::string("Hello")),
                ("b", Value::bool(true)),
                ("c", Value::u128(123))
            ])
        );
        assert_eq!(foo_bytes_cursor.len(), 0, "all bytes should have been consumed");
    }
}
