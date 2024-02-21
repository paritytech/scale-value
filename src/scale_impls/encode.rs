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

use core::fmt::Display;

use crate::prelude::*;
use crate::value_type::{Composite, Primitive, Value, ValueDef, Variant};
use codec::{Compact, Encode};
use scale_bits::Bits;
use scale_decode::TypeResolver;
use scale_encode::error::ErrorKind;
use scale_encode::{error::Kind, EncodeAsFields, EncodeAsType, Error};
use scale_encode::{
    Composite as EncodeComposite, CompositeField, FieldIter, Variant as EncodeVariant,
};

use scale_type_resolver::UnhandledKind;

impl<T> EncodeAsType for Value<T> {
    fn encode_as_type_to<R: TypeResolver>(
        &self,
        type_id: &R::TypeId,
        types: &R,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        match &self.value {
            ValueDef::Composite(val) => encode_composite(val, type_id, types, out),
            ValueDef::Variant(val) => encode_variant(val, type_id, types, out),
            ValueDef::Primitive(val) => encode_primitive(val, type_id, types, out),
            ValueDef::BitSequence(val) => encode_bitsequence(val, type_id, types, out),
        }
    }
}

impl<T> EncodeAsFields for Value<T> {
    fn encode_as_fields_to<R: TypeResolver>(
        &self,
        fields: &mut dyn FieldIter<'_, R::TypeId>,
        types: &R,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        match &self.value {
            ValueDef::Composite(composite) => composite.encode_as_fields_to(fields, types, out),
            _ => Err(Error::custom_str("Cannot encode non-composite Value shape into fields")),
        }
    }
}

impl<T> EncodeAsFields for Composite<T> {
    fn encode_as_fields_to<R: TypeResolver>(
        &self,
        fields: &mut dyn FieldIter<'_, R::TypeId>,
        types: &R,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        match self {
            Composite::Named(vals) => {
                let keyvals =
                    vals.iter().map(|(key, val)| (Some(&**key), CompositeField::new(val)));
                EncodeComposite::new(keyvals).encode_composite_fields_to(fields, types, out)
            }
            Composite::Unnamed(vals) => {
                let vals = vals.iter().map(|val| (None, CompositeField::new(val)));
                EncodeComposite::new(vals).encode_composite_fields_to(fields, types, out)
            }
        }
    }
}

// A scale-value composite type can represent sequences, arrays, composites and tuples. `scale_encode`'s Composite helper
// can't handle encoding to sequences/arrays. However, we can encode safely into sequences here because we can inspect the
// values we have and more safely skip newtype wrappers without also skipping through types that might represent 1-value
// sequences/arrays for instance.
fn encode_composite<'a, T, R: TypeResolver>(
    value: &Composite<T>,
    mut type_id: &'a R::TypeId,
    types: &'a R,
    out: &mut Vec<u8>,
) -> Result<(), Error> {
    // Encode our composite Value as-is (pretty much; we will try to
    // unwrap the Value only if we need primitives).
    fn do_encode_composite<T, R: TypeResolver>(
        value: &Composite<T>,
        type_id: &R::TypeId,
        types: &R,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        // let mut visit_tuple_or_composite = || match value {
        //     Composite::Named(vals) => {
        //         let keyvals =
        //             vals.iter().map(|(key, val)| (Some(&**key), CompositeField::new(val)));
        //         EncodeComposite::new(keyvals).encode_composite_as_type_to(type_id, types, out)
        //     }
        //     Composite::Unnamed(vals) => {
        //         let vals = vals.iter().map(|val| (None, CompositeField::new(val)));
        //         EncodeComposite::new(vals).encode_composite_as_type_to(type_id, types, out)
        //     }
        // };

        // let visitor = scale_type_resolver::visitor::new::<'_, (), R::TypeId, Result<(), Error>, _>(
        //     (),
        //     |_: (), err: UnhandledKind| {
        //         Err(Error::new(ErrorKind::Custom(Box::new(StringError(format!("{:?}", err))))))
        //     },
        // )
        // .visit_tuple(|_, _| visit_tuple_or_composite())
        // .visit_composite(|_, _| visit_tuple_or_composite());

        struct EncodingVisitor<'a, T, R: TypeResolver> {
            value: &'a Composite<T>,
            out: &'a mut Vec<u8>,
            types: &'a R,
            type_id: &'a R::TypeId,
        }

        impl<'a, T, R: TypeResolver> EncodingVisitor<'a, T, R> {
            fn visit_composite_or_tuple(self) -> Result<(), Error> {
                match self.value {
                    Composite::Named(vals) => {
                        let keyvals =
                            vals.iter().map(|(key, val)| (Some(&**key), CompositeField::new(val)));
                        EncodeComposite::new(keyvals).encode_composite_as_type_to(
                            self.type_id,
                            self.types,
                            self.out,
                        )
                    }
                    Composite::Unnamed(vals) => {
                        let vals = vals.iter().map(|val| (None, CompositeField::new(val)));
                        EncodeComposite::new(vals).encode_composite_as_type_to(
                            self.type_id,
                            self.types,
                            self.out,
                        )
                    }
                }
            }
        }

        impl<'a, T, R: TypeResolver> scale_type_resolver::ResolvedTypeVisitor<'a>
            for EncodingVisitor<'a, T, R>
        {
            type TypeId = R::TypeId;
            type Value = Result<(), Error>;

            fn visit_unhandled(self, _: UnhandledKind) -> Self::Value {
                let mut values = self.value.values();
                match (values.next(), values.next()) {
                    // Exactly one value:
                    (Some(value), None) => {
                        value.encode_as_type_to(self.type_id, self.types, self.out)
                    }
                    // Some other number of values:
                    _ => Err(Error::new(ErrorKind::WrongShape {
                        actual: Kind::Tuple,
                        expected_id: format!("{:?}", self.type_id),
                    })),
                }
            }

            fn visit_tuple<TypeIds>(self, _type_ids: TypeIds) -> Self::Value
            where
                TypeIds: ExactSizeIterator<Item = &'a Self::TypeId>,
            {
                self.visit_composite_or_tuple()
            }

            fn visit_composite<Fields>(self, _: Fields) -> Self::Value
            where
                Fields: FieldIter<'a, Self::TypeId>,
            {
                self.visit_composite_or_tuple()
            }

            fn visit_sequence(self, type_id: &'a Self::TypeId) -> Self::Value {
                // sequences start with compact encoded length:
                Compact(self.value.len() as u32).encode_to(self.out);
                match self.value {
                    Composite::Named(named_vals) => {
                        for (name, val) in named_vals {
                            val.encode_as_type_to(type_id, self.types, self.out)
                                .map_err(|e| e.at_field(name.to_string()))?;
                        }
                    }
                    Composite::Unnamed(vals) => {
                        for (idx, val) in vals.iter().enumerate() {
                            val.encode_as_type_to(type_id, self.types, self.out)
                                .map_err(|e| e.at_idx(idx))?;
                        }
                    }
                }
                Ok(())
            }

            fn visit_array(self, array_ty_id: &'a Self::TypeId, array_len: usize) -> Self::Value {
                if self.value.len() != array_len {
                    return Err(Error::new(ErrorKind::WrongLength {
                        actual_len: self.value.len(),
                        expected_len: array_len,
                    }));
                }
                for (idx, val) in self.value.values().enumerate() {
                    val.encode_as_type_to(array_ty_id, self.types, self.out)
                        .map_err(|e| e.at_idx(idx))?;
                }
                Ok(())
            }

            fn visit_bit_sequence(
                self,
                store: scale_type_resolver::BitsStoreFormat,
                order: scale_type_resolver::BitsOrderFormat,
            ) -> Self::Value {
                let format = scale_bits::Format { store, order };
                encode_vals_to_bitsequence(self.value.values(), self.out, format)
            }
        }

        let visitor = EncodingVisitor { value, out, types, type_id };
        match types.resolve_type(type_id, visitor) {
            Ok(Ok(())) => Ok(()),
            Ok(Err(err)) => Err(err),
            Err(err) => {
                Err(Error::new(ErrorKind::Custom(Box::new(StringError(format!("{:?}", err))))))
            }
        }
    }

    // First, try and encode everything as-is, only writing to the output
    // byte if the encoding is actually successful. This means that if the
    // Value provided matches the structure of the TypeInfo exactly, things
    // should always work.
    let original_error = {
        let mut temp_out = Vec::new();
        match do_encode_composite(value, type_id, types, &mut temp_out) {
            Ok(()) => {
                out.extend_from_slice(&temp_out);
                return Ok(());
            }
            Err(e) => e,
        }
    };

    // Next, unwrap any newtype wrappers from our TypeInfo and try again. If we
    // can unwrap, then try to encode our Value to this immediately (this will work
    // if the Value provided already ignored all newtype wrappers). If we have nothing
    // to unwrap then ignore this extra encode attempt.
    {
        let inner_type_id = find_single_entry_with_same_repr::<R>(type_id, types)
            .map_err(|err| Error::new(ErrorKind::TypeNotFound(format!("{:?}", err))))?;
        // Todo/Question: Of course this is completely stupid, we should probably add `PartialEq` bound for R::TypeId in general;
        if format!("{inner_type_id:?}") != format!("{type_id:?}") {
            let mut temp_out = Vec::new();
            if let Ok(()) = do_encode_composite(value, inner_type_id, types, &mut temp_out) {
                out.extend_from_slice(&temp_out);
                return Ok(());
            }
            type_id = inner_type_id;
        }
    }

    // Now, start peeling layers off our Value type in case some newtype wrappers
    // were provided. We do this one layer at a time because it's difficult or
    // impossible to know how to line values up with TypeInfo, so we can't just
    // strip lots of layers from the Value straight away. We continue to ignore
    // any errors here and will always return the original_error if we can't encode.
    // Everything past the original attempt is just trying to be flexible, anyway.
    while let Some(value) = get_only_value_from_composite(value) {
        let mut temp_out = Vec::new();
        if let Ok(()) = value.encode_as_type_to(type_id, types, &mut temp_out) {
            out.extend_from_slice(&temp_out);
            return Ok(());
        }
    }

    // return the original error we got back if none of the above is succcessful.
    Err(original_error)
}

// skip into the target type past any newtype wrapper like things:
fn find_single_entry_with_same_repr<'a, R: TypeResolver>(
    type_id: &'a R::TypeId,
    types: &'a R,
) -> Result<&'a R::TypeId, R::Error> {
    let visitor = scale_type_resolver::visitor::new(type_id, |original, _| original)
        .visit_tuple(|original, fields| {
            if fields.len() == 1 {
                let ty = fields.next().expect("has 1 item; qed;");
                find_single_entry_with_same_repr(ty, types).unwrap_or(original)
            } else {
                original
            }
        })
        .visit_composite(|original, fields| {
            if fields.len() == 1 {
                let ty = fields.next().expect("has 1 item; qed;").id;
                find_single_entry_with_same_repr(ty, types).unwrap_or(original)
            } else {
                original
            }
        })
        .visit_array(|original, ty_id, len| {
            if len == 1 {
                find_single_entry_with_same_repr(ty_id, types).unwrap_or(original)
            } else {
                original
            }
        });

    types.resolve_type(type_id, visitor)
}

// if the composite type has exactly one value, return that Value, else return None.
fn get_only_value_from_composite<T>(value: &'_ Composite<T>) -> Option<&'_ Value<T>> {
    let mut values = value.values();
    match (values.next(), values.next()) {
        (Some(value), None) => Some(value),
        _ => None,
    }
}

/// Error type for any string.
// Note:
#[derive(Debug, Clone)]
pub struct StringError(String);

impl Display for StringError {
    fn fmt(
        &self,
        f: &mut scale_info::prelude::fmt::Formatter<'_>,
    ) -> scale_info::prelude::fmt::Result {
        self.0.fmt(f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for StringError {}

// It's likely that people will use a composite to represen bit sequences,
// so support encoding to them in this way too.
fn encode_vals_to_bitsequence<'a, T: 'a>(
    vals: impl ExactSizeIterator<Item = &'a Value<T>>,
    out: &mut Vec<u8>,
    format: scale_bits::Format,
) -> Result<(), Error> {
    let mut bools = Vec::with_capacity(vals.len());
    for (idx, value) in vals.enumerate() {
        if let Some(v) = value.as_bool() {
            // support turning (true, false, true, true, false) into a bit sequence.
            bools.push(v);
        } else if let Some(v) = value.as_u128() {
            // support turning (1, 0, 1, 1, 0) into a bit sequence.
            if v == 0 || v == 1 {
                bools.push(v == 1)
            } else {
                return Err(Error::custom_str(
                    "Cannot encode non-boolean/0/1 value into a bit sequence entry",
                )
                .at_idx(idx));
            }
        } else if let Some(v) = value.as_i128() {
            // support turning (1, 0, 1, 1, 0) into a bit sequence (if the number's are not unsigned it's still fine).
            if v == 0 || v == 1 {
                bools.push(v == 1)
            } else {
                return Err(Error::custom_str(
                    "Cannot encode non-boolean/0/1 value into a bit sequence entry",
                )
                .at_idx(idx));
            }
        } else {
            // anything else is an error.
            return Err(Error::custom_str(
                "Cannot encode non-boolean/0/1 value into a bit sequence entry",
            )
            .at_idx(idx));
        }
    }

    scale_bits::encode_using_format_to(bools.into_iter(), format, out);
    Ok(())
}

fn encode_variant<T, R: TypeResolver>(
    value: &Variant<T>,
    type_id: &R::TypeId,
    types: &R,
    out: &mut Vec<u8>,
) -> Result<(), Error> {
    match &value.values {
        Composite::Named(vals) => {
            let keyvals = vals.iter().map(|(key, val)| (Some(&**key), CompositeField::new(val)));
            EncodeVariant { name: &value.name, fields: EncodeComposite::new(keyvals) }
                .encode_variant_as_type_to(type_id, types, out)
        }
        Composite::Unnamed(vals) => {
            let vals = vals.iter().map(|val| (None, CompositeField::new(val)));
            EncodeVariant { name: &value.name, fields: EncodeComposite::new(vals) }
                .encode_variant_as_type_to(type_id, types, out)
        }
    }
}

fn encode_primitive<R: TypeResolver>(
    value: &Primitive,
    type_id: &R::TypeId,
    types: &R,
    bytes: &mut Vec<u8>,
) -> Result<(), Error> {
    match value {
        Primitive::Bool(val) => val.encode_as_type_to(type_id, types, bytes),
        Primitive::Char(val) => val.encode_as_type_to(type_id, types, bytes),
        Primitive::String(val) => val.encode_as_type_to(type_id, types, bytes),
        Primitive::U128(val) => val.encode_as_type_to(type_id, types, bytes),
        Primitive::I128(val) => val.encode_as_type_to(type_id, types, bytes),
        Primitive::U256(val) => val.encode_as_type_to(type_id, types, bytes),
        Primitive::I256(val) => val.encode_as_type_to(type_id, types, bytes),
    }
}

fn encode_bitsequence<R: TypeResolver>(
    value: &Bits,
    type_id: &R::TypeId,
    types: &R,
    bytes: &mut Vec<u8>,
) -> Result<(), Error> {
    value.encode_as_type_to(type_id, types, bytes)
}

#[cfg(test)]
mod test {
    use crate::value;

    use super::*;
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

    // Attempt to SCALE encode a Value and expect it to match the standard Encode impl for the second param given.
    fn assert_can_encode_to_type<T: Encode + scale_info::TypeInfo + 'static>(
        value: Value<()>,
        ty: T,
    ) {
        let expected = ty.encode();
        let mut buf = Vec::new();

        let (ty_id, types) = make_type::<T>();

        value.encode_as_type_to(&ty_id, &types, &mut buf).expect("error encoding value as type");
        assert_eq!(expected, buf);
    }

    #[test]
    fn can_encode_basic_primitive_values() {
        assert_can_encode_to_type(Value::i128(123), 123i8);
        assert_can_encode_to_type(Value::i128(123), 123i16);
        assert_can_encode_to_type(Value::i128(123), 123i32);
        assert_can_encode_to_type(Value::i128(123), 123i64);
        assert_can_encode_to_type(Value::i128(123), 123i128);

        assert_can_encode_to_type(Value::u128(123), 123u8);
        assert_can_encode_to_type(Value::u128(123), 123u16);
        assert_can_encode_to_type(Value::u128(123), 123u32);
        assert_can_encode_to_type(Value::u128(123), 123u64);
        assert_can_encode_to_type(Value::u128(123), 123u128);

        assert_can_encode_to_type(Value::bool(true), true);
        assert_can_encode_to_type(Value::bool(false), false);

        assert_can_encode_to_type(Value::string("Hello"), "Hello");
        assert_can_encode_to_type(Value::string("Hello"), "Hello".to_string());
    }

    #[test]
    fn chars_encoded_like_numbers() {
        assert_can_encode_to_type(Value::char('j'), 'j' as u32);
        assert_can_encode_to_type(Value::char('j'), b'j');
    }

    #[test]
    fn can_encode_primitive_arrs_to_array() {
        use crate::Primitive;

        assert_can_encode_to_type(Value::primitive(Primitive::U256([12u8; 32])), [12u8; 32]);
        assert_can_encode_to_type(Value::primitive(Primitive::I256([12u8; 32])), [12u8; 32]);
    }

    #[test]
    fn can_encode_primitive_arrs_to_vecs() {
        use crate::Primitive;

        assert_can_encode_to_type(Value::primitive(Primitive::U256([12u8; 32])), vec![12u8; 32]);
        assert_can_encode_to_type(Value::primitive(Primitive::I256([12u8; 32])), vec![12u8; 32]);
    }

    #[test]
    fn can_encode_arrays() {
        let value = Value::unnamed_composite(vec![
            Value::u128(1),
            Value::u128(2),
            Value::u128(3),
            Value::u128(4),
        ]);
        assert_can_encode_to_type(value, [1u16, 2, 3, 4]);
    }

    #[test]
    fn can_encode_variants() {
        #[derive(Encode, scale_info::TypeInfo)]
        enum Foo {
            Named { hello: String, foo: bool },
            Unnamed(u64, Vec<bool>),
        }

        let named_value = value!(Named { foo: true, hello: "world" });

        assert_can_encode_to_type(named_value, Foo::Named { hello: "world".into(), foo: true });

        let unnamed_value = value!(Unnamed(123u64, (true, false, true)));

        assert_can_encode_to_type(unnamed_value, Foo::Unnamed(123, vec![true, false, true]));
    }

    #[test]
    fn can_encode_vec_tuples() {
        // Presume we have a type: Vec<(u8, u16)>.
        let vec_tuple = value!(((20u8, 30u16)));

        assert_can_encode_to_type(vec_tuple, vec![(20u8, 30u16)]);
    }

    #[test]
    fn can_encode_structs() {
        #[derive(Encode, scale_info::TypeInfo)]
        struct Foo {
            hello: String,
            foo: bool,
        }

        let named_value = value!({foo: true, hello: "world"});

        assert_can_encode_to_type(named_value, Foo { hello: "world".into(), foo: true });
    }

    #[test]
    fn can_encode_tuples_from_named_composite() {
        let named_value = value!({hello: "world", foo: true});
        assert_can_encode_to_type(named_value, ("world", true));
    }

    #[test]
    fn can_encode_tuples_from_unnamed_composite() {
        let unnamed_value = value!(("world", true));
        assert_can_encode_to_type(unnamed_value, ("world", true));
    }

    #[test]
    fn can_encode_unnamed_composite_to_named_struct() {
        #[derive(Encode, scale_info::TypeInfo)]
        struct Foo {
            hello: String,
            foo: bool,
        }

        // This is useful because things like transaction calls are often named composites, but
        // we just want to be able to provide the correct values as simply as possible without
        // necessarily knowing the names.
        let unnamed_value = value!(("world", true));
        assert_can_encode_to_type(unnamed_value, Foo { hello: "world".to_string(), foo: true });
    }

    #[test]
    fn can_encode_bitvecs() {
        use scale_bits::bits;

        // We have more thorough tests of bitvec encoding in scale-bits.
        // Here we just do a basic confirmation that bool composites or
        // bitsequences encode to the bits we'd expect.
        assert_can_encode_to_type(
            Value::bit_sequence(bits![0, 1, 1, 0, 0, 1]),
            bits![0, 1, 1, 0, 0, 1],
        );
        // a single value should still encode OK:
        assert_can_encode_to_type(value!((false)), bits![0]);
        assert_can_encode_to_type(
            value!((false, true, true, false, false, true)),
            bits![0, 1, 1, 0, 0, 1],
        );
        assert_can_encode_to_type(value!((0u8, 1u8, 1u8, 0u8, 0u8, 1u8)), bits![0, 1, 1, 0, 0, 1]);
        assert_can_encode_to_type(value!((0, 1, 1, 0, 0, 1)), bits![0, 1, 1, 0, 0, 1]);
    }

    #[test]
    fn can_encode_to_compact_types() {
        assert_can_encode_to_type(Value::u128(123), Compact(123u64));
        assert_can_encode_to_type(Value::u128(123), Compact(123u64));
        assert_can_encode_to_type(Value::u128(123), Compact(123u64));
        assert_can_encode_to_type(Value::u128(123), Compact(123u64));

        // As a special case, as long as ultimately we have a primitive value, we can compact encode it:
        assert_can_encode_to_type(value!((123)), Compact(123u64));
        assert_can_encode_to_type(value!(({foo: 123u64})), Compact(123u64));
    }

    #[test]
    fn can_encode_skipping_newtype_wrappers() {
        // One layer of "newtype" can be ignored:
        #[derive(Encode, scale_info::TypeInfo)]
        struct Foo {
            inner: u32,
        }
        assert_can_encode_to_type(Value::u128(32), Foo { inner: 32 });

        // Two layers can be ignored:
        #[derive(Encode, scale_info::TypeInfo)]
        struct Bar(Foo);
        assert_can_encode_to_type(Value::u128(32), Bar(Foo { inner: 32 }));
        assert_can_encode_to_type(value!((32u8)), Bar(Foo { inner: 32 }));

        // Encoding a Composite to a Composite(Composite) shape is fine too:
        #[derive(Encode, scale_info::TypeInfo)]
        struct SomeBytes(Vec<u8>);
        assert_can_encode_to_type(
            Value::from_bytes([1, 2, 3, 4, 5]),
            SomeBytes(vec![1, 2, 3, 4, 5]),
        );
        assert_can_encode_to_type(Value::from_bytes([1]), SomeBytes(vec![1]));
    }
}
