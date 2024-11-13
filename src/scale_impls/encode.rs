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

impl<T> EncodeAsType for Value<T> {
    fn encode_as_type_to<R: TypeResolver>(
        &self,
        type_id: R::TypeId,
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
fn encode_composite<T, R: TypeResolver>(
    value: &Composite<T>,
    mut type_id: R::TypeId,
    types: &R,
    out: &mut Vec<u8>,
) -> Result<(), Error> {
    // Encode our composite Value as-is (pretty much; we will try to
    // unwrap the Value only if we need primitives).
    fn do_encode_composite<T, R: TypeResolver>(
        value: &Composite<T>,
        type_id: R::TypeId,
        types: &R,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        // context to hand to visitor functions:
        let ctx = (type_id.clone(), out);

        let visit_composite_or_tuple =
            |(type_id, out): (R::TypeId, &mut Vec<u8>)| -> Result<(), Error> {
                match value {
                    Composite::Named(vals) => {
                        let keyvals =
                            vals.iter().map(|(key, val)| (Some(&**key), CompositeField::new(val)));
                        EncodeComposite::new(keyvals)
                            .encode_composite_as_type_to(type_id, types, out)
                    }
                    Composite::Unnamed(vals) => {
                        let vals = vals.iter().map(|val| (None, CompositeField::new(val)));
                        EncodeComposite::new(vals).encode_composite_as_type_to(type_id, types, out)
                    }
                }
            };

        let visitor = scale_type_resolver::visitor::new::<
            '_,
            (R::TypeId, &mut Vec<u8>),
            R::TypeId,
            Result<(), Error>,
            _,
        >(ctx, |(type_id, out), _| {
            let mut values = value.values();
            match (values.next(), values.next()) {
                // Exactly one value:
                (Some(value), None) => value.encode_as_type_to(type_id, types, out),
                // Some other number of values:
                _ => Err(Error::new(ErrorKind::WrongShape {
                    actual: Kind::Tuple,
                    expected_id: format!("{:?}", type_id),
                })),
            }
        })
        .visit_composite(|ctx, _, _| visit_composite_or_tuple(ctx))
        .visit_tuple(|ctx, _| visit_composite_or_tuple(ctx))
        .visit_sequence(|(_, out), _path, type_id| {
            // sequences start with compact encoded length:
            Compact(value.len() as u32).encode_to(out);
            match value {
                Composite::Named(named_vals) => {
                    for (name, val) in named_vals {
                        val.encode_as_type_to(type_id.clone(), types, out)
                            .map_err(|e| e.at_field(name.to_string()))?;
                    }
                }
                Composite::Unnamed(vals) => {
                    for (idx, val) in vals.iter().enumerate() {
                        val.encode_as_type_to(type_id.clone(), types, out)
                            .map_err(|e| e.at_idx(idx))?;
                    }
                }
            }
            Ok(())
        })
        .visit_array(|(_, out), type_id, array_len| {
            if value.len() != array_len {
                return Err(Error::new(ErrorKind::WrongLength {
                    actual_len: value.len(),
                    expected_len: array_len,
                }));
            }
            for (idx, val) in value.values().enumerate() {
                val.encode_as_type_to(type_id.clone(), types, out).map_err(|e| e.at_idx(idx))?;
            }
            Ok(())
        })
        .visit_bit_sequence(|(_, out), store, order| {
            let format = scale_bits::Format { store, order };
            encode_vals_to_bitsequence(value.values(), out, format)
        });

        match types.resolve_type(type_id, visitor) {
            Ok(Ok(())) => Ok(()),
            Ok(Err(err)) => Err(err),
            Err(err) => Err(Error::new(ErrorKind::TypeResolvingError(format!("{:?}", err)))),
        }
    }

    // First, try and encode everything as-is, only writing to the output
    // bytes if the encoding is actually successful. This means that if the
    // Value provided matches the structure of the TypeInfo exactly, things
    // should always work.
    let original_error = {
        let mut temp_out = Vec::new();
        match do_encode_composite(value, type_id.clone(), types, &mut temp_out) {
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
        let (inner_type_id, inner_is_different) =
            find_single_entry_with_same_repr::<R>(type_id.clone(), types);
        if inner_is_different {
            let mut temp_out = Vec::new();
            if let Ok(()) = do_encode_composite(value, inner_type_id.clone(), types, &mut temp_out)
            {
                out.extend_from_slice(&temp_out);
                return Ok(());
            }
            type_id = inner_type_id;
        }
    }

    // Peel off a single layer from the provided Value (if it appears to be new-type-esque,
    // ie contains just one value) to see if, after doing so, the thing can be successfully
    // encoded. The inner `.encode_as_type_to` will loop around and peel off another layer
    // etc if no luck. Ultimately we'll just return the original error below if this all
    // fails.
    if let Some(value) = get_only_value_from_composite(value) {
        let mut temp_out = Vec::new();
        if let Ok(()) = value.encode_as_type_to(type_id.clone(), types, &mut temp_out) {
            out.extend_from_slice(&temp_out);
            return Ok(());
        }
    }

    // return the original error we got back if none of the above is succcessful.
    Err(original_error)
}

/// Skip into the target type past any newtype wrapper like things.
/// Also returns a bool indicating whether we skipped into something or not.
/// This bool is true when the returned id is different from the id that was passed in.
fn find_single_entry_with_same_repr<R: TypeResolver>(
    type_id: R::TypeId,
    types: &R,
) -> (R::TypeId, bool) {
    fn do_find<R: TypeResolver>(
        type_id: R::TypeId,
        types: &R,
        type_id_has_changed: bool,
    ) -> (R::TypeId, bool) {
        let ctx = (type_id.clone(), type_id_has_changed);
        let visitor = scale_type_resolver::visitor::new(ctx.clone(), |ctx, _| ctx)
            .visit_tuple(|return_unchanged, fields| {
                if fields.len() == 1 {
                    let ty = fields.next().expect("has 1 item; qed;");
                    do_find(ty, types, true)
                } else {
                    return_unchanged
                }
            })
            .visit_composite(|return_unchanged, _, fields| {
                if fields.len() == 1 {
                    let ty = fields.next().expect("has 1 item; qed;").id;
                    do_find(ty, types, true)
                } else {
                    return_unchanged
                }
            })
            .visit_array(
                |return_unchanged, ty_id, len| {
                    if len == 1 {
                        do_find(ty_id, types, true)
                    } else {
                        return_unchanged
                    }
                },
            );
        types.resolve_type(type_id, visitor).unwrap_or(ctx)
    }
    do_find(type_id, types, false)
}

// if the composite type has exactly one value, return that Value, else return None.
fn get_only_value_from_composite<T>(value: &'_ Composite<T>) -> Option<&'_ Value<T>> {
    let mut values = value.values();
    match (values.next(), values.next()) {
        (Some(value), None) => Some(value),
        _ => None,
    }
}

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
    type_id: R::TypeId,
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
    type_id: R::TypeId,
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
    type_id: R::TypeId,
    types: &R,
    bytes: &mut Vec<u8>,
) -> Result<(), Error> {
    value.encode_as_type_to(type_id, types, bytes)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::value;
    use codec::{Compact, Encode};
    use scale_info::PortableRegistry;

    // Panic after some duration.
    #[cfg(feature = "__std")]
    fn panic_after<T, F>(d: core::time::Duration, f: F) -> T
    where
        T: Send + 'static,
        F: FnOnce() -> T,
        F: Send + 'static,
    {
        extern crate std;

        use std::{sync::mpsc, thread};

        let (done_tx, done_rx) = mpsc::channel();
        let handle = thread::spawn(move || {
            let val = f();
            done_tx.send(()).expect("Unable to send completion signal");
            val
        });

        match done_rx.recv_timeout(d) {
            Ok(_) => handle.join().expect("Thread panicked"),
            Err(_) => panic!("Thread took too long"),
        }
    }

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

        value.encode_as_type_to(ty_id, &types, &mut buf).expect("error encoding value as type");
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
    fn can_encode_skipping_struct_newtype_wrappers() {
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

    #[test]
    fn can_encode_skipping_value_newtype_wrappers() {
        #[derive(Encode, scale_info::TypeInfo)]
        struct Foo {
            inner: u32,
        }

        // The correct number of layers to match Foo
        assert_can_encode_to_type(
            Value::unnamed_composite(vec![Value::u128(32)]),
            Foo { inner: 32 },
        );
        // One layer too many.
        assert_can_encode_to_type(
            Value::unnamed_composite(vec![Value::unnamed_composite(vec![Value::u128(32)])]),
            Foo { inner: 32 },
        );
        // Two layers too many.
        assert_can_encode_to_type(
            Value::unnamed_composite(vec![Value::unnamed_composite(vec![
                Value::unnamed_composite(vec![Value::u128(32)]),
            ])]),
            Foo { inner: 32 },
        );
    }

    // Prior to https://github.com/paritytech/scale-value/pulls/48, this test will take
    // too long and panic. #48 should ensure that this doesn't happen.
    #[test]
    #[cfg(feature = "__std")]
    fn encoding_shouldnt_take_forever() {
        panic_after(core::time::Duration::from_millis(100), || {
            #[derive(scale_info::TypeInfo, codec::Encode)]
            struct A(bool);

            let mut buf = Vec::new();
            let (ty_id, types) = make_type::<A>();
            let value = Value::unnamed_composite(vec![Value::from_bytes(0u32.to_le_bytes())]);

            value
                .encode_as_type_to(ty_id, &types, &mut buf)
                .expect_err("We tried encoding a Value of the wrong shape so this should fail");
        })
    }
}
