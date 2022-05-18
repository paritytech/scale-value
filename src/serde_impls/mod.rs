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

mod bitvec_helpers;
mod deserialize;
mod deserializer;
mod serialize;
mod serializer;

/// An opaque error that is returned if we cannot deserialize the [`Value`] type.
pub use deserializer::Error as DeserializeError;

pub use serializer::{Error as SerializeError, ValueSerializer};

// test that we can serialize and deserialize a range of things to and from Value.
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
