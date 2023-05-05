// Copyright (C) 2022 Parity Technologies (UK) Ltd. (admin@parity.io)
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

use super::string_helpers;
use crate::value::{BitSequence, Composite, Primitive, Value, ValueDef, Variant};
use std::fmt::{Display, Write};

impl<T> Display for Value<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T> Display for ValueDef<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueDef::Composite(c) => c.fmt(f),
            ValueDef::Variant(v) => v.fmt(f),
            ValueDef::BitSequence(b) => fmt_bitsequence(b, f),
            ValueDef::Primitive(p) => p.fmt(f),
        }
    }
}

impl<T> Display for Composite<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Composite::Named(vals) => {
                f.write_str("{ ")?;
                for (idx, (name, val)) in vals.iter().enumerate() {
                    if idx != 0 {
                        f.write_str(", ")?;
                    }
                    if is_ident(name) {
                        f.write_str(name)?;
                    } else {
                        fmt_string(name, f)?;
                    }
                    f.write_str(": ")?;
                    val.fmt(f)?;
                }
                f.write_str(" }")?;
            }
            Composite::Unnamed(vals) => {
                f.write_char('(')?;
                for (idx, val) in vals.iter().enumerate() {
                    if idx != 0 {
                        f.write_str(", ")?;
                    }
                    val.fmt(f)?;
                }
                f.write_char(')')?;
            }
        }
        Ok(())
    }
}

impl<T> Display for Variant<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if is_ident(&self.name) {
            f.write_str(&self.name)?;
        } else {
            // If the variant name isn't a valid ident, we parse it into
            // a special "v" prefixed string to allow arbitrary content while
            // keeping it easy to parse variant names with minimal lookahead.
            // Most use cases should never see or care about this.
            f.write_char('v')?;
            fmt_string(&self.name, f)?;
        }
        f.write_char(' ')?;
        self.values.fmt(f)
    }
}

impl Display for Primitive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Primitive::Bool(true) => f.write_str("true"),
            Primitive::Bool(false) => f.write_str("false"),
            Primitive::Char(c) => fmt_char(*c, f),
            Primitive::I128(n) => n.fmt(f),
            Primitive::U128(n) => n.fmt(f),
            Primitive::String(s) => fmt_string(s, f),
            // We don't currently have a sane way to parse into these or
            // format out of them:
            Primitive::U256(_) | Primitive::I256(_) => Err(std::fmt::Error),
        }
    }
}

fn fmt_string(s: &str, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_char('"')?;
    for char in s.chars() {
        match string_helpers::to_escape_code(char) {
            Some(escaped) => {
                f.write_char('\\')?;
                f.write_char(escaped)?
            }
            None => f.write_char(char)?,
        }
    }
    f.write_char('"')
}

fn fmt_char(c: char, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_char('\'')?;
    match string_helpers::to_escape_code(c) {
        Some(escaped) => {
            f.write_char('\\')?;
            f.write_char(escaped)?
        }
        None => f.write_char(c)?,
    }
    f.write_char('\'')
}

fn fmt_bitsequence(b: &BitSequence, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_char('<')?;
    for bit in b.iter() {
        match bit {
            true => f.write_char('1')?,
            false => f.write_char('0')?,
        }
    }
    f.write_char('>')
}

/// Is the string provided a valid ident (as per from_string::parse_ident).
fn is_ident(s: &str) -> bool {
    let mut chars = s.chars();

    // First char must be a letter (false if no chars)
    let Some(fst) = chars.next() else { return false };
    if !fst.is_alphabetic() {
        return false;
    }

    // Other chars must be letter, number or underscore
    for c in chars {
        if !c.is_alphanumeric() && c != '_' {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn outputs_expected_string() {
        let expected = [
            (Value::bool(true), "true"),
            (Value::bool(false), "false"),
            (Value::char('a'), "'a'"),
            (Value::u128(123), "123"),
            (Value::unnamed_composite([Value::bool(true), Value::string("hi")]), r#"(true, "hi")"#),
            (
                Value::named_composite([
                    ("hi there", Value::bool(true)),
                    ("other", Value::string("hi")),
                ]),
                r#"{ "hi there": true, other: "hi" }"#,
            ),
            (
                Value::named_variant(
                    "Foo",
                    [
                        (
                            "ns",
                            Value::unnamed_composite([
                                Value::u128(1),
                                Value::u128(2),
                                Value::u128(3),
                            ]),
                        ),
                        ("other", Value::char('a')),
                    ],
                ),
                "Foo { ns: (1, 2, 3), other: 'a' }",
            ),
        ];

        for (value, expected_str) in expected {
            assert_eq!(&value.to_string(), expected_str);
        }
    }

    #[test]
    fn pretty_variant_ident_used_when_possible() {
        let expected = [
            ("simpleIdent", true),
            ("S", true),
            ("S123", true),
            ("S123_", true),
            ("", false),
            ("complex ident", false),
            ("0Something", false),
            ("_Something", false),
        ];

        for (ident, should_be_simple) in expected {
            let v = Value::variant(ident, Composite::Named(vec![]));
            let s = v.to_string();
            assert_eq!(
                !s.trim().starts_with("v"),
                should_be_simple,
                "{s} should be simple: {should_be_simple}"
            );
        }
    }

    // These tests stringify and then parse from string, so need "from_string" feature.
    #[cfg(feature = "from_string")]
    mod from_to {
        use super::*;

        fn assert_from_to<T: std::fmt::Debug + PartialEq>(val: Value<T>) {
            let s = val.to_string();
            match crate::stringify::from_str(&s) {
                (Err(e), _) => {
                    panic!("'{s}' cannot be parsed back into the value {val:?}: {e}");
                }
                (Ok(new_val), rest) => {
                    assert_eq!(
                        val.remove_context(),
                        new_val,
                        "value should be the same after parsing to/from a string"
                    );
                    assert_eq!(
                        rest.len(),
                        0,
                        "there should be no unparsed string but got '{rest}'"
                    );
                }
            }
        }

        #[test]
        fn primitives() {
            assert_from_to(Value::bool(true));
            assert_from_to(Value::bool(false));

            assert_from_to(Value::char('\n'));
            assert_from_to(Value::char('😀'));
            assert_from_to(Value::char('a'));
            assert_from_to(Value::char('\0'));
            assert_from_to(Value::char('\t'));

            assert_from_to(Value::i128(-123_456));
            assert_from_to(Value::u128(0));
            assert_from_to(Value::u128(123456));

            assert_from_to(Value::string("hello \"you\",\n\n\t How are you??"));
            assert_from_to(Value::string(""));
        }

        #[test]
        fn composites() {
            assert_from_to(Value::named_composite([
                ("foo", Value::u128(12345)),
                ("bar", Value::bool(true)),
                ("a \"weird\" name", Value::string("Woop!")),
            ]));
            assert_from_to(Value::unnamed_composite([
                Value::u128(12345),
                Value::bool(true),
                Value::string("Woop!"),
            ]));
        }

        #[test]
        fn variants() {
            assert_from_to(Value::named_variant(
                "A weird variant name",
                [
                    ("foo", Value::u128(12345)),
                    ("bar", Value::bool(true)),
                    ("a \"weird\" name", Value::string("Woop!")),
                ],
            ));
            assert_from_to(Value::unnamed_variant(
                "MyVariant",
                [Value::u128(12345), Value::bool(true), Value::string("Woop!")],
            ));
        }

        #[test]
        fn bit_sequences() {
            use scale_bits::bits;
            assert_from_to(Value::bit_sequence(bits![0, 1, 1, 0, 1, 1, 0]));
            assert_from_to(Value::bit_sequence(bits![]));
        }
    }
}
