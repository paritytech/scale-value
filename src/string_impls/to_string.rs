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

use super::string_helpers;
use crate::prelude::*;
use crate::value_type::{BitSequence, Composite, Primitive, Value, ValueDef, Variant};
use core::fmt::{Display, Write};

/// A struct which will try to format a [`Value`] and write the output to a writer.
/// This can be configured with custom parsers to extend how to write out the value.
pub struct ToWriterBuilder<T, W> {
    style: FormatStyle,
    custom_formatters: Vec<CustomFormatter<T, W>>,
    indent_by: String,
    print_context: Option<ContextPrinter<T, W>>,
}

type CustomFormatter<T, W> = Box<dyn Fn(&Value<T>, &mut W) -> Option<core::fmt::Result> + 'static>;
type ContextPrinter<T, W> = Box<dyn Fn(&T, &mut W) -> core::fmt::Result + 'static>;

impl<T, W: core::fmt::Write> ToWriterBuilder<T, W> {
    pub(crate) fn new() -> Self {
        ToWriterBuilder {
            style: FormatStyle::Compact,
            custom_formatters: Vec::new(),
            indent_by: "  ".to_owned(),
            print_context: None,
        }
    }

    /// Write the [`crate::Value`] to a compact string.
    ///
    /// # Example
    ///
    /// ```rust
    /// use scale_value::{value,Value};
    /// use scale_value::stringify::to_writer_custom;
    ///
    /// let val = value!({
    ///     foo: (1,2,3,4,5),
    ///     bar: true
    /// });
    ///
    /// let mut s = String::new();
    ///
    /// to_writer_custom()
    ///     .write(&val, &mut s)
    ///     .unwrap();
    ///
    /// assert_eq!(s, r#"{ foo: (1, 2, 3, 4, 5), bar: true }"#);
    /// ```
    pub fn compact(mut self) -> Self {
        self.style = FormatStyle::Compact;
        self
    }

    /// Write the [`crate::Value`] to a pretty spaced string.
    ///
    /// # Example
    ///
    /// ```rust
    /// use scale_value::{value,Value};
    /// use scale_value::stringify::to_writer_custom;
    ///
    /// let val = value!({
    ///     foo: (1,2,3,4,5),
    ///     bar: true
    /// });
    ///
    /// let mut s = String::new();
    ///
    /// to_writer_custom()
    ///     .spaced()
    ///     .write(&val, &mut s)
    ///     .unwrap();
    ///
    /// assert_eq!(s, r#"{
    ///   foo: (
    ///     1,
    ///     2,
    ///     3,
    ///     4,
    ///     5
    ///   ),
    ///   bar: true
    /// }"#);
    /// ```
    pub fn spaced(mut self) -> Self {
        self.style = FormatStyle::Indented(0);
        self
    }

    /// Write the context contained in each value out, too. This is prepended to
    /// each value within angle brackets (`<` and `>`).
    ///
    /// # Warning
    ///
    /// When this is used, the resulting outpuot cannot then be parsed back into [`Value`]
    /// (in part since the user can output arbitrary content for the context). Nevertheless,
    /// writing the context can be useful for debugging errors and providing more verbose output.
    ///
    ///
    pub fn write_context<F: Fn(&T, &mut W) -> core::fmt::Result + 'static>(mut self, f: F) -> Self {
        self.print_context = Some(Box::new(f));
        self
    }

    /// Add a custom formatter (for example, [`crate::stringify::custom_formatters::format_hex`]).
    /// Custom formatters have the opportunity to read the value at each stage, and:
    ///
    /// - Should output `None` if they do not wish to override the standard formatting (in this case,
    /// they should also avoid writing anything to the provided writer).
    /// - Should output `Some(core::fmt::Result)` if they decide to override the default formatting at
    /// this point.
    ///
    /// Custom formatters are tried in the order that they are added here, and when one decides
    /// to write output (signalled by returning `Some(..)`), no others will be tried. Thus, the order
    /// in which they are added is important.
    pub fn custom_formatter<F: Fn(&Value<T>, &mut W) -> Option<core::fmt::Result> + 'static>(
        mut self,
        f: F,
    ) -> Self {
        self.custom_formatters.push(Box::new(f));
        self
    }

    /// Write some value to the provided writer, using the currently configured options.
    pub fn write(&self, value: &Value<T>, writer: W) -> core::fmt::Result {
        let mut formatter = self.as_formatter(writer);
        fmt_value(value, &mut formatter)
    }

    fn as_formatter(&self, writer: W) -> Formatter<'_, T, W> {
        Formatter {
            writer,
            style: self.style,
            custom_formatters: &self.custom_formatters,
            indent_by: &self.indent_by,
            print_context: &self.print_context,
        }
    }
}

struct Formatter<'a, T, W> {
    writer: W,
    style: FormatStyle,
    custom_formatters: &'a [CustomFormatter<T, W>],
    indent_by: &'a str,
    print_context: &'a Option<ContextPrinter<T, W>>,
}

impl<'a, T, W: core::fmt::Write> Formatter<'a, T, W> {
    fn indent_step(&mut self) {
        self.style = match &self.style {
            FormatStyle::Compact => FormatStyle::Compact,
            FormatStyle::Indented(n) => FormatStyle::Indented(n + 1),
        };
    }
    fn unindent_step(&mut self) {
        self.style = match &self.style {
            FormatStyle::Compact => FormatStyle::Compact,
            FormatStyle::Indented(n) => FormatStyle::Indented(n.saturating_sub(1)),
        };
    }
    fn newline_or_nothing(&mut self) -> core::fmt::Result {
        match self.style {
            FormatStyle::Compact => Ok(()),
            FormatStyle::Indented(n) => write_newline(&mut self.writer, &self.indent_by, n),
        }
    }
    fn newline_or_space(&mut self) -> core::fmt::Result {
        match self.style {
            FormatStyle::Compact => self.writer.write_char(' '),
            FormatStyle::Indented(n) => write_newline(&mut self.writer, &self.indent_by, n),
        }
    }
    fn should_print_context(&self) -> bool {
        self.print_context.is_some()
    }
    fn print_context(&mut self, ctx: &T) -> core::fmt::Result {
        if let Some(f) = &self.print_context {
            f(ctx, &mut self.writer)
        } else {
            Ok(())
        }
    }
    fn print_custom_format(&mut self, value: &Value<T>) -> Option<core::fmt::Result> {
        for formatter in self.custom_formatters {
            // Try each formatter until one "accepts" the value, and then return the result from that.
            if let Some(res) = formatter(value, &mut self.writer) {
                return Some(res);
            }
        }
        None
    }
}

impl<'a, T, W: core::fmt::Write> core::fmt::Write for Formatter<'a, T, W> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        // For now, we don't apply any formatting to this, and expect
        // things to manually call `newline` etc to have formatting.
        self.writer.write_str(s)
    }
}

fn write_newline(
    writer: &mut impl core::fmt::Write,
    indent_str: &str,
    indent: usize,
) -> core::fmt::Result {
    writer.write_char('\n')?;
    for _ in 0..indent {
        writer.write_str(indent_str)?;
    }
    Ok(())
}

/// this defines whether the above [`ToStrBuilder`] will write "newlines" in a
/// compact style or more spaced out with indentation.
#[derive(Clone, Copy)]
enum FormatStyle {
    Indented(usize),
    Compact,
}

// Make a default formatter to use in the Display impls.
fn default_builder<T, W: core::fmt::Write>(alternate: bool) -> ToWriterBuilder<T, W> {
    let mut builder = ToWriterBuilder::new();
    if alternate {
        builder = builder.spaced();
    }
    builder
}

impl<T> Display for Value<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T> Display for ValueDef<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let builder = default_builder(f.alternate());
        fmt_valuedef(self, &mut builder.as_formatter(f))
    }
}

impl<T> Display for Composite<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let builder = default_builder(f.alternate());
        fmt_composite(self, &mut builder.as_formatter(f))
    }
}

impl<T> Display for Variant<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let builder = default_builder(f.alternate());
        fmt_variant(self, &mut builder.as_formatter(f))
    }
}

impl Display for Primitive {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let builder = default_builder::<(), _>(f.alternate());
        fmt_primitive(self, &mut builder.as_formatter(f))
    }
}

fn fmt_value<T, W: core::fmt::Write>(v: &Value<T>, f: &mut Formatter<T, W>) -> core::fmt::Result {
    if f.should_print_context() {
        f.write_char('<')?;
        f.print_context(&v.context)?;
        f.write_str("> ")?;
    }

    // Print custom output if there is some, else fall back to the normal logic.
    f.print_custom_format(v).unwrap_or_else(|| fmt_valuedef(&v.value, f))
}

fn fmt_valuedef<T, W: core::fmt::Write>(
    v: &ValueDef<T>,
    f: &mut Formatter<T, W>,
) -> core::fmt::Result {
    match v {
        ValueDef::Composite(c) => fmt_composite(c, f),
        ValueDef::Variant(v) => fmt_variant(v, f),
        ValueDef::BitSequence(b) => fmt_bitsequence(b, f),
        ValueDef::Primitive(p) => fmt_primitive(p, f),
    }
}

fn fmt_variant<T, W: core::fmt::Write>(
    v: &Variant<T>,
    f: &mut Formatter<T, W>,
) -> core::fmt::Result {
    if is_ident(&v.name) {
        f.write_str(&v.name)?;
    } else {
        // If the variant name isn't a valid ident, we parse it into
        // a special "v" prefixed string to allow arbitrary content while
        // keeping it easy to parse variant names with minimal lookahead.
        // Most use cases should never see or care about this.
        f.write_char('v')?;
        fmt_string(&v.name, f)?;
    }
    f.write_char(' ')?;
    fmt_composite(&v.values, f)
}

fn fmt_composite<T, W: core::fmt::Write>(
    v: &Composite<T>,
    f: &mut Formatter<T, W>,
) -> core::fmt::Result {
    match v {
        Composite::Named(vals) => {
            if vals.is_empty() {
                f.write_str("{}")?;
            } else {
                f.write_str("{")?;
                f.indent_step();
                f.newline_or_space()?;
                for (idx, (name, val)) in vals.iter().enumerate() {
                    if idx != 0 {
                        f.write_str(",")?;
                        f.newline_or_space()?;
                    }
                    if is_ident(name) {
                        f.write_str(name)?;
                    } else {
                        fmt_string(name, f)?;
                    }
                    f.write_str(": ")?;
                    fmt_value(val, f)?;
                }
                f.unindent_step();
                f.newline_or_space()?;
                f.write_str("}")?;
            }
        }
        Composite::Unnamed(vals) => {
            if vals.is_empty() {
                f.write_str("()")?;
            } else {
                f.write_char('(')?;
                f.indent_step();
                f.newline_or_nothing()?;
                for (idx, val) in vals.iter().enumerate() {
                    if idx != 0 {
                        f.write_str(",")?;
                        f.newline_or_space()?;
                    }
                    fmt_value(val, f)?;
                }
                f.unindent_step();
                f.newline_or_nothing()?;
                f.write_char(')')?;
            }
        }
    }
    Ok(())
}

fn fmt_primitive<T, W: core::fmt::Write>(
    p: &Primitive,
    f: &mut Formatter<T, W>,
) -> core::fmt::Result {
    match p {
        Primitive::Bool(true) => f.write_str("true"),
        Primitive::Bool(false) => f.write_str("false"),
        Primitive::Char(c) => fmt_char(*c, f),
        Primitive::I128(n) => write!(f, "{n}"),
        Primitive::U128(n) => write!(f, "{n}"),
        Primitive::String(s) => fmt_string(s, f),
        // We don't currently have a sane way to parse into these or
        // format out of them:
        Primitive::U256(_) | Primitive::I256(_) => Err(core::fmt::Error),
    }
}

fn fmt_string<T, W: core::fmt::Write>(s: &str, f: &mut Formatter<T, W>) -> core::fmt::Result {
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

fn fmt_char<T, W: core::fmt::Write>(c: char, f: &mut Formatter<T, W>) -> core::fmt::Result {
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

fn fmt_bitsequence<T, W: core::fmt::Write>(
    b: &BitSequence,
    f: &mut Formatter<T, W>,
) -> core::fmt::Result {
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
    use crate::value;

    use super::*;

    #[test]
    fn outputs_expected_string() {
        let expected = [
            (Value::bool(true), "true"),
            (Value::bool(false), "false"),
            (Value::char('a'), "'a'"),
            (Value::u128(123), "123"),
            (value!((true, "hi")), r#"(true, "hi")"#),
            (
                Value::named_composite([
                    ("hi there", Value::bool(true)),
                    ("other", Value::string("hi")),
                ]),
                r#"{ "hi there": true, other: "hi" }"#,
            ),
            (value!(Foo { ns: (1u8, 2u8, 3u8), other: 'a' }), "Foo { ns: (1, 2, 3), other: 'a' }"),
        ];

        for (value, expected_str) in expected {
            assert_eq!(&value.to_string(), expected_str);
        }
    }

    #[test]
    fn expanded_output_works() {
        let v = value!({
            hello: true,
            empty: (),
            sequence: (1,2,3),
            variant: MyVariant (1,2,3),
            inner: {
                foo: "hello"
            }
        });

        //// The manual way to do this would be:
        // let mut s = String::new();
        // fmt_value(&v, &mut Formatter::spaced(&mut s)).unwrap();

        assert_eq!(
            format!("{v:#}"),
            "{
  hello: true,
  empty: (),
  sequence: (
    1,
    2,
    3
  ),
  variant: MyVariant (
    1,
    2,
    3
  ),
  inner: {
    foo: \"hello\"
  }
}"
        );
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
                !s.trim().starts_with('v'),
                should_be_simple,
                "{s} should be simple: {should_be_simple}"
            );
        }
    }

    // These tests stringify and then parse from string, so need "from-string" feature.
    #[cfg(feature = "from-string")]
    mod from_to {
        use super::*;

        fn assert_from_to<T: core::fmt::Debug + PartialEq>(val: Value<T>) {
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
            assert_from_to(value!(MyVariant(12345u32, true, "Woop!")));
        }

        #[test]
        fn bit_sequences() {
            use scale_bits::bits;
            assert_from_to(Value::bit_sequence(bits![0, 1, 1, 0, 1, 1, 0]));
            assert_from_to(Value::bit_sequence(bits![]));
        }
    }
}
