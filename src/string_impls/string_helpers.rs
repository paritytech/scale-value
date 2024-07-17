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

/// Return the escape code for a given char, or None
/// if there is no escape code for it.
pub fn to_escape_code(c: char) -> Option<char> {
    let escaped = match c {
        '\n' => 'n',
        '\t' => 't',
        '"' => '"',
        '\'' => '\'',
        '\r' => 'r',
        '\\' => '\\',
        '\0' => '0',
        _ => return None,
    };
    Some(escaped)
}

/// Given some escape code (char following a '\'), return the
/// unescaped char that it represents, or None if it is not a
/// valid escape code.
#[cfg(feature = "from-string")]
pub fn from_escape_code(c: char) -> Option<char> {
    let unescaped = match c {
        'n' => '\n',
        't' => '\t',
        '"' => '"',
        '\'' => '\'',
        'r' => '\r',
        '\\' => '\\',
        '0' => '\0',
        _ => return None,
    };
    Some(unescaped)
}

/// We write a Value to some writer via this type, which controls
/// the level of indentation and whether to format in a compact or
/// pretty style.
pub(crate) struct Formatter<W, T> {
    writer: W,
    style: FormatStyle,
    print_context: Option<Box<dyn Fn(&T, &mut W) -> core::fmt::Result>>,
}

impl<W: core::fmt::Write, T> Formatter<W, T> {
    pub(crate) fn compact(writer: W) -> Self {
        Formatter { writer, style: FormatStyle::Compact, print_context: None }
    }
    pub(crate) fn spaced(writer: W) -> Self {
        Formatter { writer, style: FormatStyle::Indented(0), print_context: None }
    }
    pub(crate) fn context<F: Fn(&T, &mut W) -> core::fmt::Result + 'static>(mut self, f: F) -> Self {
        self.print_context = Some(Box::new(f));
        self
    }
    pub(crate) fn indent_by(&mut self, indent: usize) {
        self.style = match &self.style {
            FormatStyle::Compact => FormatStyle::Compact,
            FormatStyle::Indented(n) => FormatStyle::Indented(n + indent),
        };
    }
    pub(crate) fn unindent_by(&mut self, indent: usize) {
        self.style = match &self.style {
            FormatStyle::Compact => FormatStyle::Compact,
            FormatStyle::Indented(n) => FormatStyle::Indented(n.saturating_sub(indent)),
        };
    }
    pub(crate) fn newline_or_nothing(&mut self) -> core::fmt::Result {
        match self.style {
            FormatStyle::Compact => Ok(()),
            FormatStyle::Indented(n) => write_newline(&mut self.writer, n),
        }
    }
    pub(crate) fn newline_or_space(&mut self) -> core::fmt::Result {
        match self.style {
            FormatStyle::Compact => self.writer.write_char(' '),
            FormatStyle::Indented(n) => write_newline(&mut self.writer, n),
        }
    }
    pub(crate) fn should_print_context(&self) -> bool {
        self.print_context.is_some()
    }
    pub(crate) fn print_context(&mut self, ctx: &T) -> core::fmt::Result {
        if let Some(f) = &self.print_context {
            f(ctx, &mut self.writer)
        } else {
            Ok(())
        }
    }
}

impl<W: core::fmt::Write, T> core::fmt::Write for Formatter<W, T> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        // For now, we don't apply any formatting to this, and expect
        // things to manually call `newline` etc to have formatting.
        self.writer.write_str(s)
    }
}

/// this defines whether the above formatter will write "newlines" in a
/// compact style or more spaced out with indentation.
enum FormatStyle {
    Indented(usize),
    Compact,
}

pub fn write_newline(writer: &mut impl core::fmt::Write, indent: usize) -> core::fmt::Result {
    writer.write_char('\n')?;
    for _ in 0..indent {
        writer.write_char(' ')?;
    }
    Ok(())
}
