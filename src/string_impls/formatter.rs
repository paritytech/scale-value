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
use crate::Value;

/// Options to configure a [`Formatter`].
pub(crate) struct FormatOpts<W, T> {
    style: FormatStyle,
    indent_by: String,
    custom_formatter: Option<Box<dyn Fn(&Value<T>, &mut W) -> Option<core::fmt::Result>>>,
    print_context: Option<Box<dyn Fn(&T, &mut W) -> core::fmt::Result>>,
}

impl<W: core::fmt::Write, T> FormatOpts<W, T> {
    pub(crate) fn new() -> Self {
        FormatOpts {
            style: FormatStyle::Compact,
            indent_by: "  ".to_owned(),
            custom_formatter: None,
            print_context: None,
        }
    }
    pub(crate) fn compact(mut self) -> Self {
        self.style = FormatStyle::Compact;
        self
    }
    pub(crate) fn spaced(mut self) -> Self {
        self.style = FormatStyle::Indented(0);
        self
    }
    pub(crate) fn context<F: Fn(&T, &mut W) -> core::fmt::Result + 'static>(
        mut self,
        f: F,
    ) -> Self {
        self.print_context = Some(Box::new(f));
        self
    }
    pub(crate) fn custom_formatter<
        F: Fn(&Value<T>, &mut W) -> Option<core::fmt::Result> + 'static,
    >(
        mut self,
        f: F,
    ) -> Self {
        self.custom_formatter = Some(Box::new(f));
        self
    }
}

/// We write a Value to some writer via this type, which controls
/// the level of indentation and whether to format in a compact or
/// pretty style.
pub(crate) struct Formatter<W, T> {
    writer: W,
    opts: FormatOpts<W, T>,
}

impl<W: core::fmt::Write, T> Formatter<W, T> {
    pub(crate) fn new(writer: W, opts: FormatOpts<W, T>) -> Self {
        Formatter { writer, opts }
    }
    pub(crate) fn indent_step(&mut self) {
        self.opts.style = match &self.opts.style {
            FormatStyle::Compact => FormatStyle::Compact,
            FormatStyle::Indented(n) => FormatStyle::Indented(n + 1),
        };
    }
    pub(crate) fn unindent_step(&mut self) {
        self.opts.style = match &self.opts.style {
            FormatStyle::Compact => FormatStyle::Compact,
            FormatStyle::Indented(n) => FormatStyle::Indented(n.saturating_sub(1)),
        };
    }
    pub(crate) fn newline_or_nothing(&mut self) -> core::fmt::Result {
        match self.opts.style {
            FormatStyle::Compact => Ok(()),
            FormatStyle::Indented(n) => write_newline(&mut self.writer, &self.opts.indent_by, n),
        }
    }
    pub(crate) fn newline_or_space(&mut self) -> core::fmt::Result {
        match self.opts.style {
            FormatStyle::Compact => self.writer.write_char(' '),
            FormatStyle::Indented(n) => write_newline(&mut self.writer, &self.opts.indent_by, n),
        }
    }
    pub(crate) fn should_print_context(&self) -> bool {
        self.opts.print_context.is_some()
    }
    pub(crate) fn print_context(&mut self, ctx: &T) -> core::fmt::Result {
        if let Some(f) = &self.opts.print_context {
            f(ctx, &mut self.writer)
        } else {
            Ok(())
        }
    }
    pub(crate) fn print_custom_format(&mut self, value: &Value<T>) -> Option<core::fmt::Result> {
        if let Some(f) = &self.opts.custom_formatter {
            f(value, &mut self.writer)
        } else {
            None
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
