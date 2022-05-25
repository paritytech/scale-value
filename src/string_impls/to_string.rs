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

use std::fmt::{Display, Write};
use crate::value::{
    Value,
    ValueDef,
    Primitive,
    Composite,
    Variant,
    BitSequence,
};
use super::string_helpers;

impl <T> Display for Value<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
    }
}

impl <T> Display for ValueDef<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
       match self {
            ValueDef::Composite(c) => c.fmt(f),
            ValueDef::Variant(v) => v.fmt(f),
            ValueDef::BitSequence(b) => fmt_bitsequence(b, f),
            ValueDef::Primitive(p) => p.fmt(f),
        }
    }
}

impl <T> Display for Composite<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Composite::Named(vals) => {
                f.write_str("{ ")?;
                for (name, val) in vals {
                    if is_ident(name) {
                        f.write_str(name)?;
                    } else {
                        fmt_string(name, f)?;
                    }
                    f.write_str(": ")?;
                    val.fmt(f)?;
                }
                f.write_str(" }")?;
            },
            Composite::Unnamed(vals) => {
                f.write_char('(')?;
                for val in vals {
                    val.fmt(f)?;
                }
                f.write_char(')')?;
            }
        }
        Ok(())
    }
}

impl <T> Display for Variant<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !is_ident(&self.name) {
            // Variant names can, in theory, not be valid idents, but in that
            // case they cannot be printed properly, since we expect idents
            // when parsing.
            return Err(std::fmt::Error);
        }
        f.write_str(&self.name)?;
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
            },
            None => f.write_char(char)?
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
        },
        None => f.write_char(c)?
    }
    f.write_char('\'')
}

fn fmt_bitsequence(b: &BitSequence, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_char('<')?;
    for bit in b.iter() {
        match bit.as_ref() {
            true => f.write_char('1')?,
            false => f.write_char('0')?,
        }
    }
    f.write_char('>')
}

/// Is the string provided a valid ident (as per from_string::parse_ident).
fn is_ident(s: &str) -> bool {
    for (idx, c) in s.chars().enumerate() {
        if idx == 0 && !c.is_alphabetic() {
            return false
        } else if !c.is_alphanumeric() || c != '_' {
            return false
        }
    }
    true
}
