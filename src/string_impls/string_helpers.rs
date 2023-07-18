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
