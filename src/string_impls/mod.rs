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

#[cfg(feature = "from_string")]
mod custom_parsers;
#[cfg(feature = "from_string")]
mod from_string;

mod string_helpers;
mod to_string;

#[cfg(feature = "from_string")]
pub use from_string::{
    FromStrBuilder, ParseBitSequenceError, ParseCharError, ParseComplexError, ParseCustomError,
    ParseError, ParseErrorKind, ParseNumberError, ParseStringError,
};

#[cfg(feature = "from_string")]
pub use custom_parsers::{parse_hex, parse_ss58, ParseHexError};
