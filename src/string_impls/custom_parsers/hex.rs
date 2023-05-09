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

use crate::{
    stringify::{ParseError, ParseErrorKind},
    Value,
};

/// Attempt to parse a hex string into a [`Value<()>`] (or more specifically,
/// an unnamed composite).
///
/// - Returns an error if we see a leading `0x` and then see invalid hex
///   characters after this.
/// - Returns `None` if no `0x` is seen first.
/// - Returns `Some(value)` if parsing was successful. In this case, the string
///   reference given is wound forwards to consume what was parsed.
pub fn parse_hex(s: &mut &str) -> Option<Result<Value<()>, ParseError>> {
    let bytes = s.as_bytes();

    // Look for leading "0x"; None if this obviously isn't hex.
    if bytes[0] != b'0' || bytes[1] != b'x' {
        return None;
    }

    let mut composite_values = vec![];

    // find all valid hex chars after 0x:
    let mut idx = 2;
    let mut last_nibble = None;
    loop {
        // Break if we hit end of string.
        let Some(b) = bytes.get(idx) else {
            break;
        };

        // Break as soon as we hit some non-alphanumeric char.
        if !b.is_ascii_alphanumeric() {
            break;
        }

        // 4 bit number from hex char
        let hex_nibble = (b'a'..=b'f')
            .contains(b)
            .then(|| b - b'a' + 10)
            .or_else(|| (b'A'..=b'F').contains(b).then(|| b - b'A' + 10))
            .or_else(|| b.is_ascii_digit().then(|| b - b'0'));

        let Some(hex_nibble) = hex_nibble else {
            return Some(Err(ParseErrorKind::custom(ParseHexError::InvalidChar(*b as char)).at(idx)))
        };

        match last_nibble {
            None => {
                // The first of 2 chars; keep hold of:
                last_nibble = Some(hex_nibble)
            }
            Some(n) => {
                // The second; combine and push byte to output:
                let byte = n * 16 + hex_nibble;
                composite_values.push(Value::u128(byte as u128));
                last_nibble = None;
            }
        }

        idx += 1;
    }

    // We have leftovers; wrong length!
    if last_nibble.is_some() {
        return Some(Err(ParseErrorKind::custom(ParseHexError::WrongLength).between(0, idx)));
    }

    // Consume the "used" up bytes and return our Value.
    //
    // # Safety
    //
    // We have consumed only ASCII chars to get this far, so
    // we know the bytes following them make up a valid str.
    *s = unsafe { std::str::from_utf8_unchecked(&bytes[idx..]) };
    Some(Ok(Value::unnamed_composite(composite_values)))
}

#[derive(Debug, PartialEq, Clone, thiserror::Error)]
#[allow(missing_docs)]
pub enum ParseHexError {
    #[error("Invalid hex character: {0}")]
    InvalidChar(char),
    #[error("Hex string is the wrong length; should be an even length")]
    WrongLength,
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parses_same_as_hex_crate() {
        let expects = ["0x", "0x00", "0x000102030405060708090A0B", "0xDEADBEEF", "0x00BAB10C"];

        for input in expects {
            let expected_hex = hex::decode(input.trim_start_matches("0x")).expect("valid hex");
            let cursor = &mut &*input;
            let hex = parse_hex(cursor).expect("valid hex expected").expect("no error expected");

            assert_eq!(hex, Value::from_bytes(expected_hex), "values should match");
        }
    }

    #[test]
    fn consumes_parsed_hex() {
        let expects =
            [("0x foo", " foo"), ("0x00,bar", ",bar"), ("0x123456-2", "-2"), ("0xDEADBEEF ", " ")];

        for (input, expected_remaining) in expects {
            let cursor = &mut &*input;
            let _ = parse_hex(cursor).expect("valid hex expected").expect("no error expected");

            assert_eq!(*cursor, expected_remaining);
        }
    }

    #[test]
    fn err_wrong_length() {
        let expects = ["0x1", "0x123"];

        for input in expects {
            let cursor = &mut &*input;
            let err =
                parse_hex(cursor).expect("some result expected").expect_err("an error is expected");

            assert_eq!(err.start_loc, 0);
            assert_eq!(err.end_loc, Some(input.len()));

            let ParseErrorKind::Custom(err) = err.err else {
                panic!("expected custom error")
            };

            let concrete_err: Box<ParseHexError> = err.downcast().unwrap();
            assert_eq!(&*concrete_err, &ParseHexError::WrongLength);
            assert_eq!(input, *cursor);
        }
    }

    #[test]
    fn err_invalid_char() {
        let expects = [("0x12345x", 'x', 7), ("0x123h4", 'h', 5), ("0xG23h4", 'G', 2)];

        for (input, bad_char, pos) in expects {
            let cursor = &mut &*input;
            let err =
                parse_hex(cursor).expect("some result expected").expect_err("an error is expected");

            assert_eq!(err.start_loc, pos);
            assert!(err.end_loc.is_none());

            let ParseErrorKind::Custom(err) = err.err else {
                panic!("expected custom error")
            };

            let concrete_err: Box<ParseHexError> = err.downcast().unwrap();
            assert_eq!(&*concrete_err, &ParseHexError::InvalidChar(bad_char));
            assert_eq!(input, *cursor);
        }
    }
}
