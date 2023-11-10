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
use crate::{stringify::ParseError, Value};

/// Attempt to parse an ss58 address into a [`Value<()>`] (or more specifically,
/// an unnamed composite wrapped in a newtype which represents an AccountId32).
///
/// - Returns `None` if we can't parse the address.
/// - Returns `Some(value)` if parsing was successful. In this case, the string
///   reference given is wound forwards to consume what was parsed.
pub fn parse_ss58(s: &mut &str) -> Option<Result<Value<()>, ParseError>> {
    let bytes = parse_ss58_bytes(s)?;
    Some(Ok(Value::from_bytes(bytes)))
}

fn parse_ss58_bytes(s: &mut &str) -> Option<Vec<u8>> {
    const CHECKSUM_LEN: usize = 2;

    // ss58 addresses are base58 encoded. Base58 is all alphanumeric chars
    // minus a few that look potentially similar. So, gather alphanumeric chars
    // first.
    let end_idx = s.find(|c: char| !c.is_ascii_alphanumeric()).unwrap_or(s.len());
    let maybe_ss58 = &s[0..end_idx];
    let rest = &s[end_idx..];

    if maybe_ss58.is_empty() {
        return None;
    }

    // Break early on obvious non-addresses that we want to parse elsewise, ie true, false or numbers.
    // This is mostly an optimisation but also eliminates some potential weird edge cases.
    if maybe_ss58 == "true"
        || maybe_ss58 == "false"
        || maybe_ss58.chars().all(|c: char| c.is_ascii_digit())
    {
        return None;
    }

    // If what we are parsing is a variant ident, a `{` or `(` will follow
    // (eg `Foo { hi: 1 }` or `Foo (1)`). In this case, don't try to parse
    // as an ss58 address, since it would definitely be wrong to do so.
    if rest.trim_start().starts_with(|c| c == '(' || c == '{') {
        return None;
    }

    // Attempt to base58-decode these chars.
    use base58::FromBase58;
    let Ok(bytes) = maybe_ss58.from_base58() else { return None };

    // decode length of address prefix.
    let prefix_len = match bytes.first() {
        Some(0..=63) => 1,
        Some(64..=127) => 2,
        _ => return None,
    };

    if bytes.len() < prefix_len + CHECKSUM_LEN {
        return None;
    }

    // The checksum is the last 2 bytes:
    let checksum_start_idx = bytes.len() - CHECKSUM_LEN;

    // Check that the checksum lines up with the rest of the address; if not,
    // this isn't a valid address.
    let hash = ss58hash(&bytes[0..checksum_start_idx]);
    let checksum = &hash[0..CHECKSUM_LEN];
    if &bytes[checksum_start_idx..] != checksum {
        return None;
    }

    // Everything checks out; wind the string cursor forwards and
    // return the bytes representing the address provided.
    *s = rest;
    Some(bytes[prefix_len..checksum_start_idx].to_vec())
}

fn ss58hash(data: &[u8]) -> Vec<u8> {
    use blake2::{Blake2b512, Digest};
    const PREFIX: &[u8] = b"SS58PRE";
    let mut ctx = Blake2b512::new();
    ctx.update(PREFIX);
    ctx.update(data);
    ctx.finalize().to_vec()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn can_parse_ss58_address() {
        // hex keys obtained via `subkey`, so we're comparing our decoding against that.
        // We simultaneously check that things after the address aren't consumed.
        let expected = [
            // Alice
            (
                "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY ",
                "d43593c715fdd31c61141abd04a99fd6822c8558854ccde39a5684e7a56da27d",
                " ",
            ),
            // Bob
            (
                "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty-100",
                "8eaf04151687736326c9fea17e25fc5287613693c912909cb226aa4794f26a48",
                "-100",
            ),
            // Charlie
            (
                "5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y,1,2,3",
                "90b5ab205c6974c9ea841be688864633dc9ca8a357843eeacf2314649965fe22",
                ",1,2,3",
            ),
            // Eve
            (
                "5HGjWAeFDfFCWPsjFQdVV2Msvz2XtMktvgocEZcCj68kUMaw }",
                "e659a7a1628cdd93febc04a4e0646ea20e9f5f0ce097d9a05290d4a9e054df4e",
                " }",
            ),
        ];

        for (ss58, expected_hex, expected_remaining) in expected {
            let cursor = &mut &*ss58;
            let bytes = parse_ss58_bytes(cursor).expect("address should parse OK");
            let expected = hex::decode(expected_hex).expect("hex should decode OK");

            assert_eq!(bytes, expected);
            assert_eq!(*cursor, expected_remaining);
        }
    }

    #[test]
    fn invalid_addresses_will_error() {
        let invalids = [
            // An otherwise valid address in a variant "ident" position will not parse:
            "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY { hi: 1 }",
            "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY     \t\n (1)",
            // Invalid addresses will return None:
            "Foo",
            "",
        ];

        for invalid in invalids {
            assert!(parse_ss58_bytes(&mut &*invalid).is_none());
        }
    }
}
