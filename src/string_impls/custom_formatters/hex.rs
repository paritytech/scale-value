// Copyright (C) 2022-2024 Parity Technologies (UK) Ltd. (admin@parity.io)
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
use crate::{Composite, Primitive, Value, ValueDef};
use core::fmt::Write;

/// This can be used alongside [`crate::stringify::ToWriterBuilder::custom_formatter()`] (which
/// itself is constructed via [`crate::stringify::to_writer_custom()`]). It will format as a hex
/// string any unnamed composite whose values are all primitives in the range 0-255 inclusive.
///
/// # Example
///
/// ```rust
/// use scale_value::{value,Value};
/// use scale_value::stringify::{to_writer_custom, custom_formatters::format_hex};
///
/// let val = value!({
///     foo: (1u64,2u64,3u64,4u64,5u64),
///     bar: (1000u64, 10u64)
/// });
///
/// let mut s = String::new();
///
/// to_writer_custom()
///     .custom_formatter(|v, w| format_hex(v, w))
///     .write(&val, &mut s)
///     .unwrap();
///
/// assert_eq!(s, r#"{ foo: 0x0102030405, bar: (1000, 10) }"#);
/// ```
pub fn format_hex<T, W: Write>(
    value: &Value<T>,
    writer: W,
) -> Option<core::fmt::Result> {
    // Print unnamed sequences of u8s as hex strings; ignore anything else.
    if let ValueDef::Composite(Composite::Unnamed(vals)) = &value.value {
        for val in vals {
            if !matches!(val.value, ValueDef::Primitive(Primitive::U128(n)) if n < 256) {
                return None;
            }
        }
        Some(value_to_hex(vals, writer))
    } else {
        None
    }
}

// Just to avoid needing to import the `hex` dependency just for this.
fn value_to_hex<T, W: core::fmt::Write>(vals: &Vec<Value<T>>, mut writer: W) -> core::fmt::Result {
    writer.write_str("0x")?;
    for val in vals {
        if let ValueDef::Primitive(Primitive::U128(n)) = &val.value {
            let n = *n as u8;
            writer.write_char(u4_to_hex(n >> 4))?;
            writer.write_char(u4_to_hex(n & 0b00001111))?;
        }
    }
    Ok(())
}

fn u4_to_hex(n: u8) -> char {
    static HEX: [char; 16] =
        ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'];
    *HEX.get(n as usize).expect("Expected a u4 (value between 0..=15")
}


#[cfg(test)]
mod test {
    use super::*;
    use crate::value;

    #[test]
    fn test_value_to_hex() {
        let mut s = String::new();
        format_hex(&value! {(0usize,230usize,255usize,15usize,12usize,4usize)}, &mut s)
            .expect("decided not to convert to hex")
            .expect("can't write to writer without issues");

        assert_eq!(s, "0x00E6FF0F0C04");
    }

    #[test]
    fn test_value_not_to_hex() {
        let mut s = String::new();
        // 256 is too big to be a u8, so this value isn't valid hex.
        assert_eq!(format_hex(&value! {(0usize,230usize,256usize)}, &mut s), None);
    }
}