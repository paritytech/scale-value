use core::fmt::Write;

use super::path::Path;
use crate::scale::DecodeError;
use crate::{Composite, Primitive, Value, ValueDef};

/// An error encountered when decoding some bytes using the [`crate::scale::tracing`] module.
#[derive(Clone, Debug)]
pub struct TraceDecodingError<Val> {
    inner: TraceDecodingErrorInner<Val>,
}

impl<Val> TraceDecodingError<Val> {
    pub(crate) fn map_decoded_so_far<NewVal>(
        self,
        f: impl FnOnce(Val) -> NewVal,
    ) -> TraceDecodingError<NewVal> {
        match self.inner {
            TraceDecodingErrorInner::FromDecodeError(e) => {
                TraceDecodingErrorInner::FromDecodeError(e).into()
            }
            TraceDecodingErrorInner::FromVisitor(e) => {
                TraceDecodingErrorInner::FromVisitor(VisitorError {
                    at: e.at,
                    decode_error: e.decode_error,
                    decoded_so_far: f(e.decoded_so_far),
                })
                .into()
            }
        }
    }
    pub(crate) fn with_outer_context<NewVal>(
        self,
        outer_path: impl FnOnce() -> Path,
        default_outer_value: impl FnOnce() -> NewVal,
        into_outer_value: impl FnOnce(Val) -> NewVal,
    ) -> TraceDecodingError<NewVal> {
        match self.inner {
            TraceDecodingErrorInner::FromDecodeError(e) => {
                TraceDecodingErrorInner::FromVisitor(VisitorError {
                    at: outer_path(),
                    decoded_so_far: default_outer_value(),
                    decode_error: e,
                })
                .into()
            }
            TraceDecodingErrorInner::FromVisitor(e) => {
                TraceDecodingErrorInner::FromVisitor(VisitorError {
                    at: e.at,
                    decoded_so_far: into_outer_value(e.decoded_so_far),
                    decode_error: e.decode_error,
                })
                .into()
            }
        }
    }
}

impl<Val> From<TraceDecodingErrorInner<Val>> for TraceDecodingError<Val> {
    fn from(value: TraceDecodingErrorInner<Val>) -> Self {
        TraceDecodingError { inner: value }
    }
}

#[derive(Clone, Debug)]
enum TraceDecodingErrorInner<Val> {
    FromDecodeError(DecodeError),
    FromVisitor(VisitorError<Val>),
}

#[derive(Clone, Debug)]
struct VisitorError<Val> {
    at: Path,
    decoded_so_far: Val,
    decode_error: DecodeError,
}

impl<Ctx: core::fmt::Debug> core::fmt::Display for TraceDecodingError<Value<Ctx>> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match &self.inner {
            TraceDecodingErrorInner::FromDecodeError(e) => {
                write!(f, "Error decoding value: {e}")
            }
            TraceDecodingErrorInner::FromVisitor(e) => {
                write!(
                    f,
                    "Error decoding value at {}: {}\nDecoded so far:\n\n",
                    e.at, e.decode_error,
                )?;
                display_value_with_typeid(f, &e.decoded_so_far)
            }
        }
    }
}

#[cfg(feature = "std")]
impl<Ctx: core::fmt::Debug> std::error::Error for TraceDecodingError<Value<Ctx>> {}

impl<TypeId> From<DecodeError> for TraceDecodingError<TypeId> {
    fn from(value: DecodeError) -> Self {
        TraceDecodingErrorInner::FromDecodeError(value).into()
    }
}

impl<TypeId> From<codec::Error> for TraceDecodingError<TypeId> {
    fn from(value: codec::Error) -> Self {
        TraceDecodingErrorInner::FromDecodeError(value.into()).into()
    }
}

fn display_value_with_typeid<Id: core::fmt::Debug>(
    f: &mut core::fmt::Formatter<'_>,
    value: &Value<Id>,
) -> core::fmt::Result {
    use crate::string_impls::{fmt_value, FormatOpts, Formatter};

    let format_opts = FormatOpts::new()
        .spaced()
        .context(|type_id, writer: &mut &mut core::fmt::Formatter| write!(writer, "{type_id:?}"))
        .custom_formatter(|value, writer| custom_hex_formatter(value, writer));
    let mut formatter = Formatter::new(f, format_opts);

    fmt_value(value, &mut formatter)
}

fn custom_hex_formatter<T, W: core::fmt::Write>(
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
        custom_hex_formatter(&value! {(0usize,230usize,255usize,15usize,12usize,4usize)}, &mut s)
            .expect("decided not to convert to hex")
            .expect("can't write to writer without issues");

        assert_eq!(s, "0x00E6FF0F0C04");
    }

    #[test]
    fn test_value_not_to_hex() {
        let mut s = String::new();
        // 256 is too big to be a u8, so this value isn't valid hex.
        assert_eq!(custom_hex_formatter(&value! {(0usize,230usize,256usize)}, &mut s), None);
    }
}
