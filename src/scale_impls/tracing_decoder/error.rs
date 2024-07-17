use super::path::Path;
use crate::scale::DecodeError;
use crate::{Composite, Value, ValueDef};

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

impl<Val: core::fmt::Display> core::fmt::Display for TraceDecodingError<Val> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match &self.inner {
            TraceDecodingErrorInner::FromDecodeError(e) => {
                write!(f, "Error decoding value: {e}")
            }
            TraceDecodingErrorInner::FromVisitor(e) => {
                write!(
                    f,
                    "Error decoding value at {}: {}\nDecoded so far: {}",
                    e.at, e.decode_error, e.decoded_so_far
                )
            }
        }
    }
}

#[cfg(feature = "std")]
impl<Val: core::fmt::Display + core::fmt::Debug> std::error::Error for TraceDecodingError<Val> {}

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

// fn display_value_with_typeid<Id: core::fmt::Debug>(f: &mut core::fmt::Formatter<'_>, value: &Value<Id>) -> core::fmt::Result {
//     let type_id = &value.context;
//     match &value.value {
//         ValueDef::Variant(var) => {
//             write!(f, "{} [{type_id}] ", var.name)?;
//             display_composite_with_typeid(f, &var.values)?;
//         }
//         ValueDef::Composite(_) => {

//         }
//         ValueDef::BitSequence(_) => {

//         }
//         ValueDef::Primitive(_) => {

//         }
//     }
//     Ok(())
// }

// fn display_composite_with_typeid<Id: core::fmt::Debug>(f: &mut core::fmt::Formatter<'_>, value: &Composite<Id>) -> core::fmt::Result {
//     match value {
//         Composite::Named(named) => {
//             write!(f, "{{\n");
//             for (key, val) in named {
//                 write!(f, "  {key}: ")?;
//                 display_value_with_typeid(f, val)?;
//                 write!("\n")
//             }
//         },
//         Composite::Unnamed(unnamed) => {

//         }
//     }

//     Ok(())
// }
