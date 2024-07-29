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

use super::path::Path;
use crate::prelude::*;
use crate::string_impls::format_hex;
use crate::scale::DecodeError;
use crate::Value;
use core::fmt::Write;

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
    crate::string_impls::ToWriterBuilder::new()
        .spaced()
        .write_context(|type_id, writer: &mut &mut core::fmt::Formatter| write!(writer, "{type_id:?}"))
        .custom_formatter(|value, writer| format_hex(value, writer))
        .write(value, f)
}

