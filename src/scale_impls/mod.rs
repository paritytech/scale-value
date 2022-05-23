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

mod bit_sequence;
mod decode;
mod encode;
mod type_id;

/// The portable version of [`scale_info::Type`]
type ScaleType = scale_info::Type<scale_info::form::PortableForm>;

/// The portable version of a [`scale_info`] type ID.
type ScaleTypeId = scale_info::interner::UntrackedSymbol<std::any::TypeId>; // equivalent to: <scale_info::form::PortableForm as scale_info::form::Form>::Type;

/// The portable version of [`scale_info::TypeDef`]
type ScaleTypeDef = scale_info::TypeDef<scale_info::form::PortableForm>;

pub use bit_sequence::BitSequenceError;
pub use decode::{decode_value_as_type, DecodeError};
pub use encode::{encode_value_as_type, EncodeError};

pub use type_id::TypeId;
