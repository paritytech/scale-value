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

use std::fmt::Display;

use super::ScaleTypeId;

/// This represents the ID of a type found in the metadata. A scale info type representation can
/// be converted into this, and we get this back directly when decoding types into Values.
#[derive(
	Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct TypeId(u32);

impl TypeId {
	/// Return the u32 ID expected by a PortableRegistry.
	pub(crate) fn id(self) -> u32 {
		self.0
	}
}

impl Display for TypeId {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}

impl From<ScaleTypeId> for TypeId {
	fn from(id: ScaleTypeId) -> Self {
		TypeId(id.id())
	}
}

impl From<&ScaleTypeId> for TypeId {
	fn from(id: &ScaleTypeId) -> Self {
		TypeId(id.id())
	}
}

impl From<&TypeId> for TypeId {
	fn from(id: &TypeId) -> Self {
		*id
	}
}

impl From<u32> for TypeId {
	fn from(id: u32) -> Self {
		TypeId(id)
	}
}
