// Copyright 2022 Parity Technologies (UK) Ltd.
// This file is part of scale-value.
//
// scale-value is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// scale-value is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with scale-value.  If not, see <http://www.gnu.org/licenses/>.

mod bitvec_helpers;
mod deserialize;
mod deserializer;
mod serialize;
mod serializer;

/// An opaque error that is returned if we cannot deserialize the [`Value`] type.
pub use deserializer::Error as DeserializeError;

pub use serializer::{Error as SerializeError, ValueSerializer};

