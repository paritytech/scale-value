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

use super::ScaleTypeDef as TypeDef;
use scale_info::{form::PortableForm, PortableRegistry, TypeDefBitSequence, TypeDefPrimitive};

/// An error that can occur when we try to encode or decode to a SCALE bit sequence type.
#[derive(Debug, Clone, thiserror::Error, PartialEq)]
pub enum BitSequenceError {
	/// The registry did not contain the bit order type listed.
	#[error("Bit order type {0} not found in registry")]
	BitOrderTypeNotFound(u32),
	/// The registry did not contain the bit store type listed.
	#[error("Bit store type {0} not found in registry")]
	BitStoreTypeNotFound(u32),
	/// The bit order type did not have a valid identifier/name.
	#[error("Bit order cannot be identified")]
	NoBitOrderIdent,
	/// The bit store type that we found was not what we expected (a primitive u8/u16/u32/u64).
	#[error("Bit store type {0} is not supported")]
	StoreTypeNotSupported(String),
	/// The bit order type name that we found was not what we expected ("Lsb0" or "Msb0").
	#[error("Bit order type {0} is not supported")]
	OrderTypeNotSupported(String),
}

/// Obtain details about a bit sequence.
pub fn get_bitsequence_details(
	ty: &TypeDefBitSequence<PortableForm>,
	types: &PortableRegistry,
) -> Result<(BitOrderTy, BitStoreTy), BitSequenceError> {
	let bit_store_ty = ty.bit_store_type().id();
	let bit_order_ty = ty.bit_order_type().id();

	// What is the backing store type expected?
	let bit_store_def = types
		.resolve(bit_store_ty)
		.ok_or(BitSequenceError::BitStoreTypeNotFound(bit_store_ty))?
		.type_def();

	// What is the bit order type expected?
	let bit_order_def = types
		.resolve(bit_order_ty)
		.ok_or(BitSequenceError::BitOrderTypeNotFound(bit_order_ty))?
		.path()
		.ident()
		.ok_or(BitSequenceError::NoBitOrderIdent)?;

	let bit_order_out = match bit_store_def {
		TypeDef::Primitive(TypeDefPrimitive::U8) => Some(BitOrderTy::U8),
		TypeDef::Primitive(TypeDefPrimitive::U16) => Some(BitOrderTy::U16),
		TypeDef::Primitive(TypeDefPrimitive::U32) => Some(BitOrderTy::U32),
		TypeDef::Primitive(TypeDefPrimitive::U64) => Some(BitOrderTy::U64),
		_ => None,
	}
	.ok_or_else(|| BitSequenceError::OrderTypeNotSupported(format!("{bit_store_def:?}")))?;

	let bit_store_out = match &*bit_order_def {
		"Lsb0" => Some(BitStoreTy::Lsb0),
		"Msb0" => Some(BitStoreTy::Msb0),
		_ => None,
	}
	.ok_or(BitSequenceError::StoreTypeNotSupported(bit_order_def))?;

	Ok((bit_order_out, bit_store_out))
}

#[derive(Copy, Clone, PartialEq)]
pub enum BitStoreTy {
	Lsb0,
	Msb0,
}

#[derive(Copy, Clone, PartialEq)]
pub enum BitOrderTy {
	U8,
	U16,
	U32,
	U64,
}
