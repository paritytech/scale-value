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

//! This crate does not have its own single error type, but it does use the `Custom`
//! variant from some other error types, which accepts anything that can be cast into
//! a `Box<Error + Send + Sync + 'static>` on `std`, or a `Box<Debug + Send + Sync + 'static>`
//! on `no_std` envs.
//!
//! We expose a [`StrError`] and [`StringError`] here that are both compatible with either
//! `std` or `no_std` versions of this `Custom` field.

use crate::prelude::*;

/// An error from an underlying `&'static str`.
#[derive(derive_more::Display, derive_more::From, Debug, Copy, Clone, PartialEq)]
pub struct StrError(pub &'static str);

#[cfg(feature = "std")]
impl ::std::error::Error for StrError {}

#[cfg(not(feature = "std"))]
impl From<StrError> for BoxedError {
    fn from(value: StrError) -> Self {
        Box::new(value)
    }
}

/// An error which can be generated form anything implementing `Display`.
#[derive(derive_more::Display, derive_more::From, Debug, Clone, PartialEq)]
pub struct StringError(pub String);

#[cfg(feature = "std")]
impl ::std::error::Error for StringError {}

#[cfg(not(feature = "std"))]
impl From<StringError> for BoxedError {
    fn from(value: StringError) -> Self {
        Box::new(value)
    }
}

impl StringError {
    pub fn new<T: core::fmt::Display>(value: T) -> Self {
        StringError(value.to_string())
    }
}

/// An arbitrary custom error.
#[cfg(feature = "std")]
pub type BoxedError = Box<dyn ::std::error::Error + Send + Sync + 'static>;

/// An arbitrary custom error.
#[cfg(not(feature = "std"))]
pub type BoxedError = Box<dyn ::core::fmt::Debug + Send + Sync + 'static>;