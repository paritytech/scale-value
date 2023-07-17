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

// Expose a consistent prelude, whether std or no-std (this is needed
// because no-std prelude doesn't contain `alloc` things), so we add
// those back in where needed. This should _not_ expose anything that's
// not a part of the `std` prelude already; import such things as needed
// from `core` or `alloc`.
pub use prelude_contents::*;

#[cfg(feature = "std")]
mod prelude_contents {
    pub use std::prelude::rust_2021::*;
}

#[cfg(not(feature = "std"))]
mod prelude_contents {
    pub use core::prelude::rust_2021::*;

    // The core prelude doesn't include things from
    // `alloc` by default, so add the ones we need that
    // are otherwose exposed via the std prelude.
    pub use alloc::borrow::ToOwned;
    pub use alloc::string::{String, ToString};
    pub use alloc::vec::Vec;
    pub use alloc::{boxed::Box, format, vec};
}
