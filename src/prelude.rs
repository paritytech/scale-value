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

// To mirror the rust prelude, use top level
// crates to avoid needing `::` prefix everywhere, and
// import any macros we use that would otherwise be a
// part of the prelude.
macro_rules! shared_imports {
    () => {
        pub use ::codec;
        pub use ::core;
        pub use ::derive_more;
        pub use ::either;
        pub use ::frame_metadata;
        pub use ::scale_bits;
        pub use ::scale_decode;
        pub use ::scale_encode;
        pub use ::scale_info;

        #[cfg(feature = "serde")]
        pub use ::serde;

        #[cfg(feature = "from-string")]
        pub use ::yap;

        #[cfg(feature = "parser-ss58")]
        pub use ::base58;
        #[cfg(feature = "parser-ss58")]
        pub use ::blake2;

        #[cfg(test)]
        pub use ::hex;
        #[cfg(test)]
        pub use ::serde_json;

        pub use ::alloc::{boxed::Box, format, vec};
        pub use ::core::{assert_eq, matches, panic, stringify, write};
    };
}
use shared_imports;

#[cfg(feature = "std")]
mod prelude_contents {
    pub use ::std::prelude::rust_2021::*;

    super::shared_imports!();
}

#[cfg(not(feature = "std"))]
mod prelude_contents {
    pub use ::core::prelude::rust_2021::*;

    pub use ::alloc::borrow::ToOwned;
    pub use ::alloc::string::{String, ToString};
    pub use ::alloc::vec::Vec;

    super::shared_imports!();
}
