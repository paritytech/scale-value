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

// Indexing into Value's to access things. We can't use the `Index` trait,
// since it returns references, and we can't necessarily give back a reference
// (`serde_json::Value` uses a statically initialised value to give back a ref
// to in these cases, but we have a generic `Ctx` and can't do that ourselves).

use super::{Composite, Value, ValueDef, Variant};
use crate::prelude::*;

/// This trait allows indexing into [`Value`]s (and options of [`Value`]s)
/// using the [`At::at()`] function. It's a little like Rust's [`::std::ops::Index`]
/// trait, but adapted so that we can return and work with optionals.
///
/// Indexing into a [`Value`] never panics; instead it will return `None` if a
/// value at the given location cannot be found.
///
/// # Example
///
/// ```
/// use scale_value::{ Value, At };
///
/// let val = Value::named_composite([
///     ("hello", Value::unnamed_composite([
///         Value::u128(1),
///         Value::bool(true),
///         Value::named_composite([
///             ("wibble", Value::bool(false)),
///             ("foo", Value::named_composite([
///                 ("bar", Value::u128(123))
///             ]))
///         ])
///     ]))
/// ]);
///
/// // Use `at` to access nested values:
/// assert_eq!(val.at("hello").at(0), Some(&Value::u128(1)));
/// assert_eq!(val.at("hello").at(1), Some(&Value::bool(true)));
/// assert_eq!(val.at("hello").at(2).at("wibble"), Some(&Value::bool(false)));
/// assert_eq!(val.at("hello").at(2).at("foo").at("bar"), Some(&Value::u128(123)));
///
/// // If the value doesn't exist, None will be returned:
/// assert_eq!(val.at("wibble").at(3), None);
/// assert_eq!(val.at("wibble").at("wobble").at("nope"), None);
/// ```
pub trait At<Ctx>: private::Sealed {
    /// Index into a value, returning a reference to the value if one
    /// exists, or [`None`] if not.
    fn at<L: AsLocation>(&self, loc: L) -> Option<&Value<Ctx>>;
}

// Prevent users from implementing the At trait.
mod private {
    use super::*;
    pub trait Sealed {}
    impl<Ctx> Sealed for Value<Ctx> {}
    impl<Ctx> Sealed for Composite<Ctx> {}
    impl<Ctx> Sealed for Variant<Ctx> {}
    impl<T: Sealed> Sealed for Option<&T> {}
}

impl<Ctx> At<Ctx> for Composite<Ctx> {
    fn at<L: AsLocation>(&self, loc: L) -> Option<&Value<Ctx>> {
        match loc.as_location().inner {
            LocationInner::Str(s) => match self {
                Composite::Named(vals) => {
                    vals.iter().find_map(|(n, v)| if s == n { Some(v) } else { None })
                }
                _ => None,
            },
            LocationInner::Usize(n) => match self {
                Composite::Named(vals) => {
                    let val = vals.get(n);
                    val.map(|v| &v.1)
                }
                Composite::Unnamed(vals) => vals.get(n),
            },
        }
    }
}

impl<Ctx> At<Ctx> for Variant<Ctx> {
    fn at<L: AsLocation>(&self, loc: L) -> Option<&Value<Ctx>> {
        self.values.at(loc)
    }
}

impl<Ctx> At<Ctx> for Value<Ctx> {
    fn at<L: AsLocation>(&self, loc: L) -> Option<&Value<Ctx>> {
        match &self.value {
            ValueDef::Composite(c) => c.at(loc),
            ValueDef::Variant(v) => v.at(loc),
            _ => None,
        }
    }
}

impl<Ctx, T: At<Ctx>> At<Ctx> for Option<&T> {
    fn at<L: AsLocation>(&self, loc: L) -> Option<&Value<Ctx>> {
        self.as_ref().and_then(|v| v.at(loc))
    }
}

/// Types which can be used as a lookup location with [`At::at`]
/// implement this trait.
///
/// Users cannot implement this as the [`Location`] type internals
/// are opaque and subject to change.
pub trait AsLocation {
    fn as_location(&self) -> Location<'_>;
}

impl AsLocation for usize {
    fn as_location(&self) -> Location<'_> {
        Location { inner: LocationInner::Usize(*self) }
    }
}

impl AsLocation for &str {
    fn as_location(&self) -> Location<'_> {
        Location { inner: LocationInner::Str(self) }
    }
}

impl AsLocation for String {
    fn as_location(&self) -> Location<'_> {
        Location { inner: LocationInner::Str(self) }
    }
}

impl<T: AsLocation> AsLocation for &T {
    fn as_location(&self) -> Location<'_> {
        (*self).as_location()
    }
}

/// A struct representing a location to access in a [`Value`].
#[derive(Copy, Clone)]
pub struct Location<'a> {
    inner: LocationInner<'a>,
}

#[derive(Copy, Clone)]
enum LocationInner<'a> {
    Usize(usize),
    Str(&'a str),
}

#[cfg(test)]
mod test {
    use crate::value;

    use super::*;

    // This is basically the doc example with a little extra.
    #[test]
    fn nested_accessing() {
        let val = value!({hello: (1u32, true, { wibble: false, foo: {bar: 123u32}})});
        assert_eq!(val.at("hello").at(0), Some(&Value::u128(1)));
        assert_eq!(val.at("hello").at(1), Some(&Value::bool(true)));
        assert_eq!(val.at("hello").at(2).at("wibble"), Some(&Value::bool(false)));
        assert_eq!(val.at("hello").at(2).at("foo").at("bar"), Some(&Value::u128(123)));

        assert_eq!(val.at("wibble").at(3), None);
        assert_eq!(val.at("wibble").at("wobble").at("nope"), None);

        // Strings can be used:
        assert_eq!(val.at("hello".to_string()).at(0), Some(&Value::u128(1)));
        // References to valid locations are fine too:
        #[allow(clippy::needless_borrow)]
        {
            assert_eq!(val.at(&"hello").at(&0), Some(&Value::u128(1)));
        }
    }

    #[test]
    fn accessing_variants() {
        let val = value!(TheVariant { foo: 12345u32, bar: 'c' });

        assert_eq!(val.at("foo").unwrap().as_u128().unwrap(), 12345);
        assert_eq!(val.at("bar").unwrap().as_char().unwrap(), 'c');

        let val = value!(TheVariant(12345u32, 'c'));

        assert_eq!(val.at(0).unwrap().as_u128().unwrap(), 12345);
        assert_eq!(val.at(1).unwrap().as_char().unwrap(), 'c');

        // We can use `at()` on the variant directly, too:

        let val =
            Variant::named_fields("TheVariant", [("foo", value!(12345u32)), ("bar", value!('c'))]);

        assert_eq!(val.at("foo").unwrap().as_u128().unwrap(), 12345);
        assert_eq!(val.at("bar").unwrap().as_char().unwrap(), 'c');

        let val = Variant::unnamed_fields("TheVariant", [value!(12345u32), value!('c')]);

        assert_eq!(val.at(0).unwrap().as_u128().unwrap(), 12345);
        assert_eq!(val.at(1).unwrap().as_char().unwrap(), 'c');
    }

    #[test]
    fn accessing_composites() {
        // We already test accessing composite Values. This also checks that `at` works on
        // the Composite type, too..

        let val = Composite::named([("foo", value!(12345u32)), ("bar", value!('c'))]);

        assert_eq!(val.at("foo").unwrap().as_u128().unwrap(), 12345);
        assert_eq!(val.at("bar").unwrap().as_char().unwrap(), 'c');

        let val = Composite::unnamed([value!(12345u32), value!('c')]);

        assert_eq!(val.at(0).unwrap().as_u128().unwrap(), 12345);
        assert_eq!(val.at(1).unwrap().as_char().unwrap(), 'c');
    }
}
