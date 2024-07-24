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

use crate::prelude::*;

// [jsdw] This could be internally turned into a linkedlist or something
// to make the "clone and append" faster. Not too concerned right now though
// since the tracing visitor it's used for isn't built for speed.
#[derive(Clone, Debug)]
pub struct Path(Vec<PathSegment>);

impl Path {
    pub fn new() -> Path {
        Path(vec![])
    }
    pub fn at_idx(&self, idx: usize) -> Path {
        self.at(PathSegment::Index(idx))
    }
    pub fn at_field(&self, field: String) -> Path {
        self.at(PathSegment::Field(field))
    }
    pub fn at_variant(&self, variant: String) -> Path {
        self.at(PathSegment::Variant(variant))
    }

    fn at(&self, segment: PathSegment) -> Path {
        let mut p = self.0.clone();
        p.push(segment);
        Path(p)
    }
}

impl core::fmt::Display for Path {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for segment in &self.0 {
            write!(f, ".")?;
            match segment {
                PathSegment::Index(idx) => write!(f, "[{idx}]")?,
                PathSegment::Field(field) => write!(f, "{field}")?,
                PathSegment::Variant(variant) => write!(f, "{variant}")?,
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
enum PathSegment {
    Field(String),
    Index(usize),
    Variant(String),
}
