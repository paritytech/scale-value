use crate::prelude::*;

#[derive(Clone, Debug)]
pub struct Path(Vec<PathSegment>);

impl Path {
    pub fn new() -> Path {
        Path(vec![])
    }
    pub fn at(&self, segment: PathSegment) -> Path {
        let mut p = self.0.clone();
        p.push(segment);
        Path(p)
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
}

impl core::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
pub enum PathSegment {
    Field(String),
    Index(usize),
    Variant(String),
}
