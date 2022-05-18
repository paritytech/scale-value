# scale-value

This crate provides a `Value` type which can be used in conjunction with a `scale_info::PortableRegistry` to encode and decode values of arbitrary shapes to SCALE bytes. Via `serde` it's also possible to serialize and deserialize static types to and from `Value`s.