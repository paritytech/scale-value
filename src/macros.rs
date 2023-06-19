/// Construct a `scale_value::Value`
///
///
/// Supports unnamed and named composites and variants:
/// ```
/// use scale_value::value;
///
/// let val = value!({
///     name: "localhost",
///     address: V4(127, 0, 0, 1),
///     payload: {
///         bytes: (255, 3, 4, 9),
///         method: ("Post", 3000),
///     },
/// });
///
/// ```
/// Values can be nested in each other:
/// ```
/// use scale_value::value;
///
/// let data_value = value!((1, v1(1, 2), 3));
/// let val = value!(POST { data: data_value });
/// ```
/// Trailing commas are optional.
#[macro_export(local_inner_macros)]
macro_rules! value {
    ($($tt:tt)*) => {
        value_internal!($($tt)*)
    };
}

/// All patterns can be grouped into 4 main patterns:
///
/// ### `value_internal!(@unnamed [ELEMENTS] (REST))`
///
/// checks `REST` for certain patterns and if a suitable element pattern is found,
/// the element is added to the comma seperated `ELEMENTS` list. When `REST` is empty,
/// we collect all `ELEMENTS` into a Vec of values.
///
/// ### `value_internal!(@named [KEYVALUEPAIRS] (PARTIALKEY) (REST))`
///
/// goes over the REST tokens, to build up the PARTIALKEY until it is a proper KEY.
/// This happens as soon as a colon `:` token is encountered, then we switch to the next pattern:
///
/// ### `value_internal!(@named [KEYVALUEPAIRS] [KEY] (REST))`
///
/// The square brackets now indicate that the key is fully formed. Now REST is scanned for the next
/// `VALUE`. Together with the `KEY`, they are added as a key value pair tuple into the KEYVALUEPAIRS list.
/// At that point we switch back to the partial key pattern above, e.g. `value_internal!(@named [KEYVALUEPAIRS] () (REST))`
/// now with a new empty partial key that has to be filled.
/// When `REST` is empty, we collect all `KEYVALUEPAIRS` into a Vec of key-value tuples.
///
/// ### `value_internal!(BASEPATTERN)`
///
/// These patterns check if the input represents a composite or variant type or can be made into a valid `$crate::Value`.
#[macro_export(local_inner_macros)]
#[doc(hidden)]
macro_rules! value_internal {

    ////////////////////////////////////////////////////////////////////////////
    // collecting unnamed fields
    ////////////////////////////////////////////////////////////////////////////

    // done, put all the fields in a vec
    (@unnamed [$($e:expr, )*] ()) => { vec_wrapper![$($e, )*] };

    // Next value is an unnamed composite
    (@unnamed [$($e:expr, )*] (($($array:tt)*) $($rest:tt)*)) => {
        value_internal!(@unnamed [$($e, )*] (value_internal!(($($array)*))) $($rest)*)
    };

    // Next value is an unnamed variant
    (@unnamed [$($e:expr, )*] ($variant:ident ($($array:tt)*) $($rest:tt)*)) => {
        value_internal!(@unnamed [$($e, )*] (value_internal!($variant ($($array)*))) $($rest)*)
    };

    // Next value is a named composite
    (@unnamed [$($e:expr, )*] ({$($map:tt)*} $($rest:tt)*)) => {
        value_internal!(@unnamed [$($e, )*] (value_internal!({$($map)*})) $($rest)*)
    };

    // Next value is a named variant
    (@unnamed [$($e:expr, )*] ($variant:ident {$($map:tt)*} $($rest:tt)*)) => {
        value_internal!(@unnamed [$($e, )*] (value_internal!($variant {$($map)*})) $($rest)*)
    };

    // Insert the current entry followed by trailing comma
    (@unnamed [$($e:expr, )*] ($value:expr) , $($rest:tt)*) => {
        value_internal!(@unnamed [$($e, )* $value , ] ($($rest)*))
    };

    // Current entry followed by unexpected token.
    // There needs to be a comma, which would match the previous matcher or no further tokens at all matching the next matcher
     (@unnamed [$($e:expr, )*] ($value:expr) $unexpected:tt $($rest:tt)*) => {
        let token = core::stringify!($unexpected);
        compile_error!("unexpected token after expression: {}", token);
    };

    // Insert the last entry without trailing comma
    (@unnamed [$($e:expr, )*] ($value:expr)) => {
        vec_wrapper![ $($e, )* value_internal!($value) ]
    };

    // Next value is an expression followed by comma
    (@unnamed [$($e:expr, )*] ($value:expr , $($rest:tt)*)) => {
        value_internal!(@unnamed [$($e, )*] (value_internal!($value)) , $($rest)*)
    };

    // Last value is an expression with no trailing comma
    (@unnamed [$($e:expr, )*] ($value:expr)) => {
        value_internal!(@unnamed [$($e, )*] (value_internal!($value)))
    };

    ////////////////////////////////////////////////////////////////////////////
    // collecting named fields
    ////////////////////////////////////////////////////////////////////////////

    // done, put all the key value pairs in a vec
    (@named [$(($k:expr, $v:expr), )*] () ()) => { vec_wrapper![ $(($k, $v), )* ] };

    // Insert the current entry followed by trailing comma.
    (@named [$(($k:expr, $v:expr), )*] [$($key:tt)+] ($value:expr) , $($rest:tt)*) => {
        {
            let field_name = core::stringify!($($key)+).to_string();
            value_internal!(@named [$(($k, $v), )* (field_name, $value), ] () ($($rest)*))
        }
    };

    // Current entry followed by unexpected token.
    // There needs to be a comma, which would match the previous matcher or no further tokens at all matching the next matcher
    (@named [$(($k:expr, $v:expr), )*] [$($key:tt)+] ($value:expr) $unexpected:tt $($rest:tt)*) => {
        let token = core::stringify!($unexpected);
        compile_error!("unexpected token after expression: {}", token);
    };

    // Insert the last entry without trailing comma.
    (@named [$(($k:expr, $v:expr), )*] [$($key:tt)+] ($value:expr)) => {
        {
            let field_name = core::stringify!($($key)+).to_string();
            vec_wrapper![ $(($k, $v), )* (field_name, $value) ]
        }
    };

    // Next value is an unnamed composite
    (@named [$(($k:expr, $v:expr), )*] ($($key:tt)+) (: ($($array:tt)*) $($rest:tt)*)) => {
        value_internal!(@named [$(($k, $v), )*] [$($key)+] (value_internal!(($($array)*))) $($rest)*)
    };

    // Next value is an unnamed variant
    (@named [$(($k:expr, $v:expr), )*] ($($key:tt)+) (: $variant:ident ($($array:tt)*) $($rest:tt)*)) => {
        value_internal!(@named [$(($k, $v), )*] [$($key)+] (value_internal!($variant ($($array)*))) $($rest)*)
    };

    // Next value is a named composite
    (@named [$(($k:expr, $v:expr), )*] ($($key:tt)+) (: {$($map:tt)*} $($rest:tt)*)) => {
        value_internal!(@named [$(($k, $v), )*] [$($key)+] (value_internal!({$($map)*})) $($rest)*)
    };

    // Next value is a named variant
    (@named [$(($k:expr, $v:expr), )*] ($($key:tt)+) (: $variant:ident {$($map:tt)*} $($rest:tt)*)) => {
        value_internal!(@named [$(($k, $v), )*] [$($key)+] (value_internal!($variant {$($map)*})) $($rest)*)
    };

    // // Next value is an expression followed by comma
    (@named [$(($k:expr, $v:expr), )*] ($($key:tt)+) (: $value:expr , $($rest:tt)*)) => {
        value_internal!(@named [$(($k, $v), )*] [$($key)+] (value_internal!($value)) , $($rest)*)
    };

    // Last value is an expression with no trailing comma
    (@named [$(($k:expr, $v:expr), )*] ($($key:tt)+) (: $value:expr)) => {
        value_internal!(@named [$(($k, $v), )*] [$($key)+] (value_internal!($value)))
    };

    // Eror pattern: Missing value for last entry
    (@named [$(($k:expr, $v:expr), )*] ($($key:tt)+) (:)) => {
        compile_error!("missing value for last entry");
    };

    // Eror pattern: Missing colon and value for last entry
    (@named [$(($k:expr, $v:expr), )*] ($($key:tt)+) ()) => {
        compile_error!("missing colon and value for last entry");
    };

    // Eror pattern: colon as first token
    (@named [$(($k:expr, $v:expr), )*] () (: $($rest:tt)*)) => {
        compile_error!("colon in wrong position");
    };

    // Eror pattern: comma inside key
    (@named [$(($k:expr, $v:expr), )*] ($($key:tt)*) (, $($rest:tt)*)) => {
        compile_error!("comma in key of named composite");
    };

    (@named [$(($k:expr, $v:expr), )*] () (($key:expr) : $($rest:tt)*)) => {
        value_internal!(@named [$(($k, $v), )*] ($key) (: $($rest)*))
    };

    // add a token into the current key.
    (@named [$(($k:expr, $v:expr), )*] ($($key:tt)*) ($tt:tt $($rest:tt)*)) => {
        value_internal!(@named [$(($k, $v), )*] ($($key)* $tt) ($($rest)*))
    };

    ////////////////////////////////////////////////////////////////////////////
    // Main implementation of patterns:
    ////////////////////////////////////////////////////////////////////////////

    // empty composites:
    () => {
        $crate::Value::unnamed_composite(Vec::<$crate::Value>::new())
    };
    (()) => {
        $crate::Value::unnamed_composite(Vec::<$crate::Value>::new())
    };
    ({}) => {
        $crate::Value::named_composite(Vec::<(String, $crate::Value)>::new())
    };

    // named composites e.g. { age: 1, nice: false }
    ({ $($tt:tt)* }) => {
        {
            let fields: Vec::<(String, $crate::Value)> = value_internal!(@named [] () ($($tt)*));
            $crate::Value::named_composite(fields)
        }
    };

    // named variants e.g. v1 { age: 1, nice: false }
    ($variant:ident { $($tt:tt)* }) => {
        {
            let variant_name = core::stringify!($variant).to_string();
            let fields: Vec::<(String, $crate::Value)> = value_internal!(@named [] () ($($tt)*));
            $crate::Value::named_variant(variant_name,fields)
        }
    };

    // unnamed composites with (..) syntax e.g. (1,"hello",3)
    (( $($tt:tt)* )) => {
        {
            let fields = value_internal!(@unnamed [] ($($tt)*));
            $crate::Value::unnamed_composite(fields)
        }
    };

    // unnamed composites with [..] syntax e.g. [1,"hello",3]
    ([ $($tt:tt)* ]) => {
        {
            let fields = value_internal!(@unnamed [] ($($tt)*));
            $crate::Value::unnamed_composite(fields)
        }
    };

    // unnamed variants e.g. v1 (1,2,3,4)
    ($variant:ident ( $($tt:tt)* )) => {
        {
            let variant_name = core::stringify!($variant).to_string();
            let fields = value_internal!(@unnamed [] ($($tt)*));
            $crate::Value::unnamed_variant(variant_name,fields)
        }
    };

    // any other expressions
    ($val:expr) => {
        $crate::Value::from($val)
    };
}

// The json_internal macro above cannot invoke vec directly because it uses
// local_inner_macros. A vec invocation there would resolve to $crate::vec.
#[macro_export]
#[doc(hidden)]
macro_rules! vec_wrapper {
    ($($content:tt)*) => {
        vec![$($content)*]
    };
}

#[cfg(test)]
#[macro_use]
mod test {
    use crate::{value, Value};

    ///
    #[test]
    fn macro_tests() {
        // primitives:
        assert_eq!(value!(1), Value::from(1));
        assert_eq!(value!(-122193223i64), Value::from(-122193223i64));
        assert_eq!(value!(89usize), Value::from(89usize));
        assert_eq!(value!(false), Value::from(false));
        assert_eq!(value!(true), Value::from(true));
        assert_eq!(value!('h'), Value::from('h'));
        assert_eq!(value!("Hello"), Value::from("Hello"));
        assert_eq!(value!("Hello".to_string()), Value::from("Hello"));
        let s = "Hello".to_string();
        assert_eq!(value!(s), Value::from("Hello"));

        // unnamed composites:
        let unnamed_composite =
            Value::unnamed_composite([Value::from(1), Value::from("nice"), Value::from('t')]);

        assert_eq!(value!((1, "nice", 't')), unnamed_composite);
        assert_eq!(value!((1, "nice", 't',)), unnamed_composite);

        let empty_composite = Value::unnamed_composite([]);
        assert_eq!(value!(()), empty_composite);

        // named composites:
        let named_composite =
            Value::named_composite([("num", Value::from(3)), ("item", Value::from("tea"))]);
        assert_eq!(value!({num: 3, item: "tea"}), named_composite);
        assert_eq!(value!({num: 3, item: "tea", }), named_composite);
        // variants:
        let variant_no_fields = Value::variant("v1", crate::Composite::Unnamed(vec![]));
        assert_eq!(value!(v1()), variant_no_fields);
        let named_variant = Value::variant(
            "V2",
            crate::Composite::named([("num", Value::from(3)), ("item", Value::from("tea"))]),
        );
        assert_eq!(value!(V2 { num: 3, item: "tea" }), named_variant);
        // wild combination, just check if compiles:
        let _ = value!({ unnamed: unnamed_composite, vals: (v1{name: "berry", age: 34}, named_variant), named: named_composite });
    }
}
