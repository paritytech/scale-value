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
///         bytes: [255,3,4,9],
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
/// Unnamed composites can be represented by either round or square brackets: (1,2,3) or [1,2,3]
#[macro_export(local_inner_macros)]
macro_rules! value {
    ($($tt:tt)*) => {
        value_internal!($($tt)*)
    };
}

/// There are 3 modes in which value_internal! operates:
///
/// I. value_internal!(@unnamed $fields...):
/// - This fills a given `mut $fields : Vec<scale_value::Value>` variable with values.
/// - does not return anything.
///
/// II. value_internal!(@named $fields...):
/// - This fills a given `mut $fields : Vec<(String,scale_value::Value)>` variable with keys and values.
/// - does not return anything.
///
/// III. value_internal!(...):
/// - returns a `scale_value::Value`
#[macro_export(local_inner_macros)]
#[doc(hidden)]
macro_rules! value_internal {
    ////////////////////////////////////////////////////////////////////////////
    // collecting unnamed fields
    ////////////////////////////////////////////////////////////////////////////

    // done
    (@unnamed $fields:ident ()) => {};

    // Insert the current entry followed by trailing comma.
    (@unnamed $fields:ident ($value:expr) , $($rest:tt)*) => {
        $fields.push($value);
        // continue with rest of tokens, inserting them into the fields vec:
        value_internal!(@unnamed $fields ($($rest)*));
    };

    // Current entry followed by unexpected token.
    // There needs to be a comma, which would match the previous matcher or no further tokens at all matching the next matcher
     (@unnamed $fields:ident ($value:expr) $unexpected:tt $($rest:tt)*) => {
        let token = core::stringify!($unexpected);
        compile_error!("unexpected token after expression: {}", token);
    };

    // Insert the last entry without trailing comma
    (@unnamed $fields:ident ($value:expr)) => {
        $fields.push(value_internal!($value));
    };

    // Next value is an unnamed composite with [..] syntax
    (@unnamed $fields:ident ([$($array:tt)*] $($rest:tt)*)) => {
        value_internal!(@unnamed $fields (value_internal!([$($array)*])) $($rest)*);
    };

    // Next value is an unnamed composite with (..) syntax
    (@unnamed $fields:ident (($($array:tt)*) $($rest:tt)*)) => {
        value_internal!(@unnamed $fields (value_internal!(($($array)*))) $($rest)*);
    };

    // Next value is an unnamed variant
    (@unnamed $fields:ident ($variant:ident ($($array:tt)*) $($rest:tt)*)) => {
        value_internal!(@unnamed $fields (value_internal!($variant ($($array)*))) $($rest)*);
    };

    // Next value is a named composite
    (@unnamed $fields:ident ({$($map:tt)*} $($rest:tt)*)) => {
        value_internal!(@unnamed $fields (value_internal!({$($map)*})) $($rest)*);
    };

    // Next value is a named variant
    (@unnamed $fields:ident ($variant:ident {$($map:tt)*} $($rest:tt)*)) => {
        value_internal!(@unnamed $fields (value_internal!($variant {$($map)*})) $($rest)*);
    };

    // Next value is an expression followed by comma
    (@unnamed $fields:ident ($value:expr , $($rest:tt)*)) => {
        value_internal!(@unnamed $fields (value_internal!($value)) , $($rest)*);
    };

    // Last value is an expression with no trailing comma
    (@unnamed $fields:ident ($value:expr)) => {
        value_internal!(@unnamed $fields (value_internal!($value)));
    };

    ////////////////////////////////////////////////////////////////////////////
    // collecting named fields
    //   note on key collection:
    //     if key completely constructed: @named $fields:ident [$($key:tt)+] ...
    //     if still constructing key:     @named $fields:ident ($($key:tt)+) ...
    ////////////////////////////////////////////////////////////////////////////

    // done
    (@named $fields:ident () ()) => {};

    // Insert the current entry followed by trailing comma.
    (@named $fields:ident [$($key:tt)+] ($value:expr) , $($rest:tt)*) => {
        let field_name = core::stringify!($($key)+).to_string();
        $fields.push((field_name, $value));
        // continue with rest of tokens, inserting them into the fields vec:
        value_internal!(@named $fields () ($($rest)*));
    };

    // Current entry followed by unexpected token.
    // There needs to be a comma, which would match the previous matcher or no further tokens at all matching the next matcher
    (@named $fields:ident [$($key:tt)+] ($value:expr) $unexpected:tt $($rest:tt)*) => {
        let token = core::stringify!($unexpected);
        compile_error!("unexpected token after expression: {}", token);
    };

    // Insert the last entry without trailing comma.
    (@named $fields:ident [$($key:tt)+] ($value:expr)) => {
        let field_name = core::stringify!($($key)+).to_string();
        $fields.push((field_name, $value));
    };

    // Next value is an unnamed composite with [..] syntax
     (@named $fields:ident ($($key:tt)+) (: [$($array:tt)*] $($rest:tt)*)) => {
        value_internal!(@named $fields [$($key)+] (value_internal!([$($array)*])) $($rest)*);
    };

    // Next value is an unnamed composite with (..) syntax
    (@named $fields:ident ($($key:tt)+) (: ($($array:tt)*) $($rest:tt)*)) => {
        value_internal!(@named $fields [$($key)+] (value_internal!(($($array)*))) $($rest)*);
    };

    // Next value is an unnamed variant
    (@named $fields:ident ($($key:tt)+) (: $variant:ident ($($array:tt)*) $($rest:tt)*)) => {
        value_internal!(@named $fields [$($key)+] (value_internal!($variant ($($array)*))) $($rest)*);
    };

    // Next value is a named composite
    (@named $fields:ident ($($key:tt)+) (: {$($map:tt)*} $($rest:tt)*)) => {
        value_internal!(@named $fields [$($key)+] (value_internal!({$($map)*})) $($rest)*);
    };

    // Next value is a named variant
    (@named $fields:ident ($($key:tt)+) (: $variant:ident {$($map:tt)*} $($rest:tt)*)) => {
        value_internal!(@named $fields [$($key)+] (value_internal!($variant {$($map)*})) $($rest)*);
    };

    // // Next value is an expression followed by comma
    (@named $fields:ident ($($key:tt)+) (: $value:expr , $($rest:tt)*)) => {
        value_internal!(@named $fields [$($key)+] (value_internal!($value)) , $($rest)*);
    };


    // Last value is an expression with no trailing comma
    (@named $fields:ident ($($key:tt)+) (: $value:expr)) => {
        value_internal!(@named $fields [$($key)+] (value_internal!($value)));
    };

    // Eror pattern: Missing value for last entry
    (@named $fields:ident ($($key:tt)+) (:)) => {
        compile_error!("missing value for last entry");
    };

    // Eror pattern: Missing colon and value for last entry
    (@named $fields:ident ($($key:tt)+) ()) => {
        compile_error!("missing colon and value for last entry");
    };

    // Eror pattern: colon as first token
    (@named $fields:ident () (: $($rest:tt)*)) => {
        compile_error!("colon in wrong position");
    };

    // Eror pattern: comma inside key
    (@named $fields:ident ($($key:tt)*) (, $($rest:tt)*)) => {
        compile_error!("comma in key of named composite");
    };


    // todo! explain this
    (@named $fields:ident () (($key:expr) : $($rest:tt)*)) => {
        value_internal!(@named $fields ($key) (: $($rest)*));
    };

    // add a token into the current key.
    (@named $fields:ident ($($key:tt)*) ($tt:tt $($rest:tt)*)) => {
        value_internal!(@named $fields ($($key)* $tt) ($($rest)*));
    };

    ////////////////////////////////////////////////////////////////////////////
    // Main implementation of patterns:
    ////////////////////////////////////////////////////////////////////////////

    // empty composites:
    () => {
        $crate::Value::unnamed_composite(Vec::<$crate::Value>::new())
    };
    ([]) => {
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
            let mut fields = Vec::<(String, $crate::Value)>::new();
            value_internal!(@named fields () ($($tt)*));
            $crate::Value::named_composite(fields)
        }
    };

    // named variants e.g. v1 { age: 1, nice: false }
    ($variant:ident { $($tt:tt)* }) => {
        {
            let variant_name = core::stringify!($variant).to_string();
            let mut fields = Vec::<(String, $crate::Value)>::new();
            value_internal!(@named fields () ($($tt)*));
            $crate::Value::named_variant(variant_name,fields)
        }
    };

    // unnamed composites with (..) syntax e.g. (1,"hello",3)
    (( $($tt:tt)* )) => {
        {
            let mut fields = Vec::<Value>::new();
            value_internal!(@unnamed fields ($($tt)+));
            $crate::Value::unnamed_composite(fields)
        }
    };

    // unnamed composites with [..] syntax e.g. [1,"hello",3]
    ([ $($tt:tt)* ]) => {
        {
            let mut fields = Vec::<$crate::Value>::new();
            value_internal!(@unnamed fields ($($tt)*));
            $crate::Value::unnamed_composite(fields)
        }
    };

    // unnamed variants e.g. v1 (1,2,3,4)
    ($variant:ident ( $($tt:tt)* )) => {
        {
            let variant_name = core::stringify!($variant).to_string();
            let mut fields = Vec::<$crate::Value>::new();
            value_internal!(@unnamed fields ($($tt)*));
            $crate::Value::unnamed_variant(variant_name,fields)
        }
    };

    // any other expressions
    ($val:expr) => {
        $crate::Value::from($val)
    };
}
