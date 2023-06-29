use scale_value;

fn main() {
    // The `value` macro can construct Value's like so:
    let val = scale_value::value!({
        hello: "Hello",
        world: 12345,
        variant: Variant {
            foo: (1,2,3),
        }
    });

    println!("{val:?}");
}
