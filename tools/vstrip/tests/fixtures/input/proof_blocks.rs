// Test assertion and proof block stripping
fn validated_divide(a: u32, b: u32) -> u32 {
    assert(b > 0);
    assume(a < 1000);

    proof {
        let x = a as int;
        let y = b as int;
    }

    let result = a / b;

    assert(result <= a);

    result
}

// Test with proof macro
fn with_proof_macro(x: u32) -> u32 {
    proof! {
        assert(x >= 0);
    }

    x + 1
}
