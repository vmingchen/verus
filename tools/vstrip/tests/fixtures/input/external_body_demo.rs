use vstd::prelude::*;

verus! {
    // WITHOUT external_body - Verus VERIFIES this
    fn add_one_verified(x: u64) -> (result: u64)
        requires x < 100,
        ensures result == x + 1,
    {
        x + 1  // Verus checks: does this actually return x + 1? ✓
    }

    // WITH external_body - Verus TRUSTS this (dangerous if wrong!)
    #[verifier::external_body]
    fn add_one_trusted(x: u64) -> (result: u64)
        requires x < 100,
        ensures result == x + 1,
    {
        x + 2  // BUG! But Verus doesn't check - it trusts the spec
    }

    // Verus will verify this function
    fn test_verified() {
        let result = add_one_verified(5);
        assert(result == 6);  // ✓ Verus proves this is correct
    }

    // Verus will also "verify" this, but it's actually WRONG at runtime!
    fn test_trusted() {
        let result = add_one_trusted(5);
        assert(result == 6);  // ✓ Verus "proves" this (trusts the spec)
                               // But at runtime: result is actually 7!
    }

    #[verifier::external_body]
    fn main() {
        println!("Verified: {}", add_one_verified(5));  // Prints 6
        println!("Trusted: {}", add_one_trusted(5));    // Prints 7 (wrong!)
    }
}
