verus! {
    spec fn spec_func() -> int {
        42
    }

    proof fn proof_func() {
    }

    fn divide(a: u32, b: u32) -> u32
        requires b > 0,
        ensures result <= a,
    {
        a / b
    }
}
