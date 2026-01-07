// Phase 3 test - macro stripping (proof!, calc!)

fn with_proof_macro(x: u32) -> u32 {
    proof! {
        assert(x >= 0);
        let y = x as int;
    }

    x + 1
}

fn with_nested_proof(a: u32, b: u32) -> u32 {
    let result = a + b;

    proof! {
        assert(result >= a);
        assert(result >= b);
    }

    result
}

fn multiple_proof_blocks(n: u32) -> u32 {
    proof! {
        assert(n < 1000);
    }

    let x = n * 2;

    proof! {
        assert(x == n + n);
    }

    x
}

// Test calc! macro
fn with_calc(x: u32) -> u32 {
    calc! {
        (==)
        x + 1; {}
        1 + x; {}
    }

    x + 1
}

fn proof_and_exec_mixed(n: u32) -> u32 {
    let a = n + 1;  // exec

    proof! {
        let ghost_val = n as int;
        assert(ghost_val >= 0);
    }

    let b = a * 2;  // exec

    b
}
