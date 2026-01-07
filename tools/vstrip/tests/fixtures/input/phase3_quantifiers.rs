// Phase 3 test - quantifier expression stripping

fn with_forall_stmt(x: u32) -> u32 {
    forall|i: int| 0 <= i && i < x ==> i >= 0;
    x + 1
}

fn with_exists_stmt(x: u32) -> u32 {
    exists|i: int| i == x as int;
    x * 2
}

fn with_choose_stmt(x: u32) -> u32 {
    choose|i: int| i > x as int;
    x - 1
}

fn mixed_quantifiers(a: u32, b: u32) -> u32 {
    forall|x: int| x >= 0;

    let result = a + b;

    exists|y: int| y == result as int;

    result
}

fn quantifiers_in_proof_blocks(n: u32) -> u32 {
    proof! {
        forall|i: int| i < n as int;
        exists|j: int| j == n as int;
    }

    n + 10
}
