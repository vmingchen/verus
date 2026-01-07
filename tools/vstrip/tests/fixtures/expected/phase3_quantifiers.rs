fn with_forall_stmt(x: u32) -> u32 {
    x + 1
}
fn with_exists_stmt(x: u32) -> u32 {
    x * 2
}
fn with_choose_stmt(x: u32) -> u32 {
    x - 1
}
fn mixed_quantifiers(a: u32, b: u32) -> u32 {
    let result = a + b;
    result
}
fn quantifiers_in_proof_blocks(n: u32) -> u32 {
    n + 10
}
