fn with_proof_macro(x: u32) -> u32 {
    x + 1
}
fn with_nested_proof(a: u32, b: u32) -> u32 {
    let result = a + b;
    result
}
fn multiple_proof_blocks(n: u32) -> u32 {
    let x = n * 2;
    x
}
fn with_calc(x: u32) -> u32 {
    x + 1
}
fn proof_and_exec_mixed(n: u32) -> u32 {
    let a = n + 1;
    let b = a * 2;
    b
}
