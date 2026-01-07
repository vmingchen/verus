fn with_if_proof(x: u32) -> u32 {
    if x > 10 { x - 10 } else { x }
}
fn with_match_proof(x: Option<u32>) -> u32 {
    match x {
        Some(v) => v,
        None => 0,
    }
}
fn with_nested_blocks(x: u32) -> u32 {
    let result = {
        let temp = x + 1;
        temp
    };
    result
}
fn mixed_statements_and_exprs(x: u32, y: u32) -> u32 {
    let a = x + 1;
    let b = if y > 0 { y * 2 } else { 0 };
    a + b
}
