// Test ghost variable stripping
fn example(x: u32) -> u32 {
    let ghost a = x as int;
    let ghost b = a + 1;

    let y = x + 1;

    let tracked t = 42;

    y
}

// Test mixed ghost and exec variables
fn mixed_vars(n: u32) -> u32 {
    let ghost spec_val = n as int;
    let exec_val = n * 2;
    let ghost another_ghost = spec_val + 1;

    exec_val
}
