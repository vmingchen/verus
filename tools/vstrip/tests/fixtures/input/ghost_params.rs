// Test ghost and tracked function parameters using Ghost<T> and Tracked<T> types

fn with_ghost_param(x: u32, Ghost(y): Ghost<int>) -> u32 {
    x + 1
}

fn with_tracked_param(a: u32, Tracked(b): Tracked<int>, c: u32) -> u32 {
    a + c
}

fn mixed_params(
    exec1: u32,
    Ghost(g1): Ghost<int>,
    exec2: u32,
    Tracked(t1): Tracked<int>,
    exec3: u32,
) -> u32 {
    exec1 + exec2 + exec3
}

fn only_ghost_params(Ghost(x): Ghost<int>, Ghost(y): Ghost<int>) -> u32 {
    42
}

struct MyStruct {
    value: u32,
}

// Test in impl blocks
impl MyStruct {
    fn method_with_ghost(&self, x: u32, Ghost(y): Ghost<int>) -> u32 {
        x
    }
}
