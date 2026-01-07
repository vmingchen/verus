fn with_ghost_param(x: u32) -> u32 {
    x + 1
}
fn with_tracked_param(a: u32, c: u32) -> u32 {
    a + c
}
fn mixed_params(exec1: u32, exec2: u32, exec3: u32) -> u32 {
    exec1 + exec2 + exec3
}
fn only_ghost_params() -> u32 {
    42
}
struct MyStruct {
    value: u32,
}
impl MyStruct {
    fn method_with_ghost(&self, x: u32) -> u32 {
        x
    }
}
