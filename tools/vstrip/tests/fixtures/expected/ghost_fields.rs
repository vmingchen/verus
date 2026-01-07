struct MixedStruct {
    exec_field: u32,
    another_exec: u64,
}
struct OnlyGhostFields {}
struct OnlyExecFields {
    a: u32,
    b: u64,
}
impl MixedStruct {
    fn get_exec_field(&self) -> u32 {
        self.exec_field
    }
    fn get_another_exec(&self) -> u64 {
        self.another_exec
    }
}
