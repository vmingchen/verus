// Test ghost and tracked struct fields

struct MixedStruct {
    exec_field: u32,
    ghost ghost_field: int,
    another_exec: u64,
    tracked tracked_field: int,
}

struct OnlyGhostFields {
    ghost x: int,
    ghost y: int,
}

struct OnlyExecFields {
    a: u32,
    b: u64,
}

// Test methods accessing the fields
impl MixedStruct {
    fn get_exec_field(&self) -> u32 {
        self.exec_field
    }

    fn get_another_exec(&self) -> u64 {
        self.another_exec
    }
}
