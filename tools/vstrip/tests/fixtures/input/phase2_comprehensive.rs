// Comprehensive Phase 2 test - ghost/tracked parameters and fields together

struct Container {
    data: Vec<u32>,
    ghost spec_data: Seq<int>,
    capacity: usize,
    tracked perm: int,
}

impl Container {
    fn len(&self) -> usize {
        self.data.len()
    }

    fn push(&mut self, value: u32, Ghost(old_len): Ghost<int>) {
        self.data.push(value);
    }

    fn get(&self, index: usize, Tracked(perm): Tracked<int>) -> Option<u32> {
        self.data.get(index).copied()
    }

    fn with_all_ghost(Ghost(x): Ghost<int>, Ghost(y): Ghost<int>) -> u32 {
        42
    }
}

fn standalone_function(
    regular: u32,
    Ghost(spec_val): Ghost<int>,
    another_regular: u64,
    Tracked(tracked_val): Tracked<int>,
) -> u32 {
    let ghost local_spec = spec_val + 1;
    let result = regular + 10;
    let tracked local_tracked = tracked_val;

    result
}
