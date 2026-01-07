struct Container {
    data: Vec<u32>,
    capacity: usize,
}
impl Container {
    fn len(&self) -> usize {
        self.data.len()
    }
    fn push(&mut self, value: u32) {
        self.data.push(value);
    }
    fn get(&self, index: usize) -> Option<u32> {
        self.data.get(index).copied()
    }
    fn with_all_ghost() -> u32 {
        42
    }
}
fn standalone_function(regular: u32, another_regular: u64) -> u32 {
    let result = regular + 10;
    result
}
