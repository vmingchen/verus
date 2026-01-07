fn fibonacci(n: u64) -> u64 {
    if n <= 1 { n } else { fibonacci(n - 1) + fibonacci(n - 2) }
}
struct Counter {
    value: u32,
}
impl Counter {
    fn spec_method(&self) -> int {
        self.value as int
    }
    fn new() -> Self {
        Counter { value: 0 }
    }
    fn increment(&mut self) {
        self.value += 1;
    }
}
