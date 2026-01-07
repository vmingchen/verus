// Test multiple spec clauses
fn fibonacci(n: u64) -> u64
    requires n < 100,
    ensures result >= n,
    decreases n,
{
    if n <= 1 {
        n
    } else {
        fibonacci(n - 1) + fibonacci(n - 2)
    }
}

// Test impl methods with specs
struct Counter {
    value: u32,
}

impl Counter {
    spec fn spec_method(&self) -> int {
        self.value as int
    }

    fn new() -> Self
        ensures result.value == 0,
    {
        Counter { value: 0 }
    }

    fn increment(&mut self)
        requires self.value < 1000,
        ensures self.value == old(self).value + 1,
    {
        self.value += 1;
    }
}
