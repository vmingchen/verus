// Test trait methods with specs
trait Comparable {
    spec fn spec_compare(&self, other: &Self) -> bool;

    fn compare(&self, other: &Self) -> bool
        ensures result == self.spec_compare(other);
}

struct Number {
    value: i32,
}

impl Comparable for Number {
    spec fn spec_compare(&self, other: &Self) -> bool {
        self.value == other.value
    }

    fn compare(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
