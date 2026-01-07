trait Comparable {
    fn spec_compare(&self, other: &Self) -> bool;
    fn compare(&self, other: &Self) -> bool;
}
struct Number {
    value: i32,
}
impl Comparable for Number {
    fn spec_compare(&self, other: &Self) -> bool {
        self.value == other.value
    }
    fn compare(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
