trait Comparable {
    fn compare(&self, other: &Self) -> bool;
}
struct Number {
    value: i32,
}
impl Comparable for Number {
    fn compare(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
