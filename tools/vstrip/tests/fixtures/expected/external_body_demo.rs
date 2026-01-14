fn add_one_verified(x: u64) -> u64 {
    x + 1
}
fn add_one_trusted(x: u64) -> u64 {
    x + 2
}
fn test_verified() {
    let result = add_one_verified(5);
}
fn test_trusted() {
    let result = add_one_trusted(5);
}
fn main() {
    println!("Verified: {}", add_one_verified(5));
    println!("Trusted: {}", add_one_trusted(5));
}
