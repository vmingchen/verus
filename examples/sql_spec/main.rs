// Main entry point for running SQL executable tests

pub mod high_level_spec;
pub mod sql_algebra;
pub mod executable_impl;

fn main() {
    executable_impl::main();
}
