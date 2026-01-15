// SQL Formal Specification in Verus
// Based on "A Coq formalisation of SQL's execution engines"
// by V. Benzaken, E. Contejean, Ch. Keller, and E. Martins

pub mod high_level_spec;
pub mod physical_algebra;
pub mod sql_algebra;
pub mod bridge;
pub mod executable_impl;

// Re-exports for specification types only
// Note: executable_impl is NOT re-exported to avoid name conflicts with ghost types
// Use executable_impl::* explicitly when you need executable types
pub use high_level_spec::*;
pub use physical_algebra::*;
pub use sql_algebra::*;
pub use bridge::*;
