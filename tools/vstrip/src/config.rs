use std::path::PathBuf;

/// Configuration for stripping operations
#[derive(Debug, Clone)]
pub struct Config {
    /// Output file path (None = stdout)
    pub output: Option<PathBuf>,

    /// Modify file in place
    pub in_place: bool,

    /// Process directories recursively
    pub recursive: bool,

    /// Check mode: verify without writing
    pub check: bool,

    /// Keep empty files (vs. removing them)
    pub keep_empty: bool,

    /// Convert specifications to comments instead of removing them
    pub spec_as_comments: bool,
}

impl Config {
    pub fn new() -> Self {
        Self {
            output: None,
            in_place: false,
            recursive: false,
            check: false,
            keep_empty: false,
            spec_as_comments: false,
        }
    }
}

impl Default for Config {
    fn default() -> Self {
        Self::new()
    }
}
