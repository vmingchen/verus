use std::fmt;
use std::path::PathBuf;

/// Errors that can occur during stripping
#[derive(Debug)]
pub enum StripError {
    /// Failed to read input file
    IoError {
        path: PathBuf,
        source: std::io::Error,
    },

    /// Failed to parse Verus/Rust source
    ParseError {
        path: PathBuf,
        error: verus_syn::Error,
        suggestion: &'static str,
    },

    /// Failed to write output
    WriteError {
        path: Option<PathBuf>,
        source: std::io::Error,
    },

    /// Invalid configuration
    ConfigError { message: String },
}

impl fmt::Display for StripError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            StripError::IoError { path, source } => {
                write!(f, "Failed to read file {}: {}", path.display(), source)
            }
            StripError::ParseError {
                path,
                error,
                suggestion,
            } => {
                write!(
                    f,
                    "Failed to parse {}: {}\nSuggestion: {}",
                    path.display(),
                    error,
                    suggestion
                )
            }
            StripError::WriteError { path, source } => {
                if let Some(p) = path {
                    write!(f, "Failed to write to {}: {}", p.display(), source)
                } else {
                    write!(f, "Failed to write output: {}", source)
                }
            }
            StripError::ConfigError { message } => {
                write!(f, "Configuration error: {}", message)
            }
        }
    }
}

impl std::error::Error for StripError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            StripError::IoError { source, .. } => Some(source),
            StripError::WriteError { source, .. } => Some(source),
            StripError::ParseError { error, .. } => Some(error),
            _ => None,
        }
    }
}

impl From<std::io::Error> for StripError {
    fn from(error: std::io::Error) -> Self {
        StripError::WriteError {
            path: None,
            source: error,
        }
    }
}

pub type Result<T> = std::result::Result<T, StripError>;
