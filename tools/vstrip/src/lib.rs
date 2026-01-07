//! vstrip - Strip Verus specifications and proof code from Rust source files
//!
//! This library provides functionality to parse Verus-annotated Rust code,
//! remove all verification-related constructs (spec functions, proofs, ghost code),
//! and produce clean executable Rust code.

pub mod config;
pub mod error;
pub mod preprocess;
pub mod visitor;

use std::fs;
use std::path::Path;

pub use config::Config;
pub use error::{Result, StripError};
pub use visitor::StripVisitor;

use verus_syn::visit_mut::VisitMut;

/// Strip Verus specifications from source code string
///
/// # Arguments
/// * `source` - The Verus source code to strip
/// * `config` - Configuration for stripping behavior
///
/// # Returns
/// * `Ok(String)` - The stripped Rust source code
/// * `Err(StripError)` - If parsing or stripping fails
///
/// # Example
/// ```ignore
/// let source = r#"
///     verus! {
///         spec fn add_spec(a: int, b: int) -> int { a + b }
///
///         fn add(a: u32, b: u32) -> u32
///             requires a < 1000, b < 1000,
///             ensures result == a + b,
///         {
///             a + b
///         }
///     }
/// "#;
///
/// let stripped = vstrip::strip_source(source, &Config::default())?;
/// // Result: "fn add(a: u32, b: u32) -> u32 { a + b }"
/// ```
pub fn strip_source(source: &str, _config: &Config) -> Result<String> {
    // Preprocess: unwrap verus! macros
    let preprocessed = preprocess::unwrap_verus_macros(source)?;

    // Parse the source code
    let mut file = verus_syn::parse_file(&preprocessed).map_err(|e| StripError::ParseError {
        path: "<string>".into(),
        error: e,
        suggestion: "Ensure the code is valid Verus syntax",
    })?;

    // Apply stripping transformation
    let mut visitor = StripVisitor::new();
    visitor.visit_file_mut(&mut file);

    // Pretty-print the result
    let output = verus_prettyplease::unparse(&file);

    // TODO: Handle warnings
    // for warning in visitor.warnings() {
    //     eprintln!("Warning: {}", warning);
    // }

    Ok(output)
}

/// Strip Verus specifications from a file
///
/// # Arguments
/// * `path` - Path to the file to strip
/// * `config` - Configuration for stripping behavior
///
/// # Returns
/// * `Ok(String)` - The stripped Rust source code
/// * `Err(StripError)` - If file I/O, parsing, or stripping fails
pub fn strip_file(path: &Path, config: &Config) -> Result<String> {
    let source = fs::read_to_string(path).map_err(|e| StripError::IoError {
        path: path.to_path_buf(),
        source: e,
    })?;

    // Preprocess: unwrap verus! macros
    let preprocessed = preprocess::unwrap_verus_macros(&source)?;

    let mut file = verus_syn::parse_file(&preprocessed).map_err(|e| StripError::ParseError {
        path: path.to_path_buf(),
        error: e,
        suggestion: "Ensure the file is valid Verus syntax and compiles with Verus",
    })?;

    let mut visitor = StripVisitor::new();
    visitor.visit_file_mut(&mut file);

    let output = verus_prettyplease::unparse(&file);

    // Handle empty files
    if file.items.is_empty() && !config.keep_empty {
        eprintln!(
            "Warning: {} contained only specification code",
            path.display()
        );
    }

    Ok(output)
}

/// Process a file or directory according to configuration
///
/// This is the main entry point for the CLI tool.
///
/// # Arguments
/// * `input` - Path to file or directory to process
/// * `config` - Configuration for processing
///
/// # Returns
/// * `Ok(())` - If processing succeeded
/// * `Err(StripError)` - If processing failed
pub fn process(input: &Path, config: &Config) -> Result<()> {
    if !input.exists() {
        return Err(StripError::IoError {
            path: input.to_path_buf(),
            source: std::io::Error::new(std::io::ErrorKind::NotFound, "Input path does not exist"),
        });
    }

    if input.is_file() {
        process_file(input, config)
    } else if input.is_dir() {
        if config.recursive {
            process_directory(input, config)
        } else {
            Err(StripError::ConfigError {
                message: format!(
                    "{} is a directory. Use --recursive to process directories.",
                    input.display()
                ),
            })
        }
    } else {
        Err(StripError::IoError {
            path: input.to_path_buf(),
            source: std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "Input is neither a file nor a directory",
            ),
        })
    }
}

/// Process a single file
fn process_file(path: &Path, config: &Config) -> Result<()> {
    let stripped = strip_file(path, config)?;

    if config.check {
        // Check mode: just verify it worked
        println!("✓ {} would be stripped successfully", path.display());
        return Ok(());
    }

    if config.in_place {
        // Write back to the same file
        fs::write(path, &stripped).map_err(|e| StripError::WriteError {
            path: Some(path.to_path_buf()),
            source: e,
        })?;
        eprintln!("Stripped {} in place", path.display());
    } else if let Some(ref output) = config.output {
        // Write to specified output file
        fs::write(output, &stripped).map_err(|e| StripError::WriteError {
            path: Some(output.clone()),
            source: e,
        })?;
        eprintln!("Stripped {} -> {}", path.display(), output.display());
    } else {
        // Write to stdout
        print!("{}", stripped);
    }

    Ok(())
}

/// Process a directory recursively
fn process_directory(dir: &Path, config: &Config) -> Result<()> {
    use walkdir::WalkDir;

    let mut processed = 0;
    let mut errors = 0;

    for entry in WalkDir::new(dir)
        .follow_links(false)
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path = entry.path();

        // Only process .rs files
        if path.extension().and_then(|s| s.to_str()) != Some("rs") {
            continue;
        }

        match process_file(path, config) {
            Ok(()) => processed += 1,
            Err(e) => {
                eprintln!("Error processing {}: {}", path.display(), e);
                errors += 1;
            }
        }
    }

    eprintln!(
        "\nProcessed {} files ({} errors)",
        processed + errors,
        errors
    );

    if errors > 0 {
        Err(StripError::ConfigError {
            message: format!("{} files had errors", errors),
        })
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strip_basic_spec_fn() {
        let input = r#"
            spec fn add(a: int, b: int) -> int {
                a + b
            }
        "#;

        let result = strip_source(input, &Config::default());
        assert!(result.is_ok());

        let output = result.unwrap();
        // Spec function should be removed, leaving empty output
        assert!(!output.contains("spec fn"));
        assert!(!output.contains("add"));
    }

    #[test]
    fn test_strip_exec_fn_with_specs() {
        let input = r#"
            fn divide(a: u32, b: u32) -> u32
                requires b > 0,
                ensures result <= a,
            {
                a / b
            }
        "#;

        let result = strip_source(input, &Config::default());
        assert!(result.is_ok());

        let output = result.unwrap();
        // Function should remain but specs should be gone
        assert!(output.contains("fn divide"));
        assert!(output.contains("a / b"));
        assert!(!output.contains("requires"));
        assert!(!output.contains("ensures"));
    }
}
