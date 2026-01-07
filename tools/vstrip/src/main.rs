use clap::Parser;
use std::path::PathBuf;
use std::process;

use vstrip::{process, Config};

/// Strip Verus specifications and proof code from Rust source files
#[derive(Parser, Debug)]
#[command(
    name = "vstrip",
    version,
    about = "Strip Verus specifications and proof code from Rust source files",
    long_about = "vstrip removes all Verus verification constructs (spec functions, proofs, \
                  ghost code, specifications) from source files, producing clean executable Rust code."
)]
struct Cli {
    /// Input file or directory to process
    #[arg(value_name = "INPUT")]
    input: PathBuf,

    /// Output file (default: stdout)
    ///
    /// Cannot be used with --in-place
    #[arg(short, long, value_name = "FILE")]
    output: Option<PathBuf>,

    /// Modify files in place
    ///
    /// When processing a single file, replaces it with stripped version.
    /// When processing a directory with --recursive, replaces all .rs files.
    #[arg(short = 'i', long, conflicts_with = "output")]
    in_place: bool,

    /// Process directories recursively
    ///
    /// When input is a directory, recursively process all .rs files within it.
    #[arg(short, long)]
    recursive: bool,

    /// Check mode: verify stripping succeeds without writing
    ///
    /// Parses and strips files but doesn't write output. Useful for CI/CD validation.
    #[arg(long)]
    check: bool,

    /// Keep empty files after stripping
    ///
    /// By default, warns when a file contains only spec code. With this flag,
    /// creates an empty file instead.
    #[arg(long)]
    keep_empty: bool,
}

fn main() {
    let cli = Cli::parse();

    // Validate argument combinations
    if cli.in_place && cli.output.is_some() {
        eprintln!("Error: Cannot use --in-place with --output");
        process::exit(1);
    }

    if !cli.recursive && cli.input.is_dir() {
        eprintln!(
            "Error: {} is a directory. Use --recursive to process directories.",
            cli.input.display()
        );
        process::exit(1);
    }

    // Build configuration
    let config = Config {
        output: cli.output,
        in_place: cli.in_place,
        recursive: cli.recursive,
        check: cli.check,
        keep_empty: cli.keep_empty,
    };

    // Process the input
    if let Err(e) = process(&cli.input, &config) {
        eprintln!("Error: {}", e);
        if let Some(source) = std::error::Error::source(&e) {
            eprintln!("Caused by: {}", source);
        }
        process::exit(1);
    }
}
