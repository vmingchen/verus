# vstrip

A tool to strip Verus specifications and proof code from Rust source files, producing clean executable Rust code.

## Overview

`vstrip` removes all Verus verification constructs from source files:
- Spec functions (`spec fn`)
- Proof functions (`proof fn`)
- Specifications (`requires`, `ensures`, `invariant`, `decreases`)
- Ghost and tracked code
- Assertions and proof blocks
- Verification attributes

The output is standard Rust code that compiles with `rustc` without requiring Verus.

## Installation

From the Verus repository root:

```bash
cd tools/vstrip
cargo build --release
```

The binary will be at `target/release/vstrip`.

## Usage

### Basic Usage

Strip a single file to stdout:
```bash
vstrip input.rs
```

Strip a file to a specific output:
```bash
vstrip input.rs -o output.rs
```

Strip a file in place:
```bash
vstrip input.rs --in-place
```

### Directory Processing

Process all `.rs` files in a directory recursively:
```bash
vstrip src/ --recursive --in-place
```

### Check Mode

Verify files can be stripped without writing:
```bash
vstrip input.rs --check
```

## Command Line Options

- `-o, --output <FILE>` - Write output to specified file (default: stdout)
- `-i, --in-place` - Modify file(s) in place
- `-r, --recursive` - Process directories recursively
- `--check` - Check mode: verify without writing
- `--keep-empty` - Keep files that become empty after stripping
- `-h, --help` - Show help message
- `-V, --version` - Show version

## Examples

### Example 1: Basic Function

**Input:**
```rust
fn divide(a: u32, b: u32) -> u32
    requires b > 0,
    ensures result <= a,
{
    a / b
}
```

**Output:**
```rust
fn divide(a: u32, b: u32) -> u32 {
    a / b
}
```

### Example 2: Mixed Spec and Exec

**Input:**
```rust
verus! {
    spec fn add_spec(a: int, b: int) -> int {
        a + b
    }

    fn add(a: u32, b: u32) -> u32 {
        a + b
    }
}
```

**Output:**
```rust
fn add(a: u32, b: u32) -> u32 {
    a + b
}
```

### Example 3: Ghost Code

**Input:**
```rust
fn example(x: u32, ghost y: int) -> u32 {
    let ghost a = y + 1;
    assert(x > 0);
    x + 1
}
```

**Output:**
```rust
fn example(x: u32) -> u32 {
    x + 1
}
```

## Current Status

**Phase 1 (MVP)** - ✅ Complete:
- ✅ Basic project structure
- ✅ CLI interface
- ✅ Function mode stripping (spec/proof fn removal)
- ✅ Signature specification stripping (requires/ensures)
- ✅ Basic test fixtures

**Phase 2** - ✅ Complete:
- ✅ Ghost/tracked parameter stripping
- ✅ Ghost/tracked field stripping
- ✅ Type wrapper removal (Ghost<T>, Tracked<T>)
- ✅ Ghost/tracked local variable stripping

**Phase 3** - ✅ Complete:
- ✅ Expression-level proof stripping (nested assertions)
- ✅ Statement-level macro filtering (proof!, calc!)
- ✅ Assertion removal (assert, assume, assert_forall)
- ✅ Quantifier removal (forall, exists, choose)
- ✅ Ghost operator removal (@, ==>, <==>, &&&, |||)

**Phase 4** - ✅ Complete:
- ✅ Comprehensive testing (12 golden file tests + unit tests)
- ✅ Documentation updates
- ✅ verus! macro unwrapping (text-based preprocessor)
- ⏳ Recursive directory processing (future enhancement)

## Limitations

### Known Limitations

- Currently reformats code using `prettyplease` (similar to rustfmt) - original formatting is not preserved
- Recursive directory processing not yet implemented (--recursive flag not functional)
- Multi-crate processing not yet implemented
- Specifications inside other macro calls (like test infrastructure macros) may not be stripped

## Contributing

Contributions are welcome! Please see the main Verus [CONTRIBUTING.md](../../CONTRIBUTING.md) for guidelines.

## License

Licensed under either of:
- Apache License, Version 2.0 ([LICENSE-APACHE](../../LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](../../LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.
