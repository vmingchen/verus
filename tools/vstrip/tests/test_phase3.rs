use std::fs;
use vstrip::{strip_source, Config};

#[test]
fn test_phase3_macros() {
    let input = fs::read_to_string("tests/fixtures/input/phase3_macros.rs")
        .expect("Failed to read phase3_macros.rs");

    let output = strip_source(&input, &Config::default()).expect("Failed to strip");

    // Verify proof! macros are removed
    assert!(!output.contains("proof!"), "proof! macro should be removed");
    assert!(!output.contains("assert("), "assert() should be removed");

    // Verify calc! macros are removed
    assert!(!output.contains("calc!"), "calc! macro should be removed");

    // Verify executable code remains
    assert!(output.contains("fn with_proof_macro(x: u32) -> u32"));
    assert!(output.contains("x + 1"));
    assert!(output.contains("fn with_nested_proof(a: u32, b: u32) -> u32"));
    assert!(output.contains("let result = a + b;"));
    assert!(output.contains("fn multiple_proof_blocks(n: u32) -> u32"));
    assert!(output.contains("let x = n * 2;"));
    assert!(output.contains("fn with_calc(x: u32) -> u32"));
    assert!(output.contains("fn proof_and_exec_mixed(n: u32) -> u32"));
    assert!(output.contains("let a = n + 1;"));
    assert!(output.contains("let b = a * 2;"));

    println!("Output:\n{}", output);
}

#[test]
fn test_phase3_expr_proofs() {
    let input = fs::read_to_string("tests/fixtures/input/phase3_expr_proofs.rs")
        .expect("Failed to read phase3_expr_proofs.rs");

    let output = strip_source(&input, &Config::default()).expect("Failed to strip");

    // Verify proof! blocks inside expressions are removed
    assert!(
        !output.contains("proof!"),
        "proof! blocks should be removed from expressions"
    );
    assert!(!output.contains("assert("), "assert() should be removed");

    // Verify executable code remains
    assert!(output.contains("fn with_if_proof(x: u32) -> u32"));
    assert!(output.contains("if x > 10"));
    assert!(output.contains("x - 10"));

    assert!(output.contains("fn with_match_proof(x: Option<u32>) -> u32"));
    assert!(output.contains("match x"));
    assert!(output.contains("Some(v)"));

    assert!(output.contains("fn with_nested_blocks(x: u32) -> u32"));
    assert!(output.contains("let temp = x + 1;"));

    assert!(output.contains("fn mixed_statements_and_exprs"));

    println!("Output:\n{}", output);
}

#[test]
fn test_phase3_quantifiers() {
    let input = fs::read_to_string("tests/fixtures/input/phase3_quantifiers.rs")
        .expect("Failed to read phase3_quantifiers.rs");

    let output = strip_source(&input, &Config::default()).expect("Failed to strip");

    // Verify quantifiers are removed (check for usage patterns, not function names)
    assert!(
        !output.contains("forall|"),
        "forall quantifiers should be removed"
    );
    assert!(
        !output.contains("exists|"),
        "exists quantifiers should be removed"
    );
    assert!(
        !output.contains("choose|"),
        "choose quantifiers should be removed"
    );

    // Verify executable code remains
    assert!(output.contains("fn with_forall_stmt(x: u32) -> u32"));
    assert!(output.contains("x + 1"));

    assert!(output.contains("fn with_exists_stmt(x: u32) -> u32"));
    assert!(output.contains("x * 2"));

    assert!(output.contains("fn with_choose_stmt(x: u32) -> u32"));
    assert!(output.contains("x - 1"));

    assert!(output.contains("fn mixed_quantifiers(a: u32, b: u32) -> u32"));
    assert!(output.contains("let result = a + b;"));

    assert!(output.contains("fn quantifiers_in_proof_blocks(n: u32) -> u32"));
    assert!(output.contains("n + 10"));

    println!("Output:\n{}", output);
}
