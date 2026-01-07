use std::fs;
use std::path::Path;
use vstrip::{strip_source, Config};

/// Test that input fixtures match their expected output
#[test]
fn test_golden_files() {
    let input_dir = Path::new("tests/fixtures/input");
    let expected_dir = Path::new("tests/fixtures/expected");

    let mut test_files = Vec::new();
    for entry in fs::read_dir(input_dir).expect("Failed to read input directory") {
        let entry = entry.expect("Failed to read entry");
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) == Some("rs") {
            test_files.push(path.file_name().unwrap().to_string_lossy().to_string());
        }
    }

    test_files.sort();

    let mut passed = 0;
    let mut failed = 0;

    for filename in &test_files {
        let input_path = input_dir.join(filename);
        let expected_path = expected_dir.join(filename);

        if !expected_path.exists() {
            eprintln!("⚠️  No expected file for {}", filename);
            failed += 1;
            continue;
        }

        let input = fs::read_to_string(&input_path)
            .unwrap_or_else(|_| panic!("Failed to read {}", input_path.display()));

        let expected = fs::read_to_string(&expected_path)
            .unwrap_or_else(|_| panic!("Failed to read {}", expected_path.display()));

        let actual = strip_source(&input, &Config::default())
            .unwrap_or_else(|e| panic!("Failed to strip {}: {:?}", filename, e));

        if actual.trim() == expected.trim() {
            println!("✓ {}", filename);
            passed += 1;
        } else {
            eprintln!("✗ {} - Output mismatch!", filename);
            eprintln!("Expected:\n{}", expected);
            eprintln!("Actual:\n{}", actual);
            failed += 1;
        }
    }

    println!(
        "\n{} passed, {} failed out of {} tests",
        passed,
        failed,
        test_files.len()
    );

    assert_eq!(failed, 0, "{} golden file test(s) failed", failed);
}
