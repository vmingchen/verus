/// Preprocessor to unwrap verus! macros before parsing
///
/// The verus! macro is opaque to syn's parser, so we need to unwrap it
/// by extracting the contents between verus! { ... }
use crate::error::{Result, StripError};

/// Unwrap verus! macro blocks from source code
///
/// This is a simple text-based preprocessor that finds `verus! { ... }` blocks
/// and replaces them with just the contents `...`
pub fn unwrap_verus_macros(source: &str) -> Result<String> {
    let mut result = String::new();
    let mut chars = source.char_indices().peekable();

    while let Some((i, ch)) = chars.next() {
        // Look for "verus!"
        if ch == 'v' && source[i..].starts_with("verus!") {
            // Skip "verus!"
            for _ in 0..5 {
                chars.next();
            }

            // Skip whitespace
            while let Some(&(_, ch)) = chars.peek() {
                if ch.is_whitespace() {
                    chars.next();
                } else {
                    break;
                }
            }

            // Expect '{'
            if let Some((_, '{')) = chars.next() {
                // Find matching '}'
                let brace_start = chars.clone().next().map(|(i, _)| i).unwrap_or(source.len());

                match find_matching_brace(source, brace_start) {
                    Some(brace_end) => {
                        // Extract and add the contents (without braces)
                        let contents = &source[brace_start..brace_end];
                        result.push_str(contents);
                        result.push('\n');

                        // Skip past the closing brace
                        for (pos, _) in chars.by_ref() {
                            if pos >= brace_end {
                                break;
                            }
                        }
                    }
                    None => {
                        return Err(StripError::ConfigError {
                            message: "Unmatched braces in verus! macro".to_string(),
                        });
                    }
                }
            } else {
                result.push_str("verus!");
            }
        } else {
            result.push(ch);
        }
    }

    Ok(result)
}

/// Find the position of the matching closing brace
fn find_matching_brace(source: &str, start: usize) -> Option<usize> {
    let mut depth = 1;
    let mut in_string = false;
    let mut in_char = false;
    let mut escape_next = false;
    let mut in_comment = false;
    let mut in_block_comment = false;

    let bytes = source.as_bytes();
    let mut i = start;

    while i < bytes.len() {
        if escape_next {
            escape_next = false;
            i += 1;
            continue;
        }

        let ch = bytes[i] as char;

        // Handle comments
        if !in_string && !in_char {
            if in_block_comment {
                if i + 1 < bytes.len() && bytes[i] == b'*' && bytes[i + 1] == b'/' {
                    in_block_comment = false;
                    i += 2;
                    continue;
                }
                i += 1;
                continue;
            }

            if in_comment {
                if ch == '\n' {
                    in_comment = false;
                }
                i += 1;
                continue;
            }

            if i + 1 < bytes.len() {
                if bytes[i] == b'/' && bytes[i + 1] == b'/' {
                    in_comment = true;
                    i += 2;
                    continue;
                }
                if bytes[i] == b'/' && bytes[i + 1] == b'*' {
                    in_block_comment = true;
                    i += 2;
                    continue;
                }
            }
        }

        // Handle strings and chars
        if ch == '\\' {
            escape_next = true;
            i += 1;
            continue;
        }

        if ch == '"' && !in_char {
            in_string = !in_string;
            i += 1;
            continue;
        }

        if ch == '\'' && !in_string {
            // Distinguish between character literals ('a', '\n') and Rust lifetimes ('static, 'a)
            // Character literals: ' followed by 1-2 chars (possibly escaped), then '
            // Lifetimes: ' followed by an identifier character
            if i + 1 < bytes.len() {
                let next_ch = bytes[i + 1] as char;
                // If next char is alphanumeric or underscore, it's likely a lifetime
                // Lifetimes: 'static, 'a, 'b, '_
                if next_ch.is_alphanumeric() || next_ch == '_' {
                    // This is a lifetime, not a character literal - skip it
                    i += 1;
                    continue;
                }
            }
            // Otherwise, treat as character literal
            in_char = !in_char;
            i += 1;
            continue;
        }

        // Handle braces
        if !in_string && !in_char && !in_comment && !in_block_comment {
            if ch == '{' {
                depth += 1;
            } else if ch == '}' {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
        }

        i += 1;
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unwrap_simple_verus_macro() {
        let input = r#"
verus! {
    fn foo() -> u32 {
        42
    }
}
"#;
        let output = unwrap_verus_macros(input).unwrap();
        assert!(!output.contains("verus!"));
        assert!(output.contains("fn foo()"));
    }

    #[test]
    fn test_unwrap_nested_braces() {
        let input = r#"
verus! {
    fn foo() -> u32 {
        if true {
            42
        } else {
            0
        }
    }
}
"#;
        let output = unwrap_verus_macros(input).unwrap();
        assert!(!output.contains("verus!"));
        assert!(output.contains("if true"));
    }

    #[test]
    fn test_preserve_non_verus_code() {
        let input = r#"
use std::vec::Vec;

verus! {
    fn foo() {}
}

fn bar() {}
"#;
        let output = unwrap_verus_macros(input).unwrap();
        assert!(output.contains("use std::vec::Vec"));
        assert!(output.contains("fn bar()"));
        assert!(!output.contains("verus!"));
    }

    #[test]
    fn test_multiple_verus_blocks() {
        let input = r#"
verus! {
    fn foo() {}
}

verus! {
    fn bar() {}
}
"#;
        let output = unwrap_verus_macros(input).unwrap();
        assert!(!output.contains("verus!"));
        assert!(output.contains("fn foo()"));
        assert!(output.contains("fn bar()"));
    }
}
