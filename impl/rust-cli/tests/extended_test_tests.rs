// SPDX-License-Identifier: PMPL-1.0-or-later
//! Extended Test [[ ]] Tests (v1.1.0)
//!
//! Tests bash-style [[ ]] extended test syntax:
//! - Pattern matching: [[ $var == *.txt ]], [[ $var != pattern ]]
//! - Regex matching: [[ $var =~ ^[0-9]+$ ]]
//! - Lexical comparison: [[ $a < $b ]], [[ $a > $b ]]
//! - Modern operators: && and || instead of -a and -o
//! - No word splitting: variables don't need quotes
//! - Parentheses for grouping: [[ ( expr ) ]]

use vsh::test_command::execute_extended_test;

// ============================================================================
// Pattern Matching Tests: == and != with globs
// ============================================================================

#[test]
fn test_pattern_match_simple() {
    let args = vec!["test.txt".to_string(), "==".to_string(), "*.txt".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - matches pattern
}

#[test]
fn test_pattern_match_no_match() {
    let args = vec!["test.log".to_string(), "==".to_string(), "*.txt".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - doesn't match pattern
}

#[test]
fn test_pattern_nomatch_operator() {
    let args = vec!["test.log".to_string(), "!=".to_string(), "*.txt".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - doesn't match pattern
}

#[test]
fn test_pattern_question_mark() {
    let args = vec!["file1.txt".to_string(), "==".to_string(), "file?.txt".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - single char wildcard
}

#[test]
fn test_pattern_question_mark_no_match() {
    let args = vec!["file10.txt".to_string(), "==".to_string(), "file?.txt".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - two chars don't match single wildcard
}

#[test]
fn test_pattern_character_class() {
    let args = vec!["file1.txt".to_string(), "==".to_string(), "file[0-9].txt".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - matches character class
}

#[test]
fn test_pattern_multiple_wildcards() {
    let args = vec!["prefix-test-suffix".to_string(), "==".to_string(), "*-test-*".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - matches both wildcards
}

#[test]
fn test_pattern_exact_match() {
    let args = vec!["exact".to_string(), "==".to_string(), "exact".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - exact string match
}

#[test]
fn test_pattern_empty_string() {
    let args = vec!["".to_string(), "==".to_string(), "".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - empty matches empty
}

#[test]
fn test_pattern_wildcard_matches_empty() {
    let args = vec!["".to_string(), "==".to_string(), "*".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - * matches empty
}

// ============================================================================
// Regex Matching Tests: =~
// ============================================================================

#[test]
fn test_regex_match_digits() {
    let args = vec!["12345".to_string(), "=~".to_string(), "^[0-9]+$".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - matches digits
}

#[test]
fn test_regex_match_no_match() {
    let args = vec!["abc".to_string(), "=~".to_string(), "^[0-9]+$".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - no digits
}

#[test]
fn test_regex_email_pattern() {
    let args = vec!["test@example.com".to_string(), "=~".to_string(), "^[a-z]+@[a-z]+\\.[a-z]+$".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - matches email pattern
}

#[test]
fn test_regex_partial_match() {
    let args = vec!["test123more".to_string(), "=~".to_string(), "[0-9]+".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - contains digits (partial match)
}

#[test]
fn test_regex_anchored() {
    let args = vec!["test123".to_string(), "=~".to_string(), "^[a-z]+$".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - has digits, doesn't match letters-only
}

#[test]
fn test_regex_empty_string() {
    let args = vec!["".to_string(), "=~".to_string(), "^$".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - empty matches ^$
}

#[test]
fn test_regex_invalid_pattern() {
    let args = vec!["test".to_string(), "=~".to_string(), "[invalid(".to_string()];
    let result = execute_extended_test(&args);
    assert!(result.is_err()); // Error - invalid regex
}

// ============================================================================
// Lexical Comparison Tests: < and >
// ============================================================================

#[test]
fn test_lexical_less_than() {
    let args = vec!["apple".to_string(), "<".to_string(), "banana".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - "apple" < "banana"
}

#[test]
fn test_lexical_less_than_false() {
    let args = vec!["zebra".to_string(), "<".to_string(), "apple".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - "zebra" not < "apple"
}

#[test]
fn test_lexical_greater_than() {
    let args = vec!["zebra".to_string(), ">".to_string(), "apple".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - "zebra" > "apple"
}

#[test]
fn test_lexical_equal_strings() {
    let args = vec!["test".to_string(), "<".to_string(), "test".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - equal strings, not less than
}

#[test]
fn test_lexical_numbers_as_strings() {
    // Note: Lexical comparison, not numeric
    let args = vec!["10".to_string(), "<".to_string(), "9".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - "10" < "9" lexically (1 < 9)
}

#[test]
fn test_lexical_case_sensitive() {
    let args = vec!["Apple".to_string(), "<".to_string(), "apple".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - uppercase < lowercase in ASCII
}

// ============================================================================
// Logical Operator Tests: && and ||
// ============================================================================

#[test]
fn test_and_operator_both_true() {
    let args = vec![
        "test".to_string(), "==".to_string(), "test".to_string(),
        "&&".to_string(),
        "file.txt".to_string(), "==".to_string(), "*.txt".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - both conditions true
}

#[test]
fn test_and_operator_first_false() {
    let args = vec![
        "test".to_string(), "==".to_string(), "other".to_string(),
        "&&".to_string(),
        "file.txt".to_string(), "==".to_string(), "*.txt".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - first condition false
}

#[test]
fn test_or_operator_first_true() {
    let args = vec![
        "test".to_string(), "==".to_string(), "test".to_string(),
        "||".to_string(),
        "file".to_string(), "==".to_string(), "*.txt".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - first condition true (short-circuit)
}

#[test]
fn test_or_operator_both_false() {
    let args = vec![
        "test".to_string(), "==".to_string(), "other".to_string(),
        "||".to_string(),
        "file.log".to_string(), "==".to_string(), "*.txt".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - both conditions false
}

#[test]
fn test_multiple_and_operators() {
    let args = vec![
        "a".to_string(), "==".to_string(), "a".to_string(),
        "&&".to_string(),
        "b".to_string(), "==".to_string(), "b".to_string(),
        "&&".to_string(),
        "c".to_string(), "==".to_string(), "c".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - all three conditions true
}

#[test]
fn test_or_and_precedence() {
    // (false || true) && false = false
    let args = vec![
        "a".to_string(), "==".to_string(), "b".to_string(),  // false
        "||".to_string(),
        "c".to_string(), "==".to_string(), "c".to_string(),  // true
        "&&".to_string(),
        "d".to_string(), "==".to_string(), "e".to_string(),  // false
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - because && binds tighter than ||
}

// ============================================================================
// Negation Tests: !
// ============================================================================

#[test]
fn test_negation_simple() {
    let args = vec!["!".to_string(), "test".to_string(), "==".to_string(), "other".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - !(false) = true
}

#[test]
fn test_negation_true_expr() {
    let args = vec!["!".to_string(), "test".to_string(), "==".to_string(), "test".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - !(true) = false
}

#[test]
fn test_double_negation() {
    let args = vec![
        "!".to_string(),
        "!".to_string(),
        "test".to_string(), "==".to_string(), "test".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - !!(true) = true
}

// ============================================================================
// Parentheses Tests: ( )
// ============================================================================

#[test]
fn test_parentheses_grouping() {
    let args = vec![
        "(".to_string(),
        "a".to_string(), "==".to_string(), "a".to_string(),
        ")".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - grouped expression
}

#[test]
fn test_parentheses_with_or() {
    // (false || true) = true
    let args = vec![
        "(".to_string(),
        "a".to_string(), "==".to_string(), "b".to_string(),  // false
        "||".to_string(),
        "c".to_string(), "==".to_string(), "c".to_string(),  // true
        ")".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true
}

#[test]
fn test_parentheses_change_precedence() {
    // false || (true && false) = false
    let args = vec![
        "a".to_string(), "==".to_string(), "b".to_string(),  // false
        "||".to_string(),
        "(".to_string(),
        "c".to_string(), "==".to_string(), "c".to_string(),  // true
        "&&".to_string(),
        "d".to_string(), "==".to_string(), "e".to_string(),  // false
        ")".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - (true && false) = false, false || false = false
}

#[test]
fn test_negation_with_parentheses() {
    let args = vec![
        "!".to_string(),
        "(".to_string(),
        "a".to_string(), "==".to_string(), "a".to_string(),
        ")".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - !(true) = false
}

// ============================================================================
// File Tests (Same as Regular Test)
// ============================================================================

#[test]
fn test_file_exists_operator() {
    // Create temp file for testing
    use tempfile::NamedTempFile;
    let temp_file = NamedTempFile::new().unwrap();
    let path = temp_file.path().to_str().unwrap();

    let args = vec!["-e".to_string(), path.to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - file exists
}

#[test]
fn test_file_is_directory() {
    use tempfile::TempDir;
    let temp_dir = TempDir::new().unwrap();
    let path = temp_dir.path().to_str().unwrap();

    let args = vec!["-d".to_string(), path.to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - is directory
}

// ============================================================================
// String Tests
// ============================================================================

#[test]
fn test_string_empty() {
    let args = vec!["-z".to_string(), "".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - empty string
}

#[test]
fn test_string_not_empty() {
    let args = vec!["-n".to_string(), "text".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - not empty
}

#[test]
fn test_string_exact_equal() {
    let args = vec!["test".to_string(), "=".to_string(), "test".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - exact match
}

// ============================================================================
// Integer Comparison Tests
// ============================================================================

#[test]
fn test_int_equal() {
    let args = vec!["42".to_string(), "-eq".to_string(), "42".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true
}

#[test]
fn test_int_less_than() {
    let args = vec!["5".to_string(), "-lt".to_string(), "10".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - 5 < 10
}

// ============================================================================
// Complex Expression Tests
// ============================================================================

#[test]
fn test_pattern_and_regex_combined() {
    let args = vec![
        "test.txt".to_string(), "==".to_string(), "*.txt".to_string(),
        "&&".to_string(),
        "test".to_string(), "=~".to_string(), "^[a-z]+$".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - both match
}

#[test]
fn test_negated_pattern() {
    let args = vec![
        "!".to_string(),
        "test.log".to_string(), "==".to_string(), "*.txt".to_string(),
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - !( false) = true
}

#[test]
fn test_complex_with_parentheses() {
    // (file.txt == *.txt && test =~ ^[a-z]+$) || false = true
    let args = vec![
        "(".to_string(),
        "file.txt".to_string(), "==".to_string(), "*.txt".to_string(),
        "&&".to_string(),
        "test".to_string(), "=~".to_string(), "^[a-z]+$".to_string(),
        ")".to_string(),
        "||".to_string(),
        "a".to_string(), "==".to_string(), "b".to_string(),  // false
    ];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - first part is true
}

// ============================================================================
// Edge Cases
// ============================================================================

#[test]
fn test_empty_args() {
    let args = vec![];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - empty test is false
}

#[test]
fn test_single_string_arg() {
    let args = vec!["nonempty".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - non-empty string
}

#[test]
fn test_single_empty_string_arg() {
    let args = vec!["".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 1); // false - empty string
}

#[test]
fn test_pattern_with_spaces() {
    let args = vec!["hello world".to_string(), "==".to_string(), "hello*".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - "hello world" matches "hello*"
}

#[test]
fn test_regex_with_whitespace() {
    let args = vec!["hello world".to_string(), "=~".to_string(), "^hello\\s+world$".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - matches pattern with whitespace
}

#[test]
fn test_unclosed_parenthesis() {
    let args = vec![
        "(".to_string(),
        "a".to_string(), "==".to_string(), "a".to_string(),
        // Missing )
    ];
    let result = execute_extended_test(&args);
    assert!(result.is_err()); // Error - unclosed parenthesis
}

#[test]
fn test_unexpected_operator() {
    let args = vec!["a".to_string(), "==".to_string(), "b".to_string(), "extra".to_string()];
    let result = execute_extended_test(&args);
    assert!(result.is_err()); // Error - unexpected argument
}

// ============================================================================
// Comparison with Regular Test [ ] Behavior
// ============================================================================

#[test]
fn test_pattern_vs_literal_comparison() {
    // In [[ ]], == does pattern matching
    let args = vec!["test.txt".to_string(), "==".to_string(), "*.txt".to_string()];
    let extended_result = execute_extended_test(&args).unwrap();
    assert_eq!(extended_result, 0); // true - pattern matches

    // In [ ], = does literal string comparison
    use vsh::test_command::execute_test;
    let args_literal = vec!["test.txt".to_string(), "=".to_string(), "*.txt".to_string()];
    let literal_result = execute_test(&args_literal, false).unwrap();
    assert_eq!(literal_result, 1); // false - literal strings don't match
}

#[test]
fn test_no_word_splitting_simulation() {
    // In [[]], variables don't undergo word splitting
    // Simulated by passing strings with spaces
    let args = vec!["hello world".to_string(), "==".to_string(), "hello*".to_string()];
    let result = execute_extended_test(&args).unwrap();
    assert_eq!(result, 0); // true - pattern matches full string
}
