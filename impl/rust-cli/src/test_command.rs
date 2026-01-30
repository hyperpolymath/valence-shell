// SPDX-License-Identifier: PMPL-1.0-or-later
//! Test Command Implementation (POSIX test/[ built-in)
//!
//! Implements the POSIX test command for conditionals in shell scripts.
//! Used in if/while/until statements for decision making.
//!
//! # POSIX Compliance
//!
//! Supports all POSIX test operators:
//! - File tests: -f, -d, -e, -r, -w, -x, -s
//! - String tests: -z, -n, =, !=
//! - Integer comparisons: -eq, -ne, -lt, -le, -gt, -ge
//! - Logical operators: -a (AND), -o (OR), ! (NOT)
//!
//! # Exit Codes
//! - 0: Test succeeded (true)
//! - 1: Test failed (false)
//! - 2: Syntax error
//!
//! # Examples
//!
//! ```bash
//! test -f /etc/passwd          # True if file exists
//! [ -d /tmp ]                  # True if directory exists
//! test "$VAR" = "value"        # True if strings equal
//! [ $NUM -gt 10 ]              # True if NUM > 10
//! test -f file -a -r file      # True if file exists AND readable
//! ```

use anyhow::{bail, Context, Result};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;

/// Test expression evaluator
#[derive(Debug, Clone, PartialEq)]
pub enum TestExpr {
    /// File tests
    FileExists(String),
    FileIsRegular(String),
    FileIsDirectory(String),
    FileIsReadable(String),
    FileIsWritable(String),
    FileIsExecutable(String),
    FileNotEmpty(String), // -s

    /// String tests
    StringEmpty(String),    // -z
    StringNotEmpty(String), // -n
    StringEqual(String, String),
    StringNotEqual(String, String),

    /// Integer comparisons
    IntEqual(String, String),     // -eq
    IntNotEqual(String, String),  // -ne
    IntLessThan(String, String),  // -lt
    IntLessEqual(String, String), // -le
    IntGreater(String, String),   // -gt
    IntGreaterEqual(String, String), // -ge

    /// Logical operators
    Not(Box<TestExpr>),
    And(Box<TestExpr>, Box<TestExpr>),
    Or(Box<TestExpr>, Box<TestExpr>),
}

impl TestExpr {
    /// Evaluate the test expression
    ///
    /// Returns:
    /// - Ok(true) if test passes
    /// - Ok(false) if test fails
    /// - Err(_) if syntax error or evaluation error
    pub fn evaluate(&self) -> Result<bool> {
        match self {
            // File tests
            TestExpr::FileExists(path) => Ok(Path::new(path).exists()),

            TestExpr::FileIsRegular(path) => {
                Ok(Path::new(path).is_file())
            }

            TestExpr::FileIsDirectory(path) => {
                Ok(Path::new(path).is_dir())
            }

            TestExpr::FileIsReadable(path) => {
                let path = Path::new(path);
                if !path.exists() {
                    return Ok(false);
                }
                let metadata = fs::metadata(path)?;
                let permissions = metadata.permissions();
                Ok(permissions.mode() & 0o444 != 0)
            }

            TestExpr::FileIsWritable(path) => {
                let path = Path::new(path);
                if !path.exists() {
                    return Ok(false);
                }
                let metadata = fs::metadata(path)?;
                let permissions = metadata.permissions();
                Ok(permissions.mode() & 0o222 != 0)
            }

            TestExpr::FileIsExecutable(path) => {
                let path = Path::new(path);
                if !path.exists() {
                    return Ok(false);
                }
                let metadata = fs::metadata(path)?;
                let permissions = metadata.permissions();
                Ok(permissions.mode() & 0o111 != 0)
            }

            TestExpr::FileNotEmpty(path) => {
                let path = Path::new(path);
                if !path.exists() {
                    return Ok(false);
                }
                let metadata = fs::metadata(path)?;
                Ok(metadata.len() > 0)
            }

            // String tests
            TestExpr::StringEmpty(s) => Ok(s.is_empty()),

            TestExpr::StringNotEmpty(s) => Ok(!s.is_empty()),

            TestExpr::StringEqual(a, b) => Ok(a == b),

            TestExpr::StringNotEqual(a, b) => Ok(a != b),

            // Integer comparisons
            TestExpr::IntEqual(a, b) => {
                let a_val = a.parse::<i64>()
                    .context("Invalid integer for -eq comparison")?;
                let b_val = b.parse::<i64>()
                    .context("Invalid integer for -eq comparison")?;
                Ok(a_val == b_val)
            }

            TestExpr::IntNotEqual(a, b) => {
                let a_val = a.parse::<i64>()?;
                let b_val = b.parse::<i64>()?;
                Ok(a_val != b_val)
            }

            TestExpr::IntLessThan(a, b) => {
                let a_val = a.parse::<i64>()?;
                let b_val = b.parse::<i64>()?;
                Ok(a_val < b_val)
            }

            TestExpr::IntLessEqual(a, b) => {
                let a_val = a.parse::<i64>()?;
                let b_val = b.parse::<i64>()?;
                Ok(a_val <= b_val)
            }

            TestExpr::IntGreater(a, b) => {
                let a_val = a.parse::<i64>()?;
                let b_val = b.parse::<i64>()?;
                Ok(a_val > b_val)
            }

            TestExpr::IntGreaterEqual(a, b) => {
                let a_val = a.parse::<i64>()?;
                let b_val = b.parse::<i64>()?;
                Ok(a_val >= b_val)
            }

            // Logical operators
            TestExpr::Not(expr) => {
                Ok(!expr.evaluate()?)
            }

            TestExpr::And(left, right) => {
                // Short-circuit evaluation
                Ok(left.evaluate()? && right.evaluate()?)
            }

            TestExpr::Or(left, right) => {
                // Short-circuit evaluation
                Ok(left.evaluate()? || right.evaluate()?)
            }
        }
    }
}

/// Parse test command arguments into TestExpr
///
/// # Arguments
/// * `args` - Command arguments (excluding "test" or "[")
/// * `is_bracket` - True if invoked as "[" (requires trailing "]")
///
/// # Returns
/// Parsed TestExpr or error if syntax invalid
pub fn parse_test_expr(args: &[String], is_bracket: bool) -> Result<TestExpr> {
    // Handle "[" syntax - must end with "]"
    let args = if is_bracket {
        if args.is_empty() || args.last().unwrap() != "]" {
            bail!("test: missing ']'");
        }
        &args[..args.len() - 1] // Remove trailing "]"
    } else {
        args
    };

    if args.is_empty() {
        // Empty test is always false
        return Ok(TestExpr::StringEmpty(String::new()));
    }

    // Parse expression
    parse_or_expr(args, 0).map(|(expr, _)| expr)
}

/// Parse OR expression (lowest precedence)
fn parse_or_expr(args: &[String], start: usize) -> Result<(TestExpr, usize)> {
    let (mut left, mut pos) = parse_and_expr(args, start)?;

    while pos < args.len() && args[pos] == "-o" {
        pos += 1; // Skip "-o"
        let (right, new_pos) = parse_and_expr(args, pos)?;
        left = TestExpr::Or(Box::new(left), Box::new(right));
        pos = new_pos;
    }

    Ok((left, pos))
}

/// Parse AND expression (medium precedence)
fn parse_and_expr(args: &[String], start: usize) -> Result<(TestExpr, usize)> {
    let (mut left, mut pos) = parse_unary_expr(args, start)?;

    while pos < args.len() && args[pos] == "-a" {
        pos += 1; // Skip "-a"
        let (right, new_pos) = parse_unary_expr(args, pos)?;
        left = TestExpr::And(Box::new(left), Box::new(right));
        pos = new_pos;
    }

    Ok((left, pos))
}

/// Parse unary expression (highest precedence)
fn parse_unary_expr(args: &[String], start: usize) -> Result<(TestExpr, usize)> {
    if start >= args.len() {
        bail!("test: missing argument");
    }

    // Handle negation
    if args[start] == "!" {
        let (expr, pos) = parse_unary_expr(args, start + 1)?;
        return Ok((TestExpr::Not(Box::new(expr)), pos));
    }

    // Handle parentheses (if we add them later)
    // For now, parse primary expressions

    parse_primary_expr(args, start)
}

/// Parse primary expression
fn parse_primary_expr(args: &[String], start: usize) -> Result<(TestExpr, usize)> {
    if start >= args.len() {
        bail!("test: missing argument");
    }

    let arg = &args[start];

    // Unary operators
    match arg.as_str() {
        "-e" => {
            if start + 1 >= args.len() {
                bail!("test: -e requires argument");
            }
            return Ok((TestExpr::FileExists(args[start + 1].clone()), start + 2));
        }
        "-f" => {
            if start + 1 >= args.len() {
                bail!("test: -f requires argument");
            }
            return Ok((TestExpr::FileIsRegular(args[start + 1].clone()), start + 2));
        }
        "-d" => {
            if start + 1 >= args.len() {
                bail!("test: -d requires argument");
            }
            return Ok((TestExpr::FileIsDirectory(args[start + 1].clone()), start + 2));
        }
        "-r" => {
            if start + 1 >= args.len() {
                bail!("test: -r requires argument");
            }
            return Ok((TestExpr::FileIsReadable(args[start + 1].clone()), start + 2));
        }
        "-w" => {
            if start + 1 >= args.len() {
                bail!("test: -w requires argument");
            }
            return Ok((TestExpr::FileIsWritable(args[start + 1].clone()), start + 2));
        }
        "-x" => {
            if start + 1 >= args.len() {
                bail!("test: -x requires argument");
            }
            return Ok((TestExpr::FileIsExecutable(args[start + 1].clone()), start + 2));
        }
        "-s" => {
            if start + 1 >= args.len() {
                bail!("test: -s requires argument");
            }
            return Ok((TestExpr::FileNotEmpty(args[start + 1].clone()), start + 2));
        }
        "-z" => {
            if start + 1 >= args.len() {
                bail!("test: -z requires argument");
            }
            return Ok((TestExpr::StringEmpty(args[start + 1].clone()), start + 2));
        }
        "-n" => {
            if start + 1 >= args.len() {
                bail!("test: -n requires argument");
            }
            return Ok((TestExpr::StringNotEmpty(args[start + 1].clone()), start + 2));
        }
        _ => {}
    }

    // Binary operators
    if start + 2 < args.len() {
        let op = &args[start + 1];
        let left = args[start].clone();
        let right = args[start + 2].clone();

        match op.as_str() {
            "=" => return Ok((TestExpr::StringEqual(left, right), start + 3)),
            "!=" => return Ok((TestExpr::StringNotEqual(left, right), start + 3)),
            "-eq" => return Ok((TestExpr::IntEqual(left, right), start + 3)),
            "-ne" => return Ok((TestExpr::IntNotEqual(left, right), start + 3)),
            "-lt" => return Ok((TestExpr::IntLessThan(left, right), start + 3)),
            "-le" => return Ok((TestExpr::IntLessEqual(left, right), start + 3)),
            "-gt" => return Ok((TestExpr::IntGreater(left, right), start + 3)),
            "-ge" => return Ok((TestExpr::IntGreaterEqual(left, right), start + 3)),
            _ => {}
        }
    }

    // Single argument - test if non-empty string
    Ok((TestExpr::StringNotEmpty(args[start].clone()), start + 1))
}

/// Execute test command
///
/// # Returns
/// - Ok(0) if test passes (true)
/// - Ok(1) if test fails (false)
/// - Err(_) if syntax error (should return exit code 2)
pub fn execute_test(args: &[String], is_bracket: bool) -> Result<i32> {
    let expr = parse_test_expr(args, is_bracket)?;
    let result = expr.evaluate()?;
    Ok(if result { 0 } else { 1 })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::Write;
    use tempfile::TempDir;

    #[test]
    fn test_file_exists() {
        let temp = TempDir::new().unwrap();
        let file_path = temp.path().join("test.txt");
        File::create(&file_path).unwrap();

        let expr = TestExpr::FileExists(file_path.to_str().unwrap().to_string());
        assert!(expr.evaluate().unwrap());

        let expr = TestExpr::FileExists("/nonexistent/file".to_string());
        assert!(!expr.evaluate().unwrap());
    }

    #[test]
    fn test_file_is_regular() {
        let temp = TempDir::new().unwrap();
        let file_path = temp.path().join("test.txt");
        File::create(&file_path).unwrap();

        let expr = TestExpr::FileIsRegular(file_path.to_str().unwrap().to_string());
        assert!(expr.evaluate().unwrap());

        let expr = TestExpr::FileIsRegular(temp.path().to_str().unwrap().to_string());
        assert!(!expr.evaluate().unwrap()); // Directory, not regular file
    }

    #[test]
    fn test_file_is_directory() {
        let temp = TempDir::new().unwrap();

        let expr = TestExpr::FileIsDirectory(temp.path().to_str().unwrap().to_string());
        assert!(expr.evaluate().unwrap());

        let expr = TestExpr::FileIsDirectory("/nonexistent".to_string());
        assert!(!expr.evaluate().unwrap());
    }

    #[test]
    fn test_string_empty() {
        assert!(TestExpr::StringEmpty("".to_string()).evaluate().unwrap());
        assert!(!TestExpr::StringEmpty("text".to_string()).evaluate().unwrap());
    }

    #[test]
    fn test_string_equal() {
        let expr = TestExpr::StringEqual("hello".to_string(), "hello".to_string());
        assert!(expr.evaluate().unwrap());

        let expr = TestExpr::StringEqual("hello".to_string(), "world".to_string());
        assert!(!expr.evaluate().unwrap());
    }

    #[test]
    fn test_int_comparisons() {
        assert!(TestExpr::IntEqual("42".to_string(), "42".to_string()).evaluate().unwrap());
        assert!(!TestExpr::IntEqual("42".to_string(), "43".to_string()).evaluate().unwrap());

        assert!(TestExpr::IntLessThan("10".to_string(), "20".to_string()).evaluate().unwrap());
        assert!(!TestExpr::IntLessThan("20".to_string(), "10".to_string()).evaluate().unwrap());

        assert!(TestExpr::IntGreater("20".to_string(), "10".to_string()).evaluate().unwrap());
        assert!(!TestExpr::IntGreater("10".to_string(), "20".to_string()).evaluate().unwrap());
    }

    #[test]
    fn test_logical_not() {
        let expr = TestExpr::Not(Box::new(TestExpr::StringEmpty("".to_string())));
        assert!(!expr.evaluate().unwrap()); // NOT(true) = false

        let expr = TestExpr::Not(Box::new(TestExpr::StringEmpty("text".to_string())));
        assert!(expr.evaluate().unwrap()); // NOT(false) = true
    }

    #[test]
    fn test_logical_and() {
        let expr = TestExpr::And(
            Box::new(TestExpr::StringNotEmpty("text".to_string())),
            Box::new(TestExpr::IntEqual("1".to_string(), "1".to_string())),
        );
        assert!(expr.evaluate().unwrap()); // true AND true = true

        let expr = TestExpr::And(
            Box::new(TestExpr::StringEmpty("".to_string())),
            Box::new(TestExpr::IntEqual("1".to_string(), "1".to_string())),
        );
        assert!(!expr.evaluate().unwrap()); // true AND false = false
    }

    #[test]
    fn test_logical_or() {
        let expr = TestExpr::Or(
            Box::new(TestExpr::StringEmpty("".to_string())),
            Box::new(TestExpr::IntEqual("1".to_string(), "2".to_string())),
        );
        assert!(expr.evaluate().unwrap()); // true OR false = true

        let expr = TestExpr::Or(
            Box::new(TestExpr::StringEmpty("text".to_string())),
            Box::new(TestExpr::IntEqual("1".to_string(), "2".to_string())),
        );
        assert!(!expr.evaluate().unwrap()); // false OR false = false
    }

    #[test]
    fn test_parse_simple_file_test() {
        let args = vec!["-f".to_string(), "/etc/passwd".to_string()];
        let expr = parse_test_expr(&args, false).unwrap();
        assert_eq!(expr, TestExpr::FileIsRegular("/etc/passwd".to_string()));
    }

    #[test]
    fn test_parse_string_comparison() {
        let args = vec!["hello".to_string(), "=".to_string(), "world".to_string()];
        let expr = parse_test_expr(&args, false).unwrap();
        assert_eq!(expr, TestExpr::StringEqual("hello".to_string(), "world".to_string()));
    }

    #[test]
    fn test_parse_bracket_syntax() {
        let args = vec!["-f".to_string(), "/tmp".to_string(), "]".to_string()];
        let expr = parse_test_expr(&args, true).unwrap();
        assert_eq!(expr, TestExpr::FileIsRegular("/tmp".to_string()));
    }

    #[test]
    fn test_parse_bracket_missing_close() {
        let args = vec!["-f".to_string(), "/tmp".to_string()];
        let result = parse_test_expr(&args, true);
        assert!(result.is_err());
    }

    #[test]
    fn test_execute_test_true() {
        let args = vec!["-n".to_string(), "text".to_string()];
        let exit_code = execute_test(&args, false).unwrap();
        assert_eq!(exit_code, 0); // Success = 0
    }

    #[test]
    fn test_execute_test_false() {
        let args = vec!["-z".to_string(), "text".to_string()];
        let exit_code = execute_test(&args, false).unwrap();
        assert_eq!(exit_code, 1); // Failure = 1
    }
}
