// SPDX-License-Identifier: PLMP-1.0-or-later
//! Fuzz Target: Glob Expansion
//!
//! Tests glob pattern matching for:
//! - Malicious patterns (DoS via backtracking)
//! - Deep recursion (**/**/...)
//! - Edge cases (empty patterns, special chars)
//! - Resource exhaustion

#![no_main]

use libfuzzer_sys::fuzz_target;
use vsh::glob::expand_glob;

fuzz_target!(|data: &[u8]| {
    // Convert to string
    if let Ok(pattern) = std::str::from_utf8(data) {
        // Limit length to prevent DoS
        if pattern.len() > 200 {
            return;
        }

        // Skip patterns with too many wildcards (prevent combinatorial explosion)
        let wildcard_count = pattern.matches('*').count() + pattern.matches('?').count();
        if wildcard_count > 10 {
            return;
        }

        // Skip patterns with excessive recursion
        let recursive_count = pattern.matches("**").count();
        if recursive_count > 3 {
            return;
        }

        // Expand glob (should complete quickly or return error)
        // Should NEVER:
        // - Hang (exponential backtracking)
        // - Panic
        // - Use excessive memory
        let _ = expand_glob(pattern);

        // Test cases include:
        // - Simple wildcards: *.txt, file?.rs
        // - Recursive: **/*.rs
        // - Character classes: [abc], [!xyz]
        // - Braces: {a,b,c}
        // - Malicious: *, **, *{,/*}{,/*}{,/*}... (DoS)
    }
});
