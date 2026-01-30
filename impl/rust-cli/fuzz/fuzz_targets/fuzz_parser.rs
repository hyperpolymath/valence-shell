// SPDX-License-Identifier: PLMP-1.0-or-later
//! Fuzz Target: Command Parser
//!
//! Tests the parser for:
//! - Command injection attempts
//! - Malformed syntax
//! - Deep nesting
//! - Unicode handling
//! - Edge cases

#![no_main]

use libfuzzer_sys::fuzz_target;
use vsh::parser::parse_command;

fuzz_target!(|data: &[u8]| {
    // Convert fuzz input to string
    if let Ok(input) = std::str::from_utf8(data) {
        // Limit length to prevent timeouts
        if input.len() > 1000 {
            return;
        }

        // Parse command (should never crash)
        let _ = parse_command(input);

        // Parser should handle:
        // - Deep nesting: ((((((((((((((((((((((((
        // - Many quotes: """""""""""""""""""""""
        // - Shell metacharacters: ; & | $ ` \
        // - Unicode: 测试 файл αρχείο 🚀
        // - Null bytes (invalid UTF-8 filtered above)
        // - Empty input
        // - Very long tokens
    }
});
