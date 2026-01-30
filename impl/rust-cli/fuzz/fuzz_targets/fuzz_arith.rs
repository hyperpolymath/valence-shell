#![no_main]

use libfuzzer_sys::fuzz_target;
use vsh::arith::parse_arithmetic;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        // Arithmetic parser should handle:
        // - Malformed expressions
        // - Deeply nested parentheses
        // - Invalid operators
        // - Boundary cases for numbers
        // Note: We only fuzz parsing, not evaluation, to keep it simple
        let _ = parse_arithmetic(s);
    }
});
