#![no_main]

use libfuzzer_sys::fuzz_target;

// parse_signal is private, so we'll fuzz through the kill command interface
// by creating a mock ShellState with a job and trying to kill it
use vsh::{ShellState, commands::kill_job};

fuzz_target!(|data: &[u8]| {
    if let Ok(sig_str) = std::str::from_utf8(data) {
        // Create a shell state with a job
        // We use "." as root - if it fails, skip this iteration
        if let Ok(mut state) = ShellState::new(".") {
            state.jobs.add_job(1234, "sleep 10".to_string(), vec![1234]);

            // Fuzz signal parsing through kill_job
            // This will catch:
            // - Invalid signal names
            // - Signal number overflow
            // - Malformed signal strings
            // - Signal name variants (HUP vs SIGHUP)
            // Note: This will fail to actually send signals since the PIDs don't exist,
            // but it will still exercise the parsing logic
            let _ = kill_job(&mut state, Some(sig_str), "%1");
        }
    }
});
