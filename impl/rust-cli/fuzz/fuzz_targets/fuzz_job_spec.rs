#![no_main]

use libfuzzer_sys::fuzz_target;
use vsh::job::{JobTable, JobState};

fuzz_target!(|data: &[u8]| {
    if let Ok(spec) = std::str::from_utf8(data) {
        // Create a job table with some test jobs
        let mut table = JobTable::new();
        table.add_job(1234, "sleep 10".to_string(), vec![1234]);
        table.add_job(5678, "ls -la".to_string(), vec![5678]);
        table.add_job(9012, "grep test".to_string(), vec![9012]);

        // Fuzz job specification parsing
        // This will catch:
        // - Parsing bugs in %1, %+, %-, %name, %?pattern
        // - Integer overflow in job IDs
        // - Pattern matching edge cases
        // - Empty/invalid specifications
        let _ = table.get_job(spec);
    }
});
