// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Job Control
//!
//! Manages background jobs, process groups, and job state tracking.
//!
//! # Features
//!
//! - Job state tracking (Running, Stopped, Done)
//! - Process group management
//! - Job specifications (%1, %+, %-, %name, %?pattern)
//! - Current and previous job markers

use crate::process_sub::ProcessSubstitution;

/// Job state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JobState {
    /// Job is currently running
    Running,
    /// Job is stopped (suspended via SIGTSTP)
    Stopped,
    /// Job has completed
    Done,
}

impl std::fmt::Display for JobState {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            JobState::Running => write!(f, "Running"),
            JobState::Stopped => write!(f, "Stopped"),
            JobState::Done => write!(f, "Done"),
        }
    }
}

/// A job (command or pipeline running in background or suspended)
#[derive(Debug, Clone)]
pub struct Job {
    /// Job ID (1, 2, 3, ...)
    pub id: usize,
    /// Process group ID
    pub pgid: i32,
    /// Command string for display
    pub command: String,
    /// Current job state
    pub state: JobState,
    /// PIDs in this job (for pipelines)
    pub pids: Vec<i32>,
    /// PIDs of this job that have been reaped (ended and collected)
    reaped: Vec<i32>,
}

/// A job that has ended, with the process substitutions it still held.
#[derive(Debug)]
pub struct FinishedJob {
    /// Job ID
    pub id: usize,
    /// Command string for display
    pub command: String,
    /// The substitutions to release now that nothing can open them
    pub process_subs: Vec<ProcessSubstitution>,
}

/// Job table managing all jobs
#[derive(Debug)]
pub struct JobTable {
    jobs: Vec<Job>,
    next_id: usize,
    current_job_id: Option<usize>,  // %+ marker
    previous_job_id: Option<usize>, // %- marker
    /// Process substitutions that a job may still open, by job id. They live
    /// here, not in [`Job`], because a substitution cannot be cloned.
    process_subs: std::collections::HashMap<usize, Vec<ProcessSubstitution>>,
}

impl JobTable {
    /// Create new job table
    pub fn new() -> Self {
        Self {
            jobs: Vec::new(),
            next_id: 1,
            current_job_id: None,
            previous_job_id: None,
            process_subs: std::collections::HashMap::new(),
        }
    }

    /// Add a new job
    pub fn add_job(&mut self, pgid: i32, command: String, pids: Vec<i32>) -> usize {
        let id = self.next_id;
        self.next_id += 1;

        let job = Job {
            id,
            pgid,
            command,
            state: JobState::Running,
            pids,
            reaped: Vec::new(),
        };

        self.jobs.push(job);

        // Update current/previous markers
        if let Some(current) = self.current_job_id {
            self.previous_job_id = Some(current);
        }
        self.current_job_id = Some(id);

        id
    }

    /// Get job by specification (%1, %+, %-, %name, %?pattern)
    pub fn get_job(&self, spec: &str) -> Option<&Job> {
        if spec.is_empty() {
            return None;
        }

        if spec == "%%" || spec == "%+" {
            // Current job
            let id = self.current_job_id?;
            return self.jobs.iter().find(|j| j.id == id);
        }

        if spec == "%-" {
            // Previous job
            let id = self.previous_job_id?;
            return self.jobs.iter().find(|j| j.id == id);
        }

        // Parse job number: %1, %2, etc.
        if let Some(num_str) = spec.strip_prefix('%') {
            if let Ok(id) = num_str.parse::<usize>() {
                return self.jobs.iter().find(|j| j.id == id);
            }

            // Command prefix: %sleep, %find
            if !num_str.starts_with('?') {
                return self.jobs.iter().find(|j| {
                    let cmd = j.command.split_whitespace().next().unwrap_or("");
                    cmd.starts_with(num_str)
                });
            }

            // Pattern match: %?pattern
            if let Some(pattern) = num_str.strip_prefix('?') {
                return self.jobs.iter().find(|j| j.command.contains(pattern));
            }
        }

        None
    }

    /// Remove job from table
    pub fn remove_job(&mut self, id: usize) {
        self.jobs.retain(|j| j.id != id);
        // A substitution that is still here belongs to a job that is gone:
        // dropping it ends its child and removes its FIFO.
        self.process_subs.remove(&id);

        // Update markers if removed job was current/previous
        if self.current_job_id == Some(id) {
            self.current_job_id = self.previous_job_id;
            self.previous_job_id = None;
        } else if self.previous_job_id == Some(id) {
            self.previous_job_id = None;
        }
    }

    /// Update job state by PID or PGID
    pub fn update_job_state(&mut self, pid_or_pgid: i32, state: JobState) {
        for job in &mut self.jobs {
            if job.pgid == pid_or_pgid || job.pids.contains(&pid_or_pgid) {
                job.state = state;
                break;
            }
        }
    }

    /// List all jobs with formatting
    pub fn list_jobs(&self) -> Vec<String> {
        let mut lines = Vec::new();

        for job in &self.jobs {
            let marker = if Some(job.id) == self.current_job_id {
                "+"
            } else if Some(job.id) == self.previous_job_id {
                "-"
            } else {
                " "
            };

            let line = format!(
                "[{}]{}  {:<20} {}",
                job.id,
                marker,
                format!("{}", job.state),
                job.command
            );
            lines.push(line);
        }

        lines
    }

    /// Keep the process substitutions of a job until it ends: the job may open
    /// a FIFO at any later time, so nothing is released while it runs.
    pub fn attach_process_subs(&mut self, id: usize, subs: Vec<ProcessSubstitution>) {
        if subs.is_empty() {
            return;
        }
        self.process_subs.entry(id).or_default().extend(subs);
    }

    /// Take the process substitutions of a job, for a caller that has seen the
    /// job end (`fg` waits for it itself).
    pub fn take_process_subs(&mut self, id: usize) -> Vec<ProcessSubstitution> {
        self.process_subs.remove(&id).unwrap_or_default()
    }

    /// The `+` or `-` marker of a job, or a space.
    pub fn marker(&self, id: usize) -> char {
        if self.current_job_id == Some(id) {
            '+'
        } else if self.previous_job_id == Some(id) {
            '-'
        } else {
            ' '
        }
    }

    /// Reap the running jobs that have ended, without blocking.
    ///
    /// Each process of a running job is polled with `waitpid(WNOHANG)`. A job
    /// whose processes have all ended is marked [`JobState::Done`] and returned
    /// once, with the process substitutions it held. The job stays in the table
    /// until [`JobTable::remove_job`]. The caller releases the substitutions.
    #[cfg(unix)]
    pub fn reap_finished(&mut self) -> Vec<FinishedJob> {
        let mut finished = Vec::new();
        for job in &mut self.jobs {
            if job.state != JobState::Running {
                continue;
            }
            for &pid in &job.pids {
                if job.reaped.contains(&pid) {
                    continue;
                }
                let mut status: i32 = 0;
                // SAFETY: `status` is a live, exclusively borrowed i32 for the
                // whole call; waitpid writes the child's status into it and
                // nothing else. WNOHANG makes the call return at once.
                let reaped = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
                // 0: still running. A pid or -1 (no such child: someone else
                // already collected it): it has ended.
                if reaped != 0 {
                    job.reaped.push(pid);
                }
            }
            if job.pids.iter().all(|pid| job.reaped.contains(pid)) {
                job.state = JobState::Done;
                finished.push((job.id, job.command.clone()));
            }
        }
        finished
            .into_iter()
            .map(|(id, command)| FinishedJob {
                id,
                command,
                process_subs: self.process_subs.remove(&id).unwrap_or_default(),
            })
            .collect()
    }

    /// Job control needs Unix process groups; nothing is reaped elsewhere.
    #[cfg(not(unix))]
    pub fn reap_finished(&mut self) -> Vec<FinishedJob> {
        Vec::new()
    }

    /// Get all jobs
    pub fn jobs(&self) -> &[Job] {
        &self.jobs
    }
}

impl Default for JobTable {
    fn default() -> Self {
        Self::new()
    }
}

/// When the shell exits, release the substitutions of the jobs that have
/// ended. A job that is still running may open its FIFO later, so its
/// substitutions are left alone: dropping one would end its child and remove
/// the FIFO under the job.
// snip: a substitution of a job that still runs at exit is never released.
// Its FIFO stays in the temp directory, and its child stays blocked until the
// job opens the FIFO. The exit does not wait for the job.
impl Drop for JobTable {
    fn drop(&mut self) {
        for finished in self.reap_finished() {
            for sub in finished.process_subs {
                if let Err(e) = sub.cleanup() {
                    eprintln!("Warning: Failed to cleanup process substitution: {}", e);
                }
            }
        }
        for (_, subs) in self.process_subs.drain() {
            for sub in subs {
                sub.leave_running();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;
    use std::time::{Duration, Instant};

    /// Reap until `id` has ended, for at most ten seconds.
    fn reap_until_done(table: &mut JobTable, id: usize) -> Vec<FinishedJob> {
        let started = Instant::now();
        loop {
            let finished = table.reap_finished();
            if finished.iter().any(|job| job.id == id) {
                return finished;
            }
            assert!(
                started.elapsed() < Duration::from_secs(10),
                "job did not end"
            );
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    #[test]
    fn reap_marks_a_finished_job_done_and_returns_it() {
        // The reaper under test collects the child, so no handle is kept.
        let pid = Command::new("true").spawn().unwrap().id() as i32;
        let mut table = JobTable::new();
        let id = table.add_job(pid, "true &".to_string(), vec![pid]);
        let finished = reap_until_done(&mut table, id);
        assert_eq!(finished.len(), 1);
        assert_eq!(finished[0].command, "true &");
        assert_eq!(table.jobs()[0].state, JobState::Done);
        // A job is reported once.
        assert!(table.reap_finished().is_empty());
    }

    #[test]
    fn reap_leaves_a_running_job_alone() {
        let mut child = Command::new("sleep").arg("30").spawn().unwrap();
        let pid = child.id() as i32;
        let mut table = JobTable::new();
        table.add_job(pid, "sleep 30 &".to_string(), vec![pid]);
        assert!(table.reap_finished().is_empty());
        assert_eq!(table.jobs()[0].state, JobState::Running);
        child.kill().unwrap();
        child.wait().unwrap();
    }

    #[test]
    fn a_pipeline_job_ends_when_all_its_processes_have_ended() {
        let quick_pid = Command::new("true").spawn().unwrap().id() as i32;
        let mut slow = Command::new("sleep").arg("30").spawn().unwrap();
        let slow_pid = slow.id() as i32;
        let mut table = JobTable::new();
        table.add_job(
            quick_pid,
            "true | sleep 30 &".to_string(),
            vec![quick_pid, slow_pid],
        );
        std::thread::sleep(Duration::from_millis(200));
        assert!(table.reap_finished().is_empty());
        assert_eq!(table.jobs()[0].state, JobState::Running);
        slow.kill().unwrap();
        slow.wait().unwrap();
        let finished = reap_until_done(&mut table, 1);
        assert_eq!(finished.len(), 1);
    }

    #[test]
    fn test_add_job() {
        let mut table = JobTable::new();
        let id = table.add_job(1234, "sleep 10".to_string(), vec![1234]);
        assert_eq!(id, 1);
        assert_eq!(table.jobs.len(), 1);
    }

    #[test]
    fn test_get_job_by_number() {
        let mut table = JobTable::new();
        table.add_job(1234, "sleep 10".to_string(), vec![1234]);

        let job = table.get_job("%1");
        assert!(job.is_some());
        assert_eq!(job.unwrap().pgid, 1234);
    }

    #[test]
    fn test_get_job_current() {
        let mut table = JobTable::new();
        let id1 = table.add_job(1234, "sleep 10".to_string(), vec![1234]);
        let id2 = table.add_job(5678, "sleep 20".to_string(), vec![5678]);

        // %+ should be most recent (id2)
        let job = table.get_job("%+");
        assert!(job.is_some());
        assert_eq!(job.unwrap().id, id2);

        // %- should be previous (id1)
        let job = table.get_job("%-");
        assert!(job.is_some());
        assert_eq!(job.unwrap().id, id1);
    }

    #[test]
    fn test_get_job_by_command_prefix() {
        let mut table = JobTable::new();
        table.add_job(1234, "sleep 10".to_string(), vec![1234]);
        table.add_job(5678, "find / -name test".to_string(), vec![5678]);

        let job = table.get_job("%sleep");
        assert!(job.is_some());
        assert_eq!(job.unwrap().command, "sleep 10");

        let job = table.get_job("%find");
        assert!(job.is_some());
        assert_eq!(job.unwrap().command, "find / -name test");
    }

    #[test]
    fn test_get_job_by_pattern() {
        let mut table = JobTable::new();
        table.add_job(1234, "find / -name test".to_string(), vec![1234]);

        let job = table.get_job("%?name");
        assert!(job.is_some());
        assert_eq!(job.unwrap().command, "find / -name test");
    }

    #[test]
    fn test_remove_job() {
        let mut table = JobTable::new();
        let id = table.add_job(1234, "sleep 10".to_string(), vec![1234]);
        assert_eq!(table.jobs.len(), 1);

        table.remove_job(id);
        assert_eq!(table.jobs.len(), 0);
    }

    #[test]
    fn test_update_job_state() {
        let mut table = JobTable::new();
        table.add_job(1234, "sleep 10".to_string(), vec![1234]);

        table.update_job_state(1234, JobState::Stopped);
        let job = table.get_job("%1").unwrap();
        assert_eq!(job.state, JobState::Stopped);
    }

    #[test]
    fn test_list_jobs() {
        let mut table = JobTable::new();
        table.add_job(1234, "sleep 10".to_string(), vec![1234]);
        table.add_job(5678, "find /".to_string(), vec![5678]);

        let lines = table.list_jobs();
        assert_eq!(lines.len(), 2);
        assert!(lines[0].contains("[1]"));
        assert!(lines[1].contains("[2]"));
        assert!(lines[1].contains("+")); // Current job marker
    }
}
