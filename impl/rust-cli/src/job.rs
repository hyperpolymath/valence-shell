// SPDX-License-Identifier: PLMP-1.0-or-later
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

use anyhow::{anyhow, Result};

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
}

/// Job table managing all jobs
#[derive(Debug)]
pub struct JobTable {
    jobs: Vec<Job>,
    next_id: usize,
    current_job_id: Option<usize>,   // %+ marker
    previous_job_id: Option<usize>,  // %- marker
}

impl JobTable {
    /// Create new job table
    pub fn new() -> Self {
        Self {
            jobs: Vec::new(),
            next_id: 1,
            current_job_id: None,
            previous_job_id: None,
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

    /// Get mutable job by specification
    pub fn get_job_mut(&mut self, spec: &str) -> Option<&mut Job> {
        if spec.is_empty() {
            return None;
        }

        if spec == "%%" || spec == "%+" {
            let id = self.current_job_id?;
            return self.jobs.iter_mut().find(|j| j.id == id);
        }

        if spec == "%-" {
            let id = self.previous_job_id?;
            return self.jobs.iter_mut().find(|j| j.id == id);
        }

        if let Some(num_str) = spec.strip_prefix('%') {
            if let Ok(id) = num_str.parse::<usize>() {
                return self.jobs.iter_mut().find(|j| j.id == id);
            }

            if !num_str.starts_with('?') {
                return self.jobs.iter_mut().find(|j| {
                    let cmd = j.command.split_whitespace().next().unwrap_or("");
                    cmd.starts_with(num_str)
                });
            }

            if let Some(pattern) = num_str.strip_prefix('?') {
                return self.jobs.iter_mut().find(|j| j.command.contains(pattern));
            }
        }

        None
    }

    /// Remove job from table
    pub fn remove_job(&mut self, id: usize) {
        self.jobs.retain(|j| j.id != id);

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

    /// Get all jobs
    pub fn jobs(&self) -> &[Job] {
        &self.jobs
    }

    /// Remove all done jobs
    pub fn cleanup_done_jobs(&mut self) {
        let done_ids: Vec<usize> = self.jobs
            .iter()
            .filter(|j| j.state == JobState::Done)
            .map(|j| j.id)
            .collect();

        for id in done_ids {
            self.remove_job(id);
        }
    }
}

impl Default for JobTable {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert!(lines[1].contains("+"));  // Current job marker
    }
}
