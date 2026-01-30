# Phase 6 Milestone 10: Job Control

**Version**: 0.14.0
**Status**: In Progress
**Date**: 2026-01-29

---

## Overview

Implement POSIX job control for background jobs, job management, and signal handling. This allows users to run commands in the background, suspend/resume jobs, and switch between foreground/background execution.

## Syntax

### Background Jobs (`&`)

```bash
# Run command in background
sleep 10 &
[1] 12345

# Multiple background jobs
find / -name "*.log" 2>/dev/null &
tar czf backup.tar.gz /data &

# Background pipeline
cat file | grep pattern | sort &
```

### Job Management Commands

```bash
# List all jobs
jobs
[1]   Running                 sleep 10 &
[2]-  Running                 find / -name "*.log" 2>/dev/null &
[3]+  Stopped                 vim file.txt

# Bring job to foreground
fg %1           # Foreground job 1
fg              # Foreground most recent job (+ marker)

# Continue job in background
bg %2           # Resume job 2 in background
bg              # Resume most recent stopped job

# Kill a job
kill %1         # Send SIGTERM to job 1
kill -9 %2      # Send SIGKILL to job 2
```

### Job Specifications

```bash
%1              # Job number 1
%find           # Job with command starting with "find"
%?pattern       # Job with "pattern" in command
%%              # Current job (+ marker)
%+              # Current job
%-              # Previous job (- marker)
```

### Keyboard Shortcuts

- **Ctrl+Z**: Suspend foreground job (send SIGTSTP)
- **Ctrl+C**: Terminate foreground job (send SIGINT)
- **Ctrl+D**: EOF (not a signal)

## POSIX Compliance

**From POSIX.1-2017 Section 2.12:**

> Job control allows the user to selectively stop (suspend) and continue (resume) execution of processes.
>
> A job is a set of processes comprising a pipeline, and any processes descended from it, that are all in the same process group.
>
> At most one job can be the foreground job. The foreground job has access to the terminal for I/O. Other jobs run in the background.

**Key Requirements:**
1. Each job is a process group (setpgid)
2. Foreground job controls the terminal (tcsetpgrp)
3. Background jobs receive SIGTTIN/SIGTTOU if they try to read/write terminal
4. Shell must handle SIGCHLD to detect job state changes
5. Shell must handle SIGTSTP (Ctrl+Z) to suspend foreground job

## Implementation Plan

### 1. Job State Management

**Add `job.rs` module:**

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum JobState {
    Running,
    Stopped,
    Done,
}

#[derive(Debug, Clone)]
pub struct Job {
    pub id: usize,
    pub pgid: i32,              // Process group ID
    pub command: String,        // Command string for display
    pub state: JobState,
    pub pids: Vec<i32>,         // PIDs in this job (for pipelines)
}

pub struct JobTable {
    jobs: Vec<Job>,
    next_id: usize,
    current_job: Option<usize>,   // %+ marker
    previous_job: Option<usize>,  // %- marker
}

impl JobTable {
    pub fn add_job(&mut self, pgid: i32, command: String, pids: Vec<i32>) -> usize;
    pub fn get_job(&self, spec: &str) -> Option<&Job>;
    pub fn get_job_mut(&mut self, spec: &str) -> Option<&mut Job>;
    pub fn remove_job(&mut self, id: usize);
    pub fn list_jobs(&self) -> Vec<String>;
    pub fn update_job_state(&mut self, pgid: i32, state: JobState);
}
```

### 2. Process Group Management

**Add to external command execution:**

```rust
pub fn execute_external_background(
    program: &str,
    args: &[String],
    redirects: &[Redirection],
    state: &mut ShellState,
) -> Result<i32> {
    // Create process group for job
    let child = Command::new(program)
        .args(args)
        .process_group(0)  // Create new process group
        .stdin(Stdio::null())  // Background jobs don't get stdin
        .stdout(/* handle redirects */)
        .stderr(/* handle redirects */)
        .spawn()?;

    let pgid = child.id() as i32;
    let job_id = state.jobs.add_job(pgid, command_string, vec![pgid]);

    println!("[{}] {}", job_id, pgid);

    // Don't wait for background job
    // Job table will track it

    Ok(0)
}
```

### 3. Signal Handling

**Add signal handlers in `main.rs`:**

```rust
use signal_hook::{consts::signal::*, iterator::Signals};

fn setup_signal_handlers(state: Arc<Mutex<ShellState>>) -> Result<()> {
    let mut signals = Signals::new(&[SIGCHLD, SIGTSTP, SIGINT])?;

    std::thread::spawn(move || {
        for sig in signals.forever() {
            match sig {
                SIGCHLD => {
                    // Child process state changed
                    handle_sigchld(&state);
                }
                SIGTSTP => {
                    // Ctrl+Z pressed - suspend foreground job
                    handle_sigtstp(&state);
                }
                SIGINT => {
                    // Ctrl+C pressed - handled elsewhere
                    // Shell itself should not exit on SIGINT
                }
                _ => {}
            }
        }
    });

    Ok(())
}

fn handle_sigchld(state: &Arc<Mutex<ShellState>>) {
    // Use waitpid with WNOHANG to check all jobs
    loop {
        match unsafe { libc::waitpid(-1, &mut status, libc::WNOHANG | libc::WUNTRACED) } {
            0 => break,  // No more children
            -1 => break, // Error
            pid => {
                // Update job state based on status
                let state = state.lock().unwrap();
                if libc::WIFEXITED(status) || libc::WIFSIGNALED(status) {
                    state.jobs.update_job_state(pid, JobState::Done);
                } else if libc::WIFSTOPPED(status) {
                    state.jobs.update_job_state(pid, JobState::Stopped);
                }
            }
        }
    }
}
```

### 4. Built-in Commands

**Add to `parser.rs` Command enum:**

```rust
pub enum Command {
    // ... existing commands ...

    Jobs {
        long: bool,      // -l flag: show PIDs
    },

    Fg {
        job_spec: Option<String>,  // %1, %find, etc.
    },

    Bg {
        job_spec: Option<String>,
    },

    Kill {
        signal: Option<String>,  // -SIGTERM, -9, etc.
        job_spec: String,
    },
}
```

**Implement built-ins in `builtin.rs`:**

```rust
pub fn builtin_jobs(state: &ShellState, long: bool) -> Result<()> {
    let lines = state.jobs.list_jobs();
    for line in lines {
        println!("{}", line);
    }
    Ok(())
}

pub fn builtin_fg(state: &mut ShellState, job_spec: Option<&str>) -> Result<()> {
    let spec = job_spec.unwrap_or("%+");  // Default to current job
    let job = state.jobs.get_job_mut(spec)
        .ok_or_else(|| anyhow!("No such job: {}", spec))?;

    // Move job to foreground
    unsafe {
        libc::tcsetpgrp(libc::STDIN_FILENO, job.pgid);
    }

    // If stopped, send SIGCONT
    if job.state == JobState::Stopped {
        unsafe {
            libc::kill(-job.pgid, libc::SIGCONT);
        }
    }

    job.state = JobState::Running;

    // Wait for job to complete or stop
    let mut status = 0;
    unsafe {
        libc::waitpid(-job.pgid, &mut status, libc::WUNTRACED);
    }

    // Return terminal to shell
    unsafe {
        let shell_pgid = libc::getpgrp();
        libc::tcsetpgrp(libc::STDIN_FILENO, shell_pgid);
    }

    // Update job state
    if libc::WIFSTOPPED(status) {
        job.state = JobState::Stopped;
    } else {
        state.jobs.remove_job(job.id);
    }

    Ok(())
}

pub fn builtin_bg(state: &mut ShellState, job_spec: Option<&str>) -> Result<()> {
    let spec = job_spec.unwrap_or("%+");
    let job = state.jobs.get_job_mut(spec)
        .ok_or_else(|| anyhow!("No such job: {}", spec))?;

    if job.state != JobState::Stopped {
        return Err(anyhow!("Job is not stopped"));
    }

    // Send SIGCONT to resume in background
    unsafe {
        libc::kill(-job.pgid, libc::SIGCONT);
    }

    job.state = JobState::Running;
    println!("[{}] {} &", job.id, job.command);

    Ok(())
}
```

### 5. Terminal Control

**Initialize shell as session leader:**

```rust
pub fn init_shell_terminal() -> Result<()> {
    // Make shell its own process group
    unsafe {
        libc::setpgid(0, 0);
    }

    // Take control of terminal
    let shell_pgid = unsafe { libc::getpgrp() };
    unsafe {
        libc::tcsetpgrp(libc::STDIN_FILENO, shell_pgid);
    }

    // Ignore job control signals in shell
    unsafe {
        libc::signal(libc::SIGINT, libc::SIG_IGN);
        libc::signal(libc::SIGQUIT, libc::SIG_IGN);
        libc::signal(libc::SIGTSTP, libc::SIG_IGN);
        libc::signal(libc::SIGTTIN, libc::SIG_IGN);
        libc::signal(libc::SIGTTOU, libc::SIG_IGN);
    }

    Ok(())
}
```

### 6. Background Job Execution

**Update command execution:**

```rust
pub fn execute_command(cmd: &Command, state: &mut ShellState) -> Result<i32> {
    match cmd {
        Command::External { program, args, redirects, background } => {
            if *background {
                execute_external_background(program, args, redirects, state)
            } else {
                execute_external_foreground(program, args, redirects, state)
            }
        }
        // ... other commands ...
    }
}
```

**Add background flag to External command:**

```rust
External {
    program: String,
    args: Vec<String>,
    redirects: Vec<Redirection>,
    background: bool,  // New field
},
```

## Testing Strategy

### Unit Tests

```rust
#[test]
fn test_job_table_add() {
    let mut jobs = JobTable::new();
    let id = jobs.add_job(1234, "sleep 10".to_string(), vec![1234]);
    assert_eq!(id, 1);
    assert_eq!(jobs.get_job("%1").unwrap().pgid, 1234);
}

#[test]
fn test_job_spec_parsing() {
    let mut jobs = JobTable::new();
    jobs.add_job(1234, "sleep 10".to_string(), vec![1234]);
    jobs.add_job(5678, "find / -name test".to_string(), vec![5678]);

    assert!(jobs.get_job("%1").is_some());
    assert!(jobs.get_job("%sleep").is_some());
    assert!(jobs.get_job("%?find").is_some());
}

#[test]
fn test_job_state_transitions() {
    let mut jobs = JobTable::new();
    let id = jobs.add_job(1234, "sleep 10".to_string(), vec![1234]);

    let job = jobs.get_job_mut(&format!("%{}", id)).unwrap();
    assert_eq!(job.state, JobState::Running);

    jobs.update_job_state(1234, JobState::Stopped);
    assert_eq!(jobs.get_job(&format!("%{}", id)).unwrap().state, JobState::Stopped);
}
```

### Integration Tests

```bash
# Background job
vsh> sleep 5 &
[1] 12345
vsh> jobs
[1]+  Running                 sleep 5 &

# Suspend and resume
vsh> sleep 30
^Z
[1]+  Stopped                 sleep 30
vsh> bg
[1]+ sleep 30 &
vsh> fg
sleep 30

# Multiple jobs
vsh> sleep 10 &
[1] 12345
vsh> sleep 20 &
[2] 12346
vsh> jobs
[1]-  Running                 sleep 10 &
[2]+  Running                 sleep 20 &
```

## Edge Cases

1. **Job with no controlling terminal**: Background jobs should handle SIGTTIN/SIGTTOU
2. **Orphaned process groups**: Handle parent shell exit
3. **Pipeline as job**: All stages in same process group
4. **Stopped job with output**: Should buffer or redirect
5. **Multiple Ctrl+Z**: Shell should not be stopped
6. **Job completion while in foreground**: Clean up properly

## Platform Compatibility

**Unix/Linux:**
- Full support via POSIX signals and process groups
- tcsetpgrp, setpgid, kill, waitpid

**macOS:**
- Full support (same as Linux)

**Windows:**
- ❌ Not supported - Windows lacks process groups and POSIX signals
- Would require Win32 Job Objects and different API

## Deferred Features

**For later:**
1. **Job arrays**: `jobs -p` to get PIDs
2. **disown**: Remove job from job table
3. **wait**: Wait for specific job
4. **Suspended job notification**: Notify when job stops
5. **Background job completion notification**: "Done" messages

## Success Criteria

- [ ] Parse `&` for background jobs
- [ ] Create process groups for jobs
- [ ] Implement `jobs` command
- [ ] Implement `fg` command
- [ ] Implement `bg` command
- [ ] Handle SIGCHLD to track job status
- [ ] Handle SIGTSTP (Ctrl+Z) to suspend jobs
- [ ] Update job state (Running/Stopped/Done)
- [ ] Job specifications (%1, %+, %-, etc.)
- [ ] Terminal control (tcsetpgrp)
- [ ] All unit tests pass
- [ ] Integration tests pass
- [ ] Documentation complete

## Dependencies

```toml
[dependencies]
# Signal handling
signal-hook = "0.3"

# Already have libc for process management
libc = "0.2"
```

## Proven Integration (Future)

**Current** (Rust):
```rust
unsafe { libc::kill(-pgid, libc::SIGCONT) }
```

**Future** (Proven SafeJob):
```rust
extern "C" {
    fn idris_send_signal_to_group(pgid: i32, sig: i32) -> i32;
}
```

**Benefits**:
- ✅ Signal delivery proven correct
- ✅ Process group operations proven safe
- ✅ Race conditions in job state updates proven impossible
- ✅ Terminal control proven deadlock-free

See: `proven/src/Proven/SafeJob.idr` (to be created)

---

**Next Steps:**
1. Create `src/job.rs` with JobTable
2. Add signal handling setup
3. Add background flag to Command::External
4. Implement `jobs`, `fg`, `bg` built-ins
5. Update external command execution
6. Write comprehensive tests
7. Update version to 0.14.0
