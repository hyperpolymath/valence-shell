// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! A background job that ends is reaped, and its process substitutions are
//! released and removed. Each test runs the `vsh` binary with `-c`.
//!
//! A hung test would leave `sh` children that hold pipes, so every run has a
//! time limit and kills the process group of the shell when it passes.

#![cfg(target_os = "linux")]

use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use tempfile::TempDir;

struct Run {
    pid: u32,
    stdout: String,
    success: bool,
    _guard: Cleanup,
}

/// Kills the substitution children and removes the FIFOs of one shell when
/// the test ends, whether it passed or not.
struct Cleanup(u32);

impl Drop for Cleanup {
    fn drop(&mut self) {
        leftovers_cleanup(self.0);
    }
}

/// Run `vsh -c script` in `dir`; fail the test if it does not end in `secs`.
fn vsh(dir: &Path, script: &str, secs: u64) -> Run {
    // Stdout goes to a file, not a pipe: a substitution child that blocks
    // inherits the descriptor, and a pipe reader would wait for it forever.
    let out_path = dir.join(".stdout.txt");
    let mut child = Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-c")
        .arg(script)
        .current_dir(dir)
        .stdout(Stdio::from(std::fs::File::create(&out_path).unwrap()))
        .stderr(Stdio::null())
        .spawn()
        .expect("vsh runs");
    let pid = child.id();
    let guard = Cleanup(pid);
    let started = Instant::now();
    loop {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        if started.elapsed() > Duration::from_secs(secs) {
            let _ = child.kill();
            let _ = child.wait();
            panic!("`{script}` did not finish within {secs}s");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let status = child.wait().unwrap();
    Run {
        pid,
        stdout: std::fs::read_to_string(&out_path).unwrap_or_default(),
        success: status.success(),
        _guard: guard,
    }
}

/// FIFOs that the shell with this pid created.
fn fifos_of(pid: u32) -> Vec<String> {
    let prefix = format!("vsh-fifo-{pid}-");
    std::fs::read_dir("/tmp")
        .unwrap()
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .filter(|name| name.starts_with(&prefix))
        .collect()
}

/// Processes whose command line names a FIFO of the shell with this pid.
fn substitution_children_of(pid: u32) -> Vec<u32> {
    let needle = format!("vsh-fifo-{pid}-");
    let mut found = Vec::new();
    for entry in std::fs::read_dir("/proc").unwrap().flatten() {
        let name = entry.file_name().to_string_lossy().into_owned();
        let Ok(proc_pid) = name.parse::<u32>() else {
            continue;
        };
        if let Ok(cmdline) = std::fs::read(entry.path().join("cmdline")) {
            if String::from_utf8_lossy(&cmdline).contains(&needle) {
                found.push(proc_pid);
            }
        }
    }
    found
}

fn leftovers_cleanup(pid: u32) {
    for child in substitution_children_of(pid) {
        let _ = Command::new("kill")
            .arg("-9")
            .arg(child.to_string())
            .status();
    }
    for name in fifos_of(pid) {
        let _ = std::fs::remove_file(Path::new("/tmp").join(name));
    }
}

fn data_file(dir: &Path) {
    std::fs::write(dir.join("f.txt"), "data\n").unwrap();
}

#[test]
fn an_unopened_substitution_of_an_ended_job_is_released_before_the_next_command() {
    // `/bin/true` never opens the FIFO. The job ends at once; the shell must
    // reap it at the next command and release and remove the substitution,
    // not at exit.
    let dir = TempDir::new().unwrap();
    data_file(dir.path());
    let run = vsh(
        dir.path(),
        "/bin/true <(cat f.txt) &\nsleep 0.3\n/bin/true\n/bin/ls /tmp",
        20,
    );
    assert!(run.success);
    let listed: Vec<&str> = run.stdout.lines().collect();
    let prefix = format!("vsh-fifo-{}-", run.pid);
    assert!(
        !listed.iter().any(|name| name.starts_with(&prefix)),
        "the FIFO was still there at the third command: {listed:?}"
    );
    assert!(fifos_of(run.pid).is_empty(), "a FIFO is left after exit");
    assert!(
        substitution_children_of(run.pid).is_empty(),
        "the substitution child is still running"
    );
}

#[test]
fn a_late_reader_still_gets_its_input() {
    // The job opens the FIFO a second after it starts. The shell must keep
    // the substitution until the job ends.
    let dir = TempDir::new().unwrap();
    let run = vsh(
        dir.path(),
        "sh -c 'sleep 1; cat \"$1\"' sh <(pwd) > out &\nsleep 2\n/bin/true",
        20,
    );
    assert!(run.success);
    let out = std::fs::read_to_string(dir.path().join("out")).unwrap();
    let name = dir
        .path()
        .file_name()
        .unwrap()
        .to_string_lossy()
        .into_owned();
    assert!(out.trim().ends_with(&name), "out holds {out:?}");
    assert!(fifos_of(run.pid).is_empty(), "a FIFO is left after exit");
}

#[test]
fn a_job_that_ends_is_not_listed_again() {
    let dir = TempDir::new().unwrap();
    let run = vsh(dir.path(), "/bin/true &\nsleep 0.3\n/bin/true\njobs", 20);
    assert!(run.success);
    assert!(
        !run.stdout.contains("Running"),
        "an ended job is still listed as running: {}",
        run.stdout
    );
}

#[test]
fn a_read_still_gets_its_input_when_a_job_ends_during_it() {
    // The background job ends while `read` waits on stdin, so SIGCHLD
    // arrives during the read. The read must restart and get the line.
    use std::io::Write;
    let dir = TempDir::new().unwrap();
    let out_path = dir.path().join(".stdout.txt");
    let mut child = Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-c")
        .arg("sleep 0.1 &\nread x\necho \"got:$x\"")
        .current_dir(dir.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::from(std::fs::File::create(&out_path).unwrap()))
        .stderr(Stdio::null())
        .spawn()
        .expect("vsh runs");
    let _guard = Cleanup(child.id());
    std::thread::sleep(Duration::from_millis(600));
    let mut stdin = child.stdin.take().unwrap();
    stdin.write_all(b"hello\n").unwrap();
    drop(stdin);
    let started = Instant::now();
    while child.try_wait().unwrap().is_none() {
        if started.elapsed() > Duration::from_secs(10) {
            let _ = child.kill();
            let _ = child.wait();
            panic!("vsh did not finish");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let stdout = std::fs::read_to_string(&out_path).unwrap();
    assert!(stdout.contains("got:hello"), "stdout: {stdout:?}");
}

#[test]
fn a_job_that_ended_before_the_shell_exits_is_cleaned_at_exit() {
    // The job ends during the last command, so no later command reaps it:
    // the exit must release its substitution and remove the FIFO.
    let dir = TempDir::new().unwrap();
    let run = vsh(
        dir.path(),
        "sh -c 'sleep 0.3; cat \"$1\"' sh <(pwd) > late.out &\nsleep 0.8",
        10,
    );
    assert!(run.success);
    assert!(!std::fs::read_to_string(dir.path().join("late.out"))
        .unwrap()
        .is_empty());
    assert_eq!(fifos_of(run.pid), Vec::<String>::new());
}

#[test]
fn a_connected_substitution_of_an_ended_job_blocks_no_command() {
    // The writer ends at once; its >(...) reader works on for 2 seconds.
    // Later commands and the exit must not wait for it, and it must not be
    // killed: it still writes its file.
    let dir = TempDir::new().unwrap();
    let started = Instant::now();
    let run = vsh(
        dir.path(),
        "sh -c 'printf data > \"$1\"' sh >(sh -c 'sleep 2; cat > out2') &\nsleep 0.3\necho ready",
        10,
    );
    let took = started.elapsed();
    assert!(run.success);
    assert!(run.stdout.contains("ready"));
    assert!(
        took < Duration::from_millis(1500),
        "the shell waited: {took:?}"
    );
    std::thread::sleep(Duration::from_secs(3));
    assert_eq!(
        std::fs::read_to_string(dir.path().join("out2")).unwrap(),
        "data"
    );
}
