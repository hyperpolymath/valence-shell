// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Gate G0 (use): what the shell is said to do equals what this battery shows.
//!
//! Every case in `tests/conformance/battery.jsonl` is one command line with the
//! standard output and exit status that a reference shell gave for it. This
//! test starts the *built* `vsh` program on each line, in a fresh directory,
//! and compares.
//!
//! `tests/conformance/known_failing.txt` lists the cases that do not match
//! today. The list is a ratchet:
//!
//! * a case that is *not* listed and fails is a regression, and fails the test;
//! * a case that *is* listed and passes must be taken off the list, and fails
//!   the test until it is. The list can only shrink.
//!
//! What is compared, and what is not:
//!
//! * standard output, after colour codes and the shell's own `[op:…]` and
//!   `[txn:…]` receipt lines are removed;
//! * the exit status;
//! * not standard error, and not the files left behind.
//!
//! A report of every case is written to
//! `$CARGO_TARGET_TMPDIR/conformance-report.txt`.
//!
//! See `tests/conformance/README.adoc` for how to add a case.
//!
//! Linux only. The expectations were recorded on Linux, and several cases
//! use the GNU forms of `stat`, `wc` and others, which print differently
//! elsewhere.

#![cfg(target_os = "linux")]

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::os::unix::process::CommandExt;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

const BATTERY: &str = include_str!("conformance/battery.jsonl");
const KNOWN_FAILING: &str = include_str!("conformance/known_failing.txt");

/// Longest a single case may run. A case that does not finish counts as failed.
const TIME_LIMIT: Duration = Duration::from_secs(5);

/// How long the output may stay open after the shell has finished. A command
/// the shell left running can hold it open.
const OUTPUT_GRACE: Duration = Duration::from_secs(2);

/// How many cases run at once.
const WORKERS: usize = 8;

#[derive(Debug, Clone)]
struct Case {
    id: String,
    rc: i32,
    out: String,
    cmd: String,
}

#[derive(Debug)]
struct Outcome {
    id: String,
    passed: bool,
    detail: String,
}

/// Reads the battery. The first line is a comment object that carries the
/// licence header; every other line is a case. A line that is not a whole
/// case is an error, so that a case cannot drop out of the battery unseen.
fn parse_battery(text: &str) -> Vec<Case> {
    let mut lines = text.lines().filter(|line| !line.trim().is_empty());
    let header: serde_json::Value =
        serde_json::from_str(lines.next().expect("battery.jsonl: a header line"))
            .expect("battery.jsonl: the header line is a JSON object");
    assert!(
        header.get("_comment").is_some() && header.get("id").is_none(),
        "battery.jsonl: the first line is the comment object, not a case"
    );
    lines
        .enumerate()
        .map(|(index, line)| {
            let number = index + 2;
            let value: serde_json::Value = serde_json::from_str(line).unwrap_or_else(|error| {
                panic!("battery.jsonl line {number}: not a JSON object: {error}")
            });
            let text_field = |name: &str| {
                value
                    .get(name)
                    .and_then(serde_json::Value::as_str)
                    .unwrap_or_else(|| {
                        panic!("battery.jsonl line {number}: `{name}` is missing or not a string")
                    })
                    .to_string()
            };
            let rc = value
                .get("rc")
                .and_then(serde_json::Value::as_i64)
                .and_then(|status| i32::try_from(status).ok())
                .unwrap_or_else(|| {
                    panic!("battery.jsonl line {number}: `rc` is missing or not a number")
                });
            Case {
                id: text_field("id"),
                rc,
                out: text_field("out"),
                cmd: text_field("cmd"),
            }
        })
        .collect()
}

fn cases() -> Vec<Case> {
    parse_battery(BATTERY)
}

fn known_failing() -> BTreeSet<String> {
    KNOWN_FAILING
        .lines()
        .map(|line| line.split('#').next().unwrap_or("").trim())
        .filter(|id| !id.is_empty())
        .map(str::to_string)
        .collect()
}

/// Removes terminal colour codes and the shell's own receipt lines.
fn normalise(raw: &str) -> String {
    let mut plain = String::with_capacity(raw.len());
    let mut chars = raw.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == '\u{1b}' && chars.peek() == Some(&'[') {
            chars.next();
            // A control sequence ends at the first byte in the range @ to ~.
            for inner in chars.by_ref() {
                if ('@'..='~').contains(&inner) {
                    break;
                }
            }
        } else {
            plain.push(ch);
        }
    }
    let mut kept = String::with_capacity(plain.len());
    for line in plain.split_inclusive('\n') {
        if line.starts_with("[op:") || line.starts_with("[txn:") {
            continue;
        }
        kept.push_str(line);
    }
    kept
}

/// Runs one case and says whether output and exit status match.
fn run(case: &Case) -> Outcome {
    let dir = tempfile::tempdir().expect("temporary directory");
    let mut child = Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-r")
        .arg(dir.path())
        .arg("-c")
        .arg(&case.cmd)
        .current_dir(dir.path())
        .env("NO_COLOR", "1")
        .env_remove("RUST_BACKTRACE")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        // Its own process group, so that a case which does not finish can be
        // stopped together with the commands it started.
        .process_group(0)
        .spawn()
        .expect("start the built shell");

    // Read the output while the shell runs. A case that writes more than a
    // pipe holds would otherwise wait for a reader that starts only once the
    // case has finished, and be counted as not finishing.
    let stdout = child
        .stdout
        .take()
        .expect("the shell's standard output is a pipe");
    let (sender, receiver) = mpsc::channel();
    std::thread::spawn(move || {
        let mut stdout = stdout;
        let mut raw = Vec::new();
        let _ = stdout.read_to_end(&mut raw);
        let _ = sender.send(raw);
    });

    let started = Instant::now();
    let status = loop {
        match child.try_wait().expect("wait for the shell") {
            Some(status) => break Some(status),
            None if started.elapsed() >= TIME_LIMIT => {
                stop_group(child.id());
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            None => std::thread::sleep(Duration::from_millis(2)),
        }
    };

    // The reader ends when every process that holds the pipe has gone. Do
    // not wait for that without limit.
    let raw = receiver.recv_timeout(OUTPUT_GRACE).ok();

    let (passed, detail) = match (status, raw) {
        (None, _) => (false, format!("did not finish within {TIME_LIMIT:?}")),
        (Some(_), None) => (
            false,
            format!("its output was still open {OUTPUT_GRACE:?} after it finished"),
        ),
        (Some(status), Some(raw)) => {
            let got_out = normalise(&String::from_utf8_lossy(&raw));
            let got_rc = status.code().unwrap_or(-1);
            if got_out == case.out && got_rc == case.rc {
                (true, String::new())
            } else {
                (
                    false,
                    format!(
                        "expected exit {} and {:?}; got exit {} and {:?}",
                        case.rc,
                        shorten(&case.out),
                        got_rc,
                        shorten(&got_out)
                    ),
                )
            }
        }
    };
    Outcome {
        id: case.id.clone(),
        passed,
        detail,
    }
}

/// Stops every process in the group led by `leader`. Best effort: a command
/// that has moved to a group of its own is not reached.
fn stop_group(leader: u32) {
    let _ = Command::new("kill")
        .args(["-KILL", "--", &format!("-{leader}")])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
}

fn shorten(text: &str) -> String {
    const LIMIT: usize = 120;
    if text.chars().count() <= LIMIT {
        text.to_string()
    } else {
        let head: String = text.chars().take(LIMIT).collect();
        format!("{head}…")
    }
}

fn group_of(id: &str) -> &str {
    id.rsplit_once('-').map_or(id, |(group, _)| group)
}

fn run_all(cases: &[Case]) -> Vec<Outcome> {
    let chunk = cases.len().div_ceil(WORKERS).max(1);
    let mut outcomes: Vec<Outcome> = std::thread::scope(|scope| {
        let handles: Vec<_> = cases
            .chunks(chunk)
            .map(|part| scope.spawn(move || part.iter().map(run).collect::<Vec<_>>()))
            .collect();
        handles
            .into_iter()
            .flat_map(|handle| handle.join().expect("worker finished"))
            .collect()
    });
    let order: BTreeMap<&str, usize> = cases
        .iter()
        .enumerate()
        .map(|(index, case)| (case.id.as_str(), index))
        .collect();
    outcomes.sort_by_key(|outcome| order[outcome.id.as_str()]);
    outcomes
}

fn write_report(cases: &[Case], outcomes: &[Outcome], known: &BTreeSet<String>) -> String {
    let mut by_group: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    for outcome in outcomes {
        let entry = by_group.entry(group_of(&outcome.id)).or_default();
        entry.1 += 1;
        if outcome.passed {
            entry.0 += 1;
        }
    }
    let passed = outcomes.iter().filter(|outcome| outcome.passed).count();
    let mut report = format!(
        "conformance battery: {passed} of {} cases match the reference\n\n",
        outcomes.len()
    );
    for (group, (ok, total)) in &by_group {
        report.push_str(&format!("{group:<10} {ok:>3} / {total}\n"));
    }
    report.push('\n');
    for (case, outcome) in cases.iter().zip(outcomes) {
        let mark = match (outcome.passed, known.contains(&outcome.id)) {
            (true, false) => "ok  ",
            (false, true) => "FAIL",
            (true, true) => "ok!!",
            (false, false) => "NEW!",
        };
        report.push_str(&format!(
            "{mark} {:<12} {}\n",
            outcome.id,
            case.cmd.replace('\n', "\\n")
        ));
        if !outcome.passed {
            report.push_str(&format!("       {}\n", outcome.detail));
        }
    }
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("conformance-report.txt");
    let _ = std::fs::write(&path, &report);
    report
}

#[test]
fn battery_matches_the_reference_except_for_the_known_failures() {
    let cases = cases();
    assert!(
        cases.len() >= 100,
        "the battery should hold at least 100 cases, found {}",
        cases.len()
    );

    let ids: BTreeSet<&str> = cases.iter().map(|case| case.id.as_str()).collect();
    assert_eq!(ids.len(), cases.len(), "case ids must be unique");

    let known = known_failing();
    let stale: Vec<&String> = known
        .iter()
        .filter(|id| !ids.contains(id.as_str()))
        .collect();
    assert!(
        stale.is_empty(),
        "known_failing.txt names cases that are not in the battery: {stale:?}"
    );

    let outcomes = run_all(&cases);
    let report = write_report(&cases, &outcomes, &known);

    let regressions: Vec<String> = outcomes
        .iter()
        .filter(|outcome| !outcome.passed && !known.contains(&outcome.id))
        .map(|outcome| format!("{}: {}", outcome.id, outcome.detail))
        .collect();
    let now_passing: Vec<&str> = outcomes
        .iter()
        .filter(|outcome| outcome.passed && known.contains(&outcome.id))
        .map(|outcome| outcome.id.as_str())
        .collect();

    assert!(
        regressions.is_empty() && now_passing.is_empty(),
        "\n{report}\n\
         Regressions (not on the known-failing list, and failing): {regressions:#?}\n\
         Now passing (take these off tests/conformance/known_failing.txt): {now_passing:?}\n"
    );
}

/// A case line that lacks a field is an error. It used to be dropped, so a
/// mistyped `id` took its case out of the battery without a word.
#[test]
#[should_panic(expected = "line 2: `id` is missing")]
fn a_case_line_without_an_id_is_an_error() {
    parse_battery("{\"_comment\": \"x\"}\n{\"rc\": 0, \"out\": \"\", \"cmd\": \"true\"}\n");
}

#[test]
#[should_panic(expected = "the first line is the comment object")]
fn the_first_line_must_be_the_comment_object() {
    parse_battery("{\"id\": \"a-01\", \"rc\": 0, \"out\": \"\", \"cmd\": \"true\"}\n");
}

#[test]
fn every_line_after_the_first_is_a_case() {
    let lines = BATTERY
        .lines()
        .filter(|line| !line.trim().is_empty())
        .count();
    assert_eq!(cases().len(), lines - 1);
}

/// More output than a pipe holds (64 KiB on Linux) must not turn a case that
/// finishes into one that is counted as not finishing.
#[test]
fn output_larger_than_a_pipe_is_read_while_the_shell_runs() {
    let out: String = (1..=30_000).map(|n| format!("{n}\n")).collect();
    assert!(out.len() > 2 * 65_536);
    let outcome = run(&Case {
        id: "big-output".to_string(),
        rc: 0,
        out,
        cmd: "seq 1 30000".to_string(),
    });
    assert!(outcome.passed, "{}", outcome.detail);
}

/// A case that does not finish is stopped at the time limit and reported.
#[test]
fn a_case_that_does_not_finish_is_reported_within_the_limit() {
    let started = Instant::now();
    let outcome = run(&Case {
        id: "never-ends".to_string(),
        rc: 0,
        out: String::new(),
        cmd: "sleep 600".to_string(),
    });
    assert!(!outcome.passed);
    assert!(
        outcome.detail.contains("did not finish"),
        "{}",
        outcome.detail
    );
    assert!(started.elapsed() < TIME_LIMIT + OUTPUT_GRACE + Duration::from_secs(5));
}

#[test]
fn receipt_lines_and_colour_codes_are_removed_before_comparing() {
    let raw = "\u{1b}[32mgreen\u{1b}[0m\n[op:1f163398] mkdir d\nkept\n[txn:558b5380] begin t\n";
    assert_eq!(normalise(raw), "green\nkept\n");
}

#[test]
fn the_known_failing_list_ignores_comments_and_blank_lines() {
    let parsed: BTreeSet<String> = "# heading\n\nlogic-03  # bracket test\n  \nloop-01\n"
        .lines()
        .map(|line| line.split('#').next().unwrap_or("").trim())
        .filter(|id| !id.is_empty())
        .map(str::to_string)
        .collect();
    assert_eq!(
        parsed,
        ["logic-03", "loop-01"]
            .iter()
            .map(|s| s.to_string())
            .collect()
    );
}
