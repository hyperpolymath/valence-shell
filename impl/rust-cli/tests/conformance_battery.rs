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

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const BATTERY: &str = include_str!("conformance/battery.jsonl");
const KNOWN_FAILING: &str = include_str!("conformance/known_failing.txt");

/// Longest a single case may run. A case that does not finish counts as failed.
const TIME_LIMIT: Duration = Duration::from_secs(5);

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

fn cases() -> Vec<Case> {
    BATTERY
        .lines()
        .filter(|line| !line.trim().is_empty())
        .filter_map(|line| {
            let value: serde_json::Value =
                serde_json::from_str(line).expect("battery.jsonl: every line is a JSON object");
            // The first line is a comment object carrying the licence header.
            let id = value.get("id")?.as_str()?.to_string();
            let field = |name: &str| {
                value
                    .get(name)
                    .unwrap_or_else(|| panic!("battery.jsonl: case {id} has no `{name}`"))
                    .clone()
            };
            Some(Case {
                rc: i32::try_from(field("rc").as_i64().expect("`rc` is a number"))
                    .expect("`rc` fits in i32"),
                out: field("out")
                    .as_str()
                    .expect("`out` is a string")
                    .to_string(),
                cmd: field("cmd")
                    .as_str()
                    .expect("`cmd` is a string")
                    .to_string(),
                id,
            })
        })
        .collect()
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
        .spawn()
        .expect("start the built shell");

    let started = Instant::now();
    let status = loop {
        match child.try_wait().expect("wait for the shell") {
            Some(status) => break Some(status),
            None if started.elapsed() >= TIME_LIMIT => {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            None => std::thread::sleep(Duration::from_millis(2)),
        }
    };

    let mut raw = Vec::new();
    if let Some(mut stdout) = child.stdout.take() {
        let _ = stdout.read_to_end(&mut raw);
    }
    let got_out = normalise(&String::from_utf8_lossy(&raw));

    let (passed, detail) = match status {
        None => (false, format!("did not finish within {TIME_LIMIT:?}")),
        Some(status) => {
            let got_rc = status.code().unwrap_or(-1);
            if got_out == case.out && got_rc == case.rc {
                (true, String::new())
            } else {
                (
                    false,
                    format!(
                        "expected exit {} and {:?}; got exit {} and {:?}",
                        case.rc,
                        case.out,
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
