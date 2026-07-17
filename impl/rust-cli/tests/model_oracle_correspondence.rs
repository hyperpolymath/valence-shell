// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Differential correspondence: Rust implementation vs. the *proven Lean model*.
//!
//! Unlike the property tests (which check hand-transcribed laws), this test uses
//! the COMPILED Lean model as the oracle. `proofs/lean4/ModelOracle.lean` drives
//! the exact `mkdir`/`rmdir`/`createFile`/`deleteFile`/`fsUpdate` definitions that
//! the correspondence theorems are proven about, and reports the node type at a
//! set of probe paths. We generate precondition-respecting operation sequences
//! (the regime where the reversibility theorems hold), apply them to the real
//! Rust `ShellState`, run the same sequence through the Lean oracle, and assert
//! that the model and the implementation agree at every touched path.
//!
//! Any disagreement is a genuine correspondence divergence between the proven
//! model and the runtime — the thing a mechanized correspondence is meant to catch.
//!
//! Gating: if the oracle binary is not built, the test SKIPS (prints how to build
//! it) rather than failing, so `cargo test` stays green without a Lean toolchain.
//! Build it with:  cd proofs/lean4 && lake build model_oracle
//! or:             just build-model-oracle

use std::collections::BTreeMap;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

use tempfile::TempDir;
use vsh::commands::{mkdir, rm, rmdir, touch};
use vsh::state::ShellState;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Dir,
    File,
}

/// Deterministic LCG so the corpus is reproducible (no external rand dependency,
/// and Miri/CI get identical sequences run-to-run).
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            ((self.next_u64() >> 33) as usize) % n
        }
    }
}

/// Locate the compiled Lean model oracle. Env override wins; otherwise the
/// default lake build path relative to this crate.
fn locate_oracle() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("VSH_MODEL_ORACLE") {
        let pb = PathBuf::from(p);
        if pb.is_file() {
            return Some(pb);
        }
    }
    // impl/rust-cli/tests -> repo root -> proofs/lean4/.lake/build/bin/model_oracle
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let candidate = manifest
        .join("../../proofs/lean4/.lake/build/bin/model_oracle")
        .canonicalize()
        .ok()?;
    if candidate.is_file() {
        Some(candidate)
    } else {
        None
    }
}

/// One generated operation.
#[derive(Clone)]
struct Op {
    verb: &'static str, // MKDIR / RMDIR / TOUCH / RM
    path: String,
}

/// Generate a precondition-respecting sequence, maintaining a shadow of the
/// expected state so every emitted op is valid under real-filesystem rules.
fn gen_sequence(rng: &mut Rng, max_ops: usize) -> (Vec<Op>, Vec<String>) {
    let mut shadow: BTreeMap<String, Kind> = BTreeMap::new();
    let mut ops: Vec<Op> = Vec::new();
    let mut touched: BTreeMap<String, ()> = BTreeMap::new();
    let mut counter = 0usize;

    let dirs = |shadow: &BTreeMap<String, Kind>| -> Vec<String> {
        let mut v = vec![String::new()]; // root
        v.extend(
            shadow
                .iter()
                .filter(|(_, k)| **k == Kind::Dir)
                .map(|(p, _)| p.clone()),
        );
        v
    };
    let is_empty_dir = |shadow: &BTreeMap<String, Kind>, p: &str| -> bool {
        let prefix = format!("{p}/");
        !shadow.keys().any(|k| k.starts_with(&prefix))
    };
    let child = |parent: &str, name: &str| -> String {
        if parent.is_empty() {
            name.to_string()
        } else {
            format!("{parent}/{name}")
        }
    };

    let n = 1 + rng.below(max_ops);
    for _ in 0..n {
        // Weighted choice biased toward creation, with valid removals when possible.
        let roll = rng.below(10);
        if roll < 5 {
            // MKDIR under an existing directory
            let ds = dirs(&shadow);
            let parent = ds[rng.below(ds.len())].clone();
            counter += 1;
            let p = child(&parent, &format!("d{counter}"));
            if shadow.contains_key(&p) {
                continue;
            }
            shadow.insert(p.clone(), Kind::Dir);
            touched.insert(p.clone(), ());
            ops.push(Op { verb: "MKDIR", path: p });
        } else if roll < 8 {
            // TOUCH under an existing directory
            let ds = dirs(&shadow);
            let parent = ds[rng.below(ds.len())].clone();
            counter += 1;
            let p = child(&parent, &format!("f{counter}.txt"));
            if shadow.contains_key(&p) {
                continue;
            }
            shadow.insert(p.clone(), Kind::File);
            touched.insert(p.clone(), ());
            ops.push(Op { verb: "TOUCH", path: p });
        } else if roll < 9 {
            // RM an existing file
            let files: Vec<String> = shadow
                .iter()
                .filter(|(_, k)| **k == Kind::File)
                .map(|(p, _)| p.clone())
                .collect();
            if files.is_empty() {
                continue;
            }
            let p = files[rng.below(files.len())].clone();
            shadow.remove(&p);
            touched.insert(p.clone(), ());
            ops.push(Op { verb: "RM", path: p });
        } else {
            // RMDIR an empty directory
            let empties: Vec<String> = shadow
                .iter()
                .filter(|(p, k)| **k == Kind::Dir && is_empty_dir(&shadow, p))
                .map(|(p, _)| p.clone())
                .collect();
            if empties.is_empty() {
                continue;
            }
            let p = empties[rng.below(empties.len())].clone();
            shadow.remove(&p);
            touched.insert(p.clone(), ());
            ops.push(Op { verb: "RMDIR", path: p });
        }
    }

    (ops, touched.into_keys().collect())
}

/// Ask the Lean model oracle for the node type at each probe path.
fn oracle_query(oracle: &PathBuf, ops: &[Op], probes: &[String]) -> Vec<String> {
    let mut input = String::new();
    for op in ops {
        input.push_str(op.verb);
        input.push(' ');
        input.push_str(&op.path);
        input.push('\n');
    }
    input.push_str("---\n");
    for p in probes {
        input.push_str(p);
        input.push('\n');
    }

    let mut child = Command::new(oracle)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("spawn model oracle");
    child
        .stdin
        .take()
        .expect("oracle stdin")
        .write_all(input.as_bytes())
        .expect("write to oracle");
    let out = child.wait_with_output().expect("oracle output");
    assert!(out.status.success(), "oracle exited non-zero");
    String::from_utf8(out.stdout)
        .expect("oracle utf8")
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect()
}

/// The real Rust implementation's node type at a probe path (under the sandbox).
fn rust_kind(root: &std::path::Path, rel: &str) -> &'static str {
    match std::fs::symlink_metadata(root.join(rel)) {
        Ok(m) if m.is_dir() => "DIR",
        Ok(m) if m.is_file() => "FILE",
        Ok(_) => "OTHER",
        Err(_) => "NONE",
    }
}

#[test]
fn rust_matches_proven_lean_model() {
    let Some(oracle) = locate_oracle() else {
        eprintln!(
            "SKIP model_oracle_correspondence: Lean model oracle not built.\n\
             Build it with:  cd proofs/lean4 && lake build model_oracle\n\
             or:             just build-model-oracle\n\
             or set VSH_MODEL_ORACLE=/path/to/model_oracle"
        );
        return;
    };

    const SEQUENCES: usize = 200;
    const MAX_OPS: usize = 14;
    let mut rng = Rng::new(20260717u64);
    let mut checked_probes = 0usize;

    for seq in 0..SEQUENCES {
        let (ops, probes) = gen_sequence(&mut rng, MAX_OPS);
        if probes.is_empty() {
            continue;
        }

        // Apply the sequence to the real Rust implementation in a fresh sandbox.
        let temp = TempDir::new().expect("tempdir");
        let mut state =
            ShellState::new(temp.path().to_str().expect("utf8 path")).expect("shell state");
        for op in &ops {
            let r = match op.verb {
                "MKDIR" => mkdir(&mut state, &op.path, false),
                "RMDIR" => rmdir(&mut state, &op.path, false),
                "TOUCH" => touch(&mut state, &op.path, false),
                "RM" => rm(&mut state, &op.path, false),
                _ => unreachable!(),
            };
            r.unwrap_or_else(|e| {
                panic!("seq {seq}: generated op {} {} rejected by impl: {e}", op.verb, op.path)
            });
        }

        // Ask the proven model for the same probes.
        let model = oracle_query(&oracle, &ops, &probes);
        assert_eq!(
            model.len(),
            probes.len(),
            "seq {seq}: oracle returned {} answers for {} probes",
            model.len(),
            probes.len()
        );

        // Differential assertion: model vs. real implementation at every probe.
        for (probe, model_kind) in probes.iter().zip(model.iter()) {
            let impl_kind = rust_kind(temp.path(), probe);
            assert_eq!(
                model_kind, impl_kind,
                "CORRESPONDENCE DIVERGENCE (seq {seq}) at '{probe}': \
                 proven Lean model says {model_kind}, Rust impl says {impl_kind}.\n\
                 ops: {:?}",
                ops.iter().map(|o| format!("{} {}", o.verb, o.path)).collect::<Vec<_>>()
            );
            checked_probes += 1;
        }
    }

    assert!(
        checked_probes > 0,
        "no probes were checked — generator produced only empty sequences"
    );
    eprintln!("model_oracle_correspondence: {checked_probes} probes agreed across {SEQUENCES} sequences");
}
