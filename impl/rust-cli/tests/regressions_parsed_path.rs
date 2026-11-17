// SPDX-License-Identifier: MPL-2.0
//! The runtime holes of the route plan, each as a test through the real
//! command line (`vsh -r <root> -c '<commands>'`).
//!
//! Source: `docs/plans/VSH-ROUTE-PLAN-2026-11-04.adoc`, section 3.2 (holes a
//! to n) and the 2026-11-17 review (hole o). Every reproduction below was
//! re-run against `main` on 2026-11-17 and still failed. Hole p was found
//! the same day, in the scrub that closed hole d
//! (`docs/audits/2026-11-17-capstd-experiment.adoc`).
//!
//! # How to read this file
//!
//! Each test states the *safe* behaviour: what must be true after the
//! commands run. A hole is "open" while its check fails.
//!
//! [`KNOWN_OPEN`] lists the holes that are open today. The tests hold it to
//! the truth in both directions:
//!
//! * a hole in the list whose check passes fails the test, with a message to
//!   remove it from the list (so a fix cannot land without the list
//!   shrinking);
//! * a hole not in the list whose check fails is a regression.
//!
//! So the suite is green while the list is accurate, no test is skipped, and
//! the list is the record of what is still unsafe. It must become empty.
//!
//! A check returns `Err` only for the documented symptom. Anything else
//! unexpected (a set-up step failing, say) panics, so a hole cannot stay
//! "open" for the wrong reason.

#![cfg(unix)]

mod fixtures;

use fixtures::tempfile::TempDir;
use std::fs;
use std::os::unix::fs::{symlink, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// Holes that are open today. See the module documentation.
const KNOWN_OPEN: &[&str] = &["b", "o", "p"];

/// Every hole this file tests.
const ALL_HOLES: &[&str] = &[
    "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p",
];

/// Hold one hole's check against [`KNOWN_OPEN`].
fn hole(name: &str, check: impl FnOnce() -> Result<(), String>) {
    assert!(ALL_HOLES.contains(&name), "unlisted hole {name}");
    match (KNOWN_OPEN.contains(&name), check()) {
        (true, Err(symptom)) => println!("hole {name} is still open: {symptom}"),
        (true, Ok(())) => panic!(
            "hole {name} no longer reproduces. Remove it from KNOWN_OPEN in \
             tests/regressions_parsed_path.rs."
        ),
        (false, Ok(())) => {}
        (false, Err(symptom)) => panic!("hole {name} has regressed: {symptom}"),
    }
}

#[test]
fn known_open_names_only_real_holes() {
    for name in KNOWN_OPEN {
        assert!(
            ALL_HOLES.contains(name),
            "KNOWN_OPEN names unknown hole {name}"
        );
    }
}

/// A session root (`root`) inside a private directory, with a sibling
/// directory (`outside`) that the shell must never touch.
struct Sandbox {
    temp: TempDir,
    root: PathBuf,
    outside: PathBuf,
}

impl Sandbox {
    fn new() -> Self {
        let temp = TempDir::new().unwrap();
        let root = temp.path().join("root");
        let outside = temp.path().join("outside");
        fs::create_dir(&root).unwrap();
        fs::create_dir(&outside).unwrap();
        Self {
            temp,
            root,
            outside,
        }
    }

    /// Run a command line through the parsed path.
    fn vsh(&self, commands: &str) -> Output {
        Command::new(env!("CARGO_BIN_EXE_vsh"))
            .arg("-r")
            .arg(&self.root)
            .arg("-c")
            .arg(commands)
            // Wherever the shell keeps state outside the root, keep it
            // inside this sandbox.
            .env("XDG_STATE_HOME", self.temp.path().join("xdg-state"))
            .env("XDG_CACHE_HOME", self.temp.path().join("xdg-cache"))
            .env("XDG_DATA_HOME", self.temp.path().join("xdg-data"))
            .env("NO_COLOR", "1")
            .env("RUST_BACKTRACE", "0")
            .output()
            .expect("vsh should start")
    }

    /// Run a command line that is only set-up: it must succeed.
    fn vsh_ok(&self, commands: &str) {
        let output = self.vsh(commands);
        assert!(
            output.status.success(),
            "set-up `{commands}` failed: {}",
            text(&output)
        );
    }
}

fn text(output: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn read(path: &Path) -> String {
    String::from_utf8_lossy(&fs::read(path).unwrap()).into_owned()
}

/// The names in `dir`, sorted.
fn names(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    names
}

/// Every regular file under `dir`, recursively, without following links.
fn files_under(dir: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(next) = pending.pop() {
        for entry in fs::read_dir(&next).unwrap() {
            let entry = entry.unwrap();
            let kind = entry.file_type().unwrap();
            if kind.is_dir() {
                pending.push(entry.path());
            } else if kind.is_file() {
                found.push(entry.path());
            }
        }
    }
    found
}

/// Whether `haystack` holds `secret`, as raw bytes or as the JSON number
/// array the shell uses for undo data (`[83, 69, ...]`, any spacing).
fn holds_secret(haystack: &[u8], secret: &str) -> bool {
    let raw = secret.as_bytes();
    if haystack.windows(raw.len()).any(|window| window == raw) {
        return true;
    }
    let as_numbers: String = raw.iter().map(u8::to_string).collect::<Vec<_>>().join(",");
    let compact: Vec<u8> = haystack
        .iter()
        .copied()
        .filter(|byte| !byte.is_ascii_whitespace())
        .collect();
    compact
        .windows(as_numbers.len())
        .any(|window| window == as_numbers.as_bytes())
}

/// (a) Undoing an output redirection restores the file.
#[test]
fn hole_a_undo_of_a_redirection_restores_the_file() {
    hole("a", || {
        let sandbox = Sandbox::new();
        let output = sandbox.vsh("touch g; echo hi > g; undo");
        let content = read(&sandbox.root.join("g"));
        if !output.status.success() || !content.is_empty() {
            return Err(format!(
                "undo of `echo hi > g` failed (rc {:?}); g holds {content:?}",
                output.status.code()
            ));
        }
        Ok(())
    });
}

/// (b) Undo does not destroy data written by another program since.
#[test]
fn hole_b_undo_does_not_delete_data_written_outside_the_shell() {
    hole("b", || {
        let sandbox = Sandbox::new();
        sandbox.vsh_ok("touch f");
        fs::write(sandbox.root.join("f"), "precious\n").unwrap();
        sandbox.vsh("undo");
        match fs::read(sandbox.root.join("f")) {
            Ok(bytes) if bytes == b"precious\n" => Ok(()),
            Ok(bytes) => Err(format!("f was changed to {bytes:?}")),
            Err(_) => Err("undo deleted f, which another program had written to".into()),
        }
    });
}

/// (c) Obliterate is refused inside a transaction (ruling OD-3a): a
/// transaction promises rollback, and obliteration cannot be rolled back.
#[test]
fn hole_c_obliterate_is_refused_inside_a_transaction() {
    hole("c", || {
        let sandbox = Sandbox::new();
        sandbox.vsh("begin t; touch a; obliterate a --force");
        if sandbox.root.join("a").exists() {
            Ok(())
        } else {
            Err("obliterate ran inside an open transaction".into())
        }
    });
}

/// (d) After obliterate, no earlier content of the file survives in the
/// shell's own state.
#[test]
fn hole_d_obliterate_scrubs_earlier_contents_from_the_state() {
    hole("d", || {
        let sandbox = Sandbox::new();
        sandbox.vsh_ok("echo SECRETA > f; echo b > f; obliterate f --force");
        assert!(
            !sandbox.root.join("f").exists(),
            "obliterate should remove f"
        );
        let holders: Vec<String> = files_under(sandbox.temp.path())
            .into_iter()
            .filter(|path| holds_secret(&fs::read(path).unwrap(), "SECRETA"))
            .map(|path| path.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        if holders.is_empty() {
            Ok(())
        } else {
            Err(format!("the obliterated content is still in {holders:?}"))
        }
    });
}

/// (e) Arithmetic at the edge of i64 does not panic. (It wraps, as bash
/// does and as the shell's own addition and multiplication already did.)
#[test]
fn hole_e_arithmetic_overflow_does_not_panic() {
    hole("e", || {
        let sandbox = Sandbox::new();
        let minimum = "m=$(( -9223372036854775807 - 1 ))";
        let mut panics = Vec::new();
        for expression in ["m / -1", "m % -1", "-m"] {
            let output = sandbox.vsh(&format!("{minimum}; x=$(( {expression} )); echo done"));
            if output.status.code() == Some(101) || text(&output).contains("panicked") {
                panics.push(expression);
            }
        }
        if panics.is_empty() {
            Ok(())
        } else {
            Err(format!("the shell panicked evaluating {panics:?}"))
        }
    });
}

/// (f) Undo after `cd` reverses the operation that was made, not a file of
/// the same name in the new directory.
#[test]
fn hole_f_undo_after_cd_targets_the_original_path() {
    hole("f", || {
        let sandbox = Sandbox::new();
        fs::create_dir(sandbox.root.join("sub")).unwrap();
        fs::write(sandbox.root.join("sub/f"), "KEEP\n").unwrap();
        sandbox.vsh("touch f; cd sub; undo");
        let kept = fs::read(sandbox.root.join("sub/f")).ok();
        if kept.as_deref() != Some(b"KEEP\n".as_slice()) {
            return Err("undo deleted or changed the user's own sub/f".into());
        }
        if sandbox.root.join("f").exists() {
            return Err("undo left the created f in place".into());
        }
        Ok(())
    });
}

/// (g) `cd ..` at the root does not let later commands reach outside it:
/// not to create, not to write, and not to remove.
#[test]
fn hole_g_cd_cannot_leave_the_root() {
    hole("g", || {
        let sandbox = Sandbox::new();
        let parent = sandbox.temp.path();
        fs::write(parent.join("bystander"), "KEEP\n").unwrap();
        sandbox.vsh("cd ..; touch escaped");
        sandbox.vsh("cd ..; mkdir escaped_dir");
        sandbox.vsh("cd ..; echo x > escaped_out");
        sandbox.vsh("cd ..; rm bystander");
        let mut reached = Vec::new();
        for (name, command) in [
            ("escaped", "touch"),
            ("escaped_dir", "mkdir"),
            ("escaped_out", ">"),
        ] {
            if parent.join(name).exists() {
                reached.push(format!("`{command}` created {name} outside the root"));
            }
        }
        if !parent.join("bystander").exists() {
            reached.push("`rm` removed a file outside the root".into());
        }
        if reached.is_empty() {
            Ok(())
        } else {
            Err(reached.join("; "))
        }
    });
}

/// (h) Undoing a removal restores the file's permissions with its content.
#[test]
fn hole_h_undo_of_rm_restores_the_mode() {
    hole("h", || {
        let sandbox = Sandbox::new();
        let secret = sandbox.root.join("s");
        fs::write(&secret, "TOPSECRET").unwrap();
        fs::set_permissions(&secret, fs::Permissions::from_mode(0o600)).unwrap();
        sandbox.vsh_ok("rm s; undo");
        assert_eq!(
            read(&secret),
            "TOPSECRET",
            "undo should restore the content"
        );
        let mode = fs::metadata(&secret).unwrap().permissions().mode() & 0o777;
        if mode == 0o600 {
            Ok(())
        } else {
            Err(format!("the file came back with mode {mode:o}, not 600"))
        }
    });
}

/// (i) Obliterate does nothing if it cannot first record that it will: the
/// audit entry is written before the overwrite, not attempted after it.
///
/// The set-up puts a directory where the audit log goes, so the entry cannot
/// be written. If the audit log moves out of the root, this set-up must move
/// with it.
#[test]
fn hole_i_obliterate_refuses_when_it_cannot_record_the_audit_entry() {
    hole("i", || {
        let sandbox = Sandbox::new();
        fs::write(sandbox.root.join("f"), "DATA\n").unwrap();
        fs::create_dir(sandbox.root.join(".vsh-audit.log")).unwrap();
        sandbox.vsh("obliterate f --force");
        match fs::read(sandbox.root.join("f")) {
            Ok(bytes) if bytes == b"DATA\n" => Ok(()),
            _ => Err("the file was obliterated although no audit entry could be written".into()),
        }
    });
}

/// (j) Writing through an in-root symlink does not change a file outside.
#[test]
fn hole_j_redirection_does_not_follow_a_symlink_out_of_the_root() {
    hole("j", || {
        let sandbox = Sandbox::new();
        let victim = sandbox.outside.join("victim");
        fs::write(&victim, "ORIGINAL\n").unwrap();
        symlink(&victim, sandbox.root.join("link")).unwrap();
        sandbox.vsh("echo PWNED > link");
        sandbox.vsh("echo MORE >> link");
        let content = read(&victim);
        if content == "ORIGINAL\n" {
            Ok(())
        } else {
            Err(format!("the file outside the root now holds {content:?}"))
        }
    });
}

/// (k) Creating under an in-root symlink to an outside directory creates
/// nothing outside.
#[test]
fn hole_k_creation_does_not_follow_a_symlinked_directory_out_of_the_root() {
    hole("k", || {
        let sandbox = Sandbox::new();
        symlink(&sandbox.outside, sandbox.root.join("lp")).unwrap();
        sandbox.vsh("touch lp/new; mkdir lp/newdir");
        let created = names(&sandbox.outside);
        if created.is_empty() {
            Ok(())
        } else {
            Err(format!("created outside the root: {created:?}"))
        }
    });
}

/// (l) Moving into an in-root symlink to an outside directory moves nothing
/// outside.
#[test]
fn hole_l_mv_does_not_follow_a_symlinked_directory_out_of_the_root() {
    hole("l", || {
        let sandbox = Sandbox::new();
        symlink(&sandbox.outside, sandbox.root.join("lp")).unwrap();
        sandbox.vsh("touch f; mv f lp/f");
        let moved = names(&sandbox.outside);
        if moved.is_empty() {
            Ok(())
        } else {
            Err(format!("moved outside the root: {moved:?}"))
        }
    });
}

/// (m) Obliterating an in-root symlink does not destroy the file it points
/// to outside the root.
#[test]
fn hole_m_obliterate_does_not_follow_a_symlink_out_of_the_root() {
    hole("m", || {
        let sandbox = Sandbox::new();
        let victim = sandbox.outside.join("victim");
        fs::write(&victim, "PRECIOUS\n").unwrap();
        symlink(&victim, sandbox.root.join("vl")).unwrap();
        sandbox.vsh("obliterate vl --force");
        if fs::read(&victim).unwrap() == b"PRECIOUS\n" {
            Ok(())
        } else {
            Err("the file outside the root was overwritten".into())
        }
    });
}

/// (n) A hard link inside the root to a file outside it does not let the
/// shell destroy or change that file.
#[test]
fn hole_n_hard_links_do_not_reach_files_outside_the_root() {
    hole("n", || {
        let sandbox = Sandbox::new();
        let victim = sandbox.outside.join("victim");
        let other = sandbox.outside.join("other");
        fs::write(&victim, "PRECIOUS\n").unwrap();
        fs::write(&other, "OTHER\n").unwrap();
        fs::hard_link(&victim, sandbox.root.join("hl")).unwrap();
        fs::hard_link(&other, sandbox.root.join("h2")).unwrap();
        sandbox.vsh("obliterate hl --force");
        sandbox.vsh("echo X > h2");
        let mut damaged = Vec::new();
        if fs::read(&victim).unwrap() != b"PRECIOUS\n" {
            damaged.push("obliterate overwrote the outside file");
        }
        if fs::read(&other).unwrap() != b"OTHER\n" {
            damaged.push("redirection changed the outside file");
        }
        if damaged.is_empty() {
            Ok(())
        } else {
            Err(damaged.join("; "))
        }
    });
}

/// (o) After a rollback, `undo` does not try to reverse the rolled-back
/// operations again.
#[test]
fn hole_o_undo_after_rollback_does_not_reverse_twice() {
    hole("o", || {
        let sandbox = Sandbox::new();
        let output = sandbox.vsh("begin t; touch f; rollback; undo");
        assert!(
            !sandbox.root.join("f").exists(),
            "rollback should remove f: {}",
            text(&output)
        );
        if output.status.success() {
            Ok(())
        } else {
            Err(format!(
                "undo after rollback failed: {}",
                text(&output).lines().last().unwrap_or_default()
            ))
        }
    });
}

/// (p) After obliterate, no earlier content of the file survives in the
/// shell's own state, under whatever name it was saved.
///
/// The scrub of hole (d) finds the records of a file by its path. Content
/// that was saved while the file had another name is recorded under that
/// name, and is not found: `mv a b; obliterate b` leaves what `a` held.
/// The same holds for content saved through a symbolic link that has been
/// removed since, in a history written before redirections recorded the
/// file they changed.
#[test]
fn hole_p_obliterate_scrubs_contents_saved_under_an_earlier_name() {
    hole("p", || {
        let sandbox = Sandbox::new();
        sandbox.vsh_ok("echo SECRETP > a; echo b > a; mv a b; obliterate b --force");
        assert!(
            !sandbox.root.join("b").exists(),
            "obliterate should remove b"
        );
        let holders: Vec<String> = files_under(sandbox.temp.path())
            .into_iter()
            .filter(|path| holds_secret(&fs::read(path).unwrap(), "SECRETP"))
            .map(|path| path.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        if holders.is_empty() {
            Ok(())
        } else {
            Err(format!(
                "the content saved under the earlier name is still in {holders:?}"
            ))
        }
    });
}
