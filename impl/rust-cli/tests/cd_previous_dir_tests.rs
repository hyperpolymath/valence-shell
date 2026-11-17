// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! A `cd` that fails must not change what `cd -` returns to.
//!
//! `cd` used to record the directory it was leaving before it tried to
//! change, so a change that failed after its checks (here: no search
//! permission) still set the previous directory, and that was written to the
//! journal and survived a restart.
//!
//! The test runs the built shell. Root may enter any directory, so when the
//! test itself runs as root the shell is started as the unprivileged user
//! `nobody`.

#![cfg(unix)]

use std::fs::{self, Permissions};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::process::CommandExt;
use std::path::Path;
use std::process::{Command, Output, Stdio};

const NOBODY: u32 = 65534;

fn vsh(root: &Path, script: &str) -> Output {
    let built = Path::new(env!("CARGO_BIN_EXE_vsh"));
    let as_root = nix::unistd::geteuid().is_root();

    // As root the shell is started as another user, who may not be able to
    // reach the build directory (a checkout under a private home directory,
    // for one). Give that user a copy it can run. The directory is removed
    // when this function returns, after the shell has finished.
    let staged = as_root.then(|| {
        let dir = tempfile::tempdir().expect("directory for a copy of the shell");
        fs::set_permissions(dir.path(), Permissions::from_mode(0o755)).expect("open it");
        let copy = dir.path().join("vsh");
        fs::copy(built, &copy).expect("copy the built shell");
        fs::set_permissions(&copy, Permissions::from_mode(0o755)).expect("make it runnable");
        (dir, copy)
    });
    let program = staged.as_ref().map_or(built, |(_, copy)| copy.as_path());

    let mut command = Command::new(program);
    command
        .arg("-r")
        .arg(root)
        .arg("-c")
        .arg(script)
        .current_dir(root)
        .env("HOME", root)
        .env_remove("RUST_BACKTRACE")
        .stdin(Stdio::null());
    if as_root {
        command.uid(NOBODY).gid(NOBODY);
    }
    command.output().expect("start the built shell")
}

#[test]
fn a_cd_that_fails_does_not_record_a_previous_directory() {
    let root = tempfile::tempdir().expect("temporary directory");
    // The shell may run as another user, so it must be able to write here.
    fs::set_permissions(root.path(), Permissions::from_mode(0o777)).expect("open the root");
    let locked = root.path().join("locked");
    fs::create_dir(&locked).expect("create the directory");
    fs::set_permissions(&locked, Permissions::from_mode(0o000)).expect("lock the directory");

    let failed = vsh(root.path(), "cd locked");
    let back = vsh(root.path(), "cd -");

    // Let the temporary directory be removed whatever the assertions find.
    fs::set_permissions(&locked, Permissions::from_mode(0o755)).expect("unlock the directory");

    assert!(
        !failed.status.success(),
        "cd into a directory without search permission should fail; stderr: {}",
        String::from_utf8_lossy(&failed.stderr)
    );
    let stderr = String::from_utf8_lossy(&back.stderr);
    assert!(
        !back.status.success() && stderr.contains("OLDPWD not set"),
        "after a failed cd there is no previous directory to return to; \
         status {:?}, stderr: {stderr}",
        back.status.code()
    );
}

#[test]
fn a_cd_that_succeeds_still_records_where_it_came_from() {
    let root = tempfile::tempdir().expect("temporary directory");
    fs::set_permissions(root.path(), Permissions::from_mode(0o777)).expect("open the root");
    fs::create_dir(root.path().join("inner")).expect("create the directory");
    fs::set_permissions(root.path().join("inner"), Permissions::from_mode(0o777))
        .expect("open the directory");

    let run = vsh(root.path(), "cd inner; cd -; pwd");

    assert!(
        run.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    let last = stdout.lines().last().unwrap_or("");
    let expected = fs::canonicalize(root.path()).expect("canonical root");
    assert_eq!(
        Path::new(last),
        expected,
        "`cd -` should return to the root"
    );
}
