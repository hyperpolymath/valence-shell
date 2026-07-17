#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Startup command for the vsh shell. This is the canonical run entry point the
# Hyperpolymath launcher standard searches for ({repo-dir}/scripts/run.sh).
# It builds the release binary on first use, then execs the interactive shell.
# Extra arguments pass through to vsh (e.g. --version, a script path).
set -euo pipefail

REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CLI_DIR="$REPO_DIR/impl/rust-cli"
BIN="$CLI_DIR/target/release/vsh"

if [ ! -x "$BIN" ]; then
    echo "vsh: building release binary (first run)…" >&2
    ( cd "$CLI_DIR" && cargo build --release )
fi

exec "$BIN" "$@"
