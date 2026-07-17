#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# ┌─ a2ml-metadata-block ──────────────────────────────────────────────────────
# id: valence-shell.launcher
# type: launcher
# version: 0.9.0
# app-name: vsh
# app-display: Valence Shell
# app-url: ""                     # foreground terminal shell — no web endpoint
# standards-compliance:
#   - launcher-standard.adoc (hyperpolymath/standards, E-Grade Launcher Standard)
#   - LM-LA-LIFECYCLE-STANDARD.adoc
#   - cross-platform-system-integration-modes
#   - fallback-ladder-keepopen
# modes: [--auto, --start, --stop, --status, --browser, --web, --integ, --disinteg, --help, --version]
# platforms: [linux, macos, windows]
# lifecycle-phases-covered:
#   - run/auto (launch the interactive shell)
#   - status
#   - help / version
#   - system-integration (--integ / --disinteg; Linux first-class, macOS/Windows best-effort)
# lifecycle-phases-deferred:
#   # vsh is a FOREGROUND terminal shell with no HTTP server or daemon, so the
#   # server-oriented clauses of the standard do not apply and are declared
#   # deferred (not silently skipped):
#   - background-server (nohup daemon)   # BEAM daemon designed, not implemented
#   - url-readiness-polling (wait_for_server / curl)
#   - browser-launch (--auto opens the shell in the terminal, not a browser)
# └────────────────────────────────────────────────────────────────────────────
#
# E-Grade principle: one script to remember, one unified entry point for run,
# status, and system integration, self-documenting via --help / --version.

set -euo pipefail

# ── Standard variables ───────────────────────────────────────────────────────
APP_NAME="vsh"
APP_DISPLAY="Valence Shell"
REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERSION="$(grep -m1 '^version' "$REPO_DIR/impl/rust-cli/Cargo.toml" 2>/dev/null | sed -E 's/.*"([^"]+)".*/\1/')"
VERSION="${VERSION:-0.9.0}"
PID_FILE="${XDG_RUNTIME_DIR:-${TMPDIR:-/tmp}}/${APP_NAME}-server.pid"
LOG_DIR="${XDG_STATE_HOME:-$HOME/.local/state}/${APP_NAME}"
LOG_FILE="${LOG_DIR}/server.log"
MODE="${1:---auto}"

# ── Feedback helpers ─────────────────────────────────────────────────────────
log() { printf '%s\n' "$*"; }
err() { printf '%s: %s\n' "$APP_NAME" "$*" >&2; }

platform() { printf '%s-%s' "$(uname -s | tr '[:upper:]' '[:lower:]')" "$(uname -m)"; }

build_sha() {
    git -C "$REPO_DIR" rev-parse --short HEAD 2>/dev/null || printf 'unknown'
}

# ── Desktop-tools resolution ladder (graceful degradation) ───────────────────
# Source keepopen.sh / soft-attach.sh / gui-error.sh from the published ladder
# if present; otherwise install no-op shims so the launcher still works when the
# hyperpolymath desktop-tools are not installed (e.g. a fresh clone).
resolve_desktop_tools() {
    local candidates=(
        "${HP_DESKTOP_TOOLS:-}"
        "${HP_ESTATE_ROOT:-}/.desktop-tools"
        "${XDG_DATA_HOME:-$HOME/.local/share}/hyperpolymath/.desktop-tools"
        "$HOME/developer/repos/.desktop-tools"
        "$HOME/dev/repos/.desktop-tools"
    )
    local d
    for d in "${candidates[@]}"; do
        [ -n "$d" ] && [ -d "$d" ] || continue
        # shellcheck source=/dev/null
        [ -f "$d/gui-error.sh" ]  && . "$d/gui-error.sh"  || true
        # shellcheck source=/dev/null
        [ -f "$d/soft-attach.sh" ] && . "$d/soft-attach.sh" || true
        DESKTOP_TOOLS_DIR="$d"
        return 0
    done
    DESKTOP_TOOLS_DIR=""
    return 0
}

# Surface an error via GUI dialog (if the helper resolved) AND always to stderr.
gui_err() {
    err "$*"
    if command -v hp_gui_error >/dev/null 2>&1; then
        hp_gui_error "$APP_DISPLAY" "$*" || true
    fi
}

# Optional soft-attach hook on failure (no-op if tool absent).
on_start_failed() {
    if command -v hp_soft_attach_event >/dev/null 2>&1; then
        hp_soft_attach_event "$APP_NAME" "start-failed" "$LOG_FILE" || true
    fi
}

# ── vsh resolution ───────────────────────────────────────────────────────────
resolve_bin() {
    if command -v "$APP_NAME" >/dev/null 2>&1; then
        command -v "$APP_NAME"; return 0
    fi
    local rel="$REPO_DIR/impl/rust-cli/target/release/vsh"
    [ -x "$rel" ] && { printf '%s' "$rel"; return 0; }
    return 1
}

is_running() {
    [ -f "$PID_FILE" ] || return 1
    kill -0 "$(cat "$PID_FILE" 2>/dev/null)" 2>/dev/null
}

# ── Modes ────────────────────────────────────────────────────────────────────
mode_version() {
    printf '%s %s (%s) [%s]\n' "$APP_NAME" "$VERSION" "$(build_sha)" "$(platform)"
    exit 0
}

mode_help() {
    cat <<EOF
$APP_DISPLAY ($APP_NAME) launcher — E-Grade Launcher Standard

USAGE:
    ./launch.sh [MODE] [-- ARGS...]

MODES:
    --auto        (default) Build if needed and launch the interactive shell.
    --start       Alias of --auto for a foreground shell. (Background-daemon
                  semantics are DEFERRED — vsh has no server; see the BEAM
                  daemon roadmap.)
    --stop        Stop a running vsh daemon if one exists (deferred phase);
                  otherwise a friendly no-op.
    --status      Report binary location, version, platform, and daemon state.
    --browser     Alias of --auto (no web endpoint; opens the shell).
    --web         Alias of --auto.
    --integ       Install desktop integration (Linux: .desktop + launcher copy;
                  macOS/Windows: best-effort). Idempotent; --integ --force to
                  reinstall without prompting.
    --disinteg    Remove desktop integration, preserving config and logs.
    --help, -h    Show this help.
    --version, -V Print '$APP_NAME <version> (<sha>) [<platform>]' and exit 0.

FILES:
    repo:     $REPO_DIR
    startup:  $REPO_DIR/scripts/run.sh
    pid:      $PID_FILE   (deferred daemon phase)
    log:      $LOG_FILE

PLATFORM: $(platform)

Anything after the mode is passed through to vsh, e.g.:
    ./launch.sh --auto -- --version
    ./launch.sh --auto -- path/to/script.vsh
EOF
    exit 0
}

mode_status() {
    log "$APP_DISPLAY status"
    log "  version:  $APP_NAME $VERSION ($(build_sha)) [$(platform)]"
    if bin="$(resolve_bin)"; then
        log "  binary:   $bin"
    else
        log "  binary:   not built (run './launch.sh --auto' or 'just build-cli')"
    fi
    if is_running; then
        log "  daemon:   running (pid $(cat "$PID_FILE"))"
    else
        log "  daemon:   not running (vsh is a foreground shell; daemon phase deferred)"
    fi
    log "  log:      $LOG_FILE"
    exit 0
}

# --auto / --start: launch the interactive shell in the current terminal.
mode_auto() {
    mkdir -p "$LOG_DIR"
    if ! bin="$(resolve_bin)"; then
        log "Building $APP_NAME (first run)…"
        if ! ( cd "$REPO_DIR/impl/rust-cli" && cargo build --release ); then
            gui_err "build failed — see cargo output above"
            on_start_failed
            exit 1
        fi
        bin="$(resolve_bin)" || { gui_err "vsh binary missing after build"; on_start_failed; exit 1; }
    fi
    # Foreground terminal app: exec into the shell (no nohup/daemon — that phase
    # is declared deferred in the metadata header).
    exec "$bin" "$@"
}

mode_stop() {
    if is_running; then
        kill "$(cat "$PID_FILE")" 2>/dev/null || true
        rm -f "$PID_FILE"
        log "Stopped $APP_NAME daemon."
    else
        rm -f "$PID_FILE" 2>/dev/null || true
        log "$APP_NAME is a foreground shell — no daemon to stop."
    fi
    exit 0
}

# ── Desktop integration (Linux first-class; macOS/Windows best-effort) ────────
integ_linux() {
    local force="${1:-}"
    local apps="$HOME/.local/share/applications"
    local bindir="$HOME/.local/bin"
    local desktop="$apps/${APP_NAME}.desktop"
    local launcher_copy="$bindir/${APP_NAME}-launcher"

    mkdir -p "$apps" "$bindir"
    if [ -e "$desktop" ] && [ "$force" != "--force" ]; then
        log "Already integrated ($desktop). Use '--integ --force' to reinstall."
        exit 0
    fi

    # Copy, not symlink, so moving the repo doesn't break the menu entry.
    cp "$REPO_DIR/launch.sh" "$launcher_copy"
    chmod +x "$launcher_copy"

    # Terminal=true: vsh is an interactive terminal app. Route through keepopen
    # if the desktop-tools are installed; otherwise launch the shell directly.
    local exec_line
    if [ -n "${DESKTOP_TOOLS_DIR:-}" ] && [ -x "$DESKTOP_TOOLS_DIR/keepopen.sh" ]; then
        exec_line="$DESKTOP_TOOLS_DIR/keepopen.sh $APP_NAME $REPO_DIR \"$launcher_copy --auto\" \"$launcher_copy --auto\" $LOG_FILE"
    else
        exec_line="$launcher_copy --auto"
    fi

    cat > "$desktop" <<EOF
[Desktop Entry]
Type=Application
Name=$APP_DISPLAY
Comment=Formally verified reversible shell
Exec=$exec_line
Terminal=true
Categories=Development;System;TerminalEmulator;
Keywords=shell;terminal;verified;reversible;
EOF
    chmod 0444 "$desktop"
    command -v update-desktop-database >/dev/null 2>&1 && \
        update-desktop-database "$apps" >/dev/null 2>&1 || true

    log "Integrated $APP_DISPLAY:"
    log "  desktop entry: $desktop"
    log "  launcher copy: $launcher_copy"
    exit 0
}

mode_integ() {
    resolve_desktop_tools
    case "$(uname -s)" in
        Linux)  integ_linux "${1:-}";;
        Darwin) log "macOS integration is best-effort/deferred; run './launch.sh --auto' to use the shell."; exit 0;;
        *)      log "Desktop integration for $(uname -s) is deferred; run './launch.sh --auto'."; exit 0;;
    esac
}

mode_disinteg() {
    local apps="$HOME/.local/share/applications"
    local bindir="$HOME/.local/bin"
    local removed=0
    for f in "$apps/${APP_NAME}.desktop" "$HOME/Desktop/${APP_NAME}.desktop" "$bindir/${APP_NAME}-launcher"; do
        [ -e "$f" ] && { rm -f "$f"; log "removed $f"; removed=1; }
    done
    rm -f "$PID_FILE" 2>/dev/null || true
    command -v update-desktop-database >/dev/null 2>&1 && \
        update-desktop-database "$apps" >/dev/null 2>&1 || true
    # Preserve ~/.config/$APP_NAME and $XDG_STATE_HOME/$APP_NAME by design.
    [ "$removed" -eq 0 ] && log "$APP_DISPLAY was not integrated (no-op)." || \
        log "Removed $APP_DISPLAY integration (config and logs preserved)."
    exit 0
}

# ── Dispatch ─────────────────────────────────────────────────────────────────
# Consume the mode arg, pass the remainder through to vsh where applicable.
shift || true
case "$MODE" in
    --version|-V)       mode_version;;
    --help|-h)          mode_help;;
    --status)           mode_status;;
    --stop)             mode_stop;;
    --integ)            mode_integ "${1:-}";;
    --disinteg)         mode_disinteg;;
    --auto|--start|--browser|--web)
                        # allow './launch.sh --auto -- ARGS' or trailing ARGS
                        [ "${1:-}" = "--" ] && shift || true
                        mode_auto "$@";;
    -* )                err "unknown mode: $MODE (try --help)"; exit 2;;
    "" )                mode_auto;;
    * )                 # No mode given but args present: treat all as vsh args.
                        mode_auto "$MODE" "$@";;
esac
