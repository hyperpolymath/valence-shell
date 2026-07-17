<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Launcher — `launch.sh` (E-Grade Launcher Standard)

`launch.sh` at the repository root is the single, self-documenting entry point
for running and integrating `vsh`. It conforms to the Hyperpolymath
**E-Grade Launcher Standard** (`hyperpolymath/standards`,
`docs/UX-standards/launcher-standard.adoc` + `launcher/launcher-standard.a2ml`).

```bash
./launch.sh              # launch the interactive shell (default --auto)
./launch.sh --version    # vsh 0.9.0 (<sha>) [linux-x86_64]
./launch.sh --help       # full usage
./launch.sh --status     # binary, version, platform, daemon state
./launch.sh --integ      # install desktop integration (Linux first-class)
./launch.sh --disinteg   # remove integration (keeps config + logs)
```

`just run` / `just launch` delegate to `./launch.sh --auto`.

## Modes

| Mode | Behavior |
|------|----------|
| `--auto` (default) | Build if needed, then launch the interactive shell. |
| `--start` | Alias of `--auto` for a foreground shell (daemon phase deferred). |
| `--stop` | Stop a running daemon if one exists; otherwise a friendly no-op. |
| `--status` | Report binary path, version, platform, and daemon state. |
| `--browser` / `--web` | Aliases of `--auto` (no web endpoint; opens the shell). |
| `--integ` | Install desktop integration; idempotent (`--integ --force` reinstalls). |
| `--disinteg` | Remove integration, preserving `~/.config/vsh` and state/logs. |
| `--help` / `-h` | Usage, modes, file paths, detected platform. |
| `--version` / `-V` | `vsh <version> (<sha>) [<platform>]`, exit 0. |

Arguments after the mode pass through to `vsh`
(`./launch.sh --auto -- path/to/script.vsh`).

## Files

| Path | Role |
|------|------|
| `${XDG_STATE_HOME:-$HOME/.local/state}/vsh/server.log` | Log (never `/tmp`) |
| `${XDG_RUNTIME_DIR:-$TMPDIR:-/tmp}/vsh-server.pid` | PID file (deferred daemon phase) |
| `~/.local/share/applications/vsh.desktop` | Desktop entry (0444, `Terminal=true`) |
| `~/.local/bin/vsh-launcher` | Copied launcher (copy, not symlink) |

## Conformance & honest deferrals

`vsh` is a **foreground terminal shell with no HTTP server or daemon**. The
E-Grade standard is written primarily for web/GUI apps, so a subset of its MUST
clauses do not apply here. Rather than silently skip them, the launcher declares
them **deferred** in its `a2ml-metadata-block` header (`lifecycle-phases-deferred`):

| Standard clause | Status | Rationale |
|-----------------|--------|-----------|
| Universal modes (`--start/--stop/--status/--auto/--browser/--web/--help/--version/--integ/--disinteg`) | ✅ Covered | Implemented and tested. |
| `--version` format `<app> <ver> (<sha>) [<platform>]` | ✅ Covered | Verified exact match. |
| Desktop integration (idempotent, copy-not-symlink, `Terminal=true`, 0444, config/log-preserving `--disinteg`) | ✅ Covered (Linux) | macOS/Windows are best-effort/deferred. |
| `err()`/`log()`, stderr-always, GUI-error + soft-attach via the resolution ladder (graceful no-op if absent) | ✅ Covered | Degrades cleanly when desktop-tools not installed. |
| PID file / logs in XDG dirs (never `/tmp`) | ✅ Covered | Paths wired; used when a daemon exists. |
| `nohup` background server, `wait_for_server()` URL polling, browser launch | ⏸️ **Deferred** | No server/URL — the BEAM daemon is designed but not implemented. `--auto` runs the shell in the terminal, not a browser. |

When the BEAM daemon lands, the deferred server phases (nohup start, URL
readiness, browser open) can be enabled without changing the mode surface.

## Testing

The mode surface is verified manually per change:

```bash
./launch.sh --version         # exact format, exit 0
./launch.sh --status          # reports state
./launch.sh --integ           # installs; second run is idempotent
./launch.sh --disinteg        # removes; second run is a no-op
./launch.sh --auto -- --version   # passthrough to vsh
```
