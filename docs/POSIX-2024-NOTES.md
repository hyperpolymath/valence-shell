# SPDX-License-Identifier: PMPL-1.0-or-later
# POSIX 2024 (Issue 8) Compatibility Notes — Valence Shell

**Author**: Jonathan D.A. Jewell
**Last Updated**: 2026-03-10
**Reference**: IEEE Std 1003.1-2024 (POSIX.1-2024, Issue 8)

---

## Overview

POSIX.1-2024 (Issue 8) was published in June 2024, replacing POSIX.1-2017 (Issue 7).
This document tracks which POSIX 2024 changes are relevant to valence-shell and our
current compatibility status.

## Relevant POSIX 2024 Changes

### Shell Grammar Changes

| Change | Relevant? | vsh Status |
|--------|-----------|------------|
| `pipefail` option added to shell | Yes | Not implemented |
| `local` builtin standardized | Yes | Not implemented (listed as missing builtin) |
| `readarray`/`mapfile` not added | N/A | N/A |
| Here-string `<<<` **not** standardized | Info | Implemented as extension |
| `[[` compound command **not** standardized | Info | Implemented as extension |
| `$'...'` (ANSI-C quoting) **not** standardized | Info | Not implemented |

### New/Changed Utilities

| Utility | POSIX 2024 Status | vsh Status |
|---------|-------------------|------------|
| `timeout` | Newly standardized | Not implemented (external only) |
| `realpath` | Newly standardized | Not implemented |
| `yes` | Newly standardized | Not implemented (external only) |
| `getconf` | Updated | Not relevant (system utility) |
| `find` `-delete` | Newly standardized flag | Not relevant (external command) |
| `sed` `-E` (ERE) | Newly standardized flag | Not relevant (external command) |
| `xargs` `-P` | Newly standardized flag | Not relevant (external command) |

### Variable/Expansion Changes

| Change | Relevant? | vsh Status |
|--------|-----------|------------|
| `${param@operator}` transformations | Yes | Not implemented |
| `EXECIGNORE` variable | Low | Not implemented |
| Unset vs empty distinction clarified | Yes | Partially handled (`:-` vs `-`) |

### Signal Handling

| Change | Relevant? | vsh Status |
|--------|-----------|------------|
| `trap` behavior clarifications | Yes | `trap` not implemented at all |
| `SIGCHLD` handling specified | Yes | Not implemented |

## Compatibility Matrix

| POSIX 2024 Area | Supported | Partial | Not Yet |
|-----------------|-----------|---------|---------|
| Simple commands | Yes | | |
| Pipelines | Yes | | |
| Redirections (standard) | Yes | | |
| Variables & expansion | | Yes | |
| Glob expansion | Yes | | |
| Arithmetic expansion | Yes | | |
| Command substitution | Yes | | |
| Control flow (if/while/for/case) | Yes | | |
| Functions | | | Not yet |
| `trap` / signal handling | | | Not yet |
| `local` builtin | | | Not yet |
| `pipefail` | | | Not yet |
| Job control | | Yes | |
| Shell scripts (.sh) | | | Not yet |
| `${param@operator}` | | | Not yet |

## Priority for vsh

POSIX 2024 changes that should be tracked as vsh approaches v1.0:

1. **`local` builtin** — now standardized; implement alongside shell functions (M12)
2. **`pipefail`** — valuable for robust scripting; implement after pipelines are solid
3. **`${param@operator}`** — useful but lower priority than functions and scripts
4. **`trap`** — essential for any script-capable shell; implement in M11 builtin expansion
5. **Signal handling clarifications** — align with POSIX 2024 once `trap`/SIGCHLD land

## Notes

- vsh already implements several features that remain non-POSIX even in Issue 8
  (here-strings `<<<`, `[[ ]]`, process substitution, brace expansion).
  These are kept as extensions.
- The formal verification strategy is orthogonal to POSIX compliance level;
  reversibility proofs apply regardless of which POSIX edition is targeted.
- Full POSIX 2024 compliance requires completing milestones M10-M14 first
  (see `docs/POSIX_COMPLIANCE.md`).
