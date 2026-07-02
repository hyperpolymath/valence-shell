<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# ABI / FFI boundary — decision record

**Status:** documented (2026-07-01). Non-breaking — this records the current
boundary and the accepted exceptions; it does **not** rewrite any code. The
code-level consolidation (see "Deferred" below) needs a separate, owner-approved
pass.

## Context

The estate convention is **"Idris2 = ABIs, Zig = APIs + FFIs."** An audit found
the convention is *documented and partially scaffolded* but not uniformly
upheld: several non-Zig FFI/API surfaces exist, the Zig spine was unintegrated
(no C header on disk), and the primary Rust CLI doesn't consume the ABI at all.
This record names the canonical spine, sanctions the real exceptions with
rationale, and clarifies each surface's role — without a risky rewrite.

## The canonical ABI/FFI spine (conformant)

```
src/abi/*.idr            Idris2 ABI declarations (%foreign)
    │
    ▼
ffi/zig/src/main.zig     Zig FFI implementation (export fn) → libvalence_shell.{so,a}
    │
    ▼
ffi/zig/include/valence_shell.h   C header (any language via C ABI)
```

- `src/abi/Foreign.idr`'s `%foreign "C:valence_shell_*, libvalence_shell"`
  declarations correspond 1:1 to `ffi/zig/src/main.zig`'s `export fn
  valence_shell_*` symbols (11 functions).
- The C header **`ffi/zig/include/valence_shell.h`** is now present and
  **hand-maintained** to match those exports. (Older docs describe an `idris2
  --cg c-header` step, but Idris2 ships no such codegen — only chez/node/racket/
  refc — so the header is authored by hand and updated in the same commit as any
  `export fn` change.)

## Named exceptions — surfaces that are *not* on the Zig C-ABI spine

These are accepted deviations from "all FFIs are Zig", each for a concrete
reason. They are sanctioned, not stray.

| Surface | Language | Why not Zig | Status |
|---|---|---|---|
| `impl/elixir/c_src/valence_nif.c` | C | The BEAM NIF ABI is fixed by `erl_nif.h`; the glue is C by necessity. It *calls* the Zig fast-path lib. | Sanctioned exception |
| `impl/ocaml/lean_wrapper.c` | C | Marshaling Lean-4-extracted objects into OCaml uses the OCaml/Lean C runtime ABI. | Sanctioned exception |
| `impl/mcp/**/*.res` | ReScript/Deno | MCP is a *protocol* API (JSON-RPC over stdio/HTTP), not a C ABI; ReScript per estate language policy. | Sanctioned (API, not a C-ABI FFI) |

## Clarifications (role of each Rust/Zig surface)

- **`ffi/rust/` is a Rust *library*, not a C-ABI FFI.** It consumes POSIX/libc
  (a "foreign function interface" only in the *calls-libc* sense) with
  precondition checking; it exposes **no** `#[no_mangle]`/`extern "C"` symbols
  and is not something other languages link against. The C-ABI-*provider* role
  belongs to `ffi/zig`. Its docs have been relabeled to say so.
- **Two Zig trees.** `ffi/zig/` is the **canonical**, spine-conformant FFI
  (11 exports, wired to the Idris2 ABI declarations). `impl/zig/` is an
  experimental fast-path lib plus a Lean-runtime wrapper, gated on the
  not-yet-built BEAM daemon. Collapsing the two is future work.
- **The primary Rust CLI (`impl/rust-cli/`) does not link the FFI.** Its
  `build.rs` is intentionally a no-op; `vsh` is a self-contained pure-Rust
  shell today. Wiring it to the Zig FFI is future work.

## Deferred (code-level consolidation — needs owner sign-off)

Out of scope for this documentation pass because each can destabilize the
shipping shell:

1. Port `ffi/rust` to Zig, or fold it behind the Zig FFI.
2. Wire `impl/rust-cli` to the Zig FFI (replace the no-op `build.rs`).
3. Collapse `impl/zig` into `ffi/zig`.

Until then, the spine above is the documented contract, and the three
exceptions are the sanctioned deviations.

## See also

- `ABI-FFI-README.md` — architecture overview and per-language usage.
- `src/abi/README.adoc`, `ffi/zig/README.adoc` — the two ends of the spine.
