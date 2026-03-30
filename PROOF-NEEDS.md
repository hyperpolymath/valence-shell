# PROOF-NEEDS.md
<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

## Current State

- **LOC**: ~57,650
- **Languages**: Rust, ReScript, Agda, Idris2, Zig
- **Existing ABI proofs**: `src/abi/*.idr` plus extensive Agda proof suite (9 files in `proofs/agda/`)
- **Dangerous patterns**:
  - `proofs/agda/FileContentOperations.agda`: 5 `postulate`
  - `proofs/agda/FilesystemModel.agda`: 1 `postulate`
  - `proofs/agda/RMOOperations.agda`: 1 `postulate`
  - `impl/mcp/src/Server.res`: 20+ `Obj.magic` in MCP tool handlers

## What Needs Proving

### FileContentOperations Postulates (5)
- These are in the core filesystem proof — content operations are critical for shell correctness
- Audit each postulate: are they about byte-level I/O (acceptable axiom) or about logical properties (should be proven)?

### FilesystemModel Postulate (1)
- Foundation postulate — if this is wrong, all downstream proofs are unsound
- Should be the highest priority to eliminate or justify

### RMOOperations Postulate (1)
- Reversible Mutable Operations — the core innovation of valence-shell
- Any unproven claim about reversibility undermines the entire system guarantee

### MCP Server Obj.magic (impl/mcp/src/Server.res)
- Every filesystem operation handler uses `Obj.magic` for JSON result construction
- `makeToolResult` and `makeJsonResult` return type-erased values
- Prove: MCP tool responses conform to MCP protocol schema

### Rust FFI Verification (ffi/rust/)
- `ffi/rust/src/preconditions.rs`, `verification.rs`, `rmo.rs` — safety-critical FFI
- Precondition checking and operation verification should have formal backing

## Recommended Prover

- **Agda** (already in use — eliminate remaining 7 postulates)
- **Idris2** for ABI layer and Rust FFI interface contracts

## Priority

**HIGH** — Filesystem shell with formal reversibility guarantees. The 7 postulates in the Agda proofs are close to full verification. Eliminating them would make this a genuinely formally verified filesystem tool.
