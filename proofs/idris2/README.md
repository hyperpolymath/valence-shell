<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Idris2 Proofs for Valence Shell

**Status**: Proofs complete — 0 holes, builds under `--total` (v0.14.0)
**Totality**: All functions total (`%default total` + `--total`); no `partial`
**Extraction**: Compiles to executable code via Idris2 compiler

---

## Overview

This directory contains **executable specifications** of filesystem operations written in Idris2. Unlike the Lean 4/Coq/Agda proofs which are purely for verification, these Idris2 modules are designed to:

1. **Prove correctness** via dependent types
2. **Extract to executable code** via Idris2 compiler
3. **Guarantee totality** (all functions terminate)
4. **Provide unbreakable guarantees** (type-level proofs)

---

## Modules

### Core Modules

| Module | Purpose | Status | Holes |
|--------|---------|--------|-------|
| `Filesystem.Model` | Core types + structural lemmas | ✅ Proven | 0 |
| `Filesystem.Operations` | mkdir, rmdir, touch, rm, writeFile | ✅ Proven | 0 |
| `Filesystem.Composition` | Operation sequences, undo/redo | ✅ Proven | 0 |
| `Filesystem.RMO` | Irreversible operations (GDPR) | ✅ Proven | 0 |

**Total**: 4 modules, **0 proof holes**, 0 `partial` annotations, 2 registered
primitive-eq axioms (`axStringEqRefl`, `axBits8EqRefl` in `Filesystem.Axioms`).
The whole package builds under `--total`, so every theorem is a total,
machine-checked proof.

### Proof Holes — ALL CLOSED (2026-07-01)

Every `?hole` that previously stood in for a proof is now discharged with a
real, type-checked term. The closure landed **without adding any new axioms**;
where a stated theorem was a genuine non-theorem in the ordered-list model, its
signature was redesigned to the true statement (following the #60/#61/#119
precedent) rather than closed with `believe_me`. Summary:

| Theorem | How it was closed |
|---------|-------------------|
| `mkdirRmdirReversible` | `removeAddAbsent`; rmdir applicability made an explicit precondition |
| `touchRmReversible` | `removeAddAbsent` + unconditional `RmPrecondition` after touch |
| `rmdirMkdirReversible` | canonical-form precondition + `cong MkFS` (restore direction is not injective in general) |
| `rmTouchReversible` | canonical-form precondition + `cong MkFS` |
| `writeFileReversible` | `updateOverwrite` + `updateCanonicalId` |
| `operationIndependence` | restated over `Equiv` (order-independence) via `equivAddSwap` — `=` was a non-theorem |
| `cnoWriteSameContent` | canonical-form precondition + `updateCanonicalId` + `equivRefl` |
| `sequenceReversible` | induction over a `TraceReversible` witness (real per-step reversibility replaces the vacuous `isReversible = True`) |
| `compositionReversible` | genuine per-step reversibility hypotheses (the `isReversible = True` gates were vacuous) |
| `undoRedoIdentity` | `opInvOpId` + `Applicable` precondition |
| `undoRedoComposition` | induction over an `Undoable` witness + `Maybe`-monad laws (`applyNSnoc`, `bindAssoc`, `bindCong`) |
| `overwriteIrreversible` | redesigned to non-injectivity (`updateEntryDeterminedByFilter`); prior `recovery randomData = Nothing` was refuted by `recovery = Just` |
| `hardwareEraseIrreversible` | redesigned to non-injectivity (`hardwareErase` wipes to `empty`); prior type refuted by any total recovery |
| `secureDeleteNotInjective`, `gdprDeletionCompliant`, `appendOnlyAuditLog`, `auditTrailCompleteness`, `equivRefl/Sym/Trans` | already closed in earlier sessions |

---

## Building

### Prerequisites

```bash
# Install Idris2
# On Fedora:
sudo dnf install idris2

# On NixOS (recommended):
nix-shell -p idris2

# Or via .tool-versions (asdf):
asdf plugin add idris2
asdf install idris2 latest
```

### Compile

```bash
cd proofs/idris2

# Type-check all modules
idris2 --typecheck valence-shell.ipkg

# Build package
idris2 --build valence-shell.ipkg

# Generate executable (once proofs complete)
idris2 --codegen chez --output vsh-core src/Main.idr
```

### Build oracle (Justfile)

The `build-idris2` and `verify-idris2` recipes in the top-level `Justfile`
wrap the above. They are mirrored by the `idris-verification.yml` CI job.

```bash
# From repo root:
just build-idris2    # cd proofs/idris2 && idris2 --build valence-shell.ipkg
just verify-idris2   # build + count distinct ?holes for regression tracking
```

#### Oracle status (2026-07-01)

`build-idris2` **builds green** and `verify-idris2` reports **0 distinct
`?holes`**. All four modules type-check under `--total`. The
`idris-verification.yml` gate already flips to `exit 1` on build failure; with
zero holes and a clean build the layer is a hard gate, not honest debt.

### Run Tests

```bash
# Check totality of all functions
idris2 --total --check valence-shell.ipkg

# Run property tests (once implemented)
idris2 --exec main tests/Properties.idr
```

---

## Extraction Backends

Idris2 supports multiple compilation targets:

### 1. Chez Scheme (Default, Fast)

```bash
idris2 --codegen chez --output vsh-core Main.idr
./build/exec/vsh-core
```

**Pros**: Fast compilation, good runtime performance
**Cons**: Requires Chez Scheme runtime

### 2. C Backend (Production)

```bash
idris2 --codegen c --output vsh-core Main.idr
./build/exec/vsh-core
```

**Pros**: No runtime dependencies, fastest execution
**Cons**: Slower compilation

### 3. JavaScript (Browser/Deno)

```bash
idris2 --codegen javascript --output vsh-core.js Main.idr
deno run vsh-core.js
```

**Pros**: Can run in browser or Deno
**Cons**: Slower than native

---

## Correspondence to Other Proofs

### Lean 4 ↔ Idris2 Mapping

| Lean 4 Theorem | Idris2 Function | Status |
|----------------|-----------------|--------|
| `mkdir_rmdir_reversible` | `mkdirRmdirReversible` | ✅ Proven |
| `create_delete_file_reversible` | `touchRmReversible` | ✅ Proven |
| `write_file_reversible` | `writeFileReversible` | ✅ Proven |
| `operation_sequence_reversible` | `sequenceReversible` | ✅ Proven |
| `fs_equiv_refl` | `equivRefl` | ✅ Proven |
| `fs_equiv_sym` | `equivSym` | ✅ Proven |
| `fs_equiv_trans` | `equivTrans` | ✅ Proven |
| `cno_identity_element` | `cnoWriteSameContent` | ✅ Proven |
| `hardware_erase_irreversible` | `hardwareEraseIrreversible` | ✅ Proven |

### Coq ↔ Idris2 Mapping

Idris2 uses similar type theory to Coq (both based on Martin-Löf type theory), but Idris2 is designed for extraction while Coq is proof-focused.

**Key Differences**:
- Idris2: Quantitative types, linear types, totality checker
- Coq: Tactics, more automation, mature ecosystem

---

## Key Theorems (Proven)

### 1. Reversibility

```idris
mkdirRmdirReversible :
  (p : Path) ->
  (fs : Filesystem) ->
  {auto mkdirPrf : MkdirPrecondition p fs} ->
  {auto rmdirPrf : RmdirPrecondition p (mkdir p fs)} ->
  rmdir p (mkdir p fs) = fs
```

**Status**: ✅ Proven via `removeAddAbsent`
**Approach**: rmdir applicability is an explicit precondition (the mkdir
precondition does not preclude orphan children); the equality itself is the
exact-equality lemma `removeAddAbsent`.

### 2. Sequence Reversibility

```idris
sequenceReversible :
  (ops : List Operation) ->
  (fs : Filesystem) ->
  TraceReversible ops fs ->
  applySequence (reverse (map inverse ops)) (applySequence ops fs) = fs
```

**Status**: ✅ Proven by induction on the `TraceReversible` witness
**Approach**: the vacuous `All (isReversible op = True)` premise is replaced by
`TraceReversible`, which records that each step genuinely inverts at its state;
induction stitches head-cancellation to the inductive tail via `reverseCons` and
`sequenceSplit`.

### 3. Non-Injectivity (Irreversibility)

```idris
secureDeleteNotInjective :
  (p : Path) ->
  (fs1, fs2 : Filesystem) ->
  (prf1 : ObliterationProof p) ->
  (prf2 : ObliterationProof p) ->
  filter (keepIfNotP p) (entries fs1)
    = filter (keepIfNotP p) (entries fs2) ->
  removeEntry p fs1 = removeEntry p fs2
```

**Status**: Closed (issues #60/#61). Mirrors Coq's `obliterate_not_injective`.
**Approach**: Direct congruence via `removeEntryDeterminedByFilter` in `Filesystem.Model`.

The previous signature `recovery fs = fs -> Void` was a non-theorem (refuted by `recovery = id`); the redesigned signature captures the correct information-theoretic content of irreversibility — non-injectivity of the deletion map, hence no left-inverse exists.

---

## Integration with Valence Shell

### Current Architecture (v0.14.0)

```
Rust CLI (impl/rust-cli/)
  ↓
Lean 4 Proofs (verification only)
```

### Target Architecture (v2.0)

```
Rust Shell (REPL, Parser, UI)
  ↓ FFI
Idris2 Core (extracted executable)
  ↓ FFI
POSIX Syscalls
```

### FFI Example

```idris
-- In Idris2
%foreign "C:vsh_mkdir, libvsh"
prim_mkdir : String -> PrimIO Int

-- In C (generated)
int vsh_mkdir(const char* path) {
  return mkdir(path, 0755);
}

-- In Rust
#[no_mangle]
pub extern "C" fn vsh_mkdir_wrapper(path: *const c_char) -> c_int {
  // Call Idris2 compiled function
  unsafe { idris2_vsh_mkdir(path) }
}
```

---

## Roadmap

### Phase 1: Complete Proofs (Weeks 1-2)

- [x] Fill all proof holes (0 remaining as of 2026-07-01)
- [x] Verify totality of all functions (builds under `--total`)
- [ ] Add property tests

### Phase 2: Extraction (Week 3)

- [ ] Extract to Chez Scheme
- [ ] Extract to C
- [ ] Benchmark performance

### Phase 3: Integration (Week 4)

- [ ] Create FFI bindings to Rust
- [ ] Replace core operations with extracted code
- [ ] Validate with existing property tests

### Phase 4: v2.0 Release (Weeks 5-6)

- [ ] Full Idris2-based core
- [ ] 99%+ verification confidence
- [ ] Documentation and release

---

## Benefits Over Current Approach

| Aspect | Current (Rust) | With Idris2 |
|--------|---------------|-------------|
| Correctness | 85% (manual + property tests) | 99%+ (type-level proofs) |
| Totality | Not guaranteed | Guaranteed by compiler |
| Extraction | Manual rewrite | Automatic from proofs |
| Maintenance | Keep code + proofs in sync | Single source of truth |
| Confidence | "Probably correct" | "Provably correct" |

---

## Related Work

- **seL4**: Verified microkernel (Isabelle/HOL extraction to C)
- **CompCert**: Verified C compiler (Coq extraction to OCaml)
- **Idris1**: Original dependently-typed language (many verified programs)
- **Agda**: Alternative proof assistant (less focus on extraction)

---

## Contributing

See main project `CONTRIBUTING.md`. For Idris2-specific:

1. All functions must be `total` (or `partial` with justification)
2. Use dependent types for preconditions
3. Fill proof holes before adding new features
4. Add property tests for extracted code

---

## References

- [Idris2 Documentation](https://idris2.readthedocs.io/)
- [Type-Driven Development with Idris](https://www.manning.com/books/type-driven-development-with-idris)
- [PLFA (Verified Programming in Agda)](https://plfa.github.io/) - Similar approach
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/) - Coq proofs

---

**Status**: All proofs complete — 0 holes, builds under `--total`, 2 registered
primitive-eq axioms (`Filesystem.Axioms`).
**Next**: extract to executable, integrate with shell
