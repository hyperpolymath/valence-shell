# Idris2 Proofs for Valence Shell

**Status**: Initial Implementation (v0.14.0)
**Totality**: All functions marked `total` (partial where I/O required)
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
| `Filesystem.Model` | Core types: Path, Filesystem, FSEntry | ✅ Implemented | 2 (equivalence) |
| `Filesystem.Operations` | mkdir, rmdir, touch, rm, writeFile | ✅ Implemented | 8 (reversibility) |
| `Filesystem.Composition` | Operation sequences, undo/redo | ✅ Implemented | 5 (composition) |
| `Filesystem.RMO` | Irreversible operations (GDPR) | ✅ Implemented | 6 (irreversibility) |

**Total**: 4 modules, 21 proof holes to fill

### Proof Holes (TODO)

Holes are placeholders for proofs that need to be completed:

1. `equivSymProof` - Symmetry of filesystem equivalence
2. `equivTransProof` - Transitivity of filesystem equivalence
3. `rmdirPrfAfterMkdir` - Precondition after mkdir
4. `mkdirRmdirReversibleProof` - Main reversibility theorem
5. `rmdirMkdirReversibleProof` - Inverse reversibility
6. `touchRmReversibleProof` - File creation reversibility
7. `rmTouchReversibleProof` - Inverse file creation
8. `writeFileReversibleProof` - Write reversibility
9. `operationIndependenceProof` - Path independence
10. `cnoWriteSameContentProof` - CNO for same content
11. `sequenceReversibleProof` - Sequence reversibility (key theorem)
12. `compositionReversibleProof` - Composition of operations
13. `undoRedoIdentityProof` - Undo/redo identity
14. `undoRedoCompositionProof` - Multiple undo/redo
15. `secureDeleteIrreversibleProof` - Secure deletion has no inverse
16. `overwriteIrreversibleProof` - Overwrite destroys original
17. `gdprDeletionCompliantProof` - GDPR compliance
18. `hardwareEraseIrreversibleProof` - Hardware erase absolute
19. `appendOnlyAuditLogProof` - Audit log append-only
20. `auditTrailCompletenessProof` - Audit trail completeness
21. `allReversibleProof` - All operations reversible (helper)

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
| `mkdir_rmdir_reversible` | `mkdirRmdirReversible` | ⚠️ Hole |
| `create_delete_file_reversible` | `touchRmReversible` | ⚠️ Hole |
| `write_file_reversible` | `writeFileReversible` | ⚠️ Hole |
| `operation_sequence_reversible` | `sequenceReversible` | ⚠️ Hole |
| `fs_equiv_refl` | `equivRefl` | ✅ Proven |
| `fs_equiv_sym` | `equivSym` | ⚠️ Hole |
| `fs_equiv_trans` | `equivTrans` | ⚠️ Hole |
| `cno_identity_element` | `cnoWriteSameContent` | ⚠️ Hole |
| `hardware_erase_irreversible` | `hardwareEraseIrreversible` | ⚠️ Hole |

### Coq ↔ Idris2 Mapping

Idris2 uses similar type theory to Coq (both based on Martin-Löf type theory), but Idris2 is designed for extraction while Coq is proof-focused.

**Key Differences**:
- Idris2: Quantitative types, linear types, totality checker
- Coq: Tactics, more automation, mature ecosystem

---

## Key Theorems (To Be Proven)

### 1. Reversibility

```idris
mkdirRmdirReversible :
  (p : Path) ->
  (fs : Filesystem) ->
  {auto mkdirPrf : MkdirPrecondition p fs} ->
  rmdir p (mkdir p fs) = fs
```

**Status**: Hole - needs proof
**Approach**: Case analysis on filesystem structure

### 2. Sequence Reversibility

```idris
sequenceReversible :
  (ops : List Operation) ->
  (fs : Filesystem) ->
  (allReversible : All (\op => isReversible op = True) ops) ->
  applySequence (reverse (map inverse ops)) (applySequence ops fs) = fs
```

**Status**: Hole - needs proof by induction
**Approach**: Induction on `ops`, use individual reversibility

### 3. Irreversibility

```idris
secureDeleteIrreversible :
  (p : Path) ->
  (fs : Filesystem) ->
  (prf : ObliterationProof p) ->
  (recovery : Filesystem -> Filesystem) ->
  recovery fs = fs ->
  Void
```

**Status**: Hole - needs proof
**Approach**: Show contradiction - if recovery exists, violates NIST SP 800-88

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

- [ ] Fill all 21 proof holes
- [ ] Verify totality of all functions
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

**Status**: Initial implementation complete, proofs pending
**Next**: Fill proof holes, extract to executable, integrate with shell
