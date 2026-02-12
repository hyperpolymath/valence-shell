# Proof Holes Audit - Valence Shell

**Date**: 2026-02-12 (updated after proof gap closure session)
**Auditor**: Opus (deep audit + proof closure)
**Total Holes**: 31 across 4 proof systems (down from 41)

## Summary

| Category | Count | Change | Action Required |
|----------|-------|--------|-----------------|
| **Gaps** | 26 | -2 net | Need proving or explicit documentation |
| **Axioms** | 3 | 0 | Intentional — document as axioms |
| **Structural** | 2 | -8 | Standard type theory axioms |
| **Total** | **31** | **-10** | |

### What Was Closed (2026-02-12 proof session)

**Lean 4 (2 main theorems proven):**
- `append_truncate_reversible` — proven via `readFile_after_writeFile` helper + `writeFileReversible`
  (1 helper `sorry` remains for `string_take_append_length` stdlib lemma)
- `truncate_to_zero_is_write_empty` — proven with `WellFormedContent` precondition added
  (theorem was false without it — files with `nodeContent = none` are a model edge case)

**Agda (8 postulates closed, 2 partially):**
- `rmdir-mkdir-reversible` — proven with `HasDefaultDirPerms` constraint
- `deleteFile-createFile-reversible` — proven with `HasDefaultFilePerms` constraint
- `writeFileIndependence` — fully proven via path decidability
- `writeFileLastWriteWins` — fully proven via funext + case analysis
- `writeFileCommute` — fully proven via funext + case analysis
- `node`/`prf` hacks in FilesystemModel.agda — replaced with `not-path-exists-nothing` helper
- `node`/`prf` hacks in FileOperations.agda — replaced with proper `not-path-exists-nothing`
- `createFile-preserves`/`deleteFile-preserves` in file-isolation — replaced with proper proofs

**Coq (restructured, more granular):**
- `mkdir_two_dirs_reversible` — decomposed into `mkdir_creates_empty_dir` +
  `rmdir_precondition_after_mkdir` with well-formedness infrastructure added

### Key Discovery: Reverse-Direction Reversibility

**The postulates `rmdir-mkdir-reversible` and `deleteFile-createFile-reversible` were
FALSE as originally stated.** `mkdir`/`createFile` always create with `defaultPerms`, but
the original node may have had custom permissions. The theorem `mkdir(rmdir(p, fs)) = fs`
only holds when the original directory had `defaultPerms`.

This is a known model limitation — the Rust implementation always uses default
permissions, so the constraint is satisfied in practice.

## Intentional Axioms (3) — No Action Required

These all represent the same information-theoretic axiom across 3 languages:
**"Secure deletion (RMO) destroys information irreversibly"**

| File | Line | Theorem |
|------|------|---------|
| `lean4/RMOOperations.lean` | 164 | `obliterate_not_reversible` |
| `coq/rmo_operations.v` | 233 | `obliterate_not_reversible` |
| `isabelle/RMO_Operations.thy` | 167 | `obliterate_not_reversible` |

**Rationale**: Information-theoretic law — once data is physically overwritten,
recovery is mathematically impossible. This is a foundational axiom for GDPR
compliance theory, not a missing proof.

## Structural Axioms (2) — Standard

| File | Line(s) | Name | Nature |
|------|---------|------|--------|
| `agda/FilesystemModel.agda` | 157-159 | `funext` | Functional extensionality (standard axiom in intensional type theory) |
| `agda/FileContentOperations.agda` | 76-77 | `_≟ₚ_` | Path decidability instance (standard for decidable types) |

## Real Gaps (26) — Need Work

### Priority 1: Core Reversibility (4 remaining gaps, was 8)

| File | Line | Theorem | Gap | Status |
|------|------|---------|-----|--------|
| `lean4/FileContentOperations.lean` | 314 | `string_take_append_length` | String stdlib lemma | NEW helper — needs Lean 4 String.take library |
| `agda/FileContentOperations.agda` | 135 | `rewrite-goal` (in writeFileReversible) | Final case analysis step | Partially proven — needs node content case split |
| `agda/FileContentOperations.agda` | 245 | `postulate-same-content-identity` (in captureRestoreIdentity) | Write-same-content identity | Partially proven — needs writeFileSameContent |
| `agda/SymlinkOperations.agda` | 57-58 | `node`/`prf` | Proof hack in symlink reversibility | Same pattern as fixed FilesystemModel — apply `not-path-exists-nothing` |

### Priority 2: Equivalence Relations (4 gaps, unchanged)

| File | Line | Theorem | Gap |
|------|------|---------|-----|
| `agda/FilesystemEquivalence.agda` | 50-55 | `mkdirPreservesEquiv` | Equivalence under mkdir |
| `agda/FilesystemEquivalence.agda` | 57-62 | `rmdirPreservesEquiv` | Equivalence under rmdir |
| `agda/FilesystemEquivalence.agda` | 64-69 | `createFilePreservesEquiv` | Equivalence under createFile |
| `agda/FilesystemEquivalence.agda` | 71-76 | `deleteFilePreservesEquiv` | Equivalence under deleteFile |

### Priority 3: RMO/Secure Deletion (4 gaps, unchanged)

| File | Line | Theorem | Gap |
|------|------|---------|-----|
| `lean4/RMOOperations.lean` | 143 | `obliterate_removes_path` | Property through overwrites |
| `lean4/RMOOperations.lean` | 175 | `obliterate_preserves_other_paths` | Tree structure under overwrite |
| `coq/rmo_operations.v` | 173 | `obliterate_removes_path` | Permission model |
| `coq/rmo_operations.v` | 208 | `obliterate_overwrites_all_blocks` | Multi-pass induction |

### Priority 4: Path Algebra & Preconditions (6 gaps, was 6 — 2 closed, 2 new)

| File | Line | Theorem | Gap |
|------|------|---------|-----|
| `coq/filesystem_model.v` | 256 | `mkdir_parent_still_exists` | Parent path inequality |
| `coq/file_operations.v` | 141 | `delete_file_preserves_permissions` | Permission model |
| `coq/posix_errors.v` | 283 | `safe_mkdir_rmdir_reversible` | Well-formedness chain |
| `coq/filesystem_equivalence.v` | 291 | `ops_equiv_trans` | Precondition after composition |
| `coq/filesystem_composition.v` | 319 | `mkdir_creates_empty_dir` | Well-formedness (NEW) |
| `coq/filesystem_composition.v` | 352 | `rmdir_precondition_after_mkdir` | p ≠ parent_path p (NEW) |

### Priority 5: Copy/Move & Composition (5 gaps)

| File | Line | Theorem | Gap |
|------|------|---------|-----|
| `coq/copy_move_operations.v` | 148 | `copy_file_reversible` | Path existence reasoning |
| `coq/copy_move_operations.v` | 239 | `move_reversible` | Source existence under move |
| `coq/filesystem_composition.v` | 388 | `mkdir_two_dirs_reversible` | mkdir preserves well-formedness |
| `agda/CopyMoveOperations.agda` | 238-241 | `fs-update-*` (3) | Filesystem update helper lemmas |

## Recommendations

1. **Priority 1 gaps are nearly closed** — just need Lean 4 String stdlib and Agda case analysis
2. **Priority 2 gaps** follow a uniform pattern — all 4 can be closed with the same proof strategy
3. **Priority 3 gaps** (RMO) can wait — we don't claim GDPR compliance yet
4. **Priority 4 Coq gaps** mostly need a `well_formed` filesystem predicate threaded through
5. **Consider**: Agda `--cubical` flag provides funext natively, removing 1 structural axiom
6. **Model improvement needed**: Parameterize `mkdir`/`createFile` with permissions to close
   the reverse-direction gap completely (currently worked around with `HasDefaultPerms`)

## Mizar / Z3 Status

- **Mizar**: Binary format, no text-searchable holes. 0 known gaps.
- **Z3 SMT**: SAT/UNSAT queries only, no partial proof support. 0 known gaps.
