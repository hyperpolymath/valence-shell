# ECHIDNA Integration Plan - Valence Shell

**Version**: 0.6.0
**Updated**: 2026-01-28
**Purpose**: Integrate ECHIDNA neurosymbolic platform for build validation

---

## Overview

**ECHIDNA** (Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance) is a neurosymbolic theorem proving platform supporting 12 theorem provers with aspect tagging and neural proof synthesis.

**Integration Goal**: Use ECHIDNA to validate valence-shell builds against Lean 4 theorems, providing automated property-based testing and proof checking in CI/CD.

---

## What ECHIDNA Provides

### 1. Universal Prover Backend
Supports all proof systems valence-shell uses:
- ✅ **Lean 4** (Tier 1) - Primary source of truth
- ✅ **Coq/Rocq** (Tier 1) - Cross-validation
- ✅ **Agda** (Tier 1) - Cross-validation
- ✅ **Isabelle** (Tier 1) - Cross-validation
- ✅ **Z3** (Tier 1) - SMT solving
- ✅ **CVC5** (Tier 1) - SMT solving
- ✅ **Mizar** (Tier 2) - Cross-validation

### 2. Neurosymbolic AI
- Neural proof synthesis
- ML-based theorem suggestion
- Probabilistic logic (DeepProbLog)
- Proof hint generation

### 3. Aspect Tagging
- Categorize proofs by property type
- Track which operations are verified
- Generate verification reports

### 4. Build Validation
- Check proofs compile in all systems
- Validate correspondence claims
- Generate property tests

---

## Integration Architecture

```
┌──────────────────────────────────────────┐
│  Valence Shell Build                     │
│  (Rust CLI + BEAM daemon)                │
└────────────────┬─────────────────────────┘
                 │ Pre-deployment
                 ↓
┌──────────────────────────────────────────┐
│  ECHIDNA Validation Pipeline             │
│                                          │
│  1. Load Lean 4 proofs                   │
│  2. Cross-check in 6 proof systems       │
│  3. Generate property tests              │
│  4. Validate Rust correspondence         │
│  5. Check BEAM daemon properties         │
└────────────────┬─────────────────────────┘
                 │ Validation report
                 ↓
┌──────────────────────────────────────────┐
│  CI/CD Decision                          │
│  - Pass: Deploy build                    │
│  - Fail: Block deployment                │
└──────────────────────────────────────────┘
```

---

## Phase 1: Basic Integration (Week 1-2)

### 1.1 Add ECHIDNA as Dependency

**File**: `valence-shell/.tool-versions`
```bash
# Add ECHIDNA
echidna latest  # or specific version
```

**File**: `valence-shell/Cargo.toml` (workspace)
```toml
[workspace.dependencies]
echidna-prover-api = { git = "https://github.com/hyperpolymath/echidna", branch = "main" }
```

### 1.2 Create Validation Script

**File**: `valence-shell/scripts/validate-with-echidna.sh`
```bash
#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# Validate valence-shell build with ECHIDNA

set -euo pipefail

echo "=== ECHIDNA Validation Pipeline ==="

# Step 1: Verify all proofs compile
echo "1. Compiling proofs in 6 systems..."
echidna verify proofs/lean4/
echidna verify proofs/coq/
echidna verify proofs/agda/
echidna verify proofs/isabelle/
echidna verify proofs/mizar/
echidna verify proofs/z3/

# Step 2: Cross-validate theorems
echo "2. Cross-validating theorems..."
echidna cross-validate \
  --theorem mkdir_rmdir_reversible \
  --systems lean4,coq,agda,isabelle,mizar

# Step 3: Generate property tests
echo "3. Generating property tests..."
echidna generate-properties \
  --input proofs/lean4/FilesystemModel.lean \
  --output tests/echidna-properties.rs \
  --format rust

# Step 4: Run property tests
echo "4. Running generated property tests..."
cd impl/rust-cli
cargo test --test echidna-properties

# Step 5: Validate correspondence
echo "5. Validating Lean 4 → Rust correspondence..."
echidna validate-correspondence \
  --spec proofs/lean4/ \
  --impl impl/rust-cli/src/ \
  --mapping docs/LEAN4_RUST_CORRESPONDENCE.md

echo "=== Validation Complete ==="
```

### 1.3 CI/CD Integration

**File**: `.github/workflows/echidna-validation.yml`
```yaml
# SPDX-License-Identifier: PMPL-1.0-or-later
name: ECHIDNA Validation

on:
  push:
    branches: [main, develop]
  pull_request:

permissions: read-all

jobs:
  validate:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install ECHIDNA
        run: |
          # Install from release or build from source
          curl -L https://github.com/hyperpolymath/echidna/releases/latest/download/echidna-x86_64-linux.tar.gz | tar xz
          echo "$PWD" >> $GITHUB_PATH

      - name: Run ECHIDNA validation
        run: bash scripts/validate-with-echidna.sh

      - name: Upload validation report
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: echidna-validation-report
          path: echidna-report.md
```

---

## Phase 2: Property Generation (Week 3-4)

### 2.1 Automated Property Extraction

ECHIDNA can analyze Lean 4 proofs and generate Rust property tests:

**Input**: `proofs/lean4/FilesystemModel.lean`
```lean
theorem mkdir_rmdir_reversible (p : Path) (fs : Filesystem) :
  mkdir_precondition p fs →
  rmdir p (mkdir p fs) = fs
```

**Output**: `tests/echidna-properties.rs`
```rust
// Auto-generated by ECHIDNA
use proptest::prelude::*;

proptest! {
    #[test]
    fn prop_mkdir_rmdir_reversible(path in valid_path_strategy()) {
        let temp = tempdir().unwrap();
        let test_path = temp.path().join(&path);

        // Assume preconditions
        if !mkdir_precondition(&test_path) {
            return Ok(());
        }

        // Snapshot before
        let fs_before = snapshot_filesystem(&temp);

        // mkdir then rmdir
        fs::create_dir(&test_path).unwrap();
        fs::remove_dir(&test_path).unwrap();

        // Snapshot after
        let fs_after = snapshot_filesystem(&temp);

        // Assert equality
        prop_assert_eq!(fs_before, fs_after);
    }
}
```

### 2.2 Fuzzing with Neural Guidance

ECHIDNA's neural component suggests interesting test cases:

```rust
// Neural-guided fuzzing
echidna fuzz \
  --target impl/rust-cli/src/commands.rs \
  --properties tests/echidna-properties.rs \
  --neural-hints on \
  --iterations 10000
```

---

## Phase 3: Correspondence Validation (Week 5-6)

### 3.1 Automated Correspondence Checking

ECHIDNA can parse both Lean 4 and Rust to validate correspondence claims:

**Input**: `docs/LEAN4_RUST_CORRESPONDENCE.md`
```markdown
## mkdir Correspondence

Lean 4: `proofs/lean4/FilesystemModel.lean:45-60`
Rust: `impl/rust-cli/src/commands.rs:14-55`

Correspondence: ✅ Both check same preconditions
```

**ECHIDNA validates**:
1. Referenced file locations exist
2. Preconditions match between Lean 4 and Rust
3. Error handling is equivalent
4. Test coverage for each claim

### 3.2 Aspect Tagging for Verification Coverage

```bash
echidna aspect-tag proofs/lean4/ --output verification-coverage.md
```

**Output**: `verification-coverage.md`
```markdown
# Verification Coverage Report

## mkdir Operation
- ✅ Reversibility: Proven (Lean 4, Coq, Agda, Isabelle, Mizar)
- ✅ Preconditions: Implemented (Rust)
- ✅ Error handling: EEXIST, ENOENT (Rust)
- ⚠️ Parent writability: Delegated to OS
- ✅ Tests: 5/5 passing

## rmdir Operation
- ✅ Reversibility: Proven (Lean 4, Coq, Agda, Isabelle, Mizar)
- ✅ Preconditions: Implemented (Rust)
- ✅ Error handling: ENOENT, ENOTDIR, ENOTEMPTY (Rust)
- ⚠️ Root check: Missing in Rust (TODO)
- ✅ Tests: 4/5 passing (root check missing)
```

---

## Phase 4: BEAM Daemon Validation (Week 7-8)

### 4.1 Ecto Schema Validation

ECHIDNA can validate database schemas match Lean 4 models:

**Lean 4 Model**: Audit log structure
**Ecto Schema**: `impl/elixir/lib/vsh/audit_log.ex`

ECHIDNA checks:
- Field types match
- Constraints enforce invariants
- Migrations preserve properties

### 4.2 OTP Supervision Verification

Validate that supervision trees preserve filesystem invariants:

```bash
echidna validate-supervision \
  --elixir impl/elixir/lib/vsh/application.ex \
  --properties proofs/lean4/FilesystemComposition.lean
```

---

## Integration with Existing Tests

### Current Test Suite
- ✅ `tests/integration_test.sh` (28/28 passing)
- ✅ `impl/rust-cli/src/` unit tests

### ECHIDNA Additions
- **Property tests**: Generated from Lean 4
- **Fuzzing**: Neural-guided input generation
- **Correspondence checks**: Automated validation
- **Coverage reports**: Aspect tagging

### Combined CI/CD Flow

```yaml
jobs:
  test:
    steps:
      # 1. Unit tests (fast)
      - run: cargo test

      # 2. Integration tests (medium)
      - run: bash tests/integration_test.sh

      # 3. ECHIDNA validation (slow, only on main/PR)
      - if: github.ref == 'refs/heads/main' || github.event_name == 'pull_request'
        run: bash scripts/validate-with-echidna.sh
```

---

## Benefits

### 1. Automated Proof Checking
- No manual verification of all 6 proof systems
- CI/CD catches proof regressions
- Cross-validation increases confidence

### 2. Property-Based Testing
- Automatically generates test cases from theorems
- Finds edge cases humans miss
- Neural guidance explores interesting inputs

### 3. Correspondence Validation
- Ensures Rust matches Lean 4 specs
- Catches drift between proofs and implementation
- Documents verification coverage

### 4. Build Confidence
- Hash validated builds
- Deployment only if all checks pass
- Audit trail of validation

---

## Implementation Checklist

### Prerequisites
- [ ] ECHIDNA installed and available
- [ ] `.tool-versions` updated
- [ ] Validation scripts created

### Phase 1 (Basic)
- [ ] Proof compilation checks
- [ ] Cross-validation setup
- [ ] CI/CD integration

### Phase 2 (Properties)
- [ ] Property generation from Lean 4
- [ ] Neural fuzzing setup
- [ ] Test suite integration

### Phase 3 (Correspondence)
- [ ] Automated correspondence checking
- [ ] Aspect tagging reports
- [ ] Coverage tracking

### Phase 4 (BEAM)
- [ ] Ecto schema validation
- [ ] Supervision tree checks
- [ ] Distributed properties

---

## Timeline

| Week | Phase | Deliverables |
|------|-------|-------------|
| 1-2 | Phase 1 | Basic CI/CD integration |
| 3-4 | Phase 2 | Property tests generated |
| 5-6 | Phase 3 | Correspondence validated |
| 7-8 | Phase 4 | BEAM daemon checked |

**Total**: 8 weeks to full ECHIDNA integration

---

## Open Questions

1. **ECHIDNA API stability** - Is the API stable enough for CI/CD?
2. **Performance** - How long does validation take?
3. **False positives** - How to tune neural guidance?
4. **Coverage goals** - What % correspondence validation is sufficient?

---

## Related Documentation

- `docs/ARCHITECTURE.md` - Hybrid Rust+BEAM architecture
- `docs/LEAN4_RUST_CORRESPONDENCE.md` - Manual correspondence proofs
- `docs/POSIX_COMPLIANCE.md` - Incremental roadmap
- `STATE.scm` - Current project state

---

**Last Updated**: 2026-01-28
**Author**: Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
**License**: PMPL-1.0-or-later
