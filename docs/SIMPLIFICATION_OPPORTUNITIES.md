# Simplification Opportunities for Contributors

## The Current Barrier to Entry

**Reality check**: Valence Shell is intimidating. Here's what a potential contributor sees:

1. 6 proof systems (Coq, Lean 4, Agda, Isabelle, Mizar, Z3)
2. ~15,000 lines of Rust
3. 256+ theorems
4. Formal verification, correspondence checking, property testing
5. "Formally verified" in README

**Result**: "I can't contribute unless I'm a verification expert"

This is **killing your contributor pipeline**.

---

## Simplification Strategy

### 1. Split the Repository

**Problem**: Everything is in one repo, implying everything is equally important

**Solution**: Separate concerns

```
hyperpolymath/valence-shell          ← Main repo (Rust implementation)
├── impl/rust-cli/                   ← Shell implementation
├── tests/                           ← Tests (no proofs)
├── README.md                        ← User-focused
└── CONTRIBUTING.md                  ← Rust-only guide

hyperpolymath/valence-shell-proofs   ← Verification repo (optional)
├── lean4/                           ← Lean 4 proofs
├── coq/                             ← Coq proofs
├── idris2/                          ← Idris2 proofs (future core)
├── README.md                        ← Proof-focused
└── CORRESPONDENCE.md                ← How proofs relate to impl

hyperpolymath/valence-shell-verified ← v2.0 extracted core (future)
├── idris2/src/                      ← Idris2 source
├── extracted/c/                     ← Extracted C code
└── ffi/rust/                        ← Rust FFI bindings
```

**Benefits**:
✅ Main repo looks like normal Rust project
✅ Proofs are optional reference
✅ Contributors can ignore proofs entirely
✅ Verification experts can focus on proofs repo

**Workflow**:
- Main development happens in `valence-shell` repo
- Proofs updated in `valence-shell-proofs` repo (before releases)
- CI in main repo runs tests, CI in proofs repo checks verification

---

### 2. Contributor Tiers

**Current**: Everyone needs to understand everything

**Better**: Define clear contribution levels

#### Tier 1: "Feature Contributors" (No verification knowledge needed)
**What they do**:
- Add new shell features
- Fix bugs
- Improve UI/UX
- Add tests

**What they DON'T need**:
- Proof assistant knowledge
- Correspondence checking
- Formal verification

**Contribution process**:
```bash
1. Fork valence-shell repo
2. Write Rust code
3. Write tests (property tests from spec, we provide template)
4. Run: cargo test
5. Submit PR

Maintainers handle verification
```

**Example features suitable for Tier 1**:
- Add new built-in command
- Improve tab completion
- Better error messages
- Syntax highlighting
- History search

---

#### Tier 2: "Core Contributors" (Some verification awareness)
**What they do**:
- Modify state machine
- Change undo/redo logic
- Alter safety-critical code

**What they need**:
- Understand formal specifications (read Lean 4, not write it)
- Write property tests that match specs
- Run correspondence validation

**Contribution process**:
```bash
1. Fork valence-shell repo
2. Read formal spec (Lean 4 proof, we explain it)
3. Write Rust code
4. Write property tests matching spec
5. Run: ./scripts/validate-correspondence.sh
6. Submit PR (include test output)

Maintainers verify proofs match
```

**Example features suitable for Tier 2**:
- New reversible operation
- Modify undo algorithm
- Change state machine behavior

---

#### Tier 3: "Verification Experts" (Proof assistants)
**What they do**:
- Update formal proofs
- Add new theorems
- Verification sweeps

**What they need**:
- Lean 4 / Idris2 knowledge
- Theorem proving skills

**Contribution process**:
```bash
1. Fork valence-shell-proofs repo
2. Update Lean 4 proofs
3. Run: lean --check
4. Submit PR to proofs repo

Linked to implementation PR
```

---

### 3. Documentation Layering

**Current**: One README tries to explain everything

**Better**: Docs for each audience

```
docs/
├── USER_GUIDE.md                    ← End users (install, use, undo/redo)
├── CONTRIBUTOR_GUIDE_TIER1.md       ← Feature contributors (Rust only)
├── CONTRIBUTOR_GUIDE_TIER2.md       ← Core contributors (specs + Rust)
├── VERIFICATION_GUIDE.md            ← Verification experts
├── ARCHITECTURE.md                  ← High-level design
├── PROOF_OVERVIEW.md                ← Non-expert explanation of proofs
└── API_REFERENCE.md                 ← Rust API docs
```

**Example: PROOF_OVERVIEW.md** (for non-experts):
```markdown
# What Are These Proofs?

## For Non-Experts

The proofs guarantee that undo/redo works correctly. For example:

**English**: "If you create a directory, then undo, you get back to where you started."

**Lean 4 Proof**:
```lean
theorem mkdir_undo_inverse :
  ∀ (fs : Filesystem) (path : Path),
  undo (mkdir path fs) = fs
```

**Property Test** (validates proof):
```rust
#[test]
fn prop_mkdir_undo_inverse() {
    proptest!(|(path in any::<String>())| {
        let before = get_state();
        mkdir(&path);
        undo();
        let after = get_state();
        assert_eq!(before, after);
    });
}
```

**You don't need to understand the proof.** Just know:
1. The proof guarantees correctness
2. Property tests verify the Rust code matches the proof
3. If property tests pass, the Rust code is probably correct
```

---

### 4. Template-Based Contributions

**Problem**: Contributors don't know how to write property tests

**Solution**: Provide templates

Create `scripts/new-operation-template.sh`:

```bash
#!/bin/bash
# Template generator for new reversible operations

OPERATION_NAME=$1  # e.g., "chmod"

cat > "impl/rust-cli/src/commands/${OPERATION_NAME}.rs" <<EOF
// SPDX-License-Identifier: PLMP-1.0-or-later
//! ${OPERATION_NAME^} operation
//!
//! Formal specification: proofs/lean4/Operations/${OPERATION_NAME^}.lean
//!
//! Property tests: tests/property_tests.rs::prop_${OPERATION_NAME}

use crate::state::ShellState;
use crate::error::VshError;

pub fn ${OPERATION_NAME}(
    state: &mut ShellState,
    // TODO: Add parameters
) -> Result<(), VshError> {
    // TODO: Implement operation

    // Record in history for undo
    state.push_history(Operation::${OPERATION_NAME^} {
        // TODO: Save undo information
    });

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_${OPERATION_NAME}_basic() {
        // TODO: Basic functionality test
    }

    #[test]
    fn test_${OPERATION_NAME}_undo() {
        // TODO: Undo test
    }
}
EOF

cat >> "impl/rust-cli/tests/property_tests.rs" <<EOF

/// Property: ${OPERATION_NAME} is reversible
#[test]
fn prop_${OPERATION_NAME}_reversible() {
    proptest!(|(/* TODO: parameters */)| {
        let temp = TempDir::new().unwrap();
        let mut state = ShellState::new(temp.path()).unwrap();

        // Capture initial state
        let before = /* TODO: get state */;

        // Perform operation
        ${OPERATION_NAME}(&mut state, /* TODO: args */).unwrap();

        // Undo
        state.pop_undo().unwrap();

        // Verify restored
        let after = /* TODO: get state */;
        prop_assert_eq!(before, after);
    });
}
EOF

echo "✓ Created template for ${OPERATION_NAME}"
echo "Next steps:"
echo "  1. Fill in TODOs in impl/rust-cli/src/commands/${OPERATION_NAME}.rs"
echo "  2. Fill in TODOs in impl/rust-cli/tests/property_tests.rs"
echo "  3. Run: cargo test"
echo "  4. Submit PR (maintainers will handle proofs)"
```

**Usage**:
```bash
./scripts/new-operation-template.sh chmod
# Creates skeleton code with TODOs
# Contributor fills in TODOs
# Property tests verify correctness
```

---

### 5. Progressive Verification

**Problem**: All-or-nothing verification is too rigid

**Better**: Graduated verification levels

```rust
// In impl/rust-cli/src/lib.rs

#[derive(Debug, Clone, Copy)]
pub enum VerificationLevel {
    /// No verification, just tests (85% confidence)
    Tested,

    /// Property tests + correspondence validation (90% confidence)
    Validated,

    /// Lean 4 proof exists and validates (95% confidence)
    Proven,

    /// Idris2 extracted code (99%+ confidence)
    Extracted,
}

pub struct Operation {
    name: String,
    verification_level: VerificationLevel,
    // ... other fields
}
```

**Show verification level in help**:
```bash
$ vsh help

Operations:
  mkdir      Create directory            [EXTRACTED] ✓✓✓
  rmdir      Remove directory            [EXTRACTED] ✓✓✓
  touch      Create file                 [PROVEN]    ✓✓
  chmod      Change permissions          [VALIDATED] ✓
  history    Show command history        [TESTED]    ✓

Legend:
  [EXTRACTED] - 99%+ confidence (extracted from verified code)
  [PROVEN]    - 95% confidence (proven in Lean 4)
  [VALIDATED] - 90% confidence (property tests + correspondence)
  [TESTED]    - 85% confidence (unit + integration tests)
```

**Benefits**:
✅ Contributors can add `[TESTED]` features easily
✅ Verification experts can promote to `[PROVEN]`
✅ Users see what's verified
✅ Gradual improvement over time

---

### 6. Contribution Examples

Create `docs/examples/`:

```
docs/examples/
├── 01-add-builtin-command.md        ← Easy: Add `pwd` built-in
├── 02-add-reversible-operation.md   ← Medium: Add `ln -s` (symlink)
├── 03-modify-state-machine.md       ← Hard: Change undo algorithm
├── 04-write-property-test.md        ← Show how to write property tests
└── 05-update-lean-proof.md          ← For verification experts
```

**Example: docs/examples/01-add-builtin-command.md**:
```markdown
# Example: Adding `pwd` Built-in Command

Difficulty: ⭐ Easy (Tier 1 contributor, no verification needed)

## Step 1: Add command enum variant

Edit `impl/rust-cli/src/parser.rs`:
```rust
pub enum Command {
    // ... existing variants
    Pwd,  // NEW
}
```

## Step 2: Implement command

Edit `impl/rust-cli/src/builtins.rs`:
```rust
pub fn builtin_pwd(state: &ShellState) -> Result<(), VshError> {
    println!("{}", state.current_dir.display());
    Ok(())
}
```

## Step 3: Wire up parser

Edit `impl/rust-cli/src/parser.rs`:
```rust
fn parse_builtin(&mut self) -> Result<Command> {
    match self.current_token() {
        // ... existing builtins
        "pwd" => Ok(Command::Pwd),  // NEW
    }
}
```

## Step 4: Wire up executor

Edit `impl/rust-cli/src/executable.rs`:
```rust
match command {
    // ... existing commands
    Command::Pwd => builtin_pwd(&state)?,  // NEW
}
```

## Step 5: Add tests

Edit `impl/rust-cli/tests/builtin_tests.rs`:
```rust
#[test]
fn test_pwd() {
    let temp = TempDir::new().unwrap();
    let state = ShellState::new(temp.path()).unwrap();

    builtin_pwd(&state).unwrap();
    // Check stdout contains temp.path()
}
```

## Step 6: Submit PR

```bash
cargo test
git commit -m "Add pwd built-in command"
gh pr create
```

**Verification**: Not needed for this command (read-only, no state changes)
```

---

### 7. Lower the Verification Language Barrier

**Problem**: Lean 4 syntax is intimidating

**Solution**: Provide English translations

Create `proofs/lean4/ENGLISH_SPECS.md`:

```markdown
# Formal Specifications in English

This document translates Lean 4 proofs to plain English.

## mkdir_rmdir_reversible

**Lean 4**:
```lean
theorem mkdir_rmdir_reversible :
  ∀ (fs : Filesystem) (path : Path),
  (mkdir_precondition path fs) →
  (rmdir path (mkdir path fs)) = fs
```

**English**:
"For any filesystem and path, if mkdir's preconditions are met,
then removing the directory after creating it gives you back the
original filesystem."

**Preconditions**:
1. Path is not root
2. Parent directory exists
3. Path doesn't already exist

**Property Test** (impl/rust-cli/tests/property_tests.rs:42):
```rust
#[test]
fn prop_mkdir_rmdir_reversible() {
    // Validates the Lean 4 proof
}
```

---

## touch_rm_reversible

**Lean 4**:
```lean
theorem touch_rm_reversible :
  ∀ (fs : Filesystem) (path : Path),
  (rm path (touch path fs)) = fs
```

**English**:
"Creating a file and then removing it restores the original filesystem."

**Property Test** (impl/rust-cli/tests/property_tests.rs:89):
```rust
#[test]
fn prop_touch_rm_reversible() {
    // Validates the Lean 4 proof
}
```
```

---

### 8. Modular Verification

**Current**: Can't contribute without all verification infrastructure

**Better**: Verification is optional per module

```
impl/rust-cli/src/
├── core/                  ← Safety-critical (requires verification)
│   ├── state.rs          ← Must have Lean 4 proof
│   ├── undo.rs           ← Must have Lean 4 proof
│   └── operations.rs     ← Must have Lean 4 proof
│
├── extended/              ← Important (verification encouraged)
│   ├── redirections.rs   ← Should have proof, not required
│   ├── pipelines.rs      ← Should have proof, not required
│   └── job_control.rs    ← Should have proof, not required
│
└── ui/                    ← Non-critical (tests only)
    ├── repl.rs           ← Tests sufficient
    ├── completion.rs     ← Tests sufficient
    └── prompt.rs         ← Tests sufficient
```

**Benefits**:
- Contributors know where verification is required
- Can add UI features without verification
- Core remains formally verified

---

## Summary: Simplification Roadmap

### Immediate (This Week):
1. ✅ Write VERIFICATION_STRATEGY_ANALYSIS.md (done)
2. ✅ Write SIMPLIFICATION_OPPORTUNITIES.md (this document)
3. Create CONTRIBUTOR_GUIDE_TIER1.md (Rust-only guide)
4. Add "No verification needed for most contributions!" to README

### Short-term (Next Month):
1. Create contribution templates (`scripts/new-operation-template.sh`)
2. Write docs/examples/ (5 example contributions)
3. Add ENGLISH_SPECS.md (translate proofs to plain English)
4. Mark verification level in code (Tested/Validated/Proven/Extracted)

### Medium-term (v1.0):
1. Split repos (main vs proofs)
2. Implement progressive verification (tier 1/2/3)
3. Make verification optional in CI (non-blocking)

### Long-term (v2.0):
1. Idris2 extraction (core is automatically verified)
2. Contributors never touch proofs (core is extracted, rest is tested)

---

## Expected Impact

**Current state**:
- Potential contributors: ~10 (need verification expertise)
- Contribution rate: 1-2 per year
- Barrier: "I can't help unless I know Lean 4"

**After simplification**:
- Potential contributors: ~1000+ (any Rust developer)
- Contribution rate: 5-10 per month
- Message: "Write Rust, we handle verification"

**This is the difference between a research project and an open-source project.**

---

## Validation: Will This Work?

Look at successful verified projects:

### CompCert (Verified C Compiler)
- **Core team**: 5-10 verification experts
- **Contributors**: 50+ (most don't touch proofs)
- **Strategy**: Verification experts maintain proofs, community adds features

### seL4 (Verified Microkernel)
- **Core team**: 20+ verification experts (Data61)
- **Contributors**: 100+ (drivers, userspace, tools)
- **Strategy**: Kernel is verified, ecosystem is tested

### Valence Shell (Your Project)
- **Core team**: 1 (you) + future verification experts
- **Contributors**: 0 (currently) → 50+ (after simplification)
- **Strategy**: Core extracted from Idris2, features tested with property tests

**Key insight**: You don't need every contributor to know verification. You need:
1. **Small team**: Maintain formal proofs
2. **Large community**: Add features, tests, improvements
3. **Clear boundary**: What needs verification vs what needs tests

By lowering the barrier, you enable the large community while preserving verification quality.
