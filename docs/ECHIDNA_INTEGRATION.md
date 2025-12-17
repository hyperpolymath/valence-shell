# ECHIDNA Integration Guide

This document describes how to integrate Valence Shell with ECHIDNA, the neurosymbolic theorem proving platform.

## Overview

[ECHIDNA](https://github.com/hyperpolymath/echidna) (Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance) is a unified multi-prover system that combines neural proof synthesis with symbolic verification across 12 different theorem provers.

### Benefits for Valence Shell

1. **Automated Multi-Prover Generation**: Generate proofs in new systems (CVC5, HOL Light, Metamath) from existing Coq/Lean proofs
2. **Neural Completion**: AI-assisted completion of admitted lemmas
3. **Semantic Understanding**: OpenCyc integration for common-sense reasoning about filesystem operations
4. **Probabilistic Reasoning**: DeepProbLog for learning proof patterns

## Configuration Files

### echidna.toml

The main configuration file at the repository root:

```toml
[project]
name = "valence-shell"
version = "0.6.0"

[provers]
enabled = ["coq", "lean4", "agda", "isabelle", "z3", "cvc5"]
default = "coq"

[theorems.mkdir_rmdir_reversible]
description = "Directory creation is reversible"
category = "reversibility"
proven_in = ["coq", "lean4", "agda", "isabelle", "mizar", "z3"]
```

### echidna/specs/filesystem.json

Proof specifications in ECHIDNA's universal format:

```json
{
  "types": {
    "Path": { "kind": "alias", "target": "List PathComponent" },
    "Filesystem": { "kind": "function", "domain": "Path", "codomain": "Option FSNode" }
  },
  "theorems": [
    {
      "name": "mkdir_rmdir_reversible",
      "statement": "forall p fs, mkdir_precondition p fs -> rmdir p (mkdir p fs) = fs",
      "status": { "coq": "proven", "lean4": "proven", ... }
    }
  ]
}
```

## Supported Provers

### Tier 1 (Currently Implemented)

| Prover | Status | Files |
|--------|--------|-------|
| **Coq** | 77/78 complete | 7 files, ~1,900 lines |
| **Lean 4** | 59/59 complete | 5 files, ~850 lines |
| **Agda** | 55/55 complete | 5 files, ~750 lines |
| **Isabelle** | 44/44 complete | 5 files, ~750 lines |
| **Z3** | 15/15 assertions | 1 file, ~160 lines |

### Tier 2 (Partially Implemented)

| Prover | Status | Notes |
|--------|--------|-------|
| **Mizar** | 44/44 complete | 5 files, ~800 lines |
| **CVC5** | Pending | Generate from Z3 |
| **HOL Light** | Pending | Generate from Isabelle |
| **Metamath** | Pending | Generate from Coq |

### Tier 3-4 (Future)

- PVS, ACL2, HOL4

## Usage

### Prerequisites

```bash
# Install ECHIDNA
git clone https://github.com/hyperpolymath/echidna
cd echidna
just build

# Or via package manager (when available)
cargo install echidna
```

### Verify Existing Proofs

```bash
# Using ECHIDNA CLI
echidna verify --config echidna.toml

# Or using just
just verify-all
```

### Generate Proofs for New Systems

```bash
# Generate CVC5 from Z3
echidna generate --source z3 --target cvc5 --theorem mkdir_rmdir_reversible

# Generate HOL Light from Isabelle
echidna generate --source isabelle --target hol-light --all

# Batch generation
echidna generate --config echidna.toml --targets cvc5,hol-light,metamath
```

### Neural Completion

```bash
# Complete admitted lemmas
echidna complete --theorem mkdir_creates_rmdir_precondition

# Suggest helper lemmas
echidna suggest --file proofs/coq/filesystem_composition.v --line 333
```

## OpenCyc Integration

The configuration includes OpenCyc ontology for semantic understanding:

```cyc
(isa FileSystemOperation Action)
(isa mkdir FileSystemOperation)
(inverseOf mkdir rmdir)
(preconditionFor mkdir parentDirectoryExists)
```

This enables ECHIDNA to:
- Understand that `mkdir` and `rmdir` are inverse operations
- Know that `mkdir` requires parent directory to exist
- Suggest related theorems based on semantic similarity

## DeepProbLog Integration

Probabilistic rules for proof pattern learning:

```prolog
0.95::reverses(mkdir, rmdir).
0.95::reverses(createFile, deleteFile).
0.90::reverses(writeFile, writeOldContent).
```

This enables:
- Learning proof patterns from successful proofs
- Predicting likely theorems
- Suggesting proof strategies

## Theorem Categories

| Category | Description | Examples |
|----------|-------------|----------|
| `reversibility` | Operations can be undone | `mkdir_rmdir_reversible` |
| `composition` | Multiple operations compose | `operation_sequence_reversible` |
| `equivalence` | Filesystem state equality | `fs_equiv_refl`, `fs_equiv_trans` |
| `content` | File content operations | `write_file_reversible` |
| `maa` | MAA framework integration | `modification_reversible` |
| `path` | Path helper lemmas | `parent_path_ne_self` |

## Aspect Tags

Theorems are tagged with aspects for intelligent categorization:

- `filesystem` - Related to filesystem operations
- `directory` - Directory-specific
- `file` - File-specific
- `undo` - Supports undo/rollback
- `cno` - Certified Null Operation
- `identity` - Identity element properties
- `algebraic` - Algebraic structure properties
- `maa` - MAA framework specific
- `audit` - Audit trail related

## CI/CD Integration

Add to `.gitlab-ci.yml`:

```yaml
echidna-verify:
  stage: test
  script:
    - echidna verify --config echidna.toml
  rules:
    - changes:
      - proofs/**/*
```

## Known Limitations

1. **is_empty_dir semantics**: One admitted proof in Coq related to path prefix semantics
2. **Neural completion**: Requires trained model (not yet available for filesystem proofs)
3. **Tier 3-4 provers**: Not yet implemented in ECHIDNA

## Roadmap

1. **Phase 1** (Current): Configuration and specification files
2. **Phase 2**: Generate CVC5, HOL Light, Metamath proofs
3. **Phase 3**: Train neural model on filesystem proof patterns
4. **Phase 4**: Complete admitted lemmas with neural assistance
5. **Phase 5**: Extend to PVS, ACL2, HOL4

## Resources

- [ECHIDNA Repository](https://github.com/hyperpolymath/echidna)
- [ECHIDNA Documentation](https://echidna.dev/docs)
- [Valence Shell Proofs](../proofs/)
- [Proof Status](../PROOF_STATUS.md)

## Contributing

To add support for a new theorem:

1. Add theorem to `echidna.toml` under `[theorems]`
2. Add specification to `echidna/specs/filesystem.json`
3. Implement in at least one Tier 1 prover
4. Run `echidna generate` to create proofs for other systems
5. Submit PR with all generated proofs

---

**Last Updated**: 2025-12-17
**ECHIDNA Version**: Compatible with 0.1.x
