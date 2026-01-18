# Changelog

All notable changes to Valence Shell will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

**Note**: Versions 0.x.x are pre-release. Breaking changes may occur between minor versions.

## [Unreleased]

### Added
- RSR (Rhodium Standard Repository) compliance
  - LICENSE.txt (dual MIT + Palimpsest v0.8)
  - SECURITY.md policy
  - CONTRIBUTING.md with TPCF framework
  - CODE_OF_CONDUCT.md
  - MAINTAINERS.md
  - This CHANGELOG.md
  - .well-known/ directory (RFC 9116 compliant)
  - RSR_COMPLIANCE.md verification

## [0.5.0] - 2025-11-22

### Added
- **Phase 3 Initial: File Content Operations**
  - File content read/write operations in Coq (~330 lines)
  - File content operations in Lean 4 (~210 lines)
  - File content operations in Agda (~180 lines)
  - Proven reversibility: `write(old, write(new, fs)) = fs`
  - Proven independence: operations on different paths don't interfere
  - State capture/restore for undo/redo
  - FileModificationRecord for MAA audit trail

- **Equivalence Theory Completion**
  - Mizar equivalence proofs (~190 lines)
  - All 5 manual proof assistants now have complete equivalence theory
  - CNO = identity element proven in 5 systems

### Statistics
- Proof files: 23 → 27
- Proof lines: ~3,180 → ~4,280
- Total theorems: ~217 → ~256
- Systems with equivalence: 4/5 → 5/5 ✅
- Systems with content ops: 0 → 3

### Documentation
- docs/PHASE3_INITIAL_REPORT.md (comprehensive phase report)

## [0.4.0] - 2025-11-22

### Added
- **Phase 2: Composition & Equivalence Theory**
  - Composition theorems in Coq, Lean 4, Agda, Isabelle
  - Equivalence relations in Coq
  - Z3 SMT encoding for automated verification
  - CNO (Certified Null Operations) connection
  - Mizar composition framework

- **Infrastructure**
  - Containerfile for reproducible builds
  - Complete justfile with 25+ recipes
  - scripts/verify-proofs.sh multi-prover orchestration

### Fixed
- Agda composition admitted lemmas completed
- Isabelle composition `sorry` statements resolved

### Statistics
- Proof files: 19 → 23 (+4)
- Proof lines: ~2,280 → ~3,180 (+900)
- Total proofs: ~130 → ~217 (+87)

### Documentation
- docs/PHASE2_REPORT.md
- SESSION_COMPLETE.md
- INTEGRATION_SUMMARY.md

## [0.3.0] - 2025-11-22 (Early)

### Added
- **Isabelle/HOL and Mizar Support**
  - Filesystem model in Isabelle/HOL
  - File operations in Isabelle/HOL
  - Filesystem model in Mizar
  - File operations in Mizar
  - Cross-validation across 5 proof systems

### Changed
- Expanded to 5 proof assistants (was 3)
- Polyglot verification now includes different logical foundations

## [0.2.0] - 2025-11-21

### Added
- **Lean 4 and Agda Support**
  - Complete filesystem model in Lean 4
  - Complete file operations in Lean 4
  - Complete filesystem model in Agda
  - Complete file operations in Agda
  - Cross-validation between dependent type theories

### Changed
- Proofs now in 3 systems: Coq, Lean 4, Agda
- Improved proof modularity

### Documentation
- Added proof system comparison documentation

## [0.1.0] - 2025-11-20

### Added
- **Initial Coq Proofs**
  - Filesystem model with paths, nodes, permissions
  - mkdir/rmdir operations with reversibility proof
  - create_file/delete_file operations with reversibility proof
  - POSIX error modeling (EEXIST, ENOENT, EACCES, etc.)
  - Extraction framework to OCaml

- **OCaml Implementation**
  - FFI to POSIX syscalls
  - Audit logging hooks for MAA
  - Path resolution and sandboxing

- **Elixir Reference Implementation**
  - Matches Coq specification
  - POSIX error handling
  - Reversible operations (RMR primitives)

- **Core Theorems** (Coq only)
  - `mkdir_rmdir_reversible`
  - `create_delete_file_reversible`
  - `operation_independence`
  - `path_preservation`
  - Error code correctness

### Documentation
- CLAUDE.md (AI assistant context)
- docs/PROGRESS_REPORT.md
- docs/ARCHITECTURE.adoc
- proofs/README.md

### Infrastructure
- justfile build automation
- scripts/demo_verified_operations.sh
- Nix flake for reproducible builds
- GitLab CI/CD configuration

## [0.0.1] - 2025-11-19

### Added
- Initial project structure
- Basic MAA framework concepts
- RMO/RMR primitive definitions (abstract lists only)
- Repository setup (GitLab primary, GitHub mirror)

### Documentation
- Initial README
- Vision and goals document

---

## Version Numbering

**Current status**: Pre-1.0 (Research Prototype)

- **0.x.x**: Research and development
  - Breaking changes allowed
  - Formal proofs stable
  - Implementation unstable

- **1.0.0**: Production-ready (future)
  - Extraction gap closed
  - FFI verified
  - Security audit complete
  - Breaking changes follow semver

## Upgrade Notes

### 0.4.0 → 0.5.0

**New capabilities**:
- File content operations available
- Can now read/write file contents with proven reversibility

**Breaking changes**:
- None (additive only)

**Migration**:
- No migration needed
- New features are opt-in

### 0.3.0 → 0.4.0

**New capabilities**:
- Operation sequences
- Equivalence relations
- CNO = identity element

**Breaking changes**:
- None (proof additions only)

## Future Releases

### Planned for 0.6.0
- File copy/move operations
- Symbolic link support
- Content composition theorems
- Isabelle and Mizar content operations

### Planned for 0.7.0
- RMO (obliterative deletion) proofs
- GDPR compliance primitives
- Secure overwrite guarantees

### Planned for 0.8.0
- Access control modeling
- Capability-based security
- Enhanced MAA framework

### Planned for 1.0.0
- Extraction gap closed
- Full verification stack
- Production-ready implementation
- Performance optimization
- Complete POSIX compliance

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for how to contribute to future releases.

---

**Maintained by**: See [MAINTAINERS.md](MAINTAINERS.md)
**License**: MIT + Palimpsest v0.8 (see [LICENSE.txt](LICENSE.txt))
