# Security Policy

## Supported Versions

Valence Shell is currently in **research prototype** status (version 0.5.0). Security updates are provided on a best-effort basis for the current development version.

| Version | Supported          | Status |
| ------- | ------------------ | ------ |
| 0.5.x   | :white_check_mark: | Current development branch |
| < 0.5.0 | :x:                | Historical/superseded |

**Note**: This is research software with formal proofs but unverified implementation. See [Production Readiness](#production-readiness) below.

## Security Model

### Formal Verification Status

Valence Shell uses **polyglot verification** across 6 proof systems:

✅ **Formally Proven** (Mathematical Guarantees):
- Directory operations (mkdir/rmdir) reversibility
- File operations (create/delete) reversibility
- File content operations (read/write) reversibility
- Operation independence
- Composition correctness
- ~256 theorems across Coq, Lean 4, Agda, Isabelle/HOL, Mizar, Z3

⚠️ **Not Verified** (Manual Review Required):
- OCaml FFI layer (filesystem_ffi.ml)
- Elixir reference implementation
- POSIX syscall interface
- Extraction correctness (Coq → OCaml)

### Trust Boundaries

```
┌─────────────────────────────────────┐
│ Formal Proofs (HIGH TRUST)          │
│ - Coq/Lean/Agda/Isabelle/Mizar      │
│ - Mathematical guarantees            │
└─────────────┬───────────────────────┘
              │ Extraction (GAP)
┌─────────────▼───────────────────────┐
│ OCaml Implementation (MEDIUM TRUST)  │
│ - Type safe, memory safe             │
│ - Manual verification needed         │
└─────────────┬───────────────────────┘
              │ FFI (GAP)
┌─────────────▼───────────────────────┐
│ POSIX Syscalls (LOW TRUST)          │
│ - Kernel guarantees only             │
│ - File system dependent              │
└──────────────────────────────────────┘
```

## Reporting a Vulnerability

### For Research/Prototype Issues

For issues in this early-stage research prototype:

1. **Open a public issue** on GitHub: https://github.com/Hyperpolymath/valence-shell/issues
   - Tag with `security` label
   - This is a research project; responsible disclosure follows academic norms

2. **For GitLab**: https://gitlab.com/non-initiate/rhodinised/vsh/-/issues
   - Main development repository

### For Critical Security Issues

If you discover a **critical** security vulnerability that could affect users:

1. **Email**: [Contact info to be added - check repository]
2. **PGP Key**: [To be added]
3. **Expected Response Time**: 7 days (research project, best-effort)

**What qualifies as critical:**
- Arbitrary code execution
- Privilege escalation
- Data loss beyond documented limitations
- Security proof invalidation

### What to Include

A good security report includes:

1. **Description**: Clear explanation of the vulnerability
2. **Impact**: What an attacker could achieve
3. **Reproduction**: Step-by-step instructions to reproduce
4. **Proof Level**: Which layer is affected:
   - Formal proofs (breaks mathematical guarantee)
   - Implementation (FFI, syscall)
   - Documentation (incorrect claim)
5. **Suggested Fix**: If you have one

## Security Features

### Current (v0.5.0)

✅ **Proven Reversibility**
- Directory creation/deletion
- File creation/deletion
- File content modifications
- Mathematical guarantee of undo capability

✅ **Proven Independence**
- Operations on different paths don't interfere
- Concurrent operation safety (at proof level)

✅ **MAA Framework Foundation**
- Audit trail for modifications
- Reversible operations with proof
- FileModificationRecord tracking

✅ **Type Safety**
- Coq/Lean 4/Agda: Dependent types
- Isabelle/HOL: Higher-order logic
- OCaml: Strong static typing
- Elixir: Pattern matching, guards

### Planned

🔄 **RMO (Remove-Match-Obliterate)**
- GDPR "right to be forgotten" compliance
- Cryptographic erasure guarantees
- Secure overwrite proof

🔄 **Access Control**
- POSIX permissions modeling
- Capability-based security
- Principle of least privilege

🔄 **Sandboxing**
- Path restriction proofs
- Chroot-like containment
- Resource limits

## Production Readiness

**⚠️ NOT PRODUCTION READY ⚠️**

Current status: **Research Prototype**

**Do NOT use for:**
- Production systems
- Critical data
- Security-sensitive applications
- Unverified/untrusted environments

**Verification Gap:**
The formal proofs operate on abstract models. The implementation (OCaml FFI + POSIX) is **not formally connected** to the proofs. This gap means:
- Proofs guarantee model correctness
- Implementation may have bugs
- Extraction may introduce errors

**To reach production:**
1. Close extraction gap (Coq → OCaml verification)
2. Verify FFI layer
3. Complete security audit
4. Fuzzing campaign
5. Formal verification of full stack

## Security Boundaries

### What IS Guaranteed (by proofs)

✅ If preconditions hold, `rmdir(mkdir(p, fs)) = fs`
✅ If preconditions hold, `write(p, old, write(p, new, fs)) = fs`
✅ Operations on p1 don't affect p2 (p1 ≠ p2)
✅ Composition: sequences of operations reverse correctly

### What Is NOT Guaranteed

❌ Implementation matches proofs (manual review required)
❌ POSIX compliance beyond modeled operations
❌ Performance (not optimized)
❌ Concurrent access from multiple processes
❌ File system integrity after crashes
❌ Protection against malicious inputs to unverified code

## Cryptographic Disclosure

**Current version uses NO cryptography.**

Future versions may include:
- Cryptographic erasure (RMO)
- Digital signatures (audit trail)
- Encryption (data at rest)

When cryptography is added, we will:
- Document algorithms and parameters
- Provide formal security proofs where possible
- Follow NIST/IETF standards
- Disclose any custom primitives

## Dependency Security

### Current Dependencies (Minimal)

**Proof Systems** (development only):
- Coq 8.18+
- Lean 4.3+
- Agda 2.6.4+
- Isabelle/HOL 2024
- Mizar (optional)
- Z3 4.12+

**Runtime** (OCaml implementation):
- OCaml 5.0+ (compiler + stdlib only)
- Zero external runtime dependencies ✅

**Build Tools**:
- Just (command runner)
- Nix (reproducible builds, optional)

### Supply Chain Security

- **No npm/pip/cargo dependencies** in runtime
- **Reproducible builds** via Nix flake
- **Offline-first**: proofs verifiable air-gapped
- **Source verification**: Git commit signatures (planned)

## Responsible Disclosure Timeline

1. **Day 0**: Vulnerability reported
2. **Day 7**: Initial response from maintainers
3. **Day 30**: Assessment complete, severity assigned
4. **Day 90**: Fix developed and tested (if applicable)
5. **Day 90+**: Public disclosure

For critical issues, we may request coordinated disclosure with:
- OCaml team (if compiler issue)
- Coq/Lean/Agda teams (if proof assistant issue)
- Linux kernel (if syscall issue)

## Security Hall of Fame

Contributors who responsibly disclose security issues will be acknowledged here (with permission).

[None yet]

## Security Resources

- **Proof Documentation**: `proofs/README.md`
- **Verification Gap Analysis**: `docs/PROGRESS_REPORT.md`
- **Architecture**: `docs/ARCHITECTURE.adoc`
- **Test Suite**: `scripts/demo_verified_operations.sh`
- **Academic Papers**: `docs/academic-papers.md` (planned)

## Compliance & Standards

### Current

- ✅ **RSR Framework**: Bronze level (this security policy = part of compliance)
- ✅ **Offline-First**: No network dependencies
- ✅ **Type Safety**: All 6 proof systems provide strong typing
- ✅ **Memory Safety**: Rust-equivalent via OCaml (no manual memory management)

### Planned

- 🔄 **GDPR**: RMO (Remove-Match-Obliterate) for right to erasure
- 🔄 **Common Criteria**: EAL4 equivalent (formal methods)
- 🔄 **ISO 27001**: Information security management
- 🔄 **NIST Cybersecurity Framework**: When production-ready

## Contact

- **GitHub Issues**: https://github.com/Hyperpolymath/valence-shell/issues
- **GitLab Issues**: https://gitlab.com/non-initiate/rhodinised/vsh/-/issues
- **Email**: [To be added]
- **Security.txt**: See `.well-known/security.txt` (RFC 9116)

## Acknowledgments

This security policy is inspired by:
- **Rustls Security Policy**: Clarity on proof vs implementation
- **seL4 Kernel**: Formal verification security model
- **CompCert Compiler**: Verified compilation security claims

---

**Last Updated**: 2025-11-22
**Version**: 0.5.0
**Policy Version**: 1.0
