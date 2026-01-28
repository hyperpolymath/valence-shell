# Valence Shell Architecture

**Version**: 0.6.0
**Updated**: 2026-01-28
**Status**: Research Prototype → Production Path Defined

---

## Overview

Valence shell uses a **hybrid architecture** combining:
1. **Rust CLI** - Fast path for simple operations
2. **BEAM Daemon** - Complex operations with fault tolerance
3. **Lean 4 Proofs** - Formal verification foundation
4. **Echidna** - Build-time property validation

---

## Architecture Decision

**Chosen**: Hybrid Rust + Streamlined BEAM
**Rationale**: Best of both worlds
- Rust fast path → 5ms startup (competitive with bash)
- BEAM daemon → Fault tolerance, Ecto, self-healing
- Lean 4 → Single source of truth for correctness
- Echidna → Validates both implementations

**Rejected Alternatives**:
- ❌ Pure Rust - Loses BEAM fault tolerance features
- ❌ Pure BEAM - Slow startup (160ms vs 5ms)
- ❌ Coq → OCaml extraction - Complex, fragile toolchain
- ❌ Ephapax/AffineScript → WASM - Sandboxed, can't do raw POSIX

---

## Component Breakdown

### 1. Rust CLI (Fast Path)

**Location**: `impl/rust-cli/`
**Status**: ✅ Working (28/28 tests passing)
**Language**: Rust 1.75+

**Handles**:
- Simple filesystem operations: `mkdir`, `rmdir`, `touch`, `rm`
- Read operations: `cat`, `ls`, `pwd`
- Direct POSIX syscalls (no overhead)
- Local operation history
- Connects to daemon for complex ops

**Why Rust**:
- 5ms cold start (bash-competitive)
- Direct syscall access (no FFI overhead)
- Memory safe (ownership system)
- ~2MB binary size
- No garbage collection

**Verification**:
- Manual correspondence to Lean 4 theorems
- Integration tests validate behavior
- Echidna property tests on builds

---

### 2. BEAM Daemon (Complex Path)

**Location**: `impl/elixir/`
**Status**: ⚠️ In progress (NIF build issues, core logic works)
**Language**: Elixir 1.17+ on Erlang/OTP 27

**Handles**:
- Undo/redo with operation history
- Transaction grouping (begin/commit/rollback)
- MAA framework (audit logging)
- RMO operations (secure deletion)
- Complex compositions
- Distributed coordination (future)

**Why BEAM**:
- **Super concurrency** - Millions of lightweight processes
- **Secure process isolation** - Processes cannot corrupt each other's memory
- OTP supervision trees (battle-tested fault tolerance)
- "Let it crash" philosophy (proven self-healing)
- Ecto (first-class database ORM)
- Hot code reload (update without restart)
- Distributed Erlang (future clustering)

**Streamlining**:
- Strip unused OTP apps (like Chainguard does with images)
- Minimal runtime: GenServer, Supervisor, Ecto core
- Target: ~15MB footprint (vs default ~50MB)

**Communication**:
- Unix socket: `/tmp/vsh-daemon.sock`
- Protocol: JSON-RPC 2.0
- Fallback: Simple ops work even if daemon is down

---

### 3. Lean 4 Proofs (Source of Truth)

**Location**: `proofs/lean4/`
**Status**: ✅ Complete (256+ theorems)
**Systems**: Lean 4, Coq, Agda, Isabelle/HOL, Mizar, Z3

**Proven Properties**:
- `mkdir_rmdir_reversible`: Directory creation is reversible
- `create_delete_file_reversible`: File operations reverse correctly
- `operation_independence`: Different paths don't interfere
- `operation_sequence_reversible`: Composition correctness
- `cno_identity_element`: CNO (Certified Null Operation) theory

**Why Lean 4 (not Coq)**:
- More active development
- Better tooling
- Cleaner syntax
- Growing community
- Rust FFI research ongoing

**Cross-validation**:
- Same theorems proven in 6 different systems
- Different logical foundations increase confidence
- Industry precedent: seL4, CompCert

---

### 4. Echidna (Build Validation)

**Location**: TBD (integration planned)
**Status**: Not yet integrated
**Purpose**: Property-based testing of builds

**What Echidna Does**:
- Validates builds against properties derived from Lean 4
- Catches regressions in CI/CD
- Generates test cases automatically
- Ensures implementations match specifications

**Integration Points**:
- Rust CLI: Test operations match Lean 4 semantics
- BEAM daemon: Test complex operations preserve invariants
- Both: Test precondition enforcement

---

## Data Flow

### Simple Operation (Fast Path)

```
User: vsh> mkdir foo
    ↓
Rust CLI:
  1. Parse command
  2. Check preconditions (parent exists, path doesn't exist)
  3. Call mkdir() syscall directly
  4. Record in local history
  5. Return immediately (~5ms total)
```

### Complex Operation (BEAM Path)

```
User: vsh> undo
    ↓
Rust CLI:
  1. Parse command
  2. Connect to Unix socket (/tmp/vsh-daemon.sock)
  3. Send JSON-RPC request
    ↓
BEAM Daemon:
  4. Query Ecto (audit log database)
  5. Find last operation
  6. Calculate inverse operation
  7. Execute inverse (with supervision)
  8. Update audit log
  9. Return success
    ↓
Rust CLI:
  10. Display result to user
```

---

## Trust Boundaries

### High Trust (Mathematically Proven)
- Lean 4 theorems (formal proofs)
- Cross-validated in 6 proof systems
- ~256 theorems covering core operations

### Medium Trust (Verified by Testing)
- Rust CLI implementation
  - Correspondence to Lean 4 (manual proofs)
  - Integration tests (automated)
  - Echidna property tests (planned)
- BEAM daemon
  - Correspondence to Lean 4 (manual proofs)
  - Supervision ensures crash recovery
  - Ecto ensures data consistency

### Low Trust (OS/Kernel)
- POSIX syscalls (kernel guarantees only)
- Filesystem consistency (ext4/btrfs/etc)
- Hardware correctness (not verified)

---

## Verification Strategy

### Phase 4a: Rust CLI Verification

1. **Document correspondence**
   - Map each Rust function to Lean 4 theorem
   - Example: `commands::mkdir()` → `mkdir_rmdir_reversible`

2. **Manual proofs**
   - Prove Rust implementation matches specification
   - Focus on preconditions and error handling

3. **Echidna integration**
   - Property: `rmdir(mkdir(p)) == identity` (if valid)
   - Property: `mkdir(existing_path) == EEXIST`
   - Generate test cases automatically

4. **Integration tests**
   - Run full test suite (28/28 currently passing)
   - Add property-based tests

### Phase 4b: BEAM Daemon Verification

1. **Ecto schema correctness**
   - Audit log structure matches Lean 4 model
   - Database constraints enforce invariants

2. **Operation logic**
   - Undo/redo algorithms match specifications
   - Transaction semantics proven correct

3. **Supervision correctness**
   - Crash recovery preserves invariants
   - No orphaned resources

---

## Performance Targets

| Operation | Target | Current | Status |
|-----------|--------|---------|--------|
| Cold start | 5ms | ~8ms | 🟡 Close |
| mkdir | <1ms | ~0.5ms | ✅ Excellent |
| Simple cmd | <2ms | ~1ms | ✅ Excellent |
| Undo | <50ms | ~30ms | ✅ Good |
| Complex op | <100ms | Varies | 🔄 WIP |

---

## Deployment Model

### Development
```
Terminal → Rust CLI → BEAM daemon (mix run)
                   └→ SQLite audit.db
```

### Production
```
Terminal → Rust CLI (/usr/local/bin/vsh)
                   → BEAM daemon (systemd service)
                   → PostgreSQL audit log
```

**Systemd Unit** (`vsh-daemon.service`):
```ini
[Unit]
Description=Valence Shell Daemon
After=network.target

[Service]
Type=simple
ExecStart=/usr/local/lib/vsh/daemon
Restart=always
RestartSec=5s

[Install]
WantedBy=multi-user.target
```

---

## Scaling Strategy

### Single User (Current)
- Rust CLI per shell session
- One BEAM daemon per user
- Unix socket communication
- SQLite for audit logs

### Multi-User (Future)
- Rust CLI per shell session
- One BEAM daemon cluster per system
- TCP/Unix socket communication
- PostgreSQL for centralized audit
- Distributed Erlang for coordination

---

## Security Boundaries

### Sandboxing (Future Enhancement)
- Rust CLI runs in user's security context
- BEAM daemon could run as separate user
- Unix socket permissions restrict access
- Audit logs require elevated privileges (read-only to user)

### MAA Framework
- All operations logged immutably
- Audit log is append-only
- Cryptographic hashing (future)
- Distributed consensus (future)

---

## Extension Points

### 1. New Operations
- Add to Rust CLI if simple (e.g., `chmod`)
- Add to BEAM daemon if complex (e.g., `obliterate`)
- Prove in Lean 4 first
- Test with Echidna

### 2. New Proof Systems
- Already support 6 systems
- Can add more (PVS, HOL Light, ACL2)
- Cross-validation increases confidence

### 3. New Backends
- Current: Native (Rust + BEAM)
- Future: Could add WASM compilation (for sandboxed execution)
- Ephapax/AffineScript could target WASM subset

---

## Related Documentation

- `STATE.scm` - Current project state
- `ECOSYSTEM.scm` - Ecosystem relationships
- `docs/POSIX_COMPLIANCE.md` - Incremental roadmap to full POSIX shell
- `proofs/README.md` - Proof system documentation
- `README.adoc` - Project overview

---

## Open Questions

1. **Echidna integration timeline** - When to prioritize?
2. **BEAM streamlining** - Which OTP apps to strip?
3. **Systemd vs Docker** - Which deployment model first?
4. **Multi-user coordination** - When to implement distributed mode?

---

**Last Updated**: 2026-01-28
**Author**: Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
**License**: PMPL-1.0-or-later
