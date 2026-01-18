# Proven Library Integration Plan

This document outlines how the [proven](https://github.com/hyperpolymath/proven) library's formally verified modules integrate with Valence Shell.

**Note:** Valence Shell already has extensive formal proofs (256 theorems across 6 proof systems). The proven library provides Idris 2 implementations that complement existing proofs.

## Applicable Modules

### Core Integration (High Priority)

| Module | Use Case | Formal Guarantee |
|--------|----------|------------------|
| `SafeReversible` | Operation reversibility | `inverse . forward = id` |
| `SafeStateMachine` | Shell state transitions | Valid filesystem states |
| `SafeProvenance` | MAA audit trails | Hash-chained accountability |

### Supporting Modules

| Module | Use Case | Formal Guarantee |
|--------|----------|------------------|
| `SafeTree` | Directory tree operations | Coverage proofs |
| `SafeCapability` | Permission modeling | Least privilege |
| `SafeResource` | File handle lifecycle | Valid state transitions |

## Integration Points

### 1. Reversible Operations (SafeReversible)

Valence Shell's core guarantee maps directly to proven's `SafeReversible`:

```idris
-- vsh: rmdir(mkdir(p, fs)) = fs
-- proven: inverse . forward = id

SafeReversible.define
  forward  = mkdir path
  inverse  = rmdir path
  proof    = mkdirRmdirIdentity
```

### 2. Filesystem State Machine (SafeStateMachine)

```
:pristine → :modified → :staged → :committed
```

State transitions for operations:
- `touch`: pristine → modified
- `git add`: modified → staged
- `git commit`: staged → committed
- `undo`: * → previous (via reversibility proof)

### 3. MAA Audit Trail (SafeProvenance)

```
operation → SafeProvenance.logEntry → hash-chained audit record
```

Every shell operation creates a tamper-evident audit entry with:
- Operation type and arguments
- Before/after filesystem hash
- User identity and timestamp
- Previous entry hash (chain link)

## Proof System Correspondence

| vsh Proof System | proven Equivalent | Notes |
|------------------|-------------------|-------|
| Coq theorems | Idris 2 dependent types | Direct translation |
| Lean 4 proofs | Idris 2 proofs | Similar type theory |
| Agda proofs | Idris 2 native | Same language family |
| Isabelle/HOL | SafeThm module | Higher-order logic |
| Mizar | SafeProof terms | Set-theoretic foundation |
| Z3 (SMT) | SafeProperty module | Automated verification |

## Implementation Strategy

Since vsh already has proven reversibility in 6 systems, the integration focuses on:

1. **Runtime enforcement**: Use proven's compiled Idris to enforce proofs at runtime
2. **Audit trail**: Add SafeProvenance for MAA framework implementation
3. **Unified API**: Expose proven modules as vsh shell builtins

## Status

- [x] Theoretical alignment verified (256 theorems → proven correspondence)
- [ ] Add SafeReversible runtime bindings
- [ ] Integrate SafeProvenance for MAA audit trails
- [ ] Compile proven modules to OCaml for vsh integration
