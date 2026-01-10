# Valence Shell - Zig Fast Path

Fast startup CLI for the Valence Shell, targeting ~5ms cold start.

## Building

```bash
# Requires Zig 0.13.0 (stable)
asdf install zig 0.13.0
asdf set zig 0.13.0

# Build
zig build

# Test
zig build test
```

## Usage

```bash
# Fast path commands (handled directly, ~5ms startup)
./zig-out/bin/vsh mkdir mydir
./zig-out/bin/vsh touch myfile.txt
./zig-out/bin/vsh cat myfile.txt
./zig-out/bin/vsh ls
./zig-out/bin/vsh rm myfile.txt
./zig-out/bin/vsh rmdir mydir
./zig-out/bin/vsh pwd

# Daemon commands (require BEAM daemon running)
./zig-out/bin/vsh cp source dest      # Copy with undo tracking
./zig-out/bin/vsh mv source dest      # Move with undo tracking
./zig-out/bin/vsh undo                # Undo last operation
./zig-out/bin/vsh redo                # Redo last undone operation
./zig-out/bin/vsh history             # Show operation history
./zig-out/bin/vsh obliterate file     # Secure delete (IRREVERSIBLE!)
```

## Architecture

```
┌─────────────────────────────────┐
│ Formal Proofs (HIGH TRUST)      │ ← Coq/Lean4/Agda/Isabelle/Mizar/Z3
└─────────────┬───────────────────┘
              │
┌─────────────▼───────────────────┐
│ THIS ZIG LAYER (MEDIUM TRUST)   │ ← Runtime checks, fast path
│ Simple ops: mkdir, touch, rm    │
└─────────────┬───────────────────┘
              │ Unix socket (complex ops)
┌─────────────▼───────────────────┐
│ BEAM Daemon (MEDIUM TRUST)      │ ← Verified Elixir, undo/redo
└─────────────┬───────────────────┘
              │ POSIX syscalls
┌─────────────▼───────────────────┐
│ Operating System (OS TRUST)     │ ← Kernel guarantees
└─────────────────────────────────┘
```

## Starting the BEAM Daemon

The daemon provides undo/redo, history, and transaction support.

```bash
cd ../elixir
mix deps.get
mix vsh.daemon start
```

## Proof References

Each operation is backed by formal proofs:

| Operation | Theorem | Proof Systems |
|-----------|---------|---------------|
| mkdir/rmdir | mkdir_rmdir_reversible | Coq, Lean 4, Agda, Isabelle, Mizar, Z3 |
| touch/rm | create_delete_file_reversible | Coq, Lean 4, Agda, Isabelle, Mizar, Z3 |
| obliterate | obliterate_irreversible | Coq, Lean 4, Agda, Isabelle, Mizar, Z3 |

## License

AGPL-3.0-or-later
