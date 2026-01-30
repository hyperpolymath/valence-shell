# OCaml Extraction from Lean 4

**Status**: Design Complete, Implementation TODO
**Version**: 0.1.0
**Updated**: 2026-01-28

---

## Overview

This document describes how to extract OCaml code from Lean 4 proofs for the Valence Shell project.

**Key Insight**: Lean 4 compiles to C, not OCaml directly. We use C as an intermediate layer with OCaml FFI bindings.

```
┌──────────────────┐
│ Lean 4 Proofs    │  ← Source of truth
│ (*.lean files)   │
└────────┬─────────┘
         │ lean compile
         ↓
┌──────────────────┐
│ C Code           │  ← Lean compiler output
│ (*.c + *.h)      │
└────────┬─────────┘
         │ gcc -shared
         ↓
┌──────────────────┐
│ Shared Library   │  ← liblean_vsh.so
│ (*.so)           │
└────────┬─────────┘
         │ OCaml Ctypes FFI
         ↓
┌──────────────────┐
│ OCaml Module     │  ← ValenceLean.ml
│ (verified API)   │
└──────────────────┘
```

---

## Architecture

### Components

| Component | Location | Purpose |
|-----------|----------|---------|
| **Lean 4 Proofs** | `proofs/lean4/*.lean` | Formal specifications |
| **Extraction Definition** | `proofs/lean4/Extraction.lean` | Export interface |
| **C Wrapper** | `impl/ocaml/lean_wrapper.c` | C FFI layer |
| **OCaml Bindings** | `impl/ocaml/valence_lean.ml` | OCaml Ctypes bindings |
| **Integration** | `impl/ocaml/filesystem_ffi.ml` | Combines verified + real ops |

### Data Flow

```
User Code (OCaml)
      ↓
ValenceLean.safe_mkdir (OCaml)
      ↓
vsh_safe_mkdir (C wrapper)
      ↓
ValenceShell.Extraction.safeMkdir (Lean 4, compiled to C)
      ↓
Precondition check result
      ↓
If OK → FilesystemFFI.real_mkdir (real POSIX operation)
```

---

## Step-by-Step Setup

### 1. Install Dependencies

```bash
# Lean 4 (if not installed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# OCaml + Ctypes
opam install ctypes ctypes-foreign

# Build tools
sudo dnf install gcc make  # Fedora
# or: sudo apt install gcc make  # Ubuntu
```

### 2. Build Lean 4 Code

```bash
cd proofs/lean4
lake build Extraction
```

**Output**:
- `.lake/build/lib/Extraction.o` - Compiled object files
- `.lake/build/lib/Extraction.c` - Generated C code (if configured)
- `.lake/build/ir/Extraction.c` - Intermediate representation

### 3. Compile C Wrapper

```bash
cd impl/ocaml

# Compile wrapper + Lean generated code to shared library
gcc -shared -fPIC -o liblean_vsh.so \
    lean_wrapper.c \
    ../../proofs/lean4/.lake/build/lib/Extraction.o \
    -I$(lean --print-prefix)/include \
    -L$(lean --print-prefix)/lib/lean \
    -lleanshared \
    -Wl,-rpath,$(lean --print-prefix)/lib/lean
```

**Flags explained**:
- `-shared` - Create shared library (.so)
- `-fPIC` - Position-independent code (required for .so)
- `-I$(lean --print-prefix)/include` - Lean runtime headers
- `-L$(lean --print-prefix)/lib/lean` - Lean runtime library path
- `-lleanshared` - Link against Lean runtime
- `-Wl,-rpath,...` - Embed runtime library path in .so

### 4. Build OCaml Module

```bash
# Compile OCaml bindings
ocamlfind ocamlopt -package ctypes.foreign -c valence_lean.ml

# Link with existing code
ocamlfind ocamlopt -package ctypes.foreign -linkpkg \
    valence_lean.cmx filesystem_ffi.ml -o vsh_test
```

### 5. Test Integration

```ocaml
(* test_extraction.ml *)
let () =
  (* Create filesystem handle *)
  let fs = ValenceLean.create_fs "/tmp/vsh_test" in

  (* Test 1: Valid mkdir (should succeed precondition check) *)
  (match ValenceLean.safe_mkdir fs "/test_dir" with
   | Ok () ->
       print_endline "✓ Preconditions satisfied for mkdir";
       (* Now do real mkdir *)
       (match FilesystemFFI.real_mkdir fs "/test_dir" with
        | Ok () -> print_endline "✓ Real mkdir succeeded"
        | Error e -> Printf.printf "✗ Real mkdir failed: %s\n"
                       (Unix.error_message e))
   | Error e ->
       Printf.printf "✗ Preconditions failed: %s\n" (Unix.error_message e));

  (* Test 2: Duplicate mkdir (should fail precondition check) *)
  (match ValenceLean.safe_mkdir fs "/test_dir" with
   | Ok () -> print_endline "✗ Should have failed (EEXIST)"
   | Error Unix.EEXIST -> print_endline "✓ Correctly rejected duplicate mkdir"
   | Error e -> Printf.printf "✗ Wrong error: %s\n" (Unix.error_message e));

  (* Clean up *)
  ValenceLean.destroy_fs fs
```

Run:
```bash
ocamlfind ocamlopt -package ctypes.foreign -linkpkg \
    valence_lean.cmx filesystem_ffi.ml test_extraction.ml -o test
./test
```

---

## Current Status

### ✅ Complete

- [x] Lean 4 extraction interface (`Extraction.lean`)
- [x] C wrapper skeleton (`lean_wrapper.c`)
- [x] OCaml Ctypes bindings (`valence_lean.ml`)
- [x] Integration documentation (this file)

### ⚠️ TODO

- [ ] Complete Lean object marshaling in `lean_wrapper.c`
- [ ] Test Lean → C → OCaml pipeline
- [ ] Add Dune build configuration
- [ ] Integrate with existing `filesystem_ffi.ml`
- [ ] Add property-based tests (verify Lean guarantees hold)
- [ ] Benchmarking (overhead of FFI calls)

---

## Implementation Notes

### Lean Object Marshaling

Lean 4 uses reference-counted objects. Key APIs:

```c
#include <lean/lean.h>

// String operations
lean_object* lean_mk_string(const char* s);
const char* lean_string_cstr(lean_object* s);

// Reference counting
void lean_inc_ref(lean_object* o);
void lean_dec_ref(lean_object* o);

// Structure access
lean_object* lean_ctor_get(lean_object* o, size_t i);  // Get field i
uint8_t lean_unbox(lean_object* o);  // Unbox Bool/Nat
```

### Filesystem State Management

The Lean `Filesystem` type is an abstract function `Path → Option FSNode`. For real operations, we need to:

1. **Track state in Lean object**: Update Lean filesystem value after each operation
2. **Sync with real filesystem**: Ensure Lean state matches disk state
3. **Handle divergence**: Deal with external modifications to filesystem

**Design Decision**: Use Lean only for precondition checking, not state tracking.

```ocaml
(* Stateless approach - recommended *)
let verified_mkdir path =
  (* 1. Build abstract FS from current disk state *)
  let abstract_fs = build_abstract_fs () in
  (* 2. Check preconditions with Lean *)
  match ValenceLean.safe_mkdir abstract_fs path with
  | Ok () ->
      (* 3. Do real operation *)
      Unix.mkdir path 0o755
  | Error e -> Error e
```

### Performance Considerations

**FFI Overhead**:
- OCaml → C: ~10-50ns per call
- C → Lean: Negligible (already compiled)
- String marshaling: ~100ns per path

**Optimization**: Cache precondition check results when paths haven't changed.

---

## Alternative Approaches

### 1. Pure Lean Extraction (if available)

Lean 4 can potentially extract to other targets via plugins:

```bash
# Hypothetical Lean → OCaml plugin
lake build --target ocaml
```

**Status**: No official OCaml backend exists (as of 2026-01).

### 2. Coq Extraction

Use Coq proofs instead (`proofs/coq/extraction.v` already configured):

```bash
cd proofs/coq
coqc extraction.v  # Generates filesystem.ml
```

**Advantage**: Direct OCaml output
**Disadvantage**: Lean 4 is our primary specification language

### 3. Manual Translation

Manually translate Lean code to OCaml:

**Advantage**: Full control, no FFI overhead
**Disadvantage**: No formal guarantee of correctness

---

## Integration with Rust CLI

The Rust CLI (`impl/rust-cli/`) is the primary implementation. OCaml extraction serves as:

1. **Reference implementation**: Directly from proofs
2. **Cross-validation**: Compare Rust vs OCaml behavior
3. **Audit tool**: Verify Rust CLI matches specification

**Workflow**:
```
Lean 4 Spec
    ├→ Rust CLI (production)
    └→ OCaml Extract (reference/audit)
```

---

## Testing Strategy

### Unit Tests

Test C wrapper functions:
```c
// test_wrapper.c
void test_safe_mkdir() {
    vsh_filesystem_t* fs = vsh_filesystem_create("/tmp/test");
    vsh_result_t r = vsh_safe_mkdir(fs, "/new_dir");
    assert(r.success == 1);
    vsh_filesystem_destroy(fs);
}
```

### Integration Tests

Test OCaml bindings:
```ocaml
(* test_bindings.ml *)
let test_safe_mkdir () =
  let fs = ValenceLean.create_fs "/tmp/test" in
  let result = ValenceLean.safe_mkdir fs "/new_dir" in
  match result with
  | Ok () -> true
  | Error _ -> false
```

### Property Tests

Verify Lean theorems hold in OCaml:
```ocaml
(* test_properties.ml *)
(* Property: mkdir followed by rmdir is identity *)
let test_mkdir_rmdir_reversible path =
  let fs = build_fs () in
  let () = verified_mkdir fs path in
  let () = verified_rmdir fs path in
  filesystem_equal fs (build_fs ())  (* Should be unchanged *)
```

---

## References

- [Lean 4 FFI Guide](https://lean-lang.org/lean4/doc/dev/ffi.html)
- [Lean Runtime API]($(lean --print-prefix)/include/lean/lean.h)
- [OCaml Ctypes Tutorial](https://github.com/ocamllabs/ocaml-ctypes)
- [seL4 Verification](https://sel4.systems/) - Similar approach (Isabelle → C)
- [CompCert](https://compcert.org/) - Verified compiler (Coq → C)

---

## Contact

For questions about OCaml extraction:
- Check: `proofs/lean4/Extraction.lean` (inline documentation)
- Check: `impl/ocaml/lean_wrapper.c` (implementation notes)
- Repo: https://github.com/hyperpolymath/valence-shell
