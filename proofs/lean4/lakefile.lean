-- SPDX-License-Identifier: MPL-2.0
-- Valence Shell — Lean 4 Proof Package
--
-- Last verified working: Lean 4 v4.12.0 (2026-03-10)
-- Toolchain pinned in: lean-toolchain
-- CI workflow:          .github/workflows/lean-verification.yml
--                       .github/workflows/rust-cli.yml (lean4 job)
--
-- No external dependencies (Mathlib not required).
-- If Mathlib is added in future, pin to a specific toolchain-compatible
-- commit in lakefile.lean and update lean-toolchain accordingly.
import Lake
open Lake DSL

package «valence-shell» where
  version := v!"0.1.0"

@[default_target]
lean_lib FilesystemModel where
  srcDir := "."

lean_lib FileOperations where
  srcDir := "."

lean_lib FileContentOperations where
  srcDir := "."

lean_lib FilesystemComposition where
  srcDir := "."

lean_lib FilesystemEquivalence where
  srcDir := "."

lean_lib SymlinkOperations where
  srcDir := "."

lean_lib Extraction where
  srcDir := "."

lean_lib RMOOperations where
  srcDir := "."

lean_lib CopyMoveOperations where
  srcDir := "."

lean_lib PermissionOperations where
  srcDir := "."

lean_lib CrashConsistency where
  srcDir := "."

lean_lib PathTraversal where
  srcDir := "."

-- Executable model oracle: drives the proven model for differential testing
-- against the Rust implementation. Build: `lake build model_oracle`.
lean_exe model_oracle where
  root := `ModelOracle
  srcDir := "."
