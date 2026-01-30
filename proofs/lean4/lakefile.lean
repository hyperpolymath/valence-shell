-- SPDX-License-Identifier: PLMP-1.0-or-later
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
