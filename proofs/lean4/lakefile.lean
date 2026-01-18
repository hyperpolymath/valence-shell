-- SPDX-License-Identifier: AGPL-3.0-or-later
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
