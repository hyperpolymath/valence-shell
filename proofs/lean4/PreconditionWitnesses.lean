-- SPDX-License-Identifier: MPL-2.0
/- Valence Shell - precondition non-vacuity witnesses (Lean 4)

   Every reversibility theorem here has the shape `Pre p fs → op⁻¹ (op p fs) = fs`.
   If `Pre` is uninhabited the theorem is vacuously true and says nothing.
   This module exhibits one concrete state for each operation's precondition,
   so a future edit that makes a precondition empty fails the build.

   Added 2026-11-09 after `RmdirPrecondition` was found to be uninhabited
   (`isEmptyDir` quantified over ancestors instead of descendants). Audit:
   docs/audits/2026-11-09-proof-ground-truth.adoc.
-/
import FilesystemModel
import FileOperations
import SymlinkOperations
import FilesystemComposition

namespace PreconditionWitnesses

theorem mkdir_pre_inhabited : MkdirPrecondition ["a"] emptyFS :=
  ⟨by simp [pathExists, emptyFS], ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl, rfl⟩⟩

theorem rmdir_pre_inhabited : RmdirPrecondition ["a"] (mkdir ["a"] emptyFS) := by
  refine ⟨⟨defaultPerms, by simp [mkdir, fsUpdate]⟩,
          ⟨⟨defaultPerms, by simp [mkdir, fsUpdate]⟩, ?_⟩,
          ⟨⟨FSNodeType.directory, defaultPerms⟩,
            by simp [mkdir, fsUpdate, parentPath, emptyFS], rfl⟩,
          by simp [rootPath]⟩
  intro child hpre hne ⟨node, hn⟩
  match child, hpre, hne, hn with
  | [], h, _, _ => simp at h
  | [c], h, hne, _ =>
      simp [List.isPrefixOf] at h; subst h; exact hne rfl
  | _ :: _ :: _, _, _, hn =>
      simp [mkdir, fsUpdate, emptyFS] at hn

-- Negative control: a directory with a child does not satisfy the precondition.
-- Guards against a weakening of `isEmptyDir` that `rmdir_pre_inhabited` alone
-- would not catch.
theorem rmdir_pre_rejects_nonempty :
    ¬ RmdirPrecondition ["a"] (mkdir ["a", "b"] (mkdir ["a"] emptyFS)) := by
  intro h
  exact h.isEmpty.2 ["a", "b"] (by simp [List.isPrefixOf]) (by simp)
    ⟨⟨FSNodeType.directory, defaultPerms⟩, by simp [mkdir, fsUpdate]⟩

theorem createFile_pre_inhabited : CreateFilePrecondition ["a"] emptyFS :=
  ⟨by simp [pathExists, emptyFS], ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl, rfl⟩⟩

theorem deleteFile_pre_inhabited :
    DeleteFilePrecondition ["a"] (createFile ["a"] emptyFS) :=
  ⟨⟨defaultPerms, by simp [createFile, fsUpdate]⟩,
   ⟨⟨FSNodeType.directory, defaultPerms⟩,
     by simp [createFile, fsUpdate, parentPath, emptyFS], rfl⟩⟩

theorem symlink_pre_inhabited : SymlinkPrecondition ["a"] emptyFS :=
  ⟨by simp [pathExists, emptyFS], ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl, rfl⟩⟩

-- `reversible (.mkdirOp p)` needs `RmdirPrecondition` after the mkdir, so it was
-- also uninhabited before the fix. This makes the composition theorems for
-- sequences that contain mkdir non-vacuous.
theorem mkdir_reversible_inhabited : reversible (.mkdirOp ["a"]) emptyFS :=
  ⟨mkdir_pre_inhabited, rmdir_pre_inhabited, trivial⟩

end PreconditionWitnesses
