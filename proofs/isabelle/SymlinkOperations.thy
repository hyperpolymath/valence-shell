(* SPDX-License-Identifier: PLMP-1.0-or-later *)
theory SymlinkOperations
  imports FilesystemModel
begin

text \<open>
  Valence Shell - Symlink Operations

  Abstract model of symbolic link creation and removal.
  In this model, a symlink is represented as a file node with default
  permissions; the target path is modeled externally.
\<close>

section \<open>Symlink Operations\<close>

text \<open>Preconditions for creating a symlink\<close>
definition symlink_precondition :: "path \<Rightarrow> filesystem \<Rightarrow> bool" where
  "symlink_precondition p fs = (
    \<not> path_exists p fs \<and>
    parent_exists p fs \<and>
    is_directory (parent_path p) fs \<and>
    has_write_permission (parent_path p) fs)"

text \<open>Create a symlink at path p (modeled as a file node)\<close>
definition symlink :: "path \<Rightarrow> filesystem \<Rightarrow> filesystem" where
  "symlink p fs = fs_update p (Some \<lparr> node_type = File, node_permissions = default_perms \<rparr>) fs"

text \<open>Remove a symlink at path p\<close>
definition unlink :: "path \<Rightarrow> filesystem \<Rightarrow> filesystem" where
  "unlink p fs = fs_update p None fs"

section \<open>Postcondition Lemmas\<close>

theorem symlink_creates_path:
  "symlink_precondition p fs \<Longrightarrow> path_exists p (symlink p fs)"
  unfolding path_exists_def symlink_def fs_update_def
  by auto

theorem unlink_removes_path:
  assumes "path_exists p fs"
  shows "\<not> path_exists p (unlink p fs)"
  using assms
  unfolding path_exists_def unlink_def fs_update_def
  by auto

section \<open>Reversibility Theorem\<close>

theorem symlink_unlink_reversible:
  assumes "symlink_precondition p fs"
  shows "unlink p (symlink p fs) = fs"
proof -
  have "\<And>p'. (unlink p (symlink p fs)) p' = fs p'"
  proof -
    fix p'
    show "(unlink p (symlink p fs)) p' = fs p'"
    proof (cases "p = p'")
      case True
      then have "fs p' = None"
        using assms
        unfolding symlink_precondition_def path_exists_def
        by auto
      then show ?thesis
        unfolding unlink_def symlink_def fs_update_def
        using True
        by auto
    next
      case False
      then show ?thesis
        unfolding unlink_def symlink_def fs_update_def
        by auto
    qed
  qed
  then show ?thesis by auto
qed

end
