(* SPDX-License-Identifier: AGPL-3.0-or-later *)
theory CopyMoveOperations
  imports Main FilesystemModel FileOperations
begin

text \<open>
  Valence Shell - Copy and Move Operations

  This theory formalizes copy and move (rename) operations
  with reversibility proofs for the MAA framework.

  Key Properties:
  - Copy creates an exact duplicate
  - Move is atomic rename (preserves data)
  - Both operations are reversible under preconditions
\<close>

section \<open>Copy Operation\<close>

text \<open>Precondition for file copy\<close>
definition copy_file_precondition :: "Path \<Rightarrow> Path \<Rightarrow> Filesystem \<Rightarrow> bool" where
  "copy_file_precondition src dst fs \<equiv>
    is_file src fs \<and>
    \<not> path_exists dst fs \<and>
    parent_exists dst fs \<and>
    is_directory (parent_path dst) fs \<and>
    has_read_permission src fs \<and>
    has_write_permission (parent_path dst) fs"

text \<open>Copy file operation\<close>
definition copy_file :: "Path \<Rightarrow> Path \<Rightarrow> Filesystem \<Rightarrow> Filesystem" where
  "copy_file src dst fs = (case fs src of
    Some node \<Rightarrow> fs_update dst (Some node) fs
  | None \<Rightarrow> fs)"

section \<open>Move Operation\<close>

text \<open>Check if path is prefix of another\<close>
definition is_path_prefix :: "Path \<Rightarrow> Path \<Rightarrow> bool" where
  "is_path_prefix p1 p2 \<equiv> \<exists>suffix. p2 = p1 @ suffix"

text \<open>Precondition for move/rename\<close>
definition move_precondition :: "Path \<Rightarrow> Path \<Rightarrow> Filesystem \<Rightarrow> bool" where
  "move_precondition src dst fs \<equiv>
    path_exists src fs \<and>
    \<not> path_exists dst fs \<and>
    parent_exists dst fs \<and>
    src \<noteq> dst \<and>
    \<not> (is_directory src fs \<and> is_path_prefix src dst) \<and>
    has_write_permission (parent_path src) fs \<and>
    has_write_permission (parent_path dst) fs"

text \<open>Move operation\<close>
definition move :: "Path \<Rightarrow> Path \<Rightarrow> Filesystem \<Rightarrow> Filesystem" where
  "move src dst fs = (case fs src of
    Some node \<Rightarrow>
      let fs' = fs_update dst (Some node) fs in
      fs_update src None fs'
  | None \<Rightarrow> fs)"

section \<open>Copy Operation Theorems\<close>

text \<open>Theorem: copy creates a file at destination\<close>
theorem copy_file_creates_destination:
  assumes "copy_file_precondition src dst fs"
  shows "path_exists dst (copy_file src dst fs)"
proof -
  from assms obtain perms content where src_file: "fs src = Some (FileNode perms content)"
    using copy_file_precondition_def is_file_def by auto
  show ?thesis
    unfolding path_exists_def copy_file_def
    using src_file fs_update_at_path by auto
qed

text \<open>Theorem: copy preserves source\<close>
theorem copy_file_preserves_source:
  assumes "copy_file_precondition src dst fs"
      and "src \<noteq> dst"
  shows "fs src = (copy_file src dst fs) src"
proof -
  from assms(1) obtain node where src_exists: "fs src = Some node"
    using copy_file_precondition_def is_file_def path_exists_def by auto
  show ?thesis
    unfolding copy_file_def
    using src_exists assms(2) fs_update_other_path by auto
qed

text \<open>Theorem: copy creates exact duplicate of content\<close>
theorem copy_file_same_content:
  assumes "copy_file_precondition src dst fs"
  shows "fs src = (copy_file src dst fs) dst"
proof -
  from assms obtain node where src_exists: "fs src = Some node"
    using copy_file_precondition_def is_file_def path_exists_def by auto
  show ?thesis
    unfolding copy_file_def
    using src_exists fs_update_at_path by auto
qed

text \<open>Theorem: copy is reversible by deleting destination\<close>
theorem copy_file_reversible:
  assumes "copy_file_precondition src dst fs"
  shows "delete_file dst (copy_file src dst fs) = fs"
proof -
  from assms obtain node where src_exists: "fs src = Some node"
    and dst_not_exists: "\<not> path_exists dst fs"
    using copy_file_precondition_def is_file_def path_exists_def by auto
  have fs_update_then_delete: "delete_file dst (fs_update dst (Some node) fs) = fs"
  proof -
    have "\<forall>p. (delete_file dst (fs_update dst (Some node) fs)) p = fs p"
    proof
      fix p
      show "(delete_file dst (fs_update dst (Some node) fs)) p = fs p"
      proof (cases "p = dst")
        case True
        then have "(delete_file dst (fs_update dst (Some node) fs)) p = None"
          unfolding delete_file_def fs_update_def by simp
        moreover from dst_not_exists True have "fs p = None"
          unfolding path_exists_def by auto
        ultimately show ?thesis by simp
      next
        case False
        then show ?thesis
          unfolding delete_file_def fs_update_def by simp
      qed
    qed
    then show ?thesis by auto
  qed
  show ?thesis
    unfolding copy_file_def
    using src_exists fs_update_then_delete by auto
qed

section \<open>Move Operation Theorems\<close>

text \<open>Theorem: move creates path at destination\<close>
theorem move_creates_destination:
  assumes "move_precondition src dst fs"
  shows "path_exists dst (move src dst fs)"
proof -
  from assms obtain node where src_exists: "fs src = Some node"
    using move_precondition_def path_exists_def by auto
  show ?thesis
    unfolding path_exists_def move_def
    using src_exists by (auto simp: Let_def fs_update_at_path fs_update_other_path)
qed

text \<open>Theorem: move removes source\<close>
theorem move_removes_source:
  assumes "move_precondition src dst fs"
  shows "\<not> path_exists src (move src dst fs)"
proof -
  from assms obtain node where src_exists: "fs src = Some node"
    and src_neq_dst: "src \<noteq> dst"
    using move_precondition_def path_exists_def by auto
  have "(move src dst fs) src = None"
    unfolding move_def
    using src_exists src_neq_dst
    by (auto simp: Let_def fs_update_def)
  then show ?thesis
    unfolding path_exists_def by auto
qed

text \<open>Theorem: move preserves content (node is same)\<close>
theorem move_preserves_content:
  assumes "move_precondition src dst fs"
  shows "fs src = (move src dst fs) dst"
proof -
  from assms obtain node where src_exists: "fs src = Some node"
    and src_neq_dst: "src \<noteq> dst"
    using move_precondition_def path_exists_def by auto
  show ?thesis
    unfolding move_def
    using src_exists src_neq_dst
    by (auto simp: Let_def fs_update_def)
qed

text \<open>Theorem: move is reversible\<close>
theorem move_reversible:
  assumes "move_precondition src dst fs"
  shows "move dst src (move src dst fs) = fs"
proof -
  from assms obtain node where
    src_exists: "fs src = Some node" and
    dst_not_exists: "\<not> path_exists dst fs" and
    src_neq_dst: "src \<noteq> dst"
    using move_precondition_def path_exists_def by auto

  have after_first_move: "move src dst fs = fs_update src None (fs_update dst (Some node) fs)"
    unfolding move_def using src_exists by (auto simp: Let_def)

  have dst_in_first: "(move src dst fs) dst = Some node"
    using after_first_move src_neq_dst
    by (auto simp: fs_update_def)

  have reverse_move: "move dst src (move src dst fs) =
    fs_update dst None (fs_update src (Some node) (move src dst fs))"
    unfolding move_def using dst_in_first by (auto simp: Let_def)

  show ?thesis
  proof (rule ext)
    fix p
    show "(move dst src (move src dst fs)) p = fs p"
    proof (cases "p = src")
      case True
      then show ?thesis
        using reverse_move src_neq_dst src_exists
        by (auto simp: fs_update_def)
    next
      case False
      then show ?thesis
      proof (cases "p = dst")
        case True
        then have "fs p = None"
          using dst_not_exists path_exists_def by auto
        also have "(move dst src (move src dst fs)) p = None"
          using True reverse_move by (auto simp: fs_update_def)
        ultimately show ?thesis by simp
      next
        case False
        then show ?thesis
          using \<open>p \<noteq> src\<close> reverse_move after_first_move
          by (auto simp: fs_update_def)
      qed
    qed
  qed
qed

section \<open>Preservation Theorems\<close>

text \<open>Theorem: copy preserves unrelated paths\<close>
theorem copy_preserves_other_paths:
  assumes "p \<noteq> dst"
  shows "fs p = (copy_file src dst fs) p"
  unfolding copy_file_def
  using assms by (cases "fs src") (auto simp: fs_update_def)

text \<open>Theorem: move preserves unrelated paths\<close>
theorem move_preserves_other_paths:
  assumes "p \<noteq> src" and "p \<noteq> dst"
  shows "fs p = (move src dst fs) p"
  unfolding move_def
  using assms by (cases "fs src") (auto simp: Let_def fs_update_def)

section \<open>Composition Theorems\<close>

text \<open>Theorem: copy then move destination = move source\<close>
theorem copy_then_move:
  assumes "copy_file_precondition src dst fs"
      and "move_precondition dst dst2 (copy_file src dst fs)"
  shows "(move dst dst2 (copy_file src dst fs)) dst2 = fs src"
proof -
  have step1: "(copy_file src dst fs) dst = fs src"
    using copy_file_same_content[OF assms(1)] by simp
  have step2: "(move dst dst2 (copy_file src dst fs)) dst2 = (copy_file src dst fs) dst"
    using move_preserves_content[OF assms(2)] by simp
  show ?thesis using step1 step2 by simp
qed

text \<open>
  Summary of Proven Claims:

  Copy Operations:
  \<checkmark> copy_file_creates_destination
  \<checkmark> copy_file_preserves_source
  \<checkmark> copy_file_same_content
  \<checkmark> copy_file_reversible
  \<checkmark> copy_preserves_other_paths

  Move Operations:
  \<checkmark> move_creates_destination
  \<checkmark> move_removes_source
  \<checkmark> move_preserves_content
  \<checkmark> move_reversible
  \<checkmark> move_preserves_other_paths

  Composition:
  \<checkmark> copy_then_move
\<close>

end
