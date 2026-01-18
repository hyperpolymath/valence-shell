(*  Valence Shell - File Operations (Isabelle/HOL)

    Extension of filesystem model to include file operations.
    Proves reversibility of file create/delete operations.
*)

theory FileOperations
  imports FilesystemModel
begin

(* File Operations *)

definition create_file_precondition :: "path \<Rightarrow> filesystem \<Rightarrow> bool" where
  "create_file_precondition p fs = (
    \<not> path_exists p fs \<and>
    parent_exists p fs \<and>
    is_directory (parent_path p) fs \<and>
    has_write_permission (parent_path p) fs)"

definition create_file :: "path \<Rightarrow> filesystem \<Rightarrow> filesystem" where
  "create_file p fs = fs_update p (Some \<lparr> node_type = File, node_permissions = default_perms \<rparr>) fs"

definition delete_file_precondition :: "path \<Rightarrow> filesystem \<Rightarrow> bool" where
  "delete_file_precondition p fs = (
    is_file p fs \<and>
    has_write_permission (parent_path p) fs)"

definition delete_file :: "path \<Rightarrow> filesystem \<Rightarrow> filesystem" where
  "delete_file p fs = fs_update p None fs"

(* Postcondition Theorems *)

theorem create_file_creates_file:
  "create_file_precondition p fs \<Longrightarrow> is_file p (create_file p fs)"
  unfolding is_file_def create_file_def fs_update_def
  by auto

theorem create_file_path_exists:
  "create_file_precondition p fs \<Longrightarrow> path_exists p (create_file p fs)"
  unfolding path_exists_def create_file_def fs_update_def
  by auto

theorem delete_file_removes_path:
  "delete_file_precondition p fs \<Longrightarrow> \<not> path_exists p (delete_file p fs)"
  unfolding path_exists_def delete_file_def fs_update_def
  by auto

(* File Reversibility Theorem *)

theorem create_file_delete_file_reversible:
  assumes "create_file_precondition p fs"
  shows "delete_file p (create_file p fs) = fs"
proof -
  have "\<And>p'. (delete_file p (create_file p fs)) p' = fs p'"
  proof -
    fix p'
    show "(delete_file p (create_file p fs)) p' = fs p'"
    proof (cases "p = p'")
      case True
      then have "fs p' = None"
        using assms
        unfolding create_file_precondition_def path_exists_def
        by auto
      then show ?thesis
        unfolding delete_file_def create_file_def fs_update_def
        using True
        by auto
    next
      case False
      then show ?thesis
        unfolding delete_file_def create_file_def fs_update_def
        by auto
    qed
  qed
  then show ?thesis by auto
qed

(* Additional Theorems *)

theorem create_file_preserves_other_paths:
  "p \<noteq> p' \<Longrightarrow> fs p' = (create_file p fs) p'"
  unfolding create_file_def fs_update_def
  by auto

theorem create_file_preserves_directories:
  assumes "is_directory p' fs" "p \<noteq> p'"
  shows "is_directory p' (create_file p fs)"
  using assms
  unfolding is_directory_def create_file_def fs_update_def
  by auto

theorem mkdir_preserves_files:
  assumes "is_file p' fs" "p \<noteq> p'"
  shows "is_file p' (mkdir p fs)"
  using assms
  unfolding is_file_def mkdir_def fs_update_def
  by auto

(* Reverse direction reversibility - rmdir then mkdir *)
(* Note: requires original directory had default_perms for exact equality *)
theorem rmdir_mkdir_reversible:
  assumes "rmdir_precondition p fs"
      and "mkdir_precondition p (rmdir p fs)"
      and "fs p = Some \<lparr> node_type = Directory, node_permissions = default_perms \<rparr>"
  shows "mkdir p (rmdir p fs) = fs"
proof -
  have "\<And>p'. (mkdir p (rmdir p fs)) p' = fs p'"
  proof -
    fix p'
    show "(mkdir p (rmdir p fs)) p' = fs p'"
    proof (cases "p = p'")
      case True
      then show ?thesis
        unfolding mkdir_def rmdir_def fs_update_def
        using assms(3) True
        by auto
    next
      case False
      then show ?thesis
        unfolding mkdir_def rmdir_def fs_update_def
        by auto
    qed
  qed
  then show ?thesis by auto
qed

(* Reverse direction reversibility - delete then create *)
(* Note: requires original file had default_perms for exact equality *)
theorem delete_file_create_file_reversible:
  assumes "delete_file_precondition p fs"
      and "create_file_precondition p (delete_file p fs)"
      and "fs p = Some \<lparr> node_type = File, node_permissions = default_perms \<rparr>"
  shows "create_file p (delete_file p fs) = fs"
proof -
  have "\<And>p'. (create_file p (delete_file p fs)) p' = fs p'"
  proof -
    fix p'
    show "(create_file p (delete_file p fs)) p' = fs p'"
    proof (cases "p = p'")
      case True
      then show ?thesis
        unfolding create_file_def delete_file_def fs_update_def
        using assms(3) True
        by auto
    next
      case False
      then show ?thesis
        unfolding create_file_def delete_file_def fs_update_def
        by auto
    qed
  qed
  then show ?thesis by auto
qed

(* File Isolation Theorem *)

theorem file_isolation:
  assumes "p1 \<noteq> p2" "path_exists p2 fs"
  shows "path_exists p2 (create_file p1 fs) \<and> path_exists p2 (delete_file p1 fs)"
proof -
  obtain node where "fs p2 = Some node"
    using assms(2) path_exists_def by auto
  then show ?thesis
    unfolding path_exists_def create_file_def delete_file_def fs_update_def
    using assms(1)
    by auto
qed

(* Summary: File operations proven reversible in Isabelle/HOL *)

end
