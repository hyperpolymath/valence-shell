(*  Valence Shell - Filesystem Model (Isabelle/HOL)

    A formal model of POSIX-like filesystem operations for proving
    MAA (Mutually Assured Accountability) properties.

    This model focuses on directory operations (mkdir/rmdir) with
    the goal of proving reversibility and correctness properties.
*)

theory FilesystemModel
  imports Main "HOL-Library.Sublist"
begin

(* Path Model *)
type_synonym path_component = string
type_synonym path = "path_component list"

definition root_path :: path where
  "root_path = []"

definition parent_path :: "path \<Rightarrow> path" where
  "parent_path p = (case rev p of
                      [] \<Rightarrow> []
                    | (x # xs) \<Rightarrow> rev xs)"

definition path_name :: "path \<Rightarrow> path_component option" where
  "path_name p = (case rev p of
                    [] \<Rightarrow> None
                  | (name # _) \<Rightarrow> Some name)"

(* Filesystem Nodes *)
datatype fs_node_type = File | Directory

record permissions =
  readable :: bool
  writable :: bool
  executable :: bool

definition default_perms :: permissions where
  "default_perms = \<lparr> readable = True, writable = True, executable = True \<rparr>"

record fs_node =
  node_type :: fs_node_type
  node_permissions :: permissions

(* Filesystem State *)
type_synonym filesystem = "path \<Rightarrow> fs_node option"

definition empty_fs :: filesystem where
  "empty_fs p = (case p of
                   [] \<Rightarrow> Some \<lparr> node_type = Directory, node_permissions = default_perms \<rparr>
                 | _ \<Rightarrow> None)"

(* Filesystem Predicates *)
definition path_exists :: "path \<Rightarrow> filesystem \<Rightarrow> bool" where
  "path_exists p fs = (\<exists>node. fs p = Some node)"

definition is_directory :: "path \<Rightarrow> filesystem \<Rightarrow> bool" where
  "is_directory p fs = (\<exists>perms. fs p = Some \<lparr> node_type = Directory, node_permissions = perms \<rparr>)"

definition is_file :: "path \<Rightarrow> filesystem \<Rightarrow> bool" where
  "is_file p fs = (\<exists>perms. fs p = Some \<lparr> node_type = File, node_permissions = perms \<rparr>)"

definition parent_exists :: "path \<Rightarrow> filesystem \<Rightarrow> bool" where
  "parent_exists p fs = path_exists (parent_path p) fs"

definition has_write_permission :: "path \<Rightarrow> filesystem \<Rightarrow> bool" where
  "has_write_permission p fs = (\<exists>node. fs p = Some node \<and> writable (node_permissions node))"

definition is_empty_dir :: "path \<Rightarrow> filesystem \<Rightarrow> bool" where
  "is_empty_dir p fs = (is_directory p fs \<and>
    (\<forall>child. prefix p child \<and> child \<noteq> p \<longrightarrow> \<not> path_exists child fs))"

(* Basic Lemmas *)
lemma path_exists_empty_fs_root:
  "path_exists root_path empty_fs"
  unfolding path_exists_def empty_fs_def root_path_def
  by auto

lemma not_path_exists_empty_fs:
  "p \<noteq> root_path \<Longrightarrow> \<not> path_exists p empty_fs"
  unfolding path_exists_def empty_fs_def root_path_def
  by (cases p; auto)

(* Filesystem Operations *)
definition fs_update :: "path \<Rightarrow> fs_node option \<Rightarrow> filesystem \<Rightarrow> filesystem" where
  "fs_update p n fs = (\<lambda>p'. if p = p' then n else fs p')"

(* mkdir: Create a directory *)
definition mkdir_precondition :: "path \<Rightarrow> filesystem \<Rightarrow> bool" where
  "mkdir_precondition p fs = (
    \<not> path_exists p fs \<and>
    parent_exists p fs \<and>
    is_directory (parent_path p) fs \<and>
    has_write_permission (parent_path p) fs)"

definition mkdir :: "path \<Rightarrow> filesystem \<Rightarrow> filesystem" where
  "mkdir p fs = fs_update p (Some \<lparr> node_type = Directory, node_permissions = default_perms \<rparr>) fs"

(* rmdir: Remove a directory *)
definition rmdir_precondition :: "path \<Rightarrow> filesystem \<Rightarrow> bool" where
  "rmdir_precondition p fs = (
    is_directory p fs \<and>
    is_empty_dir p fs \<and>
    has_write_permission (parent_path p) fs \<and>
    p \<noteq> root_path)"

definition rmdir :: "path \<Rightarrow> filesystem \<Rightarrow> filesystem" where
  "rmdir p fs = fs_update p None fs"

(* Postcondition Theorems *)
theorem mkdir_creates_directory:
  "mkdir_precondition p fs \<Longrightarrow> is_directory p (mkdir p fs)"
  unfolding is_directory_def mkdir_def fs_update_def
  by auto

theorem mkdir_path_exists:
  "mkdir_precondition p fs \<Longrightarrow> path_exists p (mkdir p fs)"
  unfolding path_exists_def mkdir_def fs_update_def
  by auto

theorem rmdir_removes_path:
  "rmdir_precondition p fs \<Longrightarrow> \<not> path_exists p (rmdir p fs)"
  unfolding path_exists_def rmdir_def fs_update_def
  by auto

(* The Main Reversibility Theorem *)
theorem mkdir_rmdir_reversible:
  assumes "mkdir_precondition p fs"
  shows "rmdir p (mkdir p fs) = fs"
proof -
  have "\<And>p'. (rmdir p (mkdir p fs)) p' = fs p'"
  proof -
    fix p'
    show "(rmdir p (mkdir p fs)) p' = fs p'"
    proof (cases "p = p'")
      case True
      then have "fs p' = None"
        using assms
        unfolding mkdir_precondition_def path_exists_def
        by auto
      then show ?thesis
        unfolding rmdir_def mkdir_def fs_update_def
        using True
        by auto
    next
      case False
      then show ?thesis
        unfolding rmdir_def mkdir_def fs_update_def
        by auto
    qed
  qed
  then show ?thesis by auto
qed

(* Additional Theorems *)
theorem mkdir_preserves_other_paths:
  "p \<noteq> p' \<Longrightarrow> fs p' = (mkdir p fs) p'"
  unfolding mkdir_def fs_update_def
  by auto

theorem rmdir_preserves_other_paths:
  "p \<noteq> p' \<Longrightarrow> fs p' = (rmdir p fs) p'"
  unfolding rmdir_def fs_update_def
  by auto

theorem mkdir_parent_still_exists:
  assumes "mkdir_precondition p fs"
  shows "path_exists (parent_path p) (mkdir p fs)"
proof -
  obtain node where "fs (parent_path p) = Some node"
    using assms
    unfolding mkdir_precondition_def parent_exists_def path_exists_def
    by auto
  then show ?thesis
    unfolding path_exists_def mkdir_def fs_update_def
    by (cases "p = parent_path p"; auto)
qed

end
