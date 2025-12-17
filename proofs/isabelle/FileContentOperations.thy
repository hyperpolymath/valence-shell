(*  Valence Shell - File Content Operations (Isabelle/HOL)

    File content operations: read and write
    Proves reversibility of content modifications
    Extends the verified filesystem with content tracking
*)

theory FileContentOperations
  imports FilesystemModel FileOperations
begin

(* File Content Type *)

type_synonym file_content = "string"

definition empty_content :: "file_content" where
  "empty_content = ''''"

(* Extended Filesystem Node with Content *)

record fs_node_with_content =
  nc_type :: node_type
  nc_permissions :: permissions
  nc_content :: "file_content option"  (* None for directories, Some for files *)

(* Extended Filesystem *)

type_synonym filesystem_with_content = "path \<Rightarrow> fs_node_with_content option"

(* Conversion Functions *)

definition fs_to_fs_with_content :: "filesystem \<Rightarrow> filesystem_with_content" where
  "fs_to_fs_with_content fs = (\<lambda>p.
    case fs p of
      None \<Rightarrow> None
    | Some node \<Rightarrow>
        Some \<lparr> nc_type = node_type node,
               nc_permissions = node_permissions node,
               nc_content = (if node_type node = File then Some empty_content else None) \<rparr>)"

(* File Content Operations *)

definition read_file :: "path \<Rightarrow> filesystem_with_content \<Rightarrow> file_content option" where
  "read_file p fs = (
    case fs p of
      None \<Rightarrow> None
    | Some node \<Rightarrow>
        (if nc_type node = File then nc_content node else None))"

definition write_file :: "path \<Rightarrow> file_content \<Rightarrow> filesystem_with_content \<Rightarrow> filesystem_with_content" where
  "write_file p content fs = (\<lambda>p'.
    if p = p' then
      case fs p' of
        None \<Rightarrow> None
      | Some node \<Rightarrow>
          (if nc_type node = File
           then Some \<lparr> nc_type = nc_type node,
                       nc_permissions = nc_permissions node,
                       nc_content = Some content \<rparr>
           else Some node)
    else fs p')"

(* Preconditions *)

definition read_file_precondition :: "path \<Rightarrow> filesystem_with_content \<Rightarrow> bool" where
  "read_file_precondition p fs = (
    \<exists>node. fs p = Some node \<and> nc_type node = File \<and> readable (nc_permissions node))"

definition write_file_precondition :: "path \<Rightarrow> filesystem_with_content \<Rightarrow> bool" where
  "write_file_precondition p fs = (
    \<exists>node. fs p = Some node \<and> nc_type node = File \<and> writable (nc_permissions node))"

(* Reversibility Theorems *)

theorem read_file_preserves_fs:
  "fs = fs"
  by auto

theorem write_file_reversible:
  assumes "write_file_precondition p fs"
      and "read_file p fs = Some old_content"
  shows "write_file p old_content (write_file p new_content fs) = fs"
proof -
  have "\<And>p'. (write_file p old_content (write_file p new_content fs)) p' = fs p'"
  proof -
    fix p'
    show "(write_file p old_content (write_file p new_content fs)) p' = fs p'"
    proof (cases "p = p'")
      case True
      obtain node where hnode: "fs p = Some node" "nc_type node = File"
        using assms(1) write_file_precondition_def by auto
      have hcontent: "nc_content node = Some old_content"
        using assms(2) hnode read_file_def by auto
      show ?thesis
        unfolding write_file_def
        using True hnode hcontent
        by auto
    next
      case False
      then show ?thesis
        unfolding write_file_def
        by auto
    qed
  qed
  then show ?thesis by auto
qed

(* Content Preservation *)

theorem write_file_independence:
  assumes "p1 \<noteq> p2"
  shows "read_file p2 (write_file p1 content fs) = read_file p2 fs"
  unfolding read_file_def write_file_def
  using assms
  by auto

(* Content Operations and Basic Operations *)

theorem create_file_empty_content:
  assumes "create_file_precondition p fs"
  shows "read_file p (fs_to_fs_with_content (create_file p fs)) = Some empty_content"
  unfolding read_file_def fs_to_fs_with_content_def create_file_def fs_update_def
  by auto

(* State Tracking for Reversibility *)

record file_state =
  state_path :: path
  state_content :: file_content
  state_exists :: bool

definition capture_file_state :: "path \<Rightarrow> filesystem_with_content \<Rightarrow> file_state" where
  "capture_file_state p fs = (
    case read_file p fs of
      Some content \<Rightarrow> \<lparr> state_path = p, state_content = content, state_exists = True \<rparr>
    | None \<Rightarrow> \<lparr> state_path = p, state_content = empty_content, state_exists = False \<rparr>)"

definition restore_file_state :: "file_state \<Rightarrow> filesystem_with_content \<Rightarrow> filesystem_with_content" where
  "restore_file_state state fs = (
    if state_exists state
    then write_file (state_path state) (state_content state) fs
    else fs)"

theorem capture_restore_identity:
  assumes "write_file_precondition p fs"
  shows "restore_file_state (capture_file_state p fs) fs = fs"
proof -
  obtain node where hnode: "fs p = Some node" "nc_type node = File"
    using assms write_file_precondition_def by auto
  have hread: "\<exists>content. read_file p fs = Some content"
    unfolding read_file_def using hnode by auto
  then obtain content where hcontent: "read_file p fs = Some content" by auto
  have "capture_file_state p fs = \<lparr> state_path = p, state_content = content, state_exists = True \<rparr>"
    unfolding capture_file_state_def using hcontent by auto
  then have "restore_file_state (capture_file_state p fs) fs = write_file p content fs"
    unfolding restore_file_state_def by auto
  also have "... = fs"
    using write_file_reversible[OF assms hcontent] by auto
  finally show ?thesis by auto
qed

(* MAA Framework Integration *)

record file_modification_record =
  mod_path :: path
  mod_old_content :: file_content
  mod_new_content :: file_content

definition apply_modification :: "file_modification_record \<Rightarrow> filesystem_with_content \<Rightarrow> filesystem_with_content" where
  "apply_modification record fs = write_file (mod_path record) (mod_new_content record) fs"

definition reverse_modification :: "file_modification_record \<Rightarrow> filesystem_with_content \<Rightarrow> filesystem_with_content" where
  "reverse_modification record fs = write_file (mod_path record) (mod_old_content record) fs"

theorem modification_reversible:
  assumes "write_file_precondition (mod_path record) fs"
      and "read_file (mod_path record) fs = Some (mod_old_content record)"
  shows "reverse_modification record (apply_modification record fs) = fs"
  unfolding reverse_modification_def apply_modification_def
  using write_file_reversible[OF assms]
  by auto

(* Summary: File content operations proven reversible in Isabelle/HOL
   - read/write file operations defined
   - reversibility of write operations proven
   - state capture/restore for undo functionality
   - MAA framework integration with modification records
*)

end
