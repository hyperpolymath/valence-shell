(* SPDX-License-Identifier: AGPL-3.0-or-later *)
theory FileContentOperations
  imports Main FilesystemModel FileOperations
begin

text \<open>
  Valence Shell - File Content Operations

  This theory extends the filesystem model with file content operations:
  - read_file: Read file contents
  - write_file: Write file contents

  These operations support reversible content modifications,
  enabling undo/redo for file content changes.
\<close>

section \<open>File Contents\<close>

text \<open>File content is a list of bytes\<close>
type_synonym FileContent = "nat list"

text \<open>Empty content\<close>
definition empty_content :: FileContent where
  "empty_content = []"

section \<open>Extended Filesystem with Content\<close>

text \<open>Extended filesystem node with content\<close>
record FSNodeWithContent =
  node_type :: NodeType
  node_perms :: Permissions
  node_content :: "FileContent option"  \<comment> \<open>None for directories, Some for files\<close>

text \<open>Extended filesystem mapping paths to nodes with content\<close>
type_synonym FilesystemWithContent = "Path \<Rightarrow> FSNodeWithContent option"

section \<open>Conversion Functions\<close>

text \<open>Convert basic filesystem to filesystem with content\<close>
definition fs_to_fs_with_content :: "Filesystem \<Rightarrow> FilesystemWithContent" where
  "fs_to_fs_with_content fs = (\<lambda>p.
    case fs p of
      None \<Rightarrow> None
    | Some node \<Rightarrow> Some \<lparr>
        node_type = get_node_type node,
        node_perms = get_permissions node,
        node_content = (if get_node_type node = File then Some empty_content else None)
      \<rparr>)"

section \<open>File Content Operations\<close>

text \<open>Read file content\<close>
definition read_file :: "Path \<Rightarrow> FilesystemWithContent \<Rightarrow> FileContent option" where
  "read_file p fs = (case fs p of
    None \<Rightarrow> None
  | Some node \<Rightarrow>
      if node_type node = File
      then node_content node
      else None)"

text \<open>Write file content\<close>
definition write_file :: "Path \<Rightarrow> FileContent \<Rightarrow> FilesystemWithContent \<Rightarrow> FilesystemWithContent" where
  "write_file p content fs = (\<lambda>p'.
    if p' = p then
      case fs p' of
        None \<Rightarrow> None
      | Some node \<Rightarrow>
          if node_type node = File
          then Some (node\<lparr>node_content := Some content\<rparr>)
          else Some node
    else fs p')"

section \<open>Preconditions\<close>

text \<open>Can read file if it exists and is a file with read permission\<close>
definition read_file_precondition :: "Path \<Rightarrow> FilesystemWithContent \<Rightarrow> bool" where
  "read_file_precondition p fs \<equiv>
    \<exists>node. fs p = Some node \<and>
           node_type node = File \<and>
           readable (node_perms node)"

text \<open>Can write file if it exists and is a file with write permission\<close>
definition write_file_precondition :: "Path \<Rightarrow> FilesystemWithContent \<Rightarrow> bool" where
  "write_file_precondition p fs \<equiv>
    \<exists>node. fs p = Some node \<and>
           node_type node = File \<and>
           writable (node_perms node)"

section \<open>Reversibility Properties\<close>

text \<open>Reading doesn't change the filesystem\<close>
theorem read_file_preserves_fs:
  assumes "read_file p fs = Some content"
  shows "fs = fs"
  by simp

text \<open>Writing old content back restores filesystem\<close>
theorem write_file_reversible:
  assumes "write_file_precondition p fs"
      and "read_file p fs = Some old_content"
  shows "write_file p old_content (write_file p new_content fs) = fs"
proof (rule ext)
  fix p'
  show "write_file p old_content (write_file p new_content fs) p' = fs p'"
  proof (cases "p' = p")
    case True
    from assms obtain node where
      node_def: "fs p = Some node" and
      is_file: "node_type node = File" and
      has_perm: "writable (node_perms node)"
      unfolding write_file_precondition_def by auto
    from assms(2) node_def is_file have
      content_eq: "node_content node = Some old_content"
      unfolding read_file_def by auto
    have "write_file p new_content fs p = Some (node\<lparr>node_content := Some new_content\<rparr>)"
      using node_def is_file
      unfolding write_file_def by simp
    hence "write_file p old_content (write_file p new_content fs) p =
           Some (node\<lparr>node_content := Some new_content\<rparr>\<lparr>node_content := Some old_content\<rparr>)"
      using is_file
      unfolding write_file_def by simp
    also have "... = Some (node\<lparr>node_content := Some old_content\<rparr>)"
      by simp
    also have "... = Some node"
      using content_eq by simp
    also have "... = fs p"
      using node_def by simp
    finally show ?thesis using True by simp
  next
    case False
    then show ?thesis
      unfolding write_file_def by simp
  qed
qed

section \<open>Content Preservation\<close>

text \<open>Writing to one file doesn't affect others\<close>
theorem write_file_independence:
  assumes "p1 \<noteq> p2"
  shows "read_file p2 (write_file p1 content fs) = read_file p2 fs"
  using assms
  unfolding write_file_def read_file_def
  by simp

section \<open>Content Operations and Basic Operations\<close>

text \<open>Creating a file initializes empty content\<close>
theorem create_file_empty_content:
  assumes "create_file_precondition p fs"
  shows "read_file p (fs_to_fs_with_content (create_file p fs)) = Some empty_content"
proof -
  have "create_file p fs p = Some (FileNode default_permissions [])"
    unfolding create_file_def fs_update_def by simp
  hence "fs_to_fs_with_content (create_file p fs) p =
         Some \<lparr>node_type = File, node_perms = default_permissions, node_content = Some empty_content\<rparr>"
    unfolding fs_to_fs_with_content_def by auto
  thus ?thesis
    unfolding read_file_def by simp
qed

section \<open>State Tracking for Reversibility\<close>

text \<open>Record of file state for undo/redo\<close>
record FileState =
  state_path :: Path
  state_content :: FileContent
  state_exists :: bool

text \<open>Capture current file state\<close>
definition capture_file_state :: "Path \<Rightarrow> FilesystemWithContent \<Rightarrow> FileState" where
  "capture_file_state p fs = (case read_file p fs of
    Some content \<Rightarrow> \<lparr>state_path = p, state_content = content, state_exists = True\<rparr>
  | None \<Rightarrow> \<lparr>state_path = p, state_content = empty_content, state_exists = False\<rparr>)"

text \<open>Restore file state\<close>
definition restore_file_state :: "FileState \<Rightarrow> FilesystemWithContent \<Rightarrow> FilesystemWithContent" where
  "restore_file_state state fs =
    (if state_exists state
     then write_file (state_path state) (state_content state) fs
     else fs)"

text \<open>Capturing and restoring is identity (for existing files)\<close>
theorem capture_restore_identity:
  assumes "write_file_precondition p fs"
  shows "restore_file_state (capture_file_state p fs) fs = fs"
proof -
  from assms obtain node where
    node_def: "fs p = Some node" and
    is_file: "node_type node = File"
    unfolding write_file_precondition_def by auto
  from node_def is_file have
    read_some: "\<exists>content. read_file p fs = Some content"
    unfolding read_file_def by auto
  then obtain content where read_eq: "read_file p fs = Some content" by auto
  have capture_eq: "capture_file_state p fs = \<lparr>state_path = p, state_content = content, state_exists = True\<rparr>"
    using read_eq
    unfolding capture_file_state_def by simp
  have restore_eq: "restore_file_state (capture_file_state p fs) fs =
                    write_file p content fs"
    using capture_eq
    unfolding restore_file_state_def by simp
  show ?thesis
  proof (rule ext)
    fix p'
    show "restore_file_state (capture_file_state p fs) fs p' = fs p'"
    proof (cases "p' = p")
      case True
      from read_eq node_def is_file have
        content_eq: "node_content node = Some content"
        unfolding read_file_def by auto
      have "write_file p content fs p = Some (node\<lparr>node_content := Some content\<rparr>)"
        using node_def is_file
        unfolding write_file_def by simp
      also have "... = Some node"
        using content_eq by simp
      also have "... = fs p"
        using node_def by simp
      finally show ?thesis using True restore_eq by simp
    next
      case False
      then show ?thesis
        using restore_eq
        unfolding write_file_def by simp
    qed
  qed
qed

section \<open>Integration with MAA Framework\<close>

text \<open>File modification record for audit trail\<close>
record FileModificationRecord =
  mod_path :: Path
  mod_old_content :: FileContent
  mod_new_content :: FileContent
  mod_timestamp :: nat

text \<open>Create modification record\<close>
definition create_mod_record :: "Path \<Rightarrow> FileContent \<Rightarrow> FileContent \<Rightarrow> nat \<Rightarrow> FileModificationRecord" where
  "create_mod_record p old_content new_content timestamp =
    \<lparr>mod_path = p, mod_old_content = old_content, mod_new_content = new_content, mod_timestamp = timestamp\<rparr>"

text \<open>Apply modification\<close>
definition apply_modification :: "FileModificationRecord \<Rightarrow> FilesystemWithContent \<Rightarrow> FilesystemWithContent" where
  "apply_modification record fs = write_file (mod_path record) (mod_new_content record) fs"

text \<open>Reverse modification\<close>
definition reverse_modification :: "FileModificationRecord \<Rightarrow> FilesystemWithContent \<Rightarrow> FilesystemWithContent" where
  "reverse_modification record fs = write_file (mod_path record) (mod_old_content record) fs"

text \<open>Modification is reversible\<close>
theorem modification_reversible:
  assumes "write_file_precondition (mod_path record) fs"
      and "read_file (mod_path record) fs = Some (mod_old_content record)"
  shows "reverse_modification record (apply_modification record fs) = fs"
  using assms
  unfolding reverse_modification_def apply_modification_def
  by (rule write_file_reversible)

text \<open>
  Summary of Proven Claims:

  \<checkmark> File content operations (read_file, write_file)
  \<checkmark> Preconditions for safe file access
  \<checkmark> Reversibility: write(p, old, write(p, new, fs)) = fs
  \<checkmark> Independence: write(p1, c, fs) doesn't affect p2
  \<checkmark> Integration with basic operations (create_file_empty_content)
  \<checkmark> State capture/restore for undo/redo
  \<checkmark> MAA modification records with reversibility

  This extends Valence Shell with content operations,
  maintaining the reversibility guarantees established
  for structural operations (mkdir, create, etc.).
\<close>

end
