(* SPDX-License-Identifier: PMPL-1.0-or-later *)
theory PermissionOperations
  imports FilesystemModel
begin

text \<open>
  Valence Shell - Permission Operations

  Formalizes chmod and chown as reversible operations.
  Proves that applying the old permission/ownership after a change
  restores the original filesystem state.
\<close>

section \<open>Extended Types for Permission/Ownership\<close>

text \<open>Unix permission mode (lower 12 bits of mode_t)\<close>
type_synonym mode = nat

text \<open>Unix user/group IDs\<close>
record ownership =
  uid :: nat
  gid :: nat

text \<open>Extended filesystem node with separate mode and ownership\<close>
record fs_node_ext =
  ext_node_type :: fs_node_type
  ext_mode :: mode
  ext_owner :: ownership

text \<open>Extended filesystem\<close>
type_synonym filesystem_ext = "path \<Rightarrow> fs_node_ext option"

section \<open>chmod Operation\<close>

text \<open>chmod precondition: path must exist\<close>
definition chmod_precondition :: "path \<Rightarrow> filesystem_ext \<Rightarrow> bool" where
  "chmod_precondition p fs = (\<exists>node. fs p = Some node)"

text \<open>Apply chmod: change mode bits of a file\<close>
definition chmod :: "path \<Rightarrow> mode \<Rightarrow> filesystem_ext \<Rightarrow> filesystem_ext" where
  "chmod p newMode fs = (\<lambda>p'.
    if p = p' then
      (case fs p' of
        None \<Rightarrow> None
      | Some node \<Rightarrow> Some \<lparr> ext_node_type = ext_node_type node,
                             ext_mode = newMode,
                             ext_owner = ext_owner node \<rparr>)
    else
      fs p')"

section \<open>chmod Theorems\<close>

theorem chmod_reversible:
  assumes "\<exists>node. fs p = Some node \<and> ext_mode node = oldMode"
  shows "chmod p oldMode (chmod p newMode fs) = fs"
proof -
  have "\<And>p'. (chmod p oldMode (chmod p newMode fs)) p' = fs p'"
  proof -
    fix p'
    show "(chmod p oldMode (chmod p newMode fs)) p' = fs p'"
    proof (cases "p = p'")
      case True
      obtain node where Hnode: "fs p = Some node" and Hmode: "ext_mode node = oldMode"
        using assms by auto
      show ?thesis
        unfolding chmod_def
        using True Hnode Hmode
        by (cases node) auto
    next
      case False
      then show ?thesis
        unfolding chmod_def
        by auto
    qed
  qed
  then show ?thesis by auto
qed

theorem chmod_same_mode:
  assumes "\<exists>node. fs p = Some node \<and> ext_mode node = m"
  shows "chmod p m fs = fs"
proof -
  have "\<And>p'. (chmod p m fs) p' = fs p'"
  proof -
    fix p'
    show "(chmod p m fs) p' = fs p'"
    proof (cases "p = p'")
      case True
      obtain node where Hnode: "fs p = Some node" and Hmode: "ext_mode node = m"
        using assms by auto
      show ?thesis
        unfolding chmod_def
        using True Hnode Hmode
        by (cases node) auto
    next
      case False
      then show ?thesis
        unfolding chmod_def
        by auto
    qed
  qed
  then show ?thesis by auto
qed

theorem chmod_commute:
  assumes "p1 \<noteq> p2"
  shows "chmod p1 m1 (chmod p2 m2 fs) = chmod p2 m2 (chmod p1 m1 fs)"
proof -
  have "\<And>p'. (chmod p1 m1 (chmod p2 m2 fs)) p' = (chmod p2 m2 (chmod p1 m1 fs)) p'"
  proof -
    fix p'
    show "(chmod p1 m1 (chmod p2 m2 fs)) p' = (chmod p2 m2 (chmod p1 m1 fs)) p'"
    proof (cases "p1 = p'")
      case True
      then have "p2 \<noteq> p'" using assms by auto
      then show ?thesis
        unfolding chmod_def
        using True by auto
    next
      case False
      then show ?thesis
      proof (cases "p2 = p'")
        case True
        then show ?thesis
          unfolding chmod_def
          using False by auto
      next
        case False2: False
        then show ?thesis
          unfolding chmod_def
          using False by auto
      qed
    qed
  qed
  then show ?thesis by auto
qed

theorem chmod_preserves_other:
  assumes "p1 \<noteq> p2"
  shows "(chmod p1 m fs) p2 = fs p2"
  unfolding chmod_def
  using assms by auto

section \<open>chown Operation\<close>

text \<open>chown precondition: path must exist\<close>
definition chown_precondition :: "path \<Rightarrow> filesystem_ext \<Rightarrow> bool" where
  "chown_precondition p fs = (\<exists>node. fs p = Some node)"

text \<open>Apply chown: change ownership of a file\<close>
definition chown :: "path \<Rightarrow> ownership \<Rightarrow> filesystem_ext \<Rightarrow> filesystem_ext" where
  "chown p newOwner fs = (\<lambda>p'.
    if p = p' then
      (case fs p' of
        None \<Rightarrow> None
      | Some node \<Rightarrow> Some \<lparr> ext_node_type = ext_node_type node,
                             ext_mode = ext_mode node,
                             ext_owner = newOwner \<rparr>)
    else
      fs p')"

section \<open>chown Theorems\<close>

theorem chown_reversible:
  assumes "\<exists>node. fs p = Some node \<and> ext_owner node = oldOwner"
  shows "chown p oldOwner (chown p newOwner fs) = fs"
proof -
  have "\<And>p'. (chown p oldOwner (chown p newOwner fs)) p' = fs p'"
  proof -
    fix p'
    show "(chown p oldOwner (chown p newOwner fs)) p' = fs p'"
    proof (cases "p = p'")
      case True
      obtain node where Hnode: "fs p = Some node" and Howner: "ext_owner node = oldOwner"
        using assms by auto
      show ?thesis
        unfolding chown_def
        using True Hnode Howner
        by (cases node) auto
    next
      case False
      then show ?thesis
        unfolding chown_def
        by auto
    qed
  qed
  then show ?thesis by auto
qed

theorem chown_same_owner:
  assumes "\<exists>node. fs p = Some node \<and> ext_owner node = o"
  shows "chown p o fs = fs"
proof -
  have "\<And>p'. (chown p o fs) p' = fs p'"
  proof -
    fix p'
    show "(chown p o fs) p' = fs p'"
    proof (cases "p = p'")
      case True
      obtain node where Hnode: "fs p = Some node" and Howner: "ext_owner node = o"
        using assms by auto
      show ?thesis
        unfolding chown_def
        using True Hnode Howner
        by (cases node) auto
    next
      case False
      then show ?thesis
        unfolding chown_def
        by auto
    qed
  qed
  then show ?thesis by auto
qed

theorem chmod_chown_commute:
  "chmod p m (chown p o fs) = chown p o (chmod p m fs)"
proof -
  have "\<And>p'. (chmod p m (chown p o fs)) p' = (chown p o (chmod p m fs)) p'"
  proof -
    fix p'
    show "(chmod p m (chown p o fs)) p' = (chown p o (chmod p m fs)) p'"
    proof (cases "p = p'")
      case True
      then show ?thesis
        unfolding chmod_def chown_def
        by (cases "fs p") auto
    next
      case False
      then show ?thesis
        unfolding chmod_def chown_def
        by auto
    qed
  qed
  then show ?thesis by auto
qed

theorem chown_preserves_other:
  assumes "p1 \<noteq> p2"
  shows "(chown p1 o fs) p2 = fs p2"
  unfolding chown_def
  using assms by auto

text \<open>
  Summary of Proven Claims:

  @{text "\<checkmark>"} chmod_reversible -- chmod(old, chmod(new, fs)) = fs
  @{text "\<checkmark>"} chmod_same_mode -- chmod with same mode is identity
  @{text "\<checkmark>"} chmod_commute -- chmod at different paths commutes
  @{text "\<checkmark>"} chmod_preserves_other -- chmod preserves unrelated paths
  @{text "\<checkmark>"} chown_reversible -- chown(old, chown(new, fs)) = fs
  @{text "\<checkmark>"} chown_same_owner -- chown with same owner is identity
  @{text "\<checkmark>"} chmod_chown_commute -- chmod and chown at same path commute
  @{text "\<checkmark>"} chown_preserves_other -- chown preserves unrelated paths
\<close>

end
