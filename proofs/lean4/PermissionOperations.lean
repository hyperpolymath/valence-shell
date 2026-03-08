-- SPDX-License-Identifier: PMPL-1.0-or-later
/-
  Valence Shell - Permission Operations (Lean 4)

  Formalizes chmod and chown as reversible operations.
  Proves that applying the old permission/ownership after a change
  restores the original filesystem state.
-/

import FilesystemModel

namespace ValenceShell.Permissions

/-- Unix permission mode (lower 12 bits of mode_t) -/
def Mode := Nat

/-- Unix user/group IDs -/
structure Ownership where
  uid : Nat
  gid : Nat
  deriving Repr, DecidableEq

/-- Extended filesystem node with permissions and ownership -/
structure FSNodeExt where
  nodeType : FSNodeType
  mode : Mode
  owner : Ownership
  deriving Repr, DecidableEq

/-- Extended filesystem -/
def FilesystemExt := Path → Option FSNodeExt

-- ============================================================================
-- chmod Operation
-- ============================================================================

/-- chmod precondition: path must exist -/
def ChmodPrecondition (p : Path) (fs : FilesystemExt) : Prop :=
  ∃ node, fs p = some node

/-- Apply chmod: change mode bits of a file -/
def chmod (p : Path) (newMode : Mode) (fs : FilesystemExt) : FilesystemExt :=
  fun p' =>
    if p = p' then
      match fs p' with
      | none => none
      | some node => some { node with mode := newMode }
    else
      fs p'

/-- Theorem: chmod is reversible — restoring old mode restores fs -/
theorem chmod_reversible (p : Path) (fs : FilesystemExt)
    (oldMode newMode : Mode)
    (hpre : ChmodPrecondition p fs)
    (hold : ∃ node, fs p = some node ∧ node.mode = oldMode) :
    chmod p oldMode (chmod p newMode fs) = fs := by
  funext p'
  unfold chmod
  by_cases h : p = p'
  · subst h
    simp only [ite_true]
    obtain ⟨node, hnode, hmode⟩ := hold
    rw [hnode]
    simp only
    rw [hnode]
    simp only
    -- After two chmods: mode goes newMode → oldMode = original
    cases node with
    | mk nt m o =>
      simp only at hmode
      subst hmode
      rfl
  · simp only [h, ite_false]

/-- chmod to same mode is identity -/
theorem chmod_same_mode (p : Path) (fs : FilesystemExt)
    (hpre : ChmodPrecondition p fs)
    (hold : ∃ node, fs p = some node ∧ node.mode = m) :
    chmod p m fs = fs := by
  funext p'
  unfold chmod
  by_cases h : p = p'
  · subst h
    simp only [ite_true]
    obtain ⟨node, hnode, hmode⟩ := hold
    rw [hnode]
    cases node with
    | mk nt md o =>
      simp only at hmode
      subst hmode
      rfl
  · simp only [h, ite_false]

/-- chmod to different paths commute -/
theorem chmod_commute (p1 p2 : Path) (fs : FilesystemExt)
    (m1 m2 : Mode) (hneq : p1 ≠ p2) :
    chmod p1 m1 (chmod p2 m2 fs) = chmod p2 m2 (chmod p1 m1 fs) := by
  funext p'
  unfold chmod
  by_cases h1 : p1 = p'
  · subst h1
    have h2 : p2 ≠ p1 := Ne.symm hneq
    simp only [ite_true, h2, ite_false]
  · by_cases h2 : p2 = p'
    · subst h2
      simp only [h1, ite_false, ite_true]
    · simp only [h1, h2, ite_false]

/-- chmod preserves other paths -/
theorem chmod_preserves_other (p1 p2 : Path) (fs : FilesystemExt)
    (m : Mode) (hneq : p1 ≠ p2) :
    (chmod p1 m fs) p2 = fs p2 := by
  unfold chmod
  simp only [hneq, ite_false]

-- ============================================================================
-- chown Operation
-- ============================================================================

/-- chown precondition: path must exist -/
def ChownPrecondition (p : Path) (fs : FilesystemExt) : Prop :=
  ∃ node, fs p = some node

/-- Apply chown: change ownership of a file -/
def chown (p : Path) (newOwner : Ownership) (fs : FilesystemExt) : FilesystemExt :=
  fun p' =>
    if p = p' then
      match fs p' with
      | none => none
      | some node => some { node with owner := newOwner }
    else
      fs p'

/-- Theorem: chown is reversible — restoring old owner restores fs -/
theorem chown_reversible (p : Path) (fs : FilesystemExt)
    (oldOwner newOwner : Ownership)
    (hpre : ChownPrecondition p fs)
    (hold : ∃ node, fs p = some node ∧ node.owner = oldOwner) :
    chown p oldOwner (chown p newOwner fs) = fs := by
  funext p'
  unfold chown
  by_cases h : p = p'
  · subst h
    simp only [ite_true]
    obtain ⟨node, hnode, howner⟩ := hold
    rw [hnode]
    simp only
    rw [hnode]
    simp only
    cases node with
    | mk nt m o =>
      simp only at howner
      subst howner
      rfl
  · simp only [h, ite_false]

/-- chown to same owner is identity -/
theorem chown_same_owner (p : Path) (fs : FilesystemExt)
    (hpre : ChownPrecondition p fs)
    (hold : ∃ node, fs p = some node ∧ node.owner = o) :
    chown p o fs = fs := by
  funext p'
  unfold chown
  by_cases h : p = p'
  · subst h
    simp only [ite_true]
    obtain ⟨node, hnode, howner⟩ := hold
    rw [hnode]
    cases node with
    | mk nt m ow =>
      simp only at howner
      subst howner
      rfl
  · simp only [h, ite_false]

/-- chmod and chown commute (they modify different fields) -/
theorem chmod_chown_commute (p : Path) (fs : FilesystemExt)
    (m : Mode) (o : Ownership) :
    chmod p m (chown p o fs) = chown p o (chmod p m fs) := by
  funext p'
  unfold chmod chown
  by_cases h : p = p'
  · subst h
    simp only [ite_true]
    cases hfs : fs p with
    | none => simp [hfs]
    | some node => simp [hfs]
  · simp only [h, ite_false]

/-- chown preserves other paths -/
theorem chown_preserves_other (p1 p2 : Path) (fs : FilesystemExt)
    (o : Ownership) (hneq : p1 ≠ p2) :
    (chown p1 o fs) p2 = fs p2 := by
  unfold chown
  simp only [hneq, ite_false]

-- ============================================================================
-- Combined Permission Modification Record
-- ============================================================================

/-- Permission modification for audit trail -/
structure PermModRecord where
  modPath : Path
  oldMode : Mode
  newMode : Mode
  oldOwner : Ownership
  newOwner : Ownership

/-- Apply permission modification -/
def applyPermMod (rec : PermModRecord) (fs : FilesystemExt) : FilesystemExt :=
  chown rec.modPath rec.newOwner (chmod rec.modPath rec.newMode fs)

/-- Reverse permission modification -/
def reversePermMod (rec : PermModRecord) (fs : FilesystemExt) : FilesystemExt :=
  chown rec.modPath rec.oldOwner (chmod rec.modPath rec.oldMode fs)

/-
  Summary of Proven Claims:

  ✓ chmod_reversible — chmod(old, chmod(new, fs)) = fs
  ✓ chmod_same_mode — chmod with same mode is identity
  ✓ chmod_commute — chmod at different paths commutes
  ✓ chmod_preserves_other — chmod preserves unrelated paths
  ✓ chown_reversible — chown(old, chown(new, fs)) = fs
  ✓ chown_same_owner — chown with same owner is identity
  ✓ chmod_chown_commute — chmod and chown at same path commute
  ✓ chown_preserves_other — chown preserves unrelated paths
-/

end ValenceShell.Permissions
