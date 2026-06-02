/- SPDX-License-Identifier: MPL-2.0
   Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

   Valence Shell — Path-traversal containment proof (frontier item A-12)

   Formalises the path-normalisation discipline implemented by
   `vsh::state::ShellState::resolve_path` in `impl/rust-cli/src/state.rs`
   and proves that the result is always within the sandbox root,
   regardless of `..` components in the input.

   The 2026-02-12 audit caught a real CVE-class bug here
   (`resolve_path("../../etc/passwd")` escaped the sandbox before the
   `normalized.starts_with(root)` check + `..`-pop guard landed). This
   module is the regression-guard.

   Companion property test:
   `impl/rust-cli/tests/security_tests.rs::property_resolve_path_stays_within_sandbox`
-/

namespace PathTraversal

-- Path representation matches `FilesystemModel.Path` (List String of
-- components). Kept local to avoid coupling: this module is about
-- containment of a path-string normalisation, not about the
-- filesystem semantics.
abbrev Path := List String

-- A raw path component as parsed from a user-supplied string.
-- Mirrors `std::path::Component` in Rust (the three variants
-- `resolve_path` switches on; we elide RootDir/Prefix since the
-- Rust code strips them before normalisation).
inductive Component where
  | parentDir : Component
  | curDir    : Component
  | normal    : String → Component
  deriving DecidableEq, Repr

-- Step the normaliser by one component. Matches the Rust loop body:
--   `..` → pop if normalized strictly extends root (still within root
--          AND not at root); silently clamp at root otherwise
--   `.`  → skip
--   name → append
def applyComponent (root normalized : Path) (c : Component) : Path :=
  match c with
  | Component.parentDir =>
      if root <+: normalized ∧ normalized ≠ root then
        normalized.dropLast
      else
        normalized
  | Component.curDir    => normalized
  | Component.normal s  => normalized ++ [s]

-- Drive the normaliser over a list of components, starting from
-- `root` as the initial accumulator (matches the Rust implementation,
-- which starts `normalized` empty and pre-joins with root).
def normalizeRaw (root : Path) (raw : List Component) : Path :=
  raw.foldl (applyComponent root) root

-- The final safety check (Rust line 589-593 in `state.rs`): if the
-- accumulated result somehow does not start with root, clamp to root.
-- This is defensive; the foldl invariant we prove below means the
-- check never fires, but the clamp is what makes the theorem closed-
-- form regardless of `applyComponent` correctness.
def normalizePath (root : Path) (raw : List Component) : Path :=
  let n := normalizeRaw root raw
  if root <+: n then n else root

-- ---------------------------------------------------------------------
-- Helper lemmas
-- ---------------------------------------------------------------------

-- Appending on the right preserves prefix (`xs <+: ys → xs <+: ys ++ zs`).
-- This is the key compositional step used by the `Component.normal`
-- case. Uses `List.prefix_append` (every list is a prefix of itself
-- appended) plus transitivity of `<+:`.
theorem isPrefix_append_right
    (xs ys zs : Path) (h : xs <+: ys) :
    xs <+: ys ++ zs :=
  h.trans (List.prefix_append ys zs)

-- Dropping the last element preserves a prefix, provided the prefix
-- itself wasn't the whole list (otherwise dropping erases an element
-- of the prefix and breaks containment).
theorem isPrefix_dropLast
    (xs ys : Path)
    (hp : xs <+: ys) (hne : ys ≠ xs) :
    xs <+: ys.dropLast := by
  -- Obtain the witness suffix: ys = xs ++ tail
  obtain ⟨tail, htail⟩ := hp
  -- tail must be non-empty (if it were [], then ys = xs ++ [] = xs,
  -- contradicting hne).
  cases tail with
  | nil =>
      exfalso; apply hne
      simpa using htail.symm
  | cons t ts =>
      -- ys = xs ++ (t :: ts); dropLast strips the trailing element.
      -- ys.dropLast = (xs ++ (t :: ts)).dropLast = xs ++ (t :: ts).dropLast
      -- (since t :: ts is non-empty), so xs is still a prefix.
      refine ⟨(t :: ts).dropLast, ?_⟩
      subst htail
      rw [List.dropLast_append_of_ne_nil _ (List.cons_ne_nil t ts)]

-- ---------------------------------------------------------------------
-- Per-step invariant
-- ---------------------------------------------------------------------

-- Applying one component preserves the root-prefix invariant.
theorem applyComponent_preserves_root_prefix
    (root normalized : Path) (c : Component)
    (h : root <+: normalized) :
    root <+: applyComponent root normalized c := by
  cases c with
  | curDir =>
      unfold applyComponent
      exact h
  | normal s =>
      unfold applyComponent
      exact isPrefix_append_right root normalized [s] h
  | parentDir =>
      unfold applyComponent
      by_cases hcond : root <+: normalized ∧ normalized ≠ root
      · simp [hcond]
        obtain ⟨hpre, hne⟩ := hcond
        exact isPrefix_dropLast root normalized hpre hne
      · simp [hcond]; exact h

-- ---------------------------------------------------------------------
-- foldl invariant
-- ---------------------------------------------------------------------

-- foldl preserves the root-prefix invariant for any initial accumulator
-- that already starts with root.
theorem normalizeRaw_acc_preserves_root_prefix
    (root : Path) :
    ∀ (raw : List Component) (acc : Path),
      root <+: acc →
      root <+: raw.foldl (applyComponent root) acc := by
  intro raw
  induction raw with
  | nil =>
      intro acc h; exact h
  | cons c rest ih =>
      intro acc h
      simp only [List.foldl]
      apply ih
      exact applyComponent_preserves_root_prefix root acc c h

-- The intermediate result is always within root.
theorem normalizeRaw_within_root (root : Path) (raw : List Component) :
    root <+: normalizeRaw root raw := by
  unfold normalizeRaw
  exact normalizeRaw_acc_preserves_root_prefix root raw root (List.prefix_refl root)

-- ---------------------------------------------------------------------
-- Headline theorem (frontier A-12)
-- ---------------------------------------------------------------------

-- Path-traversal containment: `normalizePath root raw` is always a
-- descendant of `root`, regardless of `..` / `.` / normal components
-- in `raw`. This is the regression-guard for the 2026-02-12 CVE-class
-- audit fix.
theorem path_traversal_containment
    (root : Path) (raw : List Component) :
    root <+: normalizePath root raw := by
  unfold normalizePath
  by_cases h : root <+: normalizeRaw root raw
  · simp [h]
  · simp [h]

-- Corollary: the final clamp never fires (the unfolded definition
-- always lands on `normalizeRaw root raw`, never on the fallback
-- `root`). Useful as a regression-guard against changes to
-- `applyComponent` that would silently break the invariant.
theorem normalizePath_eq_normalizeRaw
    (root : Path) (raw : List Component) :
    normalizePath root raw = normalizeRaw root raw := by
  unfold normalizePath
  have h : root <+: normalizeRaw root raw := normalizeRaw_within_root root raw
  simp [h]

end PathTraversal
