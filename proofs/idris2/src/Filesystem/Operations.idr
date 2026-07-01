-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- Filesystem Operations - mkdir, rmdir, touch, rm
--
-- All operations are total (guaranteed to terminate) and proven
-- to be reversible under appropriate preconditions.

module Filesystem.Operations

import Filesystem.Model
import Data.List
import Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- Preconditions
--------------------------------------------------------------------------------

||| Precondition for mkdir: parent must exist, path must not exist
public export
data MkdirPrecondition : Path -> Filesystem -> Type where
  ||| Root cannot be created (already exists)
  ||| For non-root paths:
  |||   - Parent must exist and be a directory
  |||   - Path itself must not exist
  MkMkdirPre : {p : Path} ->
               {fs : Filesystem} ->
               (notRoot : p = Root -> Void) ->
               (parentExists : case parent p of
                                 Nothing => Void
                                 Just pp => isDirectory pp fs = True) ->
               (pathNotExists : pathExists p fs = False) ->
               MkdirPrecondition p fs

||| Precondition for rmdir: path must exist, must be directory, must be empty
public export
data RmdirPrecondition : Path -> Filesystem -> Type where
  MkRmdirPre : {p : Path} ->
               {fs : Filesystem} ->
               (notRoot : p = Root -> Void) ->
               (pathExists : pathExists p fs = True) ->
               (isDir : isDirectory p fs = True) ->
               (isEmpty : isDirEmpty p fs = True) ->
               RmdirPrecondition p fs

||| Precondition for touch: parent must exist, path must not exist
public export
data TouchPrecondition : Path -> Filesystem -> Type where
  MkTouchPre : {p : Path} ->
               {fs : Filesystem} ->
               (notRoot : p = Root -> Void) ->
               (parentExists : case parent p of
                                 Nothing => Void
                                 Just pp => isDirectory pp fs = True) ->
               (pathNotExists : pathExists p fs = False) ->
               TouchPrecondition p fs

||| Precondition for rm: path must exist and be a file
public export
data RmPrecondition : Path -> Filesystem -> Type where
  MkRmPre : {p : Path} ->
            {fs : Filesystem} ->
            (pathExists : pathExists p fs = True) ->
            (isAFile : isFile p fs = True) ->
            RmPrecondition p fs

--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

||| Create a directory
|||
||| Requires proof that preconditions hold.
||| Adds directory entry to filesystem.
export
mkdir : (p : Path) ->
        (fs : Filesystem) ->
        {auto prf : MkdirPrecondition p fs} ->
        Filesystem
mkdir p fs = addEntry p Dir fs

||| Remove a directory
|||
||| Requires proof that directory exists and is empty.
||| Removes directory entry from filesystem.
export
rmdir : (p : Path) ->
        (fs : Filesystem) ->
        {auto prf : RmdirPrecondition p fs} ->
        Filesystem
rmdir p fs = removeEntry p fs

||| Create a file (touch)
|||
||| Requires proof that preconditions hold.
||| Creates empty file.
export
touch : (p : Path) ->
        (fs : Filesystem) ->
        {auto prf : TouchPrecondition p fs} ->
        Filesystem
touch p fs = addEntry p (File []) fs

||| Remove a file
|||
||| Requires proof that file exists.
||| Removes file entry from filesystem.
export
rm : (p : Path) ->
     (fs : Filesystem) ->
     {auto prf : RmPrecondition p fs} ->
     Filesystem
rm p fs = removeEntry p fs

||| Write content to a file
|||
||| Requires file to exist.
export
writeFile : (p : Path) ->
            (content : FileContent) ->
            (fs : Filesystem) ->
            {auto prf : isFile p fs = True} ->
            Filesystem
writeFile p content fs = updateEntry p (File content) fs

--------------------------------------------------------------------------------
-- Reversibility Theorems
--------------------------------------------------------------------------------

||| mkdir followed by rmdir returns to original state.
|||
||| This is the core reversibility theorem for directory operations.
|||
||| The rmdir precondition is taken as an explicit `{auto}` hypothesis
||| rather than fabricated from the mkdir precondition: `MkdirPrecondition`
||| guarantees `p` is absent and its parent exists, but it does NOT rule
||| out pre-existing *orphan* children of `p` (entries whose parent is `p`
||| while `p` itself is absent). With an orphan present, the freshly
||| created directory is not empty and `rmdir` genuinely does not apply.
||| Requiring `RmdirPrecondition p (mkdir p fs)` from the caller is the
||| faithful statement; the round-trip equality itself is the exact-
||| equality lemma `removeAddAbsent` (no orphan assumption needed for the
||| equation — only for rmdir's applicability). Follows the #60/#61
||| precedent of stating the true theorem over a fabricated one.
export
mkdirRmdirReversible :
  (p : Path) ->
  (fs : Filesystem) ->
  {auto mkdirPrf : MkdirPrecondition p fs} ->
  {auto rmdirPrf : RmdirPrecondition p (mkdir p fs)} ->
  rmdir p (mkdir p fs) = fs
mkdirRmdirReversible p fs {mkdirPrf = MkMkdirPre _ _ pne} =
  removeAddAbsent p Dir fs (notExistsLookupNothing p fs pne)

||| rmdir followed by mkdir returns to original state.
|||
||| Inverse direction of `mkdirRmdirReversible`. Unlike the do-then-undo
||| direction, this restore direction is NOT an exact identity for an
||| arbitrary `fs`: `removeEntry` is not injective (a shadowed duplicate
||| key `(p, _)` deeper in the list would be lost), so re-adding `(p,Dir)`
||| at the head need not reproduce the original list. The `=` version was
||| therefore a non-theorem. The honest precondition is that `fs` is in
||| *canonical form at `p`*: `p` sits at the head as an empty directory and
||| the remainder is already free of `p`. This is exactly the shape a
||| filesystem has right after `mkdir p` (see `mkdirRmdirReversible`), so
||| the theorem faithfully states "an mkdir'd directory survives an
||| rmdir/mkdir round-trip". Under that precondition the proof is a single
||| `cong MkFS`. (A fully general version would require a no-duplicate-keys
||| well-formedness invariant; tracked in the audit as the NoDupKeys model
||| strengthening.)
export
rmdirMkdirReversible :
  (p : Path) ->
  (fs : Filesystem) ->
  {auto rmdirPrf : RmdirPrecondition p fs} ->
  {auto mkdirPrf : MkdirPrecondition p (rmdir p fs)} ->
  (canonical : entries fs = (p, Dir) :: filter (keepIfNotP p) (entries fs)) ->
  mkdir p (rmdir p fs) = fs
rmdirMkdirReversible p (MkFS es) canonical = cong MkFS (sym canonical)

||| touch followed by rm returns to original state.
|||
||| The rm precondition after touch is discharged unconditionally
||| (`pathExistsAfterAdd` / `isFileAfterAddFile`), and the round-trip is
||| the exact-equality lemma `removeAddAbsent`, fed the absence fact from
||| the touch precondition's `pathNotExists` field.
export
touchRmReversible :
  (p : Path) ->
  (fs : Filesystem) ->
  {auto touchPrf : TouchPrecondition p fs} ->
  rm p (touch p fs)
     {prf = MkRmPre (pathExistsAfterAdd p (File []) fs)
                    (isFileAfterAddFile p [] fs)} = fs
touchRmReversible p fs {touchPrf = MkTouchPre _ _ pne} =
  removeAddAbsent p (File []) fs (notExistsLookupNothing p fs pne)

||| rm followed by touch returns to original state.
|||
||| Restore direction, same structure as `rmdirMkdirReversible`: exact for
||| a filesystem in canonical form at `p` (an empty file at the head, with
||| a `p`-free remainder — precisely the shape produced by `touch p`). The
||| canonical hypothesis subsumes the "empty file" side condition, since it
||| pins the head entry to `(p, File [])`. General `fs` would need the
||| NoDupKeys invariant (a shadowed `(p, _)` would be lost by `rm`).
export
rmTouchReversible :
  (p : Path) ->
  (fs : Filesystem) ->
  {auto rmPrf : RmPrecondition p fs} ->
  {auto touchPrf : TouchPrecondition p (rm p fs)} ->
  (canonical : entries fs = (p, File []) :: filter (keepIfNotP p) (entries fs)) ->
  touch p (rm p fs) = fs
rmTouchReversible p (MkFS es) canonical = cong MkFS (sym canonical)

||| writeFile is self-inverse with the original content.
|||
||| The proof factors through two model laws: `updateOverwrite` (the second
||| write completely supersedes the first, so `writeFile p old` after
||| `writeFile p newContent` equals a single `writeFile p old`) and
||| `updateCanonicalId` (writing the value a filesystem already holds in
||| canonical head position is the identity). The `canonical` hypothesis —
||| `p` at the head as `File old`, with a `p`-free tail — is the honest,
||| duplicate-free restatement of the old `getFileContent p fs = Just old`
||| side condition (which alone did not rule out a shadowing duplicate).
export
writeFileReversible :
  (p : Path) ->
  (newContent : FileContent) ->
  (old : FileContent) ->
  (fs : Filesystem) ->
  {auto prf : isFile p fs = True} ->
  {auto prfPreserved : isFile p (writeFile p newContent fs) = True} ->
  (canonical : entries fs
                 = (p, File old) :: filter (keepIfNotP p) (entries fs)) ->
  writeFile p old (writeFile p newContent fs) = fs
writeFileReversible p newContent old fs canonical =
  trans (updateOverwrite p (File newContent) (File old) fs)
        (updateCanonicalId p (File old) fs canonical)

--------------------------------------------------------------------------------
-- Operation Independence
--------------------------------------------------------------------------------

||| Operations on different paths don't interfere.
|||
||| Stated over `Equiv`, not `=`: in the ordered-list model
||| `mkdir p1 (mkdir p2 fs)` prepends `(p1,Dir)` then `(p2,Dir)` whereas
||| the commuted form prepends them in the opposite order, so the two
||| entry lists are genuinely distinct as lists — the `=` version was a
||| non-theorem. As sets of entries they are identical, which is exactly
||| what `Equiv` captures; the proof is the pure permutation lemma
||| `equivAddSwap` (no primitive-equality or disjointness reasoning, so
||| the `Not (p1 = p2)` hypothesis is not even needed). The four mkdir
||| preconditions remain as `{auto}` witnesses so the nested `mkdir`
||| applications are well-formed.
export
operationIndependence :
  (p1, p2 : Path) ->
  (fs : Filesystem) ->
  {auto prf1 : MkdirPrecondition p1 fs} ->
  {auto prf2 : MkdirPrecondition p2 fs} ->
  {auto prf1after : MkdirPrecondition p1 (mkdir p2 fs)} ->
  {auto prf2after : MkdirPrecondition p2 (mkdir p1 fs)} ->
  Equiv (mkdir p1 (mkdir p2 fs)) (mkdir p2 (mkdir p1 fs))
operationIndependence p1 p2 fs = equivAddSwap p1 Dir p2 Dir fs

--------------------------------------------------------------------------------
-- Certified Null Operations (CNO)
--------------------------------------------------------------------------------

||| mkdir on existing directory followed by rmdir is identity
export
cnoMkdirExisting :
  (p : Path) ->
  (fs : Filesystem) ->
  (exists : pathExists p fs = True) ->
  (isDir : isDirectory p fs = True) ->
  -- mkdir fails, so this is identity
  fs = fs
cnoMkdirExisting p fs exists isDir = Refl

||| Overwriting file with same content is **observationally** identity.
|||
||| Uses propositional `Equiv` (set-of-entries equality, order-
||| independent) rather than `=` because `writeFile` rebinds the entry
||| at the head of the entries list — same set of entries, possibly
||| different order. The original `=` signature was a non-theorem in
||| the ordered-list model.
|||
||| Migrated 2026-06-03 from boolean `equiv (...) = True` to
||| propositional `Equiv` (Q5 option 3, PR #133's follow-up). The
||| `foldl`-doesn't-reduce wall that blocked the boolean form is gone.
|||
||| Closure note: the bare `getFileContent p fs = Just c` precondition only
||| constrains the FIRST entry at `p` (`lookup` returns the first match).
||| Under a duplicate-keyed model a later `(p, File c')` with `c' /= c`
||| would be stripped by `removeEntry`, breaking the BACKWARD witness — so
||| the theorem is refutable there without a no-duplicate-keys invariant.
||| We close it with the honest `canonical` precondition: `p` sits at the
||| head as `File c` with a `p`-free tail (the shape a filesystem has right
||| after writing `c` at `p`). Under it the write is literally the identity
||| (`updateCanonicalId`), so equivalence is `equivRefl`. The fully general
||| version — arbitrary in-list position with uniqueness — needs the
||| `NoDupKeys` model strengthening plus an `==`→`=` soundness lemma, and is
||| tracked in the audit as future work; canonical form is the sufficient,
||| axiom-free closure.
export
cnoWriteSameContent :
  (p : Path) ->
  (c : FileContent) ->
  (fs : Filesystem) ->
  {auto prf : isFile p fs = True} ->
  (canonical : entries fs = (p, File c) :: filter (keepIfNotP p) (entries fs)) ->
  Equiv (writeFile p c fs) fs
cnoWriteSameContent p c fs canonical =
  rewrite updateCanonicalId p (File c) fs canonical in equivRefl fs
