-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- Filesystem Model - Core Types and Definitions
--
-- This module defines the abstract filesystem model used throughout
-- the valence-shell verification. All operations are total and proven
-- to terminate.

module Filesystem.Model

import Data.Bool
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.String
import Decidable.Equality

import Filesystem.Axioms

%default total

--------------------------------------------------------------------------------
-- Path Representation
--------------------------------------------------------------------------------

||| A filesystem path represented as a list of components
||| Root is the empty list, /foo/bar is ["foo", "bar"]
public export
data Path : Type where
  ||| Root path /
  Root : Path
  ||| Path component
  Cons : String -> Path -> Path

%name Path p, q, r

||| Convert path to string for display
export
pathToString : Path -> String
pathToString Root = "/"
pathToString (Cons comp rest) =
  "/" ++ comp ++ pathToString rest

||| Path equality is decidable
export
DecEq Path where
  decEq Root Root = Yes Refl
  decEq Root (Cons _ _) = No (\case Refl impossible)
  decEq (Cons _ _) Root = No (\case Refl impossible)
  decEq (Cons x xs) (Cons y ys) with (decEq x y)
    decEq (Cons x xs) (Cons x ys) | Yes Refl with (decEq xs ys)
      decEq (Cons x xs) (Cons x xs) | Yes Refl | Yes Refl = Yes Refl
      decEq (Cons x xs) (Cons x ys) | Yes Refl | No contra =
        No (\Refl => contra Refl)
    decEq (Cons x xs) (Cons y ys) | No contra =
      No (\Refl => contra Refl)

||| Boolean equality on paths (required by Data.List.lookup / elem)
public export
Eq Path where
  Root         == Root         = True
  (Cons x xs)  == (Cons y ys)  = x == y && xs == ys
  _            == _            = False

||| Parent of a path
export
parent : Path -> Maybe Path
parent Root = Nothing
parent (Cons _ p) = Just p

||| Check if path is root
export
isRoot : Path -> Bool
isRoot Root = True
isRoot _ = False

--------------------------------------------------------------------------------
-- Filesystem State
--------------------------------------------------------------------------------

||| File content represented as list of bytes
public export
FileContent : Type
FileContent = List Bits8

||| A filesystem entry - either directory or file
public export
data FSEntry : Type where
  ||| Directory entry
  Dir : FSEntry
  ||| File entry with content
  File : FileContent -> FSEntry

||| Boolean equality on filesystem entries
public export
Eq FSEntry where
  Dir          == Dir          = True
  (File c1)    == (File c2)    = c1 == c2
  _            == _            = False

||| Filesystem state mapping paths to entries
public export
record Filesystem where
  constructor MkFS
  ||| Mapping from paths to entries
  entries : List (Path, FSEntry)

%name Filesystem fs, fs1, fs2

||| Empty filesystem (only root directory)
export
empty : Filesystem
empty = MkFS []

--------------------------------------------------------------------------------
-- Filesystem Queries
--------------------------------------------------------------------------------

||| Check if a path exists in the filesystem
export
pathExists : Path -> Filesystem -> Bool
pathExists p (MkFS entries) =
  isJust $ lookup p entries

||| Get entry at path
export
getEntry : Path -> Filesystem -> Maybe FSEntry
getEntry p (MkFS entries) = lookup p entries

||| Check if path is a directory
export
isDirectory : Path -> Filesystem -> Bool
isDirectory p fs = case getEntry p fs of
  Just Dir => True
  _ => False

||| Check if path is a file
export
isFile : Path -> Filesystem -> Bool
isFile p fs = case getEntry p fs of
  Just (File _) => True
  _ => False

||| Get file content
export
getFileContent : Path -> Filesystem -> Maybe FileContent
getFileContent p fs = case getEntry p fs of
  Just (File content) => Just content
  _ => Nothing

||| Check if directory is empty
export
isDirEmpty : Path -> Filesystem -> Bool
isDirEmpty p (MkFS entries) =
  let children = filter (\(q, _) => parent q == Just p) entries
  in null children

--------------------------------------------------------------------------------
-- Filesystem Modification
--------------------------------------------------------------------------------

||| Add an entry to filesystem
public export
addEntry : Path -> FSEntry -> Filesystem -> Filesystem
addEntry p entry (MkFS entries) =
  MkFS ((p, entry) :: entries)

||| Predicate: keep entries at paths other than `p`. Named (rather than
||| inlined as a lambda) so that proofs about `removeEntry` can refer to
||| the *same* predicate as the implementation — anonymous lambdas at
||| separate call sites don't unify in Idris2 0.8.0.
public export
keepIfNotP : Path -> (Path, FSEntry) -> Bool
keepIfNotP p (q, _) = p /= q

||| Remove an entry from filesystem
public export
removeEntry : Path -> Filesystem -> Filesystem
removeEntry p (MkFS entries) =
  MkFS (filter (keepIfNotP p) entries)

||| `removeEntry p` depends only on the `keepIfNotP p` projection of the
||| entries list. If two filesystems agree on this projection, they are
||| observationally identical after `removeEntry p`. This is the
||| structural lemma underlying RMO's non-injectivity (see
||| `Filesystem.RMO.secureDeleteNotInjective`, which mirrors Coq's
||| `obliterate_not_injective`).
public export
removeEntryDeterminedByFilter :
  (p : Path) ->
  (fs1, fs2 : Filesystem) ->
  filter (keepIfNotP p) (entries fs1)
    = filter (keepIfNotP p) (entries fs2) ->
  removeEntry p fs1 = removeEntry p fs2
removeEntryDeterminedByFilter p (MkFS e1) (MkFS e2) agreeOff =
  cong MkFS agreeOff

||| Update entry at path
public export
updateEntry : Path -> FSEntry -> Filesystem -> Filesystem
updateEntry p entry fs =
  addEntry p entry (removeEntry p fs)

--------------------------------------------------------------------------------
-- Primitive-eq reflexivity (lifted from Filesystem.Axioms)
--
-- Kept after the 2026-06-03 Q5-option-3 migration: `Equiv` no longer
-- consumes these derived lemmas, but they remain available for future
-- proofs that genuinely need leaf-level `(==) = True` shape.
--------------------------------------------------------------------------------

||| `Path` equality is reflexive — proved by structural induction over
||| `Path`, using `axStringEqRefl` at the leaf for each `String` component.
export
pathEqRefl : (p : Path) -> (p == p) = True
pathEqRefl Root = Refl
pathEqRefl (Cons s rest) =
  rewrite axStringEqRefl s in
  rewrite pathEqRefl rest in
  Refl

||| `FSEntry` equality is reflexive — `Dir == Dir = True` by definition,
||| `File c == File c = c == c = True` via `fileContentEqRefl`.
export
fsEntryEqRefl : (e : FSEntry) -> (e == e) = True
fsEntryEqRefl Dir = Refl
fsEntryEqRefl (File c) = fileContentEqRefl c

||| Tuple `(Path, FSEntry)` equality reflexivity — combines `pathEqRefl`
||| and `fsEntryEqRefl` through the derived `Eq` instance.
export
entryEqRefl : (e : (Path, FSEntry)) -> (e == e) = True
entryEqRefl (p, fe) =
  rewrite pathEqRefl p in
  rewrite fsEntryEqRefl fe in
  Refl

--------------------------------------------------------------------------------
-- Structural lemmas about addEntry / removeEntry / lookup
--
-- These are the algebraic backbone the reversibility theorems in
-- `Filesystem.Operations` and `Filesystem.Composition` are built on.
-- They live here (not in the downstream modules) because `addEntry`,
-- `removeEntry` and `keepIfNotP` reduce definitionally only inside their
-- defining module; exporting the *lemmas* lets callers reason about the
-- operations without the definitions leaking across the module boundary.
--------------------------------------------------------------------------------

||| `keepIfNotP p` rejects the key `p` itself. Closes the leaf on
||| `pathEqRefl` (which in turn rests on `axStringEqRefl`).
export
keepSelfFalse : (p : Path) -> (e : FSEntry) -> keepIfNotP p (p, e) = False
keepSelfFalse p e = rewrite pathEqRefl p in Refl

||| `lookup` on a list whose head key is exactly `p` returns that head's
||| value — the first-match semantics collapse via `pathEqRefl`.
export
lookupConsSame : (p : Path) -> (v : FSEntry) -> (es : List (Path, FSEntry)) ->
                 lookup p ((p, v) :: es) = Just v
lookupConsSame p v es = rewrite pathEqRefl p in Refl

||| Filtering out a key that does not occur is the identity. Structural
||| induction on the entry list; the head case splits on `p == k` and the
||| matching branch is discharged by the `lookup … = Nothing` hypothesis.
export
removeAbsentId : (p : Path) -> (es : List (Path, FSEntry)) ->
                 lookup p es = Nothing -> filter (keepIfNotP p) es = es
removeAbsentId p [] prf = Refl
removeAbsentId p ((k, v) :: rest) prf with (p == k) proof eqPK
  removeAbsentId p ((k, v) :: rest) prf | True  = absurd prf
  removeAbsentId p ((k, v) :: rest) prf | False =
    cong ((k, v) ::) (removeAbsentId p rest prf)

||| Core reversibility building block: removing a key immediately after
||| adding it, when the key was absent beforehand, restores the original
||| filesystem exactly (not merely up to `Equiv`). This is what makes
||| mkdir/rmdir and touch/rm honest inverses on their preconditions.
export
removeAddAbsent : (p : Path) -> (e : FSEntry) -> (fs : Filesystem) ->
                  lookup p (entries fs) = Nothing ->
                  removeEntry p (addEntry p e fs) = fs
removeAddAbsent p e (MkFS es) prf =
  rewrite keepSelfFalse p e in cong MkFS (removeAbsentId p es prf)

||| Querying the entry just added returns exactly that entry.
export
getEntryAfterAdd : (p : Path) -> (e : FSEntry) -> (fs : Filesystem) ->
                   getEntry p (addEntry p e fs) = Just e
getEntryAfterAdd p e (MkFS es) = lookupConsSame p e es

||| The path just added exists.
export
pathExistsAfterAdd : (p : Path) -> (e : FSEntry) -> (fs : Filesystem) ->
                     pathExists p (addEntry p e fs) = True
pathExistsAfterAdd p e (MkFS es) = rewrite lookupConsSame p e es in Refl

||| Adding a `File` entry makes the path a file.
export
isFileAfterAddFile : (p : Path) -> (c : FileContent) -> (fs : Filesystem) ->
                     isFile p (addEntry p (File c) fs) = True
isFileAfterAddFile p c (MkFS es) = rewrite lookupConsSame p (File c) es in Refl

||| Adding a `Dir` entry makes the path a directory.
export
isDirAfterAddDir : (p : Path) -> (fs : Filesystem) ->
                   isDirectory p (addEntry p Dir fs) = True
isDirAfterAddDir p (MkFS es) = rewrite lookupConsSame p Dir es in Refl

||| A non-existent path has no `lookup` result — bridges the boolean
||| `pathExists … = False` precondition to the propositional
||| `lookup … = Nothing` form the reversibility lemmas consume.
export
notExistsLookupNothing : (p : Path) -> (fs : Filesystem) ->
                         pathExists p fs = False ->
                         lookup p (entries fs) = Nothing
notExistsLookupNothing p (MkFS es) prf with (lookup p es)
  notExistsLookupNothing p (MkFS es) prf | Nothing  = Refl
  notExistsLookupNothing p (MkFS es) prf | (Just x) = absurd prf

||| `updateEntry p e` depends only on the `keepIfNotP p` projection of the
||| entries (the new value `e` is fixed): two filesystems agreeing off `p`
||| land on the same state after an update at `p`. The `updateEntry`
||| analogue of `removeEntryDeterminedByFilter`, and the structural basis
||| for RMO's `overwriteIrreversible` (overwrite discards whatever was at
||| `p`, so distinct originals collapse — information loss).
export
updateEntryDeterminedByFilter :
  (p : Path) -> (e : FSEntry) -> (fs1, fs2 : Filesystem) ->
  filter (keepIfNotP p) (entries fs1)
    = filter (keepIfNotP p) (entries fs2) ->
  updateEntry p e fs1 = updateEntry p e fs2
updateEntryDeterminedByFilter p e fs1 fs2 agree =
  cong (addEntry p e) (removeEntryDeterminedByFilter p fs1 fs2 agree)

||| `filter` is idempotent: filtering an already-filtered list changes
||| nothing (every survivor already satisfies the predicate).
export
filterIdem : (f : a -> Bool) -> (xs : List a) ->
             filter f (filter f xs) = filter f xs
filterIdem f [] = Refl
filterIdem f (x :: xs) with (f x) proof fx
  filterIdem f (x :: xs) | True  = rewrite fx in cong (x ::) (filterIdem f xs)
  filterIdem f (x :: xs) | False = filterIdem f xs

||| Overwriting collapses: an update at `p` completely supersedes any
||| immediately preceding update at the same `p`. The earlier value is
||| gone — this is the write-write coalescing law.
export
updateOverwrite : (p : Path) -> (e1, e2 : FSEntry) -> (fs : Filesystem) ->
                  updateEntry p e2 (updateEntry p e1 fs) = updateEntry p e2 fs
updateOverwrite p e1 e2 (MkFS es) =
  cong (\t => MkFS ((p, e2) :: t))
       (rewrite keepSelfFalse p e1 in filterIdem (keepIfNotP p) es)

||| Writing the value a filesystem already holds in canonical head
||| position is the identity. `canonical` says `p` sits at the head with
||| value `e` and the tail is `p`-free — exactly the shape left by a prior
||| write of `e` at `p`.
export
updateCanonicalId : (p : Path) -> (e : FSEntry) -> (fs : Filesystem) ->
                    entries fs = (p, e) :: filter (keepIfNotP p) (entries fs) ->
                    updateEntry p e fs = fs
updateCanonicalId p e (MkFS es) canonical = cong MkFS (sym canonical)

||| Removing `p` after adding it on top of a `p`-cleared state is the same
||| as just clearing `p`. The stability law behind undo/redo: redoing a
||| removal (remove ∘ add ∘ remove) lands on the same state as the single
||| removal, with no residual dependence on the intervening add.
export
removeAddRemove : (p : Path) -> (e : FSEntry) -> (fs : Filesystem) ->
                  removeEntry p (addEntry p e (removeEntry p fs))
                    = removeEntry p fs
removeAddRemove p e (MkFS es) =
  cong MkFS (rewrite keepSelfFalse p e in filterIdem (keepIfNotP p) es)

--------------------------------------------------------------------------------
-- Filesystem Equivalence (Q5 option 3: propositional `All` / `Elem`)
--
-- 2026-06-03 migration: the previous `equiv : Filesystem -> Filesystem
-- -> Bool` used `Foldable.all` which does NOT reduce on `(x :: xs)`
-- under Idris2 0.8.0's elaboration — `all p (x :: xs) = (p x && all p
-- xs)` fails by `Refl`. That blocked `equivTrans` and
-- `cnoWriteSameContent`. Replacing with the propositional `All` /
-- `Elem` view from `Data.List.Quantifiers` makes every reasoning step
-- structural and pattern-matchable. Equivalence is now a proof object,
-- not a boolean computation.
--
-- Decidability bridge below for callers that genuinely need `Bool`.
--------------------------------------------------------------------------------

||| Two filesystems are equivalent if every entry of one is an `Elem`
||| of the other and vice versa (set-of-entries equality ignoring
||| order). Stored as two `All`-witnesses — one per direction.
public export
data Equiv : Filesystem -> Filesystem -> Type where
  MkEquiv :
    {0 fs1, fs2 : Filesystem} ->
    All (\e => Elem e (entries fs2)) (entries fs1) ->
    All (\e => Elem e (entries fs1)) (entries fs2) ->
    Equiv fs1 fs2

--------------------------------------------------------------------------------
-- Equivalence laws
--------------------------------------------------------------------------------

||| `mapProperty`-shape helper: weaken each `Elem e xs` witness in an
||| `All`-list to `Elem e (y :: xs)` by `There`.
private
allThere :
  {0 ys : List (Path, FSEntry)} -> {0 y : (Path, FSEntry)} ->
  All (\e => Elem e ys) xs ->
  All (\e => Elem e (y :: ys)) xs
allThere []        = []
allThere (p :: ps) = There p :: allThere ps

||| Reflexivity of equivalence. Structural induction on the entries
||| list: every entry is at `Here`, and the recursive hypothesis weakens
||| via `allThere`. No primitive-eq axioms, no `believe_me`.
export
equivRefl : (fs : Filesystem) -> Equiv fs fs
equivRefl (MkFS [])         = MkEquiv [] []
equivRefl (MkFS (e :: rest)) =
  let MkEquiv fwd bwd = equivRefl (MkFS rest)
  in MkEquiv (Here :: allThere fwd) (Here :: allThere bwd)

||| Symmetry of equivalence. Constructor reorder — the two `All`
||| witnesses just swap. (Replaces the boolean-form `andCommutative`
||| rewrite, which was the same idea expressed via `&&`.)
export
equivSym : Equiv fs1 fs2 -> Equiv fs2 fs1
equivSym (MkEquiv fwd bwd) = MkEquiv bwd fwd

||| Transitivity of equivalence. Each entry of `fs1` has an `Elem`
||| witness in `entries fs2` (via `fwd12`); use that witness to index
||| into `fwd23`, which gives an `Elem` witness in `entries fs3`.
||| `mapProperty` lifts this pointwise step to the whole `All`. The
||| backward direction is symmetric.
|||
||| Closes #119 Cat-B `equivTransProof` cleanly without the foldl
||| destructuring problem that blocked the boolean form.
export
equivTrans : Equiv fs1 fs2 -> Equiv fs2 fs3 -> Equiv fs1 fs3
equivTrans (MkEquiv fwd12 bwd12) (MkEquiv fwd23 bwd23) =
  MkEquiv (mapProperty (\elemIn2 => indexAll elemIn2 fwd23) fwd12)
          (mapProperty (\elemIn1 => indexAll elemIn1 bwd12) bwd23)

||| Every entry of a list is a member of that same list — the `All`/`Elem`
||| reflexivity witness underlying `equivRefl`, exposed as a reusable
||| building block for permutation-style equivalences.
export
allElemSelf : (es : List (Path, FSEntry)) -> All (\e => Elem e es) es
allElemSelf []        = []
allElemSelf (x :: xs) = Here :: allThere (allElemSelf xs)

||| Swapping the first two entries of a filesystem yields an equivalent
||| filesystem. `Equiv` is set-of-entries equality, so reordering the head
||| pair is a no-op — proved purely by reshuffling `Elem` witnesses, with
||| no primitive-equality reasoning. This is the order-independence lemma
||| that makes commuting independent operations an `Equiv` theorem.
export
equivSwapHead : (a, b : (Path, FSEntry)) -> (es : List (Path, FSEntry)) ->
                Equiv (MkFS (a :: b :: es)) (MkFS (b :: a :: es))
equivSwapHead a b es =
  MkEquiv
    (There Here :: Here :: allThere (allThere (allElemSelf es)))
    (There Here :: Here :: allThere (allThere (allElemSelf es)))

||| Two `addEntry`s on top of the same filesystem commute up to `Equiv`.
||| The concrete filesystems differ only in the order of their first two
||| entries, so this is `equivSwapHead` lifted to the `addEntry` interface.
||| Holds unconditionally — even when the two keys coincide — because
||| `Equiv` is order- and multiplicity-tolerant on the shared tail.
export
equivAddSwap : (p1 : Path) -> (e1 : FSEntry) ->
               (p2 : Path) -> (e2 : FSEntry) -> (fs : Filesystem) ->
               Equiv (addEntry p1 e1 (addEntry p2 e2 fs))
                     (addEntry p2 e2 (addEntry p1 e1 fs))
equivAddSwap p1 e1 p2 e2 (MkFS es) = equivSwapHead (p1, e1) (p2, e2) es
