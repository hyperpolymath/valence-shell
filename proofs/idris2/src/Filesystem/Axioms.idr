-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- Primitive-eq reflexivity axioms — Q1-C pilot
--
-- This module is the single registered home for `believe_me`-backed
-- axioms in the Idris2 proof layer. Any other use of `believe_me` in
-- `proofs/idris2/**` is rejected by the CI guard at
-- `.github/scripts/check-idris2-believe-me.sh`.
--
-- The axioms here exist because Idris2 0.8.0 does NOT reduce primitive
-- String / Bits8 `==` on opaque values at type-check time, even though
-- every backend (Chez / Node / Racket) evaluates them correctly at
-- runtime. We bridge this gap with two named, audited axioms — morally
-- identical to Agda's `postulate funext` (already accepted) and Coq's
-- `Axiom is_empty_dir_dec` (already accepted).
--
-- Adding a new axiom requires:
--   1. Adding it to this module (and ONLY this module).
--   2. Adding the matching entry to `.machine_readable/IDRIS2_AXIOMS.a2ml`.
--   3. The CI grep guard verifies the two stay in sync.

module Filesystem.Axioms

import Data.String

%default total

--------------------------------------------------------------------------------
-- Primitive equality reflexivity
--------------------------------------------------------------------------------

||| AXIOM: primitive `String` equality is reflexive on opaque values.
|||
||| Operational justification: every Idris2 backend evaluates
||| `prim__strEq s s` to `True` for any `s : String`. The type-checker
||| cannot see through the primitive on opaque (non-literal) `s`, so
||| we register the fact as a named axiom rather than block every
||| downstream proof on the operational reality.
|||
||| Audit registry: `.machine_readable/IDRIS2_AXIOMS.a2ml` key
||| `axStringEqRefl`.
export
axStringEqRefl : (s : String) -> (s == s) = True
axStringEqRefl _ = believe_me (Refl {x = True})

||| AXIOM: primitive `Bits8` equality is reflexive on opaque values.
|||
||| Operational justification: every Idris2 backend evaluates
||| `prim__eqBits8 b b` to `True` for any `b : Bits8`. As with
||| `axStringEqRefl`, registered here so the type-checker has the
||| fact available without seeing through the primitive.
|||
||| Audit registry: `.machine_readable/IDRIS2_AXIOMS.a2ml` key
||| `axBits8EqRefl`.
export
axBits8EqRefl : (b : Bits8) -> (b == b) = True
axBits8EqRefl _ = believe_me (Refl {x = True})

--------------------------------------------------------------------------------
-- Derived: list reflexivity
--------------------------------------------------------------------------------

||| `List Bits8` (= `FileContent`) equality reflexivity, lifted from
||| `axBits8EqRefl` over the standard `Eq` instance for `List`.
|||
||| Not an axiom — proved structurally. Lives in this module purely
||| to colocate with the axiom it depends on.
export
fileContentEqRefl : (xs : List Bits8) -> (xs == xs) = True
fileContentEqRefl [] = Refl
fileContentEqRefl (x :: rest) =
  rewrite axBits8EqRefl x in
  rewrite fileContentEqRefl rest in
  Refl
