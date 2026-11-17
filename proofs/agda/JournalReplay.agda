{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
{- Valence Shell - journal events and replay (Agda)

   The shell's persisted state is rebuilt by replaying a log of events. This
   module defines the state, the events, and `replay`, and proves:

   * `replay-++`          replaying a log then more events is replaying the
                          longer log;
   * `run-ids`            events other than a snapshot never remove or
                          reorder history: the operation ids before are a
                          prefix of the operation ids after;
   * `rollback-closes`    after `rolledBack` no transaction is open;
   * `rollback-no-live`   after `rolledBack` no operation of the rolled-back
                          transaction is still live (not undone);
   * `recorded-joins`     an operation recorded inside a transaction belongs
                          to it;
   * `snapshot-replay`    a log consisting of one snapshot of a state replays
                          to that state (this is what compaction writes).

   Modelling choices, stated so the Rust code can be held to them:

   * The history is append-only. Undo, redo and rollback never delete an
     entry; undo and rollback mark it, and redo records a new operation.
   * Everything that must survive a restart is an event in the one log,
     including the open transaction and the auxiliary state (`Aux`, for
     example the previous directory). There is no second file.
   * Rollback marks every operation of the open transaction as undone by the
     transaction. On `main` as of 2026-11-17 the Rust code does not do this
     (`begin; touch f; rollback; undo` fails); the code is to follow the
     model.
   * The history size cap is not modelled. It is applied only when the
     journal is compacted, as a change of state outside these theorems.

   `Op` is the operation record (type, path, undo data); only its id matters
   here.

   Added 2026-11-17 for route-plan Phase C (journal redesign), step C1.
-}

open import Data.Nat.Base using (ℕ)

module JournalReplay (Op : Set) (opId : Op → ℕ) (Aux : Set) where

open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.List.Base using (List; []; _∷_; _++_; map; foldl)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.DecPropositional _≟ℕ_ using (_∈?_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- State

record Entry : Set where
  constructor entry
  field
    op       : Op
    undoneBy : Maybe ℕ        -- id of the undo operation or transaction

open Entry public

Live : Entry → Set
Live e = undoneBy e ≡ nothing

record Txn : Set where
  constructor txn
  field
    txnId : ℕ
    ops   : List ℕ            -- ids of the operations recorded inside it

open Txn public

record State : Set where
  constructor state
  field
    history : List Entry
    active  : Maybe Txn       -- the open transaction, if any
    closed  : List ℕ          -- ids of committed transactions
    aux     : Maybe Aux

open State public

empty : State
empty = state [] nothing [] nothing

ids : List Entry → List ℕ
ids = map (λ e → opId (op e))

------------------------------------------------------------------------
-- Events

data Event : Set where
  recorded   : Op → Event           -- an operation was performed
  undone     : ℕ → ℕ → Event        -- target id, id of the undo operation
  begun      : ℕ → Event            -- a transaction was opened
  committed  : Event
  rolledBack : Event
  auxSet     : Maybe Aux → Event
  snapshot   : State → Event        -- the whole state (written by compaction)

Incremental : Event → Set
Incremental (snapshot _) = ⊥
Incremental _            = ⊤

-- Mark an entry as undone when `d` holds. An entry already undone keeps its
-- first mark.
firstMark : ℕ → Maybe ℕ → Maybe ℕ
firstMark by nothing  = just by
firstMark by (just b) = just b

markWhen : ∀ {P : Set} → Dec P → ℕ → Entry → Entry
markWhen (yes _) by e = entry (op e) (firstMark by (undoneBy e))
markWhen (no _)  by e = e

markId : ℕ → ℕ → Entry → Entry
markId target by e = markWhen (opId (op e) ≟ℕ target) by e

markIn : List ℕ → ℕ → Entry → Entry
markIn targets by e = markWhen (opId (op e) ∈? targets) by e

joinTxn : ℕ → Maybe Txn → Maybe Txn
joinTxn i nothing          = nothing
joinTxn i (just (txn t os)) = just (txn t (i ∷ os))

beginTxn : ℕ → Maybe Txn → Maybe Txn
beginTxn t nothing  = just (txn t [])
beginTxn t (just x) = just x          -- already open: the event is ignored

commitTxn : Maybe Txn → List ℕ → List ℕ
commitTxn nothing          cs = cs
commitTxn (just (txn t _)) cs = t ∷ cs

rollbackHistory : Maybe Txn → List Entry → List Entry
rollbackHistory nothing           h = h
rollbackHistory (just (txn t os)) h = map (markIn os t) h

apply : Event → State → State
apply (recorded o)   s = record s { history = history s ++ entry o nothing ∷ []
                                  ; active  = joinTxn (opId o) (active s) }
apply (undone i by)  s = record s { history = map (markId i by) (history s) }
apply (begun t)      s = record s { active = beginTxn t (active s) }
apply committed      s = record s { active = nothing
                                  ; closed = commitTxn (active s) (closed s) }
apply rolledBack     s = record s { history = rollbackHistory (active s) (history s)
                                  ; active  = nothing }
apply (auxSet a)     s = record s { aux = a }
apply (snapshot s′)  _ = s′

run : State → List Event → State
run = foldl (λ s e → apply e s)

replay : List Event → State
replay = run empty

------------------------------------------------------------------------
-- Replay of a longer log

run-++ : ∀ s es fs → run s (es ++ fs) ≡ run (run s es) fs
run-++ s []       fs = refl
run-++ s (e ∷ es) fs = run-++ (apply e s) es fs

replay-++ : ∀ es fs → replay (es ++ fs) ≡ run (replay es) fs
replay-++ = run-++ empty

------------------------------------------------------------------------
-- History is append-only

markWhen-id : ∀ {P : Set} (d : Dec P) by e → opId (op (markWhen d by e)) ≡ opId (op e)
markWhen-id (yes _) by e = refl
markWhen-id (no _)  by e = refl

ids-map : ∀ (f : Entry → Entry) → (∀ e → opId (op (f e)) ≡ opId (op e)) →
          ∀ h → ids (map f h) ≡ ids h
ids-map f same []      = refl
ids-map f same (e ∷ h) rewrite same e | ids-map f same h = refl

-- `xs ⊑ ys`: `xs` is a prefix of `ys`.
_⊑_ : List ℕ → List ℕ → Set
xs ⊑ ys = ∃ λ zs → xs ++ zs ≡ ys

⊑-refl : ∀ {xs} → xs ⊑ xs
⊑-refl {xs} = [] , ++-identityʳ xs

⊑-reflexive : ∀ {xs ys} → xs ≡ ys → xs ⊑ ys
⊑-reflexive {xs} eq = [] , trans (++-identityʳ xs) eq

⊑-trans : ∀ {xs ys zs} → xs ⊑ ys → ys ⊑ zs → xs ⊑ zs
⊑-trans {xs} (as , refl) (bs , refl) = as ++ bs , sym (++-assoc xs as bs)

rollbackHistory-ids : ∀ t h → ids (rollbackHistory t h) ≡ ids h
rollbackHistory-ids nothing           h = refl
rollbackHistory-ids (just (txn t os)) h =
  ids-map (markIn os t) (λ e → markWhen-id (opId (op e) ∈? os) t e) h

apply-ids : ∀ e s → Incremental e → ids (history s) ⊑ ids (history (apply e s))
apply-ids (recorded o)  s _ =
  opId o ∷ [] , sym (map-++ (λ e → opId (op e)) (history s) (entry o nothing ∷ []))
apply-ids (undone i by) s _ =
  ⊑-reflexive (sym (ids-map (markId i by)
                      (λ e → markWhen-id (opId (op e) ≟ℕ i) by e) (history s)))
apply-ids (begun t)     s _ = ⊑-refl
apply-ids committed     s _ = ⊑-refl
apply-ids rolledBack    s _ =
  ⊑-reflexive (sym (rollbackHistory-ids (active s) (history s)))
apply-ids (auxSet a)    s _ = ⊑-refl

-- Events other than a snapshot only ever extend the sequence of operation
-- ids: replaying a longer log yields a history that the shorter log's
-- history is a prefix of.
run-ids : ∀ s fs → All Incremental fs → ids (history s) ⊑ ids (history (run s fs))
run-ids s []       []         = ⊑-refl
run-ids s (e ∷ fs) (inc ∷ incs) =
  ⊑-trans (apply-ids e s inc) (run-ids (apply e s) fs incs)

------------------------------------------------------------------------
-- Transactions

recorded-joins : ∀ o s t os → active s ≡ just (txn t os) →
  ∃ λ os′ → active (apply (recorded o) s) ≡ just (txn t os′) × opId o ∈ os′
recorded-joins o s t os eq rewrite eq = opId o ∷ os , refl , here refl

rollback-closes : ∀ s → active (apply rolledBack s) ≡ nothing
rollback-closes s = refl

firstMark-just : ∀ by m → ¬ (firstMark by m ≡ nothing)
firstMark-just by nothing  ()
firstMark-just by (just _) ()

markWhen-live : ∀ {P : Set} (d : Dec P) by e → Live (markWhen d by e) → ¬ P
markWhen-live (yes _) by e live _ = firstMark-just by (undoneBy e) live
markWhen-live (no ¬p) by e _      = ¬p

markIn-no-live : ∀ os t h →
  All (λ e → Live e → ¬ (opId (op e) ∈ os)) (map (markIn os t) h)
markIn-no-live os t []      = []
markIn-no-live os t (e ∷ h) =
  (λ live → subst (λ i → ¬ (i ∈ os))
              (sym (markWhen-id (opId (op e) ∈? os) t e))
              (markWhen-live (opId (op e) ∈? os) t e live))
  ∷ markIn-no-live os t h

-- After a rollback, no operation of the rolled-back transaction is live, so
-- a later `undo` cannot select one.
rollback-no-live : ∀ s t os → active s ≡ just (txn t os) →
  All (λ e → Live e → ¬ (opId (op e) ∈ os)) (history (apply rolledBack s))
rollback-no-live s t os eq rewrite eq = markIn-no-live os t (history s)

------------------------------------------------------------------------
-- Compaction

-- Compaction replaces the log with one snapshot of the current state.
snapshot-replay : ∀ s → replay (snapshot s ∷ []) ≡ s
snapshot-replay s = refl

snapshot-then : ∀ s fs → replay (snapshot s ∷ fs) ≡ run s fs
snapshot-then s fs = refl
