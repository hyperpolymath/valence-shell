{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
{- Valence Shell - journal model: an instance and worked cases (Agda)

   `JournalModel` is stated over parameters (a byte type, a header, a
   checksum, an event serialisation). If those parameters could not all be
   met at once, its theorems would say nothing. This module builds one
   instance and runs the definitions on concrete data, so that:

   * the parameters are shown to be jointly satisfiable (`dec-enc` included:
     a serialisation of every event, snapshots too, with a proved round
     trip);
   * the decoder and loader are shown to compute (each case below is closed
     by `refl`);
   * the hypotheses of the crash theorems are shown to be inhabited (each
     theorem is applied to a concrete crash).

   The instance is deliberately small: a "byte" is a natural number, the
   header is one cell holding the payload length, and the checksum is one
   cell holding the sum of the payload. It is not the Rust format.

   A second framing instance (`C`) has a header of two cells: the length,
   then a check of the length. It shows what the decoder's canonical-header
   test does once the header carries a check, which is the shape of the Rust
   format: a changed length is damage, even when the changed length runs
   past the end of the input.

   Added 2026-11-17 for route-plan Phase C (journal redesign), step C1.
-}

module JournalWitnesses where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_; length; foldr)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; universal)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
import Data.Maybe.Base as Maybe
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
import Data.Product.Base as Prod
open import Data.Sum.Base using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

import JournalFraming
import JournalReplay
import JournalModel

open JournalReplay ℕ (λ o → o) ℕ

------------------------------------------------------------------------
-- Framing parameters

hdr : ℕ → List ℕ
hdr n = n ∷ []

unhdr : List ℕ → ℕ
unhdr []      = 0
unhdr (n ∷ _) = n

chk : List ℕ → List ℕ
chk p = foldr _+_ 0 p ∷ []

------------------------------------------------------------------------
-- A serialisation of events with a proved round trip

record Codec (A : Set) : Set where
  constructor codec
  field
    put     : A → List ℕ
    get     : List ℕ → Maybe (A × List ℕ)
    get-put : ∀ a rest → get (put a ++ rest) ≡ just (a , rest)

open Codec

getNat : List ℕ → Maybe (ℕ × List ℕ)
getNat []      = nothing
getNat (n ∷ r) = just (n , r)

natC : Codec ℕ
natC = codec (λ n → n ∷ []) getNat (λ _ _ → refl)

module _ {A B : Set} (ca : Codec A) (cb : Codec B) where
  getPair : List ℕ → Maybe ((A × B) × List ℕ)
  getPair bs = get ca bs >>= λ ar → get cb (proj₂ ar) >>= λ br →
               just ((proj₁ ar , proj₁ br) , proj₂ br)

  get-putPair : ∀ ab rest → getPair ((put ca (proj₁ ab) ++ put cb (proj₂ ab)) ++ rest)
                            ≡ just (ab , rest)
  get-putPair (a , b) rest
    rewrite ++-assoc (put ca a) (put cb b) rest
          | get-put ca a (put cb b ++ rest)
          | get-put cb b rest
    = refl

  pairC : Codec (A × B)
  pairC = codec (λ ab → put ca (proj₁ ab) ++ put cb (proj₂ ab)) getPair get-putPair

module _ {A : Set} (ca : Codec A) where
  putMaybe : Maybe A → List ℕ
  putMaybe nothing  = 0 ∷ []
  putMaybe (just a) = 1 ∷ put ca a

  getMaybe : List ℕ → Maybe (Maybe A × List ℕ)
  getMaybe (0 ∷ r) = just (nothing , r)
  getMaybe (1 ∷ r) = Maybe.map (Prod.map₁ just) (get ca r)
  getMaybe _       = nothing

  get-putMaybe : ∀ m rest → getMaybe (putMaybe m ++ rest) ≡ just (m , rest)
  get-putMaybe nothing  rest = refl
  get-putMaybe (just a) rest rewrite get-put ca a rest = refl

  maybeC : Codec (Maybe A)
  maybeC = codec putMaybe getMaybe get-putMaybe

  puts : List A → List ℕ
  puts []       = []
  puts (x ∷ xs) = put ca x ++ puts xs

  gets : ℕ → List ℕ → Maybe (List A × List ℕ)
  gets zero    r = just ([] , r)
  gets (suc n) r = get ca r >>= λ xr → gets n (proj₂ xr) >>= λ xsr →
                   just (proj₁ xr ∷ proj₁ xsr , proj₂ xsr)

  gets-puts : ∀ xs rest → gets (length xs) (puts xs ++ rest) ≡ just (xs , rest)
  gets-puts []       rest = refl
  gets-puts (x ∷ xs) rest
    rewrite ++-assoc (put ca x) (puts xs) rest
          | get-put ca x (puts xs ++ rest)
          | gets-puts xs rest
    = refl

  getList : List ℕ → Maybe (List A × List ℕ)
  getList []      = nothing
  getList (n ∷ r) = gets n r

  listC : Codec (List A)
  listC = codec (λ xs → length xs ∷ puts xs) getList gets-puts

module _ {A B : Set} (f : A → B) (g : B → A) (fg : ∀ b → f (g b) ≡ b) (ca : Codec A) where
  get-putIso : ∀ b rest → Maybe.map (Prod.map₁ f) (get ca (put ca (g b) ++ rest)) ≡ just (b , rest)
  get-putIso b rest rewrite get-put ca (g b) rest | fg b = refl

  isoC : Codec B
  isoC = codec (λ b → put ca (g b)) (λ bs → Maybe.map (Prod.map₁ f) (get ca bs)) get-putIso

entryC : Codec Entry
entryC = isoC (λ p → entry (proj₁ p) (proj₂ p)) (λ e → op e , undoneBy e) (λ _ → refl)
              (pairC natC (maybeC natC))

txnC : Codec Txn
txnC = isoC (λ p → txn (proj₁ p) (proj₂ p)) (λ t → txnId t , ops t) (λ _ → refl)
            (pairC natC (listC natC))

stateC : Codec State
stateC = isoC (λ p → state (proj₁ p) (proj₁ (proj₂ p))
                           (proj₁ (proj₂ (proj₂ p))) (proj₂ (proj₂ (proj₂ p))))
              (λ s → history s , active s , closed s , aux s) (λ _ → refl)
              (pairC (listC entryC)
                (pairC (maybeC txnC) (pairC (listC natC) (maybeC natC))))

-- A parse that must use up its whole input.
whole : ∀ {A : Set} → Maybe (A × List ℕ) → Maybe A
whole (just (a , [])) = just a
whole (just (_ , _ ∷ _)) = nothing
whole nothing = nothing

whole-put : ∀ {A : Set} (ca : Codec A) a → whole (get ca (put ca a)) ≡ just a
whole-put ca a =
  trans (cong (λ bs → whole (get ca bs)) (sym (++-identityʳ (put ca a))))
        (cong whole (get-put ca a []))

enc : Event → List ℕ
enc (recorded n o) = 0 ∷ n ∷ o ∷ []
enc (undone i by)  = 1 ∷ i ∷ by ∷ []
enc (begun t)      = 2 ∷ t ∷ []
enc committed      = 3 ∷ []
enc rolledBack     = 4 ∷ []
enc (auxSet a)     = 5 ∷ put (maybeC natC) a
enc (snapshot s)   = 6 ∷ put stateC s

dec : List ℕ → Maybe Event
dec (0 ∷ n ∷ o ∷ [])  = just (recorded n o)
dec (1 ∷ i ∷ by ∷ []) = just (undone i by)
dec (2 ∷ t ∷ [])      = just (begun t)
dec (3 ∷ [])          = just committed
dec (4 ∷ [])          = just rolledBack
dec (5 ∷ r)           = Maybe.map auxSet (whole (get (maybeC natC) r))
dec (6 ∷ r)           = Maybe.map snapshot (whole (get stateC r))
dec _                 = nothing

dec-enc : ∀ e → dec (enc e) ≡ just e
dec-enc (recorded n o) = refl
dec-enc (undone i by) = refl
dec-enc (begun t)     = refl
dec-enc committed     = refl
dec-enc rolledBack    = refl
dec-enc (auxSet a)    = cong (Maybe.map auxSet) (whole-put (maybeC natC) a)
dec-enc (snapshot s)  = cong (Maybe.map snapshot) (whole-put stateC s)

------------------------------------------------------------------------
-- The instance

module M = JournalModel ℕ _≟_ 0 1 hdr (λ _ → refl) unhdr chk (λ _ → refl)
                        ℕ (λ o → o) ℕ enc dec dec-enc

-- In this instance every payload can be framed.
fits : ∀ es → M.Fits es
fits es = universal (λ _ → refl) _

------------------------------------------------------------------------
-- Framing: worked cases

-- A frame is length, payload, sum.
frame-example : M.frame (5 ∷ 6 ∷ []) ≡ 2 ∷ 5 ∷ 6 ∷ 11 ∷ []
frame-example = refl

-- Two frames decode to two records, nothing left over.
decode-example :
  M.decode (2 ∷ 5 ∷ 6 ∷ 11 ∷ 0 ∷ 0 ∷ []) ≡ ((5 ∷ 6 ∷ []) ∷ [] ∷ [] , [])
decode-example = refl

-- The second frame cut short at each point: the first record is kept, and
-- the cut bytes are reported as left over.
torn-header-only : M.decode (1 ∷ 9 ∷ 9 ∷ 2 ∷ []) ≡ ((9 ∷ []) ∷ [] , 2 ∷ [])
torn-header-only = refl

torn-in-payload : M.decode (1 ∷ 9 ∷ 9 ∷ 2 ∷ 5 ∷ []) ≡ ((9 ∷ []) ∷ [] , 2 ∷ 5 ∷ [])
torn-in-payload = refl

torn-before-sum : M.decode (1 ∷ 9 ∷ 9 ∷ 2 ∷ 5 ∷ 6 ∷ []) ≡ ((9 ∷ []) ∷ [] , 2 ∷ 5 ∷ 6 ∷ [])
torn-before-sum = refl

-- A wrong checksum: the record is rejected, and so is everything after it.
bad-sum : M.decode (1 ∷ 9 ∷ 9 ∷ 2 ∷ 5 ∷ 6 ∷ 12 ∷ 0 ∷ 0 ∷ [])
          ≡ ((9 ∷ []) ∷ [] , 2 ∷ 5 ∷ 6 ∷ 12 ∷ 0 ∷ 0 ∷ [])
bad-sum = refl

------------------------------------------------------------------------
-- The rejected tail: worked cases

-- The tails of the four cases above. A record cut short is torn; a whole
-- record with a wrong checksum is damaged.
torn-header-only-tail : M.classify (2 ∷ []) ≡ M.torn
torn-header-only-tail = refl

torn-before-sum-tail : M.classify (2 ∷ 5 ∷ 6 ∷ []) ≡ M.torn
torn-before-sum-tail = refl

bad-sum-tail : M.classify (2 ∷ 5 ∷ 6 ∷ 12 ∷ 0 ∷ 0 ∷ []) ≡ M.damaged
bad-sum-tail = refl

clean-tail : M.classify [] ≡ M.clean
clean-tail = refl

-- With a header that is the bare length, a changed length that runs past
-- the end of the input cannot be told from a record cut short. The frame
-- of 5 ∷ 6 ∷ [] with its length changed from 2 to 9:
changed-length-looks-torn : M.classify (9 ∷ 5 ∷ 6 ∷ 11 ∷ []) ≡ M.torn
changed-length-looks-torn = refl

------------------------------------------------------------------------
-- A header that carries a check of the length

-- The header is the length followed by a check cell. The check here is the
-- successor of the length; the Rust format uses part of a hash.
hdrC : ℕ → List ℕ
hdrC n = n ∷ suc n ∷ []

module C = JournalFraming ℕ _≟_ 1 1 hdrC (λ _ → refl) unhdr chk (λ _ → refl)

-- Every payload can be framed.
fitsC : ∀ p → C.Frameable p
fitsC p = refl

-- A frame is length, check of the length, payload, sum.
frameC-example : C.frame (5 ∷ 6 ∷ []) ≡ 2 ∷ 3 ∷ 5 ∷ 6 ∷ 11 ∷ []
frameC-example = refl

decodeC-example : C.decode (2 ∷ 3 ∷ 5 ∷ 6 ∷ 11 ∷ 0 ∷ 1 ∷ 0 ∷ [])
                  ≡ ((5 ∷ 6 ∷ []) ∷ [] ∷ [] , [])
decodeC-example = refl

-- The same change as above, length 2 to 9 with the check cell untouched.
-- The header is no longer canonical, so this is damage. Nothing is
-- accepted, and the record after it is not dropped as if it were torn.
changed-length-is-damage :
  C.classify (9 ∷ 3 ∷ 5 ∷ 6 ∷ 11 ∷ 0 ∷ 1 ∷ 0 ∷ []) ≡ C.damaged
changed-length-is-damage = refl

changed-length-accepts-nothing :
  C.decode (9 ∷ 3 ∷ 5 ∷ 6 ∷ 11 ∷ 0 ∷ 1 ∷ 0 ∷ [])
  ≡ ([] , 9 ∷ 3 ∷ 5 ∷ 6 ∷ 11 ∷ 0 ∷ 1 ∷ 0 ∷ [])
changed-length-accepts-nothing = refl

-- A changed check cell is damage too.
changed-check-is-damage : C.classify (2 ∷ 4 ∷ 5 ∷ 6 ∷ 11 ∷ []) ≡ C.damaged
changed-check-is-damage = refl

-- A record cut short is still torn, at every cut: inside the header, at
-- its end, inside the payload, before the sum.
cut-in-header : C.classify (2 ∷ []) ≡ C.torn
cut-in-header = refl

cut-after-header : C.classify (2 ∷ 3 ∷ []) ≡ C.torn
cut-after-header = refl

cut-in-payload : C.classify (2 ∷ 3 ∷ 5 ∷ []) ≡ C.torn
cut-in-payload = refl

cut-before-sum : C.classify (2 ∷ 3 ∷ 5 ∷ 6 ∷ []) ≡ C.torn
cut-before-sum = refl

-- The theorem applies: the hypotheses of `classify-torn` are inhabited.
classify-torn-applies : C.classify (2 ∷ 3 ∷ 5 ∷ []) ≡ C.torn
classify-torn-applies =
  C.classify-torn (5 ∷ 6 ∷ []) (2 ∷ 3 ∷ 5 ∷ []) (6 ∷ 11 ∷ []) (fitsC (5 ∷ 6 ∷ []))
    (λ ()) (λ ()) refl

-- What is not caught: damage that leaves a canonical header declaring more
-- than the input holds. Length and check cell changed together, 2 ∷ 3 to
-- 9 ∷ 10. This is the blind spot of any header check, and how unlikely it
-- is depends on the check's strength.
changed-header-with-matching-check-looks-torn :
  C.classify (9 ∷ 10 ∷ 5 ∷ 6 ∷ 11 ∷ []) ≡ C.torn
changed-header-with-matching-check-looks-torn = refl

------------------------------------------------------------------------
-- Replay: worked cases

-- Rollback marks the operations it reverses and closes the transaction, so
-- nothing is left for a later `undo` to select.
session : List Event
session = begun 1 ∷ recorded 0 7 ∷ recorded 0 8 ∷ rolledBack ∷ []

rollback-example :
  replay session ≡ state (entry 7 (just 1) ∷ entry 8 (just 1) ∷ []) nothing [] nothing
rollback-example = refl

-- Commit leaves the operations live and records the transaction.
commit-example :
  replay (begun 1 ∷ recorded 0 7 ∷ committed ∷ [])
  ≡ state (entry 7 nothing ∷ []) nothing (1 ∷ []) nothing
commit-example = refl

-- An undo mark, then a redo recorded as a new operation.
undo-redo-example :
  replay (recorded 0 7 ∷ undone 7 8 ∷ recorded 0 9 ∷ [])
  ≡ state (entry 7 (just 8) ∷ entry 9 nothing ∷ []) nothing [] nothing
undo-redo-example = refl

-- A record at the history cap drops the oldest entry in the same event.
trim-example :
  replay (recorded 0 7 ∷ recorded 0 8 ∷ recorded 1 9 ∷ [])
  ≡ state (entry 8 nothing ∷ entry 9 nothing ∷ []) nothing [] nothing
trim-example = refl

------------------------------------------------------------------------
-- Crashes: worked cases and applied theorems

synced : List Event
synced = begun 1 ∷ recorded 0 7 ∷ []

-- The synced part of the file.
synced-bytes : M.log synced ≡ 2 ∷ 2 ∷ 1 ∷ 3 ∷ 3 ∷ 0 ∷ 0 ∷ 7 ∷ 7 ∷ []
synced-bytes = refl

-- `rolledBack` is appended but not yet synced; its frame is 1 ∷ 4 ∷ 4 ∷ [].
-- A crash keeps one cell of it. Loading gives the state before it.
crash-mid-record : M.load (M.log synced ++ 1 ∷ []) ≡ just (replay synced)
crash-mid-record = refl

-- A crash keeps all of it. Loading gives the state after it.
crash-after-record :
  M.load (M.log synced ++ 1 ∷ 4 ∷ 4 ∷ []) ≡ just (replay (synced ++ rolledBack ∷ []))
crash-after-record = refl

a-crash : M.Crash (M.journal synced (rolledBack ∷ [])) (M.log synced ++ 1 ∷ 4 ∷ [])
a-crash = M.crashed (1 ∷ 4 ∷ []) (4 ∷ []) refl

-- The theorems apply to it: their hypotheses are inhabited.
write-atomic-applies :
  (M.load (M.log synced ++ 1 ∷ 4 ∷ []) ≡ just (replay synced))
  ⊎ (M.load (M.log synced ++ 1 ∷ 4 ∷ []) ≡ just (replay (synced ++ rolledBack ∷ [])))
write-atomic-applies =
  M.write-atomic synced rolledBack (fits synced) (fits (rolledBack ∷ [])) a-crash

crash-recovery-applies :
  ∃ λ qs₁ → ∃ λ qs₂ → (qs₁ ++ qs₂ ≡ rolledBack ∷ [])
    × (M.load (M.log synced ++ 1 ∷ 4 ∷ []) ≡ just (replay (synced ++ qs₁)))
crash-recovery-applies =
  M.crash-recovery synced (rolledBack ∷ []) (fits synced) (fits (rolledBack ∷ [])) a-crash

-- What the loader leaves over after that crash is not classified as damage.
crash-tail-applies :
  M.classify (M.discarded (M.log synced ++ 1 ∷ 4 ∷ [])) ≢ M.damaged
crash-tail-applies =
  M.crash-tail synced (rolledBack ∷ []) (fits synced) (fits (rolledBack ∷ [])) a-crash

crash-tail-example : M.classify (M.discarded (M.log synced ++ 1 ∷ 4 ∷ [])) ≡ M.torn
crash-tail-example = refl

-- Compaction: the snapshot record alone loads to the same state.
compaction-example : M.load (M.compacted synced) ≡ just (replay synced)
compaction-example = refl

compaction-applies : M.load (M.compacted synced) ≡ just (replay synced)
compaction-applies =
  M.compaction-safe synced (fits synced) (fits (snapshot (replay synced) ∷ []))
    (inj₂ refl)

-- A record that does not parse is an error, not a skipped line: tag 9 is no
-- event, and its frame is well formed.
unknown-record : M.load (1 ∷ 9 ∷ 9 ∷ []) ≡ nothing
unknown-record = refl
