{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
{- Valence Shell - journal model: storage, crashes and recovery (Agda)

   This module joins the record framing (`JournalFraming`) and the event
   replay (`JournalReplay`) through a model of the file the journal lives
   in, and proves what a restart recovers after a crash.

   The file model. A file is the bytes known to be on disk (`durable`) and
   the bytes appended since the last sync (`pending`). `sync` moves pending
   to durable. A crash leaves the durable bytes followed by *some prefix* of
   the pending bytes (`Crash`).

   Main results, for a journal whose synced events are `es` and whose
   appended, not yet synced events are `qs`:

   * `crash-recovery`   after any crash, loading the file succeeds and yields
                        the replay of `es` followed by a prefix of `qs`;
   * `crash-state`      so the recovered state is one the shell actually
                        passed through after its last sync;
   * `synced-survives`  with nothing pending, the recovered state is exactly
                        the replay of `es`;
   * `write-atomic`     with one event pending, the recovered state is the
                        one before that event or the one after it;
   * `compaction-safe`  replacing the file by one snapshot record, when the
                        replacement is all-or-nothing, never changes the
                        recovered state;
   * `append-shape`, `sync-shape`  appending a record then syncing keeps the
                        file in the shape these theorems are about.

   What this does NOT prove. These are statements about the model:

   * The crash model is an assumption about the storage: synced bytes
     survive, and the unsynced part survives as a prefix. It does not cover
     reordered or partly written blocks, or stale bytes in the unsynced
     region. For arbitrary file contents only `JournalFraming.decode-sound`
     and `decode-normal` apply: what is accepted is byte for byte a run of
     well-formed frames at the front of the file. Bytes that were never
     written as a frame but carry a matching checksum would be accepted.
   * `compaction-safe` assumes the replacement is all-or-nothing (write a
     new file, sync it, rename it over the old one, sync the directory).
   * The Rust code is not derived from this model. The link is the storage
     interface in the Rust code and the crash-point harness
     (`impl/rust-cli/tests/journal_crash_tests.rs`), which is test evidence.

   `enc`/`dec` are the event serialisation (JSON in the Rust code); the only
   property used is that decoding an encoded event gives it back.

   Added 2026-11-17 for route-plan Phase C (journal redesign), step C1.
-}

open import Data.Nat.Base using (ℕ; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

import JournalFraming
import JournalReplay

module JournalModel
  -- framing
  (Byte : Set)
  (_≟_ : DecidableEquality Byte)
  (w c : ℕ)
  (hdr : ℕ → List Byte)
  (hdr-length : ∀ n → length (hdr n) ≡ suc w)
  (unhdr : List Byte → ℕ)
  (sum : List Byte → List Byte)
  (sum-length : ∀ p → length (sum p) ≡ c)
  -- events
  (Op : Set) (opId : Op → ℕ) (Aux : Set)
  -- serialisation
  (enc : JournalReplay.Event Op opId Aux → List Byte)
  (dec : List Byte → Maybe (JournalReplay.Event Op opId Aux))
  (dec-enc : ∀ e → dec (enc e) ≡ just e)
  where

open JournalFraming Byte _≟_ w c hdr hdr-length unhdr sum sum-length public
open JournalReplay Op opId Aux public

import Data.Maybe.Base as Maybe
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Properties
  using (++-identityʳ; ++-conicalˡ; map-++; ∷-injective)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

------------------------------------------------------------------------
-- The file

record File : Set where
  constructor file
  field
    durable : List Byte      -- on disk
    pending : List Byte      -- appended since the last sync

open File public

append : List Byte → File → File
append bs f = file (durable f) (pending f ++ bs)

sync : File → File
sync f = file (durable f ++ pending f) []

-- What a crash can leave: the durable bytes and a prefix of the pending
-- bytes.
data Crash (f : File) : List Byte → Set where
  crashed : ∀ t u → pending f ≡ t ++ u → Crash f (durable f ++ t)

------------------------------------------------------------------------
-- The journal in the file

log : List Event → List Byte
log es = frames (map enc es)

-- The events can be framed (each serialised event fits the length field).
Fits : List Event → Set
Fits es = All Frameable (map enc es)

journal : List Event → List Event → File
journal es qs = file (log es) (log qs)

log-++ : ∀ es qs → log (es ++ qs) ≡ log es ++ log qs
log-++ es qs = trans (cong frames (map-++ enc es qs)) (frames-++ (map enc es) (map enc qs))

-- Writing one event appends its frame.
append-shape : ∀ es qs e →
  append (frame (enc e)) (journal es qs) ≡ journal es (qs ++ e ∷ [])
append-shape es qs e =
  cong (file (log es))
    (sym (trans (log-++ qs (e ∷ []))
                (cong (log qs ++_) (++-identityʳ (frame (enc e))))))

sync-shape : ∀ es qs → sync (journal es qs) ≡ journal (es ++ qs) []
sync-shape es qs = cong (λ d → file d []) (sym (log-++ es qs))

------------------------------------------------------------------------
-- Loading

consM : ∀ {A : Set} → Maybe A → Maybe (List A) → Maybe (List A)
consM (just x) (just xs) = just (x ∷ xs)
consM (just _) nothing   = nothing
consM nothing  _         = nothing

-- Every accepted record must parse; one that does not is an error, never
-- skipped.
decodeAll : List Payload → Maybe (List Event)
decodeAll []       = just []
decodeAll (p ∷ ps) = consM (dec p) (decodeAll ps)

decodeAll-enc : ∀ es → decodeAll (map enc es) ≡ just es
decodeAll-enc []       = refl
decodeAll-enc (e ∷ es) rewrite dec-enc e | decodeAll-enc es = refl

-- The state recovered from a file's bytes, or `nothing` if a record does
-- not parse.
load : List Byte → Maybe State
load bs = Maybe.map replay (decodeAll (proj₁ (decode bs)))

-- The bytes the loader did not accept. The writer truncates the file to the
-- accepted part before appending again (`JournalFraming.decode-normal`).
discarded : List Byte → List Byte
discarded bs = proj₂ (decode bs)

------------------------------------------------------------------------
-- Crash recovery

map-split : ∀ (ps₁ : List Payload) {ps₂} (xs : List Event) → ps₁ ++ ps₂ ≡ map enc xs →
  ∃ λ xs₁ → ∃ λ xs₂ → (xs₁ ++ xs₂ ≡ xs) × (ps₁ ≡ map enc xs₁)
map-split []        xs       eq = [] , xs , refl , refl
map-split (p ∷ ps₁) (x ∷ xs) eq with ∷-injective eq
... | p≡ , eq′ with map-split ps₁ xs eq′
...   | xs₁ , xs₂ , split , ps₁≡ =
  x ∷ xs₁ , xs₂ , cong (x ∷_) split , cong₂ _∷_ p≡ ps₁≡

crash-recovery : ∀ es qs → Fits es → Fits qs →
  ∀ {bs} → Crash (journal es qs) bs →
  ∃ λ qs₁ → ∃ λ qs₂ → (qs₁ ++ qs₂ ≡ qs) × (load bs ≡ just (replay (es ++ qs₁)))
crash-recovery es qs fes fqs (crashed t u pend)
  with decode-crash (map enc es) (map enc qs) fes fqs t u (sym pend)
... | ps₁ , ps₂ , t′ , psplit , dec≡ with map-split ps₁ qs psplit
...   | qs₁ , qs₂ , split , ps₁≡ =
  qs₁ , qs₂ , split
  , trans (cong (λ d → Maybe.map replay (decodeAll (proj₁ d))) dec≡)
      (trans (cong (λ ps → Maybe.map replay (decodeAll (map enc es ++ ps))) ps₁≡)
        (trans (cong (λ ps → Maybe.map replay (decodeAll ps)) (sym (map-++ enc es qs₁)))
               (cong (Maybe.map replay) (decodeAll-enc (es ++ qs₁)))))

-- The recovered state is one the shell passed through after its last sync.
crash-state : ∀ es qs → Fits es → Fits qs →
  ∀ {bs} → Crash (journal es qs) bs →
  ∃ λ qs₁ → ∃ λ qs₂ → (qs₁ ++ qs₂ ≡ qs) × (load bs ≡ just (run (replay es) qs₁))
crash-state es qs fes fqs cr with crash-recovery es qs fes fqs cr
... | qs₁ , qs₂ , split , ld =
  qs₁ , qs₂ , split , trans ld (cong just (replay-++ es qs₁))

-- With nothing pending, a crash loses nothing.
synced-survives : ∀ es → Fits es →
  ∀ {bs} → Crash (journal es []) bs → load bs ≡ just (replay es)
synced-survives es fes cr with crash-recovery es [] fes [] cr
... | qs₁ , qs₂ , split , ld =
  trans ld (cong (λ q → just (replay q))
                 (trans (cong (es ++_) (++-conicalˡ qs₁ qs₂ split)) (++-identityʳ es)))

-- With one event pending, the recovered state is the one before it or the
-- one after it.
write-atomic : ∀ es q → Fits es → Fits (q ∷ []) →
  ∀ {bs} → Crash (journal es (q ∷ [])) bs →
  (load bs ≡ just (replay es)) ⊎ (load bs ≡ just (replay (es ++ q ∷ [])))
write-atomic es q fes fq cr with crash-recovery es (q ∷ []) fes fq cr
... | [] , _ , _ , ld =
  inj₁ (trans ld (cong (λ x → just (replay x)) (++-identityʳ es)))
... | x ∷ qs₁ , qs₂ , split , ld with ∷-injective split
...   | x≡q , rest =
  inj₂ (trans ld (cong (λ x → just (replay (es ++ x)))
                       (cong₂ _∷_ x≡q (++-conicalˡ qs₁ qs₂ rest))))

------------------------------------------------------------------------
-- Compaction

-- Compaction writes a new file holding one snapshot of the current state
-- and puts it in place of the old one. If a crash leaves either the old
-- file (as any crash of it) or the complete new file, the recovered state
-- is the same.
compacted : List Event → List Byte
compacted es = log (snapshot (replay es) ∷ [])

compaction-safe : ∀ es → Fits es → Fits (snapshot (replay es) ∷ []) →
  ∀ {bs} → Crash (journal es []) bs ⊎ (bs ≡ compacted es) →
  load bs ≡ just (replay es)
compaction-safe es fes fsnap (inj₁ cr)   = synced-survives es fes cr
compaction-safe es fes fsnap (inj₂ refl) =
  trans (cong (λ d → Maybe.map replay (decodeAll (proj₁ d)))
              (decode-clean (map enc (snapshot (replay es) ∷ [])) fsnap))
        (cong (Maybe.map replay) (decodeAll-enc (snapshot (replay es) ∷ [])))
