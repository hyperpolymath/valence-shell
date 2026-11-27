{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
{- Valence Shell - journal record framing (Agda)

   The on-disk journal is one file of records. Each record is a *frame*:

       header (fixed width, carries the payload length)
       payload
       checksum of the payload (fixed width)

   This module defines the frame, a decoder, and proves:

   * `step-frame`      a frame at the front of the input is read back exactly;
   * `step-sound`      whatever the decoder accepts is byte-for-byte a frame
                       at the front of the input (nothing is misread);
   * `step-torn`       a frame cut short at any point is rejected;
   * `classify-torn`   and it is classified as torn, never as damaged;
   * `decode-sound`    the accepted records, re-encoded, followed by the
                       rejected tail, are exactly the input;
   * `decode-frames`   a sequence of frames followed by a rejected tail
                       decodes to exactly those records and that tail;
   * `decode-crash`    after a crash that keeps the synced frames and any
                       prefix of the unsynced ones, the decoder returns the
                       synced records followed by a prefix of the unsynced
                       records;
   * `decode-crash-tail`  after such a crash the bytes the decoder rejects
                       are never classified as damaged;
   * `decode-normal`   re-encoding what was accepted gives a clean journal,
                       for any input at all.

   What is assumed, as module parameters (no postulates):

   * the header has a fixed width of at least one byte (`hdr-length`);
   * the checksum has a fixed width (`sum-length`).

   Nothing is assumed about the checksum's strength. The torn-tail results
   need none: truncation is caught by the length in the header. A checksum
   only makes it unlikely that bytes which were never written as a frame are
   accepted as one; `step-sound` states exactly what acceptance means, and it
   holds for any checksum function.

   The header may carry more than the length. The decoder accepts a header
   `h` only if it is canonical, `hdr (unhdr h) ≡ h`. If `hdr n` is the length
   followed by a check of the length, as in the Rust format, that test is the
   header check. With a header that is the bare length it holds for every
   input and says nothing.

   `classify` names what the rejected tail is: `clean`, `torn` (the input
   ends inside a record) or `damaged` (a whole header that is not canonical,
   or a whole record that was still rejected). One direction is proved:
   a crash never yields `damaged` (`classify-torn`, `decode-crash-tail`).
   The other direction is not a theorem and cannot be one: damage that
   leaves a canonical header declaring more bytes than the file holds is
   classified `torn`. How unlikely that is depends on the strength of the
   header check, about which nothing is assumed here.

   `Frameable p` says the header can carry the length of `p`. With a 4-byte
   length field this is `length p < 2^32`; the writer must refuse longer
   payloads.

   Added 2026-11-17 for route-plan Phase C (journal redesign), step C1.
   `classify` and its theorems were added the same day, with the header
   check in the Rust format.
-}

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

module JournalFraming
  (Byte : Set)
  (_≟_ : DecidableEquality Byte)
  (w c : ℕ)                                   -- header width is `suc w`
  (hdr : ℕ → List Byte)
  (hdr-length : ∀ n → length (hdr n) ≡ suc w)
  (unhdr : List Byte → ℕ)
  (sum : List Byte → List Byte)
  (sum-length : ∀ p → length (sum p) ≡ c)
  where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
import Data.Maybe.Base as Maybe
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
import Data.Product.Base as Prod
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties using (≤-trans; m≤n+m; suc-injective)
open import Data.List.Properties
  using (++-assoc; ++-identityʳ; ++-identityʳ-unique; ++-conicalˡ; ++-conicalʳ;
         length-++; ∷-injective; ≡-dec)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Relation.Nullary using (Dec; yes; no; ¬_)

Payload : Set
Payload = List Byte

_≟ᴸ_ : DecidableEquality (List Byte)
_≟ᴸ_ = ≡-dec _≟_

------------------------------------------------------------------------
-- List lemmas

-- Two ways of splitting one list overlap in one of two ways.
++-split : ∀ {A : Set} (xs : List A) {ys} t {u} → t ++ u ≡ xs ++ ys →
           (∃ λ v → xs ≡ t ++ v × u ≡ v ++ ys) ⊎
           (∃ λ v → t ≡ xs ++ v × ys ≡ v ++ u)
++-split []       t       eq = inj₂ (t , refl , sym eq)
++-split (x ∷ xs) []      eq = inj₁ (x ∷ xs , refl , eq)
++-split (x ∷ xs) (y ∷ t) eq with ∷-injective eq
... | y≡x , eq′ with ++-split xs t eq′
...   | inj₁ (v , xs≡ , u≡)  = inj₁ (v , cong₂ _∷_ (sym y≡x) xs≡ , u≡)
...   | inj₂ (v , t≡ , ys≡)  = inj₂ (v , cong₂ _∷_ y≡x t≡ , ys≡)

-- Equal appends with equally long fronts have equal fronts and backs.
++-cancel-length : ∀ {A : Set} (xs xs′ : List A) {ys ys′} →
                   length xs ≡ length xs′ → xs ++ ys ≡ xs′ ++ ys′ →
                   xs ≡ xs′ × ys ≡ ys′
++-cancel-length []       []         _   eq = refl , eq
++-cancel-length []       (_ ∷ _)    ()
++-cancel-length (_ ∷ _)  []         ()
++-cancel-length (x ∷ xs) (x′ ∷ xs′) len eq with ∷-injective eq
... | x≡ , eq′ with ++-cancel-length xs xs′ (suc-injective len) eq′
...   | xs≡ , ys≡ = cong₂ _∷_ x≡ xs≡ , ys≡

------------------------------------------------------------------------
-- Taking exactly n bytes

splitExact : ℕ → List Byte → Maybe (List Byte × List Byte)
splitExact zero    bs       = just ([] , bs)
splitExact (suc n) []       = nothing
splitExact (suc n) (b ∷ bs) = Maybe.map (Prod.map₁ (b ∷_)) (splitExact n bs)

splitExact-++ : ∀ xs ys → splitExact (length xs) (xs ++ ys) ≡ just (xs , ys)
splitExact-++ []       ys = refl
splitExact-++ (x ∷ xs) ys rewrite splitExact-++ xs ys = refl

splitExact-len : ∀ {n} xs ys → length xs ≡ n →
                 splitExact n (xs ++ ys) ≡ just (xs , ys)
splitExact-len xs ys refl = splitExact-++ xs ys

splitExact-sound : ∀ n bs {xs ys} → splitExact n bs ≡ just (xs , ys) →
                   (xs ++ ys ≡ bs) × (length xs ≡ n)
splitExact-sound zero    bs       refl = refl , refl
splitExact-sound (suc n) (b ∷ bs) eq with splitExact n bs in eq′
splitExact-sound (suc n) (b ∷ bs) refl | just (xs′ , ys′) =
  let ++≡ , len≡ = splitExact-sound n bs eq′ in cong (b ∷_) ++≡ , cong suc len≡

------------------------------------------------------------------------
-- Frames

frame : Payload → List Byte
frame p = hdr (length p) ++ (p ++ sum p)

frames : List Payload → List Byte
frames []       = []
frames (p ∷ ps) = frame p ++ frames ps

-- The header can carry this payload's length.
Frameable : Payload → Set
Frameable p = unhdr (hdr (length p)) ≡ length p

frame-++ : ∀ p rest → frame p ++ rest ≡ hdr (length p) ++ (p ++ (sum p ++ rest))
frame-++ p rest =
  trans (++-assoc (hdr (length p)) (p ++ sum p) rest)
        (cong (hdr (length p) ++_) (++-assoc p (sum p) rest))

frames-++ : ∀ ps qs → frames (ps ++ qs) ≡ frames ps ++ frames qs
frames-++ []       qs = refl
frames-++ (p ∷ ps) qs =
  trans (cong (frame p ++_) (frames-++ ps qs))
        (sym (++-assoc (frame p) (frames ps) (frames qs)))

------------------------------------------------------------------------
-- Reading one frame

guard : ∀ {P : Set} → Dec P → Maybe ⊤
guard (yes _) = just tt
guard (no _)  = nothing

guard-yes : ∀ {P : Set} (d : Dec P) → P → guard d ≡ just tt
guard-yes (yes _) _ = refl
guard-yes (no ¬p) p = ⊥-elim (¬p p)

afterSum : Payload → List Byte × List Byte → Maybe (Payload × List Byte)
afterSum p (s , r) = guard (s ≟ᴸ sum p) >>= λ _ → just (p , r)

afterPayload : List Byte × List Byte → Maybe (Payload × List Byte)
afterPayload (p , r) = splitExact c r >>= afterSum p

afterHeader : List Byte × List Byte → Maybe (Payload × List Byte)
afterHeader (h , r) =
  guard (hdr (unhdr h) ≟ᴸ h) >>= λ _ → splitExact (unhdr h) r >>= afterPayload

-- `just (p , rest)` when the input starts with a well-formed frame carrying
-- `p`; `nothing` otherwise.
step : List Byte → Maybe (Payload × List Byte)
step bs = splitExact (suc w) bs >>= afterHeader

step-frame : ∀ p rest → Frameable p → step (frame p ++ rest) ≡ just (p , rest)
step-frame p rest fr
  rewrite frame-++ p rest
        | splitExact-len (hdr (length p)) (p ++ (sum p ++ rest)) (hdr-length (length p))
        | fr
        | guard-yes (hdr (length p) ≟ᴸ hdr (length p)) refl
        | splitExact-++ p (sum p ++ rest)
        | splitExact-len (sum p) rest (sum-length p)
        | guard-yes (sum p ≟ᴸ sum p) refl
  = refl

step-sound : ∀ bs {p r} → step bs ≡ just (p , r) →
             (frame p ++ r ≡ bs) × Frameable p
step-sound bs eq with splitExact (suc w) bs in e₁
... | just (h , r₁) with hdr (unhdr h) ≟ᴸ h
...   | yes canon with splitExact (unhdr h) r₁ in e₂
...     | just (p′ , r₂) with splitExact c r₂ in e₃
...       | just (s , r₃) with s ≟ᴸ sum p′
step-sound bs refl | just (h , r₁) | yes canon | just (p′ , r₂) | just (s , r₃) | yes s≡ =
  let h++ , _    = splitExact-sound (suc w) bs e₁
      p++ , plen = splitExact-sound (unhdr h) r₁ e₂
      s++ , _    = splitExact-sound c r₂ e₃
      hdr≡ : hdr (length p′) ≡ h
      hdr≡ = trans (cong hdr plen) canon
  in trans (frame-++ p′ r₃)
       (trans (cong₂ _++_ hdr≡
                 (cong (p′ ++_) (trans (cong (_++ r₃) (sym s≡)) s++)))
         (trans (cong (h ++_) p++) h++))
   , trans (cong unhdr hdr≡) (sym plen)

step-[] : step [] ≡ nothing
step-[] = refl

-- A frame cut short is rejected.
step-torn : ∀ p t u → Frameable p → u ≢ [] → t ++ u ≡ frame p → step t ≡ nothing
step-torn p t u fr u≢[] eq with step t in st
... | nothing = refl
... | just (p′ , r) = ⊥-elim (u≢[] (++-conicalʳ r u r++u≡[]))
  where
  sound = step-sound t st
  fr′ : Frameable p′
  fr′ = proj₂ sound

  whole : hdr (length p′) ++ (p′ ++ (sum p′ ++ (r ++ u))) ≡ hdr (length p) ++ (p ++ sum p)
  whole =
    trans (cong (hdr (length p′) ++_)
             (trans (cong (p′ ++_) (sym (++-assoc (sum p′) r u)))
                    (sym (++-assoc p′ (sum p′ ++ r) u))))
      (trans (sym (++-assoc (hdr (length p′)) ((p′ ++ (sum p′ ++ r))) u))
        (trans (cong (_++ u) (sym (frame-++ p′ r)))
          (trans (cong (_++ u) (proj₁ sound)) eq)))

  hdrs = ++-cancel-length (hdr (length p′)) (hdr (length p))
           (trans (hdr-length (length p′)) (sym (hdr-length (length p)))) whole

  len≡ : length p′ ≡ length p
  len≡ = trans (sym fr′) (trans (cong unhdr (proj₁ hdrs)) fr)

  bodies = ++-cancel-length p′ p len≡ (proj₂ hdrs)

  r++u≡[] : r ++ u ≡ []
  r++u≡[] = ++-identityʳ-unique (sum p)
              (sym (trans (cong (λ q → sum q ++ (r ++ u)) (sym (proj₁ bodies)))
                          (proj₂ bodies)))

------------------------------------------------------------------------
-- Reading the whole journal

-- Result: the records accepted, and the bytes left over. The journal is
-- clean exactly when nothing is left over.
Decoded : Set
Decoded = List Payload × List Byte

continue : (List Byte → Decoded) → List Byte → Maybe (Payload × List Byte) → Decoded
continue rec bs nothing        = [] , bs
continue rec bs (just (p , r)) = Prod.map₁ (p ∷_) (rec r)

decodeFuel : ℕ → List Byte → Decoded
decodeFuel zero    bs = [] , bs
decodeFuel (suc k) bs = continue (decodeFuel k) bs (step bs)

decode : List Byte → Decoded
decode bs = decodeFuel (length bs) bs

decodeFuel-sound : ∀ k bs →
  frames (proj₁ (decodeFuel k bs)) ++ proj₂ (decodeFuel k bs) ≡ bs
decodeFuel-sound zero    bs = refl
decodeFuel-sound (suc k) bs with step bs in st
... | nothing      = refl
... | just (p , r) =
  trans (++-assoc (frame p) _ _)
    (trans (cong (frame p ++_) (decodeFuel-sound k r)) (proj₁ (step-sound bs st)))

-- Nothing is misread: the accepted records are, byte for byte, the front of
-- the input.
decode-sound : ∀ bs → frames (proj₁ (decode bs)) ++ proj₂ (decode bs) ≡ bs
decode-sound bs = decodeFuel-sound (length bs) bs

decodeFuel-frameable : ∀ k bs → All Frameable (proj₁ (decodeFuel k bs))
decodeFuel-frameable zero    bs = []
decodeFuel-frameable (suc k) bs with step bs in st
... | nothing      = []
... | just (p , r) = proj₂ (step-sound bs st) ∷ decodeFuel-frameable k r

decode-frameable : ∀ bs → All Frameable (proj₁ (decode bs))
decode-frameable bs = decodeFuel-frameable (length bs) bs

decodeFuel-frames : ∀ ps t → All Frameable ps → step t ≡ nothing →
  ∀ k → length ps ≤ k → decodeFuel k (frames ps ++ t) ≡ (ps , t)
decodeFuel-frames []       t []         st zero    _ = refl
decodeFuel-frames []       t []         st (suc k) _ rewrite st = refl
decodeFuel-frames (p ∷ ps) t (fr ∷ frs) st (suc k) (s≤s le)
  rewrite ++-assoc (frame p) (frames ps) t
        | step-frame p (frames ps ++ t) fr
        | decodeFuel-frames ps t frs st k le
  = refl

frame-longer : ∀ p rest → suc (length rest) ≤ length (frame p ++ rest)
frame-longer p rest = subst (suc (length rest) ≤_) (sym len≡)
                        (s≤s (m≤n+m (length rest) (w + length (p ++ sum p))))
  where
  len≡ : length (frame p ++ rest) ≡ suc (w + length (p ++ sum p)) + length rest
  len≡ = trans (length-++ (frame p))
           (cong (_+ length rest)
             (trans (length-++ (hdr (length p)))
                    (cong (_+ length (p ++ sum p)) (hdr-length (length p)))))

frames-longer : ∀ ps t → length ps ≤ length (frames ps ++ t)
frames-longer []       t = z≤n
frames-longer (p ∷ ps) t =
  subst (suc (length ps) ≤_) (cong length (sym (++-assoc (frame p) (frames ps) t)))
    (≤-trans (s≤s (frames-longer ps t)) (frame-longer p (frames ps ++ t)))

-- Frames followed by a rejected tail decode to exactly those records and
-- that tail.
decode-frames : ∀ ps t → All Frameable ps → step t ≡ nothing →
                decode (frames ps ++ t) ≡ (ps , t)
decode-frames ps t frs st =
  decodeFuel-frames ps t frs st (length (frames ps ++ t)) (frames-longer ps t)

decode-clean : ∀ ps → All Frameable ps → decode (frames ps) ≡ (ps , [])
decode-clean ps frs =
  trans (cong decode (sym (++-identityʳ (frames ps)))) (decode-frames ps [] frs step-[])

-- Re-encoding what was accepted gives a clean journal, whatever the input.
decode-normal : ∀ bs → decode (frames (proj₁ (decode bs))) ≡ (proj₁ (decode bs) , [])
decode-normal bs = decode-clean (proj₁ (decode bs)) (decode-frameable bs)

------------------------------------------------------------------------
-- What the rejected tail is

-- Why the decoder stopped. `clean`: nothing is left. `torn`: the input ends
-- inside a record, and its header, if all of it is there, is canonical.
-- `damaged`: a whole header that is not canonical, or a whole record. The
-- last is damage when the decoder rejected that record, which is the only
-- case `classify` is meant for: the bytes left over by `decode`.
data Tail : Set where
  clean torn damaged : Tail

clean≢damaged : clean ≢ damaged
clean≢damaged ()

torn≢damaged : torn ≢ damaged
torn≢damaged ()

-- The part after the header: is all of it there?
classifyBody : Maybe (List Byte × List Byte) → Tail
classifyBody nothing  = torn
classifyBody (just _) = damaged

whenCanon : ∀ {P : Set} → Dec P → Tail → Tail
whenCanon (yes _) t = t
whenCanon (no _)  _ = damaged

whenCanon-yes : ∀ {P : Set} (d : Dec P) → P → ∀ t → whenCanon d t ≡ t
whenCanon-yes (yes _) _ t = refl
whenCanon-yes (no ¬p) p t = ⊥-elim (¬p p)

classifyHeader : Maybe (List Byte × List Byte) → Tail
classifyHeader nothing        = torn
classifyHeader (just (h , r)) =
  whenCanon (hdr (unhdr h) ≟ᴸ h) (classifyBody (splitExact (unhdr h + c) r))

classify : List Byte → Tail
classify []       = clean
classify (b ∷ bs) = classifyHeader (splitExact (suc w) (b ∷ bs))

classify-∷ : ∀ t → t ≢ [] → classify t ≡ classifyHeader (splitExact (suc w) t)
classify-∷ []      t≢ = ⊥-elim (t≢ refl)
classify-∷ (_ ∷ _) _  = refl

-- A list cannot give as many bytes as a longer list has.
splitExact-short : ∀ xs y ys → splitExact (length (xs ++ y ∷ ys)) xs ≡ nothing
splitExact-short []       y ys = refl
splitExact-short (x ∷ xs) y ys rewrite splitExact-short xs y ys = refl

-- A whole header written by `frame`, followed by a body cut short, is torn.
torn-body : ∀ p v x u → Frameable p → p ++ sum p ≡ v ++ x ∷ u →
            classifyHeader (splitExact (suc w) (hdr (length p) ++ v)) ≡ torn
torn-body p v x u fr body =
  trans (cong classifyHeader (splitExact-len H v (hdr-length (length p))))
    (trans (whenCanon-yes (hdr (unhdr H) ≟ᴸ H) (cong hdr fr)
              (classifyBody (splitExact (unhdr H + c) v)))
      (cong classifyBody
        (trans (cong (λ n → splitExact n v) len≡) (splitExact-short v x u))))
  where
  H = hdr (length p)

  len≡ : unhdr H + c ≡ length (v ++ x ∷ u)
  len≡ = trans (cong (_+ c) fr)
           (trans (cong (length p +_) (sym (sum-length p)))
             (trans (sym (length-++ p)) (cong length body)))

-- An interrupted append is never reported as damage: a frame cut short,
-- with at least one byte kept, is torn.
classify-torn : ∀ p t u → Frameable p → t ≢ [] → u ≢ [] → t ++ u ≡ frame p →
                classify t ≡ torn
classify-torn p t []      fr t≢ u≢ eq = ⊥-elim (u≢ refl)
classify-torn p t (x ∷ u) fr t≢ u≢ eq with ++-split (hdr (length p)) t eq
-- The cut is at the end of the header.
... | inj₁ ([] , H≡ , u≡) =
  trans (classify-∷ t t≢)
    (trans (cong (λ s → classifyHeader (splitExact (suc w) s))
              (trans (sym (++-identityʳ t))
                (trans (sym H≡) (sym (++-identityʳ (hdr (length p)))))))
           (torn-body p [] x u fr (sym u≡)))
-- The cut is inside the header.
... | inj₁ (y ∷ v , H≡ , _) =
  trans (classify-∷ t t≢)
    (cong classifyHeader
      (trans (cong (λ n → splitExact n t)
                (trans (sym (hdr-length (length p))) (cong length H≡)))
             (splitExact-short t y v)))
-- The cut is after the header.
... | inj₂ (v , t≡ , body) =
  trans (classify-∷ t t≢)
    (trans (cong (λ s → classifyHeader (splitExact (suc w) s)) t≡)
           (torn-body p v x u fr body))

-- The same without asking that a byte was kept: a frame cut short at any
-- point is not classified as damage.
classify-cut : ∀ p t u → Frameable p → u ≢ [] → t ++ u ≡ frame p →
               classify t ≢ damaged
classify-cut p []      u fr u≢ eq = clean≢damaged
classify-cut p (b ∷ t) u fr u≢ eq =
  subst (_≢ damaged) (sym (classify-torn p (b ∷ t) u fr (λ ()) u≢ eq)) torn≢damaged

------------------------------------------------------------------------
-- A prefix of a run of frames

-- Any prefix of `frames qs` is some whole frames of `qs` followed by a tail
-- that the decoder rejects (an empty tail, or a frame cut short), and that
-- tail is not classified as damage.
frames-split⁺ : ∀ qs → All Frameable qs → ∀ t u → t ++ u ≡ frames qs →
  ∃ λ qs₁ → ∃ λ qs₂ → ∃ λ t′ →
    (qs₁ ++ qs₂ ≡ qs) × (t ≡ frames qs₁ ++ t′) × (step t′ ≡ nothing)
    × (classify t′ ≢ damaged)
frames-split⁺ [] [] t u eq =
  [] , [] , [] , refl , ++-conicalˡ t u eq , step-[] , clean≢damaged
frames-split⁺ (q ∷ qs) (fr ∷ frs) t u eq with ++-split (frame q) t eq
... | inj₁ ([] , fq≡ , _) =
  (q ∷ []) , qs , [] , refl
  , trans (sym (++-identityʳ t))
      (trans (sym fq≡)
        (sym (trans (++-identityʳ (frame q ++ [])) (++-identityʳ (frame q)))))
  , step-[] , clean≢damaged
... | inj₁ (x ∷ v , fq≡ , _) =
  [] , (q ∷ qs) , t , refl , refl , step-torn q t (x ∷ v) fr (λ ()) (sym fq≡)
  , classify-cut q t (x ∷ v) fr (λ ()) (sym fq≡)
... | inj₂ (v , t≡ , fqs≡) with frames-split⁺ qs frs v u (sym fqs≡)
...   | qs₁ , qs₂ , t′ , split , v≡ , st , cl =
  (q ∷ qs₁) , qs₂ , t′ , cong (q ∷_) split
  , trans t≡ (trans (cong (frame q ++_) v≡) (sym (++-assoc (frame q) (frames qs₁) t′)))
  , st , cl

frames-split : ∀ qs → All Frameable qs → ∀ t u → t ++ u ≡ frames qs →
  ∃ λ qs₁ → ∃ λ qs₂ → ∃ λ t′ →
    (qs₁ ++ qs₂ ≡ qs) × (t ≡ frames qs₁ ++ t′) × (step t′ ≡ nothing)
frames-split qs frs t u eq with frames-split⁺ qs frs t u eq
... | qs₁ , qs₂ , t′ , split , t≡ , st , _ = qs₁ , qs₂ , t′ , split , t≡ , st

-- Crash recovery at the level of records. `es` are the synced records and
-- `qs` the unsynced ones; the surviving file is the synced frames followed
-- by any prefix `t` of the unsynced frames. The decoder returns `es`
-- followed by a prefix `qs₁` of `qs`, and the tail it rejects is not
-- classified as damage.
decode-crash⁺ : ∀ es qs → All Frameable es → All Frameable qs →
  ∀ t u → t ++ u ≡ frames qs →
  ∃ λ qs₁ → ∃ λ qs₂ → ∃ λ t′ →
    (qs₁ ++ qs₂ ≡ qs) × (decode (frames es ++ t) ≡ (es ++ qs₁ , t′))
    × (classify t′ ≢ damaged)
decode-crash⁺ es qs fes fqs t u eq with frames-split⁺ qs fqs t u eq
... | qs₁ , qs₂ , t′ , split , t≡ , st , cl =
  qs₁ , qs₂ , t′ , split
  , trans (cong decode bytes≡)
      (decode-frames (es ++ qs₁) t′
        (All.++⁺ fes (All.++⁻ˡ qs₁ (subst (All Frameable) (sym split) fqs))) st)
  , cl
  where
  bytes≡ : frames es ++ t ≡ frames (es ++ qs₁) ++ t′
  bytes≡ = trans (cong (frames es ++_) t≡)
             (trans (sym (++-assoc (frames es) (frames qs₁) t′))
                    (cong (_++ t′) (sym (frames-++ es qs₁))))

decode-crash : ∀ es qs → All Frameable es → All Frameable qs →
  ∀ t u → t ++ u ≡ frames qs →
  ∃ λ qs₁ → ∃ λ qs₂ → ∃ λ t′ →
    (qs₁ ++ qs₂ ≡ qs) × (decode (frames es ++ t) ≡ (es ++ qs₁ , t′))
decode-crash es qs fes fqs t u eq with decode-crash⁺ es qs fes fqs t u eq
... | qs₁ , qs₂ , t′ , split , dec≡ , _ = qs₁ , qs₂ , t′ , split , dec≡

-- After a crash, what the decoder rejects is never classified as damage.
-- A reader that refuses a damaged journal is therefore never stopped by a
-- crash, as long as the crash keeps a prefix of what was appended.
decode-crash-tail : ∀ es qs → All Frameable es → All Frameable qs →
  ∀ t u → t ++ u ≡ frames qs →
  classify (proj₂ (decode (frames es ++ t))) ≢ damaged
decode-crash-tail es qs fes fqs t u eq with decode-crash⁺ es qs fes fqs t u eq
... | qs₁ , qs₂ , t′ , split , dec≡ , cl =
  subst (λ d → classify (proj₂ d) ≢ damaged) (sym dec≡) cl
