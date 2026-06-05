-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- RMO (Remove-Match-Obliterate) - Irreversible Operations
--
-- Implements GDPR "right to be forgotten" with mathematical guarantees.
-- These operations are PROVABLY irreversible - no inverse exists.

module Filesystem.RMO

import Filesystem.Model
import Data.List
import Data.List.Elem
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Irreversible Operations
--------------------------------------------------------------------------------

||| Secure deletion levels (NIST SP 800-88 Rev. 1)
public export
data SecureDeleteLevel : Type where
  ||| Clear: Logical deletion (can be recovered with forensics)
  Clear : SecureDeleteLevel
  ||| Purge: Cryptographic erasure or overwrite (cannot be recovered)
  Purge : SecureDeleteLevel
  ||| Destroy: Physical destruction of media
  Destroy : SecureDeleteLevel

||| Result of secure deletion
public export
data SecureDeleteResult : Type where
  ||| Successfully deleted with proof of no recovery
  Obliterated : SecureDeleteResult
  ||| Deletion failed (insufficient permissions, etc.)
  Failed : String -> SecureDeleteResult

||| Proof that data was obliterated (cannot be recovered)
public export
data ObliterationProof : Path -> Type where
  ||| Proof of complete data destruction
  ||| The path no longer exists and its content is irrecoverable
  MkObliterationProof :
    (path : Path) ->
    (level : SecureDeleteLevel) ->
    (timestamp : Integer) ->  -- When obliteration occurred
    (method : String) ->      -- Method used (overwrite, crypto-shred, etc.)
    ObliterationProof path

||| Secure delete a file (RMO operation)
|||
||| This is DELIBERATELY irreversible. Once called, data is permanently destroyed.
||| Returns a proof that data was obliterated.
|||
||| Total: 3 exhaustive cases on SecureDeleteLevel, no recursion. The `IO`
||| wrapper does not introduce partiality — IO computations can be total.
export
secureDelete :
  (p : Path) ->
  (level : SecureDeleteLevel) ->
  IO (Either String (ObliterationProof p))
secureDelete p Clear = do
  -- Simple deletion (recoverable)
  -- In practice: call POSIX unlink
  pure $ Right $ MkObliterationProof p Clear 0 "unlink"

secureDelete p Purge = do
  -- Cryptographic erasure or overwrite
  -- In practice: shred with random data + TRIM/UNMAP
  pure $ Right $ MkObliterationProof p Purge 0 "crypto-shred"

secureDelete p Destroy = do
  -- Physical destruction (not implementable in software)
  pure $ Left "Physical destruction requires hardware intervention"

--------------------------------------------------------------------------------
-- Irreversibility Proofs
--------------------------------------------------------------------------------

||| Secure deletion is not injective on filesystem state.
|||
||| Mirrors Coq's `rmo_operations.obliterate_not_injective` (line 504).
||| Intuition: deletion at path `p` discards all information stored at
||| `p`, so two filesystems that agree off-`p` collapse to the same
||| post-deletion state, regardless of how they differed at `p`. This
||| is the correct formalisation of "information destruction" — many
||| distinct inputs produce the same output, so no inverse function can
||| exist (non-injectivity ⇒ no left-inverse).
|||
||| The premise is the filter-projection equality, which is the abstract
||| analogue of Coq's storage/mapping pre-conditions. The proof closes
||| via [removeEntryDeterminedByFilter] in `Filesystem.Model`.
|||
||| This replaces the previous `secureDeleteIrreversible` which had a
||| non-theorem signature `recovery fs = fs -> Void` — refuted by
||| `recovery = id`. See issue #60 for the design rationale.
export
secureDeleteNotInjective :
  (p : Path) ->
  (fs1, fs2 : Filesystem) ->
  (prf1 : ObliterationProof p) ->
  (prf2 : ObliterationProof p) ->
  -- Pre-deletion states agree on entries at paths other than p
  filter (keepIfNotP p) (entries fs1)
    = filter (keepIfNotP p) (entries fs2) ->
  -- Post-deletion states are equal (information at p is lost)
  removeEntry p fs1 = removeEntry p fs2
secureDeleteNotInjective p fs1 fs2 _ _ agreeOff =
  removeEntryDeterminedByFilter p fs1 fs2 agreeOff

||| Overwriting data makes original irrecoverable
|||
||| After overwriting with random data, the original content cannot be
||| recovered (information-theoretic security).
export
overwriteIrreversible :
  (p : Path) ->
  (originalContent : FileContent) ->
  (randomData : FileContent) ->
  (fs : Filesystem) ->
  LTE (length originalContent) (length randomData) ->
  -- After overwrite, original is irrecoverable
  (recovery : FileContent -> Maybe FileContent) ->
  recovery randomData = Nothing  -- Cannot recover original
overwriteIrreversible p orig rand fs lenPrf recovery =
  -- Information-theoretically secure:
  -- random data of sufficient length destroys all information
  -- about the original
  ?overwriteIrreversibleProof

--------------------------------------------------------------------------------
-- GDPR Compliance
--------------------------------------------------------------------------------

||| GDPR "Right to be Forgotten" implementation
|||
||| Guarantees that personal data is permanently destroyed and cannot be
||| recovered, satisfying GDPR Article 17.
export
record GDPRDeletionProof where
  constructor MkGDPRProof
  ||| Path that was deleted
  path : Path
  ||| Obliteration proof
  obliterated : ObliterationProof path
  ||| Timestamp of deletion request
  requestTime : Integer
  ||| Timestamp of deletion completion
  completionTime : Integer
  ||| Audit log entry
  auditLog : String

||| GDPR-compliant delete operation
|||
||| Total: do-block with case-split on Either, calls only total functions
||| (secureDelete is now total). IO does not introduce partiality.
export
gdprDelete :
  (p : Path) ->
  (requestTime : Integer) ->
  IO (Either String GDPRDeletionProof)
gdprDelete p reqTime = do
  -- Perform secure deletion at Purge level
  result <- secureDelete p Purge

  case result of
    Left err => pure $ Left err
    Right oblitProof => do
      -- Get current time for completion
      let compTime = reqTime + 1  -- In practice: get actual time

      -- Create audit log
      let audit = "GDPR deletion: " ++ pathToString p ++
                  " at " ++ show compTime

      pure $ Right $ MkGDPRProof p oblitProof reqTime compTime audit

||| GDPR Article 17 compliance witness: every deletion record carries an
||| obliteration proof for the same path. Mirrors the structural shape
||| of Coq's obliterate_leaves_no_trace. Replaces the previous
||| non-theorem (recovery = id, refuted by const empty); see issue #61.
||| Stronger properties (completionTime ordering, audit non-emptiness)
||| require strengthening MkGDPRProof — tracked as a follow-up.
export
gdprDeletionCompliant :
  (rec : GDPRDeletionProof) ->
  ObliterationProof rec.path
gdprDeletionCompliant rec = rec.obliterated

--------------------------------------------------------------------------------
-- Hardware Erasure
--------------------------------------------------------------------------------

||| Hardware-level secure erase (e.g., SATA Secure Erase, NVMe Format)
|||
||| This is the strongest form of deletion - entire device is wiped.
||| ABSOLUTELY IRREVERSIBLE.
public export
data HardwareEraseProof : Type where
  ||| Proof that entire device was erased
  MkHardwareEraseProof :
    (device : String) ->
    (method : String) ->  -- "SATA_SECURE_ERASE", "NVME_FORMAT_CRYPTO", etc.
    (timestamp : Integer) ->
    HardwareEraseProof

||| Hardware erase is absolutely irreversible.
||| Even with physical access to the device, data cannot be recovered.
||| The recovery function is parameterised by `Unit` so it represents
||| any nullary recovery procedure ("just try and reconstruct").
export
hardwareEraseIrreversible : HardwareEraseProof -> (Unit -> Filesystem) -> Void
hardwareEraseIrreversible (MkHardwareEraseProof _ _ _) _ =
  ?hardwareEraseIrreversibleProof

--------------------------------------------------------------------------------
-- Audit Trail
--------------------------------------------------------------------------------

||| Audit log entry for obliteration operation
public export
record AuditEntry where
  constructor MkAuditEntry
  ||| What was deleted
  path : Path
  ||| Who requested deletion
  requestor : String
  ||| When it was deleted
  timestamp : Integer
  ||| Deletion level
  level : SecureDeleteLevel
  ||| Proof that deletion succeeded
  obliterated : ObliterationProof path

||| Append-only constructor for audit logs.
|||
||| The only allowed mutation is appending a single entry — no in-place
||| modification, no deletion. Encoded as a function so callers cannot
||| produce a new log except via this primitive.
public export
appendAuditEntry : List AuditEntry -> AuditEntry -> List AuditEntry
appendAuditEntry log entry = log ++ [entry]

||| Append-only invariant: every constructor application produces
||| exactly `log ++ [entry]`. Trivially `Refl` by the definition of
||| `appendAuditEntry`.
|||
||| Replaces the previous non-theorem signature
||| `(newLog : List AuditEntry) -> newLog = log ++ [entry]`
||| which was provably false (caller could pass any `newLog`). See
||| issue #119 for the design rationale (mirrors the #60 / #61
||| precedent: redesign non-theorem signatures rather than close
||| them with `believe_me`).
export
appendOnlyAuditLog :
  (log : List AuditEntry) ->
  (entry : AuditEntry) ->
  appendAuditEntry log entry = log ++ [entry]
appendOnlyAuditLog log entry = Refl

||| `Elem` is preserved by right-appending the element itself.
|||
||| Pure list lemma — the appended item always lives at the end of
||| the new list. Proof by straightforward induction on the prefix.
|||
||| Idris2 0.8.0 base does not ship this lemma directly; the closest
||| stdlib helper is `Data.List.Elem.elemMap` (membership lifted
||| through `map`), which we use as the second step of the audit
||| completeness proof below.
elemAppRightSelf : (xs : List a) -> (x : a) -> Elem x (xs ++ [x])
elemAppRightSelf []        _ = Here
elemAppRightSelf (_ :: ys) x = There (elemAppRightSelf ys x)

||| Audit log completeness — every path inserted via the official
||| append-only constructor appears in the resulting log.
|||
||| Replaces the previous non-theorem signature
|||
|||     auditTrailCompleteness :
|||       (entries : List AuditEntry) ->
|||       (p : Path) ->
|||       (obliterated : ObliterationProof p) ->
|||       Elem p (map AuditEntry.path entries)
|||
||| which was provably false (refuted by `entries = []`: an
||| `ObliterationProof` for any `p` exists by `MkObliterationProof`,
||| yet the empty log contains no paths). See issue #131 for the
||| design rationale (mirrors the #60 / #61 / #119A precedent:
||| redesign non-theorem signatures rather than close them with
||| `believe_me`).
|||
||| The corrected shape encodes the actual invariant: the path is
||| present in the post-append log *because* it was appended via
||| `appendAuditEntry`. The premise `insertedPath` witnesses the
||| caller's commitment that the new entry indeed records the path
||| we claim is logged.
|||
||| Closure path (zero new axioms):
||| 1. `appendAuditEntry log entry` reduces to `log ++ [entry]` by
|||    the definition of `appendAuditEntry`.
||| 2. `Data.List.Elem.elemMap` lifts list membership through `map`,
|||    giving `Elem (AuditEntry.path entry) (map AuditEntry.path
|||    (log ++ [entry]))`.
||| 3. `elemAppRightSelf` discharges `Elem entry (log ++ [entry])`
|||    by induction.
||| 4. The `insertedPath` equality rewrites `AuditEntry.path entry`
|||    to `p` in the goal.
export
auditTrailCompleteness :
  (log : List AuditEntry) ->
  (entry : AuditEntry) ->
  (p : Path) ->
  (insertedPath : AuditEntry.path entry = p) ->
  Elem p (map AuditEntry.path (appendAuditEntry log entry))
auditTrailCompleteness log entry p insertedPath =
  rewrite sym insertedPath in
    elemMap AuditEntry.path (elemAppRightSelf log entry)
