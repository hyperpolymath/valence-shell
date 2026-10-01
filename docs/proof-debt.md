<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# Proof debt

This register documents the three source-level escape hatches detected by the
shared trusted-base gate at revision `1c2346017abafd7dfb754ceca652c6393bb58684`.
It does not count imported library axioms or claim end-to-end verification.
See [the proof audit](PROOF_HOLES_AUDIT.adoc) and
[the open frontier](PROOF-OPEN-FRONTIER.adoc) for broader proof obligations.

The sections follow the
[estate trusted-base policy](https://github.com/hyperpolymath/standards/blob/74d2f66f575246cf6e313ae7775f44df6e097ff2/docs/TRUSTED-BASE-REDUCTION-POLICY.adoc).

## (a) Discharged in this repo

No discharged entries in this register. Historical closures are recorded in
the proof audit linked above.

## (b) Budgeted — tested with refutation budget

None. This register makes no claim of a measured refutation budget for the
assumptions below.

## (c) Necessary axiom

- `proofs/agda/FilesystemModel.agda:161` — `funext` postulate.
  - **Justification**: the filesystem is represented as a function from paths
    to optional nodes. Pointwise equality needs functional extensionality to
    yield propositional equality of filesystems in the current intensional
    Agda model. This is an explicit assumption, not a proof term derived in
    that model; changing to cubical Agda would change the proof foundation.
  - **Citation**: the source uses `Extensionality lzero lzero` from
    `Axiom.Extensionality.Propositional` in the Agda standard library and cites
    the HoTT Book, Axiom 2.9.3. See the
    [declaration and justification](../proofs/agda/FilesystemModel.agda).

- `proofs/idris2/src/Filesystem/Axioms.idr:44` — `axStringEqRefl`.
  - **Justification**: the current Idris2 model assumes primitive String
    equality is reflexive on opaque values. The type checker cannot reduce
    that primitive equality for an arbitrary String, so the existing
    `believe_me` term supplies `(s == s) = True`. This trusts the backend's
    primitive equality semantics; it is not a general equality soundness
    axiom. Removing it would require a constructive equality representation
    or an appropriate primitive-equality proof.
  - **Citation**: the named axiom and its operational rationale are in
    [Filesystem.Axioms](../proofs/idris2/src/Filesystem/Axioms.idr), with its
    consumers recorded under `axStringEqRefl` in the
    [existing axiom registry](../.machine_readable/IDRIS2_AXIOMS.a2ml).

- `proofs/idris2/src/Filesystem/Axioms.idr:57` — `axBits8EqRefl`.
  - **Justification**: the same primitive-equality boundary applies to Bits8.
    The existing `believe_me` term supplies `(b == b) = True` for opaque bytes.
    `fileContentEqRefl` then lifts this assumption structurally to byte lists;
    the list proof introduces no additional axiom. Eliminating the assumption
    requires a constructive byte representation or a primitive-equality proof.
  - **Citation**: see
    [Filesystem.Axioms](../proofs/idris2/src/Filesystem/Axioms.idr) and the
    `axBits8EqRefl` entry in the
    [existing axiom registry](../.machine_readable/IDRIS2_AXIOMS.a2ml).

## (d) DEBT — actively to be closed

None of the three detected escape hatches is unclassified. This does not
discharge the implementation correspondence and other obligations tracked in
the open frontier linked above.
