<!-- doc-kind: finding
date: 2026-08-24
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Decide the shape of the manifest-closure gate

**Type:** grilling · **Map:** [An MMF release bar for the opam packages](../map-opam-mmf-release-bar.md)
**Blocked by:** nothing — takeable

## Question

The map settled that closure is **part of the bar, and gated**. This ticket
decides what the gate checks and where it runs. It does not write the script —
that is execution.

Today the closure claim is prose in a MANIFEST header, and it is already false
in detail: the `robust-predicates` header describes a "15-file set" and an
"11 files" Flocq layer, while the list holds **21 paths** (4 + 17).
`assemble.sh` verifies nothing.

Decide:

1. **What "closed" means precisely.** The natural reading is that every
   `From NTS.Proofs[.Flocq] Require` in a shipped file resolves to another
   shipped file. Confirm that, and decide the treatment of `Require` lines that
   resolve to Rocq's Stdlib or Flocq — presumably allowed, but the allowed set
   should be named rather than assumed, because "depends only on Stdlib" is a
   headline claim in both descriptions.
2. **Where the gate runs.** Three candidates, not exclusive: inside
   `assemble.sh` so a bad manifest cannot assemble; as a `make ci-guards` check
   so it runs on every push; in the release workflow so a mint cannot proceed.
   The map's standing preference argues for the earliest point that can fail.
3. **Whether the header counts stay.** A count in a comment is a hook that rots
   — this one already did. Either the gate derives and prints the count, or the
   comment drops it. Do not keep a hand-maintained number.
4. **Whether the gate also checks the reverse direction** — that every file in
   `theories/` of the assembled package is listed in the MANIFEST, so a stray
   copied file cannot ride along unlisted.
5. **Per-package or shared.** Two packages, two manifests, one concept. Decide
   whether this is one script taking a package directory, or two.

Related but distinct, and deliberately not folded in here: the accuracy of the
*prose* claims in the opam descriptions is ticket 07.
