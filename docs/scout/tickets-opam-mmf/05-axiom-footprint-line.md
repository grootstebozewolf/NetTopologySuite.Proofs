<!-- doc-kind: finding
date: 2026-08-24
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Decide the axiom-footprint line, per package

**Type:** grilling · **Map:** [An MMF release bar for the opam packages](../map-opam-mmf-release-bar.md)
**Blocked by:** nothing — takeable

## Question

Both packages make an axiom claim in their opam description, and the two claims
are materially different:

- **`spatial-algebra`** — "both `Qed`-closed with NO axioms (*Closed under the
  global context*)", "zero axioms", "no Flocq, no classical reals".
- **`robust-predicates`** — "the only axioms are the standard classical-reals +
  functional-extensionality used throughout the corpus (see `make`'s
  `Print Assumptions` output)".

The corpus itself declares three classical-reals axioms for `theories/`
(`sig_not_dec`, `sig_forall_dec`, `functional_extensionality_dep`) plus
`Classical_Prop.classic` from Flocq for the binary64 layer. So
`robust-predicates`' claim is roughly right and `spatial-algebra`'s is a
stronger, per-file claim about two specific files.

Decide what the bar requires:

1. **Verified at release time, or asserted?** The claim currently lives in prose.
   The gates-over-prose preference says the bar should require
   `Print Assumptions` output *from the assembled package build* — not from the
   corpus build, since the package is what a consumer gets. Confirm, and decide
   where that output is recorded so a reader can check it (release notes,
   a file in the tarball, the README).
2. **The exact wording of each line.** "Zero axioms" is a strong, checkable
   claim and worth keeping if it is true of the assembled package; it is also
   exactly the kind of claim that silently becomes false when a shipped file
   gains an import. Decide whether the bar states it per package, per file, or
   per module.
3. **What happens when the two disagree.** If the bar has one axiom line and the
   packages have different footprints, either the line is per-package or it
   states the union. The map allows per-package exceptions; this is one.
4. **Whether `spatial-algebra`'s claim survives the `DE9IM.v` change.** That file
   gained the `im_unsupported` sentinel and its theorems since the last mint.
   The claim is that it is axiom-free — check it against the current file rather
   than trusting the description.

Deliberately out of this ticket: the *other* prose claims in the descriptions
(ticket 07) and manifest closure (ticket 02), even though all three are
"is the description true" questions. This one is about axioms because the axiom
claim is the load-bearing one for a proof library.
