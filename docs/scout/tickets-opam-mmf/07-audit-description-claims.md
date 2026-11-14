<!-- doc-kind: finding
date: 2026-08-24
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Audit the opam descriptions for stale and unearned claims

**Type:** task · **Map:** [An MMF release bar for the opam packages](../map-opam-mmf-release-bar.md)
**Blocked by:** nothing — takeable

## Question

The two opam descriptions are the packages' shop window and they are long,
specific and unverified. One claim in the same family — the MANIFEST's
"15-file set" — is already provably wrong, which is reason enough to check the
rest before minting.

Go through both `.opam` files sentence by sentence and mark each factual claim
**earned**, **stale**, or **unearned**. The output is that list plus corrected
text; the bar line that keeps it true is ticket 06's business.

Specific claims already worth suspicion:

- `spatial-algebra`: "Two independent modules", "zero intra-corpus
  dependencies", "no Flocq, no classical reals". Check against the current
  `DE9IM.v` and `RelateIntDetBound.v`, not against the description's own history.
- `spatial-algebra`: the `DE9IM` module list — "disjoint, intersects, contains,
  within, covers, ..." — and whether the new `im_unsupported` sentinel deserves
  a mention, since it changes what the module says about *unsupported* pairs.
- `robust-predicates`: "a small, self-contained Rocq library" against 21 files.
- `robust-predicates`: "robust segment-intersection predicates" — check the
  `Intersect_b64_exact_*` chain actually delivers what a reader would infer.
- `robust-predicates`: the GeoCoq comparison ("GeoCoq is synthetic/axiomatic").
  A claim about a third-party library that will age without anyone noticing;
  decide whether a package description should carry it at all.
- `robust-predicates`: the Shewchuk Theorem 13 counterexample paragraph. This is
  the most valuable sentence in either description and the most damaging if
  imprecise — verify it says exactly what the corpus proves.
- Both: `logpath:NTS.Proofs`. Correct today, but flagged in the map's fog as a
  possibly unneighbourly namespace for a distributed package.

Also check the two `README.md` files under `packaging/` and the top-level
`packaging/README.md`, which have the same exposure and none of the scrutiny.

Cite by name, never by line number — the reason this ticket exists is that hooks
and hand-maintained counts rot.
