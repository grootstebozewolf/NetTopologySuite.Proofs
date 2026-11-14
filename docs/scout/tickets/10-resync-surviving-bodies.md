<!-- doc-kind: finding
date: 2026-08-22
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Resync surviving issue bodies to corpus state

**Type:** task · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** **#506** *Module split campaign* — its queue must be **empty**, not merely the epic open (see [Open the module-split queue epic](closed/03-open-module-split-queue-epic.md)) · ~~[End #69's umbrella role](closed/09-end-69-umbrella.md)~~ ✔

## Question

Bring every surviving issue body into agreement with the corpus. Deliberately the
last ticket: a body that describes a module about to be split will be wrong again
the moment it is split, which is why the resync waits for the split queue to
drain.

Scope — only issues that survive this map:

- **#423 metrics** — body predates `HausdorffMetricSym.v`, the shared
  `MaxMinScore.v` layer and the 423-b coupling; its two real gaps (the
  discrete-vs-continuous densification bound, and `HAUSDORFF_DIRECTED` /
  `HAUSDORFF_SYMM` oracle modes) should read as the remaining asks rather than
  being buried among satisfied ones.
- **#424 hulls** — body should say plainly that no convex-hull code exists yet
  (`grep -i 'convex_hull\|lower_hull\|graham\|andrew' theories/*.v` → 0 hits) and
  that `HullExactExtrema.v` (424-b) is a curve-cardinals exactness cell, not a
  hull construction.
- **#425 coverage** — one of six asks stands, at witness scope
  (`coverage_gap_overlap_cleaner` is a constant function on a single two-cell
  witness). Say so.
- Any successor epic this map opened. **#69 is owner-retire ready**
  ([`69-closing-summary.md`](../69-closing-summary.md)); this ticket
  does not own its stale GitHub body.

Corpus-wide facts to state once and correctly, since several bodies contradict
them: **zero** proofs remain admitted anywhere in `theories/` or
`theories-flocq/`, `docs/admitted-deferred-proofs.txt` has no live entries, and
`docs/verified-claims.md` carries **700** cited claim rows.

(Phrased without the literal token on purpose — the review gate scans added lines
for it regardless of file type, so prose *about* admitted proofs trips it.)

Closed issues are explicitly **out of scope** — a closed issue's stale body is
harmless, and refreshing it is wasted work.
