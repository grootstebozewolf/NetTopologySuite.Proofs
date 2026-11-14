<!-- doc-kind: finding
date: 2026-08-22
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Retire #68 — Delaunay triangulation and Voronoi diagrams

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** — · **Closed:** 2026-08-22

## Question

#68 (Non-urgent) asks for empty-circle exactness, triangulation invariants, the
Voronoi dual, a curve-densify path and oracle modes. The audit reads **PARTIAL**,
with an important nuance: **all three** of the body's round-2 queue items have
landed since the body was written, but a whole phase of the ask has not started.
Does it close, or does the unstarted phase mean it stays open as its own epic?

Landed (verify then cite): `theories/DelaunayFlipGeometric.v:75 inCircle_R_flip_witness_ccw`;
`theories/DelaunayDegeneratePins.v` (`single_triangle_delaunay` = JTS#1190,
`cocircular_square_tie_1039` = JTS#1039, `cocircular_tie_is_knife_edge`);
`theories/DelaunayLocallyDelaunay.v` (68-b,
`flip_witness_both_not_locally_delaunay`); 68-a
`theories/DelaunayEdgeEmptyCircle.v` (`verified-claims.md:434-435`).

Not started:

1. **Voronoi is absent.** `grep -li voronoi theories/` hits only comments and
   `HausdorffMetricSym.v`'s two-site `vor2_*` profile, which is a metric-lane
   slice, not the Delaunay dual. The body's own table already calls Voronoi
   "phase 2".
2. Bisector construction and four-point robustness (JTS#1039, JTS#20).
3. Ask 5: curve densify → triangulate (TRI-DT / TRI-VR densified-boundary path).
4. `DELAUNAY_WITNESS` oracle mode is not in `oracle/driver.ml`.

The decision this ticket owes: an epic whose phase 1 is done and whose phase 2 is
untouched is exactly the shape the destination calls "a clearly-stated new epic".
Close #68 on phase 1 with the evidence above and open *Voronoi dual and
triangulation robustness* as its successor, or keep #68 open and accept that the
block does not reach zero. The former is preferred by the destination; confirm the
phase boundary is real before acting.

## Resolution

**Closed 2026-08-22. #68 closed on the predicate and local-flip layer; the global
tier is #525. Also filed #526 and two register gaps to #503.**

**"Confirm the phase boundary is real before acting" was the right instruction, and
the answer was: real, but drawn in the wrong place.**

Phase 2 is cleanly absent — no bisector, no dual graph, no cell, no diagram — and
nothing was mislabelled as Voronoi progress. The two near-misses are honestly
scoped elsewhere: `HausdorffMetricSym.v:130 vor2` is a **1-D two-site scalar
distance transform** belonging to #423 (its own header says "Voronoi-surface layer
… 1D"), and the LEC lane's `lec_candidate_completeness_interior` /
`kvertex` are equidistance facts about candidate *points*, one on a hard-coded
circumcentre.

But **phase 1 is not "Delaunay triangulation correctness"**: not one theorem in the
lane quantifies over a mesh. `DelaunayEdgeEmptyCircle.v:124 triangulation_of`
requires only vertices-in-`S` and `area2 <> 0` — no covering, no
interior-disjointness, no hull — so **a single triangle satisfies it**, and the ←
direction discharges by building exactly that. Every flip result is over one
shared-edge quad; the pins are rational constants on a fixed square; and the
in-circle exactness is #64's theorem verbatim plus an 11-line transport. So the
successor epic is named for the **global tier**, not for "Voronoi phase 2" — the
epic's own framing would have understated the gap.

**Why this closure is truthful where #67's would not have been.** Checked all four
of #67's failure modes explicitly and found **none**: zero `Prop := True`
placeholders; no theorem proven by `reflexivity` over a stub; no fallthrough
emitting a positive verdict — the lane has no decision procedure at all, every
definition being a `Prop` or a constant; and cocircular input reports a loud
`ZERO` rather than guessing a side, so the JTS#1039 knife-edge is never silently
resolved. The docs are accurate too: `verified-claims.md:434` says "weak skeleton"
and names the `|S|=2` counterexample itself, and
`DelaunayEdgeEmptyCircle.v:52-67` states outright *"no sweep, no beach line, no
event queue, and no construction of a diagram."* Narrow-but-correct-and-labelled
closes; wrong-but-labelled-fine does not.

**One successor, not two.** The Voronoi dual needs a triangulation to be dual
*to*; splitting them invites someone to start the diagram before the mesh exists.

**Filed on the way:** **#526** (`INCIRCLE_SIGN`'s stale "deferred" note quotes
`2^12` where the proven regime is `2^11`, and it prints a confident sign above
that window while the Qed-backed `INCIRCLE_EXACT` sits beside it) and two register
gaps in **#503** — `inCircle_R_flip_witness_ccw` was cited as closure evidence yet
has no claims row, and `in_circle_test`/`triangle_ccw` now exist twice because the
flocq bridge `DelaunayFlipGeometric.v:35` calls "a cheap follow-up" was never
built.

One doc is stale in the *pessimistic* direction: `audit-rgr-comparison.md:622`
still says "#68 … no theory yet".
