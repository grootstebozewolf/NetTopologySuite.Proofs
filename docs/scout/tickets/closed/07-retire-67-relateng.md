<!-- doc-kind: finding
date: 2026-08-22
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Retire #67 — RelateNG matrix and boundary handling

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** — · **Closed:** 2026-08-22 (decision: **do not** close #67 yet)

## Question

#67 (Immediate) asks for the DE-9IM matrix, predicates, MOD2 boundary handling,
prepared mode and oracle modes. The audit reads **MOSTLY**: both named round-2
blockers are now Qed. Does it close, and where does its residue go?

Satisfied (verify then cite): `theories/RelateNGTouchCells.v:75 touch_triangle_pair_ii_cell`
and `RelateNGTouch.v:166/200 touch_int_ext_exclusion`; the JCT seam lift
`gtri_point_in_ring_imp_pos` annotated **DISCHARGED (was Admitted)**, with the
guard-free form refuted by `touch_triangle_ii_separation_not_unconditional`; the
regime→cell triple `touch_triangles_regime_cells_ii_bb_ee` (2026-07-20,
`docs/relate-ng-status.md` and the archived triage §S15l); asks 1/2/3a green via `DE9IM.v` and
`RelateLineLine.v`; oracle `RELATE_MATRIX`, `RELATE_PREDICATE`,
`CURVE_RELATE_MATRIX` present. `RelateNG.v` split into six layers 2026-08-15
(`docs/audit-meso-sample-2026-08.md` B6 = DONE).

Residue to place:

1. The full nine-cell `geom_de9im_pointset` capstone — BI and side-E\* cells
   mismatch the hand-specified F values because of half-open ring inclusion on
   shared edges; still recorded as open on `docs/relate-ng-status.md`. Is
   this one issue or several? (This is the fog patch the map names.)
2. `TPR_Overlap` and the remaining regimes — defined in
   `RelateMatrixTriangle.v:28/100`, no sound cheap test yet.
3. Multi-geometry / compound-input pipeline.
4. Prepared-cache end-to-end `evaluate` hook.
5. An oracle geometry-**compute** mode; today's modes are pinned-catalog only.

Also settle a convention question this epic raises: the sibling GEOS rung doc
(`docs/geos-oracle-rung-2026-08.md`) records six warns as "soft boundary/DE-9IM
convention notes" with no decision recorded on the convention itself. That
half-open-inclusion convention is the same one blocking residue item 1 — decide
whether it is one decision serving both, and record it once.

## Resolution

**Closed 2026-08-22 with the decision that #67 does NOT close.** The convention is
settled as **ADR-0003**; two wrong-answer issues filed (#522, #523); four
documentation defects to #503. A second-pass ticket carries the closure.

### This is the first ticket to break the pattern, deliberately

#64, #65 and #66 closed on scope achieved, because their amber rows were *named
conditionals and flagged frontiers* — honest partial results. #67's compute path
is different in kind:

- `RelateNGCore.v:337` returns `ll_matrix_disjoint` — `FFFFFFFFF`, a positive
  claim of disjointness — for **every** pair that is not rect×rect or
  triangle×triangle. No sentinel; `BUFFER_REGION` at least *promises*
  `DEGENERATE`.
- `RelateNGCore.v:301 triangle_pair_regime` cannot emit `TPR_Overlap`, so
  overlapping triangles — a supported pair — compute as **disjoint**.
- `RelateMatrixTriangle.v:89-94` defines four classifiers as `Prop := True`, so
  `TPR_Overlap` is provable for any six points and
  `triangle_pair_fill_overlap_eq` is Qed by `reflexivity`.
- `RelatePrepared.v:48 prepared_evaluate_agrees` is Qed **by `reflexivity`** over
  that stub — a green proof resting on the wrong answer.

Closing under "satisfied on scope achieved" would be the same species of
overclaim this map has spent the session filing corrections for.

### The convention question answered: two conventions, one migration

The nine-cell capstone was blocked by an **undeclared conflation**, not missing
geometry. `RectangleJCT.v:182 point_in_ring_rect_iff` proves parity inclusion is
half-open (`x0 <= px p < x1`), so a shared vertical line is A's boundary and B's
*interior*. That single fact is why the rect II cell is free (`RelateNGRect.v:305`)
and why BI / side-E\* are nonempty against a matrix asserting `F`.

Four of the six GEOS WARNs (`IN !contains`, chord `y=0`) are **the same
convention**. The other two (apex `(0,1)`, `OUT intersects`) are vertex-grazing
rays — the `ray_avoids_vertices` genericity guard, **provably irreducible** inside
the parity model (`RelateNGTouchRED.v:170`, Qed). Only leaving parity removes it,
which is what the specification tier does. Hence: two conventions, one migration.

**ADR-0003** declares the two-tier model the code already implements — OGC open
interior **specifies**, half-open parity **computes**, `gtri_point_in_ring_imp_pos`
bridges, and `ring_complement` + `ray_avoids_vertices` are **permanent
load-bearing guards** (the Qed refutation proves them maximal, so calling them
deferrals was wrong). CONTEXT.md now carries *specified interior*, *computed
interior* and *interior bridge*, with the rule that a claim must say which tier it
is in.

### My residue list was stale on two of five — the fifth ticket running

- Item 5 said the relate oracle has "no geometry compute". **Wrong**:
  `CURVE_RELATE_MATRIX` (`driver.ml:3593`) computes genuinely, and the driver's own
  comment contrasts it with the catalog modes. It has its own honesty defect
  instead (#523).
- Item 4 said the prepared end-to-end hook is missing. It **exists** and is
  vacuous — `RelatePrepared.v:41` `evaluate pg g := relate (pg_geom pg) g`, proven
  by `reflexivity`, with `pg_cache`/`pg_tri_cache` populated and never consulted.

### What is genuinely strong here

`RelateNGTouch.v:200 touch_int_ext_exclusion` — Qed, unconditional, `nra`-only —
and `RelateNGTouchRED.v:170` — a Qed *refutation* that pins the II guard as
maximal. Both correctly described everywhere checked. The guard is a result, not a
gap.
