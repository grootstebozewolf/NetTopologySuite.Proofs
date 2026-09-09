# RelateNG / DE-9IM — living status (Scholar Sam)

Successor of the archived pre-#530 triage
(`docs/history/issue-67-relateng-triage.md`). Cite theorems by **name**.
Do not cite line numbers. Session counts and S-rung labels in the archive
are chronology.

Cross-epic source of record for batch status remains
[`TRIAGE_NTS_JTS_ISSUES.md`](../TRIAGE_NTS_JTS_ISSUES.md). The #522
children have their own live gate: [`docs/scout/map-522.md`](scout/map-522.md).

## What to open

| Question | Surface |
|---|---|
| Is this theorem in the corpus? | [`verified-claims.md`](verified-claims.md) `#67` / `#522` rows |
| What is the specified interior? | [ADR-0003](adr/ADR-0003-two-tier-interior-spec-parity-computation.md) |
| What is the next #522 grab? | [`scout/map-522.md`](scout/map-522.md) |
| Does #67 itself retire? | [`scout/tickets/closed/11-retire-67-second-pass.md`](scout/tickets/closed/11-retire-67-second-pass.md) (overtaken; owner already retired the GitHub object) |
| Rect + triangle touch cells | [`rect-triangle-touch-milestone.md`](rect-triangle-touch-milestone.md) |
| Clothoid leftovers | [`clothoid-open-questions-triage.md`](clothoid-open-questions-triage.md) |
| Why the triage was written | [`history/issue-67-relateng-triage.md`](history/issue-67-relateng-triage.md) |

## Proven (gated names)

These are the facts Scholar Sam still needs from the old triage. Each
name is a ledger row (or a sibling listed next to one). If a name is
missing from `verified-claims.md`, that is a #503 defect, not a hole in
the mathematics.

**Honesty / decline**

- `RelateNGCore.v : relate_unsupported_no_predicate` — general-case fallthrough declines
- `RelateNGDisjoint.v : relate_tjunction_pair_no_predicate` — leftover decline pin is the T-junction
- `RelateNGOracleSurface.v : triangle_unsupported_token` — wire token `UNSUPPORTED` (#588 + #595 / `522-f`)

**Regime predicates and bar 1**

- `RelateMatrixTriangle.v : regime_predicates_pairwise_exclusive` — the four former `True` arms are geometry
- `RelateNGContainsBridge.v : contains_b_ccw_implies_closed_containment` — detector → closed containment
- `RelateNGOverlap.v : triangle_pair_regime_overlap` / `RelateNGDisjoint.v : triangle_pair_regime_disjoint` / `RelateNGTouchVertexRegime.v : triangle_pair_regime_touchvertex`
- `triangles_touch_on_shared_edge` — frozen shared-edge predicate (not reminted)

**Bar 2 gtri cells (specified interior; classifier pins not reminted)**

- `RelateNGDisjointCells.v : sentinel_disjoint_ogc_gtri_cells` — FF2FF1212
- `RelateNGContainsCells.v : contains_pair_ogc_gtri_cells` — 212FF1FF2
- `RelateNGTouchEdgeCells.v : touch_edge_pair_ogc_gtri_cells` — FF2F11212
- `RelateNGOverlapCells.v : overlap_pair_ogc_gtri_cells` — 212101212

**Completeness is false**

- `RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`

**Touch cells (the row the archive understated)**

- `touch_triangles_regime_cells_ii_bb_ee` — II + BB + EE `cell_ok` under `TPR_TouchEdge`
- `touch_int_ext_exclusion` — unconditional specified-interior exclusion
- `touch_triangle_ii_separation_not_unconditional` — guard-free II is false
- `relate_on_rects_dispatches` / `touch_regime_exterior_row_pinned` / `touch_rect_pair_ii_cell`
- `ii_cell_dim2_sound_gtri`

**Line×line noding (67-c and the S15 pipeline)**

- `line_collection_test10_de9im_pointset` / `line_collection_matrix_fold_sound`
- `line_pair_fill_disjoint_ie_not_true_dim` — S8 fill honesty gap
- Exterior-row true-dim pin lives in `RelateNodingLineLineExtPinned.v` (ledger #67-c)

**Prepared hook**

- `RelatePrepared.v : prepared_evaluate_cache_short_circuit` — cache-consulting `evaluate` (#591 / `522-e`)

**Curve-polygon × point / S10b–S12**

- `arc_chord_dist_sq_via_sweep`
- `point_in_rect_curve_geometry_iff_polygon`
- `point_in_rect_curve_geometry_characterisation`

## Still open (not a theorem)

Carved off the archive's "still open" list. None of these is a decline
disguised as disjointness — that was #530.

- **Full RelateNG noding** for arbitrary (point / line / area / collection)
  geometry. Today's `relate` declines off the rect and triangle dispatch.
  Not a #522 child.
- **Nine-cell `geom_de9im_pointset` capstone** — BI and side-E\* vs hand-specified
  `F`, because parity `point_set` is half-open. ADR-0003 is the convention;
  triangle bar-2 gtri cells are on `main` (#592–#594). Ticket 11 tracks
  whether the capstone consumed the ADR.
- **Touches-vs-Share `LPR_Touches` fill split** (line×line). Companion of
  `line_pair_fill_share_ii_not_pinned_int_bnd_only`.
- **`F` vs not-computed** on `CURVE_RELATE_MATRIX` — sibling #523, not a
  #522 child. Children `523-a` / `523-b` / `523-c` (#603 #604 #605)
  landed. Ticket 523 stays open, not accepted. Coq emptiness is `None`
  (`RelateCurveMatrix.v : cell_none_iff_empty`). The oracle prints `?`
  for lineal undistinguished cells and an exhausted 80×80 probe; E/B
  `failwith`. EE stays `2` (`geom_de9im_ee_nonempty`). Whole-matrix
  Decline is already honest
  (`RelateNGCore.v : relate_unsupported_no_predicate`). Chart:
  [`scout/map-523.md`](scout/map-523.md). Spec:
  [`scout/spec-523.md`](scout/spec-523.md).
- **Empty/empty `relate`** — parked on the #522 epic (declines; ISO 13249-3
  if revisited).
- **`TPR_TouchEdge` exclusivity** vs the four gtri predicates — named, not
  proved. Carved on `main` via #597. Chart: [`scout/map-522-leftovers.md`](scout/map-522-leftovers.md).
- **Disjoint fill remint** (FFFFFFFFF → FF2FF1212) — unnamed. Not `522-f`.
- **Mutual vertex-in-open-edge sliver** — leftover `Ⅰ` bar 1 landed.
  Headline `RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`.
  Compiled pair is II = 2, BB = 1. Fill stays `im_unsupported`. Chart:
  [`scout/map-tjunction-cert.md`](scout/map-tjunction-cert.md).
  Do **not** mint `522-n`.
- **Obtuse-at-v certificate** — leftover `Ⅱ` classified.
  Headline `RelateNGTouchObtuse.v : triangle_pair_regime_obtuse`.
  Fill stays `im_unsupported`. Leftover `Ⅱ` is QED
  (`RelateNGTouchObtuse.v : leftover_ii_qed_or_qex`). Epic #522
  stop is QED ∨ QEX (`RelateNGEpic522.v : ticket_522_qed_or_qex`).
  Do not bucket with leftover `Ⅰ`.
- **Mixed-cone certificate** — leftover `Ⅴ` classified.
  Headline `RelateNGTouchMixedCone.v : triangle_pair_regime_mixedcone`.
  Fill stays `im_unsupported`.
- **Same-cone certificate** — leftover `Ⅵ` classified.
  Headline `RelateNGTouchSameCone.v : triangle_pair_regime_samecone`.
  Fill stays `im_unsupported`. Epic #522 stop is QED ∨ QEX
  (`RelateNGEpic522.v : ticket_522_qed_or_qex`),
  discharged QEX on an unnamed lens after leftover `Ⅵ`. Leftover
  `Ⅰ`–`Ⅵ` are classified
  (`RelateNGEpic522.v : ticket_522_classified_qed_or_qex`). Leftover
  `Ⅶ` is already #642.
- **Exterior-side one-sided T** — leftover `Ⅲ`. `Ⅲ∨Ⅳ` xor with two
  witnesses. Headline
  `RelateNGTouchOnesided.v : triangle_pair_regime_onesided`. Fill token
  is load-bearing (`im_unsupported`). Not CONTEXT Bar 1.
- **Interior-side stem** — leftover `Ⅳ`. Residue pair compiled.
  `RelateNGComplete.v : interior_side_pair_inhabits`. Headline
  `RelateNGTouchOnesided.v : triangle_pair_regime_interior_side`.
  Pair `(0,0)(2,0)(0,1)` vs `(1,0)(5/4,1/4)(3/4,1/4)`. Same-side;
  `overlap_b` false; II nonempty. Fill stays `im_unsupported`.
  Not CONTEXT Bar 1. Chart:
  [`scout/map-interior-side-cert.md`](scout/map-interior-side-cert.md).
- **Inherited JCT seam** for general-polygon Contains (not the rectangle
  special case). `point_in_ring_correct` remains conditional.

Volatile counts (how many cells, how many S-rungs) stay in the archive.
This page names theorems and tickets only. The prose gate is
`scripts/validate-claims.sh` over `docs/gated-prose-docs.txt`.

## External pins the archive still got right

- JTS#1175 (`computeLineEnds` skipping disjoint line-component ends) is
  fixed upstream (JTS#1200). The corpus pin is the JTS#1175 class in
  `RelateBoundary.v` / `jts1175_*` ledger rows.
- NTS#819 prepared A-L cache is a performance issue; the proof obligation
  is result-independence of the cache path
  (`RelatePrepared.v : prepared_evaluate_cache_short_circuit`).
