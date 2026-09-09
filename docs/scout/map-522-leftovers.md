# Map — #522 leftovers (after wrap-up)

A wayfinder map. Charted 2026-08-30. This is **not** a second copy of
[`map-522.md`](map-522.md) and it is **not** a `wayfinder:map` GitHub
issue. The epic comment stays the design of record. #589 stays closed.

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are precomposed
> Roman numerals (`Ⅰ`, `Ⅱ`, `Ⅲ`, `Ⅳ`, …), not `522-*` letters
> and not repeated `Ⅰ` marks. Do not remint ADR-0004. Do not mint
> GitHub children from this map.

topics: relate
claimId: none
witness: none

## Destination

**Name the residue so the next `/implement` cannot steal a closed
`522-*` letter or invent `522-n`.**

The #522 honesty ask and wired-triangle bar 1 → bar 2 are done
([`522-closing-summary.md`](522-closing-summary.md)). What remains is
**named leftover work** (`Ⅰ` sliver bar 1; `Ⅱ` obtuse-at-v classified;
`Ⅲ∨Ⅳ` xor with two compiled witnesses; `Ⅳ` residue pair;
`Ⅴ` mixed-cone classified; `Ⅵ` same-cone inhabitance), #67 /
sibling residue, or owner sign-off on the epic. After this
letter the residue is not “unnamed proof work, leftover `Ⅰ`.”

## Notes

**#522 children.** Wrap-up #596 closed #576 and #578. Harness #595
closed #575. Carve #597 is **on `main`**: it closed #567 without
proving TouchEdge exclusivity. Every child is closed. The epic stays
open for owner sign-off.

**Shared classifier pins.** `triangle_pair_fill` and `rect_pair_fill`
share `aa_matrix_disjoint` (FFFFFFFFF), `aa_matrix_partial_overlap`
(2FFF1FFF2), `aa_matrix_contains` (2FFFFFFF2), `aa_matrix_touch_vertical`
(FFFF1FFF2). The OGC gtri names (`*_ogc`) are **separate** definitions.
A remint of a shared pin moves the rect lane too. `DE9IM.v` `pat_disjoint`
rejects FF2FF1212 (`RelateNGDisjointCells.v : ogc_disjoint_fill_not_im_disjoint`).

**Frozen anchors.** `touch_int_ext_exclusion`,
`touch_triangle_ii_separation_not_unconditional`,
`triangles_touch_on_shared_edge`. Ray parity enters only via ADR-0003.

**#589.** Closed / red. Do not merge or reopen. This file is the leftovers
chart; `map-522.md` stays the child-ticket freshness layer.

**Leftover ids.** Precomposed Roman numerals (`Ⅰ`, `Ⅱ`, `Ⅲ`,
`Ⅳ`, …), not `522-*` letters and not repeated `Ⅰ` marks. `Ⅰ` is
the mutual vertex-in-open-edge sliver (II = 2, BB = 1). `Ⅱ` is the
obtuse-at-v certificate (classified; fill token). `Ⅲ` is
the exterior-side one-sided T (compiled pair; II empty). `Ⅳ` is the
interior-side stem (compiled residue pair; II nonempty). The xor
(`RelateNGCore.v : touch_onesided_t_b`) is a `Ⅲ∨Ⅳ` configuration
class with two compiled witnesses; it is not a leftover-`Ⅲ`
detector. `Ⅴ` is mixed-cone (classified; fill token). `Ⅵ` is
same-cone inhabitance (fill token; no denotation). Completeness
is an unnamed lens pair. Epic #522 stop is
QED ∨ QEX (`RelateNGEpic522.v : ticket_522_qed_or_qex`); leftover
`Ⅰ`–`Ⅵ` are classified (`RelateNGEpic522.v : ticket_522_classified_qed_or_qex`).
Leftover `Ⅶ` is already written as #642;
this letter does not mint it. Do not swap them.

## Leftover table

Parks follow ADR-0002 (`CONTEXT.md`): sequencing / research / technique.
Value and priority are orthogonal.

| Id | Leftover | Kind | Park | Status | Do not |
|---|---|---|---|---|---|
| `Ⅰ` | Mutual vertex-in-open-edge sliver | #522-adjacent | research | Bar 1 landed. Chart: [`map-tjunction-cert.md`](map-tjunction-cert.md). Headline `RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`. Pair `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)`. Compiled pair is II = 2, BB = 1 — a sliver, not a kiss. Fill stays `im_unsupported`. | steal `522-j` / `522-m` / `522-f`; remint fills; bucket obtuse under `Ⅰ`; mint `522-n` |
| — | TouchEdge exclusivity vs the four gtri predicates | #522-adjacent | technique | Named leftover, no numeral. Carved by #597 (`522-a-touch-edge-carve`), not proved. | treat the carve as exclusivity; remint frozen anchors |
| — | Classifier fill remints (`aa_matrix_*` → `*_ogc`) | #522-adjacent | sequencing | Unnamed. Four shared pins; disjoint blocked by `pat_disjoint`. Not `522-f`. | remint in a harness letter; steal `522-f` / `522-d` / `522-h` |
| `Ⅱ` | Obtuse-at-v certificate | #522-adjacent | research | Classified (QED). Chart: [`map-obtuse-cert.md`](map-obtuse-cert.md). Headline `RelateNGTouchObtuse.v : triangle_pair_regime_obtuse`. Pair `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)`. Shared origin; cone `side_dot = 0`. Detector `RelateNGCore.v : touch_obtuse_vertex_b` is a closed cone plus `negb cone_separates_b` — not a remint of #572. Fill stays `im_unsupported`. Leftover `Ⅱ` is QED (`RelateNGTouchObtuse.v : leftover_ii_qed_or_qex`). Epic #522 stop is QED ∨ QEX (`RelateNGEpic522.v : ticket_522_qed_or_qex`). Ticket 27 closed. | remint `cone_separates_b` / `touch_vertex_b`; steal `522-i` / `522-m`; emit `FFFF1FFF2`; claim Bar 1; mint `522-n` / leftover `Ⅶ` |
| `Ⅲ` | Exterior-side one-sided T | #522-adjacent | research | Exterior-side pair compiled. Headline `RelateNGTouchOnesided.v : triangle_pair_regime_onesided`. Pair `(0,0)(2,0)(0,1)` vs `(1,0)(1/2,-1)(3/2,-1)`. Contact `(1,0)` is collinear with A's base `y = 0`. II empty (`RelateNGComplete.v : onesided_t_ii_empty`) — not a compiled BB-dim-0 cell; there is no `onesided_t_bb_dim0`. Xor is `Ⅲ∨Ⅳ` with two compiled witnesses. Fill token is load-bearing (`im_unsupported`). `classify_triangle_pair` arm is `True` — leftover `Ⅰ` honesty, not CONTEXT Bar 1. Completeness is unnamed after leftover `Ⅵ`. | remint leftover `Ⅰ`; remint leftover `Ⅱ`; remint leftover `Ⅳ`; emit `FFFFFFFFF` / `FFFF1FFF2` / `FF2F11212`; claim Bar 1; claim a leftover-`Ⅲ` detector; mint `522-n` / leftover `Ⅶ` |
| `Ⅳ` | Interior-side stem | #522-adjacent | research | Residue pair compiled. Headline `RelateNGTouchOnesided.v : triangle_pair_regime_interior_side`. Pair `(0,0)(2,0)(0,1)` vs `(1,0)(5/4,1/4)(3/4,1/4)`. Same A and contact as leftover `Ⅲ`; remaining B vertices sit on the interior side of `y = 0` (`RelateNGComplete.v : interior_side_same_side`). Stem `gtri A = 0`; remaining B vertices `gtri A > 0`; none `gtri A < 0`. So `overlap_b` false (`RelateNGComplete.v : interior_side_overlap_b_false`) while II is nonempty (`RelateNGComplete.v : interior_side_ii_nonempty`) — DE-9IM overlap, detector miss. Inhabitance `RelateNGComplete.v : interior_side_pair_inhabits`. Boolean is not side-aware. Leftover `Ⅲ` looks like areal Touches. One constructor, one `True` arm, one `im_unsupported` — fill token keeps those families from mixing. Not CONTEXT Bar 1. Completeness is unnamed after leftover `Ⅵ`. | invent a side-distinguishing detector; remint the fill; steal leftover `Ⅲ`; emit `FFFFFFFFF` / `FFFF1FFF2` / `FF2F11212`; claim Bar 1; mint `522-n` / leftover `Ⅶ` |
| `Ⅴ` | Mixed-cone certificate | #522-adjacent | research | Classified (QED). Chart: [`map-mixed-cone-cert.md`](map-mixed-cone-cert.md). Headline `RelateNGTouchMixedCone.v : triangle_pair_regime_mixedcone`. Pair `(0,0)(2,0)(0,2)` vs `(0,0)(-1,-1)(3,1)`. Shared origin; remaining B verts have opposite-sign `side_dot` vs `nA = (2,2)`. Detector `RelateNGCore.v : mixed_cone_vertex_b` is opposite-sign plus `negb` of both cones — not a remint of #572 or leftover `Ⅱ`. Fill stays `im_unsupported`. Epic #522 stop is QED ∨ QEX (`RelateNGEpic522.v : ticket_522_qed_or_qex`), discharged QEX on an unnamed lens after leftover `Ⅵ`. Leftover `Ⅰ`–`Ⅵ` are classified (`RelateNGEpic522.v : ticket_522_classified_qed_or_qex`). Ticket 28 closed. | remint `cone_separates_b` / `touch_obtuse_vertex_b`; steal `522-j` / `522-m`; emit `FFFF1FFF2`; claim Bar 1; mint `522-n` / leftover `Ⅶ` |
| `Ⅵ` | Same-sign cone spill | #522-adjacent | research | Inhabitance, not a same-cone or overlap theorem. Chart: [`map-same-cone-cert.md`](map-same-cone-cert.md). Headline `RelateNGTouchSameCone.v : triangle_pair_regime_samecone`. Pair `(0,0)(2,0)(0,2)` vs `(0,0)(3,1)(1,3)`. Shared origin; remaining B verts have same-sign `side_dot` vs `nA = (2,2)`. Detector `RelateNGCore.v : same_cone_vertex_b` is both-strict-pos plus `negb` of both cones and of `mixed_cone_from_v` — not a remint of #572, leftover `Ⅱ`, or leftover `Ⅴ`. Fill stays `im_unsupported`. `classify_triangle_pair` arm is `True` — no denotation. There is no `TPR_SameCone ⇒ interiors meet`. Epic #522 stop is QED ∨ QEX (`RelateNGEpic522.v : ticket_522_qed_or_qex`); letter-local copy is the #577 disjunction (`RelateNGTouchSameCone.v : triangle_pair_regime_ccw_stop`), discharged QEX on an unnamed lens. Ticket 29 closed. Leftover `Ⅶ` is already #642. | remint `cone_separates_b` / `mixed_cone_vertex_b` / `overlap_b`; steal `522-j` / `522-m`; emit `2FFF1FFF2`; claim Bar 1; claim a same-cone soundness result; mint `522-n`; merge to `main` |
| — | Nine-cell `geom_de9im_pointset` | #67 / ticket 11 | technique | ADR-0003 half-open leftover. | mint as a #522 child |
| — | Full RelateNG noding + Touches-vs-Share | #67 | sequencing | Off-dispatch `relate` already declines honestly. | mint as a #522 child |
| — | `F` vs not-computed on `CURVE_RELATE_MATRIX` | sibling #523 | sequencing | Ticket 11 precondition 3. | steal a closed `522-*` letter |
| — | Empty/empty `relate` | parked on #522 | sequencing | Declines today; ISO 13249-3 if revisited. | treat as a decline bug |

## Decisions so far

- Honesty sentinel — #530.
- Wired bar 1 — #580 #581 #582 + contains bridge #586.
- Completeness false — #583 / #584. Certificates not invented.
- Bar 2 gtri cells — #587 #592 #593 #594. Pins not reminted.
- Wire token + harness — #588 + #595. Decline vector was the T-junction;
  leftover `Ⅰ` moved `REGIME DECLINE` to obtuse-at-v; leftover `Ⅱ`
  moved it to mixed-cone; leftover `Ⅴ` moved it to same-cone;
  leftover `Ⅵ` moved it to an unnamed lens.
- Wrap-up — #596. Owner sign-off still required.
- #567 DoD met; TouchEdge exclusivity carved on `main` via #597, not proved.
- #589 wayfinder PR stays closed.
- Leftover ids switch to precomposed Roman numerals. `Ⅰ` = mutual
  vertex-in-open-edge sliver. `Ⅱ` = obtuse-at-v. `Ⅲ` = exterior-side
  one-sided T (compiled pair; `Ⅲ∨Ⅳ` xor; two witnesses;
  fill token). `Ⅳ` = interior-side stem (compiled residue pair).
  `Ⅴ` is mixed-cone (classified). `Ⅵ` is same-cone (classified).
  Completeness is an unnamed lens pair (not leftover `Ⅶ`).
  `522-n` is not minted.

## Fog

- **Owner sign-off on #522** is paperwork on the epic, not a leftover
  proof. Closing summary: [`522-closing-summary.md`](522-closing-summary.md).
- **Remint order** if asked: disjoint is the sharpest (Qex already
  compiled); contains / touch / overlap follow the same pointer pattern
  and the same shared-pin caution.
- **`Ⅲ`** is compiled as an exterior-side stem
  (`RelateNGComplete.v : onesided_t_pair_inhabits`). The xor
  (`RelateNGTouchOnesided.v : triangle_pair_regime_onesided`) is
  `Ⅲ∨Ⅳ` with two compiled witnesses, not a leftover-`Ⅲ` detector.
  II empty is compiled. BB dim 0 is not. Fill stays `im_unsupported`.
- **`Ⅳ`** is the interior-side stem. Residue pair compiled
  (`RelateNGComplete.v : interior_side_pair_inhabits`;
  `RelateNGTouchOnesided.v : triangle_pair_regime_interior_side`).
  Chart: [`map-interior-side-cert.md`](map-interior-side-cert.md).
  Grill: [`map-interior-side-grill.md`](map-interior-side-grill.md).
  Spec: [`spec-interior-side.md`](spec-interior-side.md). Ticket 26
  closed. Fill stays `im_unsupported`.
- **`Ⅱ`** is compiled (QED). Chart: [`map-obtuse-cert.md`](map-obtuse-cert.md).
  Headline `RelateNGTouchObtuse.v : triangle_pair_regime_obtuse`.
  Ticket 27 closed.
- **`Ⅴ`** is compiled (QED). Chart: [`map-mixed-cone-cert.md`](map-mixed-cone-cert.md).
  Headline `RelateNGTouchMixedCone.v : triangle_pair_regime_mixedcone`.
  Ticket 28 closed.
- **`Ⅵ`** is compiled (inhabitance). Chart: [`map-same-cone-cert.md`](map-same-cone-cert.md).
  Headline `RelateNGTouchSameCone.v : triangle_pair_regime_samecone`.
  Ticket 29 closed. Epic #522 stop is QED ∨ QEX
  (`RelateNGEpic522.v : ticket_522_qed_or_qex`),
  discharged QEX on an unnamed lens. Leftover `Ⅰ`–`Ⅵ` are classified
  (`RelateNGEpic522.v : ticket_522_classified_qed_or_qex`).
  Leftover `Ⅶ` is already #642.

## Frontier

Leftover `Ⅰ` bar 1 is landed. Leftover `Ⅱ` is classified
(`RelateNGTouchObtuse.v : triangle_pair_regime_obtuse`; QED). Leftover
`Ⅲ` and leftover `Ⅳ` are the two compiled witnesses of a `Ⅲ∨Ⅳ`
xor; fill stays `im_unsupported`. Leftover `Ⅴ` is classified
(`RelateNGTouchMixedCone.v : triangle_pair_regime_mixedcone`; QED).
Leftover `Ⅵ` is inhabitance
(`RelateNGTouchSameCone.v : triangle_pair_regime_samecone`; classified).
Epic #522 stop is QED ∨ QEX, discharged QEX on an unnamed lens
(`RelateNGEpic522.v : ticket_522_qed_or_qex`). Leftover `Ⅰ`–`Ⅵ`
are classified (`RelateNGEpic522.v : ticket_522_classified_qed_or_qex`).

```
#522 honesty + wired bar 1/2 ════════════════════ done (#596 wrap-up)

Ⅰ ──────── mutual vertex-in-open-edge sliver ── bar 1 ── TPR_TouchPartialEdge
Ⅱ ─────── obtuse-at-v certificate ── classified ── TPR_TouchObtuse (fill token)
Ⅲ∨Ⅳ xor ── two witnesses ── TPR_TouchOnesided (fill token)
Ⅳ ───── interior-side stem ── residue pair ── TPR_TouchOnesided (fill token)
Ⅴ ─────── mixed-cone certificate ── classified ── TPR_MixedCone (fill token)
Ⅵ ─────── same-cone certificate ── classified ── TPR_SameCone (fill token)
unnamed ── lens pair after leftover Ⅵ ── live completeness cex
unnamed ── TouchEdge exclusivity ── technique ── carve #597 on main
unnamed ── fill remints (4 shared pins) ── sequencing ── not 522-f

#67 / 11 ── geom_de9im_pointset · noding · Touches-vs-Share
#523 ────── F vs not-computed
parked ──── empty/empty

522-n ── not minted
Ⅶ ── unused ── do not mint
```
