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

Wired bar 1 → bar 2 done ([`522-closing-summary.md`](522-closing-summary.md)).
`Ⅰ`–`Ⅸ` classified (`RelateNGEpic522.v : ticket_522_classified_qed_or_qex` LEFT).
Completeness QEX after `Ⅸ` (`RelateNGEpic522.v : ticket_522_qed_or_qex` RIGHT).
Epic stays open. Do not mint `Ⅹ` / `522-n`.

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
detector. Do not mint leftover `Ⅹ`.

## Leftover table

Parks follow ADR-0002 (`CONTEXT.md`): sequencing / research / technique.
Value and priority are orthogonal.

| Id | Leftover | Kind | Park | Status | Do not |
|---|---|---|---|---|---|
| `Ⅰ` | Mutual vertex-in-open-edge sliver | #522-adjacent | research | Bar 1 landed. Chart: [`map-tjunction-cert.md`](map-tjunction-cert.md). Headline `RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`. Pair `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)`. Compiled pair is II = 2, BB = 1 — a sliver, not a kiss. Fill stays `im_unsupported`. | steal `522-j` / `522-m` / `522-f`; remint fills; bucket obtuse under `Ⅰ`; mint `522-n` |
| — | TouchEdge exclusivity vs the four gtri predicates | #522-adjacent | technique | Named leftover, no numeral. Carved by #597 (`522-a-touch-edge-carve`), not proved. | treat the carve as exclusivity; remint frozen anchors |
| — | Classifier fill remints (`aa_matrix_*` → `*_ogc`) | #522-adjacent | sequencing | Unnamed. Four shared pins; disjoint blocked by `pat_disjoint`. Not `522-f`. | remint in a harness letter; steal `522-f` / `522-d` / `522-h` |
| `Ⅱ` | Obtuse-at-v certificate | #522-adjacent | research | Classified. `RelateNGTouchObtuse.v : leftover_ii_qed_or_qex`. Chart: [`map-obtuse-cert.md`](map-obtuse-cert.md). Fill `im_unsupported`. | remint #572; emit `FFFF1FFF2`; mint `522-n` / `Ⅹ` |
| `Ⅲ` | Exterior-side one-sided T | #522-adjacent | research | `RelateNGTouchOnesided.v : triangle_pair_regime_onesided`. `Ⅲ∨Ⅳ` xor. Fill `im_unsupported`. | remint `Ⅰ`/`Ⅳ`; claim Bar 1; mint `522-n` / `Ⅹ` |
| `Ⅳ` | Interior-side stem | #522-adjacent | research | `RelateNGTouchOnesided.v : triangle_pair_regime_interior_side`. `RelateNGComplete.v : interior_side_pair_inhabits`. Fill `im_unsupported`. | steal `Ⅲ`; claim Bar 1; mint `522-n` / `Ⅹ` |
| `Ⅴ` | Mixed-cone certificate | #522-adjacent | research | `RelateNGTouchMixedCone.v : leftover_v_qed_or_qex`. Chart: [`map-mixed-cone-cert.md`](map-mixed-cone-cert.md). Fill `im_unsupported`. | remint `Ⅱ`; mint `522-n` / `Ⅹ` |
| `Ⅵ` | Same-sign cone spill | #522-adjacent | research | Classified. `RelateNGTouchSameCone.v : leftover_vi_qed_or_qex` (`TPR_SameCone`). Fill `im_unsupported`. | remint leftover `Ⅴ`; mint `522-n` / `Ⅹ` |
| `Ⅶ` | Edge-cross residue | #522-adjacent | research | Classified. `RelateNGTouchLens.v : leftover_vii_qed_or_qex` (`TPR_Lens`). Fill `im_unsupported`. | remint leftover `Ⅵ`; mint `522-n` / `Ⅹ` |
| `Ⅷ` | Nested containment | #522-adjacent | research | Classified. `RelateNGTouchInside.v : leftover_viii_qed_or_qex` (`TPR_Inside`). Fill `im_unsupported`. | remint contains; mint `522-n` / `Ⅹ` |
| `Ⅸ` | Same-side shared-edge nest | #522-adjacent | research | Classified. `RelateNGTouchNest.v : leftover_ix_qed_or_qex` (`TPR_Nest`). Completeness QEX after this (`RelateNGEpic522.v : ticket_522_qed_or_qex` RIGHT). | remint leftover `Ⅷ`; mint leftover `Ⅹ` / `522-n` |
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
  moved it to mixed-cone; leftover `Ⅴ` moved it to an unnamed CCW pair.
- Wrap-up — #596. Owner sign-off still required.
- #567 DoD met; TouchEdge exclusivity carved on `main` via #597, not proved.
- #589 wayfinder PR stays closed. Do not mint `Ⅹ` / `522-n`.

## Fog

- **Owner sign-off on #522** is paperwork on the epic, not a leftover
  proof. Closing summary: [`522-closing-summary.md`](522-closing-summary.md).
- **Remint order** if asked: disjoint is the sharpest (Qex already
  compiled); contains / touch / overlap follow the same pointer pattern
  and the same shared-pin caution.

## Frontier

```
#522 honesty + wired bar 1/2 ════════════════════ done (#596 wrap-up)

Ⅰ–Ⅸ ── classified ── ticket_522_classified_qed_or_qex LEFT
unnamed ── CCW pair after leftover Ⅸ ── ticket_522_qed_or_qex RIGHT
unnamed ── TouchEdge exclusivity ── technique ── carve #597 on main
unnamed ── fill remints (4 shared pins) ── sequencing ── not 522-f

#67 / 11 ── geom_de9im_pointset · noding · Touches-vs-Share
#523 ────── F vs not-computed
parked ──── empty/empty

522-n / Ⅹ ── not minted
```
