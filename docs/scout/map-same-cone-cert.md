# Map — leftover `Ⅵ` same-sign cone spill

A wayfinder map. Charted 2026-08-30; compiled 2026-08-30. This is **not**
a GitHub child, **not** a remint of `522-j` / `522-m` / `522-i`, and
**not** leftover `Ⅴ`'s opposite-sign cone
(`map-mixed-cone-cert.md`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are precomposed
> Roman numerals. This leftover is **`Ⅵ`**. Do not swap it with `Ⅴ`.
> Do not remint ADR-0004. This map does not mint a GitHub child.
> Leftover `Ⅶ` is already written as #642; this letter does not mint it.

topics: relate
claimId: Ⅵ
witness: Ⅵ-same-cone-cex

## Destination

**Name the leftover-Ⅴ completeness residue as leftover `Ⅵ`.**
Accept as leftover-Ⅵ inhabitance. Reject as a same-cone theorem or
an overlap theorem.

Ticket #577 asked either completeness (QED) or a documented counterexample
(QEX). Relocating
`RelateNGTouchSameCone.v : triangle_pair_regime_ccw_stop` here does **not**
move epic #522 closer to QED — the #577 disjunction copied into a third
file. Completeness is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`). The
filtered retry is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
The live cex is an unnamed lens pair. Leftover `Ⅶ` is already #642.
`leftover_vi_qed_or_qex` is classified ∨ declined on the pair this
letter just classified.

## The pair (compiled)

A = `(0,0)(2,0)(0,2)`, B = `(0,0)(3,1)(1,3)`.

Inhabits `TPR_SameCone`:
`RelateNGUnnamedCex.v : same_cone_pair_samecone`.
Headline: `RelateNGTouchSameCone.v : triangle_pair_regime_samecone`
(inhabitance, not soundness).

Same A as leftover `Ⅴ`, leftover `Ⅱ`, and #572 / `522-i`. Leftover
`Ⅴ` moves B's third vertex to `(−1,−1)` (opposite-sign `side_dot`).
This leftover puts both remaining B-vertices on the **same** side of
`nA = (2,2)`: `side_dot(3,1) = 8`, `side_dot(1,3) = 8`. Both remaining
A-vertices are likewise both-pos vs `nB`. Interiors meet at `(0.5,0.5)`;
`overlap_b` is still a vertex-stab certificate and misses (no vertex
strictly inside the other). That is leftover policy, not a cone theorem.

Detector `RelateNGCore.v : same_cone_vertex_b` is both-strict-pos plus
`negb cone_separates_b` plus `negb closed_cone_separates_b` plus
`negb mixed_cone_from_v`. Not a remint of #572, leftover `Ⅱ`, or
leftover `Ⅴ`. The `negb mixed_cone_from_v` is classifier order written
twice (`mixed_cone_from_v` is already exclusive of `both_strict_pos`).
Harmless, not content.

Constructor `TPR_SameCone` stays on `im_unsupported`
(`RelateMatrixTriangle.v : triangle_pair_fill_touch_samecone_eq`;
`RelateNGOracleSurface.v : triangle_touch_samecone_wire`). Do not emit
`2FFF1FFF2`. `classify_triangle_pair` arm is `True` — no denotation.
There is no `TPR_SameCone ⇒ interiors meet`.

Oracle / harness: `oracle/de9im_triangle_vectors.txt` `REGIME SAME_CONE`
(fill still `UNSUPPORTED`). Decline golden is the unnamed lens pair
A = `(0,0)(3,0)(0,3)`, B = `(2,-1)(2,2)(-1,2)`.

`classified_hard_pairs_still_samecone` is misnamed: those pairs stay
Disjoint / Overlap / TouchVertex / TouchEdge.

## Nearby pairs that are **not** this leftover

| Pair | What it is | Do not |
|---|---|---|
| `(0,0)(2,0)(0,2)` vs `(0,0)(-1,-1)(3,1)` | Leftover `Ⅴ`. Classified **`TPR_MixedCone`**. Opposite-sign `side_dot`. `RelateNGComplete.v : mixed_cone_pair_mixedcone`. | remint `mixed_cone_vertex_b` |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)` | Leftover `Ⅱ`. Classified **`TPR_TouchObtuse`**. Product of `side_dot`s is 0. | remint `touch_obtuse_vertex_b` |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(0,-2)` | #572 / `522-i`. Classified **`TPR_TouchVertex`**. Same-sign opposite cone. | remint `cone_separates_b` / steal `522-i` |
| `(0,0)(3,0)(0,3)` vs `(2,-1)(2,2)(-1,2)` | Unnamed completeness cex on this letter. Lens; interiors meet; no shared vertex. Already written as leftover `Ⅶ` / #642. | steal leftover `Ⅶ` |

Leftover `Ⅶ` is already written as #642. Epic `#522` stays OPEN.
Do not merge this letter to `main`.
