# Map — mixed-cone certificate

A wayfinder map. Charted 2026-08-30; compiled 2026-08-30. This is **not**
a GitHub child, **not** a remint of `522-j` / `522-m` / `522-i`, and
**not** leftover `Ⅱ`'s closed-cone vertex kiss
(`map-obtuse-cert.md`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are precomposed
> Roman numerals. This leftover is **`Ⅴ`**. Do not swap it with `Ⅱ`.
> Do not remint ADR-0004. This map does not mint a GitHub child.
> Leftover `Ⅵ` is same-cone inhabitance. Leftover `Ⅶ` is already #642.

topics: relate
claimId: Ⅴ
witness: Ⅴ-mixed-cone-cex

## Destination

**Classify the leftover-Ⅱ completeness residue as leftover `Ⅴ`
without reminting `cone_separates_b` / `touch_obtuse_vertex_b`.**

Ticket #577 asked either completeness (QED) or a documented counterexample
(QEX). Leftover `Ⅴ`'s letter stop is
`RelateNGTouchMixedCone.v : triangle_pair_regime_ccw_stop` (discharged QEX).
The filtered sibling is
`RelateNGTouchMixedCone.v : triangle_pair_regime_ccw_stop_not_tjunction`.
Completeness is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`). The
filtered retry is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
The live cex after leftover `Ⅵ` is an unnamed lens pair (not leftover
`Ⅶ`). Leftover `Ⅴ` itself is QED
(`RelateNGTouchMixedCone.v : leftover_v_qed_or_qex`).
Epic #522 stop is QED ∨ QEX (`RelateNGEpic522.v : ticket_522_qed_or_qex`).

## The pair (compiled)

A = `(0,0)(2,0)(0,2)`, B = `(0,0)(-1,-1)(3,1)`.

Both-CCW: `RelateNGComplete.v : mixed_cone_pair_both_ccw`. Not the
T-junction 12-tuple: `RelateNGComplete.v : mixed_cone_pair_not_tjunction`.
Classifies `TPR_MixedCone`:
`RelateNGComplete.v : mixed_cone_pair_mixedcone`.
Headline: `RelateNGTouchMixedCone.v : triangle_pair_regime_mixedcone`.

Same A as leftover `Ⅱ` and #572 / `522-i`. Leftover `Ⅱ` moves B's
third vertex to `(1,-1)` (`side_dot = 0`). This leftover puts the
remaining B-vertices on **opposite** sides of `nA = (2,2)`:
`side_dot(-1,-1) = -4`, `side_dot(3,1) = 8`.

Detector `RelateNGCore.v : mixed_cone_vertex_b` is opposite-sign
`side_dot` plus `negb cone_separates_b` plus
`negb closed_cone_separates_b`. Not a remint of #572 or leftover `Ⅱ`.

Constructor `TPR_MixedCone` stays on `im_unsupported`
(`RelateMatrixTriangle.v : triangle_pair_fill_touch_mixed_eq`;
`RelateNGOracleSurface.v : triangle_touch_mixed_wire`). Do not emit
`FFFF1FFF2`. `classify_triangle_pair` arm is `True`.

Oracle / harness: `oracle/de9im_triangle_vectors.txt` `REGIME TOUCH_MIXED`
(fill still `UNSUPPORTED`). Decline golden after leftover `Ⅵ` is the
unnamed lens pair A = `(0,0)(3,0)(0,3)`, B = `(2,-1)(2,2)(-1,2)`.

## Nearby pairs that are **not** this leftover

| Pair | What it is | Do not |
|---|---|---|
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)` | Leftover `Ⅱ`. Classified **`TPR_TouchObtuse`**. Product of `side_dot`s is 0. | remint `touch_obtuse_vertex_b` |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(0,-2)` | #572 / `522-i`. Classified **`TPR_TouchVertex`**. Same-sign opposite cone. | remint `cone_separates_b` / steal `522-i` |
| `(0,0)(2,0)(0,2)` vs `(0,0)(3,1)(1,3)` | Leftover `Ⅵ` same-sign spill. Inhabits **`TPR_SameCone`**. Not a denotation. `RelateNGUnnamedCex.v : same_cone_pair_samecone`. | steal leftover `Ⅵ` |
| `(0,0)(3,0)(0,3)` vs `(2,-1)(2,2)(-1,2)` | Unnamed completeness cex on leftover `Ⅵ`. Lens; interiors meet; no shared vertex. Already written as leftover `Ⅶ` / #642. | steal leftover `Ⅶ` |

Leftover `Ⅶ` is already written as #642. Epic `#522` stays OPEN.
