# Leftover `Ⅵ` — name the leftover-Ⅴ same-sign cone spill

**Type:** task
**Blocked by:** leftover `Ⅴ` (ticket 28 / PR #638)
**Spec:** [`map-same-cone-cert.md`](../../map-same-cone-cert.md)
**claimId:** `Ⅵ` · **GitHub:** none · **witness:** `Ⅵ-same-cone-cex`

## Ask

Name the leftover-`Ⅴ` completeness residue
A = `(0,0)(2,0)(0,2)`, B = `(0,0)(3,1)(1,3)` as leftover `Ⅵ`.
Accept as leftover-Ⅵ inhabitance. Reject as a same-cone theorem or
an overlap remint. Do not remint `cone_separates_b` /
`mixed_cone_vertex_b` / `touch_obtuse_vertex_b` / `overlap_b`.
Do not emit `2FFF1FFF2` or `FFFF1FFF2`. Do not steal `522-j` /
`522-m`. Leftover `Ⅶ` is already written as #642; this letter
does not mint it. Do not merge leftover `Ⅴ` or this letter unless
asked.

## Resolution

Inhabitance. Detector `RelateNGCore.v : same_cone_vertex_b` is
both-strict-pos plus `negb` of both cones and of
`mixed_cone_from_v`. Classifier reaches `TPR_SameCone`
(`RelateNGUnnamedCex.v : same_cone_pair_samecone`;
`RelateNGTouchSameCone.v : triangle_pair_regime_samecone`).
Headline is inhabitance, not soundness. Fill stays
`im_unsupported`. `classify_triangle_pair` arm is `True` — no
denotation. There is no `TPR_SameCone ⇒ interiors meet`.
`overlap_b` stays a vertex-stab certificate. Epic #522 stop is
the #577 disjunction copied here
(`RelateNGTouchSameCone.v : triangle_pair_regime_ccw_stop`),
discharged QEX on an unnamed lens
(`RelateNGUnnamedCex.v : unnamed_ccw_pair_unsupported`).
`leftover_vi_qed_or_qex` is classified ∨ declined on the pair just
classified. `classified_hard_pairs_still_samecone` is misnamed
(those pairs stay Disjoint / Overlap / TouchVertex / TouchEdge).

Do not remint leftover
`Ⅰ` / `Ⅱ` / `Ⅲ` / `Ⅳ` / `Ⅴ` / `522-j` / `522-m` / `522-f` /
`522-i`. Do not mint `522-n`. Leftover `Ⅶ` is already #642.
Do not merge this letter to `main`.
