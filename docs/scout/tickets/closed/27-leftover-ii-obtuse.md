<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Leftover `Ⅱ` — classify the obtuse-at-v pair

**Type:** task · **Map:** [#522 leftovers](../../map-522-leftovers.md)
**Blocked by:** — · **Closed:** 2026-08-30 (pair classified)
**Spec:** [`map-obtuse-cert.md`](../../map-obtuse-cert.md)
**claimId:** `Ⅱ` · **GitHub:** none · **witness:** `Ⅱ-obtuse-cex`

> Umbrella: leftover `Ⅱ`. Does not retire epic 522. Not leftover
> `Ⅰ`. Not leftover `Ⅲ`. Not leftover `Ⅳ`. Not a `522-*` letter.

## Question

Leftover `Ⅱ` is the compiled #584 / 522-m obtuse-at-v pair
A = `(0,0)(2,0)(0,2)`, B = `(0,0)(-2,0)(1,-1)`. Shared origin.
`cone_separates_b` is false (`side_dot = 0` on `(1,-1)`). Sibling
of the #572 / `522-i` pair (same A; B third vertex `(0,-2)`).
This letter writes a **new boolean**, not a remint of
`cone_separates_b` / `touch_vertex_b`. Completeness must stay
false. Do not mint leftover `Ⅵ`.

## Resolution

**Closed 2026-08-30 with acceptance.** Pair classified.

A = `(0,0)(2,0)(0,2)`, B = `(0,0)(-2,0)(1,-1)`. Both CCW.
Shared origin. Closed cone plus `negb cone_separates_b`
(`RelateNGCore.v : touch_obtuse_vertex_b`). Classifier emits
`TPR_TouchObtuse`
(`RelateNGComplete.v : obtuse_pair_touch_obtuse`;
`RelateNGTouchObtuse.v : triangle_pair_regime_obtuse`).
Fill stays `im_unsupported`. False on `classified_hard_pairs`
(including #572), leftover `Ⅰ`, leftover `Ⅲ`, leftover `Ⅳ`, and
the #567 contains pair. Completeness stays false on an unnamed
CCW pair after leftover `Ⅴ`
(`RelateNGUnnamedCex.v : unnamed_ccw_pair_unsupported`).
Epic #522 stop is QED ∨ QEX
(`RelateNGTouchObtuse.v : triangle_pair_regime_ccw_stop`),
discharged QEX. Leftover `Ⅱ` itself is QED
(`RelateNGTouchObtuse.v : leftover_ii_qed_or_qex`).
`classify_triangle_pair` arm is `True` — leftover `Ⅰ` honesty,
not CONTEXT Bar 1. `cone_separates_b` was not reminted. Epic
`#522` stays OPEN.

## Non-goals

Do not remint `cone_separates_b` / `touch_vertex_b` /
`touch_partial_edge_b` / `touch_onesided_t_b` / `shares_edge_b`.
Do not remint `aa_matrix_*`. Do not emit `FFFF1FFF2` on
`TPR_TouchObtuse`. Do not mint `522-n`. Do not mint `Ⅴ`. Do not
steal leftover `Ⅰ` / `Ⅲ` / `Ⅳ` / `522-j` / `522-m` / `522-f` /
`522-i`. Do not claim completeness or Bar 1. Do not comment on a
GitHub issue unless the user says `comment`.
