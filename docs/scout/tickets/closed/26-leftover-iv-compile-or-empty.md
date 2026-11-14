<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Leftover `Ⅳ` — compile a residue cex or prove emptiness

**Type:** task · **Map:** [#522 leftovers](../../map-522-leftovers.md)
**Blocked by:** — · **Closed:** 2026-08-30 (residue pair compiled)
**Spec:** [`spec-interior-side.md`](../../spec-interior-side.md) slice A
**claimId:** `Ⅳ` · **GitHub:** none · **witness:** `Ⅳ-interior-side-cex`

> Umbrella: leftover `Ⅳ`. Does not retire epic 522. Not leftover
> `Ⅰ`. Not leftover `Ⅱ`. Not leftover `Ⅲ`. Not a `522-*` letter.

## Question

Leftover `Ⅳ` is a named family that had **no** compiled 12-tuple
at ask time. The xor (`RelateNGCore.v : touch_onesided_t_b`) was
already a `Ⅲ∨Ⅳ` configuration class with leftover `Ⅲ` compiled
(#628). `overlap_b` may steal same-side stems (those are leftover
`522-b`). This letter compiles a residue witness or proves the
residue empty. Do not invent the tuple in a comment and treat it as
compiled. Do not remint the xor. Do not invent a detector.

## Resolution

**Closed 2026-08-30 with acceptance (1).** Residue pair compiled.

A = `(0,0)(2,0)(0,1)`, B = `(1,0)(5/4,1/4)(3/4,1/4)`. Both CCW.
Same A and contact as leftover `Ⅲ`; remaining B vertices sit on
the interior side of `y = 0`
(`RelateNGComplete.v : interior_side_same_side`). Not mutual.
No shared vertex. Stem `gtri A = 0`; remaining B vertices
`gtri A > 0`; none `gtri A < 0`. So `overlap_b` false
(`RelateNGComplete.v : interior_side_overlap_b_false`) while II is
nonempty (`RelateNGComplete.v : interior_side_ii_nonempty`) —
DE-9IM overlap, detector miss. Classifier emits
`TPR_TouchOnesided`
(`RelateNGComplete.v : interior_side_pair_inhabits`;
`RelateNGTouchOnesided.v : triangle_pair_regime_interior_side`).
One constructor, one fill token, one `True` arm — not a side-aware
detector. Fill stays `im_unsupported`. Completeness stays false on
leftover `Ⅱ`. The xor was not reminted. Not CONTEXT Bar 1
(regime reachability is not a designated matrix). Epic `#522`
stays OPEN.

## Non-goals

Do not invent a prose 12-tuple and treat it as compiled. Do not
write a detector. Do not remint `touch_onesided_t_b` /
`touch_partial_edge_b` / `cone_separates_b` / `shares_edge_b` /
`overlap_b`. Do not remint `aa_matrix_*`. Do not mint `522-n`.
Do not mint `Ⅴ`. Do not steal leftover `Ⅰ` / `Ⅱ` / `Ⅲ` /
`522-j` / `522-m` / `522-f` / `522-b` / `522-i`. Do not pile onto
#609, #611, #628, #629, or a `508-*` branch. Do not comment on a
GitHub issue unless the user says `comment`.
