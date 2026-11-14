<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Spec — leftover `Ⅳ` (interior-side stem)

A takeable implementation spec. Written 2026-08-30 from the grill
([`map-interior-side-grill.md`](map-interior-side-grill.md)) plus the
research chart ([`map-interior-side-cert.md`](map-interior-side-cert.md),
#629) and the leftover-`Ⅲ` compile (#628). This is **not** leftover
`Ⅰ`, **not** leftover `Ⅱ`, **not** leftover `Ⅲ`, and **not** a remint
of `522-n`. It does **not** invent a 12-tuple. It does **not** invent
a side-distinguishing detector. It does **not** retire epic 522.

> `/implement Ⅳ` is the later letter. That letter must not treat
> a prose sketch as the spec pair. The xor is already compiled.

topics: relate
claimId: Ⅳ
witness: Ⅳ-interior-side-cex

## Destination

**Compiled.** Residue pair
`RelateNGComplete.v : interior_side_pair_inhabits`. Headline
`RelateNGTouchOnesided.v : triangle_pair_regime_interior_side`.
A = `(0,0)(2,0)(0,1)`, B = `(1,0)(5/4,1/4)(3/4,1/4)`. Both CCW.
Same-side (`RelateNGComplete.v : interior_side_same_side`).
`overlap_b` false (`RelateNGComplete.v : interior_side_overlap_b_false`).
II nonempty (`RelateNGComplete.v : interior_side_ii_nonempty`).
The xor (`RelateNGCore.v : touch_onesided_t_b`) emits
`TPR_TouchOnesided`. Fill stays `im_unsupported`. Completeness stays
false (`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`).

CONTEXT **Regime** reachability is witness-scoped
(`RelateNGComplete.v : interior_side_pair_onesided`). CONTEXT **Bar 1**
is not met: the pair is classified, but there is no designated
witness matrix, and `classify_triangle_pair` stays `True`. Same
honesty as leftover `Ⅰ` #609 and leftover `Ⅲ` #628. Do not call
that stop CONTEXT Bar 1. Do not write a second detector.

## Why the grill is the source, not a re-grill

The grill confirmed six claims against the leftover-`Ⅲ` compile.
Do not re-verify them unless the tree moved:

| Claim | Where |
|---|---|
| Leftover-`Ⅳ` residue pair | `RelateNGComplete.v : interior_side_pair_inhabits` |
| Leftover `Ⅲ` is opposite-side | `RelateNGComplete.v : onesided_t_ii_empty` |
| Xor is `Ⅲ∨Ⅳ` | `RelateNGCore.v : touch_onesided_t_b` |
| `overlap_b` may steal | `RelateNGCore.v : overlap_b`; leftover `522-b` |
| Bar 1 not applicable | CONTEXT; pair compiled, no leftover-`Ⅳ` matrix |
| Residue inhabited | `RelateNGComplete.v : interior_side_pair_inhabits` |

## Family (acceptance predicate, not a pair)

A later compiled 12-tuple inhabits leftover `Ⅳ` only if **all** of
the following hold. This list is the filter. It is not a sketch of
coordinates.

1. Both triangles are CCW.
2. A vertex of one sits in the **open interior** of an edge of the
   other (endpoints out; strict on-edge, not a shared vertex).
3. The contact is **not mutual** (leftover `Ⅰ`'s
   `touch_partial_edge_b` stays false).
4. The triangles share **no vertex** (leftover `Ⅱ` / `522-i` stay
   out).
5. Remaining vertices of the stemmed triangle sit on the **same
   side** of the supporting line as the other triangle's interior
   (leftover `Ⅲ` is opposite-side; `RelateNGComplete.v : onesided_t_ii_empty`
   stays out).
6. `overlap_b` is false (`RelateNGCore.v : overlap_b`). A same-side
   stem that fires this arm is leftover `522-b`, not leftover `Ⅳ`.
7. The tuple is not a `classified_hard_pairs` row, not leftover `Ⅰ`,
   not leftover `Ⅱ`, not leftover `Ⅲ`, not the RelatePrepared CW
   12-tuple.

Do not write those seven bullets as a 12-tuple in this spec.
Typically II is nonempty. Prove II empty before calling the pair
areal Touches. There is no `onesided_t_bb_dim0`.

## Slices for `/implement Ⅳ`

One letter. There is no detector slice.

### Slice A — compile a residue cex, or prove emptiness

**Today.** Residue pair compiled
(`RelateNGComplete.v : interior_side_pair_inhabits`). Completeness
false on leftover `Ⅱ`. The xor is already compiled and fires on
this pair. Do not remint it.

**After this slice.** Landed as (1):

1. A named 12-tuple in `RelateNGComplete.v` that satisfies the family
   filter, with a finding that the classifier emits
   `TPR_TouchOnesided` (`RelateNGCore.v : touch_onesided_t_b` is
   already true on any xor-true pair that missed the earlier arms).
   Both-CCW proofs sit next to the coords. Record that the pair is
   interior-side (same side of the supporting line). **or**
2. A theorem that every both-CCW same-side one-sided T is already
   classified by `overlap_b` / `contains_b` / leftover `Ⅰ`.

Do **not** invent the tuple in a comment and treat it as compiled.
Do **not** remint `RelateNGCore.v : touch_onesided_t_b`. Do **not**
emit `FFFFFFFFF` / `FFFF1FFF2` / `FF2F11212`. Do **not** move the
decline golden unless the golden pair itself classifies. Do **not**
remint leftover `Ⅰ` or leftover `Ⅲ` fills. A side-distinguishing
boolean is a later leftover, and only if asked. Next unused is `Ⅴ`.

## Parks (ADR-0002)

- **Research (slice A).** Residue pair compiled.
- **Sequencing.** Side-distinguishing detector, constructor split,
  fill. Gated on slice A **and** an owner ask.
- **Technique.** None.

## Non-goals

Do not invent a 12-tuple. Do not remint the xor. Do not remint the
fill. Do not claim CONTEXT Bar 1. Do not prove leftover-`Ⅳ` facts
through `classify_triangle_pair`. Do not steal leftover `Ⅰ` /
leftover `Ⅱ` / leftover `Ⅲ` / `522-j` / `522-m` / `522-f` /
`522-b` / `522-i`. Do not mint `522-n`. Do not mint `Ⅴ`.
