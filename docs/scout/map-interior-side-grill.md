<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Grill — leftover `Ⅳ` (interior-side stem)

A grilling record. Charted 2026-08-30. This is **not** leftover `Ⅰ`,
**not** leftover `Ⅱ`, **not** leftover `Ⅲ`, and **not** a second copy
of [`map-interior-side-cert.md`](map-interior-side-cert.md) (#629). It
does **not** invent a 12-tuple. It does **not** invent a
side-distinguishing detector. It does **not** remint
`RelateNGCore.v : touch_onesided_t_b`.

> Research chart: [`map-interior-side-cert.md`](map-interior-side-cert.md)
> (#629). Leftover `Ⅲ` compile is #628. Ticket 26 compiled the
> residue pair. This grill is the compile-letter tense: named;
> inhabited; the xor is a `Ⅲ∨Ⅳ` configuration class with two
> compiled witnesses (one constructor, one fill token, one `True`
> arm — not a side-aware detector). `overlap_b` may steal other
> same-side stems. CONTEXT Bar 1 is not met. It does not write a
> second detector. Completeness is mixed-cone.

topics: relate
claimId: Ⅳ
witness: Ⅳ-interior-side-cex

## Destination

**Verify leftover `Ⅳ` against the leftover-`Ⅲ` compile and against
CONTEXT.** Name what holds. Park what does not. Ticket 26 compiled
the residue pair. Do not invent a side-distinguishing detector.

## Verdict

The family is named. Ticket 26 compiled the residue pair
(`RelateNGComplete.v : interior_side_pair_inhabits`). The compiled leftover-`Ⅳ` 12-tuple is
`(0,0)(2,0)(0,1)` vs `(1,0)(5/4,1/4)(3/4,1/4)`.
Leftover `Ⅲ` remains the exterior-side pair
(`RelateNGComplete.v : onesided_t_pair_inhabits`) — II empty
(`RelateNGComplete.v : onesided_t_ii_empty`). The xor
(`RelateNGCore.v : touch_onesided_t_b`) is a `Ⅲ∨Ⅳ` configuration
class with two compiled witnesses
(`RelateNGTouchOnesided.v : triangle_pair_regime_onesided` and
`RelateNGTouchOnesided.v : triangle_pair_regime_interior_side`).
One constructor, one fill token, one `True` arm. It is not
side-aware and not a partition of one-sided T's. Ticket 22's
leftover-`Ⅲ` bar is met. “Detector for leftover `Ⅲ`” is not.

`overlap_b` sits earlier (`RelateNGCore.v : overlap_b`;
`RelateNGCore.v : triangle_pair_regime`). On this pair: stem
`gtri A = 0`, remaining B vertices `gtri A > 0`, none `gtri A < 0`.
Vertex-stab misses. `contains_b` misses because the stem sits on
`∂A`. II is nonempty at `(1, 1/6)` — compiled. So: DE-9IM overlap,
`overlap_b` false. That is the residue, and the reason the fill
token is load-bearing. Same-side stems that do have an exterior
B-vertex remain leftover `522-b`. Completeness stays false on leftover
`Ⅱ` (`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`).
A second `TPR_TouchOnesided` witness does not touch that theorem.
CONTEXT **Bar 1** needs a designated witness matrix. There is none.
`classify_triangle_pair` stays `True`. Fill stays
`im_unsupported` (`RelateNGTouchOnesided.v : onesided_fill_still_unsupported`).
This is a **research park** (ADR-0002). Regime reachability is not
Bar 1.

## Claims grilled live

### 1. Residue pair compiled (ticket 26)

**Closed by ticket 26.** The leftover-`Ⅲ` pair remains
exterior-side (`RelateNGComplete.v : onesided_t_pair_inhabits`).
The interior-side 12-tuple is
`RelateNGComplete.v : interior_side_pair_inhabits`. The other compiled leftovers are leftover `Ⅰ`
(`RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`)
and leftover `Ⅱ`
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
`classified_hard_pairs` is four rows. None of those is this family.

### 2. Leftover `Ⅲ` is the opposite-side witness, not this leftover

**Confirmed.**

| Finding | Leftover | Why not `Ⅳ` |
|---|---|---|
| `RelateNGComplete.v : onesided_t_pair_inhabits` | `Ⅲ` | Exterior-side. Contact `(1,0)` on A's base `y = 0`. II empty (`RelateNGComplete.v : onesided_t_ii_empty`). There is no `onesided_t_bb_dim0`. |
| `RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial` | `Ⅰ` | Mutual. Same-side sliver. II = 2, BB = 1. |
| `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction` | `Ⅱ` | Shared vertex; cone `side_dot = 0`. |

### 3. The xor is `Ⅲ∨Ⅳ`, not a leftover-`Ⅳ` detector

**Confirmed.** `RelateNGCore.v : touch_onesided_t_b` is
`xorb (some_vertex_on_open_edges A B) (some_vertex_on_open_edges B A)`.
No side test. True on leftover `Ⅲ`. True on leftover `Ⅳ`
(`RelateNGComplete.v : interior_side_onesided_true`). Classifier order
(`RelateNGCore.v : triangle_pair_regime`) emits `TPR_TouchOnesided`
for any xor-true pair that missed the earlier arms. Do **not** remint
the xor. A side-distinguishing boolean, if asked later, tests the
side of the supporting line **after** the xor.

### 4. `overlap_b` may steal same-side stems

**Confirmed, and not flattened on this pair.** `RelateNGCore.v : overlap_b`
needs a B-vertex with `0 < gtri A` and a B-vertex with `gtri A < 0`,
plus a vertex of A strictly exterior to B. This pair: stem
`gtri A = 0` (`RelateNGComplete.v : interior_side_gtri_A_stem`);
remaining B vertices `gtri A > 0`
(`interior_side_gtri_A_e` / `interior_side_gtri_A_f`); none
`gtri A < 0`. So `overlap_b` is false
(`RelateNGComplete.v : interior_side_overlap_b_false`) while II is
nonempty (`interior_side_ii_nonempty`) — DE-9IM overlap, detector
miss. Same-side stems that do have an exterior B-vertex remain
leftover `522-b`
(`RelateNGComplete.v : classified_overlap_pair`). Emitting
`FF2F11212` on `TPR_TouchOnesided` would still mix leftover `Ⅲ`
(II empty) with this pair.

| Detector | Why it is the wrong tool for leftover `Ⅳ` |
|---|---|
| `touch_edge_b` | `RelateNGCore.v : shares_edge_b` is endpoint-pair equality. A T is not a full shared edge. |
| `contains_b` | Needs `0 < gtri A` at every B-vertex. A stem on the supporting line has `gtri = 0`. |
| `overlap_b` | May fire. Those pairs are leftover `522-b`. |
| `separated_b` | A supporting-edge separator is a disjoint witness. A T is contact. |
| `touch_vertex_b` | Needs a shared vertex and `RelateNGCore.v : cone_separates_b`. This family has **no** shared vertex. |
| `touch_partial_edge_b` | Mutual. Leftover `Ⅰ`. This family is one-sided. |
| `touch_onesided_t_b` | True on leftover `Ⅲ` and leftover `Ⅳ`. No side test. |

### 5. CONTEXT Bar 1 is not applicable

**Confirmed miss — not a failed bar, an absent subject.** Bar 1 needs
a classified leftover-`Ⅳ` pair **and** a designated witness matrix.
The pair is compiled (`RelateNGComplete.v : interior_side_pair_inhabits`).
There is no leftover-`Ⅳ` matrix. The constructor is already on
`im_unsupported`. `classify_triangle_pair` arm for
`TPR_TouchOnesided` is `True` — leftover `Ⅰ` honesty, not CONTEXT
Bar 1. Nothing that mentions `TPR_TouchOnesided` may be proved
through `classify_triangle_pair`. Decline golden is mixed-cone.
Do not emit `FFFFFFFFF`. Do not emit `FFFF1FFF2` or `FF2F11212` on
`TPR_TouchOnesided` — leftover `Ⅲ` looks like areal Touches,
leftover `Ⅳ` looks like overlap. The fill token is the only thing
keeping those families from mixing.

### 6. Residue inhabited

**Closed by ticket 26.** The residue pair reaches
`TPR_TouchOnesided` (`RelateNGTouchOnesided.v : triangle_pair_regime_interior_side`).
`overlap_b` is false (`RelateNGComplete.v : interior_side_overlap_b_false`).
II nonempty (`RelateNGComplete.v : interior_side_ii_nonempty`).
Not a designated matrix. Not CONTEXT Bar 1.

## Parks (ADR-0002)

- **Research:** residue pair compiled
  (`RelateNGComplete.v : interior_side_pair_inhabits`).
- **Sequencing:** side-distinguishing detector, constructor split,
  fill. All gated on the research park **and** an owner ask. The xor
  is already compiled. Do not invent a second detector as the first
  implement letter.
- **Technique:** none. There is no leftover-`Ⅳ` detector statement
  to grill.

## Not this leftover

Not leftover `Ⅰ` / #609. Not leftover `Ⅱ` / #611. Not leftover
`Ⅲ` / #628. Not #570 overlap. Not #572 TouchVertex. Not line×line
IB. Not a remint of `aa_matrix_*`. Not a remint of
`touch_onesided_t_b`. Do not mint `522-n`. Do not mint `Ⅴ`. Do not
steal `522-j` / `522-m` / `522-f` / `522-i` / `522-b`.

## If `/implement Ⅳ` is asked

Ticket 26 compiled the residue. Do not remint the xor. Do not remint
the fill. Do not call regime reachability CONTEXT Bar 1.
Completeness stays false on mixed-cone. This letter does not
move that theorem.

## Decisions so far

- Family named — #629 / [`map-interior-side-cert.md`](map-interior-side-cert.md).
- Leftover `Ⅲ` compile — #628 /
  `RelateNGTouchOnesided.v : triangle_pair_regime_onesided`.
  `Ⅲ∨Ⅳ` xor, two witnesses, fill token, completeness mixed-cone.
- This grill — named; Bar 1 not applicable (no matrix).
- Ticket 26 — residue pair
  `RelateNGComplete.v : interior_side_pair_inhabits`.
- Spec / tickets — [`spec-interior-side.md`](spec-interior-side.md);
  scout 23–26 closed.

## Frontier

```
family named ── #629 ── map-interior-side-cert.md
     residue pair ── interior_side_pair_inhabits
     this grill ── confirmed against the leftover-Ⅲ compile

Ⅳ ── research #629 ── grill (this file) ── spec-interior-side.md
     tickets 23–26 closed ── residue pair compiled
     xor already Ⅲ∨Ⅳ ── do not invent a detector

Ⅰ ── mutual same-side sliver ── #609 ── not this leftover
Ⅱ ── obtuse-at-v ── TPR_TouchObtuse ── not this leftover
Ⅲ ── exterior-side stem ── #628 ── Ⅲ∨Ⅳ xor, two witnesses

522-n ── not minted
Ⅴ ── unused ── ask before assigning
```
