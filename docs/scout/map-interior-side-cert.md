<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Map — leftover `Ⅳ` interior-side one-sided T

A wayfinder map. Charted 2026-08-30. This is **not** a GitHub child,
**not** a remint of leftover `Ⅰ` / leftover `Ⅲ` / `522-j` / `522-m`
/ `522-f`, **not** leftover `Ⅱ`'s obtuse-at-v certificate, and **not**
the line×line noding T-junction
(`RelateNodingLineLineMeet.v : segments_int_bnd_touches_ib_cell`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are precomposed
> Roman numerals. This leftover is **`Ⅳ`**. The mutual vertex-in-open-edge
> sliver is **`Ⅰ`**. Obtuse-at-v is **`Ⅱ`**. The exterior-side one-sided
> T is **`Ⅲ`**. The xor is `Ⅲ∨Ⅳ` with two compiled witnesses
> (one constructor, one fill token, one `True` arm — not a
> side-aware detector). Do not swap them. Do not remint ADR-0004.
> This map does not mint a GitHub child. Next unused is **`Ⅴ`**
> — ask before assigning.

topics: relate
claimId: Ⅳ
witness: Ⅳ-interior-side-cex

## Destination

**Name the interior-side family. Residue pair compiled
(`RelateNGComplete.v : interior_side_pair_inhabits`).**

Leftover `Ⅲ` compiled an **exterior-side** stem
(`RelateNGComplete.v : onesided_t_pair_inhabits`). Interiors sit on
**opposite** sides of the supporting line, so II is empty
(`RelateNGComplete.v : onesided_t_ii_empty`). The xor
(`RelateNGCore.v : touch_onesided_t_b`) does not test that side. This
map assigns leftover **`Ⅳ`** to the **same-side** one-sided T.
Ticket 26 compiled the residue pair
(`RelateNGComplete.v : interior_side_pair_inhabits`). It does
**not** invent a side-distinguishing detector. Completeness stays
false (`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`).

## The family (not a spec pair)

A vertex of one both-CCW triangle sits in the **open interior** of an
edge of the other. The contact is **not mutual**. The triangles share
**no vertex**. The remaining vertices of the stemmed triangle sit on
the **same side** of the supporting line as the other triangle's
interior.

That is leftover `Ⅰ`'s same-side geometry without leftover `Ⅰ`'s
mutual open-edge hit, and leftover `Ⅲ`'s one-sided hit without
leftover `Ⅲ`'s opposite-side II emptiness.

| Leftover | Contact | Sides of the supporting line | II |
|---|---|---|---|
| `Ⅰ` | mutual | same side | nonempty sliver (`RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`) |
| `Ⅲ` | one-sided | opposite sides | empty (`RelateNGComplete.v : onesided_t_ii_empty`) |
| `Ⅳ` | one-sided | same side | typically nonempty |

The xor (`RelateNGCore.v : touch_onesided_t_b`) is true on leftover
`Ⅲ` and leftover `Ⅳ`
(`RelateNGComplete.v : interior_side_onesided_true`). It does not
distinguish the rows. Classifier order
(`RelateNGCore.v : triangle_pair_regime`) emits
`TPR_TouchOnesided` for any xor-true pair that missed the earlier
arms. Fill stays `im_unsupported`
(`RelateNGTouchOnesided.v : onesided_fill_still_unsupported`).

Residue pair: A = `(0,0)(2,0)(0,1)`, B = `(1,0)(5/4,1/4)(3/4,1/4)`
(`RelateNGComplete.v : interior_side_pair_inhabits`).

A same-side stem with one remaining vertex strictly interior and
another strictly exterior is leftover `522-b`
(`RelateNGCore.v : overlap_b`), not this leftover.

## Why leftover `Ⅰ`, leftover `Ⅱ`, and leftover `Ⅲ` exclude it

| Leftover | Why it is not `Ⅳ` |
|---|---|
| `Ⅰ` | Mutual. Both bottoms share a positive-length open-closed segment. Headline `RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`. Same-side sliver; II nonempty. The detector is `touch_partial_edge_b`, not the xor. |
| `Ⅱ` | Shared vertex; cone `side_dot = 0`. Classified `RelateNGTouchObtuse.v : triangle_pair_regime_obtuse`. Not a vertex-in-open-edge T. |
| `Ⅲ` | One-sided, **opposite** sides. Compiled pair `(0,0)(2,0)(0,1)` vs `(1,0)(1/2,-1)(3/2,-1)`. B-vertex `(1,0)` sits in A's open base (`RelateNGComplete.v : onesided_t_B_on_open_base`). II empty because `gsA + gsC` of B equals `-py` (`RelateNGComplete.v : onesided_t_ii_empty`). Headline `RelateNGTouchOnesided.v : triangle_pair_regime_onesided`. |

On the leftover-`Ⅲ` compile letter every earlier wired detector is
built for a different contact:

| Detector | Why it is the wrong tool for this family |
|---|---|
| `touch_edge_b` | `RelateNGCore.v : shares_edge_b` is endpoint-pair equality. A T is not a full shared edge. |
| `contains_b` | Needs `0 < gtri A` at **every** B-vertex (`RelateNGCore.v : contains_b`). A stem on the supporting line has `gtri = 0`. |
| `overlap_b` | Needs a B-vertex with `0 < gtri A` **and** a B-vertex with `gtri A < 0` (`RelateNGCore.v : overlap_b`). A same-side stem can fire this arm. Those pairs are leftover `522-b`, not `Ⅳ`. The residue is same-side xor-true pairs that miss this arm. |
| `separated_b` | A supporting-edge separator is a disjoint witness. A T is contact. |
| `touch_vertex_b` | Needs a shared vertex and `RelateNGCore.v : cone_separates_b`. This family has **no** shared vertex. |
| `touch_partial_edge_b` | Mutual. Leftover `Ⅰ`. This family is one-sided. |
| `touch_onesided_t_b` | True on leftover `Ⅲ` and on leftover `Ⅳ`. No side test. Do not treat a xor-true pair as leftover `Ⅲ` without the opposite-side II-empty pin. |

## Nearby pairs that are **not** this leftover

| Pair / object | What it is | Do not |
|---|---|---|
| `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)` | Leftover `Ⅰ` sliver. Mutual. Same-side. II = 2, BB = 1. `RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`. | steal leftover `Ⅰ` |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)` | Leftover `Ⅱ` obtuse-at-v. Shared vertex. `RelateNGTouchObtuse.v : triangle_pair_regime_obtuse`. | remint leftover `Ⅱ` |
| `(0,0)(2,0)(0,1)` vs `(1,0)(1/2,-1)(3/2,-1)` | Leftover `Ⅲ` exterior-side stem. Opposite sides. II empty. `RelateNGComplete.v : onesided_t_pair_inhabits`. | steal leftover `Ⅲ` |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(0,-2)` | #572 / `522-i`. Classified **`TPR_TouchVertex`**. `RelateNGComplete.v : classified_touchvertex_pair`. | remint `cone_separates_b` / steal `522-i` |
| `(0,0)(1,0)(0,1)` vs `(2,0)(3,0)(2,1)` | #530 / #571 sentinel. Classified **disjoint**. `RelateNGComplete.v : classified_disjoint_pair`. | treat as the decline golden |
| `(0,0)(1,0)(0,1)` vs `(1/4,1/4)(5/4,1/4)(1/4,5/4)` | #570 / `522-b`. Classified **overlap**. `RelateNGComplete.v : classified_overlap_pair`. | bucket a same-side stem under leftover `Ⅳ` after `overlap_b` fires |
| Full shared edge `(0,0)(1,0)(0,1)` vs `(1,0)(1,1)(0,1)` | Frozen `TPR_TouchEdge` pin. | widen `shares_edge_b` |
| Line×line int×bnd | `RelateNodingLineLineMeet.v : segments_int_bnd_touches_ib_cell`. #67 / S15d. | steal as the triangle certificate |

The four wired hard pairs (`RelateNGComplete.v : classified_hard_pairs`)
classify. They are not this leftover.

## If `/implement Ⅳ` is asked — implement rungs (not this map)

Park: **research** (ADR-0002). Residue pair compiled
(`RelateNGComplete.v : interior_side_pair_inhabits`).

1. **Compile a cex, or prove emptiness of the residue.** Do not invent
   a 12-tuple in prose and treat it as the spec. A later implement
   letter must pin coordinates in `RelateNGComplete.v` (both-CCW;
   one-sided; same side of the supporting line; not leftover `Ⅰ`;
   not leftover `Ⅲ`; `overlap_b` false; not a `classified_hard_pairs`
   row) **or** prove that every same-side one-sided T is already
   classified by `overlap_b` / `contains_b`. Only then write a
   side-distinguishing detector, and only if asked.
2. **Not a widening of leftover `Ⅲ`.** Do **not** remint
   `RelateNGCore.v : touch_onesided_t_b`. The xor is load-bearing
   leftover-`Ⅲ` honesty. A new boolean, if asked, tests the side of
   the supporting line (or II emptiness) **after** the xor.
3. **Do not remint the fill.** Leftover `Ⅲ` is II empty and looks
   like areal Touches. Leftover `Ⅳ` is typically II nonempty and
   looks like leftover `Ⅰ`'s sliver / overlap-adjacent. There is no
   `onesided_t_bb_dim0`. The owner names a matrix **and** picks a
   side before any remint of `TPR_TouchOnesided` off
   `im_unsupported`. Do not emit `FFFFFFFFF`. Do not point the
   classifier at `aa_matrix_touch_vertical` /
   `aa_matrix_touch_edge_ogc` / `aa_matrix_partial_overlap`.
4. **Constructor split is an owner call.** Reuse `TPR_TouchOnesided`
   vs add a constructor. This map does not pick. Reuse keeps leftover
   `Ⅲ` and leftover `Ⅳ` on one fill. A new constructor can stay on
   the token.
5. **Bar 1 first, if inhabited.** Do not claim bar-2 nine-cell gtri
   in the first letter unless asked.
6. **Harness golden.** Decline is mixed-cone. Wiring leftover `Ⅳ`
   (if inhabited) does not move that golden. Do not assume
   completeness.
7. **Classifier order.** After leftover `Ⅲ`'s xor arm if a new
   constructor is asked. Do not reorder the four wired certificates.
   Do not pile onto leftover `Ⅰ` / leftover `Ⅱ` / leftover `Ⅲ`.
8. **Completeness stays false until proved.** Naming this family does
   not prove CCW-completeness. Do not claim
   `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete` is
   obsolete. Do not steal `522-j` / `522-m` / `522-f` / leftover `Ⅰ`
   / leftover `Ⅱ` / leftover `Ⅲ`.

## Decisions so far

- Completeness false on mixed-cone — #583 / #584 / `522-j` /
  `522-m`.
- Leftover `Ⅰ` bar 1 — #609 /
  `RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`.
- Leftover `Ⅲ` compiled and classified — #628 /
  `RelateNGTouchOnesided.v : triangle_pair_regime_onesided`. Fill
  stays `im_unsupported`.
- Leftover ids reminted to precomposed Roman numerals on #628.
  `Ⅳ` minted as the interior-side stem. This letter is the `Ⅳ`
  detail chart.
- Parent leftovers chart: `docs/scout/map-522-leftovers.md`.
- `522-n` is not minted. `Ⅴ` is unused.

## Fog

- **Inhabited as `TPR_TouchOnesided`.** Residue pair
  `RelateNGComplete.v : interior_side_pair_inhabits`. Same-side
  stems with a strict-interior B-vertex and a strict-exterior
  B-vertex remain leftover `522-b`.
- **II cell.** Typically nonempty (same-side). Not leftover `Ⅲ`'s
  empty pin (`RelateNGComplete.v : onesided_t_ii_empty`). Do not
  call leftover `Ⅳ` areal Touches until II is compiled empty or
  not.
- **Constructor vs reuse `TPR_TouchOnesided`.** Technique, not this
  map.
- **Fill.** Owner names a matrix **and** a side. Remint is a
  different leftover from this chart.
- **Leftover `Ⅲ`.** Compiled exterior-side stem. Do not remint that
  pair. Do not treat the xor as leftover-`Ⅳ`-complete.
- **`Ⅴ`.** Unused. Ask before assigning it.

## Frontier

Leftover `Ⅳ` is named. Residue pair compiled. This map does
not invent a detector.

```
family named ── same-side one-sided vertex-in-open-edge T
     residue pair ── interior_side_pair_inhabits
     xor already true; overlap_b may steal; II nonempty

Ⅳ ── research ── destination met (name + pair)
     grill ── map-interior-side-grill.md ── ticket 26 closed

Ⅰ ── mutual same-side sliver ── map-tjunction-cert.md ── not this leftover
Ⅱ ── obtuse-at-v ── TPR_TouchObtuse ── not this leftover
Ⅲ ── opposite-side stem ── TPR_TouchOnesided (fill token) ── not this leftover
not this leftover ── #570 overlap ── classified_overlap_pair
not this leftover ── #572 TouchVertex ── classified_touchvertex_pair
not this leftover ── fill remint ── owner names matrix and side
not this leftover ── widen touch_onesided_t_b ── leftover Ⅲ honesty

522-n ── not minted
Ⅴ ── unused ── ask before assigning
```
