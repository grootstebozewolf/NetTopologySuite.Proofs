<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Map — T-junction / partial-edge sliver certificate

A wayfinder map. Charted 2026-08-30. This is **not** a GitHub child, **not**
a remint of `522-j` / `522-m`, and **not** the line×line noding T-junction
(`RelateNodingLineLineMeet.v : segments_int_bnd_touches_ib_cell`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are precomposed
> Roman numerals. This leftover is **`Ⅰ`**. Obtuse-at-v is **`Ⅱ`**.
> Do not swap them. Do not remint ADR-0004.
> This map does not mint a GitHub child.

topics: relate
claimId: Ⅰ
witness: none

## Destination

**Name the #577 finding pair as the next certificate's specification, without
inventing the certificate.**

Ticket #577 asked either completeness or a documented counterexample that
becomes the next certificate's spec. Completeness is false
(`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`). The
compiled pair is the spec. This map charts what that spec is, what it is
not, and what `/implement` of leftover `Ⅰ` must not steal. It does **not**
write a detector. `/implement` of `Ⅰ` is a later letter.

## The pair (the spec)

A = `(0,0)(2,0)(0,1)`, B = `(1,0)(3,0)(2,1)`.

Pinned as `tjunction_pair_coords` in `RelateNGComplete.v`. Both-CCW:
`gdbl A = gdbl B = 2` (`RelateNGComplete.v : tjunction_pair_both_ccw`).
Oracle / harness golden: `oracle/de9im_triangle_vectors.txt` `REGIME TOUCH_PARTIAL`
(fill still `UNSUPPORTED`). Decline golden is the unnamed mixed-cone pair.
`RelateNGOracleSurface.v : relate_tjunction_wire_unsupported` still holds
because the fill is `im_unsupported`.

```
        (0,1)                 (2,1)
           *                    *
          / \                  / \
         /   \                /   \
   (0,0)*-----*-----*-----*(3,0)
              (1,0) (2,0)
```

The bottoms `[(0,0),(2,0)]` and `[(1,0),(3,0)]` are collinear on `y = 0`.
They overlap on the open-closed segment from `(1,0)` to `(2,0)`:

- B-vertex `(1,0)` sits in the **open interior** of A's bottom edge.
- A-vertex `(2,0)` sits in the **open interior** of B's bottom edge.
- No vertex is shared (`point_eqb` all false).
- No full edge is shared (`shares_edge_b` is endpoint-pair equality).

The corpus nickname is "T-junction / partial-edge kiss". The compiled
pair is **sliver overlap**, not a kiss: both apices have `y > 0`, so
`(1.5, 0.01)` has `gtri A > 0` and `gtri B > 0`. Interiors meet
(II = 2). BB is the segment `(1,0)–(2,0)` (dim 1). `overlap_b` misses
because no B-vertex is strictly interior to A (the #570 pure-lens hole).
The detector names the vertex-on-open-edge *configuration*. It does not
establish `triangles_partial_overlap` and it does not establish
interiors-disjoint touch. That is why fill stays `im_unsupported`.
An exterior-side one-sided T is leftover `Ⅲ`
(`RelateNGComplete.v : onesided_t_pair_inhabits`), not this leftover.
The interior-side stem is leftover `Ⅳ`
(`RelateNGComplete.v : interior_side_pair_inhabits`).
The xor is `Ⅲ∨Ⅳ` with two compiled witnesses.

## Why every wired detector misses

Classifier order (`RelateNGCore.v : triangle_pair_regime`):
`touch_edge_b` → `contains_b` → `overlap_b` → `separated_b` →
`touch_vertex_b` → `touch_partial_edge_b` → `TPR_TouchPartialEdge`
→ `touch_onesided_t_b` → `TPR_TouchOnesided` → `TPR_Unsupported`.
Headline for leftover `Ⅰ`:
`RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`.
Leftover `Ⅲ` xor (`Ⅲ∨Ⅳ`, two witnesses):
`RelateNGTouchOnesided.v : triangle_pair_regime_onesided`.
Leftover `Ⅳ` headline:
`RelateNGTouchOnesided.v : triangle_pair_regime_interior_side`.

| Detector | Why false on this pair |
|---|---|
| `touch_edge_b` | `shares_edge_b` needs both endpoints of one edge to equal both endpoints of another. `(0,0)≠(1,0)` and `(2,0)≠(3,0)`. |
| `contains_b` | Needs `0 < gtri A` at every B-vertex. `(1,0)` and `(3,0)` lie on the supporting line `y = 0` (`gtri ≤ 0`). |
| `overlap_b` | Needs a B-vertex with `0 < gtri A`. All three B-vertices have `gtri A ≤ 0`. `(2,1)` is strictly exterior. |
| `separated_b` | `RelateNGDisjoint.v : tjunction_no_separator` — no supporting edge is vertex-strict. |
| `touch_vertex_b` | `exactly_one_shared_from_a` is false (no shared vertex). |
| `touch_partial_edge_b` | **True** on this pair (leftover `Ⅰ` bar 1). |

Compiled fill still declines: `RelateNGDisjoint.v : tjunction_pair_unsupported`
(`triangle_pair_fill TPR_TouchPartialEdge = im_unsupported`).
No named predicate holds: `RelateNGDisjoint.v : relate_tjunction_pair_no_predicate`.

## Nearby pairs that are **not** this leftover

| Pair | What it is | Do not |
|---|---|---|
| `(0,0)(1,0)(0,1)` vs `(2,0)(3,0)(2,1)` | #530 / #571 sentinel. Classified **disjoint**. | treat as the decline golden |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)` | Obtuse-at-v. `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`. Shared vertex; cone `side_dot = 0`. | bucket under one letter |
| `(0,0)(1,0)(0,1)` vs `(2,0)(2,1)(3,0)` | RelatePrepared decline 12-tuple. B is **CW** (`gdbl < 0`). Domain-boundary, not the kiss. | use as the T-junction spec |
| Line×line int×bnd | `RelateNodingLineLineMeet.v : segments_int_bnd_touches_ib_cell`. #67 / S15d. IB dim-0. | steal as the triangle certificate |
| Full shared edge `(0,0)(1,0)(0,1)` vs `(1,0)(1,1)(0,1)` | Frozen `TPR_TouchEdge` pin. | widen `shares_edge_b` to absorb the kiss |

An **exterior-side one-sided T** is leftover `Ⅲ`
(`RelateNGComplete.v : onesided_t_pair_inhabits`;
`RelateNGTouchOnesided.v : triangle_pair_regime_onesided`;
`TPR_TouchOnesided`; fill still `im_unsupported`). Contact is
collinear with the supporting edge. II empty is compiled; BB dim 0
is not. The xor is `Ⅲ∨Ⅳ` with two compiled witnesses. The
interior-side stem is leftover `Ⅳ`
(`RelateNGComplete.v : interior_side_pair_inhabits`).
Not this leftover.

## If `/implement Ⅰ` is asked — implement rungs (not this map)

Park: **research** (ADR-0002). Bar 1 of leftover `Ⅰ` is the letter that
writes the detector.

1. **Detector, not a remint.** A new boolean (working name only:
   `touch_partial_edge_b`) that is true on this 12-tuple and false on the
   four wired hard pairs (`classified_hard_pairs`). Do **not** widen
   `shares_edge_b` / `touch_edge_b`. That vocab is the frozen TouchEdge
   leftover (#597 carve). Do **not** remint `aa_matrix_*` pins.
2. **Constructor is an owner call.** Reuse `TPR_TouchEdge` vs add a
   constructor. Reuse inherits fill `FFFF1FFF2` (`aa_matrix_touch_vertical`)
   and fights TouchEdge exclusivity. A new constructor can stay on
   `im_unsupported` until a fill is named. This map does not pick.
3. **Bar 1 first.** The compiled pair is sliver overlap (II nonempty).
   Do not claim bar-2 nine-cell gtri. Do **not** remint the fill to
   `FF2F11212` / `FFFF1FFF2` — that would be a confident Touches matrix
   on overlapping triangles. Cite `aa_matrix_touch_edge_ogc`; do not
   point the classifier at it. If a fill is ever named, start from the
   overlap-ogc family plus BB = 1, after proving II empty or not.
4. **Harness golden must move.** Today's decline vector **is this pair**.
   If the pair classifies, `REGIME DECLINE` in
   `oracle/de9im_triangle_vectors.txt` and the hunt selfcheck notes must
   point at a still-unsupported pair (mixed-cone is the existing one).
   Do not turn the decline into a confident `FFFFFFFFF`.
5. **Classifier order.** After `touch_edge_b` (full shared edge wins).
   Do not reorder the four wired certificates.
6. **Completeness stays false.** Wiring this pair does not prove
   CCW-completeness. Obtuse-at-v remains. Do not claim
   `triangle_pair_regime_ccw_incomplete` is obsolete.

## Decisions so far

- Completeness false on this pair — #583 / `522-j`.
- Filtered retry still false (obtuse) — #584 / `522-m`.
- Honest decline wire token is this pair — #588 + #595 / `522-f`.
- Certificates not invented in those letters.
- Parent leftovers chart: #598 / `docs/scout/map-522-leftovers.md` (on `main`).
- Leftover ids are Roman numerals. This leftover is `Ⅰ`. `522-n` is
  not minted.

## Fog

- **`Ⅱ`.** Obtuse-at-v. Finding
  `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`.
  Do not invent that detector in leftover `Ⅰ`.
- **Constructor vs reuse `TPR_TouchEdge`.** Technique, not this map.
- **Fill.** The compiled pair is sliver overlap (II = 2, BB = 1). The
  designated TouchEdge pin is still `FFFF1FFF2`. Do not remint this
  constructor to a Touches fill. Remint is a different leftover.
- **Family width.** This spec is the compiled mutual sliver. An
  exterior-side one-sided T is leftover `Ⅲ`
  (`RelateNGComplete.v : onesided_t_pair_inhabits`). The interior-side
  stem is leftover `Ⅳ`
  (`RelateNGComplete.v : interior_side_pair_inhabits`).
  The xor is `Ⅲ∨Ⅳ`.

## Frontier

Leftover `Ⅰ` bar 1 is landed (`triangle_pair_regime_touchpartial`).
Fill is still `im_unsupported`. Completeness stays false on `Ⅱ`.

```
#577 finding ── triangle_pair_regime_incomplete_tjunction ── historical

Ⅰ ── mutual vertex-in-open-edge sliver ── bar 1 ── TPR_TouchPartialEdge
     pair (0,0)(2,0)(0,1) vs (1,0)(3,0)(2,1)
     decline golden moved to mixed-cone

Ⅱ ── obtuse-at-v ── TPR_TouchObtuse ── not this leftover
not this leftover ── line×line T ── #67
not this leftover ── widen shares_edge_b ── TouchEdge leftover
not this leftover ── fill remint ── four shared pins

522-n ── not minted
Ⅲ ──── compiled exterior-side stem ── TPR_TouchOnesided (fill token)
Ⅳ ──── interior-side stem ── TPR_TouchOnesided (fill token)
Ⅴ ── unused ── ask before assigning
```
