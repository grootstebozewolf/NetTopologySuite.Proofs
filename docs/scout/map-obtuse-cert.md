# Map — obtuse-at-v certificate

A wayfinder map. Charted 2026-08-30; compiled 2026-08-30. This is **not**
a GitHub child, **not** a remint of `522-j` / `522-m` / `522-i`, and
**not** leftover `Ⅰ`'s mutual vertex-in-open-edge sliver
(`map-tjunction-cert.md`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are precomposed
> Roman numerals. This leftover is **`Ⅱ`**. The T-junction / partial-edge
> sliver is **`Ⅰ`**. Do not swap them. Do not remint ADR-0004.
> This map does not mint a GitHub child. Leftover `Ⅴ` is mixed-cone.
> `Ⅵ`–`Ⅸ` later classified; do not mint `Ⅹ`.

topics: relate
claimId: Ⅱ
witness: Ⅱ-obtuse-cex

## Destination

**Classify the #584 finding pair as leftover `Ⅱ` without reminting
`cone_separates_b` / `touch_vertex_b`.**

Ticket #577 asked either completeness (QED) or a documented counterexample
(QEX). Leftover `Ⅱ`'s letter stop is
`RelateNGTouchObtuse.v : triangle_pair_regime_ccw_stop` (discharged QEX).
The filtered sibling is
`RelateNGTouchObtuse.v : triangle_pair_regime_ccw_stop_not_tjunction`.
Completeness is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`). The
filtered retry is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
The live cex is an unnamed CCW pair after leftover `Ⅴ`. Leftover
`Ⅱ` itself is QED (`RelateNGTouchObtuse.v : leftover_ii_qed_or_qex`).
Epic #522 stop is QED ∨ QEX (`RelateNGEpic522.v : ticket_522_qed_or_qex`).
This map charts the compiled leftover-`Ⅱ` pair, what it is not, and
what a later letter must not steal.

## The pair (compiled)

A = `(0,0)(2,0)(0,2)`, B = `(0,0)(-2,0)(1,-1)`.

Both-CCW: `RelateNGComplete.v : obtuse_pair_both_ccw`. Not the T-junction
12-tuple: `RelateNGComplete.v : obtuse_pair_not_tjunction`. Classifies
`TPR_TouchObtuse`: `RelateNGComplete.v : obtuse_pair_touch_obtuse`.
Headline: `RelateNGTouchObtuse.v : triangle_pair_regime_obtuse`.

Same A as the #572 / `522-i` vertex-touch pin
(`RelateNGComplete.v : classified_touchvertex_pair`): A vs
`(0,0)(-2,0)(0,-2)` classifies `TPR_TouchVertex`. This leftover only
moves B's third vertex from `(0,-2)` to `(1,-1)`.

```
        (0,2)
           *
          /|
         / |
   (0,0)*--+--*(2,0)
        |
        |     *(1,-1)
        |
   (-2,0)*
```

They share **exactly one vertex** — the origin. No full edge is shared
(`shares_edge_b` is endpoint-pair equality). A's bottom `[(0,0),(2,0)]`
and B's bottom `[(0,0),(-2,0)]` meet only at `(0,0)`.

The vertex-touch cone is constructed in `RelateNGCore.v : cone_separates_b`:
normal `nA = vec_sum_from v (2,0) (0,2) = (2,2)`. Then
`RelateNGCore.v : side_dot` of B's remaining vertex `(1,-1)` against
`nA` is `1·2 + (−1)·2 = 0`. The *strict* cone demands a sign on both
remaining B-vertices (`both_strict_neg_b` / `both_strict_pos_b`). A zero
fails. That is the compiled #572 miss. Leftover `Ⅱ` adds a *closed*
cone (`RelateNGCore.v : touch_obtuse_vertex_b`) plus
`negb cone_separates_b`, so the #572 pair stays `TPR_TouchVertex`
(`RelateNGTouchObtuse.v : hard_touchvertex_no_obtuse`).

The corpus nickname is **obtuse-at-v**. B's angle at the shared vertex
is obtuse: legs `(−2,0)` and `(1,−1)` have negative dot product. `(1,−1)`
sits on the supporting line of A's cone through `v` (the line `y = −x`).
The shared set is a **vertex** (BB dimension 0), not leftover `Ⅰ`'s
positive-length collinear sliver.

Constructor `TPR_TouchObtuse` stays on `im_unsupported`
(`RelateMatrixTriangle.v : triangle_pair_fill_touch_obtuse_eq`;
`RelateNGOracleSurface.v : triangle_touch_obtuse_wire`). Do not emit
`FFFF1FFF2` — that pin is #572 / `TPR_TouchVertex`.
`classify_triangle_pair` arm is `True` — leftover `Ⅰ` honesty, not
CONTEXT Bar 1.

Oracle / harness: `oracle/de9im_triangle_vectors.txt` `REGIME TOUCH_OBTUSE`
(fill still `UNSUPPORTED`). Decline golden is an unnamed CCW pair after
leftover `Ⅴ`.

## Why every wired detector misses

Classifier order (`RelateNGCore.v : triangle_pair_regime`):
`touch_edge_b` → `contains_b` → `overlap_b` → `separated_b` →
`touch_vertex_b` → leftover `Ⅰ` → leftover `Ⅲ∨Ⅳ` → leftover `Ⅱ` →
leftover `Ⅴ` → `TPR_Unsupported`.

| Detector | Why false on this pair |
|---|---|
| `touch_edge_b` | No full shared edge. `(0,0)(2,0)` ≠ `(0,0)(−2,0)`. |
| `contains_b` | Needs `0 < gtri A` at every B-vertex. `(0,0)` is a vertex of A (`gtri ≤ 0`). |
| `overlap_b` | Needs a B-vertex with `0 < gtri A`. `(0,0)` and `(−2,0)` have `gtri A ≤ 0`; `(1,−1)` is strictly exterior. |
| `separated_b` | `RelateNGComplete.v : obtuse_no_separator` — the shared origin is an endpoint of every candidate edge. |
| `touch_vertex_b` | `exactly_one_shared_from_a` is **true**. `cone_separates_b` is **false** (`side_dot = 0` on `(1,−1)`). |
| `touch_partial_edge_b` | `RelateNGTouchPartialEdge.v : obtuse_no_partial_edge`. No vertex sits in an open edge. |
| `touch_onesided_t_b` | `RelateNGTouchOnesided.v : obtuse_no_onesided`. Same: no vertex-in-open-edge. |

## Nearby pairs that are **not** this leftover

| Pair | What it is | Do not |
|---|---|---|
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(0,-2)` | #572 / `522-i`. Classified **`TPR_TouchVertex`**. Same A; B's third vertex is strictly in the opposite cone. | remint `cone_separates_b` / steal `522-i` |
| `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)` | Leftover `Ⅰ` sliver. **No** shared vertex. `RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`. | bucket under one letter |
| `(0,0)(1,0)(0,1)` vs `(2,0)(3,0)(2,1)` | #530 / #571 sentinel. Classified **disjoint**. | treat as the decline golden |
| `(0,0)(2,0)(0,2)` vs `(0,0)(1/2,1/2)(-2,0)` | Ticket nudge. `RelateNGTouchVertexRegime.v : touchvertex_nudge_off`. Remaining B-vertex sits on A's side of `nA` (overlap, not a closed cone). | treat as obtuse-at-v |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-1,-1)(3,1)` | Leftover `Ⅴ` mixed-cone. Classified **`TPR_MixedCone`**. Remaining B-vertices sit on **opposite** sides of `nA`. `RelateNGComplete.v : mixed_cone_pair_mixedcone`. | steal leftover `Ⅴ` |
| `(0,0)(1,0)(0,1)` vs `(2,0)(2,1)(3,0)` | RelatePrepared decline 12-tuple. B is **CW** (`gdbl < 0`). Domain-boundary. | use as the obtuse spec |
| Line×line int×bnd | `RelateNodingLineLineMeet.v : segments_int_bnd_touches_ib_cell`. #67 / S15d. IB dim-0. | steal as the triangle certificate |
| Full shared edge `(0,0)(1,0)(0,1)` vs `(1,0)(1,1)(0,1)` | Frozen `TPR_TouchEdge` pin. | widen `shares_edge_b` |

A **dim-0 T** (vertex in an open edge, no shared vertex) is unnamed.
Leftover `Ⅴ` is mixed-cone. It is **not** this leftover.

The four wired hard pairs (`RelateNGComplete.v : classified_hard_pairs`)
classify. They are not this leftover
(`RelateNGTouchObtuse.v : classified_hard_pairs_no_obtuse`).

## Decisions so far

- Completeness false on the T-junction — #583 / `522-j`. Leftover `Ⅰ`
  classified that pair (#609).
- Filtered retry still false — #584 / `522-m`. The original 522-m pair
  is this leftover; completeness moved to mixed-cone.
- Vertex-touch bar 1 on the sibling pair — #582 / `522-i`.
- Honest decline wire token — #588 + #595 / `522-f`. Decline golden is
  mixed-cone after this letter.
- Constructor is new (`TPR_TouchObtuse`); fill stays `im_unsupported`.
  Do not remint `cone_separates_b`.
- Parent leftovers chart: `docs/scout/map-522-leftovers.md`.
- Leftover `Ⅰ` detail chart: `docs/scout/map-tjunction-cert.md`.
- Ticket 27 closed — this compile.

## Fog

- **Fill.** Geometry of the kiss is areal Touches with BB dim 0. The
  designated TouchVertex pin is still `FFFF1FFF2`. Remint is a different
  leftover.
- **Family width.** This spec is the compiled closed-cone vertex kiss.
  A dim-0 T is unnamed. Mixed-cone is unnamed. Do not mint `Ⅴ`.
- **`classify_triangle_pair`.** Arm is `True`. Do not prove leftover-`Ⅱ`
  facts through it.

## Frontier

Leftover `Ⅱ` is compiled (QED)
(`RelateNGTouchObtuse.v : leftover_ii_qed_or_qex`). Epic #522 stop
is QED ∨ QEX (`RelateNGEpic522.v : ticket_522_qed_or_qex`).

```
#584 finding ── triangle_pair_regime_ccw_incomplete_not_tjunction ── still false
     original pair classified ── TPR_TouchObtuse
     live cex ── mixed-cone (0,0)(2,0)(0,2) vs (0,0)(-1,-1)(3,1)

Ⅱ ── obtuse-at-v ── RelateNGTouchObtuse.v : triangle_pair_regime_obtuse
     pair (0,0)(2,0)(0,2) vs (0,0)(-2,0)(1,-1)
     shared vertex; cone side_dot = 0
     fill im_unsupported; not CONTEXT Bar 1

Ⅰ ── T-junction / partial-edge sliver ── map-tjunction-cert.md ── not this leftover
not this leftover ── #572 TouchVertex ── (0,-2) third vertex
not this leftover ── ticket nudge ── touchvertex_nudge_off
not this leftover ── mixed-cone ── live completeness cex
not this leftover ── line×line T ── #67
not this leftover ── widen cone_separates_b ── steal 522-i
not this leftover ── widen shares_edge_b ── TouchEdge leftover
not this leftover ── fill remint ── four shared pins

522-n ── not minted
Ⅴ ── unused ── ask before assigning
```
