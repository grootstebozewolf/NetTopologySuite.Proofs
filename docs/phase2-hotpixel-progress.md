# Phase 2 progress: hot-pixel foundations + segment-touches filter

**Status.** Living progress record for the Phase 2 (snap-rounding noder)
foundations slices. The scope, reusable Phase 0/1 foundations, and the
first-slice plan are in
[`docs/audit-phase2-snap-rounding.md`](audit-phase2-snap-rounding.md);
this document records what has actually landed in
[`theories/HotPixel.v`](../theories/HotPixel.v) (R-side) and
[`theories-flocq/HotPixel_b64.v`](../theories-flocq/HotPixel_b64.v)
(binary64 layer), slice by slice.

Throughout: the corpus invariant holds (no `Admitted` / `Axiom` /
`Parameter` added; the registry stays at its baseline of 4), and every
new theorem closes with only the four standard classical-reals axioms.

## Layered structure

The segment-touches-pixel story is organised in three layers, with a
soundness arrow flowing upward:

```
form (b)  b64_segment_touches_hot_pixel_partial   (decidable bool filter)
            |  soundness  (true -> ...)
form (a)  b64_segment_touches_hot_pixel_spec       (parametric existential)
            |  soundness
R-side    segment_touches_hot_pixel (BP2P ...)      (exact predicate)
```

The pixel is the half-open square `[cx - r, cx + r) x [cy - r, cy + r)`
(closed lower bounds, open upper bounds), at the unit-grid scale
`scale = 1`, radius `r = 1/2`.

## Slices landed

### Slice 1.5 — `in_hot_pixel` bridge (item 1)

`b64_in_hot_pixel_sound`: lifts the rounded-pixel soundness
(`b64_in_hot_pixel_sound_rounded`) to the exact R-side `in_hot_pixel`.
Under `coord_int_safe` (`|n| <= 2^25`) the bounds `IZR n +/- 1/2 =
(2n +/- 1)/2` have a 27-bit mantissa at most, exactly representable in
binary64's 53-bit significand, so the rounded boundaries coincide with
the exact ones on the nose. Foundation theorems: `b64_half`,
`B2R_b64_{one,two,half}`, `b64_hot_pixel_radius_at_one`,
`b64_minus_half_int_exact`, `b64_plus_half_int_exact`,
`generic_format_F2R_27bit_exp_neg1`. (9 theorems.)

### Slice 2 — form (a) parametric existential (item 3a)

`b64_segment_touches_hot_pixel_spec := segment_touches_hot_pixel
(BP2P P0) (BP2P P1) (BP2P C) 1`. Three endpoint lemmas
(`_spec_l/_r/_degenerate`) lift from `b64_in_hot_pixel = true` via
Slice 1.5; `b64_segment_touches_hot_pixel_sound` documents the bridge
to the R-side as the identity unfolding. (4 theorems.)

### Slice 3 — endpoint-only bool filter (item 3b)

`b64_segment_touches_hot_pixel_endpoints` (bool) +
`_endpoints_sound` (to form (a)) + `_endpoints_sound_R` (to R-side).
The prompt's separate decidability helper was redundant —
`b64_in_hot_pixel` already returns `bool`. (3 theorems.)

### Slice 4 — BB-overlap counterexample (item 3c)

R-side certificate that bounding-box overlap is **necessary but not
sufficient** for touch: `bb_overlap_not_sufficient_for_touches` with
witness `P0=(0,1)`, `P1=(3/2,-1)`, `C=(3/2,1/2)` — BBs overlap on both
axes but no `t in [0,1]` places the convex combination inside the
half-open pixel. Corrects an erroneous witness from a Slice 3 commit
message. (4 theorems, in `theories/HotPixel.v`.)

### Slice 5 — closed-edge crossing (item 3d)

`b64_segment_crosses_bottom_edge_sound`,
`b64_segment_crosses_left_edge_sound`. The closed lower bounds (`<=`)
make the explicit-`t*` edge-crossing witness valid with equality — no
epsilon-shift. Proof shape: `field` for the linear product identity,
`nra` for `0 < t* < 1` and the principal-coordinate-on-edge identity,
`lra` for the half-open inequalities. (2 theorems.)

### Slice 6 — opposite-edge crossing (item 3e, opposite)

`b64_segment_crosses_top_and_bottom_sound`,
`b64_segment_crosses_left_and_right_sound`. For a segment passing
through OPPOSITE edges, the midpoint of the two crossing parameters
pins the principal coordinate to the pixel center exactly
(`(cy+1/2 + cy-1/2)/2 = cy`), strictly inside the half-open pixel. No
IVT needed. (2 theorems.)

### Slice 7 — adjacent-edge crossing (item 3e, adjacent)

`b64_segment_crosses_{top_left,top_right,bottom_left,bottom_right}_sound`.
Also via the two-crossing midpoint, but with range preconditions on
both crossings. At the midpoint, each coordinate averages one edge
value with the other crossing's in-range coordinate, landing strictly
inside — crucially holding for the OPEN top/right edges, since
`avg(in-range, edge) < edge`. All eight crossing patterns now have
Prop-form soundness. (4 theorems.)

### Slice 9 — point-in-pixel completeness (item 3g, point)

The converse of the Slice 1.5 bridge: under `coord_int_safe` +
eval-safety, the exact R-side `in_hot_pixel` IMPLIES the binary64
boolean decision `b64_in_hot_pixel = true`. Completeness helpers
`b64_le_complete` / `b64_lt_complete` (converses of the Slice 1.5
soundness helpers), a shared `b64_hot_pixel_bounds_exact` (the four
bounds' B2R values + finiteness), `b64_in_hot_pixel_complete`, and
`b64_segment_touches_hot_pixel_endpoint_complete` (the filter fires
whenever an endpoint lies in the pixel). With Slice 1.5 this makes the
boolean pixel decision sound AND complete in the integer regime. The
crossing-case filter completeness (the geometric classification) stays
deferred. (5 theorems.)

### Slices 3f + 8 — decidable bool wrappers (item 3f)

Forward-elimination helpers `Rlt_bool_elim` / `Rle_bool_elim` over
Flocq's `Rlt_bool` / `Rle_bool`. Eight `_dec` predicates (one per
crossing pattern) + their `_dec_sound` lemmas, composed with the
endpoint filter into:

```coq
Definition b64_segment_touches_hot_pixel_partial (P0 P1 C : BPoint) : bool :=
  b64_segment_touches_hot_pixel_endpoints P0 P1 C
  || b64_crosses_bottom_edge_dec P0 P1 C
  || b64_crosses_left_edge_dec P0 P1 C
  || b64_crosses_top_bottom_dec P0 P1 C
  || b64_crosses_left_right_dec P0 P1 C
  || b64_crosses_top_left_dec P0 P1 C
  || b64_crosses_top_right_dec P0 P1 C
  || b64_crosses_bottom_left_dec P0 P1 C
  || b64_crosses_bottom_right_dec P0 P1 C.
```

`b64_segment_touches_hot_pixel_partial_sound` (to form (a)) and
`_partial_sound_R` (to the R-side). The filter soundly decides every
crossing pattern + both endpoint cases. (16 theorems across the two
slices.)

## Deferred-block status

| # | Item | Status |
|---|---|---|
| 1 | `b64_in_hot_pixel_sound` bridge | **landed** (Slice 1.5; unit-grid scale, arbitrary power-of-two scale remains) |
| 2 | `b64_hot_pixel_center` via `Bnearbyint` | deferred (round-to-integer primitive) |
| 3a | form (a) parametric existential | **landed** (Slice 2) |
| 3b | form (b) endpoint-only filter | **landed** (Slice 3) |
| 3c | form (b) BB-overlap counterexample | **landed** (Slice 4) |
| 3d | form (b) closed-edge crossing | **landed** (Slice 5) |
| 3e | form (b) open + adjacent crossing | **landed** (Slices 6 + 7; all 8 patterns) |
| 3f | form (b) decidable bool wrapper | **landed** (Slices 3f + 8; all 8 patterns) |
| 3g-point | point-in-pixel completeness + endpoint-case filter completeness | **landed** (Slice 9) |
| 3g-crossing | crossing-case filter completeness | **deferred** — the geometric classification argument |
| 4 | integer-regime exact-radius | deferred |

## What remains before the unqualified `b64_segment_touches_hot_pixel`

The partial filter is **sound** (`partial = true` -> touches). The
ENDPOINT half of completeness is now in hand (Slice 9:
`b64_segment_touches_hot_pixel_endpoint_complete` — if either endpoint
lies in the pixel, the filter fires). The remaining piece
(3g-crossing) is the harder classification argument: prove that any
segment genuinely touching the half-open pixel **with both endpoints
outside** must trigger one of the eight edge-crossing disjuncts — i.e.
the disjunction is exhaustive over all the ways a chord can enter a
convex half-open cell.

A noder needs *completeness* (no false negatives — it must insert a
vertex at every pixel a segment passes through, or snap-rounding misses
required vertices). Completeness is therefore the gate before the
unqualified `b64_segment_touches_hot_pixel` ships with the full
sound-and-complete contract, and before the passes-through relation
(the next Phase 2 milestone) can be stated computationally.

## Cumulative

49 theorems Qed-closed across `HotPixel.v` + `HotPixel_b64.v` for the
Phase 2 foundations, zero `Admitted`, only the four standard
classical-reals axioms throughout.
