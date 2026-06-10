# The escape-descent campaign — closing H1's last residual

**Branch:** `claude/jct-escape-descent`. **Target:**
`JCTEscapeDescent.escape_descent` — from an even-parity guarded complement
point with at least one crossing, reach (through the complement) a guarded
point with strictly fewer crossings. With it,
`parity_seam_offring_of_descent` closes the full corrected H1 seam; the
trapped half and the separation clause are already Qed (PR #165).

Why a path-following construction is unavoidable: a spiral polygon's centre
has even parity yet all four axis rays blocked — no straight-line escape
exists, so the detour must follow the boundary of the first blocking edge.
`ring_simple` enters here and only here (a doubly-wound ring has even-parity
trapped points).

## Rungs

| # | content | status |
|---|---|---|
| 1 | **East approach** (`JCTEastApproach.v`): the crossing abscissa `cross_x`, the first wall `min_cross_x`, the skeleton-free run-up, the east walk preserving complement/guard/count, and `crossings_distinct` (simplicity's first theorem: distinct crossing edges cross at distinct abscissae) | **Qed** |
| 2 | **The corridor toolkit** (`JCTCorridor.v`): the corridor along a carrier edge is a straight segment (`edge_x_at` affine), connected through the complement under per-edge clearances that are pure affine endpoint evaluations (`corridor_avoid_{carrier,west,east,below,above}`); `level_gap` parks endpoints at vertex-level-free heights for a free ray guard; unit-square worked instance | **Qed** |
| 3 | **The walk kit** (`JCTWalkKit.v`): the mixed clearance via the three-point affine law (`corridor_avoid_clipped_west`/`_east`, clip points by affine inversion `clip_params_asc`/`_desc`), plus the jog connectors `horizontal_connected`/`vertical_connected` gluing corridor pieces. Generic geometry complete | **Qed** |
| 4 | **The walk step** (`JCTWalkStep.v`): east run-up + wall corridor assembled into one complement path (`walk_step`), with the join exact (`cross_x_is_edge_x_at`) and the destination parked, off-ring and guarded (`walk_step_guarded` via `exists_parked_height`); conditional only on the corridor clearances | **Qed** |
| 4b-1 | **The taut bridge** (`JCTTautClearance.v`): `ring_taut` (the walk's simplicity notion, strictly stronger than corpus `ring_simple` which admits T-touches), `taut_no_line_touch` (line = segment inside a span-interior window, so line-meetings force the carrier pointwise), `affine_root` (constructive affine IVT), `clip_ordered_asc/_desc` | **Qed** |
| 4b-2 | **The per-edge clearance case tree**: for each edge of a taut ring, decide the clip-point signs (west → explicit margin; east → any offset; mixed → an `affine_root` zero inside the window → `taut_no_line_touch` forces the carrier, handled by `corridor_avoid_carrier`); fold the margins by `Rmin` into a uniform `delta0` (`wall_corridor_clear`) | open |
| 4b-3 | **Corners + recursion**: the corner sector at each shared vertex (turn sign from `Orientation.cross`) and the bounded recursion around the boundary until a count-free point is reached | open |
| 5 | **Assembly**: `escape_descent_holds : ring_simple r -> ring_closed r -> ... -> escape_descent r`, composed through `parity_seam_offring_of_descent` — H1 closed | open |

## Rung 1 deliverables (this commit)

- `cross_x p e` — the height-`py p` crossing abscissa; under the ray guard
  every half-open crossing is a **strict** straddle
  (`ho_cross_strict_of_guard`), so the abscissa is the edge's unique
  height point (`cross_pt_on_edge` / `height_pt_unique`) and lies strictly
  east of `p` (`cross_x_east`).
- `min_cross_x` — the first wall, with existence (`min_cross_x_some_of_cross`),
  achievement (`min_cross_x_achieved`) and the lower bound
  (`min_cross_x_lb`).
- `east_segment_free` — the half-open run-up `[px p, X1)` at `p`'s height is
  skeleton-free: non-crossing edges by the part-6 ray lemma, crossing edges
  because their unique height point sits at or beyond the wall.
- `east_approach` — THE RUNG THEOREM: every point of the run-up is
  complement-connected to `p`, off-ring, guarded, and carries the **same**
  `ho_count` (`cross_iff_shift_east` + `ho_count_ext`): all descent
  invariants survive the approach.
- `crossings_distinct` — **the first genuine use of `ring_simple` in the H1
  campaign**: two distinct crossing edges cross the ray at distinct
  abscissae, because a shared crossing point is interior to both (strict
  straddles) and would be a proper intersection. This is what makes "the
  first wall" a single well-defined edge for rung 2 to walk around.
