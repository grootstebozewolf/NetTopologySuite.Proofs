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
| 4b-2 | **The per-edge clearance case tree** (`JCTWallClear.v`): for each edge of a taut ring, decide the clip-point signs (west → explicit margin; east → any offset; mixed → an `affine_root` zero inside the window → `taut_no_line_touch` forces the carrier, handled by `corridor_avoid_carrier` via `touch_clearance`); fold the margins by `Rmin` into a uniform `delta0` (`wall_corridor_clear`) | **Qed** |
| 4b-3 | **The corner sector** (`JCTCornerSector.v`): past the wall edge's bottom vertex `v` by a vertical drop just west of `v` (`corner_sector_guarded`), with `eps` shrunk after `delta`; tautness gives the obstacle dichotomy (`taut_vertex_endpoint`: edges through `v` are endpoint-incident, slope-bounded; edges missing `v` get explicit margins). Plus `corridor_offset_jog` and below-level parking (`depth_gap`). Residual hypothesis recorded: no horizontal edge extends west from `v` | **Qed** |
| 5a | **The corner-abutting clearance** (`JCTCornerClear.v`): under `corner_opens_east` at the wall's bottom vertex, the corridor is free on the whole half-open window `(py v, yhi]` with ONE uniform `delta0` (`wall_corridor_clear_corner`), dissolving the window-before-`delta` vs `eps`-after-`delta` deadlock; `corner_passage` composes ride + drop into the full corner move. The hypothesis fails exactly inside a wedge — where interior walkers must stick (`odd_parity_trapped`). Subsumes 4b-3's horizontal residual | **Qed** |
| 5b | **The mirror kit** (`JCTMirrorKit.v`): the walk must sometimes back *upward* out of a wedge (the spiral demands it), so the traversal needs corridor moves in all four orientations. Coordinate-reflection transport (`xmir` east↔west, `ymir` over↔under) of skeleton/tautness/closedness/connectivity/boundedness, both ways via involutions; `ymir` is *exact* for guard, crossings, `ho_count`, parity (the ray is horizontal; under the guard, half-open = strict straddle, which is y-symmetric). All west/under theorems of rungs 2–5a now apply to the mirrored rings and pull back | **Qed** |
| 5c-1 | **The top passage + terminal count** (`JCTTopPassage.v`): `corner_passage_top` — the over-the-top move (the y-flip pullback of `corner_passage`, with `corner_opens_east_top` and the guard transported exactly), backing the walk out of sealed wedges; `ho_count_zero_east` — at or east of `xsup` (the east-most vertex abscissa) the count is zero, the traversal's terminal payoff | **Qed** |
| 5c-2 | **The four-orientation passage kit** (`JCTPassageKit.v`): corner moves west/east × under/over with uniform interfaces; the x-flip can't transport the ray guard, so destinations expose *level freshness* instead (parked in a `depth_gap`; `ray_guard_of_fresh` recovers the guard in any direction). Conditions in original coordinates: `corner_opens_east`(`_top`) / `corner_opens_west`(`_top`) | **Qed** |
| 5c-3 | **The under-tip crossing** (`JCTTipCrossing.v`): at a local-minimum corner the band just below `v` is skeleton-free across the whole corner — the side-switch move connecting west-side passage destinations to east-side corridors (y-flip: over a local-maximum tip). Incident edges sit entirely above the level; non-incident edges get taut margins (`hprobe_avoid_level_crossing`) | **Qed** |
| 5c-4 | **The corner boxes** (`JCTCornerBox.v`): the 4b-3 dispatch clears the whole abscissa interval, so its fold gives a skeleton-free *rectangle* beside the corner, in all four orientations via the mirror kit; `box_connected_of_clear` connects any two points of a free rectangle. The boxes absorb all corner glue: drops, rejoin jogs, passage↔tip-crossing transfers | **Qed** |
| 5c-5 | **The ring-cycle structure** (`JCTRingCycle.v`): proper rings (`ring_core_nodup`), edge membership = list splitting, unique in/out edge per vertex (the seam vertex handled), `incident_two` (degree-2: every incident edge is the in- or out-edge — discharging the corner conditions against the cycle neighbours), `cyclic_next`/`_prev`, the achieved eastmost vertex, and the `xsup`-free terminal count | **Qed** |
| 5c-6 | **The hug state + first composite** (`JCTHugStep.v`): `hugs_west` anchors connectivity at the span midpoint with all-offsets freedom; `hug_step_pass_down_west` carries it through a degree-2 downward pass-through corner with all corner conditions *discharged* via `incident_two`. Plus `wall_corridor_clear_corner_top` and `apex_abscissa_bound` (y-flip gap-fillers) | **Qed** |
| 5c-7 | **The mirrored hug steps** (`JCTHugMirror.v`): `hugs_east` + state transport through both reflections (`corridor_ymir`/`_xmir`, `mid_ymir`/`_xmir`, injective-map `NoDup`); `hug_step_pass_up_west`, `hug_step_pass_down_east`, `hug_step_pass_up_east` — all four pass-through composites now Qed by transport | **Qed** |
| 5c-8 | **The open-side local-min composite** (`JCTMinOpenStep.v`): `hug_step_min_open_we` — passage down e's west flank, under-tip crossing, east corner box, east corner-abutting rise; the hug side flips (`hugs_west e → hugs_east f`). East-side gap-fillers by x-flip pullback (`wall_corridor_clear_east`, `wall_corridor_clear_corner_east`, `corridor_connected_east`, `foot_abscissa_bound`); `incident_pair_min` | **Qed** |
| 5c-9 | **The mirrored turnarounds** (`JCTMinOpenMirror.v`): `hug_step_min_open_ew` (xmir), `hug_step_max_open_we` (ymir), `hug_step_max_open_ew` (both) — the open-side corner inventory complete (4 pass-throughs + 4 open turnarounds) | **Qed** |
| 5c-10 | **The corner disk** (`JCTCornerDisk.v`): non-incident edges miss a fixed square around each vertex (taut margins + the 5c-3 rectangle probe); no except-one clearance needed — the pinched descent splits into a fixed away-window (rung 4b-2, `f`'s clip margin positive there) plus the disk window where `e`/`f` clear pointwise | **Qed** |
| 5c-11 | **The pinched turnaround** (`JCTPinchedStep.v`): `hug_step_min_pinched_we` — wedge descent on a fixed 4b-2 window, cross-wedge jog (incident edges pointwise, others by the disk), east ascent; the wedge width's affine root at the corner fixes the band height before `δ`. The last corner move | **Qed** |
| 5c-12 | **Pinched mirrors + the bridge** (`JCTPinchedMirror.v`): the three pinched transports and `carrier_side_equiv` (the two extremum conditions are one slope comparison — single-`Rle_dec` dispatch). Corner-move inventory complete: 4 pass-throughs + 4 open + 4 pinched | **Qed** |
| 5c-13 | **The per-corner total step** (`JCTCornerDispatch.v`): `hugs := hugs_west ∨ hugs_east`; `hug_step_corner` rounds any degree-2 corner (height-sign dispatch, bridge `Rle_dec` for extrema, `corner_slopes_distinct` strictifying the pinched branch via `interior_param`) — the traversal's engine | **Qed** |
| 5c-14 | **The cycle walk + the entry** (`JCTHugCycle.v`): `hugs_everywhere` (hug one edge ⇒ hug all, list induction + seam wrap) and `hug_entry` (east approach → `hugs_west` of the first wall, anchored at the walker) | **Qed** |
| 5c-15 | **Edge-entry counting** (`JCTEdgeCount.v`): `ho_count_one_in` — exactly-one-crossing counts via positional split uniqueness (`ring_edges_split_pos`, `in_edge_prefix_unique`, `in_edge_count_le1`) — the payoff's odd case | **Qed** |
| 5c-16a | **The payoff kit** (`JCTPayoffKit.v`): out-edge counting symmetry, `noncross_far` (non-incidents never cross band rays near the eastmost vertex: convex-combination abscissae + the disk), the incident crossing kernels, `ho_count_zero_of_no_cross`, and the last clearance mirror (`wall_corridor_clear_corner_east_top`) | **Qed** |
| 5c-16b | **The payoff + assembly**: per-corner-type rides at the eastmost vertex harvesting a connected guarded point with count 0 (east rides / bands) or count 1 (west rides / wedge probes — odd, contradicting the even walker via `parity_constant_on_components`); `escape_descent_holds : ring_taut → ring_core_nodup → no_horizontal_edges → escape_descent r`; compose through `parity_seam_offring_of_descent` — H1 closed | open |

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
