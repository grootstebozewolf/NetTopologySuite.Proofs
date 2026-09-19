# Research — #824 rect-touch's six remaining DE-9IM cells (IB/IE/BI/BE/EI/EB)

Read-only research ticket, child of map #822. No `.v` files were changed.

## Sources consulted

- `theories/RelateNGRect.v` — `rect_pair_regime`, `rects_touch_vertical_edge`,
  `touch_rect_pair_ii_cell` / `_ee_cell` (Qed), `touch_rect_pair_bb_cell_shape`
  (classifier-constant only), the deferral note at line 341.
- `theories/RelateNGTouchCells.v` / `RelateNGTouchEdgeCells.v` — the
  **triangle**-touch analogue, including the already-landed
  `touch_edge_pair_ogc_gtri_cells : FF2F11212` (all nine cells, gtri
  vocabulary, Qed, no ray-genericity guard needed for the six cells this
  ticket is about — only the triangle II cell needs the JCT-seam bridge).
- `docs/adr/ADR-0003-...md` — spec tier (open interior) vs. computation tier
  (`point_in_ring` half-open parity), bridged only for the tricky cells.
- `theories/RectangleJCT.v:182 point_in_ring_rect_iff` — the load-bearing
  formula: parity region is `y0 < py < y1 ∧ x0 <= px < x1` (left edge
  included, right/top/bottom excluded).
- `theories/RelateCurveMatrix.v:171-186` — `SInt := point_set` (parity),
  `SExt := ~point_set` (parity complement), `SBnd := geom_boundary` (exact,
  closed edges, parity-independent). `SInt`/`SBnd` overlap on the left edge;
  `SBnd`/`SExt` overlap on the other three edges — this is the concrete shape
  of the "half-open" cost ADR-0003 names.
- `docs/relate-ng-status.md`, `docs/scout/map-522.md`,
  `docs/rect-triangle-touch-milestone.md` for provenance/vocabulary.

## Setup

Vertical touch: `A = [ax0,ax1]×[ay0,ay1]`, `B = [bx0,bx1]×[by0,by1]`,
`bx0 = ax1`, y-ranges overlap (`Rmax ay0 by0 < Rmin ay1 by1`,
`rects_touch_vertical_edge`). Horizontal touch is the same argument rotated
90°. Corner-touch (point contact only) is a degenerate sub-case not covered
by `rects_touch_vertical_edge`/`rects_touch_horizontal_edge` as currently
named in the repo — flagged below, not analyzed in depth.

**Headline finding: the true OGC value of the six cells is the standard
"adjacent-polygon" pattern, already Qed for triangles as `FF2F11212`
(`RelateNGTouchEdgeCells.v : touch_edge_pair_ogc_gtri_cells`) — and the rect
case is strictly *easier* to prove than the triangle case for five of the
six cells, because axis-alignment turns every argument into one-sided
interval inequality instead of `gtri`-sign algebra.**

## Per-cell classification (spec tier = open interior, per ADR-0003)

| Cell | Value | Class | Guard needed? | Proof shape |
|---|---|---|---|---|
| **IB** | `F` (None) | (a) fixed, unconditional | none — holds under spec *and* literal coded `point_set` | `A`-interior gives `px < ax1`; `B`-boundary gives `px >= bx0 = ax1`. Same x-separation `Rlt_irrefl` pattern as the landed `touch_rect_pair_ii_cell`. |
| **BI** | `F` (None) | spec tier: (a) fixed, unconditional *once stated against an open-box interior predicate* — none exists in `RelateNGRect.v` yet (no rect analogue of `tri_interior`). Coded tier (`SInt := point_set`): **(c) genuinely false, unguarded, no rescue** | Spec: none (pure interval arithmetic). Coded/parity: **no guard fixes it** — the counterexample is the whole shared-edge interior, not an edge case. | Counterexample: `touch_vertical_bb_point`'s midpoint `(ax1, mid)` is on `A`'s boundary (right edge) *and* in `B`'s coded `point_set` interior, because `point_in_ring_rect_iff` puts `B`'s **left** edge (`px = bx0`) inside `B`'s parity region. This is exactly the ADR-0003 "BI ... nonempty against a matrix specifying F" cost, made concrete. |
| **IE** | `Some 2` | (a) fixed, unconditional | none | `A`'s point_set/spec-interior forces `px < ax1 = bx0`, which alone satisfies `B`'s exterior (`~point_set B`, whose complement disjunct `px < bx0` fires regardless of `py`). So `A`'s whole interior ⊆ `B`'s exterior: dim 2, nonempty as long as `A` is nondegenerate (`ax0 < ax1`). Does **not** even need the y-overlap hypothesis. |
| **EI** | `Some 2` | (a) fixed, unconditional | none | Symmetric to IE: `B`'s interior forces `px >= bx0 = ax1`, which alone satisfies `A`'s exterior. |
| **BE** | `Some 1` | (a) fixed, unconditional | none | `A`'s *left* edge (`px = ax0 < ax1 = bx0`) is entirely inside `B`'s exterior regardless of `py`; a full 1-D segment, so dim exactly 1 (bounded above by `A`'s boundary being 1-D). |
| **EB** | `Some 1` | (a) fixed, unconditional | none | Symmetric: `B`'s right edge (`px = bx1 > bx0 = ax1`) is entirely inside `A`'s exterior. |

Assembled, the six cells plus the already-Qed II/EE and the classifier-shape
BB give exactly **`FF2F11212`** — the standard OGC "polygons share a boundary
segment" matrix, matching the triangle result bit for bit.

## Why the rect classifier's current constant fill is wrong, not just incomplete

`rect_pair_fill RPR_TouchVert` (frozen in
`touch_rect_pair_bb_cell_shape`) is `{ii:F, ib:F, ie:F, bi:F, bb:1, be:F,
ei:F, eb:F, ee:2}` — i.e. `FFFFF1FF2`. Per the table above, **IE, EI, BE, EB
are actually `2, 2, 1, 1`**, not `F`. This mirrors the triangle finding
already on record in `RelateNGTouchEdgeCells.v`
(`ogc_touch_ie_not_classifier` / `triangle_touch_fill_ie_still_empty`): the
classifier fill under-reports. Reminting `rect_pair_fill`/`aa_matrix_touch_vertical`
is out of scope here (that's the classifier-remint work flagged in
`map-522.md`, and BB's real-pointset upgrade is #825) — noted only so the
next ticket doesn't reopen this as a fresh discovery.

## IB vs. BI: the one place spec and parity genuinely diverge

IB and BI look symmetric but are not, because the half-open parity
convention is asymmetric (it favors the **left** edge). IB uses `A`'s
interior against `B`'s boundary — both tiers agree because the relevant
inequality (`px < ax1`) is on the boundary the two tiers *agree* about (the
right/upper side of `A`). BI uses `A`'s boundary against `B`'s interior —
the relevant inequality is on `B`'s **left** edge, exactly where
`point_in_ring_rect_iff` diverges from the open box. So BI is the honest
rect analogue of the triangle II cell's split between the algebraic
(`tri_interior`, unconditional) and parity (`point_set`, guard-carrying)
statements — except for BI **no guard exists that rescues the parity
statement**, because the failing region is the entire shared edge, not a
measure-zero adversarial point (contrast triangle II's vertex-grazing
witness, which needs an adversary). BI is a case where "provable under a
named guard" isn't available; the honest move is to decline the literal
`cell_ok None SBnd SInt` claim and instead prove the spec-tier fact against
a new (trivial-to-add) open-box interior predicate, exactly as `tri_interior`
was added for triangles rather than fixing `point_set`.

## Connection to the triangle-touch case (#823)

The rect case transfers the triangle *destination* value (`FF2F11212`)
without needing the triangle case's heaviest machinery:

- **IE/EI/BE/EB**: triangle versions (`touch_ie_dim2`, `touch_ei_dim2`,
  `touch_be_dim1`, `touch_eb_dim1` in `RelateNGTouchEdgeCells.v`) need
  disk/witness constructions and `gtri_le_gsB`/`gsC` sign-comparison lemmas
  because a triangle edge isn't axis-aligned. For rects the same four cells
  reduce to one-line interval inequalities (no witnesses needed beyond
  "any point of the known-nonempty region"). **Expect full transfer of the
  value, with a much shorter proof** — this is the "rects are simpler"
  case working as expected.
- **IB**: triangle's `touch_ib_empty` uses `touch_int_ext_exclusion` (an
  algebraic sign-flip lemma across the shared edge's line). Rect's IB uses
  plain `Rlt_irrefl` on x-coordinates — same shape, simpler.
  **Transfers directly.**
- **BI**: triangle's `touch_bi_empty` is Qed via `gtri_nonneg_iff` /
  `gtri_pos_iff` stated purely in the `gtri` (spec/open) vocabulary — it
  never touches `point_set`, so the triangle module sidesteps the
  parity-divergence issue entirely by never proving the BI cell against
  `point_set` in the first place. **This is the key transfer lesson for
  rects**: don't try to prove `cell_ok None SBnd SInt` against
  `RelateCurveMatrix.point_set`; prove it against a rect-`tri_interior`
  analogue (`ax0 < px < ax1 ∧ ay0 < py < ay1`, pure `lra`), the same move
  ADR-0003 already blesses. Once that predicate exists, BI **transfers
  directly and becomes unconditional** — no guard, unlike anything in the
  triangle II story, because axis-aligned separation needs no ray-genericity
  argument at all (it's a straight interval comparison, not a Jordan-curve
  argument).
- **Divergence point**: the triangle module never needed a JCT-seam-style
  bridge for these six cells at all (only triangle II did, elsewhere in
  `RelateNGTouchCells.v`). So the *expected* rect story is: five cells
  (IB, IE, EI, BE, EB) are immediate one-line transfers; BI needs exactly
  one new definition (open-box interior) mirroring `tri_interior`, after
  which it too is unconditional. No cell in this six needs anything like
  `ring_complement`/`ray_avoids_vertices`.

## Corner-touch caveat (not analyzed)

`rects_touch_vertical_edge`/`_horizontal_edge` require a strict y/x-overlap
(`Rmax < Rmin`), so pure corner contact (rectangles touching at a single
point, `Rmax = Rmin`) is a different, unnamed regime not covered by this
analysis or by the existing Qed lemmas. If #822/#824's scope later widens to
corner touch, the six-cell table above does not apply as-is (BB would become
a single point, not a segment, and BE/EB/IE/EI's "full edge is exterior"
argument still works but IB/BI's argument needs re-checking against a
degenerate zero-length shared edge).

## Summary table (for the issue comment)

| Cell | Value | Class | Guard | Rect vs. triangle |
|---|---|---|---|---|
| IB | F | (a) unconditional | none | transfers, simpler |
| BI | F (spec) / **false** (literal `point_set`) | (a) spec / (c) coded-tier decline | none rescues the coded form | transfers once a `tri_interior`-style predicate is added; triangle already avoids the trap by never using `point_set` here |
| IE | Some 2 | (a) unconditional | none | transfers, simpler |
| EI | Some 2 | (a) unconditional | none | transfers, simpler |
| BE | Some 1 | (a) unconditional | none | transfers, simpler |
| EB | Some 1 | (a) unconditional | none | transfers, simpler |

Assembled with the already-Qed II (F) and EE (Some 2), and BB (Some 1, shape
only, real-pointset upgrade is #825), the full spec-tier rect-touch matrix is
`FF2F11212` — identical to the triangle touch-edge result.
