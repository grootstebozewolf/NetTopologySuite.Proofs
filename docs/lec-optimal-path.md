<!-- doc-kind: guide -->
# The LEC optimal-path ledger — failed hypotheses as guides

**Lane**: LargestEmptyCircle (construct) · **updated**: 16 Aug 2026 ·
**modules**: `theories/LECChordGap.v`, `theories/LECObstacleDistance.v`,
`theories/LECArcRow.v`, `theories/LECSegmentRow.v`,
`theories/LECFlattenRow.v`, `theories/LECCandidateVertex.v`,
`theories/LargestEmptyCircle.v`, `theories/CellRadiusBound.v` ·
**oracle**: `LEC_CIRCLE`, `OBSTACLE_DISTANCE` (5-row typed table + §I
candidate sweep), `ARC_DISTANCE` (§C pins)

This lane runs prove-or-disprove: each engine-side hypothesis about how the
largest empty circle can be computed FASTER is either Qed-proven or refuted
by a Qed-closed disproof on an explicit witness cell.  **A refuted
hypothesis is not discarded — it is recorded here, because each failed path
constrains what the theoretically optimal algorithm must do.**  This file is
the prose ledger of those refutations and of the guide each one leaves
behind.

## The target: what "optimal" means here

JTS/NTS `LargestEmptyCircle` ships branch-and-bound: subdivide the domain
into square cells, bound each cell's achievable radius, refine the best
cell until the bound gap is under tolerance.  Its cost scales with the
subdivision depth, not just the obstacle count.  The theoretical optimum
for POINT obstacles is candidate enumeration: the maximiser of
nearest-obstacle distance over a bounded domain lies at a Voronoi vertex,
at a Voronoi-edge × boundary crossing, or on the boundary structure — a
finite candidate set computable in O(n log n) (Toussaint 1983,
doi:10.1007/BF00993201).  For DISC obstacles the additively-weighted
Voronoi (Apollonius) diagram plays the same role, because distance to a
filled disc is exactly the additively-weighted distance to its centre once
clamped at zero — the reduction proven as `min_disc_dist_weighted`.

The corpus's job is the exactness half: prove the closed forms an optimal
algorithm would enumerate, and refute the shortcuts that look cheaper but
are wrong.  The runtime half (median laser vs chainsaw under the perf
gate's 15% slack) stays engine-side by design.

## The ledger

### F1 — "the chord path is enough" (REFUTED · `LECChordGap.v`)

- **Hypothesis** (PERF-GATE, LEC row): "LargestEmptyCircle stays on the
  chord path — no cheaper construction beat densify-then-LEC."
- **Verdict**: disproved as an exactness claim on the single-circle-
  obstacle cell.  `lec_chord_hypothesis_refuted`: the exact LEC of the
  radius-2 circle over its disk is the closed form (centre, 2); the
  4-chord densification's exact answer is (centre, √2); every finite
  chording underestimates by cos(θ/2).
- **Witness**: circle r=2 about the origin vs its inscribed-square
  chording — laser 2, chainsaw √2.
- **Guide**: per-shape CLOSED FORMS exist where densification only
  converges.  The replacement is a typed per-component metric — which the
  engine then implemented (`ObstacleDistance`, jts-curve typed-obstacle
  lane) and F2/F3's module proved exact.

### F2 — "corners are enough" (REFUTED · `LECObstacleDistance.v`)

- **Hypothesis** (H-CORNER): "a radius achievable somewhere in a cell is
  achievable at one of the cell's corners" — the vertex-sampling shortcut
  that would let branch-and-bound bound a cell by evaluating its corners
  and skip `CellRadiusBound.v`'s √2·h Lipschitz slack.
- **Verdict**: `corner_sampling_hypothesis_refuted`.  On the 3-4-5
  witness cell (discs r=3 at (±4,0), domain [−4,4]×[−3,3]) all FOUR
  rectangle corners touch the discs — clearance exactly 0 — while the
  rectangle centre clears exactly 1 (`corner_clearance_zero`,
  `centre_clearance_one`).
- **Why it fails structurally**: min-of-distances is not convex; its
  maxima sit on bisectors in the cell INTERIOR, invisible from the
  vertices.
- **Guide**: cell bounds must carry the Lipschitz slack.  Together with
  9004-d this is a pincer: `cell_achievable_radius_bound` proves the
  centre-clearance + √2·h bound SOUND, its cell-slack witness proves the
  slack not droppable, and H-CORNER proves the vertex-only alternative
  UNSOUND.  The subdivision bound JTS ships is, in this exact sense, the
  right one — the speed frontier is not in weakening it but in replacing
  enumeration of cells with enumeration of candidates (F3).

### F3 — "the optimum is interior" (REFUTED · `LECObstacleDistance.v`)

- **Hypothesis** (H-INTERIOR): "the LEC centre may be searched among
  interior points" — e.g. only at interior equidistant points (Voronoi/
  Apollonius vertices, ≥3 obstacles tied), the tempting pure-vertex
  candidate set.
- **Verdict**: `interior_maximiser_hypothesis_refuted`, via
  `lec_two_discs_maximisers`: on the witness cell the maximisers are
  EXACTLY (0, ±3) — on the domain boundary (py = ±3), on the two-disc
  bisector, equidistant from just TWO obstacles.  No point of the cell is
  equidistant from three obstacles at the optimum radius; an
  Apollonius-vertex-only enumeration finds nothing.
- **Guide**: the optimal candidate set is Toussaint's, transported to
  discs by the Apollonius reduction (`min_disc_dist_weighted`):
  weighted-Voronoi VERTICES ∪ (weighted-Voronoi EDGES × boundary
  crossings) ∪ boundary structure.  The witness optimum (0,3) is a
  bisector × boundary crossing — the middle class, the one H-INTERIOR
  drops.

### F4 — "gate the sector on the query point" (REFUTED · `LECArcRow.v`)

- **Hypothesis** (H-QUERYGATE): "the chord-sign sector gate may test the
  query point P itself instead of its radial foot" — one projection
  cheaper, and seemingly safe because the atan2 gate does exactly that
  (angle(P) = angle(foot): rays through the centre are angle-invariant).
- **Verdict**: `query_side_sector_hypothesis_refuted`.  On the minor arc
  (3,4)–(0,5)–(−3,4) of the r=5 circle about the origin, the query
  P = (16,12) and the arc mid lie on the SAME side of the chord y = 4
  (sign product 288 > 0), so the naive gate admits the radial branch and
  prices the window at |20 − 5| = 15.  But the radial foot (4,3) lies on
  the OTHER side (product −36 < 0): the Qed clearance is the endpoint
  fallback √233 > 15.2.  The naive row UNDERSTATES the obstacle
  distance, so an LEC built on it rejects radii in (15, √233] that are
  actually empty — the certified circle silently shrinks below the true
  optimum, an exactness failure no perf gate can see.
- **Why it fails structurally**: the span⇔sign equivalence
  (`arc_span_contains_iff_sign`) is a theorem ON THE CIRCLE: the chord
  line separates the circle's two arcs, but it does not sort the plane
  by which arc a ray hits.  A query can cross the chord line while its
  foot does not.
- **Guide**: gates and metrics live on different domains.  Angular gates
  are ray-invariant (may take P); algebraic sign gates are circle-bound
  (must take the foot).  The certified total form (`arc_dist`) projects
  first — and the `ARC_DISTANCE` §C pins now trip any atan2 → chord-sign
  refactor that forgets to.

### F5 — "seed the empty fold with unit 0" (REFUTED · `LECFlattenRow.v`)

- **Hypothesis** (H-EMPTYFOLD): "the min-fold flatten extends to the empty
  member list with fold unit 0" — the tempting `fold(min, 0, [])` base
  case an implementer reaches for when the collection has no members.
- **Verdict**: `empty_fold_zero_unit_hypothesis_refuted`.  Against an
  empty obstacle list EVERY radius is empty (the emptiness quantifier is
  vacuous), so the iff with threshold 0 already fails at rho = 1 — and no
  finite unit can repair it: for any candidate v, rho = max(0, v) + 1 is
  empty yet exceeds v (`empty_fold_no_finite_unit`).  Rmin has no unit
  in R.
- **Why it fails structurally**: the flatten is an infimum over member
  clearances; an empty infimum is +∞, which R does not contain.  Any
  finite default converts "no obstacles" into "an obstacle at distance
  v" — it does not understate a constraint, it INVENTS one, capping the
  LEC at v for no reason.
- **Guide**: k = 0 must be a VERDICT, not a value.  The oracle's
  `OBSTACLE_DISTANCE` k = 0 → DEGENERATE gate is the mathematically
  forced behaviour, now theorem-backed; engines should reject or
  special-case empty obstacle collections rather than fold a default.

### F6 — "the supporting line's foot suffices" (REFUTED · `LECSegmentRow.v`)

- **Hypothesis** (H-LINEFOOT): "the point-to-segment distance is the
  distance to the perpendicular foot on the supporting line" — the
  clamp-free projection an implementer gets by reusing a point-to-LINE
  routine for a facet.
- **Verdict**: `seg_line_foot_hypothesis_refuted`.  For A = (0,0),
  B = (4,0), P = (7,4) the foot lands at (7,0) — distance 4 — but the
  segment's nearest point is the ENDPOINT B = (4,0) at distance 5 (a
  3-4-5 witness).  The unclamped foot UNDERSTATES whenever the foot
  parameter leaves [0,1]: the segment is not its line.
- **Why it fails structurally**: the quadratic |P − A − t(B−A)|² is
  minimised over ℝ at the foot t₀, but over the FACET the domain is
  [0,1]; convexity pushes the constrained minimum to the nearer endpoint
  exactly when t₀ exits.  Dropping the clamp inflates every empty-circle
  radius bound near segment ends — the LEC would claim clearance that a
  facet endpoint already violates.
- **Guide**: the clamp is not an optimisation, it IS the row
  (`seg_dist`, proven exact in `empty_disk_seg_iff`; the degenerate
  A = B facet collapses to the POINT row, `seg_dist_degenerate`, so no
  validity gate is needed).  Oracle `OBSTACLE_DISTANCE` §H pins the trap
  numerically: at the witness the row answers 5 where the foot says 4.

### F7 — "interior candidates suffice" (REFUTED · `LECCandidateVertex.v`)

- **Hypothesis** (H-INTERIOR): "the LEC maximiser lies strictly inside
  the domain, so a candidate enumeration may skip the boundary classes"
  — the shortcut that walks only Voronoi vertices.
- **Verdict**: `interior_maximiser_hypothesis_refuted`.  The two-disc
  corpus cell already kills it: BOTH its maximisers (0, ±3)
  (`lec_two_discs_maximisers`) sit ON the rectangle's boundary — they
  are bisector × boundary crossings, not interior vertices.
- **Why it fails structurally**: the clearance function is convex-cell
  concave-ish along bisectors; when the unconstrained tie point leaves
  the domain, the max slides to where the bisector CROSSES the boundary
  — a class the interior-only walk never visits.
- **Guide**: both candidate classes are load-bearing, and the pairing of
  witnesses proves each non-redundant: the three-point instance's unique
  maximiser is the INTERIOR Voronoi vertex (`lec_three_points`), the
  two-disc instance's maximisers are BOUNDARY crossings.  An enumeration
  must walk vertices AND bisector × boundary crossings AND domain
  vertices — exactly `tri_candidates`'s three classes.

### F8 — "≥ 3 nearest sites, no interiority needed" (REFUTED · `LECCandidateComplete.v`)

- **Hypothesis** (H-NO-BALL): "an LEC maximiser always has ≥ 3 nearest
  sites, so the interior-ball premise of the general candidate theorem
  is bureaucracy" — the reading that would let an implementation skip
  the boundary candidate classes whenever the domain is convex.
- **Verdict**: `f8_interiority_load_bearing`.  Two sites at (0,0) and
  (2,0) with the domain their connecting segment: the midpoint (1,0) IS
  the largest-empty-disk centre (radius 1, `f8_led`) yet has exactly
  TWO nearest sites (`f8_within_two`).  The domain has empty interior,
  so the ball premise fails at every point — and must.
- **Why it fails structurally**: the improvement kernel needs room to
  move.  On a degenerate (lower-dimensional) domain the only legal
  directions are along the domain, and along the segment the midpoint's
  two antipodal away-vectors genuinely block first-order improvement.
  The instance is also the antipodal trap for the naive direction
  d = u₁ + u₂ = 0 (the generic two-nearest supplier degenerates; the
  perpendicular rescues improvement only OFF the segment).
- **Guide**: degenerate domains route to the EDGE theorem (where two
  nearest sites are permitted — the midpoint is a bisector crossing,
  `f8_midpoint_not_within_one` confirms within-ONE fails), never to the
  interior theorem.  An implementation may use the ≥ 3-nearest filter
  only where a 2-D ball fits inside the domain.

### F9 — "the sum-direction supplier survives weighting" (REFUTED · `LECCandidateWeighted.v`)

- **Hypothesis** (H-SUM-WEIGHTED): "F8's two-nearest supplier d = u₁+u₂
  works for the additively-weighted clearance too — a tie is a tie" —
  the reading under which the Apollonius rung would be a renaming pass.
- **Verdict**: `f9_unweighted_supplier_refuted`.  At the weighted tie
  p = (0,0), discs ((−1,0), ½) and ((4,−3), 9⁄2) — norms 1 vs 5,
  clearance ½ — the sum direction u₁+u₂ = (−3,3) strictly WORSENS the
  clearance for every t ∈ (0, 1/3) (`f9_sum_direction_worsens`: the
  squared distance to c₁ along it is 1 − 6t + 18t² < 1).  No step bound
  rescues it.
- **Why it fails structurally**: with equal norms,
  ⟨u₁+u₂, u₁⟩ = |u₁|² + ⟨u₁,u₂⟩ ≥ |u₁|² − |u₁||u₂| = 0; with UNEQUAL
  norms the same bound reads |u₁|² − |u₁||u₂| < 0 — the sum direction
  can point INTO the nearer site.  The tie is in the weighted values,
  not the norms, and the supplier only ever saw the norms.
- **Guide**: the repaired supplier is the weighted-bisector normal
  v = d₂·u₁ + d₁·u₂ (square-root-free; ⟨v,uᵢ⟩ = dᵢ·N with
  N = d₁d₂ + ⟨u₁,u₂⟩, one sign for the whole case split).  With equal
  weights v = d·(u₁+u₂): F8 is the equal-weights slice
  (`equal_weights_tie_unweighted`).

### F10 — "MIC can only be made performant with chord approximation" (REFUTED · `MICChordNecessity.v`)

- **Hypothesis** (H-CHORD): "the MIC branch-and-bound certificate — JTS
  `Cell.getMaxDistance` soundness, the fact that makes grid pruning
  correct — requires linearizing curved boundaries into chords."  (The
  wall-clock half of "performant" stays engine-side per policy; the
  corpus adjudicates the mathematical necessity claim.)
- **Verdict**: counterexample, in both directions.  POSITIVE:
  `mic_cell_bound_exact_arc` — the 9004-d cell bound instantiated at
  the attaining point of the exact arc metric gives
  r' ≤ arc_dist a c + √2·h with the closed-form callback and no chord
  anywhere (same for segment facets, `mic_cell_bound_exact_seg`; the
  1-Lipschitz certificates fall out of the same exactness pair).
  NEGATIVE: chords are structurally inexact — EVERY chord of a circle
  strictly understates the clearance at the centre
  (`chord_strictly_understates`, parallelogram law: the midpoint sits
  at squared depth r² − |AB|²/4), in particular the arc's own chord
  (`chord_of_arc_understates_at_centre`).  The integer 3-4-5 instance
  pins the gap: arc (3,4)→(5,0)→(3,−4) about (0,0), exact clearance 5,
  chord clearance 3 (`mic345_chord_gap`).
- **Why it fails structurally**: the certificate never consumed
  linearity — it is two triangle steps over an abstract obstacle
  region, and the only thing the metric must supply is exactness
  (lower bound + attained), which the typed arc row proved.  Chord
  refinement, by contrast, converges from below and reaches the arc
  value at no finite resolution.
- **Guide**: swap the clearance callback, keep the grid — exactly the
  jts-curve engine posture (JTS PR #8).  The certified per-row metrics
  make the swap sound; the chord path is a lower bound, usable only
  as a pruning UNDERestimate, never as the answer.
- **WAYPOINT (parked path, not a verdict)**: the O(n log n)
  candidate-walk half for curved boundaries is NOT settled.  The F8/F9
  improvement kernels fix their sites — the kernel hypothesis names a
  per-site away-vector p − s with s constant — but an arc obstacle's
  nearest point a*(p) moves with p, so the two-nearest supplier does
  not instantiate as-stated.  The attempted reduction (freeze a*(p) as
  a point site per step) fails in the kernel's tie case: the frozen
  site's distance is only a lower bound off the foot, and strict
  improvement needs the true arc distance.  Candidate completeness
  over arc obstacles — bisectors of arcs are conic loci — is the next
  genuine rung on this wall.

## What is Qed today (the verified bridge under the engine's table)

- **Filled-disc row exact**: `empty_disk_disc_iff` — emptiness of the
  disc obstacle at radius ρ ⟺ ρ ≤ max(0, dist(c,P) − r).  Lower bound by
  the reverse triangle inequality; ATTAINED by P itself (inside) or the
  radial projection onto the bounding circle (outside).
- **Full-circle-ring row exact**: `empty_disk_ring_iff` — same two
  halves for abs(dist(c,P) − r); from the very centre any circle point
  attains r.  (The disc/ring distinction the engine's table draws —
  filled CurvePolygon vs closed CircularString — is exactly the clamp.)
- **Flatten row sound**: `empty_disk_union_iff` /
  `empty_disk_two_discs_iff` — emptiness against a union is emptiness
  against each part; collection clearance is the min-fold.
- **Apollonius reduction**: `min_disc_dist_weighted` — clamping commutes
  with min, so LEC over discs ≡ additively-weighted LEC over centres.
- **A closed curved-collection cell**: `lec_two_discs` — the LEC of two
  3-4-5 discs over a rectangle is ((0,3), 2), fully rational, maximisers
  characterised exactly.  The oracle mode `OBSTACLE_DISTANCE` gates the
  pins bit-exact (clearance 2 at (0,±3), 1 at the centre, 0 at the four
  corners).
- **Point-to-arc row exact, TOTAL** (`LECArcRow.v`, closes the former
  rung 1): `arc_dist_exact` / `empty_disk_arc_iff` — the engine's
  CircularString per-window row.  The banked analytic core
  (`ArcPointDistance.v` radial/fallback/centre cases over
  `ArcSinglePeak.v`'s single-peak dot bound, Qed 2026-07-01) is glued
  into ONE unconditional closed form: centre → r (nearer endpoint);
  foot passes the chord-sign gate → |d − r|; else → nearer endpoint.
  New glue: the circumcircle meets its chord LINE only at the chord
  endpoints (`on_circle_side_zero_is_endpoint`, divisionless
  q·(q − m) = 0 collapse), so the span predicate IS one sign test
  (`arc_span_contains_iff_sign`) — decidable and atan2-free.  With
  `empty_disk_union_iff` this prices every CompoundCurve window.
- **Flatten row exact, N-ARY** (`LECFlattenRow.v`, closes the former
  flatten rung): `empty_disk_list_iff` — emptiness against a finite
  union is emptiness against every member — and the headline
  `empty_disk_flatten_iff`: the min-fold of the typed per-member closed
  forms over a NONEMPTY list is exactly the collection's emptiness
  threshold.  One `exact_clearance` interface (lower bound + attained)
  packages the typed rows (`typed_row_exact`), `exact_clearance_union`
  closes it under union with value Rmin, and `exact_clearance_fold`
  folds it down the member list — the engine's
  `getNumMembers`/`getMemberN` min, as one Qed statement.  The oracle's
  `OBSTACLE_DISTANCE` speaks the matching ARC member row (singleton
  bit-parity with `ARC_DISTANCE`, mixed min-folds pinned bit-exact).
- **Segment/facet row exact** (`LECSegmentRow.v`, closes the last
  per-component rung): the clamped projection
  t* = clamp((P−A)·(B−A)/|B−A|², 0, 1) is the EXACT facet distance —
  lower bound by the clamped-quadratic minimisation (interior branch
  L·(f(t) − f(t*)) = (Lt − s)², endpoint branches by sign), attainment
  definitional at the clamp point (`empty_disk_seg_iff`).  TOTAL: the
  zero-length facet collapses to the point row
  (`seg_dist_degenerate`) — no validity gate.  Slotted into the typed
  table as `TSeg` (fifth row), so the flatten prices facets into
  collections with zero new proof work — the first payoff of the
  `exact_clearance` abstraction.  Oracle: SEG member row, §H clamp pins
  (interior 3, endpoint 5-not-4, zero-length == POINT bit-exact).
- **Candidate completeness, WITNESS-SCOPED** (`LECCandidateVertex.v`,
  the summit rung's witness half): for the three-point instance —
  sites (0,0), (4,0), (2,3), domain their hull — the LEC is the
  interior Voronoi vertex (2, 5/6) at radius 13/6
  (`lec_three_points`, stated through `largest_empty_disk` and priced
  by the flatten row's `empty_disk_flatten_iff`), the maximiser is
  UNIQUE (`lec_three_points_maximiser_unique`), and it lies in the
  finite three-class enumeration {Voronoi vertex; bisector × boundary
  crossings; domain vertices} (`maximiser_is_candidate`).  Proof
  engine: hand-found per-cell Handelman certificates — e.g.
  169 − 36(x² + y²) = 52(2−x) + 5(13−4x−6y) + 12(2−x)(3x−2y) +
  6(13−4x−6y)y on A's cell — giving the bound AND the uniqueness from
  one `ring` identity each, no solver search.  Paired with F7 (the
  two-disc maximisers are boundary crossings), the two witnesses prove
  both candidate classes non-redundant.  Oracle: `OBSTACLE_DISTANCE` §I
  — vertex ≈ 13/6 at 1e-12, mirror-symmetric edge crossings
  bit-identical, 109-sample grid sweep never beats the enumeration.

- **Candidate completeness, GENERAL for point sites**
  (`LECCandidateComplete.v`, the summit rung's general half): for
  ARBITRARY finite point-site sets, every largest-empty-disk maximiser
  with positive clearance is a candidate — an interior maximiser can
  never have its nearest sites covered by two points
  (`lec_candidate_completeness_interior`: it is a Voronoi vertex, ≥ 3
  nearest sites), and a maximiser strictly inside a domain edge can
  never have a unique nearest site
  (`lec_candidate_completeness_boundary_edge`: it is a bisector ×
  boundary crossing); domain vertices are the only remaining boundary
  points.  Proof engine: ONE improvement kernel
  (`improvement_kernel`) over the shift expansion
  dist²(p + t·d, s) = r² + 2t·⟨d, p−s⟩ + t²·|d|², with the inner
  product required only ≥ 0 — the quadratic term forces strict
  improvement, so the unique-nearest, generic two-nearest
  (d = u₁ + u₂, strict positivity by the nonzero-square trick — no
  Cauchy–Schwarz), ANTIPODAL two-nearest (d = the perpendicular, inner
  products exactly zero), and along-edge (d = ±e) cases all feed the
  same engine.  The positive forms (`within_two_improvable`,
  `within_one_improvable_on_segment`) CONSTRUCT the strictly better
  centre; the maximiser theorems are their negation-form corollaries,
  so the whole file is classic-free (standard trio only).  Oracle:
  `OBSTACLE_DISTANCE` §J — the sum-direction improvement pinned on a
  bisector point, the antipodal stall bit-identical at the F8 midpoint,
  the perpendicular rescue = √(1+t²) at 1e-12, and a 129-sample segment
  sweep confirming `f8_led`.

## Open rungs (in likelihood order)

The point-to-arc rung closed 15 Aug 2026 (`LECArcRow.v`, F4); the n-ary
flatten rung closed 16 Aug 2026 (`LECFlattenRow.v`, F5); the
segment/facet rung closed 16 Aug 2026 (`LECSegmentRow.v`, F6).  Every
per-component metric the engine's `ObstacleDistance` table computes now
has a Qed exactness spec.  **Candidate completeness closed
WITNESS-SCOPED 16 Aug 2026** (`LECCandidateVertex.v`, F7), **GENERAL
FOR POINT SITES 16 Aug 2026** (`LECCandidateComplete.v`, F8), and
**WEIGHTED (the Apollonius summit) 16 Aug 2026**
(`LECCandidateWeighted.v`, F9): every maximiser over arbitrary finite
point-site sets is an interior Voronoi vertex, an edge bisector
crossing, or a domain vertex — the theorem a trusted O(n log n) LEC
needs — and the same interior classification holds for the
additively-weighted clearance min (dist(p, cᵢ) − rᵢ) that
`min_disc_dist_weighted` reduces disc sites to.  The prediction below
verified exactly: the kernel's shift expansion survived verbatim
(per-site levels w + rᵢ), the sum-direction supplier did NOT — F9 pins
a weighted tie (norms 1 vs 5, a 3-4-5 instance) where the F8 formula
u₁+u₂ strictly WORSENS clearance for every t ∈ (0, 1/3) — and the
weighted-bisector normal v = d₂·u₁ + d₁·u₂ replaced it, with one
identity (|v|² = 2·d₁·d₂·N, ⟨v,uᵢ⟩ = dᵢ·N for N = d₁·d₂ + ⟨u₁,u₂⟩)
running the whole generic/antipodal/impossible case split
square-root-free.  What remains:

1. **Edge-constrained weighted variant**: the weighted analogue of
   `within_one_improvable_on_segment` (unique weighted-nearest site at
   a point strictly inside a domain edge) — same sign-matched ±e
   supplier expected.
2. **Polygon assembly**: a concrete convex-polygon domain type packaging
   interior/edge/vertex into one disjunctive classification statement —
   pure plumbing over the kernels once a polygon type exists in the
   lane.
3. **Runtime half**: stays engine-side (perf gate); the corpus only ever
   adjudicates exactness.

## Relation to the engine lane

The jts-curve typed-obstacle lane (JTS PR #8, `cursor/curve-perf-gate-45a0`)
keeps uncertified LEC on the branch-and-bound grid and swaps the clearance
callback for the typed metric — the F2 guide says that grid's bound is
right, the F1/F3 guides say where the next speed rung lives: certified
closed forms per cell class, then candidate enumeration on the Apollonius
side once the completeness rung lands.  The CircularString row is now
certified end-to-end: the engine's per-window metric has a Qed total twin
(`arc_dist`), the F4 guide fixes its gate discipline (project before any
chord-sign test), and the locked `OBSTACLE_DISTANCE` + `ARC_DISTANCE` §C
vectors are the differential handshake between the two sides.
