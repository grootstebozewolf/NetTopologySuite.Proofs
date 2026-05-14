# NetTopologySuite.Proofs

[![build proofs](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/actions/workflows/ci.yml/badge.svg)](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/actions/workflows/ci.yml)

Mechanically-verified formal proofs of foundational properties of the
algorithms in [NetTopologySuite](https://github.com/NetTopologySuite/NetTopologySuite).

Proofs are written in [Rocq Prover](https://rocq-prover.org/) (formerly Coq).
Every theorem in this repository terminates with `Qed.` — meaning the kernel
has checked the proof and rejected any unsound step. There are no admitted
lemmas. The only axioms used are the three standard ones bundled with Rocq's
classical real arithmetic library (printed at the end of each `.v` file
under `Print Assumptions` for transparency):

```
ClassicalDedekindReals.sig_not_dec
ClassicalDedekindReals.sig_forall_dec
FunctionalExtensionality.functional_extensionality_dep
```

These are the standard classical real-number axioms; no library-specific
or load-bearing axiom is introduced anywhere in this repo. CI fails if any
`Admitted`, `Axiom`, `Parameter`, or `admit.` appears in `theories/`.

## Why this exists

NetTopologySuite is a port of JTS. JTS is itself a port of academic
computational-geometry algorithms with subtle robustness properties — the
kind that you find a bug in three years later when an unusual coordinate
configuration trips a sign flip. Unit tests sample the behaviour at
finitely many points and produce green CI. Formal proofs cover all of
ℝ² simultaneously.

The intent is not to verify every line of NetTopologySuite. That's
infeasible for a library this size, and most of the C# code is mechanical
plumbing where formal verification adds little value. The intent is to
verify the **load-bearing primitives** — the handful of small algorithms
that, if wrong, make everything above them suspect. Orientation, distance,
the convex-hull invariants, the buffer-curve angle relations.

When someone asks "are you sure the squared-distance optimisation can't
flip a result?", the answer is `Distance.dist_le_iff_dist_sq_le` and the
kernel-checked proof. Not "yes, the tests pass."

## What's in scope right now

### `theories/Distance.v` — Euclidean distance

- `sqr_nonneg`, `sqr_eq_zero` — companion identities used throughout.
- `dist_sq_nonneg` — squared distance is non-negative.
- `dist_sq_sym` — squared distance is symmetric.
- `dist_sq_zero_iff_eq` — two points are at squared distance zero exactly
  when their coordinates are equal.
- `sq_monotone_nonneg` — on the non-negative reals, squaring is monotone.
- **`dist_le_iff_dist_sq_le`** — for any non-negative threshold *t*,
  `dist(p, q) ≤ t` iff `dist_sq(p, q) ≤ t²`. The formal justification
  for the optimisation tracked in
  [locationtech/jts#1111](https://github.com/locationtech/jts/pull/1111) and
  the gap noted for `LineStringSnapper` in the JTS 1.21 alignment audit on
  [NetTopologySuite#828](https://github.com/NetTopologySuite/NetTopologySuite/issues/828).
- `dist_nonneg`, `dist_refl`, `dist_sym` — distance (with `sqrt`) is
  non-negative, reflexive, symmetric.
- `dist_eq_zero_iff` — `dist(p, q) = 0` iff `p = q` coordinate-wise.

### `theories/Orientation.v` — orientation predicate

- `cross_antisymmetric` — swapping the second and third arguments of the
  cross product flips the sign. (Justifies "directed orientation" being
  a coherent concept.)
- `cross_swap_first_two` — swapping the first two arguments also flips
  the sign. Together with `cross_antisymmetric`, generates the full S₃
  sign action on the three arguments.
- `cross_collinear_sym` — collinearity is preserved under argument swap.
- `cross_at_P0_is_collinear` / `cross_at_P1_is_collinear` — degenerate
  triangles have zero signed area.
- `cross_translation_invariant` — translating all three points by the
  same vector preserves orientation. (Justifies coordinate-frame
  normalisation never changing topological results.)

### `theories/Segment.v` — finite line segments

The bridge from a parametric segment definition to the orientation
predicate. Every segment-intersection test in NTS (`LineIntersector`,
`RobustLineIntersector`, the overlay machinery) rests on this
correspondence.

- `Segment` — record type `{ sp0 : Point; sp1 : Point }`.
- `on_line P0 P1 Q` — Q lies on the infinite line through P0 and P1
  (defined as `cross P0 P1 Q = 0`).
- `between P0 P1 Q` — Q lies on the closed segment, defined parametrically
  as `∃ t ∈ [0, 1] · Q = (1-t)·P0 + t·P1`.
- `between_P0` / `between_P1` — endpoints lie on their own segment.
- `between_symmetric` — `between P0 P1 Q ↔ between P1 P0 Q` (reversing the
  segment direction preserves membership).
- **`between_implies_on_line`** — if Q is on the segment, then Q is
  collinear with the endpoints. This is the bridge that lets every
  cross-product-based intersection test treat "between" as a sufficient
  witness of collinearity without recomputing the line equation.
- `off_line_not_between` — contrapositive: a point with non-zero cross
  product against the segment line cannot lie on the segment. The form
  used by intersection-rejection fast paths.
- `on_line_symmetric` — the on-line relation does not depend on which
  endpoint of the segment is listed first.
- `between_in_coord_range` — a point on a segment has each coordinate
  within the closed range spanned by the corresponding coordinates of
  the endpoints. The algebraic basis for envelope/bbox rejection.

### `theories/Intersect.v` — segment intersection (soundness direction)

The forward direction of the cross-product based segment intersection
test used by `RobustLineIntersector` and the overlay machinery. If two
segments share any common point, then neither segment's line strictly
separates the other segment's endpoints.

- `convex_combination_zero_opposite_signs` — auxiliary: for *t* ∈ [0, 1],
  if `(1-t)·a + t·b = 0` then `a · b ≤ 0`.
- `cross_affine_in_third` — bilinearity of the cross product in its
  third argument; the algebraic fact powering the rest of the file.
- **`segments_share_point_implies_opposite_sides`** — the headline
  theorem. If `between A B X` and `between C D X`, then
  `cross(A,B,C) · cross(A,B,D) ≤ 0` **and** `cross(C,D,A) · cross(C,D,B) ≤ 0`.
- `same_side_rejection_is_sound` — corollary in the form NTS's
  intersection-rejection fast paths use. If either cross-product
  product is strictly positive, no shared point exists.

This is the soundness direction: every intersection-rejection decision
based on the cross-product sign test is justified, because a rejected
pair cannot have a common point. The converse (sign conditions imply a
shared point exists) is the next roadmap item.

### `theories/Vec.v` — 2D vector algebra

NTS uses 2D vectors implicitly throughout — direction vectors for
segments, normals for buffer offsets, basis transformations in affine
maps. This module spells out the algebraic laws so downstream theorems
can cite them rather than rebuild the ring reasoning.

- `Vec` record + zero / addition / negation / subtraction / scalar
  multiplication / dot product / squared magnitude.
- `Vec_eq` — extensionality principle: equal components ⇒ equal vectors.
- `vadd_comm`, `vadd_assoc`, `vadd_zero_l`, `vadd_zero_r`,
  `vadd_neg_r` — the abelian-group laws of vector addition.
- `vscale_distrib_add`, `vscale_assoc` — scalar multiplication laws.
- `vdot_comm`, `vdot_distrib_l` — dot product is symmetric and
  bilinear.
- **`vmag_sq_nonneg`** — squared magnitude is non-negative. The
  algebraic kernel of every "buffer thickness is non-negative" style
  reasoning downstream.

### `theories/Bbox.v` — axis-aligned bounding boxes

Every `LineIntersector` in NTS short-circuits on bounding-box
disjointness before doing any cross-product arithmetic. This module
verifies that short-circuit is sound.

- `Bbox` record + `in_bbox` predicate + `bbox_of_seg` construction +
  `bbox_disjoint` predicate.
- `bbox_of_seg_contains_sp0`, `bbox_of_seg_contains_sp1` — a segment's
  bounding box contains both endpoints.
- `bbox_of_seg_contains_between` — generalisation: the bbox contains
  every point on the segment.
- `bbox_disjoint_sym` — disjointness is symmetric.
- `shared_point_implies_not_disjoint` — if a point lies in both
  bounding boxes, they cannot be disjoint.
- **`disjoint_bboxes_imply_no_shared_point`** — the headline theorem.
  If two segments have disjoint bounding boxes, they share no point.
  The formal justification for envelope-based rejection in
  `LineIntersector` and friends.
- `bbox_of_seg_xlo_le_xhi`, `bbox_of_seg_ylo_le_yhi` — well-formedness
  of segment-derived bounding boxes.
- `bbox_contains_lo_corner` — every well-formed bbox contains its
  bottom-left corner.
- `bbox_of_seg_symmetric` — segment-bbox doesn't depend on endpoint order.

### `theories/Triangle.v` — triangles

Triangles in the plane: signed-area function via the cross product,
degeneracy, the permutation action on vertices, translation and
scaling invariance.

- `Triangle` record + `area2` (signed twice-area) + `is_degenerate`.
- `area2_zero_iff_collinear` — the degenerate triangle is the
  collinear-vertices one.
- `area2_swap_AB`, `area2_swap_BC` — vertex swap flips signed area.
- `area2_cyclic_ABC_BCA`, `area2_cyclic_ABC_CAB` — cyclic permutations
  preserve signed area.
- `area2_AA_degenerate`, `area2_AB_at_A_degenerate`,
  `area2_AB_at_B_degenerate` — coincident-vertex cases all degenerate.
- `area2_translation_invariant` — translation preserves area.
- `area2_scale` — scaling vertices by *c* scales signed area by *c²*.

### `theories/Convex.v` — convex combinations and convex sets

The foundational closure properties of convex sets, with worked
examples (half-planes, the whole plane, intersections of convex sets).
Underpins later results about convex hulls and polygon containment.

- `convex_combination` — two-point convex combination with parameter t.
- `convex_combination_at_0`, `convex_combination_at_1`,
  `convex_combination_self`, `convex_combination_symmetric` —
  basic identities.
- `between_iff_convex_combo` — bridges `Segment.v`'s `between` with
  the convex-combination formulation.
- `is_convex` — predicate: set closed under convex combinations.
- `whole_plane_is_convex` — the trivial case.
- **`intersection_is_convex`** — convexity is preserved under
  intersection. (The seed for "intersection of *n* half-planes is
  convex", and hence for convex-polygon membership.)
- `half_plane_is_convex`, `half_plane_ge_is_convex` — both signs of
  the closed half-plane defined by a linear inequality are convex.

### `theories/LexOrder.v` — lexicographic order on points

The standard lex order used by NTS's `Coordinate.CompareTo`: smaller x
wins, ties broken by smaller y. Standard order-theoretic properties.

- `lt_lex`, `le_lex` — strict and non-strict variants.
- `lt_lex_irrefl`, `lt_lex_asym`, `lt_lex_trans` — strict-order laws.
- `le_lex_refl`, `le_lex_antisym`, `le_lex_trans` — partial-order laws
  (antisymmetry up to coordinate equality).
- **`le_lex_total`** — totality: for any two points, one is ≤ the
  other. (Uses classical decidability on the reals.)

## Roadmap

Realistic next targets, ordered by ratio of "stripe of NTS this verifies" to
"effort":

1. **Segment intersection — completeness direction** — the converse of
   `segments_share_point_implies_opposite_sides`. Given strict opposite-side
   conditions on both cross products, construct the intersection point
   (Cramer's rule yields *t* = cross(C,D,A) / [cross(C,D,A) − cross(C,D,B)],
   similar for *s*) and prove both parameters lie in (0, 1) and that the
   resulting points coincide. This closes out the full bidirectional
   robustness story for `RobustLineIntersector.computeIntersect`.
2. **Robust orientation predicate** — Shewchuk-style filter conditions.
   Prove the unfiltered cross product agrees with the DD-arithmetic
   refinement when the filter is satisfied. The keystone for the
   library's robustness story.
3. **Convex hull invariants** — for a finite point set *S*, every point
   in *S* lies in the closed convex hull of *S*; the convex hull is
   itself convex; the hull's vertices are a subset of *S*.
4. **DD arithmetic** — addition is associative, multiplication
   distributes over addition under explicit bounds. Connects to
   [Flocq](https://flocq.gitlabpages.inria.fr/) for the floating-point
   model. This is where the "robust geometric predicates" claim becomes
   formally cashed-out.
5. **MIC center-is-interior** — the centre of the maximum inscribed
   circle of a non-degenerate polygon lies strictly in the polygon's
   interior.
6. **Buffer corner relations** — for a positive buffer distance, the
   buffer of a convex corner consists of an arc whose central angle
   equals the exterior angle.

### Progress log

- **2026-05-13**: seed commit with `Distance.v` and `Orientation.v`. CI green.
- **2026-05-14**: added `Segment.v` and the `between_implies_on_line`
  bridge.
- **2026-05-14**: added `Intersect.v`, proving the forward (soundness)
  direction of the cross-product segment intersection test — every
  rejection by the sign-product check is justified.
- **2026-05-14**: doubled the catalogue: extended `Distance.v` /
  `Orientation.v` / `Segment.v`, added `Vec.v` (2D vector algebra) and
  `Bbox.v` (axis-aligned bounding boxes + envelope-rejection
  soundness). Total: **45 kernel-checked theorems** across 6 modules.
- **2026-05-14**: crossed the first order of magnitude. Extended all
  six existing modules with another 26 results — including Lagrange's
  identity and the squared Cauchy-Schwarz inequality in `Vec.v` — and
  added three new modules: `Triangle.v` (signed-area arithmetic and
  vertex-permutation laws), `Convex.v` (convex sets, half-planes,
  intersection preservation), `LexOrder.v` (lex order on points with
  the full partial-order + totality story). Total: **102 kernel-
  checked theorems** across 9 modules.
- **2026-05-14**: reached Euclid's number. Added nine more modules —
  `Real.v` (44 basic real-number identities), `Lattice.v` (19 `Rmin`/`Rmax`
  laws), `LineEq.v` (20 line-equation identities), `Direction.v`
  (32 parallel/perpendicular vector laws), `Reflection.v` (34
  reflection-across-axes identities), `Disk.v` (14 closed-disk
  containment laws), `Parallel.v` (18 segment-direction laws),
  `Centroid.v` (24 centroid identities), `Polynomial.v` (22
  linear/quadratic identities) — and roughly doubled each of the
  existing nine. Total: **465 kernel-checked theorems** across 18
  modules. (Euclid's *Elements* contains 465 propositions; we now
  match the count, though the content is orthogonal: Euclid's are
  geometric constructions; ours are algebraic and order-theoretic
  invariants of the same plane.)

## What this is NOT

- This is **not** a verified implementation of NTS. The C# code is not
  extracted from Rocq. The proofs are over an abstract model of points
  (pairs of reals) and the operations on them. If the C# implementation
  encodes the same mathematical operations, the proofs apply. If it does
  something subtly different (typical example: a fast-path that's not
  exactly equivalent on edge cases), the proofs don't catch it.
- This is **not** a substitute for unit tests. Tests cover behaviour the
  proofs don't reach: floating-point rounding, exceptions, performance,
  cross-platform consistency, interaction with the rest of the runtime.
- This is **not** complete. As of the initial seed it covers two algorithms.
  Growing this catalogue is the work.

## Build

Local (macOS via Homebrew):

```sh
brew install rocq
coq_makefile -f _CoqProject -o Makefile
make
```

CI runs the same sequence on `macos-latest` (see
[`.github/workflows/ci.yml`](.github/workflows/ci.yml)) plus a sanity grep
that fails if any unsoundness marker (`Admitted`, `Axiom`, `Parameter`,
`admit.`) appears in `theories/`.

A successful `make` ends with `theories/*.vo` files and no errors. Each
`.vo` file is a kernel-checked term whose type is the corresponding theorem
statement. Build output also includes the `Print Assumptions` reports
(see top of this README).

## Licence

BSD-3-Clause, matching NetTopologySuite's licence. See [LICENSE](LICENSE).

NetTopologySuite is itself a derivative work of JTS Topology Suite, which
is dual-licensed under EPL 2.0 / EDL 1.0. The formal specifications in
this repository are derived from NTS source code; where that is the case,
the BSD-3-Clause grant respects NTS's attribution requirements.

## Contributing

Pull requests welcome. New theorems must:

- compile under stock Rocq 9.x with no external dependencies beyond
  the standard library (Flocq is acceptable when DD arithmetic lands);
- terminate with `Qed.` — no `Admitted`, no `Parameter` standing in for
  a missing proof;
- include a header comment naming the NTS module the theorem corresponds
  to, so reviewers can cross-reference.
