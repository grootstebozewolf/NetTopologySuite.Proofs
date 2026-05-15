# NetTopologySuite.Proofs

[![build proofs](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/actions/workflows/ci.yml/badge.svg)](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/actions/workflows/ci.yml)

Mechanically-verified formal proofs of foundational properties of the
algorithms in [NetTopologySuite](https://github.com/NetTopologySuite/NetTopologySuite).

Proofs are written in [Rocq Prover](https://rocq-prover.org/) (formerly Coq).

**The invariant**: every `.v` file in `theories/` and `theories-flocq/`
ends each proof with `Qed.` (or `Defined.` for computable terms). No
`Admitted`. Structural sanity lemmas are closed. Semantic soundness
bridges that are not yet proven are explicitly marked as future work in
the file header *and have no `Admitted` theorem standing in for them* —
they are absent rather than stubbed.

CI fails if any `Admitted`, `Axiom`, `Parameter`, or `admit.` appears in
any `.v` file. The only axioms used are the three standard ones bundled
with Rocq's classical real arithmetic library (printed at the end of
each `.v` file under `Print Assumptions` for transparency):

```
ClassicalDedekindReals.sig_not_dec
ClassicalDedekindReals.sig_forall_dec
FunctionalExtensionality.functional_extensionality_dep
```

These are the standard classical real-number axioms; no library-specific
or load-bearing axiom is introduced anywhere.

The repository has two source directories:

- **`theories/`** — Stdlib-only modules. Builds on the host runner
  (macOS-latest with Homebrew Rocq); this is the CI canonical target.
- **`theories-flocq/`** — modules that additionally depend on Flocq.
  Builds inside the container only (host CI runner has no Flocq). The
  no-`Admitted` invariant above applies HERE TOO — the directory split
  is purely about which CI runner builds the file, not about which
  proof standard it meets.

**Status.** The foundational layer (real-number, vector, distance,
orientation, segment, bbox, triangle, convex, lex-order, plus their
companions) is Qed-closed.  The curve-linearisation stack
(`Linearise` → `Simplify` → `Tin` → `Validate` → `Validate_decidable`)
is Qed-closed in the abstract.  The binary64 instance
(`Validate_binary64.v` + RocqRefRunner) is shipping to
[NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve);
its R-bridge soundness theorem is the next open item.  The Phase 0–7
chokepoint sequence (robust orientation, line intersection, snap
rounding, planar overlay) is the next major direction and is currently
at 0% on the C# side.

## Why this exists

Computational-geometry algorithms have subtle robustness properties — the
kind of bug you find three years later when an unusual coordinate
configuration trips a sign flip.  Unit tests sample behaviour at finitely
many points; formal proofs cover all of ℝ² simultaneously.

The intent is not to verify every line of NetTopologySuite — that's
infeasible.  Most of the C# code is plumbing.  The intent is to verify
the load-bearing primitives: the handful of small algorithms that, if
wrong, make everything above them suspect.  Orientation, distance, the
convex-hull invariants, the buffer-curve angle relations.

## Core primitives

Foundational geometry modules.  These are the algebraic and structural
facts that downstream work cites; they sit on top of Stdlib only and
build on the host CI runner without Flocq.

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
  third argument; used throughout the rest of the file.
- **`segments_share_point_implies_opposite_sides`** — if `between A B X`
  and `between C D X`, then `cross(A,B,C) · cross(A,B,D) ≤ 0` **and**
  `cross(C,D,A) · cross(C,D,B) ≤ 0`.
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
- **`disjoint_bboxes_imply_no_shared_point`** — if two segments have
  disjoint bounding boxes, they share no point.  The formal
  justification for envelope-based rejection in `LineIntersector` and
  friends.
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

## In-flight work

Modules atop the core primitives in active development.  Two threads
currently live here:

- The **curve-linearisation stack** (`Linearise` → `Simplify` → `Tin` →
  `Validate` → `Validate_decidable` → `Validate_binary64`), tracking the
  SFA-CA curves prototype on the upstream
  [`enhancement/curved-circularstring-tin`](https://github.com/NetTopologySuite/NetTopologySuite)
  branch.
- The **Phase 0 chokepoint** (`Orientation_b64`), the first slice of
  the multi-year roadmap toward `RobustLineIntersector` / overlay-
  topology verification.

Both feed binary64 implementations consumed by
[NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve).

### `theories/Linearise.v` — tolerance contract for curve linearisation

The mathematical companion of the SFA-CA `ILinearizable` interface
prototyped on the NTS `enhancement/curved-circularstring-tin` branch.
Three regimes — convergent scalar quantities, convergent topological
predicates, and tolerance-sensitive predicates — captured as formal
theorems. The framework justifies the staged plan in JTS discussion
[#1193](https://github.com/locationtech/jts/discussions/1193) (ship
linearisation now, native curve algorithms later).

- `Shape`, `within_eps`, `hausdorff_le`, `gap_ge` — the tolerance
  contract: shapes as point predicates with Hausdorff-bounded
  approximation and gap-based separation.
- `dist_triangle` — Euclidean triangle inequality on ℝ², proved from
  `Vec.cauchy_schwarz_sq` + `sq_monotone_nonneg`.
- **`chord_le_detour`** + **`polyline_chord_lower_bound`** — regime 1:
  for any list of intermediate points, the chord is a lower bound on
  any polyline visiting them in order. Refining a polyline never
  decreases its length.
- **`disjoint_under_linearise`** (+ strict variant) — regime 2: if two
  shapes have gap ≥ δ and each is within ε of an approximation, the
  approximations are gap ≥ δ−2ε apart. Disjointness predicates are
  ε-stable.
- **`regime3_counterexample`** + **`EqualsExact_not_stable`** —
  regime 3: distinct shapes can share a common ε-approximation; exact
  equality is *not* preserved by ε-approximation.  The limit of what
  Phase-3 linearisation can preserve.

### `theories/Simplify.v` — greedy polyline simplification

Inductive specification of Douglas-Peucker-style simplification, in two
flavours (chord-deficit and perpendicular-distance). Both are sound
under the tolerance contract from `Linearise.v`.

- `simp_step` / `simp_star` — inductive specs of a single greedy drop
  and its reflexive-transitive closure (chord-deficit form).
- `simp_step_perp` / `simp_star_perp` — the same for the squared-
  cross-product perpendicular-distance test, matching what
  Zygmunt-Róg (Measurement 260, 2026) use in production DEM
  generalisation.
- **`simp_step_length_monotone`** + **`simp_star_length_monotone`** —
  simplification never increases polyline length. Proof uses
  `chord_le_detour`; the tolerance hypothesis is *not* consumed —
  length-monotonicity holds for any drop.
- `simp_step_preserves_head` / `simp_step_preserves_last` (and star
  variants) — endpoints are pinned across both single-step and
  iterated simplification.
- `simp_drop_here_length_deficit` — exact identity: the length
  reduction equals the chord-deficit at the dropped point.

### `theories/Tin.v` — TIN boundary adjacency

Formalises the merging condition in Zygmunt-Róg (Measurement 260,
2026): adjacent TINs built from a shared boundary polyline must agree
on boundary vertices for seamless merging.  Proved via `Linearise.v`
and `Simplify.v` endpoint-preservation theorems.

- `TaggedTin` record + `same_source_boundary` predicate.
- **`same_source_share_endpoints`** (chord, perp, and mixed-mode
  variants) — two TINs simplified from the same source boundary
  always agree on head and last vertex, regardless of which
  derivation each side chose. Sufficient for adjacency-merging
  algorithms to detect shared boundary edges.
- `same_source_boundary_length_bounded` — neither simplification
  inflates the source boundary length.

### `theories/Validate.v` — constructive simplifier + soundness

The executable counterpart of `Simplify.v`'s inductive specifications.
Left-to-right greedy realisations of both flavours, with soundness
theorems proving each output is in the corresponding `simp_star`
relation. Ready for OCaml extraction.

- `greedy_simplify` / `greedy_simplify_perp` — `Fixpoint`s using
  Stdlib's `Rle_dec` for the tolerance comparison.
- **`greedy_simplify_correct`** / **`greedy_simplify_perp_correct`** —
  soundness: the output is `simp_star`-related to the input.
- Six inheritance corollaries (length monotone, head/last preserved,
  perp variants) — one-line proofs that compose the soundness theorem
  with the spec-level lemmas from `Simplify.v`.

### `theories/Validate_decidable.v` — carrier-generic simplifier

The perpendicular form lifted into a typeclass `OrderedReal` of
"ordered ring coercible to ℝ with decidable ≤". Same soundness
theorem, proved once for the abstract carrier and inheriting to every
instance. An R instance ships with the file; the Flocq binary64
instance is the in-flight slice in `theories-flocq/`.

- `Class OrderedReal` — 8 fields (`t0`, `t2`, `tplus`, `tsub`,
  `tmult`, `to_real`, `tle_dec`) + 5 homomorphism laws.
- `Instance OrderedReal_R` — the R instance.
- `greedy_simplify_perp_T` (`Fixpoint`, parameterised over T) +
  **`greedy_simplify_perp_T_correct`** — abstract soundness
  theorem; depends on only one classical-reals axiom
  (`sig_forall_dec`), strictly fewer than the corollaries that
  compose with `dist_triangle`.

### `theories-flocq/Validate_binary64.v` — Flocq instance + RocqRefRunner

A Flocq-based `binary64` instance of the perpendicular-distance
simplifier, paired with a native-float OCaml extraction (`oracle/`)
that compiles to the **RocqRefRunner** binary used as a differential
testing reference by the C# implementation in
[NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve).
Lives in a separate directory only because the host CI doesn't have
Flocq; the corpus-wide no-`Admitted` invariant applies here too.

- `BPoint` record + `binary64` arithmetic helpers (`b64_plus`,
  `b64_minus`, `b64_mult`, `b64_le` — NaN-safe via `Bcompare`) and
  geometric helpers (`b64_cross`, `b64_dist_sq`).
- `greedy_simplify_perp_b64_aux` / `greedy_simplify_perp_b64` — the
  greedy perpendicular-distance simplifier as a Coq `Fixpoint`.
- 14 Qed-closed structural lemmas: `_nil`, `_singleton`,
  `_two_points`, `_never_none`, `_some_eq`, `_aux_head`,
  `_preserves_head`, `_aux_nonempty`, `_nonempty`, `_aux_length_le`,
  `_length_le`, `_aux_in_kept`, `_in_head`.
- Companion file `Validate_binary64_extract.v` adds the native-float
  extraction directives (binding `Binary.binary_float` to OCaml `float`
  and overriding `Bplus`/`Bminus`/`Bmult`/`Bcompare` with the native
  operators). Produces `oracle/extracted.ml`, which links with
  `oracle/driver.ml` to build the RocqRefRunner standalone binary.

The R-bridge soundness theorem (`greedy_simplify_binary64_sound` —
threading the no-overflow preconditions through the `Fixpoint`) is
not yet proven and is not stubbed with `Admitted`; the `PROOF STATUS`
block at the top of the file says so explicitly.  The per-op lifts
that this theorem composes are now available in
[`B64_bridge.v`](theories-flocq/B64_bridge.v) (`b64_plus_correct`,
`b64_minus_correct`, `b64_mult_correct`).

### `theories-flocq/B64_bridge.v` — binary64 ↔ ℝ correctness lifts

Thin wrappers around Flocq's `Bplus_correct` / `Bminus_correct` /
`Bmult_correct` for the `b64_plus` / `b64_minus` / `b64_mult` helpers
from `Validate_binary64.v`.  Each theorem takes a bundled
`b64_safe op x y` precondition (operand finiteness + no-overflow on
the rounded result, parameterised by the R-side op) and concludes
that the binary64 operation's `B2R` is exactly the rounded
`B2R x ⊕ B2R y` and the result is finite.  Same 4-axiom set as the
rest of the corpus.

The lifts are deliberately small.  The interesting work moves to the
caller:

- For the simplifier R-bridge, threading the precondition through
  the recursive structure of `greedy_simplify_perp_b64`.
- For Stage A's arithmetic identities (antisymmetry, cyclic
  permutation, translation invariance), composing two or three lifts
  per identity under a shared precondition.
- For Stages B / C of orient2d, threading the precondition through
  the expansion-arithmetic primitives (`grow-expansion`,
  `fast-expansion-sum`, `expansion-product`) — see
  [`docs/audit-shewchuk-stages.md`](docs/audit-shewchuk-stages.md).

### `theories-flocq/Orient_b64_sound.v` — soundness bridge for the Stage A filter

First soundness statement for `b64_orient_sign_filtered`.  Currently
proves *decoder consistency*: the five-valued sign returned by the
filter agrees with the sign of the rounded binary64 `b64_orient2d`
value (under `b64_orient2d_safe`).  Defines `cross_R_BP` (the exact
R-valued cross product on `BPoint` inputs) as the target of the
future cross_R-soundness theorem.  See the file's PROOF STATUS block
for the precise statement of that theorem, and
[`docs/soundness-strategy.md`](docs/soundness-strategy.md) for the
two open paths to it (a Shewchuk-style forward-error analysis that
was attempted and demoted, and an integer-coordinate exact regime
currently in progress).

### `theories-flocq/Orient_b64_R.v` — R-side identities for `b64_orient2d`

First downstream consumer of `B64_bridge`.  Bundles the seven
no-overflow obligations of one `b64_orient2d` call into a single
predicate `b64_orient2d_safe P0 P1 Q : Prop` (four `b64_safe Rminus`
on the coordinate differences, two `b64_safe Rmult` on the product
terms, one `b64_safe Rminus` on the outer subtraction).

The headline theorem proved Qed-closed today:

```coq
Theorem b64_orient2d_antisymmetric_R :
  forall P0 P1 Q,
    b64_orient2d_safe P0 P1 Q ->
    b64_orient2d_safe P0 Q  P1 ->
    B2R (b64_orient2d P0 P1 Q) = - B2R (b64_orient2d P0 Q P1).
```

Cyclic permutation and translation invariance follow the same pattern
and are the immediate follow-ups.  A magnitude-bounded variant of the
precondition (one `|coord| < 2^N` per input + a helper lemma that
derives the seven `b64_safe` obligations from it) is the slice after,
producing a more ergonomic interface for downstream callers.

### `theories-flocq/Orientation_b64.v` — Phase 0 chokepoint

The first chokepoint module.  Ships the binary64 orientation
predicate end-to-end through extraction and into the
[NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve)
`Robust.Orientation` namespace, in two layers.

**Naive layer** (the cross-product evaluated directly in binary64):

- `b64_orient2d P0 P1 Q` — signed twice-area of the triangle
  `(P0, P1, Q)`, reusing the `b64_minus` / `b64_mult` / `bx` / `by_`
  helpers from `Validate_binary64.v`.
- `Inductive orient_sign := OrientPos | OrientNeg | OrientZero | OrientNan` —
  four-valued result that admits NaN explicitly rather than
  collapsing it.  Downstream callers MUST handle `OrientNan`.
- `b64_orient_sign` — routes through `b64_compare` against `+0`.

**Shewchuk Stage A filter** (forward-error filter on top of the naive
layer):

- `b64_three`, `b64_sixteen`, `b64_eps` — Flocq-constructed binary64
  constants via `binary_normalize`; `b64_eps = 2^-52` is the spacing
  at 1.0 in IEEE 754 binary64.
- `b64_errbound_A_coeff = (3 + 16·eps) * eps` — Shewchuk's Stage A
  forward-error coefficient, computed in binary64 via the same
  `Bplus` / `Bmult` primitives.  Approximately 6.66·10⁻¹⁶.
- `b64_abs` — absolute value with a concrete NaN handler.
- `b64_orient2d_detsum P0 P1 Q` — `|t1| + |t2|`, the operand-magnitude
  budget for the filter bound.
- `b64_orient2d_errbound P0 P1 Q = errbound_A_coeff * detsum` — the
  per-triangle threshold.
- `Inductive orient_sign_robust := OrientRPos | OrientRNeg | OrientRZero | OrientRNan | OrientRUncertain` —
  five-valued result, extending `orient_sign` with the Uncertain case
  the filter returns when `|det|` is within the error bound of zero.
- `b64_orient_sign_filtered` — the Stage A decoder.  If
  `|det| > errbound`, the naive sign is reliable; otherwise the
  filter returns `OrientRUncertain` rather than risk a sign flip.

Qed-closed structural lemmas across both layers: `orient_sign_eq_dec`,
`b64_orient_sign_total`, `orient_sign_distinct`,
`b64_orient_sign_non_nan_iff_compare_some`,
`orient_sign_robust_eq_dec`, `b64_orient_sign_filtered_total`,
`orient_sign_robust_distinct`.  Same 4-axiom set as
`Validate_binary64.v`.

What is NOT YET claimed here:

- The arithmetic identities that hold over ℝ (antisymmetry, cyclic
  permutation, translation invariance) need Flocq's `Bminus_correct`
  / `Bmult_correct` no-overflow preconditions — same proof slice
  deferred for the simplifier R-bridge.
- Shewchuk's **Stages B / C / D** — the expansion-arithmetic
  refinement that resolves `OrientRUncertain` into a definite
  Pos/Neg/Zero — are deferred to a later slice.  Callers facing
  `OrientRUncertain` today fall back to a higher-precision predicate
  or treat the triangle as collinear with a documented caveat.

`Orientation_b64.v` is plumbed into `Validate_binary64_extract.v`, so
the RocqRefRunner dispatches on a stdin mode line (`SIMPLIFY` /
`ORIENT` / `ORIENT_FILTERED`) into the appropriate extracted function.

## Roadmap

### Phase 0–7: the NTS topological chokepoint

A multi-year plan to formally verify the load-bearing algorithms in
NTS — `RobustLineIntersector`, the noding pipeline
(`SnapRoundingNoder` + `MCIndexNoder`), and `OverlayNG` topology
construction — down to executable, provably-robust Coq-extracted code.
3–5 person-years of focused work; each phase is independently
publishable.

| Phase | Deliverable | Status | `NetTopologySuite.Curve` consumer |
|---|---|---|---|
| Simplifier *(warm-up, not in the chokepoint sequence)* | `Validate_binary64.v` — greedy perpendicular-distance simplifier on binary64 + RocqRefRunner | Qed-closed structural (14 lemmas); soundness bridge deferred | **100%** — `Robust.Simplify.GreedyPerpSimplifier`, 262 / 262 tests bit-exact against RocqRefRunner |
| 0 | `Orientation_b64.v` — Shewchuk-adaptive orientation under Flocq binary64 | Stage A filter Qed-closed (`b64_orient_sign_filtered`, decidability, totality, 5-constructor distinctness, NaN-safety); Stages B/C/D expansion refinement + soundness bridge deferred | **filter-complete** — `Robust.Orientation.RobustOrientation` (`Orient2d` / `Sign` / `SignFiltered` with 5-valued `OrientSignRobust`) bit-exact against RocqRefRunner `ORIENT` + `ORIENT_FILTERED` modes |
| 1 | `RobustLineIntersector_b64.v` — including all degeneracies | reading-unblocked | 0% |
| 2 | `SnapRoundingNoder_b64.v` — formal model of Hobby 1999 + Halperin-Packer 2002 (ISR) | reading-unblocked | 0% |
| 3 | `OverlayNG_b64.v` — DCEL / hypermap subdivision with face labelling | reading-unblocked (Dufourd 2008 ×2 + Brun-Dufourd-Magaud 2012 in hand) | 0% |
| 4 | Native circular-arc primitives (`Linearise.v` regime 3 closure) | research, far future | 0% |
| 5 | Extraction toolchain + C# FFI to production NTS | pending Phase 1+ | 0% |
| 6 | Continuous integration of corpus against NTS test suite | pending Phase 5 | 0% |
| 7 | Soundness audit of curve-aware overlay operations | pending Phase 4 | 0% |

The "consumer" column tracks delivery on the C# side in
[NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve)
under `NetTopologySuite.Robust.*`.  100% means the algorithm is implemented,
its structural facts are mirrored as unit tests, and the implementation is
bit-exact with the Coq-extracted reference (RocqRefRunner) on every shipped
test case.  Full semantic soundness against the real-number model is a
separate axis — currently not claimed end-to-end on any phase.

The library audit for closing Phase 0 Stages B / C / D
(expansion-arithmetic refinement that resolves `OrientRUncertain`
into a definite sign) lives in
[`docs/audit-shewchuk-stages.md`](docs/audit-shewchuk-stages.md).
Bottom line: Flocq 4.2.2 ships TwoSum, Dekker's TwoProduct, and
Veltkamp splitting; the missing piece is Shewchuk's expansion
arithmetic on top of those.

The critical-path piece identified in the audit — a binary64↔ℝ
bridge for the `b64_plus` / `b64_minus` / `b64_mult` helpers — is
now Qed-closed in
[`theories-flocq/B64_bridge.v`](theories-flocq/B64_bridge.v).
Three theorems (`b64_plus_correct`, `b64_minus_correct`,
`b64_mult_correct`) each state that, under finiteness of operands
plus a no-overflow precondition, the operation's `B2R` equals the
exact rounded `B2R x ⊕ B2R y` and the result is finite.  Same
4-axiom set as the rest of the corpus.  This unblocks three
downstream targets that were each waiting on the same machinery:
the simplifier R-bridge, Stage A's arithmetic identities for
`b64_orient2d`, and Shewchuk Stages B / C of orient2d.

### Original targets (still relevant, partially complete)

1. **Segment intersection — completeness direction** — converse of
   `segments_share_point_implies_opposite_sides`. Given strict opposite-side
   conditions on both cross products, construct the intersection point
   via Cramer's rule and prove both parameters lie in (0, 1). Closes the
   full bidirectional robustness story for
   `RobustLineIntersector.computeIntersect`. Subsumed by Phase 1.
2. **Robust orientation predicate** — Shewchuk-style filter conditions.
   The keystone of the robustness story. Becomes Phase 0.
3. **Convex hull invariants** — `Convex.intersection_is_convex` covers
   the closure half; the constructive direction (vertices, lower
   hull, upper hull) is still open. The Brun-Dufourd-Magaud 2012 Coq
   formalisation is the proof-engineering template.
4. **DD arithmetic** — superseded by the Flocq-based path through
   `theories-flocq/Validate_binary64.v` and Phase 0.
5. **MIC center-is-interior** — for a non-degenerate polygon, the
   centre of the maximum inscribed circle lies strictly in the
   polygon's interior. Independent of the chokepoint work.
6. **Buffer corner relations** — for a positive buffer distance, the
   buffer of a convex corner consists of an arc whose central angle
   equals the exterior angle. Adjacent to Phase 4 (native curves).

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
  soundness). Total: **45 Qed-closed theorems** across 6 modules.
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
  existing nine. Total: **465 Qed-closed theorems** across 18
  modules. (Euclid's *Elements* contains 465 propositions; the count
  now matches.  The content is orthogonal — Euclid's propositions are
  geometric constructions; these are algebraic and order-theoretic
  invariants of the same plane.)
- **2026-05-14**: pivoted to the NTS curves prototype. Added `Linearise.v`
  (14 theorems): the tolerance contract — `within_eps`, `hausdorff_le`,
  `gap_ge` — plus the regime-1/2/3 stratification. Headline results:
  `chord_le_detour`, `polyline_chord_lower_bound`,
  `disjoint_under_linearise`, `regime3_counterexample`. The
  triangle-inequality proof `dist_triangle` follows from
  `Vec.cauchy_schwarz_sq`.
- **2026-05-14**: added `Simplify.v` (18 theorems): the inductive specs
  `simp_step` (chord-deficit form) and `simp_step_perp` (squared-cross-
  product perpendicular form, matching Zygmunt-Róg Measurement 260,
  2026), with their reflexive-transitive closures. Length monotonicity
  proved unconditionally; endpoint preservation across both single-step
  and iterated simplification.
- **2026-05-14**: added `Tin.v` (4 theorems): the TIN boundary-endpoint
  sharing theorem `same_source_share_endpoints`. Adjacent TINs
  simplified from the same source boundary always agree on head and
  last vertex regardless of which derivation each side chose. The
  formal companion of Zygmunt-Róg's adjacent-TIN merging result.
- **2026-05-14**: added `Validate.v` (12 theorems): the constructive
  `Fixpoint` realisations `greedy_simplify` and `greedy_simplify_perp`
  with their soundness theorems (output is in the corresponding
  `simp_star` relation), plus six inheritance corollaries.
- **2026-05-14**: added `Validate_decidable.v` (7 theorems): the
  perpendicular form parameterised over a typeclass `OrderedReal`.
  Soundness proved once for the abstract carrier; an R instance
  ships immediately, a Flocq binary64 instance is the next slice.
  Total: **520 Qed-closed theorems** across 23 modules in
  `theories/`.
- **2026-05-15**: container infrastructure (`Dockerfile`,
  `.dockerignore`, `_CoqProject.full`) wired up for Rocq 9.1.1 +
  `coq-flocq.4.2.2`. A `theories-flocq/` directory now hosts the
  Flocq-bearing work and is excluded from the host CI's no-`Admitted`
  grep so the main corpus invariant stays clean while the soundness
  bridges are filled in. Companion mathematical paper
  [`docs/mathematics/curves.tex`](docs/mathematics/curves.tex) in the
  upstream
  [`NetTopologySuite`](https://github.com/NetTopologySuite/NetTopologySuite)
  branch `enhancement/curved-circularstring-tin` collects the formal
  identities the proofs rest on.
- **2026-05-15**: closed the `Validate_binary64.v` simplifier slice end-
  to-end. The two original soundness `Admitted` theorems are replaced
  by 14 Qed-closed structural lemmas (head preservation, length
  monotonicity, NaN safety, etc.) — the corpus-wide no-`Admitted`
  invariant now applies uniformly across `theories/` and
  `theories-flocq/`, and the CI grep is anchored so prose mentions
  in module headers no longer false-trip. A companion file
  `Validate_binary64_extract.v` adds native-float OCaml extraction
  directives; `oracle/driver.ml` + `oracle/Makefile` build the
  RocqRefRunner standalone binary. The C# consumer
  `Robust.Simplify.GreedyPerpSimplifier` in
  [NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve)
  is bit-exact against RocqRefRunner on 262 / 262 tests (14 unit
  mirroring the Coq lemmas + 248 differential cases across random
  and adversarial families). The R-bridge soundness theorem stays
  deferred (not stubbed with `Admitted`).
- **2026-05-15**: Phase 0 chokepoint first slice.  Added
  `theories-flocq/Orientation_b64.v` (naive binary64 orientation
  predicate + four-valued sign decoder with NaN explicitly admitted)
  with Qed-closed decidability / totality / distinctness / non-NaN-
  iff-compare-Some lemmas.  `Validate_binary64_extract.v` now extracts
  both the simplifier and the orientation functions into a single
  `oracle/extracted.ml`, and `oracle/driver.ml` dispatches on a stdin
  mode line (`SIMPLIFY` / `ORIENT`).  C# consumer
  `Robust.Orientation.RobustOrientation` (with `OrientSign` enum)
  is bit-exact against RocqRefRunner on the full test suite — 385 /
  385 GreedyPerp + RobustOrientation tests pass on Apple Silicon.
  The arithmetic identities and the Shewchuk-adaptive filter are
  explicitly the next slice, not stubbed.
- **2026-05-15**: Phase 0 chokepoint — Stage A filter complete.
  Added `b64_three` / `b64_sixteen` / `b64_eps` (Flocq-constructed via
  `binary_normalize`), `b64_errbound_A_coeff = (3 + 16·eps)·eps`,
  `b64_abs`, `b64_orient2d_detsum`, `b64_orient2d_errbound`, the
  five-valued `Inductive orient_sign_robust` (with `OrientRUncertain`),
  and `b64_orient_sign_filtered` — Shewchuk's Stage A filter that
  refuses to commit to a sign when `|det|` is within the forward-error
  bound of zero.  Qed-closed lemmas: `orient_sign_robust_eq_dec`,
  `b64_orient_sign_filtered_total`, `orient_sign_robust_distinct`.
  Stages B/C/D expansion-arithmetic refinement is the next slice.
  `oracle/driver.ml` gains an `ORIENT_FILTERED` mode; the C# port
  exposes `RobustOrientation.SignFiltered` with the 5-valued
  `OrientSignRobust` enum.  Result: 396 / 396 GreedyPerp +
  RobustOrientation tests bit-exact against the RocqRefRunner — naive
  + filtered modes both green.
- **2026-05-15**: critical-path module landed.
  Added `theories-flocq/B64_bridge.v` with `b64_plus_correct`,
  `b64_minus_correct`, `b64_mult_correct` — thin wrappers around
  Flocq's `Bplus_correct` / `Bminus_correct` / `Bmult_correct` lifted
  to the binary64 helpers `b64_plus` / `b64_minus` / `b64_mult` from
  `Validate_binary64.v`.  Premises bundled into one parameterised
  predicate `b64_safe (op : R -> R -> R) (x y : binary64) : Prop`.
  Same 4-axiom set as the rest of the corpus; no `Admitted`, no new
  dependencies beyond Flocq.  This unblocks the simplifier R-bridge,
  Stage A's arithmetic identities for `b64_orient2d`, and Shewchuk
  Stages B / C of orient2d — three downstream theorems waiting on the
  same lift mechanism, see `docs/audit-shewchuk-stages.md`.
- **2026-05-15**: first downstream consumer of `B64_bridge`.  Added
  `theories-flocq/Orient_b64_R.v` with `b64_orient2d_safe` (the
  seven-conjunct no-overflow precondition for one orient2d call) and
  `b64_orient2d_antisymmetric_R`: under the precondition,
  `B2R (b64_orient2d P0 P1 Q) = - B2R (b64_orient2d P0 Q P1)`.
  Proof is mechanical: lift the two outer `b64_minus` calls via
  `b64_minus_correct`, then `round_NE_opp` + `Ropp_minus_distr` close
  it.  Validates the composition pattern.  Same 4-axiom set, Qed-
  closed.
- **2026-05-15**: vertex coincidence on binary64.  Added zero-arithmetic
  helpers to `B64_bridge.v` (`b64_round_0`, `b64_minus_self_R`,
  `b64_mult_zero_{l,r}_R`, `b64_minus_zeros_R`, plus finiteness
  companions) and proved `b64_orient2d_at_P0_R` in `Orient_b64_R.v`:
  `B2R (b64_orient2d P0 P1 P0) = 0` under two `b64_safe Rminus`
  premises (one for each non-self subtraction; the self subtractions
  discharge trivially via `b64_round 0 = 0`).  Holds genuinely in
  binary64 -- not a rounded approximation -- because every degenerate
  case has an exact-zero factor.
  Cyclic permutation was analysed and deferred: lifting via
  `b64_*_correct` produces nested `b64_round` terms that aren't
  syntactically equal under cyclic permutation, and the accumulated
  rounding error doesn't structurally cancel between the two calls.
  The identity holds for the exact ℝ-valued `cross` predicate but
  not for its binary64 evaluation in general; provable only under
  much stronger preconditions (Sterbenz exactness throughout) or as
  an error-bounded version.
- **2026-05-15**: magnitude-bounded interface (Flavour B from the
  Phase 0 audit).  Added to `B64_bridge.v`: `bpow_succ_radix2`,
  `valid_exp_b64_fexp` (instance bridging `SpecFloat.fexp` to
  `FLT_exp_valid`), `b64_safe_coord_bound := bpow radix2 500`,
  `b64_coord_safe`, `generic_format_bpow_b64`,
  `b64_round_abs_le_bpow`, `b64_safe_minus_of_bounded`,
  `b64_minus_bounded_R`, `b64_mult_bounded_R`,
  `b64_safe_minus_of_products_bounded`.  Composed in
  `Orient_b64_R.v` as `b64_orient2d_inputs_safe P0 P1 Q :=
  /\ b64_coord_safe (bx P0) ... (by_ Q)` (six conjuncts) plus
  `Theorem b64_orient2d_inputs_safe_imp_safe` deriving the
  seven-conjunct `b64_orient2d_safe` from coord-magnitude bounds.
  This is the ergonomic interface the audit identified: callers
  state one `b64_coord_safe` per coordinate (a clean condition
  expressible in human terms as `|coord| <= 2^500`) instead of
  seven sub-op no-overflow bounds.  Same 4-axiom set, Qed-closed.
  Cost of getting there: several Coq typeclass-resolution snags
  documented in the commit message; the proof structure ended up
  needing explicit `apply round_le radix2 ...` calls and a hand-
  rolled `Valid_exp (SpecFloat.fexp prec emax)` instance because
  the standard FLT instance doesn't unify through definitional
  equality.
- **2026-05-15**: soundness bridge -- decoder consistency.
  Added `theories-flocq/Orient_b64_sound.v` with `cross_R_BP`
  (the exact R-valued cross product on `BPoint` via `B2R` on each
  coordinate -- the mathematical standard the binary64 evaluation
  is eventually compared against), `b64_orient2d_finite_of_safe`
  (chains finiteness through the orient2d composition under
  `b64_orient2d_safe`), and `b64_orient_sign_filtered_consistent_with_b64`:

      forall P0 P1 Q,
        b64_orient2d_safe P0 P1 Q ->
        match b64_orient_sign_filtered P0 P1 Q with
        | OrientRPos       => 0 < B2R (b64_orient2d P0 P1 Q)
        | OrientRNeg       => B2R (b64_orient2d P0 P1 Q) < 0
        | OrientRZero      => B2R (b64_orient2d P0 P1 Q) = 0
        | OrientRNan       => True
        | OrientRUncertain => True
        end.

  The "internal consistency" half of soundness: the five-valued
  sign decoder agrees with the sign of the rounded binary64 value.
  Same 4-axiom set, Qed-closed.

  The cross_R-valued soundness theorem -- relating the decoder's
  sign to the *exact* mathematical cross product -- is documented
  as a future target in the file's PROOF STATUS block.  It requires
  the Shewchuk Stage A forward-error theorem:

      Rabs (B2R (b64_orient2d P0 P1 Q) - cross_R_BP P0 P1 Q)
        <= b64_errbound_A_coeff_value * detsum

  which is the substantive proof slice (~1-3 days), needing per-op
  forward-error lemmas (`Plus_error.plus_error`, etc.) plus the
  accumulation analysis through the four `b64_minus` / two
  `b64_mult` / outer `b64_minus` chain.  Once that lemma lands,
  cross_R soundness follows mechanically by composition with the
  decoder-consistency theorem from this slice.
- **2026-05-15**: forward-error building blocks (slice 2a of the
  soundness bridge).  Added to `B64_bridge.v`: `b64_plus_abs_error`,
  `b64_minus_abs_error`, `b64_mult_abs_error`, each giving the
  per-operation absolute error bound

      Rabs (B2R (b64_op x y) - exact_op (B2R x) (B2R y))
        <= ulp radix2 (SpecFloat.fexp prec emax) (exact_op ...).

  Built on Flocq's `error_le_ulp` from `Core/Ulp.v`; unconditional
  (no normal-range precondition).  These are the per-step pieces
  the Shewchuk Stage A chain composition will eventually thread
  through the four `b64_minus` / two `b64_mult` / outer `b64_minus`
  structure of `b64_orient2d`.  Same 4-axiom set, Qed-closed.
  Two further sub-slices documented in `Orient_b64_sound.v`'s
  PROOF STATUS: (2b) tighter relative-error versions under normal-
  range precondition via `relative_error_N_FLT`; (2c) the chain
  composition itself.

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
- This is **not** complete. Current coverage is 520+ Qed-closed
  theorems across 23 modules: the algebraic foundations (real-number,
  vector, distance, orientation, line, disk, lattice, lex order),
  segment and bounding-box primitives, triangle / convex / centroid /
  reflection laws, and the curve-linearisation stack
  (`Linearise.v` → `Simplify.v` → `Tin.v` → `Validate.v` →
  `Validate_decidable.v`). The Phase 0–7 chokepoint roadmap above
  outlines what's missing: orientation under floating-point arithmetic,
  the full robust line-intersector, snap-rounding, planar overlay, and
  native curve primitives — multi-year work, but each phase ships
  independently.

## Build

### Local (macOS via Homebrew)

```sh
brew install rocq
rocq makefile -f _CoqProject -o Makefile.gen
make -f Makefile.gen
```

This builds every module in `_CoqProject` — i.e. the Stdlib-only corpus.
Modules with external dependencies (Flocq) live in `_CoqProject.full` and
are built inside the container only (see below).

CI runs the same sequence on `macos-latest` (see
[`.github/workflows/ci.yml`](.github/workflows/ci.yml)) plus a sanity grep
that fails if any unsoundness marker (`Admitted`, `Axiom`, `Parameter`,
`admit.`) appears in `theories/`.

### Containerised build (Rocq 9.1.1 + Flocq 4.2.2)

For modules that need [Flocq](https://flocq.gitlabpages.inria.fr/) (e.g. a
forthcoming `Validate_binary64.v` linking the validation layer to IEEE-754
binary64) the canonical environment is a podman container based on the
official `rocq/rocq-prover:9.1.1-ocaml-4.14.2-flambda` image with
`coq-flocq.4.2.2` pinned via opam. This matches the toolchain Boldo et al.
JAR 2015 §5 uses.

```sh
# One-time: build the image (~5 min, pulls + compiles Flocq under
# x86_64 emulation on Apple Silicon).
podman build -t nts-proofs .

# Build the corpus inside the image (uses the workspace COPY'd at
# image-build time, regenerates Makefile.gen from _CoqProject.full).
podman run --rm nts-proofs

# Iterate against the live workspace (volume-mount).  Note: clean
# host-generated build artefacts first via the .dockerignore-equivalent
# manual step, then regenerate.
podman run --rm -v "$(pwd):/workspace:z" -w /workspace nts-proofs bash -lc \
  'rm -f Makefile.gen* .Makefile.* theories/*.vo* theories/*.glob theories/.*.aux \
   && rocq makefile -f _CoqProject.full -o Makefile.gen \
   && make -f Makefile.gen -j2'

# Interactive shell for proof development with Flocq imports available.
podman run --rm -it -v "$(pwd):/workspace:z" -w /workspace nts-proofs bash
```

The host build is the canonical CI target (the macOS-arm64 runner has no
Flocq); the container is the augmented environment for modules whose
proofs need Flocq.

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

- compile under stock Rocq 9.x;
- terminate with `Qed.` — no `Admitted`, no `Axiom`, no `Parameter`
  standing in for a missing proof. The rule applies in `theories/`
  and in `theories-flocq/` alike;
- depend only on Rocq's standard library if placed under `theories/`,
  or on Flocq 4.2.x if placed under `theories-flocq/`;
- include a header comment naming the NTS module (or JTS algorithm)
  the theorem corresponds to, so reviewers can cross-reference;
- carry the SPDX licence header and AI-assistance disclosure where
  applicable (the existing files set the pattern).
