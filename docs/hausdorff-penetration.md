<!-- doc-kind: guide -->
# Directed Hausdorff lane: shape matching and penetration depth, mechanised

**Sources.**
1. D. P. Huttenlocher, G. A. Klanderman, W. J. Rucklidge, *"Comparing
   Images Using the Hausdorff Distance"*, IEEE Trans. PAMI 15(9):850–863,
   1993 — the canonical reference for the (directed) Hausdorff distance
   that JTS/NTS `DiscreteHausdorffDistance` implements. Mechanised in
   `theories/HausdorffMetricSym.v`.
2. Y. Wen, W. Zhang, *"A Minimax Model for Generalized Penetration
   Distance Between Convex Sets by Directed Hausdorff Distance"*, IEEE
   Robotics and Automation Letters 7(3):6123–6130, 2022
   (doi:10.1109/LRA.2022.3166111). Mechanised in
   `theories/PenetrationGauge.v` and `theories/PenetrationMinimax.v`.
3. N. Meinert, *"Walking Your Frog Fast in 4 LoC"*, arXiv:2404.05708,
   2024 (DLR) — the recursion-free, linear-memory reformulation of the
   Eiter–Mannila (1994) **discrete Fréchet distance**, the ordered
   counterpart of the discrete Hausdorff. Mechanised in
   `theories/FrechetMaxmin.v`.

All `Qed`, three-axiom footprint, rational witnesses throughout — no
`sqrt`, no limits, no `Admitted`.

## The real-world problems

**Shape matching (Huttenlocher).** Model-based vision ranks stored model
shapes against an image point set. The Hausdorff distance
`H(A,B) = max(h(A,B), h(B,A))` with the *directed*
`h(A,B) = max_{a∈A} min_{b∈B} ‖a−b‖` (eqs (1)–(2)) is used because it is
a **metric**: "two shapes that are highly dissimilar cannot both be
similar to some third shape". A ranked database is only trustworthy with
the triangle inequality; correlation-style scores don't have it. The
computation runs on **Voronoi surfaces** (distance transforms)
`d(x) = min_b ‖x−b‖` — egg-carton functions whose translation identity
gives `H(A, B⊕t)` for all translations at once. This is the same
max-min JTS's `DiscreteHausdorffDistance` computes for geometry
similarity testing.

**Penetration depth (Wen–Zhang).** When two bodies *overlap*, collision
response needs the smallest translation that separates them. Wen–Zhang
generalize this from the Euclidean ball to any **gauge set** F
(Manhattan/Chebyshev/hexagon "balls" — anisotropic clearance rules): the
generalized penetration depth is the largest dilation `λF` inscribed in
the Minkowski difference `C = A ⊖ B` (eq (9)), detected by the directed
Hausdorff distance (`λF ⊆ C ⟺ h(λF, C) = 0`, eq (10)), i.e. the
**largest zero of a nonnegative, nondecreasing, convex function**
`f(λ) = h(λF, C)` (eq (11), Theorem 1) found by a secant method that
never undershoots (Theorem 2). Undershooting is the failure mode that
matters: a solver that lands below λ* reports "separated" while the
bodies still overlap.

## Statement → lemma map

| Paper item | Lemma | What it guards |
|---|---|---|
| HKR eq (1) ⇒ metric | `HausdorffMetricSym.v : Hsym_symmetric`, `Hsym_zero_iff`, `Hsym_triangle` | The symmetrization `max(h(A,B), h(B,A))` is a metric for **any** directed dissimilarity with a zero-iff-subshape law and the directed triangle inequality — proved abstractly. Model-ranking transitivity lives here. |
| HKR eq (1)+(2), instantiated | `HausdorffMetricInstance.v : hausdorff_distance_triangle`, `hausdorff_distance_zero_iff`, `hausdorff_distance_symmetric` (+ `directed_hausdorff_zero_iff`, `directed_hausdorff_triangle`, generic `max_min_score` layer) | **The instantiation, closed** (423-a Green unlocked it): at the unsquared metric, the zero law is literal `List.incl` (h = 0 ⟺ every A-vertex coincides with a B-vertex) and the directed triangle routes the arg-max vertex through nearest neighbours + `dist_triangle`. On the nonempty-list carrier (the empty sentinel genuinely falsifies both laws) `Hsym` yields the full HKR metric. Metric-unit pins: the 423-a asymmetric witness reads 2 / 3 unsquared. |
| HKR §II Voronoi surface | `vor2_zero_at_sites`, `vor2_midpoint_ridge`, `vor2_translation`, `vor2_lipschitz`, `vor2_profile_0_4` | The distance transform really is an egg carton: floor at sites, ridge at the midpoint at half the separation, slides under translation (the `H(A,B⊕t)` machinery), and is 1-Lipschitz — why rasterizing on a unit grid (paper §IV) loses at most half a pixel. |
| WZ Lemma 2 (i–ii) | `PenetrationGauge.v : gauge_hex_nonneg`, `gauge_hex_zero_iff` | Depth scores are nonnegative and vanish only at the origin (zero depth = touching, not overlapping). |
| WZ Lemma 2 (iii–iv) | `gauge_hex_abs_homogeneous`, `gauge_hex_subadditive` | The hexagon gauge scales and obeys the triangle inequality — "essentially a norm", so depth composes sanely under translation budgets. |
| WZ Lemma 2 (v) + eq (18a) | `gauge_hex_sublevel`, `gauge_hex_unit_ball` | `λF = {g ≤ λ}` — the identity that turns "largest inscribed dilation" into 1-D root finding. The unit sublevel is the paper's test hexagon verbatim. |
| norm equivalence | `gauge_sandwich` | `ℓ¹/2 ≤ hex ≤ ℓ∞ ≤ ℓ¹`: swapping the gauge moves any depth by at most 2× — the sanity bound for mixing clearance metrics. |
| WZ eq (1)–(2) | `PenetrationMinimax.v : interval_minkowski_diff` | `[−s,s] ⊖ [−u,u] = [−(s+u), s+u]`: the per-axis separating budget of two crates is the sum of half-widths — what every axis-aligned broadphase assumes. |
| WZ eqs (9)–(11), Thm 1 | `f_box_nonneg`, `f_box_nondecreasing`, `f_box_convex`, `f_box_zero_iff`, `box_inclusion_iff_le`, `box_inclusion_iff_fzero` | The box-instance profile `f(λ) = max(0, λ−c)` satisfies Theorem 1, and eq (10)'s "inclusion ⟺ h = 0 ⟺ λ ≤ c" chain holds exactly; the largest zero is the inscribed radius (eq (9)). `f_box_nondecreasing` is also Lemma 1(i) in this model. |
| WZ Thm 2, eqs (12)–(13) | `convex_three_point`, `secant_step_safe` | The secant iterate stays in `[λ*, λᵏ)` — monotone decrease, never undershoot — derived from the convexity inequality **alone** (even the slope gap `f(λᵏ) < f(λᵏ⁻¹)` is derived, not assumed). |
| WZ §IV initialisation | `secant_one_step_exact`, `secant_pin_paper_init`, `secant_box_never_undershoots` | On the affine stretch the secant is exact: starting from the paper's own `λ⁰ = 200` with depth 2, one step lands on 2 — and the abstract safety theorem instantiates at the box model. |
| Meinert Alg. 2 kernel | `FrechetMaxmin.v : frechet_maxmin_ge_current`, `frechet_maxmin_carry_monotone`, `frechet_maxmin_pred_monotone`, `frechet_maxmin_le_envelope` | The 4-LoC kernel `max(min(a,x1),x2)`: the leash always covers the current pair, and the cell value is monotone in its predecessors — the soundness core of replacing Eiter–Mannila's top-down recursion by a bottom-up row sweep. |
| EM eq (1), 2×2 | `dF_2x2_closed_form` | Unrolling the DP on two 2-point curves gives `max(d11, d22)` identically: the diagonal coupling wins and the min correctly discards both detour cells — for **all** real inputs, no metric facts needed. |
| Meinert footnote 1 | `dF_pad_invariant` | Repeating a vertex leaves the discrete Fréchet value unchanged (padded 3×2 = 2×2, all inputs) — the law that makes SIMD batch length-equalisation sound. |
| Fréchet vs Hausdorff | `frechet_sees_direction`, `dF_2x2_discards_detour` | A route and its reverse have identical vertex sets (all set distances 0 — cf. 423-a) but ordered leash 3: why trajectory analytics needs Fréchet. The detour probe kills the "max of all four entries" misreading. |

## Proof engineering notes

- **Rational case algebra instead of inf/sup.** Both papers define their
  objects by infima over ℝ or over sets. The lane replaces each with its
  closed form on the mechanised instances (`Rmax`/`Rmin`/`Rabs`
  expressions) and proves the *characterising identities* (sublevel,
  zero-iff, inclusion-iff) — the same move as the Koc lane's sqrt-free
  normalisers. Every proof is `Rle_dec`/`Rcase_abs` case-split + `lra`,
  or `nra` where products of hypotheses appear (convexity).
- **Cleared denominators.** Theorem 2's eq (12) divides by `λᵏ − λᵏ⁻¹`
  and `f(λᵏ) − f(λᵏ⁻¹)`. `convex_three_point` states the three-slope
  inequality with denominators multiplied out, so the secant lemma needs
  exactly one `field` step and no division discipline downstream.
- **Abstraction cut exactly at the claim boundary.** `Hsym_*` is proved
  over an abstract directed `h` with three axioms; the *discrete* max-min
  `h` of HKR eq (2) is micro-claim **423-a** (`eval/Claim423a.v`, RED —
  the max-min realization spec). This lane deliberately does not define
  or prove the discrete max-min in production: that is 423-a's Green,
  gated on the board. When it lands (plus a directed-triangle claim),
  `Hsym` instantiates to HKR eq (1) with no new metric work.

## Honest scope (what is NOT formalised)

- The **PDHG inner solver** (WZ recursion (16)) and Algorithm 2 — the
  numerical minimax machinery is out of scope; only the outer secant
  safety is proved.
- The **continuity** clause of WZ Theorem 1 (perturbation analysis) —
  the mechanised clauses are nonnegativity, monotonicity, convexity.
- General convex `C` — the model layer is the box instance (exactly
  solvable, rational); the gauge layer is the paper's own 2D test family
  (hexagon, ℓ¹, ℓ∞), not arbitrary compact convex symmetric F.
- HKR's translation search `M_T` (eq (3)), ranked partial distances
  (eq (4)), and grid rasterization (§IV) — noted as future rungs for
  epic #423; the 1-Lipschitz lemma is the seed of the §IV half-pixel
  bound.
- The discrete max-min itself — **RED by design** (423-a).
- Meinert's general `P×Q` list DP, his Theorem 1 (the fold/scan
  Algorithm 2 computes eq (1) in `O(Q)` memory), and the Eiter–Mannila
  sandwich `δ_F ≤ δ_dF ≤ δ_F + max(ε_p, ε_q)` — the list DP with its
  monotone-coupling spec is the natural future **Fréchet RED claim** of
  epic #423, sibling of 423-a; only the shape-fixed unrollings and the
  kernel invariants are Qed here.
