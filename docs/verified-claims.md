# Verified Claims — NetTopologySuite.Proofs

> **Living, CI-verified document.** Every theorem cited below (in
> `<module> : <name>` form) is cross-checked against the source by
> [`scripts/validate-claims.sh`](../scripts/validate-claims.sh) on each CI run;
> a renamed or removed theorem orphans its claim and fails the build. (Qed-
> closure itself is enforced corpus-wide by `scripts/check_admitted.sh`.)

Citable index of what is actually proved (Rocq 9.1.1; Flocq 4.2.2 for the
binary64 layer). Each row: `file : theorem`, plain meaning, axiom footprint,
regime. These are *soundness* statements, not a verified re-implementation.

**Regimes.** `[exact]` exact reals · `[int-b64]` integer-coordinate binary64
(`|coord| ≤ 2²⁵`) · `[int-b64-arc]` integer-coordinate binary64 for the
degree-4 `b64_inCircle` chain (`|coord| ≤ 2¹¹`, tighter than orient2d) ·
`[full-b64]` *all* finite binary64 (exact, no magnitude limit) · `[cond]`
holds under named hypotheses · `[oracle]` extracted, differential-testable
against the C# port.

**Axioms.** `theories/` uses 3 classical-reals axioms (`sig_not_dec`,
`sig_forall_dec`, `functional_extensionality_dep`); `theories-flocq/` adds
`Classical_Prop.classic` from Flocq (the "4" below). Every theorem is `Qed`;
CI rejects unregistered `Admitted`. Full README: [../README.md](../README.md).

When citing: lead with `[exact]` rows; present `[cond]` rows as "conditional
headline", never as solved; offer the oracle to reproduce a concrete case.

---

## Phase 0 — Robust orientation (CCW / `Orientation.Index`)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Orientation.v : cross_antisymmetric` | Swapping two points flips the sign `[exact]` | 3 |
| `Orientation.v : cross_cyclic` | Cyclic rotation preserves the sign `[exact]` | 3 |
| `Orientation.v : cross_translation_invariant` | Translation preserves orientation `[exact]` | 3 |
| `Orientation.v : cross_at_P0_is_collinear` (+`_P1`,`_degenerate_base`) | Coincident points ⇒ sign 0 `[exact]` | 3 |
| `Orient_b64_exact.v : b64_orient2d_exact_for_small_int` | binary64 determinant = exact cross on integer coords `[int-b64]` | 4 |
| `Orient_b64_exact.v : b64_orient_sign_filtered_sound_small_int` | Filtered (fast) predicate's Pos/Neg/Zero agree with the true sign on integer coords `[int-b64]` | 4 |
| `Orient_b64_exact_full.v : b64_orient2d_exact_sound` | **Full-plane headline.** The *exact* predicate's Pos/Neg/Zero agree with the true orientation sign for **all finite binary64** — no `\|coord\| ≤ 2²⁵` limit `[full-b64]` | 3 |

`[oracle]` `RobustOrientation` bit-exact vs `ORIENT`/`ORIENT_FILTERED`;
`ORIENT_EXACT` is the exact full-plane reference (mirrors `b64_orient2d_exact`).

**Exact predicate — full plane, 3 axioms.** `b64_orient2d_exact` is proven
sound over the *entire* binary64 plane (every finite double is a dyadic
`m·2ᵉ`; the determinant sign is computed exactly in `ℤ`). Unusually for
`theories-flocq/`, it stays at **3 axioms** (no `Classical_Prop.classic`) —
it uses only the `B2R` decode + exact `ℤ` arithmetic, no float ops.

**Still open / honest scope.** The *fast* Shewchuk-adaptive filter
(`b64_orient_sign_filtered`) is proven only on integer coords (Stage A); its
general bounded-magnitude soundness (Stages B–D) remains a registered
deferred proof. And JTS/NTS double-double `Orientation.index` is **not**
proven sound — the exact predicate is the ground-truth spec it should be
diffed against (JTS #1106).

## Relate / DE-9IM integer-coordinate substrate (#67)

Grounds the integer-arithmetic overflow-safety of the Romanschek, Clemen &
Huhnt (ISPRS IJGI 2021, 10, 715) robust DE-9IM approach (§3.2). Pure `ℤ`,
**0 axioms** (every theorem *Closed under the global context* — fewer than the
3-axiom `[exact]` reals rows). `[int]` = exact integer coordinates, bounded
window.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateIntDetBound.v : idet_abs_le_2sq` | Orientation determinant on coords in `[0,c]` satisfies `\|idet\| ≤ 2c²` (conservative algebraic bound) `[int]` | 0 |
| `RelateIntDetBound.v : idet_fits_int64_for_int32_coords` | 32-bit integer coords ⇒ determinant fits a signed 64-bit integer (`2·(2³¹−1)² ≤ 2⁶³−1`) — the paper's "32 bit integers can be used for the coordinates" `[int]` | 0 |
| `RelateIntDetBound.v : cmax_sq_le_int64` (+`cmax_succ_sq_gt_int64`) | `cmax = 3 037 000 499 = ⌊√(2⁶³−1)⌋` pinned exactly (the paper's tight 64-bit window, Eq 5/8) `[int]` | 0 |
| `RelateIntDetBound.v : idet_max_witness` (+`idet_min_witness`) | Triangles realize `±cmax²` ⇒ the determinant range `[−cmax², cmax²]` is tight `[int]` | 0 |

**Honest scope.** The universal *geometric* bound `\|idet\| ≤ c²` (Eq 4 — the
half-box-area fact that would license the full `[0, cmax]` window) is deferred;
what is closed is the conservative `2c²` bound (sufficient for the 32-bit
regime), the exact `cmax` bracketing, and the `±cmax²` tightness witnesses.

## Phase 1 — Robust segment intersection (`RobustLineIntersector`)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Intersect.v : segments_share_point_implies_opposite_sides` | Shared point ⇒ neither line strictly separates the other `[exact]` | 3 |
| `Intersect.v : same_side_rejection_is_sound` | **Rejection is sound:** a "no intersection" verdict never drops a real crossing `[exact]` | 3 |
| `Intersect.v : strict_completeness` | Strict opposite-sides both tests ⇒ interior crossing exists `[exact]` | 3 |
| `Intersect.v : collinear_share_iff_1d_overlap` | **Collinear case (new):** sharing a point ⇔ 1-D extents overlap `[exact]` | 3 |
| `Segment.v : between_of_on_line_and_coord_range` | Collinear + coord-range bounds ⇒ point lies on the segment `[exact]` | 3 |
| `Intersect_b64.v : b64_intersect_sign_filtered_sound_small_int` | 5-valued predicate's None/Point verdicts sound on integer coords `[int-b64]` | 4 |
| `Intersect_b64_exact.v : b64_intersect_point_{x,y}` | Intersection coords carry a Qed forward-error bound (K·ε) `[int-b64]` | 4 |

`[oracle]` `SignFiltered` bit-exact on 187/187 differential cases.
**Open:** float coordinate computation (needs `b64_div` + error analysis).

## Phase 2 — Snap rounding (Hobby / Halperin–Packer noder)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `SnapRounding_b64.v : b64_snap_round_preserves_passes_through` | Snapping preserves which hot pixels a segment passes through `[int-b64]` | 4 |
| `SnapRounding_b64.v : b64_snap_idempotent_finite` | **Precision-reducer idempotence:** re-snapping a finite point to the grid returns the *identical* binary64 (bit-level, not just equal real) `[int-b64]` | 4 |
| `TopologicalCorrectness_b64.v : b64_snap_round_preserves_shared_hot_pixel` | Segments sharing a pixel still share one after snapping `[int-b64]` | 4 |
| `HobbyTheorem_b64.v : hobby_lemma_4_2` | Hobby Lemma 4.2 (strip-shaped snap region) `[exact]` | 3 |
| `HobbyTheorem_b64.v : hobby_theorem_4_1_conditional` | **Conditional headline:** snap preserves "fully intersected", assuming Lemma 4.3's no-proper half `[cond]` | 4 |
| `HotPixel_b64.v : b64_passes_through_sound` | **Closed filter sound:** bool `true` ⇒ the segment (and its unit-grid snap) really meet the closed hot pixel `[exact]` | 4 |
| `HotPixel_b64.v : b64_passes_through_complete` | **Closed filter complete:** a real (half-open) pass ⇒ the bool fires `[exact]` | 4 |
| `HotPixel.v : in_hot_pixel_convex` | Half-open hot pixel is convex: both endpoints in ⇒ whole segment in `[exact]` | 3 |
| `HotPixelConvex_b64.v : b64_both_endpoints_in_pixel_whole_segment` | Same, lifted to b64-bridged points — the rounding-free endpoint route `[exact]` | 4 |
| `PassesThrough_b64_compute_unsound.v : b64_passes_through_compute_unsound` | **Honest negative:** the *rounded* compute filter is NOT sound vs the exact spec — a witness with `compute = true`, `spec = false` (sub-ulp over-accept) `[exact]` | 4 |
| `PassesThroughHalfopen_b64_compute_unsound.v : b64_passes_through_halfopen_compute_unsound` | Same honest negative for the **half-open** mode (`PASSES_THROUGH_HALFOPEN`): rounded half-open filter unsound vs its exact spec `[exact]` | 4 |
| `PassesThroughHalfopen_b64_compute_incomplete.v : b64_passes_through_halfopen_compute_incomplete` | **Honest negative (noder-unsafe direction):** the rounded half-open filter is NOT complete — `spec = true`, `compute = false` (drops a real pass grazing the open edge) `[exact]` | 4 |
| `PassesThrough_b64_compute_asymmetric.v : b64_passes_through_compute_asymmetric` (+`_halfopen_`) | **Honest negative (order-dependent noding):** the rounded passes-through filter is NOT symmetric under segment reversal — `compute P0 P1 C = true` but `compute P1 P0 C = false` (closed + half-open). The order-dependence root behind JTS#752 / JTS#1133; pure `vm_compute` `[full-b64]` | 4 |
| `PassesThrough_b64_spec_symmetric.v : b64_passes_through_hot_pixel_symmetric` | **Green companion:** the *exact* R-spec passes-through filter IS symmetric under segment reversal (`spec P0 P1 C = spec P1 P0 C`) — the order-safe noder primitive the rounded filter fails to be `[exact]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_passes_through_grid_exact_iff_touch` | **C1 grid-exactness reduction (#66 pivot):** on the unit grid a point is a fixed point of `b64_snap`, so the snap-consistency conjunct is vacuous — full-predicate grid-exactness (`compute = spec`) reduces to the single Liang-Barsky touch. Isolates the open rounded-vs-exact touch core; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : coord_int_safe_snap_id` | **C1 slice 2:** an integer-valued, bounded, finite coordinate (`coord_int_safe`) is a `b64_snap` fixed point — the integer grid IS the fixed-point grid, so the reduction's hypothesis is discharged for genuine integer-grid (post-snap noder) inputs; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : slab_guard_bridge` | **C1 slice 3:** the rounded compute degenerate-slab guard on binary64 operands equals the exact-spec guard on their `B2R` values (`b64_le_eq_Rle_bool` + `b64_eqb_true_iff_B2R`); the division-free layer of the single-touch core; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_minus_half_exact` | **C1 slice 4 (coordinate-exactness):** general half-integer subtraction is exact — for half-integer-valued operands with mantissa difference `< 2^prec`, `b64_minus` equals the exact real difference (`generic_format_half_prec` + `b64_minus_correct`). Covers the t-bound numerators (half-integer slab bound − integer endpoint) that exceed the existing 27-bit helper; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_max_B2R` (+`b64_min_B2R`) | **C1 slice 5 (max/min composition):** the operand-selecting `b64_max`/`b64_min` bridge to `Rmax`/`Rmin` on `B2R` values for finite operands — reduces the clipped-interval t-bound test to a comparison of the real values of the rounded t-bounds, isolating the division rounding to the per-bound level; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_div_round_half_over_int` | **C1 slice 6 (division-safety brick):** a half-integer numerator over a nonzero integer denominator divides bit-correctly to the rounded exact quotient — discharges `b64_div_correct`'s no-overflow precondition on the grid from `\|num/den\| ≤ \|num\| ≤ 2²⁸ < 2^emax` (`\|den\| ≥ 1`). The last division-safety obligation, closed; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_lb_tlo_eq_rounded_quotients_grid` (+`_thi_`) | **C1 slice 6 (division bridge):** on the integer grid each per-axis compute t-bound equals the exact-spec t-bound with each quotient *individually rounded* (`Rmin`/`Rmax` of `round((lo−c0)/(c1−c0))`, `round((hi−c0)/(c1−c0))`). Localises the entire residual to the per-quotient `round`; nothing but round-to-nearest's lack of an outward guarantee now separates compute from spec on the grid; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_lb_tlo_eq_round_exact_grid` (+`_thi_`) | **C1 slice 7 (round-of-exact):** rounding is monotone, so `Rmin (round a)(round b) = round (Rmin a b)` (dually Rmax) — each compute t-bound collapses to a *single* `b64_round` of the exact-spec t-bound. Unconditional (degenerate axis: `0 = round 0`, `1 = round 1`); Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_tmin_eq_round_exact_grid` (+`b64_tmax_…`) | **C1 slice 8 (clip composition):** pushing `round` through the outer `Rmax 0`/`Rmin 1` clip and the per-axis `Rmax`/`Rmin`, the whole compute clipped bound = `b64_round` of the exact-spec clipped bound. The compute/spec gap is now the single comparison `round tmin_e ≤ round tmax_e` vs `tmin_e ≤ tmax_e`; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_passes_through_complete_on_grid` (+ single-touch `b64_liang_barsky_touches_complete_on_grid`) | **C1 slice 9 — ON-GRID COMPLETENESS (Qed, closes one C1 direction):** on the integer grid, `spec = true ⇒ compute = true` — the rounded passes-through filter **never drops a pass** (the noder-SAFE direction). Free from monotonicity: `tmin_e ≤ tmax_e` ⇒ `round tmin_e ≤ round tmax_e` (slabs bit-identical, Slice 3). The on-grid *soundness* direction (`compute ⇒ spec`) remains the open core (cross-multiply → integer-determinant gap); Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_passes_through_grid_exact_cond` (+ `b64_liang_barsky_grid_exact_cond`, `b64_passes_through_sound_on_grid_cond`) | **C1 slice 10 — CONDITIONAL grid-exactness headline (Qed):** the full on-grid `compute = spec` equivalence, certified modulo ONE named real hypothesis `Rle_bool (round tmin_e)(round tmax_e) = Rle_bool tmin_e tmax_e` (the exact clip bounds `tmin_exact`/`tmax_exact`). Same honest shape as `hobby_theorem_4_1_conditional`; no Admitted/Axiom — the gap is a plain Prop hypothesis. Its `=true` half is free (Slice 9 completeness); only the `=false` (soundness) half is open, and the file documents the integer-determinant gap argument (provable unconditionally for `\|n\| ≤ 2²³`, borderline at the full `2²⁵` width); Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : round_reflects_le_of_sep` (+ `round_diff_le_of_round_le`, `clip_separated_reflects`, `b64_passes_through_grid_exact_sep`/`_sound_on_grid_sep`) | **C1 slice 11 — rounding-reflection kernel (Qed):** round-to-nearest moves each value `≤ ½ ulp`, so `round a ≤ round b ⇒ a − b ≤ ½ ulp(round a) + ½ ulp(round b)`; hence the rounded `≤` REFLECTS the exact `≤` once the values are ordered or separated beyond that band. Eliminates Slice 10's rounding hypothesis in favour of the **pure-reals** `clip_separated` (no `Rle_bool`-of-rounds): on-grid grid-exactness/soundness now hinges only on the exact bounds being ulp-separated — exactly the integer-determinant gap; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : rational_gap` (+ `grid_quotient_ratio`, `IZR_abs_ge_1`) | **C1 slice 12 — determinant-gap kernel (Qed):** two distinct rationals `na/da`, `nb/db` differ by `≥ 1/(\|da\|·\|db\|)` — their difference `(na·db − nb·da)/(da·db)` is a nonzero integer over `da·db`. `grid_quotient_ratio` exposes each grid t-bound as the integer ratio `IZR(m − 2n₀)/IZR(2(n₁ − n₀))`, so the binding `tmin_e − tmax_e` gap is `≥ 1/(\|2(x₁−x₀)\|·\|2(y₁−y₀)\|)`. The lower-bound (gap) half of `clip_separated`; pairing with a ulp upper bound closes it for bounded coords; Qed-closed `[exact]` | 3 |
| `PassesThrough_b64_grid_exact.v : b64_ulp_round_le_bpow` (+ `b64_ulp_round_le_unit`) | **C1 slice 13 — ulp upper bound (Qed):** `round x` stays in the binade of `x`, so `\|x\| ≤ 2ᵉ ⇒ ulp(round x) ≤ 2^(e+1−prec)` (`b64_round_abs_le_bpow` + Flocq `ulp_le`/`ulp_bpow`); the `[0,1]` instance gives `ulp(round x) ≤ 2^(1−prec) = 2⁻⁵²`. The **upper-bound half** of `clip_separated` — pairs with the slice-12 gap so the determinant beats the rounding band; the final tie-together (max/min selection + axis-degeneracy cases) yields unconditional on-grid soundness for `\|n\| ≤ 2²³`; Qed-closed `[exact]` | 4 |
| `PassesThrough_b64_grid_exact.v : grid_ratio_gap_exceeds_ulp_band` | **C1 slice 14 — gap beats band, `[-1,1]` (Qed):** for two distinct ratios `u=na/da`, `v=nb/db` in `[-1,1]` with `\|da\|,\|db\| ≤ 2²⁴`, `½ulp(round u)+½ulp(round v) < \|u−v\|` (band `≤ 2⁻⁵²` by slice 13, gap `≥ 2⁻⁴⁸` by slice 12). Exactly `clip_separated`'s right disjunct for the binding pair; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_ulp_round_le_rel` (+ `grid_ratio_gap_exceeds_ulp_band_rel`) | **C1 slice 15 — relative ulp + general gap-beats-band (Qed):** `\|x\| ≥ 2⁻²⁴ ⇒ ulp(round x) ≤ \|x\|·2^(2−prec)` (slice 13 at `e = mag x` + Flocq `mag` sandwich) — the RELATIVE bound that removes slice 14's `[-1,1]` restriction. With it, for two distinct **nonzero** grid ratios (numerator `≤ 2²⁵`, denominator `≤ 2²⁴`, `\|value\| ≥ 2⁻²⁴`) the band telescopes against the gap with no value-range cap: `band·\|da\|\|db\| ≤ 2⁻² < 1 ≤ gap·\|da\|\|db\|`. Covers every nonzero binding bound (incl. the constant `1 = 1/1`) — the complete analytic content of unconditional on-grid soundness for `\|n\| ≤ 2²³`; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : zero_vs_ratio_gap_exceeds_ulp_band` | **C1 slice 16 — value-0 edge of gap-beats-band (Qed):** the one binding shape slice 15 omits — a clip bound exactly `0`. With `ulp(round 0) = ulp 0 = bpow emin` (subnormal floor `~2⁻¹⁰⁷⁴`) and the relative bound on the nonzero side, `½ulp(round 0)+½ulp(round v) < \|0−v\|` for any `\|v\| ≥ 2⁻²⁴` (no ratio structure needed). Together with slice 15 the gap-beats-band family is now **total** over the binding pairs; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : gap_beats_band_of_gridbound` (+ `gridbound`, `gridbound_0/1`, `gridbound_Rmax/Rmin`) | **C1 slice 17 — `gridbound` structural glue (Qed):** a real is `gridbound` iff `0` or a bounded nonzero grid ratio (num `≤ 2²⁵`, denom `≤ 2²⁴`, `\|·\| ≥ 2⁻²⁴`). Closed under `Rmax`/`Rmin` (each selects one argument), so each exact clip bound `tmin_e = Rmax 0 (Rmax tlo_x tlo_y)`, `tmax_e = Rmin 1 (Rmin thi_x thi_y)` is `gridbound` once the per-axis t-bounds are. On `gridbound` inputs the gap-beats-band family is total: `gap_beats_band_of_gridbound` (composing slices 15+16) is **exactly `clip_separated`'s right disjunct** for any distinct binding pair. The last piece before the unconditional close is then just `tlo`/`thi` ∈ `gridbound`; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : gridbound_tlo`/`gridbound_thi` (+ `gridbound_half_quotient`, `coord_int_tight`) | **C1 slice 18a — t-bounds are gridbound:** on the tight integer grid (`coord_int_tight`, `\|n\| ≤ 2²²`) each exact per-axis t-bound `lb_tlo`/`lb_thi` is `gridbound` (degenerate axis → `0`/`1`; else `Rmin`/`Rmax` of two half-edge quotients `IZR m/2 − …`, each gridbound). Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_passes_through_grid_exact` (+ `b64_passes_through_sound_on_grid`, `clip_separated_tight`) | **C1 slice 18 — UNCONDITIONAL on-grid grid-exactness (Qed, closes C1 in the tight regime):** for integer-grid points with `\|n\| ≤ 2²²`, `b64_passes_through_hot_pixel_compute = b64_passes_through_hot_pixel` — **no named hypotheses**. `clip_separated` is discharged outright (`tmin_e`/`tmax_e` gridbound ⇒ gap beats band, slice 17), so the slice-10 conditional becomes unconditional; soundness (`compute ⇒ spec`) and completeness (slice 9) both hold. The rounded filter is machine-checked unsound *off* the grid (`PassesThrough_b64_compute_unsound.v`) yet **exact in the grid-aligned regime a snap-rounding noder actually runs in**; Qed-closed `[full-b64]` | 4 |
| `SpectrePassesThroughWitness.v : spectre_edge_passes_thru` / `_misses` / `_grid_exact_cond` | **C1 witness test on the SPECTRE monotile (Qed):** a 2×-scaled Spectre edge `(12,0)–(15,2)` (companion to `theories/SpectreExample.v`) is shown on the integer grid (`bpoint_int_safe`, via the reusable `b64Z`), the extracted compute filter's `vm_compute` verdicts are exhibited (TRUE at through-pixel `(13,1)`, FALSE at missed-pixel `(14,0)`), and the slice-10 conditional grid-exactness headline is instantiated on it — `compute = spec` modulo the one named reflection. Regression anchor `[full-b64]` | 4 |

`[oracle]` `PASSES_THROUGH_FILTER`/`PASSES_THROUGH_HALFOPEN`. The closed-filter
rows pin the **closed** filter, sound *and* complete vs the closed hot-pixel
R-spec at unit grid (the half-open predicate is strictly stronger:
`b64_..._halfopen_implies_closed`). These characterise the R-spec predicate;
the extracted oracle runs the bit-exact computational mirror
(`PassesThrough_b64_compute.v`, validated bit-for-bit). The naive
`compute ⇒ spec` rounding bridge is **machine-checked false** (the last row;
`docs/oracle-soundness-finding.md`); the provable, useful directions are grid
exactness (C1) and completeness `spec ⇒ compute` (C2). **On the integer grid,
completeness is now Qed-closed** (`b64_passes_through_complete_on_grid`, slice 9
— the rounded filter never drops a pass on the grid, the noder-safe direction).
The matching on-grid *soundness* (`compute ⇒ spec`) is now **Qed-closed
UNCONDITIONALLY for `|n| ≤ 2²²`** (`b64_passes_through_sound_on_grid`,
slice 18) — together with completeness this gives the full equality
`compute = spec` on the tight grid (`b64_passes_through_grid_exact`), with **no
named hypotheses**. The route: reduce to the pure-reals `clip_separated`
(slice 11), discharge it from the determinant gap `≥ 1/(4|d_a d_b|)` beating the
rounding band `≤ 2⁻⁵²` (slices 12–17), then show the exact clip bounds are
`gridbound` (slice 18). The full `coord_int_safe` width `2²⁵` is borderline (gap
can fall to `~2⁻⁵⁴ < ulp`) and needs the exact integer-determinant comparison,
not a forward-error bound — see `docs/audit-rgr-comparison.md`. The
general-binary64 C2 stays strongly-evidenced
open. The rounded filter is also **not symmetric** under segment reversal
(`PassesThrough_b64_compute_asymmetric.v`, both modes) — the order-dependent
noding root behind JTS#752 / JTS#1133; the symmetric, sound primitive is the
exact R-spec, not the rounded compute filter.
**Refuted:** `hobby_lemma_4_3_no_proper` is **machine-checked false** as
stated (`HobbyCounterexample_b64.v`; `docs/hobby-lemma-4-3-no-proper-refutation.md`)
— snap-rounding collapses two parallel segments onto one grid line,
manufacturing a collinear-overlap proper intersection. Moved from the
deferred-proof registry to the counterexample registry. Cite as
"conditional headline"; the per-pair preservation premise is provable
only over noded arrangements, not for arbitrary segment pairs.

`[oracle]` `CURVE_SNAP_DECISION` / `CURVE_SNAP_INVARIANTS_EXACT` (PRC-SN,
JTS#1195): exact-`Q` curve-snap grid-friendliness — snap the three arc control
points to a 1/scale grid (`q_make_precise`), then `PRESERVE` the arc iff the
snapped circumcentre lands on the grid, else `DENSIFY` (`DEGEN` if the snapped
controls go collinear). Exact `Q` catches the double-rounding the JTS binary64
centre computation hides on large / sub-grid coordinates. Reuses the
snap-rounding machinery; pure rational, no transcendental and no new axiom.

## Phase 3 — Planar overlay (OverlayNG)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Overlay.v : boolean_op` (+comm. lemmas) | Set semantics of union/intersection/difference/symdiff `[exact]` | 3 |
| `OverlayBridge.v : correct_labels_all_ops` | Edge labelling correct for every boolean op `[int-b64]` | 4 |
| `OverlayCorrectness.v : overlay_ng_correct_conditional` | **Conditional headline:** extracted overlay = boolean op, under 3 named hypotheses `[cond]` | 4 |
| `JordanCurveSeam.v : geometric_interior_stdlib_vacuous` | **JCT seam refutation:** the corpus's `geometric_interior_stdlib` is identically false (discontinuous "jump" paths collapse `connected_in_complement`), so the JCT-conditional headline is only vacuously satisfiable `[exact]` | 3 |
| `JordanCurveSeam.v : jct_hypotheses_force_empty_interior` | The conditional headline's `geometric_interior_stdlib ↔ interior_pred` hypothesis forces `interior_pred` empty too `[exact]` | 3 |
| `JordanCurveSeam.v : far_points_connected_cont` | The corrected continuous relation is non-degenerate: a straight-line path joins two off-box points in the complement — discontinuity, not geometry, caused the collapse `[exact]` | 3 |
| `JordanCurveSeam.v : jct_cont_interior_is_geometric` | **Sufficiency:** under `JCT_two_components_cont` (now with the separation clause), every interior point is a `geometric_interior_cont` point — so re-pointing H1 onto `geometric_interior_cont` is a genuine, satisfiable obligation, not the vacuous one. Does *not* prove the JCT `[exact]` | 3 |
| `JCT.v : continuity_glue` | Two functions continuous on ℝ that agree at a point glue into a continuous function — the analysis lemma behind continuous-path concatenation `[exact]` | 3 |
| `JCT.v : connected_in_complement_cont_trans` | `connected_in_complement_cont` is transitive (midpoint concatenation, glued continuous); with `_refl`/`_sym` it is an equivalence relation on the complement `[exact]` | 3 |
| `JCT.v : in_bounded_component_cont_invariant` | Boundedness is a component invariant for the continuous relation — constant on a connectivity class `[exact]` | 3 |
| `JCT.v : no_path_from_interior_to_exterior` | **Sketch's "thesis-scale" core is free:** with interior = bounded component, an interior point reaches no non-interior point through the complement — the Qed counterpart of `JCT_two_components_cont`'s separation clause, by component invariance, no JCT `[exact]` | 3 |
| `JCT.v : far_point_not_interior` | Honest continuous analogue of the vacuity witness: a point far past the bounding box is NOT interior (a real straight-line ray escapes any radius) — without claiming the interior empty `[exact]` | 3 |
| `JCT.v : point_in_ring_correct_jct_cont` | **Non-vacuous continuous headline:** `point_in_ring ↔ geometric_interior_cont` under the single named seam Prop `parity_characterises_interior_cont` (the genuine remaining JCT content) `[cond]` | 3 |

`[oracle]` `EDGE_IN_RESULT`.
**Open:** `extract_rings_valid` (DCEL, registered deferred) + polygonal JCT
(thesis-scale, no stub). The JCT seam's prior `geometric_interior_stdlib`
formulation is now **refuted as vacuous**
(`JordanCurveSeam.v : geometric_interior_stdlib_vacuous`); the genuine
theorem is restated over continuous paths as `JCT_two_components_cont`
(stated, not proved), and the overlay/buffer headline H1 has been
**re-pointed** off `geometric_interior_stdlib` onto `geometric_interior_cont`
(`OverlayCorrectness.v`, `docs/buffer-noder-pipeline.md`) so it is no longer
vacuous. See [`docs/jct-vacuity-finding.md`](jct-vacuity-finding.md) and
[`docs/h1-vacuity/`](h1-vacuity/). Cite as "conditional headline + oracle".

## Phase 4 — Native curves (linearization, chord-approx arcs)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Linearise.v : chord_le_detour` | A chord ≤ the polyline detour it replaces `[exact]` | 3 |
| `Linearise.v : disjoint_under_linearise` | ε-linearization preserves disjointness within tolerance `[exact]` | 3 |
| `Linearise.v : regime3_counterexample` | Honest negative: a predicate linearization cannot preserve `[exact]` | 3 |
| `SpectreChordArcWitness.v : spectre_chord_clips_arc_misses` (+ `_passes_misses`) | **Chord-vs-arc clip divergence (Qed):** the concrete hot-pixel form of chord-overfitting on a curved SPECTRE edge. A shallow arc `(-1,1)–(0,½)–(1,1)` (circle centre `(0,7/4)`, r=5/4, sagitta ½) and a pixel at the chord midpoint `(0,1)` (scale 2, box `[-¼,¼)×[¾,5/4)`): the straight CHORD `segment_touches_hot_pixel` (midpoint `t=½`), but the ARC does NOT — `~arc_touches_hot_pixel` and `~arc_passes_through_hot_pixel`, since the box is strictly inside the circle (`inCircle_R = 25/16 − x² − (y−7/4)² ≥ ½ > 0`). A false positive of chord approximation against passes-through; companion to `theories/SpectreExample.v` `[exact]` | 3 |
| `ArcChordApprox.v : sagitta_le_arc_radius` | Chord-vs-arc deviation bounded by the radius `[exact]` | 3 |
| `ArcIntersectIVT.v : chord_crosses_arc_circle_implies_circle_intersection` | Sign change of in-circle along a chord ⇒ real crossing (IVT) `[exact]` | 3 |
| `ArcOverlay.v : arc_overlay_correct_chord_approx` | **Conditional headline:** result point within `max_sagitta` of an arc, under 2 bridge hypotheses `[cond]` | 3 |
| `Atan2.v : cos_atan2` (+`sin_atan2`) | **Option-A foundation (issue #64):** the Stdlib-`Ratan`-built `atan2 y x` is the polar angle of `(x,y)` — `cos = x/r`, `sin = y/r` for `(x,y)≠0` `[exact]` | 4 |
| `AngleBetween.v : cos_angle_between` (+`sin_angle_between`) | **Option-A central angle/sweep (issue #64):** the signed angle `atan2(cross,dot)` between two vectors has `cos = dot/(\|u\|\|v\|)`, `sin = cross/(\|u\|\|v\|)` (Lagrange identity); sign encodes orientation. Range (-π,π] via `atan2_range` `[exact]` | 4 |
| `ArcLength.v : chord_le_arc_length` (+`chord_subtended_sq`) | **Option-A exact arc length (issue #64):** `arc_length = r·θ`; the chord never exceeds the arc (`2r·sin(θ/2) ≤ rθ`), and `chord² = 2r²(1−cosθ)` (half-angle bridge to dot products) `[exact]` | 4 |
| `InCircle_b64_exact.v : b64_inCircle_exact_sound` | **Full-plane sign exactness (issue #64 ask #4b):** the common-exponent integer-determinant predicate's sign agrees with `inCircle_R_BP` for all finite binary64 inputs — integer `ℤ` arithmetic only, no float ops, **3 axioms (no `classic`)** `[full-b64]` | 3 |
| `InCircle_b64_exact.v : b64_inCircle_exact_for_small_int` (+ `_exact_and_finite_`, `b64_inCircle_finite_for_small_int`) | **Integer-regime value exactness + finiteness:** `B2R (b64_inCircle …) = inCircle_R_BP` on the nose when every coordinate is integer-valued with `\|n\| ≤ 2¹¹`; the companion `_finite_` projection exposes `is_finite (b64_inCircle …)` (always established inside the exactness proof) — the prerequisite for the arc-line Scope B/C round-chain `[int-b64-arc]` | 4 |
| `InCircle_b64_exact.v : b64_inCircle_B2R_sign_sound_small_int` | Sign of the rounded `b64_inCircle` value agrees with `inCircle_R_BP` in the same `2¹¹` integer regime `[int-b64-arc]` | 4 |
| `InCircle_b64_exact.v : perron_inCircle_sign_sound` | Perron stage-10 thin-sliver witness at the `2¹¹` boundary: opposite-sign chord endpoints with bit-exact `b64_inCircle` values `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_{sP_R,sQ_R,dx_R,dy_R}` | **Arc-line Scope A (issue #64 ask #5a):** first-stage Cramer prefix before division — outer `sP`/`sQ` inCircle evaluations and chord `dx`/`dy` differences are bit-exact integer-valued binary64 `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_den_exact` (+ `_den_nonzero`) | **Arc-line Scope B.1 (issue #64 ask #5a):** the division denominator `den = sP − sQ` is computed **bit-exactly** (`= inCircle_R_BP S M E P − inCircle_R_BP S M E Q`, finite) — both inCircle values are integers `≤ 2⁵²` so the difference `≤ 2⁵³ = 2^prec` is exact — and is nonzero exactly under the safety predicate. The denominator round-chain gate; uses the new `b64_inCircle_finite_for_small_int`. Division/mult/add round-chain (Scope B.2) now landed (see next row); forward-error (Scope C) remains queued `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_intersect_point_{x,y}_round_chain` | **Arc-line Scope B.2 (issue #64 ask #5a):** the *full* coordinate round-chain identity — `B2R (b64_arc_line_intersect_point_x …) = round(B2R(bx P) + round(round(sP/(sP−sQ)) · (B2R(bx Q) − B2R(bx P))))` (and symmetric for `y`). Each binary64 step is pinned to its IEEE-754 rounding of the exact-real operands: the integer-exact prefix (`sP`, `den`, `dx`/`dy` from Scope A/B.1) feeds a `div → mult → plus` chain, each discharged via `b64_{div,mult,plus}_correct` with magnitude gates (`\|sP\| ≤ 2⁵²`, `\|den\| ≥ 1`, `\|dx\| ≤ 2¹²`, `t·dx ≤ 2⁶⁴`, sum `≤ 2⁶⁵ < 2^emax`). This is the exact statement of *what the float intersection computes* — the launch point for the Scope C forward-error bound `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_t_forward_error` (+ `_t_round`, `_t_abs_le_bpow_52`, `arc_line_ratio_abs_le_52`) | **Arc-line Scope C layer-1 (issue #64 ask #5a):** the computed division parameter `t = b64_div sP den` deviates from the *exact-real* ratio `sP_R/(sP_R−sQ_R)` by at most **½** — a single division half-ulp. Because the denominator is **bit-exact** (Scope B.1), there is *no* denominator-carryover error (unlike the line-line layer 1, which rounds its own denominator). Derivation: `\|sP_R\| ≤ 2⁵²`, `\|den_R\| ≥ 1` ⇒ `\|ratio\| ≤ 2⁵²` ⇒ `ulp(round ratio) ≤ bpow 0 = 1` ⇒ half-ulp `≤ ½`. First layer of the Scope C forward-error cascade against `arc_line_intersect_x_R`; layers 2–4 (mult, plus, headline) queued `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_mult_{x_forward_error,y_forward_error}` (+ `_mult_*_round_error`, `_mult_*_carry_error`, `_mult_*_safe`, `_mult_*_abs_le_bpow_64`, `_d{x,y}_abs_le_bpow_12`) | **Arc-line Scope C layer-2 (issue #64 ask #5a):** the computed product `b64_mult t d` (`d = bx Q − bx P`, resp. `by_`) deviates from the exact-real `ratio · d_R` by at most **bpow 12** (and symmetric for `y`). Decomposition: multiply half-ulp (`ulp ≤ bpow(64−prec+1) = bpow 12`, so `≤ bpow 11`) + carry of the layer-1 t-error (`\|d_R\| · ½ ≤ 2¹²·½ = bpow 11`). **No `1/\|den\|` term** — because layer 1 is absolutely `≤ ½` (bit-exact denominator, Scope B.1), the arc-line bound is a clean constant, unlike the line-line layer whose denominator-rounding carries a `bpow 80/\|den\|` tail. Layers 3–4 (the `bx P + ·` add and the coordinate headline vs `arc_line_intersect_{x,y}_R`) queued `[int-b64-arc]` | 4 |

`[oracle]` `INCIRCLE_SIGN`/`ARC_CHORD_CROSSES_CIRCLE`/`ARC_PASSES_THROUGH_PIXEL` +
the three issue-#64 arc-length modes below.
**Arc length is transcendental** (`s = √r²·Θ`, `Θ` an angle) so it has *no
Coq-extractable form*. The honest oracle therefore splits along the exactness
ladder (cf. `ArcChordApprox.v`'s polynomial layer):
- **`ARC_LENGTH_INVARIANTS_EXACT`** — the *exact-rational* invariants `r²`,
  `cos θ₀ = dot/r²`, major-arc flag (pure zarith `Q`; mirrors
  `ArcLength.chord_subtended_sq` / `AngleBetween.cos_angle_between`). Exact about
  the geometry *around* the length, not the length value. Ratchet-clean.
- **`ARC_SHORTER`** — *exact decision* of which of two arcs is shorter, decidable
  rationally when radii match (order of `Θ` from `cos θ₀` + flag); reports
  `TRANSCENDENTAL` rather than rounding when radii differ. Ratchet-clean.
- **`ARC_LENGTH`** — the literal float length, an *interface-boundary* mode
  (the value JTS/NTS compute via `Math.sqrt`/`Math.acos`); one rounding past the
  exact invariants. Hand-rolled float, a sanctioned ratchet exception
  (`docs/oracle-handrolled-allowlist.txt`, interface-boundary category).

The **arc circular-segment area** (M-AREA-CP) follows the same split:
`A_seg = (r²/2)(Θ − sin Θ)`.
- **`ARC_AREA_INVARIANTS_EXACT`** — exact rationals `r²`, `cos θ₀`, `sin²θ₀`,
  major flag (pure `Q`, ratchet-clean).
- **`ARC_AREA`** — the float segment area, interface-boundary (one `acos`+`sin`
  past the exact invariants). These replace main's earlier hand-rolled shoelace
  stub, which had bypassed the (then BSD-awk-broken) ratchet.
**Option-A note (issue #64):** `atan2` work is **4-axiom** — Stdlib's `atan`
pulls `Classical_Prop.classic` (cos/sin/sqrt stay 3-axiom). This is the cost of
the JTS-faithful atan2 representation; downstream arc-length/sweep proofs
inherit it.
**Caveat:** bridge hypotheses are *boundary* closeness — this backs "chord
approximation correct to tolerance", **not** "fixes CIRCULARSTRING
self-intersection".
**Arc-line honest scoping (PR #146):** Scope A proves only the prefix before
the dividing step (`sP`, `sQ`, `dx`, `dy`). The headline
`B2R (b64_arc_line_intersect_point_x …) = arc_line_intersect_x_R …` does
*not* hold on the nose in the integer regime (intersection parameter is
generally non-dyadic). **Scope B is now closed:** B.1 pins the denominator as
bit-exact, and B.2 (`b64_arc_line_intersect_point_{x,y}_round_chain`) pins the
*entire* `div → mult → plus` coordinate computation to its IEEE-754 round-chain
of the exact-real operands. **Scope C is now open:** layer 1
(`b64_arc_line_t_forward_error`) bounds the division parameter's drift from the
exact-real ratio by ½ — and crucially shows the bit-exact denominator
contributes *zero* carryover error. Layer 2
(`b64_arc_line_mult_{x,y}_forward_error`) bounds the `t·d` product against
`ratio·d_R` by a clean `bpow 12` (no `1/|den|` tail, unlike line-line). Layers
3–4 (the `bx P + ·` add and the coordinate headline vs
`arc_line_intersect_{x,y}_R`) remain queued.

## Issue #67 — DE-9IM matrix algebra (`DE9IM.v`, session 1)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `DE9IM.v : im_disjoint_not_intersects_partial` | **Partial headline:** JTS `disjoint` forces `intersects₀/₁/₄` false (not full `intersects` — `intersects₃` can still match; see gap witnesses) `[exact]` | 0 |
| `DE9IM.v : im_contains_transpose_within` (+`predicate_contains_transpose_within`) | `contains` on `m` ⇔ `within` on `matrix_transpose m` (JTS converse) `[exact]` | 0 |
| `DE9IM.v : im_covers_transpose_coveredBy` (+`predicate_covers_transpose_coveredBy`) | `covers` on `m` ⇔ `coveredBy` on transpose (`pattern_transpose` on all four JTS covers patterns) `[exact]` | 0 |
| `DE9IM.v : disjoint_intersects3_example_holds` | **Honest gap:** a matrix can be both `disjoint` and `intersects₃` (abstract IM algebra ≠ complete geometry IM) `[exact]` | 0 |

Full RelateNG matrix-fill and prepared-cache slices remain follow-up (#67 S3+).

## Issue #67 — line-line DE-9IM soundness (`RelateLineLine.v`, session 2)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateLineLine.v : line_line_proper_cross_sound` | **Proper crossing:** strict opposite-sign crosses ⇒ witness matrix satisfies `Crosses` and `Intersects` `[exact]` | 3 |
| `RelateLineLine.v : line_line_rejection_disjoint_sound` | **Rejection:** same-side sign test ⇒ `Disjoint` witness and no shared point (soundness of NTS rejection) `[exact]` | 3 |
| `RelateLineLine.v : line_line_share_intersects_sound` | **Share-point:** any `between` witness ⇒ `Intersects` witness matrix `[exact]` | 3 |
| `RelateLineLine.v : line_line_collinear_overlap_sound` | **Collinear overlap:** both endpoints of CD on AB ⇒ `Overlaps` (LL) witness `[exact]` | 3 |

Witness matrices are soundness targets, not a computed RelateNG IM. Endpoint-only touches inherit existential `Intersects` only.

## Issue #67 — Romanschek line–line oracle matrices (`RelateLineLine.v`, S3 seed)

Pinned 9-char DE-9IM strings from Romanschek et al. (IJGI 2021) Table 5/6 /
[topology-relations](https://github.com/dd-bim/topology-relations) agree with NTS 2.3.0 at
extent `r_max ≤ 1056`. Vectors: `oracle/de9im_line_line_vectors.txt`. Predicate
lemmas only — no WKT→matrix computation yet.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateLineLine.v : paper_test7_overlaps` | Test 7 (`1FFF0FFF2`) satisfies `Overlaps` (LL) `[exact]` | 3 |
| `RelateLineLine.v : paper_test6_not_crosses` | Test 6 (`FF1FF0102`) does **not** satisfy `Crosses` under `pat_crosses_ll` (II=F) `[exact]` | 3 |
| `RelateLineLine.v : paper_test13_crosses` | Test 13 (`0F1FF0102`) satisfies `Crosses` (LL); II=0 matches `ll_matrix_point_ii` `[exact]` | 3 |
| `RelateLineLine.v : paper_test10_not_disjoint` | Test 10 (`FF10F0102`) is **not** `Disjoint` (BI=0) though segments are separated `[exact]` | 3 |
| `RelateLineLine.v : paper_test7_agrees_overlap_witness_core` | Test 7 shares II/BB cells with `ll_matrix_overlap_ii` `[exact]` | 3 |

## Foundational — squared distance / degenerate cases (`Distance.v`)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Distance.v : dist_sq_nonneg` | Squared distance ≥ 0 `[exact]` | 3 |
| `Distance.v : dist_sq_zero_iff_eq` | Squared distance = 0 ⇔ points coincide `[exact]` | 3 |
| `Distance.v : dist_le_iff_dist_sq_le` | Distance compare ⇔ squared-distance compare (justifies sqrt-free fast path) `[exact]` | 3 |

Unconditional exact-reals — the most directly citable rows.
