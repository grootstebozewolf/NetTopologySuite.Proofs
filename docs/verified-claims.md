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
| `ExtractFacesHoles.v : extract_faces_holes_valid` (+ `extract_faces_holes_nil`, `extract_faces_holes_label_fidelity`) | **With-holes emission (`extract_rings_valid` R5, slice 3h):** the face extractor emits polygons WITH holes, nesting supplied as a spec'd oracle; under the three structural noder hypotheses plus oracle well-formedness, every emitted polygon is `valid_polygon` conditional ONLY on the per-hole `hole_inside_outer` clause — the lane's single analytic residual, now carried by an emitting extractor. Empty assignment recovers the hole-free extractor `[cond]` | 3 |
| `FaceTwinAware.v : darts_of_twin_aware` (+ `pairwise_no_proper_cross_twin_aware`, `sip_swap_left/right`) | **Twin-aware simplicity is satisfiable (corrected-plan step 1):** the undirected pairwise non-crossing predicate lifts to `darts_of` once reverse pairs are excluded — exactly the H1 shape slice 3i proved unsatisfiable, repaired; the undirected premise is the interface the step-3 geometry discharges `[exact]` | 3 |
| `FaceTwinAware.v : face_ring_simple_twin_aware` (+ `ring_simple_of_subset_twin_aware`, `face_twin_free`) | **Simplicity chain without the full-D appeal (corrected-plan step 2):** a face ring of a twin-aware arrangement is `ring_simple` given per-face twin-freeness — `FaceRingSimple.face_ring_simple` re-proved with the satisfiable predicate `[exact]` | 3 |
| `FaceTwinAware.v : extract_faces_valid_twin_aware` (+ `extract_faces_holes_valid_twin_aware`, `face_polygon_holes_valid_twin_aware`) | **Twin-aware extractor headlines:** both extractors' validity theorems restated over the satisfiable H1 plus per-face `face_twin_free` — the relocated, now-dischargeable bridge targets for `extract_rings_valid` `[cond]` | 3 |
| `FaceTwinAware.v : spur_breaks_face_twin_free` | A spur step (`fstep D x = twin x`, degree-1 tip) breaks face twin-freeness — the easy half of the antenna correction: `fan_ok` + `no_short_faces` alone do NOT give twin-freeness `[exact]` | 3 |
| `NodedGeneralPosition.v : noncollinear_share_no_proper` | **The geometric step (corrected-plan step 3):** two segments sharing an endpoint with non-parallel directions (`seg_dir_cross <> 0`) CANNOT properly cross — the four-case substitution that `a*u = c*v`, `a > 0`, `u x v <> 0` is absurd `[exact]` | 3 |
| `NodedGeneralPosition.v : noded_gp_twin_aware` (+ `noded_general_position`, `noded_gp_pairwise`) | **General position closes the bridge interface:** the no-collinear-overlap strengthening of `fully_intersected` yields undirected `pairwise_no_proper_cross`, hence (through rung 1's `darts_of_twin_aware`) the twin-aware H1 of the extractor headlines `[exact]` | 3 |
| `NodedGeneralPosition.v : collinear_pair_not_gp` | Honesty: slice 3i's collinear counterexample pair `(0,0)-(2,0)` / `(0,0)-(1,0)` genuinely fails `noded_general_position` (zero direction cross) — the strengthening excludes exactly the admitted degeneracy `[exact]` | 3 |
| `VertexGeneralPosition.v : fan_ok_of_vertex_gp` (+ `seg_dir_cross_eq_vcross_ddir`, `well_noded_fan_ok`) | **H2 from vertex general position (corrected-plan step 4a):** `seg_dir_cross = vcross∘ddir` bridges step (3)'s vocabulary to `fan_ok`'s; distinct survivors sharing an endpoint with non-parallel directions give `fan_ok (outgoing v D)` at every vertex (plus properness) `[exact]` | 3 |
| `VertexGeneralPosition.v : straight_through_not_fan_ok` (+ `straight_through_noded_gp`) | **Why H2 needs more than H1's input:** two anti-parallel collinear edges at a vertex satisfy `noded_general_position` (they don't properly cross) yet break `fan_ok` — the vertex condition is genuinely additional, not derivable from step (3) `[exact]` | 3 |
| `VertexGeneralPosition.v : well_noded_darts` (+ `well_noded_twin_aware`) | The combined bridge precondition: edge-level general position (H1 via step 3) ∧ vertex general position ∧ properness (H2) — packages both discharged hypotheses of the twin-aware extractor headlines `[exact]` | 3 |
| `NoShortFaces.v : no_short_faces_of_proper_nospur` (+ `period2_imp_spur`, `dbase_fstep`) | **H3 from properness + no-spurs (corrected-plan step 4b):** `face_period ≥ 3` since period 1 forces a degenerate dart and period 2 is exactly a twin-pair spur (`fstep d = twin d`) — `no_short_faces` reduces precisely to no-spurs, strictly weaker than `face_twin_free` `[exact]` | 3 |
| `NoShortFaces.v : extract_faces_valid_well_noded` | **Bridge capstone:** `well_noded_darts` + `no_spurs` discharge H1 (twin-aware), H2 (`fan_ok`) and H3, leaving ONLY the per-face `face_twin_free` hypothesis of `extract_faces_valid_twin_aware` open — the precise residual of the `extract_rings_valid` bridge `[cond]` | 3 |
| `ExtractHolesWellNoded.v : extract_faces_holes_valid_well_noded` | **Bridge capstone, with-holes:** same discharge for the with-holes extractor — H1/H2/H3 from `well_noded_darts` + `no_spurs`, oracle clauses pass through, residual is the identical per-face `face_twin_free`; both extractors now reduce to one gap `[cond]` | 3 |
| `FaceOrbitSep.v : same_face_sym` (+ `same_face_refl`, `_trans`, `iter_period_mult`, `dart_walk_iter_iff`) | **Face reachability is an equivalence:** `same_face D a b := ∃k, iter (fstep D) k a = b` is reflexive/transitive, and symmetric on `D` under `arrangement_ok` (via the finite-permutation return `face_orbit_finite`, no injectivity needed) `[exact]` | 3 |
| `FaceOrbitSep.v : face_twin_free_of_sep` (+ `walk_at_period_iff_same_face`, `twins_in_different_faces`) | **Per-face → global reduction:** the period walk enumerates the orbit, so per-face `face_twin_free` (all faces) follows from one global condition `twins_in_different_faces` (no dart shares a face-orbit with its twin) `[exact]` | 3 |
| `FaceOrbitSep.v : extract_faces_valid_sep` (+ `extract_faces_holes_valid_sep`) | **Capstones over one hypothesis:** both extractors validated from `well_noded_darts` + `no_spurs` + `twins_in_different_faces` — the per-face quantifier collapsed to a single global orbit condition (= no cut edge); the 2-edge-connected derivation of it is carried as the named hypothesis H_bridge of `OverlayBridge.extract_rings_valid` `[cond]` | 3 |
| `EdgeConnectivity.v : reach_sym` (+ `reach_trans`, `reachable_nil`, `adj`) | **Graph-connectivity layer (face_twin_free rung 2):** undirected vertex reachability over an edge list is an equivalence (refl/sym/trans) — the vocabulary the no-cut-edge headline needs (none existed in the corpus) `[exact]` | 3 |
| `EdgeConnectivity.v : single_edge_is_cut` (+ `triangle_2_connected`, `is_cut_edge`, `edge_2_connected`) | **Cut-edge / 2-edge-connected, non-vacuous both ways:** a lone proper edge is a cut edge; a triangle is 2-edge-connected. The orbit-linking theorem `edge_2_connected ⟹ twins_in_different_faces` is the documented deferred deep rung `[exact]` | 3 |
| `OverlayBridge.v : extract_rings_valid` (+ `extract_rings_valid_holes`, `valid_geometry_extract`) | **CLOSED conditional headline (was the last deferred-proof Admitted):** every polygon emitted by `extract_faces` on the noded labelled graph is `valid_polygon`, from `well_noded_darts` + `no_spurs` + `edge_2_connected` and ONE named hypothesis H_bridge (`∀E, edge_2_connected E → twins_in_different_faces (darts_of E)`, the rotation-system bridge characterisation). No longer Admitted; off the registry. Qed via `extract_faces_valid_sep` `[cond]` | 4 |
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
| `TriangleValidPolygon.v : triangle_with_hole_valid` (+ `gtri_ring_simple`) | **First with-holes `valid_polygon`, UNCONDITIONAL (no JCT).** The triangle-in-triangle polygon — outer `(0,0),(6,0),(0,6)`, hole `(1,1),(3,1),(1,3)` — satisfies all of `Overlay.valid_polygon`: outer + hole each `ring_closed` / `ring_simple` / `ring_has_minimum_points`, and the hole `hole_inside_outer` the outer. The only analytic clause (`hole_inside_outer`, the polygonal-JCT residual that gated `extract_rings_valid`'s with-holes case) is discharged by `hole_inside_outer_triangle` with **no named hypothesis**. `gtri_ring_simple` (a non-degenerate triangle ring is simple — every edge pair shares a vertex, via `KakeyaOverlay.sip_shared_no_cross`) is the reusable `gtri_ring` analogue of `perron_tri_ring_simple` `[exact]` | 3 |
| `KakeyaPerron_b64.v : perron_tri_b64_orient_exact` (+ `perron_b64_inputs_int_safe`, `perron_tri_b64_cross_positive`) | **Perron binary64 soundness (stage ≤ 24):** the scaled stage-n Perron triangles are `coord_int_safe`, so `b64_orient2d` is bit-exact and the sliver orientation (cross = 2^(n+2) > 0) is computed correctly — however thin the area 1/2ⁿ `[b64]` | 4 |
| `KakeyaPerron_b64.v : perron_b64_apex_unsafe_at_25` | **The soundness diameter brink:** at stage 25 the scaled apex y-coordinate 2^26 leaves the 2^25 `coord_int_safe` window — the first unsafe stage (a float-window fact, not an exact-ℝ crossing; see docs/kakeya-soundness.md) `[b64]` | 4 |
| `HatMonotileInterior.v : hat_point_in_ring` (+ `hat_hole_inside_outer`) | **The "hat" einstein, via ray parity.** The corpus's `point_in_ring` crossing-number test applied to the *actual* (NON-CONVEX) aperiodic monotile (`HatMonotile.hat_ring`, 13-gon, exact `sqrt 3` coords): the witness `(17/4, 5·√3/4)` in the hat's top bump has crossing-number **1** (only the right bump edge `(4,2)→(3,3)` is crossed; the other 12 edges sit at/below height `√3 < py p`, or to the left) ⇒ odd ⇒ inside. `hat_hole_inside_outer` nests a hole. Demonstrates the ray-parity interior holds for non-convex rings; **not** the JCT topological-interior equivalence (that's the polygonal-JCT residual) `[exact]` | 3 |
| `GeneralTriangleHoleNesting.v : hole_inside_outer_triangle` (+ `gtri_band_in_ring`) | **GREEN — arbitrary-triangle hole nesting, UNCONDITIONAL (no JCT).** The corrected, TRUE parity direction: for an interior-side point (`0 < gtri p`, all three inward slacks positive) whose `py` lies in one of the three **directed height bands** (`ay<py<by_ ∨ by_<py<cy ∨ cy<py<ay`), `point_in_ring p (gtri_ring …)` holds — `edge_cross_sign` collapses each edge's ray-crossing to its band (the opposite slack-disjunct is dead under `0<slack`), the bands are disjoint, so exactly one edge crosses ⇒ odd parity. Composes (`gtri_band_in_ring` + `In p hole`) to `hole_inside_outer_triangle`, the triangle analogue of `HoleInsideOuterRect.hole_inside_outer_rect` — the directed band plays the role of the rectangle's explicit `y0<py<y1`. Chips the `hole_inside_outer` polygonal-JCT residual of `extract_rings_valid` `[exact]` | 3 |
| `JCTNesting.v : valid_polygon_rect_outer` (+ `rect_ring_simple`) | **hole_inside_outer made usable:** a rectangular-outer polygon whose holes each have an interior vertex is `valid_polygon` unconditionally — reuses the Stage-B rect witness via `polygon_valid_of_rings`, discharging the conditional extractor's `hole_inside_outer` nesting obligation for box outers (no JCT). Proves the missing `rect_ring_simple` `[exact]` | 3 |
| `HatNesting.v : hat_inside_bounding_box` | **Einstein monotile nesting witness:** the "hat" aperiodic monotile (`HatMonotile.hat_ring`, a non-convex 13-gon) nests inside its bounding rectangle — `hole_inside_outer (rect_ring 0 0 7 3) hat_ring` via the Stage-B rect witness and a parity-interior hat vertex; no JCT, no `ring_simple`. Full `valid_polygon` for the hat is now in `HatValidPolygon.v` (`ring_simple hat_ring` closed) `[exact]` | 3 |
| `HatValidPolygon.v : hat_ring_simple` | **The hat is a simple ring (Qed):** no two edges of the non-convex 13-gon cross at an interior point — closes the ~78-pair case-bash the corpus deferred for Spectre/hat (the crossing system is linear in the segment parameters; `nra` + `sqrt 3·sqrt 3 = 3` discharges every pair, ~2 s) `[exact]` | 3 |
| `HatValidPolygon.v : valid_polygon_hat` (+ `valid_polygon_box_with_hat_hole`) | **The einstein monotile is a `valid_polygon`:** the hat alone is valid; and a rectangle with the hat punched out as a hole is valid via `JCTNesting.valid_polygon_rect_outer` — the famous aperiodic tile, fully verified in the corpus's polygon API `[exact]` | 3 |
| `HatPatch.v : ring_simple_translate` (+ `x_separated_no_cross`, `ring_edges_translate`) | **Reusable patch lemmas:** `ring_simple` is invariant under translation; rings in disjoint x-bands cannot properly cross — the tools for assembling multi-tile patches `[exact]` | 3 |
| `HatPatch.v : hat_patch_all_valid` (+ `hat_patch_non_crossing`) | **Finite hat patch witness:** a concrete two-hat patch (second placed by translation) is a list of `valid_polygon`s whose edge union is `pairwise_no_proper_cross` — a genuine multi-tile einstein patch (no substitution machinery). The 'growing-supertile brink' is ill-posed in exact ℝ; see docs/hat-soundness.md `[exact]` | 3 |
| `GeneralTriangleParityRED.v : gtri_parity_spec_false` | **RED — the queued arbitrary-triangle parity target is FALSE as stated.** `GeneralTriangleParity.gtri_parity_spec` asserts `point_in_ring p ↔ 0 < gtri p` (strict interior) for all `p`; the witness `(0,2)` on the left edge of triangle `(0,0),(4,0),(0,4)` has `point_in_ring` **true** (the rightward-ray test is **half-open** — left edge included, exactly as `RectangleJCT.point_in_ring_rect_iff`'s `x0 ≤ px`) yet `gtri = 0` (on the edge, not strictly inside). Corrects the target to the half-open characterisation / the guarded strict-interior direction `0<gtri ∧ ray_avoids_vertices ⇒ point_in_ring` (→ `hole_inside_outer_triangle`, the next GREEN for the `hole_inside_outer` residual) `[exact]` | 3 |
| `GeneralTriangleJCT.v : gtri_interior_in_ring` (+ `gtri_ray_coverage`) | **The band hypothesis of `gtri_band_in_ring`, discharged:** `0 < gtri p` (orientation *derived*, not assumed) plus the `ray_avoids_vertices` guard already places `py p` in one of the three directed bands — coverage by a 27-branch trichotomy, with grazed-vertex cases forced strictly west by the guard (necessary at the middle-vertex height, cf. `JCT_VertexGrazingCounterexample.v`) and the off-scale cases killed by the barycentric height identity — so `point_in_ring p` needs interior positivity and genericity only `[exact]` | 3 |
| `GeneralTriangleJCT.v : general_triangle_parity_characterises_interior` | For guarded strict-interior points of an arbitrary triangle, `point_in_ring ↔ geometric_interior_cont` — the **third fully Qed-closed family** (after the rectangle and the right triangle) instantiating the H1 parity seam at strict-interior scope `[exact]` | 3 |
| `GeneralTriangleJCT.v : hole_inside_outer_triangle_guarded` (+ `_generic`) | Hole nesting with **no band bookkeeping**: a hole vertex strictly inside an arbitrary triangle, under the guard — or simply three height disequalities (`_generic`) — lies `hole_inside_outer`; closes the "assembly TODO" of Stage D (triangle) in `docs/hole-inside-outer-plan.md` `[exact]` | 3 |
| `JCT_OnEdgeCounterexample.v : parity_seam_strict_refuted_on_edge` | **RED — the H1 seam itself is FALSE as stated:** `JCT.parity_characterises_interior_cont_strict` fails at ON-EDGE points — the generic-position guards do not exclude the ring skeleton, where the ray test is half-open (the `gtri_parity_spec_false` phenomenon, one level up). Witness: triangle `(0,0),(4,1),(1,3)` (no horizontal edge) and the midpoint `(1/2,3/2)` of edge `C–A`: `point_in_ring` **true** (edge `B–C` crossed once), `geometric_interior_cont` **false** (on the skeleton), and *all five premises Qed* (incl. `ring_simple`, `ray_avoids_vertices` — `3/2 ∉ {0,1,3}`). Corrects H1 to `parity_characterises_interior_cont_offring` (adds `ring_complement r p`), with the conditional headline re-wired (`point_in_ring_correct_jct_cont_offring`). The three closed strict-interior families are unaffected (strict interior ⇒ off-ring). See `docs/jct-on-edge-counterexample.md` `[exact]` | 3 |
| `RectangleOffringSeam.v : escape_beyond_x_low` (+ `_x_high`, `_y_low`, `_y_high`) | **Generic exterior-escape engine:** for ANY ring whose skeleton is bounded on one side, a point strictly beyond that bound is in NO bounded complement component — a straight axis-aligned ray of length `M+\|coord\|+1` escapes every radius `M` without meeting the skeleton (`straight_path_continuous`). The reusable half every family's exterior direction needs `[exact]` | 3 |
| `RectangleOffringSeam.v : rect_parity_seam_offring` (+ `rect_point_in_ring_iff_geometric`) | **The corrected H1 seam, discharged TOTALLY for the rectangle — the first family instance of the seam Prop itself.** For every rectangle and every point, `parity_characterises_interior_cont_offring` is a theorem: by `box_min` trichotomy — `>0` the existing strict-interior result; `=0` impossible off-ring (`box_min_nonzero_off_skeleton`); `<0` both sides false (`rect_exterior_not_in_ring` for parity, the escape engine for boundedness). Shows the on-edge RED's re-scoped seam is *satisfiable*, not just unrefuted; upgrades the rectangle from "strict-interior projection" to the full off-ring biconditional `[exact]` | 3 |
| `GeneralTriangleExterior.v : escape_beyond_halfplane` | **The half-plane escape engine** — generic over any ring: if the skeleton satisfies `a·x + b·y ≤ c` and `p` is strictly beyond (`(a,b) ≠ 0`), then `p` is in NO bounded complement component. The outward-normal ray escapes every radius `M`, with the radius defeat done **square-root-free** via the Cauchy–Schwarz polynomial identity (`(aX+bY)² ≤ (a²+b²)(X²+Y²)`, defect `(aY−bX)²`). Strictly generalises the axis-aligned escapes (a triangle's exterior points can sit inside the vertex bounding box) `[exact]` | 3 |
| `GeneralTriangleExterior.v : gtri_exterior_escapes` (+ `gtri_image_slacks_nonneg`) | **The triangle's exterior-escape half:** `gtri p < 0` (some inward slack negative) puts `p` strictly beyond that edge's half-plane while the whole skeleton lies inside it (each slack is affine along an edge with endpoint values `0`/`gdbl`), so `p` escapes. Edge nondegeneracy is derived from `0 < gdbl` by Cauchy–Schwarz, not assumed `[exact]` | 3 |
| `GeneralTriangleExterior.v : gtri_geometric_imp_in_ring` (+ `gtri_parity_seam_offring_of_exterior_parity`) | **The TOTAL geometric⇒parity direction for the triangle** (trichotomy: exterior escapes, skeleton excluded off-ring, interior is the closed family), and the triangle's **total off-ring seam conditional on exactly one residual**: exterior even parity (`gtri p < 0 ⇒ ¬point_in_ring p`) — the named target of the next rung `[cond]` | 3 |
| `GeneralTriangleOffringSeam.v : gtri_exterior_even_parity` | **The residual, closed:** exterior points of a CCW triangle have **even** ray parity, under the `ray_avoids_vertices` guard (necessary — an exterior ray grazing a vertex miscounts, e.g. `(-1,2)` for triangle `(0,0),(2,2),(0,4)`). `rpo3_cases` inverts odd parity into the four odd crossing-subsets; the triple is killed by the pairwise-incompatible directed straddles, each singleton by trichotomy on the opposite vertex's height — grazed-vertex-west slack factorisations at the vertex height, the slack-sum identity (`g_sum`) and the barycentric height identity elsewhere `[exact]` | 3 |
| `GeneralTriangleOffringSeam.v : gtri_parity_seam_offring` | **The corrected off-ring H1 seam, discharged TOTALLY for every CCW triangle — the second total family, the first with sloped edges.** For every triangle with `0 < gdbl` and every point, `parity_characterises_interior_cont_offring p (gtri_ring …)` is a theorem (the conditional assembly of `GeneralTriangleExterior.v` with its exterior-parity hypothesis now discharged). Total-family ladder: rectangle ✓, triangle ✓; next: convex n-gons `[exact]` | 3 |
| `ConvexOffringSeam.v : image_slack_nonneg` (+ `ring_edges_endpoints_in`, `conv_min_neg_inv`, `convex_exterior_escapes`) | **The generic convex layer:** for ANY ring, if every *vertex* satisfies a half-plane then the whole *skeleton* does (edge points are convex combinations of vertices, slacks are affine — the n-gon induction); a negative `conv_min` names a violated half-plane; and a point strictly beyond a vertex-satisfied half-plane escapes. The convexity hypothesis is the GLOBAL `vertices_in_halfplane` form — the local all-CCW-turns form is refuted by the pentagram (locally convex, not an intersection of half-planes) `[exact]` | 3 |
| `ConvexOffringSeam.v : convex_parity_seam_offring_of` | **The convex assembly:** for any half-plane-presented ring, the total off-ring seam follows from exactly four named family obligations — zero-set of `conv_min` on the skeleton, bounded positive region, guarded interior-odd and exterior-even parity. All topology (escape, separation, trichotomy) is discharged once, here; future convex n-gon families supply only the four facts `[cond]` | 3 |
| `ConvexOffringSeam.v : rtri_parity_seam_offring` | **The THIRD total family, free:** `rtri_ring x0 y0 x1 y1` is definitionally `gtri_ring x0 y0 x1 y0 x0 y1`, so the triangle's total seam specialises to every axis-aligned right triangle in one line `[exact]` | 3 |
| `JCTParityTransport.v : point_in_ring_dec` (+ `ray_parity_dec`, `ray_parity_excl`, `edge_crosses_ray_dec`) | **The crossing-number parity is decidable and total:** every edge list is decidably odd-or-even and never both — the strict ray test is a genuine boolean-style classifier, with no new axioms `[exact]` | 3 |
| `JCTParityTransport.v : invariant_transport_along_path` | **The transport engine (H1 proper, part 1):** a pointwise-decidable predicate that is locally stable along a path is constant along it. Pure completeness-of-ℝ (least-upper-bound) argument — decidability of the predicate replaces the classical choice the textbook clopen proof hides, keeping the 3-axiom budget `[exact]` | 3 |
| `JCTParityTransport.v : odd_parity_trapped_of_invariant` (+ `invariant_traps`, `parity_invariant_for`) | **H1's hard "trapped" half, reduced to ONE kernel — for ANY ring:** given an invariant `Q` that is decidable, locally constant along complement paths, false beyond some radius, and agreeing with `point_in_ring` at `p`, an odd-parity `p` lies in a bounded complement component. The remaining kernel is *constructing* `Q` for a general simple ring: the intended candidate is the **half-open** ray parity, since the strict parity is provably NOT locally constant (a far-west point's strict count jumps at a pass-through-vertex height) `[cond]` | 3 |
| `JCTParityTransport.v : rect_trapped_via_invariant` (+ `rect_parity_invariant`, `pos_stable_at`, `neg_stable_at`) | **The reduction is non-vacuous:** the rectangle instantiates it with `Q := 0 < box_min` — local constancy is the sign stability of a continuous complement-nonvanishing field, far-falsity is the box bound — re-deriving the rectangle's trapping through the generic engine `[exact]` | 3 |
| `JCTHalfOpenParity.v : point_in_ring_ho_agrees` (+ `edge_crosses_ray_ho`, `point_in_ring_ho_dec`, `ho_parity_excl`) | **The half-open ray parity** (edge counts when `vy ≤ h < wy` — bottom endpoint included): decidable, never-both, and **agreeing with the strict parity under `ray_avoids_vertices` alone** — the conventions differ only when `p`'s height equals a bottom-endpoint height, where the half-open crossing point *is* that vertex: excluded east of `p` by the guard, irrelevant west `[exact]` | 3 |
| `JCTHalfOpenParity.v : ho_far_west_even` (+ `ho_cross_far_west_iff`, `ho_walk_parity`, `ho_far_false`) | **Far-field evenness in all four directions** — right/up/down because no edge can cross; **west by the cyclic walk argument**: far west of every vertex an edge crosses iff its endpoints' below-flags differ, and around a CLOSED walk the flag returns to its start, so the flips are even. This is where the ring's closedness genuinely enters the JCT story; combined: half-open parity is false beyond an explicit radius `[exact]` | 3 |
| `JCTHalfOpenParity.v : odd_parity_trapped_of_ho_kernel` | **H1's trapped half, reduced to ONE concrete named kernel:** for any closed ring and `ray_avoids_vertices`-guarded odd-parity point, `in_bounded_component_cont` follows from `ho_parity_locally_constant r` — local constancy of the half-open parity along complement paths (the y-monotone vertex-pairing content of the polygonal JCT). Everything else in the trapped half is Qed `[cond]` | 3 |
| `JCTGenericStability.v : ho_generic_stable` (+ `affine_sign_stable`, `ho_asc_iff`/`ho_desc_iff`, `ho_cross_stable_generic`, `ho_parity_ball`) | **Generic-height local constancy, Qed:** at a complement point whose height differs from every vertex height, each edge's half-open crossing is a conjunction of STRICT affine signs (the division-free ray atom `PA`/`PD` is nonzero in-band, else the point is ON the edge), each stable on an explicit ball; a finite `Rmin` over the edge list yields a parity-constant ball `[exact]` | 3 |
| `JCTGenericStability.v : ho_kernel_of_level_stable` (+ `odd_parity_trapped_of_level_stable`, `path_coord_close`, `vertex_at_level_dec`) | **The kernel shrinks to vertex-level points:** the full `ho_parity_locally_constant` follows from `ho_level_stable` — local constancy at VERTEX-LEVEL complement points only, the y-monotone vertex-pairing content in its purest form. Capstone: H1's trapped half for any closed ring now needs ONLY `ho_level_stable` `[cond]` | 3 |
| `JCTLevelJump.v : ho_upper_stable` (+ `ho_cross_stable_upper`, `ho_parity_ball_upper`) | **Upper half-ball constancy at EVERY complement point, Qed — no genericity, no pairing:** the bottom-inclusive band `vy ≤ h < wy` makes the half-open parity equal its limit *from above*; per edge there are only four upper-regimes (dead-above, unreached, live-ascending, live-descending), and the live ray atoms are nonzero with the `t = 0` on-edge witness allowed `[exact]` | 3 |
| `JCTLevelJump.v : odd_parity_trapped_of_level_jump` (+ `ho_level_jump`, `ho_level_stable_of_jump`) | **The kernel shrinks to the pure downward level jump:** at a vertex-level complement point, parity *just below* the level equals parity *at* it — the east level-vertices' band-handover count, isolated on one side of one line. H1's trapped half for any closed ring now follows from that single statement `[cond]` | 3 |
| `JCTTrappedHalf.v : ho_cross_lower_flag` (+ `eastlevel`, `ho_lower_eps_all`) | **The per-edge jump law:** for a complement point `q` at a level and `q'` just below it, every edge satisfies `(cross q' ↔ cross q) ↔ (F(fst e) ↔ F(snd e))` where `F(v) := (py v = level ∧ px q < px v)` is the east-level flag — nine cases; the horizontal level edge has both endpoints on one side of `q` (else `q` is on it) `[exact]` | 3 |
| `JCTTrappedHalf.v : ho_level_jump_holds` (+ `ho_jump_walk`, `ho_jump_closed`) | **The part-4 kernel is a THEOREM:** the downward jump telescopes around the closed walk — the flag returns to its start, so the total flip is zero, exactly the far-west lemma's shape. `ho_level_jump` holds for every closed ring `[exact]` | 3 |
| `JCTTrappedHalf.v : odd_parity_trapped` | **THE TRAPPED HALF OF THE POLYGONAL JORDAN CURVE THEOREM, Qed and UNCONDITIONAL:** for ANY closed ring, a `ray_avoids_vertices`-guarded point with odd crossing parity lies in a bounded complement component. `ring_simple` is not needed. The load-bearing half of H1 — graded "multi-month, no reachable library" in the audit — is now a theorem of the corpus at the standard three axioms `[exact]` | 3 |
| `JCTSeamAssembly.v : point_in_ring_imp_geometric_cont` (+ `ho_parity_locally_constant_holds`) | **The H1 seam's hard direction, unconditional:** for every closed ring, a guarded off-ring point with odd parity is `geometric_interior_cont` — and the part-3/4/5 kernel chain is composed and named: the half-open parity is locally constant along complement paths of ANY closed ring `[exact]` | 3 |
| `JCTSeamAssembly.v : parity_seam_offring_of_escape` (+ `even_parity_escapes`, `point_in_ring_correct_of_escape`) | **H1, reduced to its final residual:** the full corrected seam `parity_characterises_interior_cont_offring` follows from the per-point escape `even_parity_escapes` (`¬point_in_ring ⇒ ¬in_bounded_component_cont`) — the only ingredient that needs `ring_simple` (a doubly-wound ring has even-parity trapped points). The parity side of the biconditional is decided by `point_in_ring_dec`, so no classical step is added. Rectangle sanity instance discharges the residual concretely `[cond]` | 3 |
| `JCTEscapeDescent.v : escape_east_of_zero_count` (+ `ho_count`, `ho_count_parity`, `ho_zero_count_ray_free`) | **The escape base case, Qed:** with zero half-open crossings and the ray guard, the open eastward ray is literally *skeleton-free* — a strict straddle east would be a counted crossing, and edge points at the ray's height are otherwise vertices or on horizontal level edges, both banished east of `p` by the guard — so the straight eastward ray escapes every radius `[exact]` | 3 |
| `JCTEscapeDescent.v : escape_of_descent` (+ `escape_descent`, `parity_seam_offring_of_descent`) | **The escape half reduced to ONE DESCENT STEP:** strong induction on the crossing count, riding the Qed component invariance — the residual `escape_descent` (from an even-parity guarded point with a crossing, reach a guarded point with strictly fewer crossings through the complement; one detour around the first blocking edge, the only place `ring_simple` lives) yields the **full corrected H1 seam** for every point `[cond]` | 3 |
| `JCTSeparation.v : parity_constant_on_components` | **Parity is constant on complement components:** guarded endpoints of any complement path of any closed ring have equal strict crossing parity — the transport engine run on the half-open kernel, with guard agreement at both ends `[exact]` | 3 |
| `JCTSeparation.v : odd_even_separated` (+ `geometric_interior_even_separated`) | **THE SEPARATION CLAUSE OF THE JORDAN CURVE THEOREM, unconditional:** an odd-parity (inside) point and an even-parity (outside) point are NEVER connected within the complement of ANY closed ring — no simplicity needed. This is the separation clause PR #82 added to the `JCT_two_components_cont` *hypothesis*, now a *theorem* `[exact]` | 3 |
| `JCTSeparation.v : rect_even_parity_escapes` (+ `gtri_…`, `rtri_…`) | **The final H1 residual holds on every total family:** rectangle, arbitrary CCW triangle, right triangle each discharge `even_parity_escapes` by their field trichotomy (interior parity contradicts evenness; skeleton contradicts the complement; exterior escapes) — the remaining general-simple-ring residual is verified non-vacuous and consistent everywhere the corpus can decide `[exact]` | 3 |
| `JCTEastApproach.v : east_approach` (+ `cross_x`, `min_cross_x`, `east_segment_free`) | **Escape-descent rung 1, the east approach:** the first wall `X1 = min_cross_x` exists and is achieved whenever the crossing count is positive; the run-up `[px p, X1)` at `p`'s height is *skeleton-free*; and every run-up point is complement-connected to `p`, off-ring, guarded, with the **same** `ho_count` — all descent invariants survive the approach `[exact]` | 3 |
| `JCTEastApproach.v : crossings_distinct` (+ `ho_cross_strict_of_guard`) | **`ring_simple`'s first theorem in the H1 campaign:** under the ray guard every half-open crossing is a strict straddle, so two distinct crossing edges cross the ray at **distinct** abscissae — a shared crossing point would be interior to both and hence a proper intersection. The first wall is a single well-defined edge for the corner corridor (rung 2) to walk around `[exact]` | 3 |
| `JCTCorridor.v : corridor_connected` (+ `edge_x_at`, `edge_x_at_affine`, `corridor_free_of_edges`) | **Escape-descent rung 2, the corridor:** the carrier line's abscissa is affine in height, so the corridor at westward offset `delta` is itself a *straight segment* — `straight_path_continuous` carries it through the complement whenever each edge is cleared `[exact]` | 3 |
| `JCTCorridor.v : corridor_avoid_west` (+ `_east`, `_below`, `_above`, `_carrier`, `affine_between`) | **Explicit affine clearances:** every per-edge corridor clearance is an endpoint evaluation — west-by-more-than-delta, strictly east, outside the height window, or the carrier itself at any positive offset. No compactness, no square roots; margins fold by finite `Rmin` `[exact]` | 3 |
| `JCTCorridor.v : guard_of_fresh_level` (+ `level_gap`, `square_corridor`) | **Parking heights:** above any height there is an explicit vertex-level-free gap (finite `Rmin` over the vertex list), so a corridor endpoint parked inside it gets `ray_avoids_vertices` for free. Worked instance: a concrete corridor inside the unit square with all four clearances discharged by the helpers `[exact]` | 3 |
| `JCTWalkKit.v : corridor_avoid_clipped_west` (+ `_east`, `clip_params_asc`/`_desc`) | **Escape-descent rung 3, the mixed clearance:** the three-point affine law `(s1−s0)·F(s) = (s1−s)·F(s0) + (s−s0)·F(s1)` (a `ring` fact) propagates a clearance that beats `delta` at both clip points to the whole window overlap; the clip points themselves come from affine inversion with `Rmax`/`Rmin` clamps. Every edge not touching the carrier inside the window is now clearable by an explicit margin `[exact]` | 3 |
| `JCTWalkKit.v : horizontal_connected` (+ `vertical_connected`) | **Jog connectors:** axis-aligned skeleton-free segments connect corridor pieces through the complement — the glue of rung 4's boundary walk `[exact]` | 3 |
| `JCTWalkStep.v : walk_step` (+ `walk_step_guarded`, `cross_x_is_edge_x_at`, `exists_parked_height`) | **Escape-descent rung 4, the assembled walk step:** the crossing abscissa *is* the carrier line's abscissa at `p`'s height, so the east run-up endpoint and the corridor top coincide exactly; composed by connectivity transitivity, `p` reaches a parked corridor point that is connected, off-ring, and guarded (`exists_parked_height` parks it inside a vertex-level-free gap) — conditional only on the corridor clearances, which rung 5 derives from `ring_simple` touch-freedom `[cond]` | 3 |
| `JCTTautClearance.v : ring_taut` (+ `ring_taut_implies_simple`) | **The walk's simplicity notion:** every meeting point of two ring edges is a shared endpoint — with a pointwise-equal-edges escape hatch that absorbs the undecidable carrier case semantically. Strictly stronger than the corpus `ring_simple`, which deliberately admits T-touches (the figure-8 note in `Overlay.v`); a T-touch on the carrier's west side genuinely blocks every corridor, so tautness is the honest hypothesis `[exact]` | 3 |
| `JCTTautClearance.v : taut_no_line_touch` (+ `affine_root`, `clip_ordered_asc`/`_desc`) | **The sign-orienting consumer:** inside a height window strictly interior to the carrier's span, the carrier's *line* and *segment* coincide — so any edge meeting the line at a window height is the carrier itself (pointwise) or violates tautness. With the constructive affine IVT (explicit `−B/A` root) and well-formed clip points, every clearance sign in the per-edge case tree is decided by endpoint evaluation `[exact]` | 3 |
| `JCTWallClear.v : wall_corridor_clear` (+ `clear_fold`) | **Escape-descent rung 4b-2, THE WALL THEOREM:** for a taut ring and a wall edge spanning a span-interior window, there is a uniform `delta0 > 0` such that the corridor at *every* offset `delta ∈ (0, delta0)` is skeleton-free — exactly the clearance hypothesis `walk_step` (rung 4) consumes. Margins fold by finite `Rmin` over the edge list `[exact]` | 3 |
| `JCTWallClear.v : per_edge_clear` (+ `touch_clearance`) | **The per-edge clearance case tree:** every obstacle edge — ascending, horizontal, or descending; below, above, west, east, or *touching* the carrier in the window — yields an explicit positive clearance. The unifying trick: any touch witness forces the obstacle to *be* the carrier pointwise (`taut_no_line_touch`), and the carrier clears its own corridor at any positive offset (`corridor_avoid_carrier`); sign changes produce touch witnesses via the constructive affine IVT. Every clearance is an affine endpoint evaluation — no compactness, no square roots `[exact]` | 3 |
| `JCTCornerSector.v : corner_sector_guarded` (+ `corner_drop`, `corner_edge_clear`) | **Escape-descent rung 4b-3, the corner sector:** from the wall's corridor at height `py v + ε` the walk rounds the wall's *bottom vertex* `v` by a vertical drop just west of `v`, landing at an off-ring, ray-guarded point strictly *below* the corner level — the point the descent recursion restarts from. `ε` shrinks after `δ`: edges incident to `v` stay within `slope·ε` of `v`, short of the `δ/2` offset; edges missing `v` are cleared by explicit positive margins at `v`'s level. Honest residual hypothesis: no horizontal edge extends west from `v` `[exact]` | 3 |
| `JCTCornerSector.v : taut_vertex_endpoint` (+ `corridor_offset_jog`, `depth_gap`) | **Tautness at a vertex:** any ring edge passing through a vertex of the wall edge has that vertex as a shared *endpoint* — the dichotomy that splits the corner obstacles into slope-bounded incident edges and margin-bounded distant ones. Plus the glue kit: corridors of two different offsets connect horizontally at a shared height (consuming the wall theorem's all-`δ` quantifier), and `depth_gap` parks heights *below* a level inside a vertex-level-free gap, giving the destination's ray guard for free `[exact]` | 3 |
| `JCTCornerClear.v : wall_corridor_clear_corner` (+ `per_edge_clear_corner`, `corridor_avoid_east_weak`) | **Escape-descent rung 5a, the corner-abutting clearance:** under `corner_opens_east` (every edge incident at the wall's bottom vertex `v` reaching weakly above `v`'s level stays weakly *east* of the wall's carrier), the corridor is skeleton-free on the whole half-open window `(py v, yhi]` with **one uniform `δ0`** — dissolving the quantifier deadlock between the wall theorem (window before `δ`) and the corner drop (`ε` after `δ`). Non-incident edges never touch the carrier on `[py v, yhi]`: a corner-level touch is a touch at `v` itself, an interior touch makes the toucher pointwise the wall — both contradict non-incidence under tautness. The hypothesis fails precisely inside a wedge (companion ascending west), which is where interior walkers must stick (`odd_parity_trapped`) `[exact]` | 3 |
| `JCTCornerClear.v : corner_passage` (+ `opens_east_horizontal`) | **The full corner move, composed:** from the wall's corridor at any window height, ride down to the corner band and drop past the bottom vertex — one complement path to an off-ring, ray-guarded point strictly *below* the corner level, with `δ0` uniform and `ε` chosen after `δ`. `corner_opens_east` subsumes rung 4b-3's no-west-horizontal residual (a horizontal edge at `v` has its far endpoint at `v`'s level, where the carrier abscissa is `px v`) `[exact]` | 3 |
| `JCTMirrorKit.v : connected_xmir_rev` (+ `ring_taut_xmir`/`_ymir`, `ring_image_xmir`/`_ymir`, `in_bounded_xmir`/`_ymir`) | **Escape-descent rung 5b, the mirror kit:** the whole complement geometry — skeleton, tautness, closedness, complement connectivity, boundedness — transports through the coordinate reflections `xmir` (east↔west) and `ymir` (over↔under), both ways via involutions. Every west-side, under-bottom corridor/corner theorem of rungs 2–5a now applies verbatim to the mirrored ring and pulls back, giving the boundary-hugging walk its other three orientations for free `[exact]` | 3 |
| `JCTMirrorKit.v : ho_count_ymir` (+ `ho_cross_ymir`, `guard_ymir`, `ho_parity_even_ymir`) | **The y-flip is exact for the crossing data:** the parity ray is horizontal, so `ray_avoids_vertices`, `edge_crosses_ray_ho`, `ho_count`, and the parity transport across `ymir` exactly — under the guard every half-open crossing is a *strict* straddle (`ho_cross_strict_of_guard`), and strictness is y-symmetric; the half-open convention's bottom-endpoint bias cancels. The x-flip reverses the ray and is used for freedom/connectivity only `[exact]` | 3 |
| `JCTTopPassage.v : corner_passage_top` (+ `edge_x_at_ymir`/`_xmir`) | **Escape-descent rung 5c-1, the over-the-top move:** `corner_passage` pulled back through the y-flip — from the wall's west corridor at any span-interior height, over the wall's *top* vertex, to an off-ring, ray-guarded point strictly *above* the top level. This is how the walk backs out of a sealed wedge. The mirrored corner condition reads in original coordinates (`corner_opens_east_top`: incident edges reaching weakly below `u` stay weakly east of the carrier), and the destination's ray guard pulls back exactly thanks to the y-flip's exactness `[exact]` | 3 |
| `JCTTopPassage.v : ho_count_zero_east` (+ `xsup`, `ho_cross_east_none`) | **The traversal's terminal count:** at or east of the ring's east-most vertex abscissa (`xsup`, an explicit `Rmax` fold) the eastward ray crosses *nothing* — every crossing abscissa is a convex combination of endpoint abscissae — so the crossing count is zero, strictly below the walker's even positive count and exactly the precondition of `escape_east_of_zero_count` `[exact]` | 3 |
| `JCTPassageKit.v : corner_passage_east` (+ `corner_passage_east_top`, `corner_passage_fresh`, `corner_passage_top_fresh`) | **Escape-descent rung 5c-2, the four-orientation passage kit:** corner moves west/east of the wall × under-bottom/over-top, with uniform interfaces — one complement path from the side-corridor at any span-interior height, around the corner, to an off-ring point strictly past the corner level. The x-flip cannot transport the eastward ray guard, so the kit exposes *level freshness* instead: destinations are parked inside a `depth_gap` (no ring vertex at that level), and a level-fresh point is guarded in every direction (`ray_guard_of_fresh`). Corner conditions in original coordinates: `corner_opens_east`(`_top`) for west-side moves, `corner_opens_west`(`_top`) for east-side moves `[exact]` | 3 |
| `JCTTipCrossing.v : under_tip_crossing` (+ `under_tip_clear`, `hprobe_avoid_level_crossing`) | **Escape-descent rung 5c-3, the side-switch:** at a *local-minimum* corner (every edge incident at `v` reaches weakly upward) the horizontal band just below `v` is skeleton-free across the whole corner `[px v − 2δ, px v + 2δ]`, so the walk passes from the west side to the east side underneath the tip — connecting the west-side passage destinations (which land in exactly this band) to the east-side corridors; the y-flip crosses *over* a local-maximum tip. Incident edges sit entirely at-or-above the level (no slope bounds needed); non-incident edges get the taut margin at `v`'s level via the horizontal twin of the corner-drop clearance `[exact]` | 3 |
| `JCTCornerBox.v : corner_box_clear` (+ `_east`, `_top`, `_east_top`, `box_connected_of_clear`) | **Escape-descent rung 5c-4, the corner boxes:** the rung 4b-3 per-edge dispatch already clears the *whole* abscissa interval, so its fold yields a skeleton-free **rectangle** beside the corner — `[px v − 2δ, px v − δ/2] × [py v − ε, py v + ε]` — and the mirror kit produces all four (east/west × bottom/top vertex). Any two points of a free rectangle connect by one vertical plus one horizontal segment, so the boxes absorb at once all the corner glue the traversal needs: drops, rejoin jogs onto the next edge's corridor, and transfers between passage destinations and tip crossings `[exact]` | 3 |
| `JCTRingCycle.v : incident_two` (+ `in_edge_unique`, `out_edge_unique`, `ring_edges_in_split`) | **Escape-descent rung 5c-5, the degree-2 structure:** in a proper ring (closed, `NoDup` core) every edge incident at a vertex is *the* in-edge or *the* out-edge — edge membership is list splitting (axiom-free), each vertex has at most one incoming and one outgoing edge (`count_occ` on the unique core occurrence; the seam vertex's in-edge ends at the closing copy, its out-edge starts at the head). This discharges the corner conditions' "for all incident edges" against the two cycle neighbours `[exact]` | 3 |
| `JCTRingCycle.v : cyclic_next` (+ `cyclic_prev`, `vertex_xmax_achieved`, `ho_count_zero_east_ub`) | **The cycle wrap and the sharpened terminal:** every edge of a closed ring has a cycle successor and predecessor (closedness wraps the seam — both axiom-free), a maximal-abscissa vertex exists, and any point weakly east of *every* vertex has crossing count zero (the `xsup`-free terminal count) `[exact]` | 3 |
| `JCTHugStep.v : hug_step_pass_down_west` (+ `hugs_west`, `wall_corridor_clear_corner_top`, `apex_abscissa_bound`) | **Escape-descent rung 5c-6, the first corner composite:** the traversal state `hugs_west` anchors connectivity at the edge's *span midpoint* (the δ-free canonical height that kills the parameter-threading circularity) with all-smaller-offsets freedom, and the composite step carries it through a degree-2 downward pass-through corner: offset jog ∘ corner passage ∘ corner-box transfer (both transfer abscissae pinned by the drop/apex bounds) ∘ top-abutting ride to the next midpoint. The corner conditions are *discharged*, not assumed — at a degree-2 corner the only incident edges are the wall (own carrier, equalities) and the continuation (far endpoint below the level, vacuous), via `incident_two`. Only tautness, the proper ring, and no-horizontal-edges remain as inputs `[exact]` | 3 |
| `JCTHugMirror.v : hug_step_pass_up_west` (+ `hug_step_pass_down_east`, `hug_step_pass_up_east`, `hugs_east`) | **Escape-descent rung 5c-7, the mirrored hug steps:** the hug state transports through the reflections — the west midpoint corridor of a y-mirrored edge *is* the y-mirror of the west midpoint corridor, and the x-mirror swaps west into *east* corridors (`hugs_east`) — so the three remaining pass-through composites (west ascending, east descending, east ascending) follow from the 5c-6 composite by transport rather than re-proof, with the ring-side hypotheses (tautness, proper ring via injective-map `NoDup`, no-horizontal) carried along `[exact]` | 3 |
| `JCTMinOpenStep.v : hug_step_min_open_we` (+ `incident_pair_min`, `wall_corridor_clear_corner_east`, `corridor_connected_east`, `foot_abscissa_bound`) | **Escape-descent rung 5c-8, the open-side turnaround:** at a local-minimum corner the boundary reverses, and the walker on the open side rounds the tip — passage down the west flank, under-tip crossing beneath the corner, east corner box, and the east corner-abutting rise to the next midpoint — flipping the hug side (`hugs_west e → hugs_east f`) exactly as right-of-travel demands. The open-side conditions are two decidable carrier-line comparisons; the east-side corridor machinery arrives by x-flip pullback of rungs 2, 4b-2, and 5a `[exact]` | 3 |
| `JCTMinOpenMirror.v : hug_step_max_open_we` (+ `hug_step_min_open_ew`, `hug_step_max_open_ew`) | **Escape-descent rung 5c-9, the mirrored turnarounds:** the open-side composite transported through the reflections — the x-flip swaps hug sides *and* carrier conditions, the y-flip turns minima into maxima keeping both — completing the **open-side corner inventory**: all four pass-throughs and all four open extremum turnarounds Qed. Only the pinched-side turnaround remains before the cycle recursion `[exact]` | 3 |
| `JCTCornerDisk.v : corner_disk_clear` (+ `disk_edge_clear`) | **Escape-descent rung 5c-10, the corner disk:** every edge *not* incident at a vertex `v` misses a fixed square neighbourhood of `v` — the pinched turnaround's last clearance. Away from the corner the wedge interior may contain nested spiral arms, so the cross-wedge jog must happen inside the taut margins around `v`, where the incident edges clear pointwise and everything else clears by this disk; the level-crossing margin `|X − px v| = m > 0` comes from `taut_vertex_endpoint`, and the rectangle probe of rung 5c-3 finishes with `δ = ε =` radius `[exact]` | 3 |
| `JCTPinchedStep.v : hug_step_min_pinched_we` | **Escape-descent rung 5c-11, the pinched turnaround:** when the departing edge climbs strictly *west* of the arriving edge, the west-side walker is inside the closing wedge — it descends to the fixed band height, jogs *across* the wedge interior (incident edges clear pointwise by the carrier identity, everything else by the corner disk), and ascends the other wall's east side. The wedge width is affine with root at the corner (`width = (KE − KF)(y − py c)`, `KE > KF` from the strict pinch), so the band height is fixed *before* `δ` and the jog has room — no quantifier circularity. The last corner move: the walk can now round every degree-2 corner of a taut, proper, horizontal-free ring on either side `[exact]` | 3 |
| `JCTPinchedMirror.v : carrier_side_equiv` (+ `hug_step_min_pinched_ew`, `hug_step_max_pinched_we`, `hug_step_max_pinched_ew`) | **Escape-descent rung 5c-12, the bridge and the last mirrors:** at an extremum corner the two carrier-side conditions are *equivalent* — both express the single slope comparison `KE ≷ KF` through the shared corner (stated for minima and maxima at once via the same-side product) — so the per-corner dispatcher decides open vs pinched with one `Rle_dec` and derives the partner condition from the bridge. With the three pinched mirrors, the **full corner-move inventory** (4 pass-throughs + 4 open + 4 pinched turnarounds) is Qed `[exact]` | 3 |
| `JCTCornerDispatch.v : hug_step_corner` (+ `corner_slopes_distinct`, `interior_param`, `hugs`) | **Escape-descent rung 5c-13, the traversal engine:** the combined state `hugs := hugs_west ∨ hugs_east` advances through *any* degree-2 corner of a taut, proper, horizontal-free ring — corner type read off the height signs, pass-throughs keeping the hug side, extrema flipping it with one `Rle_dec` deciding open vs pinched. The pinched branch is strictified by `corner_slopes_distinct`: under tautness two distinct edges through a shared corner are never collinear, since collinearity would produce a parameter-interior meeting (`interior_param`). The cycle recursion just iterates this along `cyclic_next` `[exact]` | 3 |
| `JCTHugCycle.v : hugs_everywhere` (+ `hugs_chain`, `hug_entry`) | **Escape-descent rung 5c-14, the cycle walk and the entry:** once the walker hugs *any* edge it hugs *every* edge — plain list induction along the ring's chain with one seam-wrapping corner step, no orbit combinatorics. And the walk starts where the descent stands: the rung-1 east approach lands exactly on the first wall's west corridor at the walker's own height, and the span-interior corridor rides to the midpoint — `hugs_west` of the first wall, anchored at the walker itself `[exact]` | 3 |
| `JCTEdgeCount.v : ho_count_one_in` (+ `in_edge_count_le1`, `in_edge_prefix_unique`, `ring_edges_split_pos`) | **Escape-descent rung 5c-15, edge-entry counting:** `ho_count` folds over the edge *list*, so "exactly one crossing edge" needs the crossing pair to occur once as an entry. In a proper ring it does: an edge-list occurrence locates a vertex split with the tail tracked, any two splits at an in-edge share the same prefix-with-source (the positional strengthening of the degree-2 lemmas), and a double entry would equate a prefix with a strictly longer one — killed by lengths. If the crossing edges are exactly the entries equal to the in-edge, the count is exactly 1 — the payoff's odd case `[exact]` | 3 |
| `JCTPayoffKit.v : noncross_far` (+ `ho_count_one_out`, `carrier_east_cross`, `carrier_west_nocross`, `wall_corridor_clear_corner_east_top`) | **Escape-descent rung 5c-16a, the payoff kernels:** a non-incident edge never crosses the ray of a band point near the *eastmost* vertex — its crossing abscissa is a convex combination of endpoint abscissae (at most the eastmost abscissa) and the corner disk excludes the near range — while incident edges cross exactly when they strictly straddle the height with carrier strictly east. With the out-edge counting symmetry and the last clearance mirror, every corner-band point's count is computable: 0 east or with no spanning incident, 1 with exactly one `[exact]` | 3 |
| `JCTPayoffRides.v : payoff_passage_min` (+ `payoff_east_ride`, `payoff_west_ride_pt`, `payoff_wedge_min`) | **Escape-descent rung 5c-16b, the payoff rides:** at the eastmost vertex every hug configuration yields a connected, off-ring, ray-guarded point with crossing count **0 or 1** — the east ride lands strictly east of every vertex (count 0); the pass-through west ride and the pinched wedge probe see exactly the ridden edge (count 1, the entry-counting lemmas); the open-minimum passage lands below the corner where nothing spans (count 0). The walker's even parity will eliminate the count-1 cases at assembly, and count 0 < any positive count closes the descent `[exact]` | 3 |
| `JCTEscapeDescentHolds.v : escape_descent_holds` (+ `eastmost_payoff`, `payoff_min_dispatch`, `payoff_ymir`) | **THE DESCENT, CLOSED:** for every taut, proper, horizontal-free closed ring, `escape_descent r` holds outright — the walker enters the boundary hug at its first wall, propagates around the whole ring, and the eastmost dispatch harvests a connected guarded point of count 0 (the descent's `q`: even, below any positive count) or count 1 (odd — parity transport along the connecting path would put the even walker in-ring, absurd). The campaign's single remaining residual is gone `[exact]` | 3 |
| `JCTEscapeDescentHolds.v : parity_seam_offring_taut` | **H1, CLOSED:** `parity_characterises_interior_cont_offring p r` holds **unconditionally** for taut, proper, horizontal-free rings — the corrected polygonal Jordan seam, with the trapped half, the separation clause, and now the escape half all theorems. No stub, no named hypothesis, exactly the three allowed axioms (`sig_not_dec`, `sig_forall_dec`, `functional_extensionality_dep`) `[exact]` | 3 |

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
| `ArcChordDensity.v : n_chords_achieve_eps` (+ `sagitta_conjugate_identity`, `sagitta_mul_radius_le`, `sagitta_le_quadratic_decay`) | **Sagitta-density law (triage route B):** s·(r + √(r²−l²)) = l² exactly, hence s·r ≤ l²; with half-chord budget L/n, any n with n²·(r·ε) ≥ L² (n ≥ L/√(r·ε)) brings every sub-chord's sagitta within ε — the chord-count-vs-tolerance trade-off as a theorem, per-sub-chord interface `[exact]` | 3 |
| `ArcChordSubdivision.v : equal_angle_chords_achieve_eps` (+ `chord_half_length_sq_central`, `sin_sq_le_sq`) | **Equal-angle budget discharge (route B follow-up):** l² = R(1−cos φ)/2 exactly through `angle_between`; a sub-arc subtending φ ≤ θ/n has sagitta ≤ ε whenever n²·(r·ε) ≥ (r·θ/2)² — the angle-budget form an equal-angle lineariser consumes (atan/sin Category-C lane) `[exact]` | 4 |
| `ArcIntersectIVT.v : chord_crosses_arc_circle_implies_circle_intersection` | Sign change of in-circle along a chord ⇒ real crossing (IVT) `[exact]` | 3 |
| `ArcOverlay.v : arc_overlay_correct_chord_approx` | **Conditional headline:** result point within `max_sagitta` of an arc, under 2 bridge hypotheses `[cond]` | 3 |
| `Atan2.v : cos_atan2` (+`sin_atan2`) | **Option-A foundation (issue #64):** the Stdlib-`Ratan`-built `atan2 y x` is the polar angle of `(x,y)` — `cos = x/r`, `sin = y/r` for `(x,y)≠0` `[exact]` | 4 |
| `AngleBetween.v : cos_angle_between` (+`sin_angle_between`) | **Option-A central angle/sweep (issue #64):** the signed angle `atan2(cross,dot)` between two vectors has `cos = dot/(\|u\|\|v\|)`, `sin = cross/(\|u\|\|v\|)` (Lagrange identity); sign encodes orientation. Range (-π,π] via `atan2_range` `[exact]` | 4 |
| `ArcLength.v : chord_le_arc_length` (+`chord_subtended_sq`) | **Option-A exact arc length (issue #64):** `arc_length = r·θ`; the chord never exceeds the arc (`2r·sin(θ/2) ≤ rθ`), and `chord² = 2r²(1−cosθ)` (half-angle bridge to dot products) `[exact]` | 4 |
| `ArcOffset.v : arc_offset_dist_exact` (+ `arc_offset_radial_dist`, `arc_offset_dist_lower`) | **Curve-aware buffer brick 1 (issue #65 BUF-*):** the concentric radius-`r+d` curve is *exactly* at distance `\|d\|` from the source circle — every circle point is `≥ \|d\|` away (reverse triangle inequality through the center) and the radial correspondent attains it. The defining parallel-curve property, valid up to (and including) the singularity `d = −r` `[exact]` | 3 |
| `ArcOffset.v : arc_offset_no_kink` (+ `arc_offset_tangent_parallel`, `circle_point_{x,y}_deriv`) | **Arc-offset PARALLEL (issue #65):** for `0 < r`, `0 < r+d` the offset tangent is a POSITIVE scalar multiple (`(r+d)/r`) of the source tangent — offsetting cannot rotate or reverse the direction of travel (curved analogue of `BufferOffset.offset_seg_dir`, the JTS#739/#180 kink class). Tangents are genuine `derivable_pt_lim` derivatives of the parametrisation, not decreed `[exact]` | 3 |
| `ArcOffset.v : arc_offset_tangent_dot` (+ `arc_offset_tangent_reverses_past_singularity`) | **Arc-offset singularity, quantitative (issue #65):** tangent dot product `= r(r+d)` exactly — positive before the singularity `d = −r`, zero at it, negative past it: the direction of travel REVERSES (cusp + inversion, the inverted-negative-buffer class) `[exact]` | 3 |
| `ArcOffset.v : inner_offset_past_center_not_at_distance` | **Honest negative (issue #65):** concrete Qed witness (`r = 1`, `d = −3`) that past the singularity (`d < −r`) the parallel-curve property itself FAILS — the "offset" point is at distance `1 < \|d\| = 3` from the circle. Emitting `circle_point C (r+d)` there is unsound, not merely inverted `[exact]` | 3 |
| `ArcOffset.v : arc_offset_length` | **Arc-offset length bridge (M-LEN, issue #65):** over the same sweep, `arc_length (r+d) θ = arc_length r θ + d·θ` `[exact]` | 3 |
| `ArcOffsetThreePoint.v : arc_offset_preserves_arc` (+ `arc_offset_arc_valid`, `arc_offset_arc_control_dist`) | **SQL/MM closure — "offset preserves arcs" (issue #65 BUF-*/OFF):** radially offsetting the three control points of a valid `CurveGeometry.CircularArc` (pure rational arithmetic, no trig) yields a VALID three-point arc with the SAME `arc_center` and `arc_radius = r + d`, each control point at distance `\|d\|` from its source — the representation-level fact a curve-preserving buffer needs to emit `CurvePolygon` boundaries in SQL/MM form `[exact]` | 3 |
| `ArcOffsetThreePoint.v : equidistant_point_is_arc_center` | **Circumcenter uniqueness:** any point equidistant from the three control points of a valid arc IS `arc_center` — the converse of `ArcChordApprox.arc_center_equidistant` that `CurveGeometry.v`'s §2 comment deferred (perpendicular-bisector system + Cramer against the explicit formula) `[exact]` | 3 |
| `ArcOffsetThreePoint.v : radial_offset_dist_exact` (+ `circle_offset_dist_lower_any`, `arc_radius_pos`) | **Parallel-curve property in coordinate form (issue #65):** the radial offset `C + ((r+d)/r)·(P−C)` of an on-circle point is at distance exactly `\|d\|` from the ENTIRE source circle (`−r ≤ d`); plus `0 < arc_radius` for every valid arc `[exact]` | 3 |
| `CurveRingOffset.v : curve_ring_offset_arcs_valid` (+ `curve_ring_offset_length`) | **COMPOUNDCURVE offset, structure survives (issue #65):** offsetting a `CurveRing` segment-wise (chords via `BufferOffset.offset_point`, arcs via `arc_offset_arc`) preserves per-arc validity under the per-arc safety bound `−r < d` (`ring_offset_safe`), and the segment count `[exact]` | 3 |
| `CurveRingOffset.v : arc_join_offset_continuous` | **G1 joins offset continuously (issue #65):** two consecutive arcs sharing their join point with EQUAL unit outward normals there still share it after offsetting — smooth compound curves need no join edges `[exact]` | 3 |
| `CurveRingOffset.v : tangent_continuity_insufficient_for_offset` | **Honest negative (issue #65):** tangent-LINE continuity is not enough — concrete S-curve (inflection) witness: two unit arcs meeting at `(1,0)` (centers `(0,0)`/`(2,0)`, same tangent line, ANTI-parallel normals); the `d = 1` offset tears the join to `(2,0)` vs `(0,0)`. The arc-side reason stage-2b join edges remain necessary (JTS#1147 / OffsetCurve artifact class) `[exact]` | 3 |
| `CurveRingOffset.v : segment_join_offset_continuous` (+ `curve_segment_offset_{end,start}`, `join_normals_consistent_norm_iff`) | **Uniform join lemma (issue #65):** both offset formulas factor through `P + d·n̂` via a uniform normal field (`segment_norm_{end,start}`: chords carry `unit_perp`, arcs the outward unit radial), so ONE lemma covers chord-chord, chord-arc, and arc-arc joins: shared join point + consistent normals stays shared under offset `[exact]` | 3 |
| `CurveRingOffset.v : curve_ring_offset_valid` (+ `curve_ring_offset_adjacent`, `curve_ring_offset_closed`) | **Ring-level capstone (issue #65):** a smooth compound ring (`valid_curve_ring`, all consecutive + closing joins with consistent normals) offset within the per-arc safety bound is again a `valid_curve_ring` — arcs valid, adjacent, closed. The structural prerequisite for emitting offset rings as SQL/MM `CurvePolygon` boundaries `[exact]` | 3 |
| `CurveRoundJoin.v : round_join_arc_valid` (+ `unit_cross_nonzero`) | **Round join as an SQL/MM arc (issue #65 stage 2b-curve):** at a non-G1 join the gap-filling arc (`P + d·n̂₁` → angular midpoint → `P + d·n̂₂`) is a VALID `CircularArc` — the control-point cross factors exactly as `d²·(2−h)/h·cross(n̂₁,n̂₂)` with `h = \|n̂₁+n̂₂\|`, and the turning lemma gives `cross ≠ 0` for distinct non-antipodal unit normals `[exact]` | 3 |
| `CurveRoundJoin.v : round_join_arc_center_radius` (+ `round_join_arc_on_offset_circle`) | **Join-arc circumcircle is exactly `(P, \|d\|)` (issue #65):** the emitted join arc's `arc_center` is the corner point and `arc_radius = \|d\|` — by rung 2's circumcenter uniqueness — so the round join is geometrically the offset circle of the corner, as the buffer contract demands `[exact]` | 3 |
| `CurveRoundJoin.v : round_join_connects` (+ `segment_norm_{end,start}_unit_arc`, `segment_norm_chord_unit`) | **Join-arc splicing (issue #65):** the join arc's start/end coincide with the adjacent offset segments' endpoints (uniform normal field), and the ring's own normal fields are unit vectors — the adjacency facts the assembly rung needs to splice join arcs into `curve_ring_offset` output `[exact]` | 3 |
| `CurveOffsetAssembly.v : curve_ring_offset_round_valid` (+ `offset_walk_arcs_valid`, `offset_walk_adjacent`, `join_arc_arc_valid`) | **Assembly capstone (issue #65):** walking a valid compound ring (non-degenerate chords, per-arc safety bound, `d ≠ 0`, no U-turn joins) and splicing the round-join arc at every non-G1 join — including the closing join — yields again a `valid_curve_ring`. Extends the smooth-ring capstone to ARBITRARY non-U-turn compound rings; conditional only on the SPEC of the supplied G1 decision oracle (real equality is not computable; extraction supplies the comparison) `[exact]` | 3 |
| `CurveOffsetAssembly.v : offset_walk_smooth_eq_map` | **Coherence (issue #65):** on an all-G1 ring the assembly walk inserts nothing and equals the plain segment-wise `curve_ring_offset` — the assembly conservatively extends the smooth case `[exact]` | 3 |
| `CurveSemicircle.v : semicircle_arc_valid` (+ `semicircle_arc_center_radius`, `semicircle_arc_on_offset_circle`) | **The semicircle arc (issue #65, stages 2b+2c):** for unit perpendicular `n̂`, `t̂` and `d ≠ 0`, the three-point arc `P+d·n̂ → P+d·t̂ → P−d·n̂` is a VALID SQL/MM arc (control-point cross `= −2d²·cross(t̂,n̂)`, with `cross² = 1` by `Vec.lagrange_identity`) whose circumcircle is exactly `(P, \|d\|)` — third consumer of the circumcenter-uniqueness lemma `[exact]` | 3 |
| `CurveSemicircle.v : semicircle_uturn_connects` | **U-turn join closed (issue #65):** at an anti-parallel-normal join (`n̂₂ = −n̂₁`, the case `round_join_arc` excludes), the semicircle splices the two offset segments — closing the assembly's no-U-turn exclusion at the single-join level `[exact]` | 3 |
| `CurveSemicircle.v : semicircle_cap_connects` (+ `cap_tangent_{unit,perp}`) | **Round endcap in SQL/MM form (issue #65 stage 2c):** the same semicircle caps an open compound line's end, connecting the `+d` offset boundary to the `−d` offset boundary — the curve analogue of `BufferEndcap.v`'s round-cap layer, with `vperp` as the canonical sweep direction `[exact]` | 3 |
| `CurveOffsetAssemblyTotal.v : curve_ring_offset_total_valid` (+ `join_connector_arc_valid`, `join_connector_splice`, `vadd_eq_zero_iff_vneg`) | **Total assembly — NO join exclusions (issue #65):** the three-way join policy (G1: nothing; U-turn: the semicircle with a supplied unit-perpendicular sweep side; otherwise: the round join) assembles ANY valid compound ring (non-degenerate chords, per-arc safety bound, `d ≠ 0`) into a `valid_curve_ring`, including the closing join. Conditional only on the specs of the two boolean oracles and the sweep-side supplier (`tsel_vperp_spec` discharges the canonical `vperp` instance) `[exact]` | 3 |
| `CurveOffsetAssemblyTotal.v : offset_walk_total_smooth_eq_map` | **Coherence (issue #65):** on an all-G1 ring the total walk still inserts nothing and equals the plain segment-wise `curve_ring_offset` `[exact]` | 3 |
| `CurvePolygonOffset.v : curve_polygon_offset_valid` (+ `curve_geometry_offset_valid`, `curve_polygon_offset_holes_length`, `curve_geometry_offset_length`) | **SQL/MM hierarchy lift (issue #65, P1):** applying the total ring assembly to a polygon's outer ring and every hole (one signed `d`; the side is encoded by ring orientation, the JTS OffsetCurveBuilder convention) preserves validity at every level — ring → `CurvePolygon` → `CurveGeometry` — under the bundled per-ring side conditions, with hole and polygon counts preserved. Complete w.r.t. the corpus's validity layer (hole-inside-outer is deliberately analytic-layer, tracked as P2) `[exact]` | 3 |
| `CurveJoinClassify.v : g1_decision_correct` (+ `uturn_decision_correct`, `unit_eq_iff_cross_dot`, `unit_opp_iff_cross_dot`) | **The assembly oracles are realizable (issue #65, P10 brick 1):** unit-normal equality is a RATIONAL condition on the un-normalised normals — `û = v̂ ⟺ cross(u,v) = 0 ∧ 0 < dot(u,v)` (anti-parallel: `dot < 0`) — and the ring's normal fields normalise from rational raw vectors (`vperp` of the direction; `P − arc_center`). So `g1dec`/`uturndec` (rungs 6/8/9) are each ONE exact-rational cross + dot; their specs discharge outright on rational control points `[exact]` | 3 |
| `CurveJoinClassify.v : offset_safe_iff_sq` | **Safety bound decidable from `r²` (issue #65):** `−r < d ⟺ d ≥ 0 ∨ d² < r²` — with `valid_arc`, chord non-degeneracy, and adjacency/closedness all rational point/determinant tests, EVERY hypothesis of `curve_ring_offset_total_valid` is decidable in exact rational arithmetic `[exact]` | 3 |
| `CurveOffsetEmit.v : offset_emit_ring_closed` (+ `linear_offset_emit_ring_closed`, `curve_segment_offset_chord_is_offset_seg`, `curve_ring_offset_all_chord`) | **Stage-2 → stage-3 handoff (issue #65, P3):** the assembled offset ring's chord linearisation is a `ring_closed` Phase-3 ring — the front-end's emitted edge list CLOSES, the structural contract the noding stage needs. Specialised to all-chord input it discharges the round-join flavour of the linear emitted-edge-list gap; the chord case of the curve emitter IS `BufferOffset.offset_seg` definitionally (the once-open miter/bevel emission and open-chain caps have since landed: rungs 12-13 and 14b) `[exact]` | 3 |
| `CurveBevelJoin.v : curve_ring_offset_bevel_valid` (+ `bevel_join_nondeg`, `curve_ring_offset_bevel_preserves_chords`, `bevel_emit_ring_closed`) | **Bevel assembly (issue #65, 2b row):** the bevel join is the CHORD across the tear — splice facts definitional, handles every non-G1 join (U-turns included), contributes nothing to arc validity — so any valid compound ring offset within the per-arc safety bound bevels into a `valid_curve_ring` with the LEANEST hypothesis set of the three assemblies. Non-degenerate at genuine turns with `d ≠ 0`; all-chord input gives all-chord output (the pure linear bevel emitter); the linearised output ring closes (stage-3 handoff). Miter emission is the one open join flavour `[exact]` | 3 |
| `CurveMiterJoin.v : curve_ring_offset_miter_valid` (+ `miter_connector_apex_sound`, `curve_ring_offset_miter_preserves_chords`, `miter_emit_ring_closed`) | **Miter assembly (issue #65, 2b row COMPLETE):** at chord-chord joins the connector is two chords through `BufferMiter.miter_apex` (the JTS#180 offset-line intersection, at signed perpendicular distance `d` from BOTH source edges — `miter_connector_apex_sound`); joins involving arcs fall back to the bevel chord, mirroring JTS. Any valid compound ring offset within the per-arc safety bound miters into a `valid_curve_ring` under the lean hypothesis set; all-chord in → all-chord out; the linearised output closes. With round (rungs 5–8), bevel (rung 12) and miter, the 2b join-emission story is complete `[exact]` | 3 |
| `CurveReverse.v : valid_curve_ring_reverse` (+ `rev_arc_center`, `rev_arc_radius`, `rev_arc_valid`) | **Ring reversal preserves validity (issue #65, rung 14a):** reversing a compound ring (reverse the list AND each segment; arcs swap start/end) preserves `valid_curve_ring` — the SQL/MM ring-orientation flip (the hole convention). The circumcircle is traversal-invariant, with center invariance proved via circumcenter uniqueness (its fourth consumer) `[exact]` | 3 |
| `CurveReverse.v : offset_rev_chord` (+ `offset_rev_arc`, `chord_norm_rev`, `arc_norm_rev_{end,start}`) | **The orientation wart, formalised (issue #65):** chord `unit_perp` normals FLIP under reversal but arc radial normals are traversal-agnostic, so offset and reverse commute at OPPOSITE signs per kind — `offset(rev chord) d = rev(offset chord (−d))` yet `offset(rev arc) d = rev(offset arc d)`. The formal reason a two-sided walk (and JTS's OffsetCurveBuilder) must track an explicit side flag rather than encode side by traversal `[exact]` | 3 |
| `CurveCapWalk.v : curve_chain_buffer_valid` (+ `chain_walk_adjacent`, `cap_far_connects`, `cap_start_connects`) | **The open-chain two-sided cap walk (issue #65, rung 14b):** buffering an open compound line — left `+d` walk, far semicircle cap, the REVERSAL of the forward `−d` walk (the wart-dictated design: reversal lemmas supply the right boundary's structure with no per-kind sign threading), start cap back — yields a CLOSED, VALID compound ring, under chain adjacency, valid arcs, non-degenerate chords, two-sided per-arc safety and `d ≠ 0`. Every stage-2 emission (rings rungs 6–13, chains here) now produces a valid compound ring `[exact]` | 3 |
| `InCircle_b64_exact.v : b64_inCircle_exact_sound` | **Full-plane sign exactness (issue #64 ask #4b):** the common-exponent integer-determinant predicate's sign agrees with `inCircle_R_BP` for all finite binary64 inputs — integer `ℤ` arithmetic only, no float ops, **3 axioms (no `classic`)** `[full-b64]` | 3 |
| `InCircle_b64_exact.v : b64_inCircle_exact_for_small_int` (+ `_exact_and_finite_`, `b64_inCircle_finite_for_small_int`) | **Integer-regime value exactness + finiteness:** `B2R (b64_inCircle …) = inCircle_R_BP` on the nose when every coordinate is integer-valued with `\|n\| ≤ 2¹¹`; the companion `_finite_` projection exposes `is_finite (b64_inCircle …)` (always established inside the exactness proof) — the prerequisite for the arc-line Scope B/C round-chain `[int-b64-arc]` | 4 |
| `InCircle_b64_exact.v : b64_inCircle_B2R_sign_sound_small_int` | Sign of the rounded `b64_inCircle` value agrees with `inCircle_R_BP` in the same `2¹¹` integer regime `[int-b64-arc]` | 4 |
| `InCircle_b64_exact.v : perron_inCircle_sign_sound` | Perron stage-10 thin-sliver witness at the `2¹¹` boundary: opposite-sign chord endpoints with bit-exact `b64_inCircle` values `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_{sP_R,sQ_R,dx_R,dy_R}` | **Arc-line Scope A (issue #64 ask #5a):** first-stage Cramer prefix before division — outer `sP`/`sQ` inCircle evaluations and chord `dx`/`dy` differences are bit-exact integer-valued binary64 `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_den_exact` (+ `_den_nonzero`) | **Arc-line Scope B.1 (issue #64 ask #5a):** the division denominator `den = sP − sQ` is computed **bit-exactly** (`= inCircle_R_BP S M E P − inCircle_R_BP S M E Q`, finite) — both inCircle values are integers `≤ 2⁵²` so the difference `≤ 2⁵³ = 2^prec` is exact — and is nonzero exactly under the safety predicate. The denominator round-chain gate; uses the new `b64_inCircle_finite_for_small_int`. Division/mult/add round-chain (Scope B.2) now landed (see next row); forward-error (Scope C) remains queued `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_intersect_point_{x,y}_round_chain` | **Arc-line Scope B.2 (issue #64 ask #5a):** the *full* coordinate round-chain identity — `B2R (b64_arc_line_intersect_point_x …) = round(B2R(bx P) + round(round(sP/(sP−sQ)) · (B2R(bx Q) − B2R(bx P))))` (and symmetric for `y`). Each binary64 step is pinned to its IEEE-754 rounding of the exact-real operands: the integer-exact prefix (`sP`, `den`, `dx`/`dy` from Scope A/B.1) feeds a `div → mult → plus` chain, each discharged via `b64_{div,mult,plus}_correct` with magnitude gates (`\|sP\| ≤ 2⁵²`, `\|den\| ≥ 1`, `\|dx\| ≤ 2¹²`, `t·dx ≤ 2⁶⁴`, sum `≤ 2⁶⁵ < 2^emax`). This is the exact statement of *what the float intersection computes* — the launch point for the Scope C forward-error bound `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_t_forward_error` (+ `_t_round`, `_t_abs_le_bpow_52`, `arc_line_ratio_abs_le_52`) | **Arc-line Scope C layer-1 (issue #64 ask #5a):** the computed division parameter `t = b64_div sP den` deviates from the *exact-real* ratio `sP_R/(sP_R−sQ_R)` by at most **½** — a single division half-ulp. Because the denominator is **bit-exact** (Scope B.1), there is *no* denominator-carryover error (unlike the line-line layer 1, which rounds its own denominator). Derivation: `\|sP_R\| ≤ 2⁵²`, `\|den_R\| ≥ 1` ⇒ `\|ratio\| ≤ 2⁵²` ⇒ `ulp(round ratio) ≤ bpow 0 = 1` ⇒ half-ulp `≤ ½`. First layer of the Scope C forward-error cascade against `arc_line_intersect_x_R`; layers 2–4 (mult, plus, headline) queued `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_mult_{x_forward_error,y_forward_error}` (+ `_mult_*_round_error`, `_mult_*_carry_error`, `_mult_*_safe`, `_mult_*_abs_le_bpow_64`, `_d{x,y}_abs_le_bpow_12`) | **Arc-line Scope C layer-2 (issue #64 ask #5a):** the computed product `b64_mult t d` (`d = bx Q − bx P`, resp. `by_`) deviates from the exact-real `ratio · d_R` by at most **bpow 12** (and symmetric for `y`). Decomposition: multiply half-ulp (`ulp ≤ bpow(64−prec+1) = bpow 12`, so `≤ bpow 11`) + carry of the layer-1 t-error (`\|d_R\| · ½ ≤ 2¹²·½ = bpow 11`). **No `1/\|den\|` term** — because layer 1 is absolutely `≤ ½` (bit-exact denominator, Scope B.1), the arc-line bound is a clean constant, unlike the line-line layer whose denominator-rounding carries a `bpow 80/\|den\|` tail. Layers 3–4 (the `bx P + ·` add and the coordinate headline vs `arc_line_intersect_{x,y}_R`) now landed (see next row) `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_point_{x_forward_error,y_forward_error}` (+ `_plus_*_safe`, `_point_*_round`, `_point_*_abs_le_bpow_65`, `_plus_*_round_error`, `_*P_abs_le_bpow_11`) | **Arc-line Scope C capstone — layers 3–4 (issue #64 ask #5a):** the headline forward-error bound. The float intersection coordinate is within **bpow 13** of the *exact real* value: `\|B2R(b64_arc_line_intersect_point_x …) − arc_line_intersect_x_R …\| ≤ bpow 13` (and symmetric for `y`). Layer 3 (final `bx P + ·` add): half-ulp at magnitude `≤ 2⁶⁵` ⇒ `ulp ≤ bpow(65−prec+1)=bpow 13` ⇒ `≤ bpow 12`; plus the layer-2 carry `≤ bpow 12`; total `bpow 13`. **Closes Scope C.** Crucially the bound is an *absolute constant with no `1/\|den\|` condition-number blow-up* — the entire cascade stays absolute because the denominator is bit-exact (Scope B.1). Contrast the line-line headline (`Intersect_b64_exact.v`), whose forward error carries a `bpow 80/\|den\|` tail. `[int-b64-arc]` | 4 |

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
`ratio·d_R` by a clean `bpow 12` (no `1/|den|` tail, unlike line-line). **Scope
C is now closed:** the capstone `b64_arc_line_point_{x,y}_forward_error` proves
`|B2R(b64_arc_line_intersect_point_{x,y} …) − arc_line_intersect_{x,y}_R …| ≤
bpow 13` — the float arc-line intersection coordinate is within `bpow 13` of the
exact real value, an **absolute** bound with *no `1/|den|` condition-number
blow-up*, because the bit-exact denominator (Scope B.1) keeps every layer of the
cascade absolute. So the honest arc-line story is: bit-exact prefix (A) →
bit-exact denominator (B.1) → exact round-chain identity (B.2) → absolute
`bpow 13` forward-error bound vs the exact real coordinate (C).

## Issue #67 — DE-9IM matrix algebra (`DE9IM.v`, session 1)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `DE9IM.v : im_disjoint_not_intersects_partial` | **Partial headline:** JTS `disjoint` forces `intersects₀/₁/₄` false (not full `intersects` — `intersects₃` can still match; see gap witnesses) `[exact]` | 0 |
| `DE9IM.v : im_contains_transpose_within` (+`predicate_contains_transpose_within`) | `contains` on `m` ⇔ `within` on `matrix_transpose m` (JTS converse) `[exact]` | 0 |
| `DE9IM.v : im_covers_transpose_coveredBy` (+`predicate_covers_transpose_coveredBy`) | `covers` on `m` ⇔ `coveredBy` on transpose (`pattern_transpose` on all four JTS covers patterns) `[exact]` | 0 |
| `DE9IM.v : disjoint_intersects3_example_holds` | **Honest gap:** a matrix can be both `disjoint` and `intersects₃` (abstract IM algebra ≠ complete geometry IM) `[exact]` | 0 |

Full RelateNG noding, arc/clothoid carriers, and prepared-cache slices remain
follow-up (#67 S10+).

## Issue #67 — line-line DE-9IM: witnesses + geometry (`RelateLineLine.v`, session 2)

**Honesty note (whole #67 RelateNG arc).** Each slice has two *independent*
layers and does **not** bridge them: (a) constant `*_witness` lemmas — a
hand-specified DE-9IM matrix satisfies a named predicate; (b) `*_geom` /
`*_share` / `*_not_share` / membership / mutual-exclusion lemmas — the genuine
geometric consequence of a regime. Proving a witness matrix **is** a
configuration's true DE-9IM (so that geometry ⇒ matrix) is the deferred
RelateNG-noding step (S13+) and is *not* claimed by any theorem here. The `Ax`
column is the build's per-file `Print Assumptions` audit: every issue-67
`Relate*` file is **closed under the global context (axiom-free)** for the
audited theorems — so the earlier `3` (classical-reals lane) annotations were
pessimistic and are corrected to `0` — **except `RelateArcAnalytic.v`**, whose
`arc_sweep_principal_range` genuinely inherits `Classical_Prop.classic` via the
`Atan2` / `AngleBetween` lane (4-axiom; exempted in `docs/audit-exceptions.txt`
alongside its dependencies, and marked `4` below).

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateLineLine.v : line_line_proper_cross_geom` | **Geometry:** strict opposite-sign crosses ⇒ the segments share a point (`strict_completeness`) `[exact]` | 0 |
| `RelateLineLine.v : line_line_rejected_not_share` | **Geometry:** same-side sign rejection ⇒ no shared point (soundness of NTS rejection) `[exact]` | 0 |
| `RelateLineLine.v : line_line_collinear_overlap_share` | **Geometry:** both endpoints of CD on AB ⇒ shared point `[exact]` | 0 |
| `RelateLineLine.v : ll_matrix_point_ii_crosses_ll` / `_intersects` | **Witness:** the point matrix satisfies `Crosses` (LL) / `Intersects` `[exact]` | 0 |
| `RelateLineLine.v : ll_matrix_disjoint_witness` | **Witness:** the empty matrix satisfies `Disjoint` `[exact]` | 0 |
| `RelateLineLine.v : ll_matrix_overlap_ii_overlaps` | **Witness:** the overlap matrix satisfies `Overlaps` (LL) `[exact]` | 0 |

The regime→witness assignment is realised by `line_pair_fill` in
`RelateMatrixLineLine.v` (S8).

## Issue #67 — Romanschek line–line oracle matrices (`RelateLineLine.v`, S3 seed)

Pinned 9-char DE-9IM strings from Romanschek et al. (IJGI 2021) Table 5/6 /
[topology-relations](https://github.com/dd-bim/topology-relations) agree with NTS 2.3.0 at
extent `r_max ≤ 1056`. Vectors: `oracle/de9im_line_line_vectors.txt`. Predicate
lemmas only — no WKT→matrix computation yet.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateLineLine.v : paper_test7_overlaps` | Test 7 (`1FFF0FFF2`) satisfies `Overlaps` (LL) `[exact]` | 0 |
| `RelateLineLine.v : paper_test6_not_crosses` | Test 6 (`FF1FF0102`) does **not** satisfy `Crosses` under `pat_crosses_ll` (II=F) `[exact]` | 0 |
| `RelateLineLine.v : paper_test13_crosses` | Test 13 (`0F1FF0102`) satisfies `Crosses` (LL); II=0 matches `ll_matrix_point_ii` `[exact]` | 0 |
| `RelateLineLine.v : paper_test10_not_disjoint` | Test 10 (`FF10F0102`) is **not** `Disjoint` (BI=0) though segments are separated `[exact]` | 0 |
| `RelateLineLine.v : paper_test7_agrees_overlap_witness_core` | Test 7 shares II/BB cells with `ll_matrix_overlap_ii` `[exact]` | 0 |

## Issue #67 — area-point: membership + witnesses (`RelateAreaPoint.v`, S4)

Guarded rectangle (open box, no holes). Geometry layer = point membership;
witness layer = hand-specified Contains/Touches matrices (not derived from
geometry).

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateAreaPoint.v : strict_interior_in_rect_polygon` | **Geometry:** `x0 < px < x1` and `y0 < py < y1` ⇒ point ∈ rectangle polygon `[exact]` | 0 |
| `RelateAreaPoint.v : strict_interior_in_rect_geometry` | **Geometry:** strict-interior point lies in `point_set` of the single-rectangle geometry `[exact]` | 0 |
| `RelateAreaPoint.v : ap_matrix_rect_contains_point_witness` | **Witness:** the hand-specified matrix satisfies `Contains` `[exact]` | 0 |
| `RelateAreaPoint.v : left_boundary_in_polygon_not_strict` | **Geometry:** a left-edge point is in the polygon but outside the strict interior (`px = x0`) `[exact]` | 0 |
| `RelateAreaPoint.v : ap_matrix_rect_touches_boundary_witness` | **Witness:** the S4b boundary matrix (`pat_touches_3`, EB=0) satisfies `Touches` `[exact]` | 0 |

## Issue #67 — boundary / MOD2 policy (`RelateBoundary.v`, S4b)

Line-line endpoint classification and JTS#1175 regression class.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateBoundary.v : mod2_endpoint_is_boundary` | MOD2 rule: incidence count `1` is a boundary node (line endpoint) `[exact]` | 0 |
| `RelateBoundary.v : endpoint_contact_share` | **Geometry:** shared-endpoint contact ⇒ the segments share a point `[exact]` | 0 |
| `RelateBoundary.v : ll_matrix_touches_endpoint_witness` | **Witness:** the endpoint-only matrix (`pat_touches_0`, IB=0) satisfies `Touches` `[exact]` | 0 |
| `RelateBoundary.v : jts1175_boundary_cells_preclude_disjoint` | Romanschek test 10 / JTS#1175 class: `intersects` yet not `disjoint` (BI=0 boundary visibility) `[exact]` | 0 |

## Issue #67 — area-line: witnesses + geometry (`RelateAreaLine.v`, S5)

Guarded axis-aligned rectangle vs closed segment. Regime→witness selection via
`RelateMatrixAreaLine.v` (S9).

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateAreaLine.v : al_matrix_segment_interior_intersects` | **Witness:** the interior matrix (II=1) satisfies `Intersects` `[exact]` | 0 |
| `RelateAreaLine.v : al_matrix_segment_crosses_witness` | **Witness:** the pierce matrix (`pat_crosses_lp_ap_al`, II=1 BE=0) satisfies `Crosses` `[exact]` | 0 |
| `RelateAreaLine.v : segment_pierces_rect_share` | **Geometry:** a horizontal pierce shares a point with the crossed vertical edge (`strict_completeness`) `[exact]` | 0 |
| `RelateAreaLine.v : al_matrix_disjoint_witness` | **Witness:** the empty matrix satisfies `Disjoint` (segment-above regime) `[exact]` | 0 |
| `RelateAreaLine.v : al_matrix_boundary_touch_witness` | **Witness:** the boundary matrix (`pat_touches_1`, BB=0) satisfies `Touches` `[exact]` | 0 |

## Issue #67 — area-area DE-9IM witnesses (`RelateAreaArea.v`, S6)

Guarded axis-aligned rectangle pairs (no holes). Hand-specified witnesses, one
per regime; regime→witness selection via `RelateMatrixRect.v` (S7). The regime
predicates (`rects_separated_horiz`, …) name the intended geometry but are not
consumed.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateAreaArea.v : aa_matrix_disjoint_witness` | **Witness:** the empty matrix satisfies `Disjoint` (separated-rects regime) `[exact]` | 0 |
| `RelateAreaArea.v : aa_matrix_partial_overlap_witness` (+`_intersects`) | **Witness:** the overlap matrix (`pat_overlaps_pp_aa`, II=2 BB=1 EE=2) satisfies `Overlaps` + `Intersects` `[exact]` | 0 |
| `RelateAreaArea.v : aa_matrix_contains_witness` (+`_intersects`) | **Witness:** the contains matrix satisfies `Contains` + `Intersects` `[exact]` | 0 |
| `RelateAreaArea.v : aa_matrix_touch_vertical_witness` | **Witness:** the touch matrix (`pat_touches_1`, BB=1) satisfies `Touches` `[exact]` | 0 |

## Issue #67 — rect×rect regime→witness (`RelateMatrixRect.v`, S7)

Regime-indexed `rect_pair_fill` **selects** (does not compute from geometry) the
S6 witness matrices. `classify_rect_pair` records which S6 guard names each
regime; the `*_fill_witness` facts are constant (regime hypothesis not consumed).

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateMatrixRect.v : rect_fill_disjoint_witness` | **Witness:** `im_disjoint (rect_pair_fill RPR_Disjoint)` `[exact]` | 0 |
| `RelateMatrixRect.v : rect_fill_overlap_witness` | **Witness:** `Overlaps` + `Intersects` on `rect_pair_fill RPR_Overlap` `[exact]` | 0 |
| `RelateMatrixRect.v : rect_fill_contains_witness` | **Witness:** `Contains` + `Intersects` on `rect_pair_fill RPR_Contains` `[exact]` | 0 |
| `RelateMatrixRect.v : rect_fill_touch_witness` | **Witness:** `Touches` on `rect_pair_fill RPR_TouchVert` `[exact]` | 0 |
| `RelateMatrixRect.v : overlap_not_strictly_separated` | **Geometry:** partial overlap excludes strict horizontal separation (`ax1 < bx0`) `[exact]` | 0 |
| `RelateMatrixRect.v : touch_not_overlap` | **Geometry:** vertical edge touch excludes partial overlap `[exact]` | 0 |

## Issue #67 — line×line regime→witness (`RelateMatrixLineLine.v`, S8)

Regime-indexed `line_pair_fill` selects the S2 witness matrices. Romanschek
paper matrices (S3) remain oracle pins, not selection targets.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateMatrixLineLine.v : line_fill_disjoint_witness` | **Witness:** `im_disjoint (line_pair_fill LPR_Disjoint)` `[exact]` | 0 |
| `RelateMatrixLineLine.v : line_fill_proper_cross_witness` | **Witness:** `Crosses` + `Intersects` on `line_pair_fill LPR_ProperCross` `[exact]` | 0 |
| `RelateMatrixLineLine.v : line_fill_share_witness` | **Witness:** `Intersects` on `line_pair_fill LPR_Share` `[exact]` | 0 |
| `RelateMatrixLineLine.v : line_fill_collinear_overlap_witness` | **Witness:** `Overlaps` on `line_pair_fill LPR_CollinearOverlap` `[exact]` | 0 |
| `RelateMatrixLineLine.v : rejection_not_share` | **Geometry:** same-side rejection excludes segment share `[exact]` | 0 |
| `RelateMatrixLineLine.v : collinear_overlap_not_proper_cross` | **Geometry:** collinear overlap excludes proper crossing `[exact]` | 0 |

## Issue #67 — area×line regime→witness (`RelateMatrixAreaLine.v`, S9)

Regime-indexed `area_line_fill` selects the S5 witness matrices. Oracle
vocabulary for all fill APIs is seeded in
`oracle/relate_matrix_fill_vocabulary.txt`; `RELATE_MATRIX` and
`RELATE_PREDICATE` driver modes landed in S11 (`oracle/relate_matrix.ml`).

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateMatrixAreaLine.v : area_line_fill_interior_witness` | **Witness:** `Intersects` on `area_line_fill ALR_Interior` `[exact]` | 0 |
| `RelateMatrixAreaLine.v : area_line_fill_pierce_witness` | **Witness:** `Crosses` + `Intersects` on `area_line_fill ALR_Pierce` `[exact]` | 0 |
| `RelateMatrixAreaLine.v : area_line_fill_disjoint_witness` | **Witness:** `Disjoint` on `area_line_fill ALR_Disjoint` `[exact]` | 0 |
| `RelateMatrixAreaLine.v : area_line_fill_boundary_touch_witness` | **Witness:** `Touches` on `area_line_fill ALR_BoundaryTouch` `[exact]` | 0 |
| `RelateMatrixAreaLine.v : interior_not_disjoint` | **Geometry:** strict interior excludes the segment-above-rect disjoint guard `[exact]` | 0 |
| `RelateMatrixAreaLine.v : pierce_not_touch` | **Geometry:** horizontal pierce excludes left-boundary touch (given `x0 < x1`) `[exact]` | 0 |

## Issue #67 — arc×line: chord geometry + witnesses (`RelateArcChord.v`, S10)

First curve-aware relate slice (Option B chord path). Arc chord
(`arc_start`–`arc_end`) reuses S2 line-line geometry; `chord_crosses_arc_circle`
links to `ArcIntersectIVT`. Full arc-span membership remains a gap; Option-A
analytic regimes landed in S10b.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateArcChord.v : arc_chord_proper_cross_share` | **Geometry:** arc chord properly crosses segment ⇒ shared point (S2 delegate) `[exact]` | 0 |
| `RelateArcChord.v : arc_chord_rejected_not_share` | **Geometry:** same-side rejection on arc chord vs segment ⇒ no shared point `[exact]` | 0 |
| `RelateArcChord.v : arc_circle_chord_cross_on_circle` | **Geometry:** `chord_crosses_arc_circle` ⇒ ∃ on-circle hit on chord `PQ` (IVT) `[exact]` | 0 |
| `RelateArcChord.v : arc_chord_proper_cross_not_rejected` | **Geometry:** proper cross excludes same-side rejection on arc chord `[exact]` | 0 |
| `RelateArcChord.v : ac_matrix_point_ii_crosses` / `_intersects` / `ac_matrix_disjoint_witness` | **Witness:** the reused S2 matrices satisfy `Crosses`/`Intersects`/`Disjoint` `[exact]` | 0 |

## Issue #67 — arc×line regime→witness (`RelateMatrixArcChord.v`, S10)

Regime-indexed `arc_chord_fill` selects the S10 witness matrices.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateMatrixArcChord.v : arc_fill_chord_proper_cross_witness` | **Witness:** `Crosses` + `Intersects` on `arc_chord_fill ACR_ChordProperCross` `[exact]` | 0 |
| `RelateMatrixArcChord.v : arc_fill_chord_disjoint_witness` | **Witness:** `Disjoint` on `arc_chord_fill ACR_ChordDisjoint` `[exact]` | 0 |
| `RelateMatrixArcChord.v : arc_fill_circle_cross_witness` | **Witness:** `Intersects` on `arc_chord_fill ACR_CircleCross` `[exact]` | 0 |
| `RelateMatrixArcChord.v : chord_rejected_not_share` | **Geometry:** chord rejection excludes chord share `[exact]` | 0 |

## Issue #67 — arc×line analytic: geometry + witnesses (`RelateArcAnalytic.v`, S10b)

Option-A sweep via `AngleBetween.angle_between`. This is the one issue-67
`Relate*` file in the 4-axiom lane: `arc_sweep_principal_range` is built on
`AngleBetween.angle_between_range`, so it inherits `Classical_Prop.classic` (and
the 3 allowlist axioms). The file is exempted in `docs/audit-exceptions.txt`
alongside `Atan2.v` / `AngleBetween.v` / `ArcLength.v`.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateArcAnalytic.v : arc_sweep_principal_range` | **Geometry:** `valid_arc` ⇒ principal sweep `arc_sweep_angle` ∈ (-π, π] (inherits `Classical_Prop.classic` via `AngleBetween`) `[exact]` | 4 |
| `RelateArcAnalytic.v : arc_analytic_proper_cross_share` | **Geometry:** analytic-guarded proper cross ⇒ shared point (S10 delegate) `[exact]` | 4 |

## Issue #67 — arc×line analytic regime→witness (`RelateMatrixArcAnalytic.v`, S10b)

`arc_analytic_fill` selects the S10 point witness for the analytic-cross regime.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateMatrixArcAnalytic.v : arc_analytic_fill_cross_witness` | **Witness:** `Crosses` + `Intersects` on `arc_analytic_fill AAR_AnalyticCross` `[exact]` | 0 |

## Issue #67 — clothoid×line: chord geometry + witnesses (`RelateClothoid.v`, S10b)

Minimal `ClothoidChord` carrier; witnesses reuse S2 line-line matrices.
`clothoid_L_unique_on_branch` re-exports monotone-branch uniqueness from
`ClothoidResidual`.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateClothoid.v : clothoid_chord_proper_cross_share` | **Geometry:** clothoid chord properly crosses segment ⇒ shared point `[exact]` | 0 |
| `RelateClothoid.v : clothoid_chord_rejected_not_share` | **Geometry:** same-side rejection on clothoid chord ⇒ no shared point `[exact]` | 0 |
| `RelateClothoid.v : cl_matrix_point_ii_crosses` / `_intersects` / `cl_matrix_disjoint_witness` | **Witness:** the reused S2 matrices satisfy `Crosses`/`Intersects`/`Disjoint` `[exact]` | 0 |
| `RelateClothoid.v : clothoid_L_unique_on_branch` | Conditional Halley/L uniqueness on monotone clothoid branch `[exact]` | 0 |

## Issue #67 — clothoid Flocq + Halley (`ClothoidDegenerate_b64.v`, `ClothoidResidual_b64_exact.v`, `ClothoidHalley_b64.v`, `ClothoidHalley.v`)

Route **(A)** b64 mirror of the κ₀ = κ₁ = 0 degenerate residual; route **(C)**
Scope A.0–A.3 polynomial assembly (`d2`, `r2`, `f`, `f′`) matching
`clothoid-halley-coq` `Solver.cs` / `Clothoid_L.v` shape. Problem order in
oracle/docs: `(k0, k1, L)`; assembly uses `d2`, `L`, `P`, `Q`, `Rm`, `T`
only. Chord coords: `|n| ≤ 2¹¹` (`arc_coord_int_safe`); scalar moments:
`|n| ≤ 2¹²` (`clothoid_scalar_int_safe`).

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `ClothoidDegenerate_b64.v : b64_degenerate_residual_exact` | Degenerate residual `L⊗L ⊖ d⊗d` bit-exact under `coord_int_safe` `[int-b64]` | 4 |
| `ClothoidDegenerate_b64.v : b64_degenerate_root_exact` | Residual zero iff `B2R L = B2R d` (positive integer regime), composing R-side uniqueness `[int-b64]` | 4 |
| `ClothoidDegenerate_b64.v : b64_degenerate_sign_trichotomy` | Sign of degenerate residual decides exact `L` vs `d` comparison `[int-b64]` | 4 |
| `ClothoidResidual_b64_exact.v : b64_clothoid_d2_exact` | Chord squared length `d2` bit-exact from integer arc coordinates `[int-b64-arc]` | 4 |
| `ClothoidResidual_b64_exact.v : b64_clothoid_r2_exact` | Moment sum `P²+Q²` bit-exact for integer scalars `[int-b64]` | 4 |
| `ClothoidResidual_b64_exact.v : b64_clothoid_residual_exact` | Residual `L²(P²+Q²)−d2` bit-exact under scalar + chord safety `[int-b64]` / `[int-b64-arc]` | 4 |
| `ClothoidResidual_b64_exact.v : b64_clothoid_residual_prime_exact` | Derivative assembly `2L(P²+Q²)+2L²(Q·Rm−P·T)` bit-exact `[int-b64]` | 4 |
| `ClothoidResidual_b64_exact.v : b64_clothoid_residual_unit_moments` | Unit moments `P=1`, `Q=0` ⇒ residual reduces to `L⊗L⊗1 ⊖ d2` `[int-b64]` | 4 |
| `ClothoidHalley_b64.v : b64_clothoid_residual_second_prime_exact` | Second derivative `f''` assembly bit-exact under eight-scalar `clothoid_scalar_int_safe` `[int-b64]` | 4 |
| `ClothoidHalley_b64.v : b64_clothoid_halley_denom_round` | Halley denom `2f′²−f·f''` matches composed `b64_minus`/`b64_mult` round-chain under `b64_safe` premises `[round-chain]` | 4 |
| `ClothoidHalley_b64.v : b64_clothoid_halley_step_round` | Halley step `2f·f′/(2f′²−f·f'')` matches composed `b64_div` round-chain under `b64_safe` premises `[round-chain]` | 4 |
| `ClothoidHalley_b64.v : b64_clothoid_halley_l_update_converged` | Converged guard: `l_update` is a no-op when `converged_bool` is true `[structural]` | 4 |
| `ClothoidHalley_b64.v : b64_clothoid_halley_filtered_corpus_le_four` | **Conditional headline (b64 fuel model):** filtered corpus ≤4 iterations, discharged as `H_filtered_corpus_le_four` `[cond]` | 4 |
| `ClothoidHalley_b64.v : b64_degenerate_halley_fixed_at_root` | Degenerate moments: b64 Halley `l_update` is a no-op at chord root `L = d` when converged guard fires (route A + comparison bridge; explicit positive threshold premise) `[int-b64]` | 4 |
| `ClothoidHalley.v : clothoid_halley_filtered_corpus_le_four` | **Conditional headline:** filtered ProRail corpus Halley solve uses ≤4 iterations, discharged as `H_filtered_corpus_le_four` (witness: `golden_vectors.json`) `[cond]` | 0 |
| `ClothoidHalley.v : degenerate_halley_fixed_at_root` | Degenerate moments: Halley update is a no-op at the chord root `L = d` (composes route A) `[exact]` | 0 |

**Open:** full `HasClothoidIntersect` evaluator (transcendental Fresnel).

## Issue #67 — clothoid×line regime→witness (`RelateMatrixClothoid.v`, S10b)

`clothoid_fill` selects the S10b witness matrices.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateMatrixClothoid.v : clothoid_fill_proper_cross_witness` | **Witness:** `Crosses` + `Intersects` on `clothoid_fill CLR_ChordProperCross` `[exact]` | 0 |
| `RelateMatrixClothoid.v : clothoid_fill_disjoint_witness` | **Witness:** `Disjoint` on `clothoid_fill CLR_ChordDisjoint` `[exact]` | 0 |
| `RelateMatrixClothoid.v : clothoid_fill_share_witness` | **Witness:** `Intersects` on `clothoid_fill CLR_ChordShare` `[exact]` | 0 |

## Issue #67 — oracle `RELATE_MATRIX` driver (S11)

Hand-rolled pinned-matrix catalog + `DE9IM.v` predicate engine in
`oracle/relate_matrix.ml`; wired as `RELATE_MATRIX` (9-char lookup) and
`RELATE_PREDICATE` (TRUE/FALSE) modes in `oracle/driver.ml`. Not geometry
computation — full RelateNG noding remains S13+.

| Artifact | Role |
|---|---|
| `oracle/relate_matrix.ml` | Catalog keys (COQ / FILL aliases) + `predicate_holds` mirror |
| `oracle/test_relate_matrix.ml` | Catalog length + Romanschek / area / fill predicate pins |
| `oracle/relate_matrix_fill_vocabulary.txt` | Seven fill APIs → witness matrix mapping |
| `oracle/de9im_*_vectors.txt` | Per-regime COQ + MATRIX pins for NTS/JTS diff |

## Issue #67 — curve-polygon×point: validity + witnesses (`RelateCurveAreaPoint.v`, S12)

First curve-polygon relate slice: axis-aligned rectangle as a four-chord
`COMPOUNDCURVE`. The curve-specific content is the structural-validity spine;
the Contains/Touches witnesses are S4's, reused as constant facts. This file
does **not** bridge the curve geometry's point set to `rect_polygon`, so it
makes no curve→matrix claim; the `to_geometry` ↔ `rect_polygon` bridge is
deferred (S12b).

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateCurveAreaPoint.v : valid_rect_curve_polygon` | **Geometry:** chord rect COMPOUNDCURVE satisfies `valid_curve_polygon` `[exact]` | 0 |
| `RelateCurveAreaPoint.v : rect_curve_linearised_ring_closed` | **Geometry:** `chord_approx_ring` of the rect curve outer is `ring_closed` `[exact]` | 0 |
| `RelateCurveAreaPoint.v : cap_matrix_rect_contains_point_witness` | **Witness:** the reused S4 matrix satisfies `Contains` `[exact]` | 0 |
| `RelateCurveAreaPoint.v : cap_matrix_rect_touches_boundary_witness` | **Witness:** the reused S4 matrix satisfies `Touches` `[exact]` | 0 |

## Issue #67 — curve-polygon×point regime→witness (`RelateMatrixCurveAreaPoint.v`, S12)

`curve_point_fill` selects the S12 / S4 witness matrices.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateMatrixCurveAreaPoint.v : curve_point_fill_contains_witness` | **Witness:** `Contains` on `curve_point_fill CPR_StrictInterior` `[exact]` | 0 |
| `RelateMatrixCurveAreaPoint.v : curve_point_fill_touch_witness` | **Witness:** `Touches` on `curve_point_fill CPR_LeftBoundaryTouch` `[exact]` | 0 |
| `RelateMatrixCurveAreaPoint.v : strict_interior_not_left_boundary_touch` | **Geometry:** strict interior excludes left-boundary touch `[exact]` | 0 |

## Foundational — squared distance / degenerate cases (`Distance.v`)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Distance.v : dist_sq_nonneg` | Squared distance ≥ 0 `[exact]` | 3 |
| `Distance.v : dist_sq_zero_iff_eq` | Squared distance = 0 ⇔ points coincide `[exact]` | 3 |
| `Distance.v : dist_le_iff_dist_sq_le` | Distance compare ⇔ squared-distance compare (justifies sqrt-free fast path) `[exact]` | 3 |

Unconditional exact-reals — the most directly citable rows.
| `HexagonNesting.v : hex_point_in_ring` (+ `hex_ring_simple`) | **Convex hexagon parity (Stage C, unconditional):** `point_in_ring (2,1) hex_ring` for a concrete convex 6-gon by ray-parity edge enumeration (one slanted edge crossed -> odd); the hexagon is also `ring_simple` `[exact]` | 3 |
| `HexagonNesting.v : valid_polygon_hexagon_with_hole` (+ `hole_inside_outer_hexagon`) | **Convex 6-gon with a hole is `valid_polygon`:** second concrete convex `hole_inside_outer` instance beyond the diamond, assembled via `polygon_valid_of_rings`; general convex still pending the convex-chain monotonicity lemma `[exact]` | 3 |
| `ConvexNesting.v : hole_inside_outer_convex_guarded` (+ `convex_interior_parity`) | **General convex hole_inside_outer, guarded:** any hole with a vertex strictly inside a convex outer (`0 < conv_min hps`, general position) nests inside, conditional on ONE named residual `convex_interior_parity` (the convex-chain monotonicity that `convex_parity_seam_offring_of` also leaves open). Concrete convex families discharge it; general n-gon pending `[cond]` | 3 |
| `MonotoneChainParity.v : inc_chain_le_one_cross` (+ `dec_chain_le_one_cross`) | **Convex-chain monotonicity, rung 1 — the n-independent crossing core:** a y-monotone (strictly increasing, resp. decreasing) connected edge chain is crossed by the rightward ray **at most once**. An up-edge can only be crossed through the `py a < py p < py b` disjunct of `edge_crosses_ray`; strict monotonicity makes the per-edge OPEN y-intervals consecutive-and-disjoint, so two crossed edges would put `py p` in two disjoint intervals (`lra`) — no x-arithmetic, no per-vertex case blow-up. The reusable foundation for discharging `ConvexNesting.convex_interior_parity` on a general convex n-gon (rung 2: convex ring splits into two monotone chains; rung 3: interior ⇒ exactly one rightward crossing ⇒ `point_in_ring`). List induction, pure `R` `[exact]` | 3 |
| `MonotoneChainParity.v : ray_parity_count` (+ `edge_crosses_ray_dec`, `cross_count_app`) | **Crossing-parity ↔ numeric count bridge (reusable corpus-wide):** `edge_crosses_ray` is decidable (`Rlt_dec` on each strict inequality), so a list's crossings can be COUNTED (`cross_count := length ∘ filter`), and `ray_parity_odd p es ↔ Nat.odd (cross_count p es) = true` (resp. even). Turns the mutually-inductive `ray_parity_odd/even` parity — the engine behind every `point_in_ring` proof — into ordinary `Nat` arithmetic, with `cross_count` additive over `++`. The lever that lets a chain decomposition be assembled by counting rather than by hand-enumerating edges `[exact]` | 3 |
| `MonotoneChainParity.v : bimonotone_split_parity` (+ `inc_cross_count_le_one`, `dec_cross_count_le_one`) | **Convex-chain monotonicity, rung 2 — the bimonotone-split assembly:** if a ring's edges split into an increasing chain followed by a decreasing chain (`ring_edges r = inc ++ dec`), then `point_in_ring p r` holds **iff exactly one of the two chains is crossed** by the ray (`chain_crossed inc` XOR `chain_crossed dec`). Each chain contributes at most one to `cross_count` (rung 1), so the ring is crossed 0/1/2 times and the parity is odd exactly when precisely one chain is hit (rung-1 + the §6 count bridge + `lia`). Reduces general convex `point_in_ring` to the two clean rung-3 residuals: (a) convexity yields such a split; (b) a strictly-interior point hits exactly one chain `[exact]` | 3 |
| `ConvexChainSplit.v : convex_interior_parity_from_split` (+ `hole_inside_outer_convex_via_split`) | **Convex-chain monotonicity, rung 3 — conditional closure of `convex_interior_parity`:** given a bimonotone split (`bimonotone_split outer inc dec`) and the one-chain property (`interior_hits_one_chain`), `convex_interior_parity` follows in one line from `bimonotone_split_parity`. Names the two structural residuals exactly; connecting `conv_min > 0`/`vertices_in_halfplane` to vertex ordering is the ONLY remaining open lemma of the campaign, isolated here. `hole_inside_outer_convex_via_split` composes with `hole_inside_outer_convex_guarded` to give `hole_inside_outer` from the split `[exact]` | 3 |
| `ConvexChainSplit.v : diamond_point_in_ring_via_split` (+ `diamond_bimonotone`, `diamond_inc_crossed`, `diamond_dec_not_crossed`) | **Concrete diamond witness — full pipeline exercised end-to-end:** CCW diamond ring `(0,±2),(±2,0)` split into two 2-edge chains; test point `(0,1/2)` crosses exactly the increasing (right) chain and misses the decreasing (left) chain; `bimonotone_split_parity` + the crossing arithmetic gives `point_in_ring` in 3 steps, no Admitted. Non-vacuous exercise of the full rung-1/2/3 stack `[exact]` | 3 |
| `YMonotoneSplit.v : ring_edges_split_at` (axiom-free) | **The `ring_edges` seam lemma:** the consecutive-pair edge list of `pre ++ peak :: suf` equals `ring_edges (pre ++ [peak]) ++ ring_edges (peak :: suf)` — splitting a vertex list at a vertex splits its edge list at the corresponding seam, the shared vertex meeting the two parts. The foundational vertex-ordering fact the corpus lacked; **Closed under the global context** (zero axioms) `[exact]` | 3 |
| `YMonotoneSplit.v : y_unimodal_bimonotone_split` (+ `chain_increasing_ring_edges`, `chain_decreasing_ring_edges`, `y_unimodal_point_in_ring`) | **Y-monotone split — the structural half of `interior_hits_one_chain`:** a `y_unimodal` ring (vertex y's rise strictly to a single peak, then fall strictly) admits a `MonotoneChainParity.bimonotone_split`: the prefix-to-peak edges form a `chain_increasing`, the peak-onward edges a `chain_decreasing` (via `ring_edges_split_at` + a strictly-monotone vertex run yielding a monotone edge chain). Discharges residual (a) of the convex campaign for the y-unimodal class — every convex polygon traversed from its min-y vertex is y-unimodal; reusable for any y-monotone-decomposable simple polygon. `y_unimodal_point_in_ring` composes with rung 2 for the XOR parity characterisation `[exact]` | 3 |
| `YMonotoneSplit.v : ym_diamond_bimonotone_split` (+ `ym_diamond_unimodal`) | **The hand-built diamond split, re-derived from the general machinery:** `y_unimodal_bimonotone_split` reproduces `ConvexChainSplit.v`'s explicit `diamond_inc`/`diamond_dec` verbatim from `ym_diamond_unimodal` alone, with no per-edge bookkeeping — confirming the y-monotone infrastructure subsumes the concrete witness `[exact]` | 3 |
| `YMonotoneSplit.v : strict_inc_straddle_exists` (+ `strict_dec_straddle_exists`, `last_snoc`) | **Discrete IVT for y-monotone chains — rung 2 of the y-monotone split campaign:** for a strictly-increasing (resp. decreasing) vertex list with py q strictly between the first and last vertex heights and no vertex at that height, there exists an edge in `ring_edges vs` whose y-interval straddles the ray. Proved by list induction with a `Rle_or_lt` case split: if py q < py(next vertex) the first edge straddles; otherwise advance the lower bound and recurse. Combined with `inc_chain_le_one_cross` this gives EXACTLY ONE straddling edge per chain when py q is in range. Helper `last_snoc` (`last (l ++ [x]) d = x`) is axiom-free `[exact]` | 3 |
| `YMonotoneSplit.v : y_unimodal_both_chains_straddle` | **Y-unimodal straddling corollary:** for a `y_unimodal` ring with non-empty `pre` and `suf`, a generic-position point q with py strictly between the bottom and peak has a straddling edge in BOTH chains. Narrows the remaining residual of `interior_hits_one_chain` to EXACTLY the x-geometry: for a convex ring, the inc-chain straddling edge's x-intercept exceeds px q (so it IS crossed), while the dec-chain straddling edge's x-intercept is less than px q (so it is NOT crossed) `[exact]` | 3 |
