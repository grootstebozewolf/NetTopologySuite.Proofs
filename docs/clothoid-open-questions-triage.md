# Clothoid lane — what is proved, what transports, what is open

> **Status:** living page for the clothoid lane, the main curve push. Claims of
> record are rows in [`verified-claims.md`](verified-claims.md) and pinned
> statements in [`claim-statements.json`](claim-statements.json); this page
> orders them and names the open work. Refresh it when a clothoid module lands.
> The 2026-06-12 route sessions (A–D, §3) are in git history; their outcomes
> are the module headers.

## 1. The object

A **constructive clothoid** with scale `A` is the unit-speed curve
`c(t) = (∫₀ᵗ cos(τ²/2A²) dτ, ∫₀ᵗ sin(τ²/2A²) dτ)`: heading `t²/2A²`,
curvature `t/A²`, linear in arc length (an Euler spiral).

- **Host egg** (`SheetHenClothoidCore.v : ClothoidEgg`): inflection-placed, in
  a frame `AffPlace` read as rigid or reflected (location, the *direction* of
  `ref1`, the sign of `cross(ref1, ref2)`), with `A`, a window `[sd, ed]` and
  optional measures. Evaluation is the Fresnel integral on `LipInt` (#883),
  three axioms; FTC `lipint_ftc` (#889) and Leibniz `lint_leibniz` (#896) make
  Coquelicot unnecessary for values and derivatives (ADR-0001).
- **Placed clothoid** (`ClothoidPlacement.v : placed`): `o + M c(t)` for any
  2×2 `M`, the ISO / GEOS frame `[u v]`. A similarity `M = λR` is a host
  clothoid; `det M ≠ 0` with `M` not a similarity is a **sheared clothoid**, an
  affine image of an Euler spiral and not an Euler spiral
  (`cloth_shear_law_claim`).

## 2. Representations onto the host egg

| Source | Carrier | Normaliser | Declines / notes |
|---|---|---|---|
| ISO 19107 / GML `Clothoid` (inflection-placed) | `IsoClothoid` | `IsoClothoidIntake.v : try_iso_clothoid`, field copy | tilted refs, non-similarity frame (`shear_try`: `ICF_NotSimilarityFrame`), `A ≤ 0`, `sd = ed`, measure mismatch. `sd`, `ed` read as arc length from the inflection (GML uses the normalised Fresnel parameter, `s = A√π t`) |
| SQL/MM `SPIRALCURVE` clothoid (start-placed) | `SpiralClothoid` | `IntakeSpiralFront.v : try_spiral_clothoid` via normaliser 2 (`ClothoidNorm2.v : clothoid_state_unique`, claim `0007-norm2-state`) | `iso_spiral_same_curve` ties the two forms |
| JTS `CLOTHOID (k0, k1, L)` | triple | `IntakeSpiralJts.v` | only the `example5` triple `(0, 0.005, 80)`; others `ID_JtsClothoidNotYet` |
| GEOS `Clothoid` (`o`, `u`, `v`, `A`, `t0`, `t1`) | `placed o M` | none: external placement, GEOS #1566 fixtures (`geos_shear_*`) | the host given GEOS's frame directly ignores the shear (`host_affplace_curvature_ignores_shear`) |

All intake ends in one `MkClothoid` egg (`ticket_0007_intake_mkclothoid_qed_or_qex`,
claim `0007-intake-mkclothoid`); no silent chord demote.

## 3. What is proved, by layer

Three axioms, no `Admitted`. **U** = unconditional (domain premises only);
**C** = conditional on a named premise.

| Layer | Modules | Headline | |
|---|---|---|---|
| Fresnel window | `ClothoidFresnel.v`, `ClothoidFresnelInhab.v` (claim `508-e`) | `fresnel_discharges_clothoid_window` | C on `fresnel_primitives`; the `Inhab` inhabitant is `RiemannInt`, Category-C |
| Bounds, tangent | `SheetHenClothoidBounds.v`, `ClothoidTangent.v`, `ClothoidFresnelInc.v` | `cloth_unit_speed`, `cloth_Cx_half_lt` | U |
| Traversal | `ClothoidTraversal.v` | `cloth_arc_unit_speed_linear_curvature`, `cloth_eval_fresnel_form`, `cloth_split_traversal_law` | U |
| Placement | `ClothoidPlacement.v` | `cloth_placed_curvature`, `cloth_similarity_scaled_law`, GEOS #1566 enclosures | U |
| Affine closure | `ClothoidAffine.v` (`cloth-affine-closure`) | `cloth_affine_claim` | U |
| Shear law | `ClothoidShearLaw.v` (`cloth-linear-law-iff-similarity`) | `cloth_shear_law_claim` | U |
| Change of sheet | `ClothoidSheet.v` (`cloth-sheet-transport`), `SheetRingPip.v` (`sheet-pip-transport`) | `cloth_sheet_claim`, `sheet_pip_claim` (§5) | U |
| Cook (ADR-0007) | `ClothoidCookMkClothoid.v` (`0007-clothoid-first-cook`), `SidecarClothoidEgg.v` (`0007-clothoid-egg`) | `ticket_0007_clothoid_first_cook_qed_or_qex`: locked clothoid × clothoid Hit | U; Fresnel-as-noding parks (QEX) |
| Linearise, chord | `ClothoidLinearizeContract.v` (`0007-clothoid-linearize`), `ClothoidChordRho.v` (`0007-clothoid-chord-rho`), `ClothoidEnvelope.v` (`0007-clothoid-envelope`), `ArcChordDensity.v` | `clothoid_linearizes` (tol `κmax·h²/8`), `clothoid_chord_rho`, `clothoid_envelope`, `n_chords_achieve_eps` | U |
| Length | `ClothoidLengthAbs.v` (`0007-clothoid-length`), `ClothoidLength.v` | `clothoid_length_abs`; `clothoid_arclength_is_curve_length` | U; C on `H_unit_chord`, `H_unit_approx` |
| Offset, buffer | `ClothoidOffsetContact.v`, `ClothoidBufferBridge.v`, `ClothoidBufferAssembly.v` | `clothoid_buffer_assembly_sound`, `clothoid_offset_below_min_radius_fails` | U |
| Residual | `ClothoidResidual.v`, `ClothoidDegenerate.v`, b64 mirrors | `clothoid_residual_unique_root_half`, `degenerate_unique_positive_root`; `clothoid_residual_unique_root` | U; C on `ClothoidFPrimePos` |
| Halley | `ClothoidHalley.v`, `ClothoidHalley_b64.v` | `clothoid_halley_filtered_corpus_le_four` | C on `H_filtered_corpus_le_four` |
| Relate | `RelateClothoid.v`, `RelateMatrixClothoid.v` | `clothoid_L_unique_half_branch`, `clothoid_fill_*` | U; on-branch C |

## 4. The three original questions

1. **Fresnel support.** On the R side the host eval *is* the Fresnel integral,
   with FTC and Leibniz in the corpus. The half branch is discharged
   (`clothoid_fprime_pos`); the full branch `|κL| ≤ π` stays the named premise
   `ClothoidFPrimePos`, witnessed externally in
   [`clothoid-halley-coq`](https://github.com/grootstebozewolf/clothoid-halley-coq).
   There is no binary64 Fresnel evaluator.
2. **Exact integer regime.** Bit-exact end to end is impossible (the Fresnel
   stage is transcendental). Exact where it can be: the straight-chord regime
   and the Scope-A polynomial prefix of the residual given oracle `P`, `Q`.
3. **Performance vs. linearisation.** Not a theorem. Fidelity is proved
   (`Linearise.v`, `CurveLinearise.v`, `clothoid_linearizes`); the provable face
   of the trade-off is the chord-count bound. Throughput is NTS.Curve
   benchmarking.

| Route | Content | Landed in |
|---|---|---|
| (A) | degenerate-chord exact regime | `ClothoidDegenerate.v`, `ClothoidDegenerate_b64.v` |
| (B) | sagitta-density bound, equal-angle budget | `ArcChordDensity.v`, `ArcChordSubdivision.v` |
| (C), (C′) | Scope-A residual assembly; conditional Halley bound and step | `ClothoidScopeA_b64.v`, `ClothoidResidual_b64_exact.v`, `ClothoidHalley.v`, `ClothoidHalley_b64.v` |
| (D) | full Fresnel internalisation | open: only `ClothoidFPrimePos` remains (ADR-0001) |

## 5. Shear: what transports along a change of sheet

A shear is a change of sheet `S → S′ = (f O; L e₁, L e₂)` (ADR-0007), `det L ≠ 0`.

- **Exactly:** the representation `(o, M) ↦ (f o, L M)` with split, reverse
  and demote; the clothoid × clothoid oracle (Hit keeps `(tᵢ, tⱼ)` and maps
  `p*` to `f p*`, Empty and Decline stay); noding lists; tangency; split
  vertices; on-boundary location; orientation, which flips iff `det L < 0`.
- **Point location:** the canonical east-ray test agrees on both sheets for
  seam rings (taut, proper, no horizontal edge on either sheet), through the
  affine-invariant topological interior and `parity_seam_offring_taut`.
- **Cook on `S′`:** pull back, host cook, push forward; correct on one common
  frame `(o, M)`. Two different shears decline: pulling one back leaves the
  other sheared.
- **Not at all:** the linear curvature law; distances, length, buffer and
  Hausdorff (only bounded by `σ_min(L)`, `σ_max(L)`); snap rounding (unless `L`
  is a signed permutation and the shift is on the grid); vertex identity in
  doubles (`coord_eq_not_hen_eq`).

## 6. Open work, ranked

1. **Frame scale at intake.** `similarity_ok` accepts refs orthonormal up to a
   common scale `λ`, but the host reads only the direction of `ref1`
   (`cloth_cos0 = ref1 / |ref1|`), so a frame with `|ref1| = |ref2| = λ ≠ 1` is
   evaluated at scale 1, where GEOS (`P = o + A C₂ u + A S₂ v`) scales by `λ`.
   Same mechanism as `host_affplace_curvature_ignores_shear`. Fix by absorption
   (item 2), or decline `λ ≠ 1`.
2. **Similarity absorption.** `λ c_A(t) = c_{λA}(λt)`: a similarity placement
   is a host egg with `A` and the window scaled. Also lets the sheet cook take
   frames that differ by a similarity.
3. **Placed length.** `∫ |M c′|` has no closed form under shear. Cheap rung:
   `σ_min (t₁ − t₀) ≤ length ≤ σ_max (t₁ − t₀)`; then tight enclosures (GEOS
   `getLength` integrates across the inflection).
4. **Sheared intake.** A non-similarity frame could become a placed clothoid
   `(o, M)` instead of `ICF_NotSimilarityFrame`; `det M = 0` must still be
   refused (GEOS #1566 accepts collinear frames).
5. **Clothoid × sheared-clothoid oracle**, the only way past "different shears
   decline".
6. **Metric operations on `S′`**: distance, nearest point and buffer computed
   on the target sheet; the GEOS one-root certificate needs its `σ_max(M)`
   derivative bound proved.
7. **Far-field Fresnel quadrature.** GEOS uses 0.5-wide 16-point
   Gauss–Legendre panels past the series window; the corpus has no
   Gauss–Legendre remainder theorem.
8. **Route (D)**, the full branch `ClothoidFPrimePos`.
9. **Point location beyond seam rings** (horizontal edges, T-touches): needs
   the escape half of the Jordan seam beyond taut rings.
10. **Parked:** Z / M placements; the CompoundCurve junction snap (GEOS 458f82e);
    clothoid × chord and other mixed cooks.

## 7. Oracle and tooling

- `oracle_bin` (ADR-0006) has no clothoid op. A clothoid enters as the `K`
  token of `LENGTH_UNIFIED` (length `ed − sd`), as `clothoid_fill` regimes in
  `RELATE_MATRIX` (`oracle/de9im_clothoid_vectors.txt`), and as `CLOTHOID` /
  `SPIRALCURVE` in `SQLMM_WKT` parsing.
- Differential harnesses: `tests/CurveOracleBugHunt` (NTS) and
  `tests/GeosOracleBugHunt` (GEOS). `tools/WktUnicodeIllustrator` draws curve
  WKT against the sibling NTS curves branch and exits 4 rather than draw a
  chord in a lines-only build.
- Data: the 9,058-record `golden_vectors.json` of the companion repo (CC BY 4.0,
  derived from ProRail Spoorgeometrie).
