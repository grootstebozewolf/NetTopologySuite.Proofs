<!-- doc-kind: finding
date: 2026-11-22
Provenance: d9790d4a (Alpöge third batch, merged into this branch) · Rocq 9.2 / rocq-stdlib 9.2 (nts-flocq switch)
Theorems: `CleanIntegralQED.v : RInt_unique`, `CleanIntegralQED.v : RInt_lin`, `CleanIntegralQED.v : RInt_scal`, `CleanIntegralQED.v : RInt_le`, `CleanIntegralQED.v : RInt_chasles`, `CleanIntegralQED.v : mvt_ge`, `CleanIntegralQED.v : FTC_value`, `CleanIntegralQED.v : FTC`, `CleanIntegralQED.v : RInt_change_var`, `CleanIntegralQED.v : RIntInf_chasles`, `CleanIntegralQED.v : Lc_deriv`, `CleanIntegralQED.v : window_integral`, `CleanIntegralQED.v : window_integral_rpow`, `CleanIntegralQED.v : windowU_change_var`, `CleanIntegralQED.v : kernel_integral`, `CleanIntegralQED.v : windowHyp_of_rpow_r`
-->
# An allowlist-clean integration library over Stdlib's reals; `kernel_integral` and `windowHyp_of_rpow` proved

The third Alpöge batch
(`docs/attacks/2026-11-21-alpoge-third-batch-over-reals.md`) stopped at 7
refined lemmas because Stdlib's integral theory carries
`Classical_Prop.classic`. This probe builds the missing library inside the
three-axiom allowlist (`docs/axiom-allowlist.txt`). It then uses the library
to prove the two requested checks, plus one more lemma.

Probe: `docs/h1-vacuity/CleanIntegralQED.v`, listed in
`scripts/hunt_probe_smoke.sh`. NOT a product module.

## What Stdlib offers (`Print Assumptions`, Rocq 9.2)

| clean (used) | carries `Classical_Prop.classic` (avoided) |
|---|---|
| `derivable_pt_lim_{plus,minus,opp,mult,scal,id,const,pow,comp,exp}`, `completeness`, `archimed`, `archimed_cor1`, `Rle_dec`, `Rlt_dec`, `IVT`, `RiemannInt_SF`, `StepFun_P4`, `continuity_pt_mult`, `derivable_continuous_pt` | `RiemannInt`, `RiemannInt_P10`, `ln`, `Rpower`, **`MVT`, `MVT_cor1`, `MVT_cor2`, `Rolle`**, **`Heine`, `compact_P3`**, `continuity_ab_maj`, `derive_increasing_interv`, `nonneg_derivative_1`, `null_derivative_loc` |

Every mean value theorem in Stdlib is unusable, and so is uniform continuity
on compacta. The library therefore proves its own mean value result (Part 4)
and takes uniform continuity as a hypothesis.

## The library (Parts 1–6, Stdlib only)

| part | content |
|---|---|
| 1 | **Definition.** `RInt f a b I := a ≤ b ∧ ∀ε>0 ∃δ>0`: every tagged partition of `[a,b]` with mesh `< δ` has a tagged sum within `ε` of `I`. This is Riemann's definition with a mesh condition. A partition is a list of `(tag, right end)` cells. It uses neither step functions nor `RiemannInt`. Fine partitions exist (`exists_fine`, uniform partitions via `archimed_cor1`). |
| 2 | `RInt_unique`, `RInt_plus`, **`RInt_scal`** (`c·f` is integrable without `RiemannInt_P10`), `RInt_opp`, `RInt_minus`, `RInt_lin`, `RInt_const`, `RInt_ext`, **`RInt_le`** (monotonicity), `RInt_nonneg`, `RInt_abs_bound`. |
| 3 | **`RInt_chasles`**: `RInt f a b I₁ → RInt f b c I₂ → RInt f a c (I₁+I₂)` for `f` bounded on `[a,c]`. A fine partition of `[a,c]` is split at `b`. Only the straddling cell changes the sum, by at most `2Mδ`. |
| 4 | **One-sided MVT by bisection** (`mvt_ge`, `mvt_le`): for `x < y` with `F' = f` on `[x,y]`, there is `c ∈ [x,y]` with `(F y − F x)/(y − x) ≤ f c`, and dually. Each step keeps the half on which the difference quotient stays `≥ q`; the choice is one `Rle_dec`. The limit point comes from `completeness`. A derivative estimate at `c` then gives `q ≤ f c + ε` for every `ε`. Corollaries: `mvi_upper`, `mvi_lower`, `mvi_abs`, `deriv_nonneg_incr`, `Lip_of_deriv`. |
| 5 | **FTC.** `FTC_value`: `RInt f a b I` and `F' = f` on `[a,b]` give `I = F b − F a`, for *any* Riemann-integrable `f`. The proof re-tags a fine partition with `mvt_ge` / `mvt_le` points. `FTC`: `F' = f` with `f` uniformly continuous on `[a,b]` gives `RInt f a b (F b − F a)`. The variants are `FTC_Lip` (Lipschitz `f`) and `FTC_C1` (`f` has a derivative bounded on `[a,b]`). |
| 6 | **Change of variables.** `RInt_change_var` gives `∫_{φa}^{φb} f = ∫_a^b f(φu)φ'(u) du` when `f` has an antiderivative on `[φa, φb]`. `RInt_change_var_FTC` adds that both sides exist for uniformly continuous integrands. **Improper integrals.** `RIntInf f a I` means `∫_a^T f → I` as `T → ∞`, with `∫_a^T` existing for all large `T`. Lemmas: `RIntInf_unique`, `_plus`, `_scal`, `_le`, **`RIntInf_chasles`** (`∫_a^∞ = ∫_a^b + ∫_b^∞`, which splits off a finite interval), and `RIntInf_of_antideriv`. |

## The checks (Parts 7–10, with the clean `exp` / `Lc` / `rpc` of `AlpogeRealsQED2.v`)

| statement | proof |
|---|---|
| `Lc_deriv`: `Lc' = 1/y` on `(0,∞)` | Elementary, with no inverse-function theorem. From `Lc z ≤ z − 1` and `Lc_mult`: `h/(y+h) ≤ Lc(y+h) − Lc y ≤ h/y`. |
| **`window_integral`**: `∫_Y^{Y^{1+δ}} dy/y = δ·Lc Y` (`1 ≤ Y`, `0 ≤ δ`) | `FTC_Lip` with antiderivative `Lc`; `1/y` is 1-Lipschitz on `[1,∞)`. |
| `window_integral_rpow` | The same value for the integrand `y^θ · y^{−θ−1}`, which is the shape `windowHyp_of_rpow` integrates. |
| `window_integral_by_cv` | The same value through `y = e^u` (`RInt_change_var`, u-integrand `≡ 1`). |
| `windowU_change_var` | The `y = e^u` identity of `windowHypU_of_windowHyp`: `∫_Y^{Y^{1+δ}} R(y) y^{−θ−1} dy = ∫_{Lc Y}^{(1+δ)Lc Y} R(e^u) e^{−θu} du`, for majorants `R` whose y-integrand has an antiderivative on the window. |
| **`kernel_integral`**: `RIntInf (u ↦ u^k e^{−au}/k!) 0 (a^{−(k+1)})` for `a > 0` | Antiderivative `G(u) = −a^{−(k+1)} e^{−au} P_k(au)`, where `P_k(x) = Σ_{j≤k} x^j/j!` and `P_k' = P_k − x^k/k!`. Integrability on `[0,T]` comes from `FTC_C1`. The tail: `e^x ≥ P_{k+1}(x)` (by `deriv_nonneg_incr`, induction on `k`), so `e^{−x}P_k(x) ≤ (k+1)(k+1)!/x`. |
| **`windowHyp_of_rpow_r`** (extra) | `windowHyp_of_rpow` over `R`, for `WindowHypR`, which is `WindowHyp` with the window integral an `RInt`. Majorant `|C|·y^θ`, `RInt_scal ∘ window_integral_rpow`, then `windowHyp_of_rpow_eventually` (QED2). This is the `WHR` hypothesis of `AlpogeRealsQED2.v`. |

## Effect on the 7 items the third batch could not prove

| item | status after this probe |
|---|---|
| `kernel_integral` | **proved over `R`** (`kernel_integral`) |
| `windowHyp_of_rpow` | **proved over `R`** (`windowHyp_of_rpow_r`, relative to `WindowHypR`) |
| `windowHypU_of_windowHyp` | change-of-variables identity proved for majorants with a y-antiderivative (`windowU_change_var`). A merely integrable `R` would need FTC part 1 (`x ↦ ∫_a^x f` is an antiderivative), which needs restriction to subintervals. **Not delivered.** |
| `landau_coeff` | its obstruction is gone (`RInt_scal` replaces `RiemannInt_P10`); not attempted here |
| `landau_window_ineq`, `landau_tails_chernoff` | splitting and monotonicity tools now exist (`RIntInf_chasles`, `RIntInf_le`, `RInt_abs_bound`); not attempted. The triangle inequality `\|∫f\| ≤ ∫\|f\|` needs integrability of `\|f\|`, which is not provided in general. |
| `landau_cauchy` | needs the Cauchy integral formula; out of scope |

## Limits (stated so nobody over-reads the library)

- `RInt_chasles` takes a bound on `f` as a hypothesis. "Riemann-integrable
  implies bounded" is not proved here. Neither is restriction to a
  subinterval (Cauchy criterion).
- `FTC` needs uniform continuity. Heine's theorem is not clean in Stdlib and
  is not reproved here. `FTC_value` needs no regularity but presupposes
  integrability.
- `RInt_change_var` relies on an antiderivative. It is not the general
  substitution theorem for arbitrary integrable `f`.
- `RInt` is not bridged to `IntVal` / `LaplaceAt` of
  `AlpogeDeepStatements.v`, which also require Stdlib's
  `Riemann_integrable`.

## Verification

- `rocq c -Q theories NTS.Proofs -Q theories-flocq NTS.Proofs.Flocq -Q docs/h1-vacuity NTS.Proofs.Probes docs/h1-vacuity/CleanIntegralQED.v` compiles, after `AlpogeRealsQED.v` and `AlpogeRealsQED2.v`.
- Build log with `ROCQ compile <file>` markers for that closure, run
  through `scripts/audit_axioms.sh`: **OK**. All 30 `Print Assumptions`
  blocks of the probe name only `sig_forall_dec`, `sig_not_dec` and
  `functional_extensionality_dep`. In a negative control, a
  `Print Assumptions RiemannInt_P10` log fails the audit, as it should.
- `scripts/check_admitted.sh`: OK (0 `Admitted`). The probe contains no
  `Admitted`, `admit`, `Axiom` or `Parameter`.

## OUTCOME

**QED.** There is an allowlist-clean integration library: the definition,
linearity, monotonicity, Chasles, a bisection MVT, FTC, change of variables
and improper integrals. With it, `kernel_integral`, the window integral and
`windowHyp_of_rpow` are proved over `R`. The audit is OK and there are no
`Admitted`.

The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**. Over `R`, 34 of
the 39 refined items are now proved (32 + `kernel_integral` +
`windowHyp_of_rpow`); `AlpogeSkeleton.v`'s ledger is not yet updated.

**SUMMARY ok 3 (kernel_integral, window integral, windowHyp_of_rpow) / warn 1 (windowHypU_of_windowHyp needs FTC-1 for general majorants; Chasles needs a bound hypothesis; Heine not reproved) / bug 0.**
