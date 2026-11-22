<!-- doc-kind: finding
date: 2026-11-22
Provenance: b1ee687
Theorems: `TaggedIntegral.v : tagged_ftc`, `TaggedIntegral.v : RInt_chasles`, `TaggedIntegralApps.v : kernel_integral`, `TaggedIntegralChange.v : RInt_bounded`, `TaggedIntegralChange.v : RInt_exp_change`, `LogRpowClean.v : Lc_le_rpc_div`, `ExpSeriesClean.v : exp_le_mono`
-->
# Alpöge audit: the reusable real-analysis tools moved into theories/

Requested: move only the tools into `theories/`. This follows the open
question in `2026-11-22-alpoge-theories-readiness.md`: the audit-specific
probes stay in `docs/h1-vacuity/`.

## Moved (5 modules, `_CoqProject.full`, `claimId: none`)

| module | from | content |
|---|---|---|
| `ExpSeriesClean` | `AlpogeRealsQED.v`, exp helpers | `exp` facts from the E1 series: monotonicity, `1 + x ≤ eˣ`, `(1−y)eʸ ≤ 1` |
| `LogRpowClean` | `AlpogeRealsQED2.v`, Part 0 | the logarithm `Lc` (by the intermediate value theorem) and the power `rpc`, with their laws |
| `TaggedIntegral` | `CleanIntegralQED.v`, Parts 0–6 (#1047) | `RInt` and `RIntInf`; linearity, monotonicity, Chasles; a mean value theorem by bisection; FTC; change of variables |
| `TaggedIntegralApps` | `CleanIntegralQED.v`, Parts 7–9 | `Lc′ = 1/y`; the window integrals; `kernel_integral` |
| `TaggedIntegralChange` | `AlpogeSixthBatch.v`, Part E1/E2 | `RInt_bounded`; `RInt_exp_change` (`y = eᵘ` for a merely integrable integrand) |

Stdlib's `ln`, `Rpower`, `exp_increasing`, `RiemannInt`, `MVT`, `Rolle` and
`Heine` all print `Classical_Prop.classic`. These modules use none of them.
Every `Print Assumptions` is within the corpus allowlist.

The declarations are unchanged, apart from renames the name-shape gate
requires in `theories/`:
- `FTC*` → `tagged_ftc*`;
- `E1_term_nonneg` → `e1_term_nonneg`;
- the four `Lc_*` IVT helpers, whose statements do not mention `Lc`, are
  renamed `exp_sub_const_cont`, `neg_inv_lt_self`, `exp_neg_inv_sub_neg` and
  `exp_sub_self_pos`;
- `deriv_nonneg_incr` → `deriv_nonneg_incr_mvt`. It clashed with
  `RealMonotone.v`.

## The probes

- `AlpogeRealsQED.v` and `AlpogeRealsQED2.v` `Require Export` the new
  modules.
- `CleanIntegralQED.v` keeps only Part 10, `windowHyp_of_rpow_r` (WindowHypR
  is audit-specific), and `Require Export`s the integral modules.
- `AlpogeSixthBatch.v` keeps E3, `windowHypU_of_windowHyp_R`.

Downstream probes compile unchanged, except for the renamed `FTC_C1`
(`AlpogeFifthBatch`) and the skeleton's qualified `Check`s. All 27 probes in
the Alpöge chain build in smoke order, and their axiom audits pass.

Gates:
- **name-shape:** matches its registry;
- **module-split, constructor gate:** pass;
- **README counts:** bumped to 841 registered modules, 696 under `theories/`;
- **`make ci-guards` and doc-kinds:** OK.

## OUTCOME

**QED (moved).** The tools are product modules; the audit evidence stays in
the probe lane. The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 5 / warn 0 / bug 0.**
