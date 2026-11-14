<!-- doc-kind: finding
date: 2026-11-10
Provenance: d8941061bdb7355a2635f68460b198d545b70521
Theorems: `Orient_b64_grid_cc.v : b64_orient_sign_exact_cc_grid_sound`, `Orient_b64_grid_cc.v : orient2d_grid_hyps`, `Orient_b64_grid_cc.v : b64_orient_sign_stage_d_cc_int_sound`, `Orient_b64_grid_cc.v : cc_domain_diffs_not_exact`, `Orient_b64_grid_cc.v : cc_domain_underflow`
-->
| step | claim | OUTCOME | artifact |
|---|---|---|---|
| 0 | derive Stage D's per-operation hypotheses from `\|coord\| ≤ 2^507` alone | QEX: exactness fails (`P0.x = 2^-60`, `P1.x = 1`); no-underflow fails (coordinates `2^-600`) | `Orient_b64_grid_cc.v : cc_domain_diffs_not_exact, cc_domain_underflow` |
| 1 | domain: one shared binary lattice `n·2^k`, `\|n\| < 2^52`, `-484 ≤ k ≤ 426` (sharing `k` is free; the restriction is the coefficient bound, i.e. dynamic range; owner-approved shape; ceiling 426 not 455 because the per-step Dekker bounds are crude) | definition | `Orient_b64_grid_cc.v : orient2d_inputs_on_grid` |
| 2 | exact differences on the grid | QED | `grid_minus` |
| 3 | Dekker overflow safety from one magnitude bound per step | QED | `b64_Dekker_safe_of_bound` |
| 4 | Dekker no-underflow on the grid (`2^(2k) ≥ 2^-968`) | QED | `grid_no_underflow` |
| 5 | grid implies domain + `b64_orient2d_expansion_cc_safe`; decoder sound and definite | QED | `orient2d_grid_hyps`, `b64_orient_sign_exact_cc_grid_sound` |
| 6 | integer regime = grid `k = 0`; full Stage D decoder needs only `orient2d_inputs_int_safe` | QED | `int_safe_on_grid`, `b64_orient_sign_stage_d_cc_int_sound` |
| OUTCOME | the magnitude bound alone is QEX; the common grid supplies every hypothesis | QED | this table |
