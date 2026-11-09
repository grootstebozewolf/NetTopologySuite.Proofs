| rung | claim | OUTCOME | artifact (docs/h1-vacuity/) |
|---|---|---|---|
| 0 | pure carry_clean on a Priest chain preserves nonoverlap | QED, vacuous (chain is a normal form) | `CarryCleanPure.v : carry_clean_pure` |
| 1 | strict look-ahead `\|h\| < ulp(g_next)` on Priest input | QEX (equality, binary64) | `LookaheadQEX.v : lookahead_strict_false` |
| 2 | unconditional lattice route to the 2-ulp tail bound | QEX for the route (bound holds) | `LatticeRouteQEX.v : lattice_route_false` |
| 3 | tail bound `\|Q_(k-1) - g_(k-1)\| <= 2 ulp(g_k)`, any length (FLX) | QED | `CascadeTailBound.v : cascade_tail_bound` |
| 4 | same bounds on `b64_grow_expansion_aux` / `fast_expansion_sum` | QED | `CascadeTailBound.v : b64_cascade_tail_bound, fes_output_error_bound` |
| 5 | N -> T entry; `2^M - 2*2^c <= \|g_next\|` | QED | `CascadeInvariant.v : N_to_T_entry` |
| 6 | N step on reachable states: N -> N or N -> T | QED | `CascadeInvariant.v : N_step_reachable, N_step_actual` |
| 7 | `cascade_step_obligation` over arbitrary states | QEX (false); `cascade_aligned_shape` vacuous | `CascadeInvariant.v : cascade_step_obligation_false` |
| 8 | T -> {N, P} (anti/single -> N, pending twin -> P) on reachable states | QED | `CascadeInvariant.v : cinv_T_step, T_step_reachable` |
| 9a | P -> N: a pending twin settles in exactly one step, never P again | QED | `CascadeInvariant.v : cinv_P_step, P_step_reachable, pending_twin_settles` |
| 9b | global induction: output of the real run has the aligned carry shape; `carry_clean (fast_expansion_sum e f)` nonoverlapping (nonzero Priest inputs) | QED | `CascadeInvariant.v : cascade_stage_invariant, cascade_reachable_shape, fes_carry_clean_nonoverlap` |
| 9d | zero inputs + uniqueness of block decompositions: `fes_priest_carry_pattern`, `fes_priest_reduction_nonoverlap`, `carry_clean_priest_target` for ALL Priest inputs | QED | `ZeroElim.v : fes_priest_carry_pattern_proved, fes_priest_reduction_nonoverlap_proved, carry_clean_priest_target_proved` |
| 9c | non-vacuity: Priest pair whose run is T -> P -> N (errors `-2^-54, -2^-53, 1, 0, 1`) | QED | `PendingTwinWitness.v : pending_twin_witness, pending_twin_witness_settles` |
