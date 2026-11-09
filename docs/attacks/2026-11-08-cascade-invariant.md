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
| 9a | P -> N: a pending twin settles in exactly one step (no persistence) | QED | `CascadeInvariant.v : cinv_P_step, P_step_reachable, P_last_step, pending_twin_settles` |
| 9b | one reachable-state induction chaining N/T/P steps | OPEN | — |

OUTCOME: QED (rung 9a). A Priest-valid pending twin cannot remain pending:
`cinv_P` forces `|h| = 2^c < ulp(g)/4`, so `TwoSum(g,h) = (g,h)` exactly and
the next state is `cinv_N` (block `CTwin h`, keys `2^(c+1) < ulp(g) <= ulp(g_next)`).
Settling time is exactly 1; the quantity consumed is the tiny accumulator
itself (Q' = g afterwards). `cinv_P` needed no strengthening: its look-ahead
conjunct is what `T_step_reachable` already proves at p = 53. Axioms: corpus
standard (Reals, funext, classic). No bounded search was used or needed.
Reproduce: `scripts/hunt_probe_smoke.sh` (compiles CascadeInvariant.v).
