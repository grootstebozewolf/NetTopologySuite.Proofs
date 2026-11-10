| step | claim | OUTCOME | artifact |
|---|---|---|---|
| G0 | baseline: CI green on `main` @ `4eb6c4b` with the full corpus build and `audit_axioms.sh` | PASS (run 42722911910) | CI |
| G0 | human review of `B64_CarryCleanCascade.v` rungs 0–8 | PENDING (human gate; not cleared here) | `B64_CarryCleanCascade.v` header |
| 1 | Dekker/TwoProduct pairs entering Stage D are Priest chains (zeros dropped; a zero high part forces a zero low part) | QED | `Orient_b64_expansion_cc.v : b64_Dekker_pair_priest_chain, b64_Dekker_pair_priest, b64_Dekker_zero_high` |
| 2a | `nonoverlapping_chain e` ⇒ sign(sum e) = sign(leading nonzero component) | QEX (false without an order: `[-4; 1; 8]`, sum +5) | `B64_NonoverlapSign.v : nonoverlap_sign_unordered_qex, nonoverlapping_chain_sign_unordered_false` |
| 2b | same, with "most significant" read as largest magnitude | QEX (`[8; 1; -4; 1; -4; 1; -4]`, sum −1) | `B64_NonoverlapSign.v : nonoverlap_sign_largest_qex` |
| 2c | missing hypothesis: descending magnitude (`mag_desc`); with it the sign theorem holds, zeros structural, all-zero case separate | QED | `B64_NonoverlapSign.v : nonoverlapping_chain_sign_correct, nonoverlap_tail_bound_R, mag_desc_zero_head` |
| 2d | the missing hypothesis holds for `carry_clean (fast_expansion_sum e f)` on Priest input (block keys strictly decrease), so it is not a new Stage D assumption | QED | `B64_CarryCleanSign.v : carry_clean_fes_priest_ordered, reduce_mag_desc` |
| 3 | carry_clean overflow premise `abs_sum e + abs_sum f ≤ 2^(emax−5)` from `\|coord\| ≤ 2^507` (budget 2·508+3 = 1019) | QED | `Orient_b64_expansion_cc.v : orient2d_cc_overflow_margin, orient2d_cc_coord_budget` |
| 3+ | `fast_expansion_sum_safe` derived from the same margin (dropped from the hypotheses) | QED | `B64_CarryCleanSign.v : fes_safe_of_overflow`; `Orient_b64_expansion_cc.v : b64_orient2d_expansion_cc_safe_full` |
| 4 | Stage D on `carry_clean (fast_expansion_sum …)`: value, nonoverlap, sign, Stage D soundness, orient2d soundness on the domain | QED | `Orient_b64_expansion_cc.v : b64_orient2d_expansion_cc_props, b64_orient2d_expansion_cc_sign_correct`; `Orient_b64_stage_d_cc.v : b64_orient_sign_exact_cc_sound, b64_orient_sign_stage_d_cc_sound`; `Shewchuk_vs_Z2.v : orient2d_exact_cc_agrees_with_exact_intdet` |
| 4+ | no use of `fast_expansion_sum_strong_nonoverlap_headline`, directly or transitively | QED (mechanical: chain recompiles with the headline and its five consumers deleted; mutation caught) | `scripts/check_stage_d_headline_free.sh` (CI) |

OUTCOME: QED — Stage D and the orient2d exact-path soundness headline are rebuilt on carry_clean with no dependence on the refuted headline. The literal step-2 statement (bare `nonoverlapping_chain`) is QEX; the missing hypothesis (descending magnitude) is documented and then proved for carry_clean's output from the existing block pattern, not assumed.

Scope that stays a hypothesis: Stage D's safety predicate minus `fast_expansion_sum_safe` — difference ops safe and exact, Dekker op safety, Dekker no-underflow. The integer-regime filter path is unchanged.

Release gate: rungs 0–8 human review is pending, so these results stay internal (no press-release link, no opam 0.1.1) until it clears.
