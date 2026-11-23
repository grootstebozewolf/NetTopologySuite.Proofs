<!-- doc-kind: finding
date: 2026-11-23
Provenance: 9d69eaa5c381d1ed04fb808e193fd3c54ecad4e8
Theorems: `LogRpowClean.v : rpc_inv_cancel`, `LogRpowClean.v : rpc_le_of_root`, `AlpogeLinkIrr.v : link_irr_rows_at_witness_r`, `AlpogeLinkIrr.v : linkIRR_of_join_ex_r`, `AlpogeLinkIrr.v : root_threshold_misses_member`, `AlpogeLinkIrr.v : root_threshold_keeps_member`, `AlpogeLinkIrr.v : pow_id_roundtrip`, `AlpogeLinkIrr.v : pow_id_wrong_exp`, `AlpogeLinkIrr.v : pow_id_at_zero`, `AlpogeSkeleton.v : counts`
-->
# Alpöge main line: linkIRR_of_join_ex

Requested: a direct port of `linkIRR_of_join_ex`, the next QEX call after `rank_zero_of_row_conditions`, and a NACK hunt on the member threshold and the power identity.

The arithmetic is in `theories/LogRpowClean.v` (`rpc_inv_cancel`, `rpc_le_of_root`) together with `LiftIndex.rmax_pair_split`. The port is in `docs/h1-vacuity/AlpogeLinkIrr.v`. Both are within the three-axiom allowlist, with no `Admitted`.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read from `C:\rh`; nothing was built. This does not verify RH. The verdict on the external development is unchanged: **PASS-STATIC / PENDING**.

## What the Lean proof does

`LinkIRROfJoinEx.lean:17-32`. The hypothesis `h` is `∃ x0, ∀ x ≥ x0, ∀ i, ∃ A` carrying `LabelCountGoodInjective`, `AllJoinA`, `admLq`, `CountAllRows`, and `SizesRec` at `Fm.ez`. The conclusion is `LinkIRR Fm`, by `linkIRR_of_allRows`.

The proof opens `h` as `x0`. It proves `0 < Fm.ez` by `div_pos` from `0 < eps` and `1 ≤ J`. The witness is `max(x0, (3/2)^(1/ez))`. `le_max_left` feeds `x0` back into `h`. `le_max_right` is `(3/2)^(1/ez) ≤ x`. The calc rewrites `(3/2) = ((3/2)^(1/ez))^ez` by `rpow_mul`, `one_div_mul_cancel`, and `rpow_one`, then `rpow_le_rpow` gives `3/2 ≤ x^ez`. `weight_of_join` fills `WeightAllRows` from `admLq`, `tieAdmG_holds`, `rangeW_of_sizes` at that inequality, and `AllJoinA`. The package passed on is `Lab`, `Cnt`, `Wgt`, `Sz`.

`x0` is inside `h` for that `Fm`. `ez > 0` is the hypothesis of the inverse power.

## Build log

`C:\rh\build.log` does not compile `LinkIRROfJoinEx.lean`. Around the lines that were logged, files take about 720s each (lines 6-12). The log then dies with exit `3221226505` (`STATUS_STACK_BUFFER_OVERRUN`, lines 993 and 191164) and, where `ring` fails, says to use `ring_nf` (line 9683). The port proves the inverse-power identity and the monotonicity step with `Rinv_l` and `lra` in `theories/LogRpowClean.v`. It does not re-elaborate `weight_of_join`, `rangeW_of_sizes`, or `link_irreducible_all_rows`.

## QEX (named hypotheses)

- `linkIRR_of_allRows`: the delp tail. Its implementation `link_irreducible_all_rows` (`ConcNP.lean:631-645`) adds an `atTop` number bound and calls `delp_of_allRows`.
- `weight_of_join`: `admLq`, `TieAdmG`, `RangeW`, and `AllJoinA` give `WeightAllRows` (`AllJoinP.lean:22-24`).
- `rangeW_of_sizes`: `SizesRec` and `3/2 ≤ x^ez` give `RangeW`. The body is `exp 1 ^ 12 ≤ exp (8 * x^ez)` and `2^12 ≤ host.g k` (`ConcNWeight.lean:221-236`). The port proves the `3/2` premise and passes it in.
- `tieAdmG_holds`: the `D7` record projection (`LinkIRROfJoinEx.lean:14-15`).

`root_threshold_misses_member` shows `max(0, (3/2)^1) = 3/2`, which does not clear a member `x0` of `5`. `root_threshold_keeps_member` shows `max(5, (3/2)^1) = 5` and `3/2 ≤ 5^1`. `pow_id_roundtrip` shows `((3/2)^(1/2))^2 = 3/2`. `pow_id_wrong_exp` shows `((3/2)^1)^2 = 9/4`. `pow_id_at_zero` shows the exponent `0` case equals `1`, because `/ 0 = 0` in this reals library.

## Ledger

`AlpogeSkeleton.v` cites the two theorems on the `TopG` row and `Check`s them. Counts unchanged: 53/53 refined, 46 proved over R. `linkIRR_of_join_ex` is a sub-lemma of the `TopG` item, not a new row. `AlpogeTopShape.link_irr_r` still takes the Closed-algebra call as a hypothesis; this probe is the body of that call.

## OUTCOME

**QED (refined)** for `0 < ez` from `0 < eps` and `1 ≤ J`, the witness `max(x0, (3/2)^(1/ez))` with `x0` taken from the member existential, the identity `(b^(1/e))^e = b` for `e ≠ 0`, and `3/2 ≤ x^ez`. **No candidate NACK.** The Lean `x0` is inside `h`, and the Rocq witness is computed from that `x0`. The inverse power uses the same positive exponent. **QEX** for `linkIRR_of_allRows`, `weight_of_join`, `rangeW_of_sizes`, and `tieAdmG_holds`. The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 9 / warn 0 / bug 0.**
