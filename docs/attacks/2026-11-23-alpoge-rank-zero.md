<!-- doc-kind: finding
date: 2026-11-23
Provenance: 9d69eaa5c381d1ed04fb808e193fd3c54ecad4e8
Theorems: `LiftIndex.v : exists_fin_pred_of_icc`, `LiftIndex.v : icc_zero_excluded`, `LiftIndex.v : rmax_add_one_split`, `LiftIndex.v : rmax_pair_split`, `AlpogeRankZero.v : ht_of_zL`, `AlpogeRankZero.v : rank_zero_at_witness_r`, `AlpogeRankZero.v : rank_zero_of_row_conditions_r`, `AlpogeRankZero.v : small_level_of_xr_r`, `AlpogeRankZero.v : pin_at_tup_misses_mu0`, `AlpogeRankZero.v : family_threshold_misses_member`, `AlpogeRankZero.v : threshold_keeps_member_xr`, `AlpogeSkeleton.v : counts`
-->
# Alpöge main line: rank_zero_of_row_conditions

Requested: a direct port of `rank_zero_of_row_conditions`, the next QEX call after `bRest_all` and `divinN_of_hypV`, and a NACK hunt on whether its `xr` is uniform in the family.

The arithmetic is in `theories/LiftIndex.v`. The port is in `docs/h1-vacuity/AlpogeRankZero.v`. Both are within the three-axiom allowlist, with no `Admitted`.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read from `C:\rh`; nothing was built. This does not verify RH. The verdict on the external development is unchanged: **PASS-STATIC / PENDING**.

## What the Lean proof does

`RankZeroOfLevelThree.lean:24-32`. `SmallLevelRankEq` (`GlobalTheoremInputs.lean:52-53`) is `∃ xW, ∀ x ≥ xW, ∀ i, ∀ j ∈ lifts, dZ0 j = D0`. `lifts` is `Icc 1 m`. `dZ0 j` is `finrank (Zj mu0 j)`, and the `SizeData₂` argument is ignored (`DataParams₂.lean:194`).

The proof takes the witness `max(x0, x1+1)`. From `x ≥` that max it gets `x0 ≤ x` and `x1 < x`. For `j ∈ Icc 1 m` it takes `k = j - 1`, so `j = k + 1` and `k < m`. `ht` gives `t` with `tup t = mu0` and surjectivity at each `k`. `finrank_Zj_of_pin` (`BaseRowsEqRecordRows.lean:98-108`) returns `finrank (Zj (tup t) (k+1)) = D0`. Rewriting `tup t = mu0` is `dZ0 j = D0`.

The caller (`SmallLevelRankEqClosedOfLevelProjectionSurjective.lean:36-46`) obtains `xr` from `h hc`, so the existential is inside the member. It calls `rank_zero` at `x0 = max(sel, xr)`. `le_max_left` and `le_max_right` turn `x ≥ max(sel, xr)` into `sel ≤ x` and `xr ≤ x`.

## Build log

`C:\rh\build.log` does not compile `RankZeroOfLevelThree.lean`. Around the lines that were logged, files take about 720s each (lines 6-12). The log then dies with exit `3221226505` (`STATUS_STACK_BUFFER_OVERRUN`, lines 993 and 191164) and, where `ring` fails, says to use `ring_nf` (line 9683). The caller sets `maxHeartbeats 1600000`. The port therefore proves the `omega` index step and the `max` split with `lia` and `lra` in `theories/LiftIndex.v`, and does not re-elaborate `finrank_Zj_of_pin`.

## QEX (named hypotheses)

- `finrank_Zj_of_pin`: the equality at `tup t` and index `k+1`. The adjoint and `finrank` of a range stay unread.
- `mu0_inhab`: the caller's `t` with `tup t = mu0` (`tied.div.tup.mu0`).
- `zL`: `∃ xr` inside the member, and surjectivity of `lPrj` only for `x ≥ xr`.

`pin_at_tup_misses_mu0` shows the rewrite is load-bearing: `dZ 1 1 = 2` does not give `dZ 0 1 = 2`. `family_threshold_misses_member` shows a witness built from `xr = 0` equals `1` and does not clear a member `xr` of `5`. `threshold_keeps_member_xr` shows `max(max(sel, xr), x1+1)` does clear all three. `icc_zero_excluded` shows `0` is not a lift index.

## Ledger

`AlpogeSkeleton.v` cites the two theorems on the `TopG` row and `Check`s them. Counts unchanged: 53/53 refined, 46 proved over R. `rank_zero` is a sub-lemma of the `TopG` item, not a new row.

## OUTCOME

**QED (refined)** for the index shift, the two max splits, the witness `max(x0, x1+1)`, and the caller packaging `xW = max(max(sel, xr), x1+1)` with `xr` taken from the member existential. **No candidate NACK.** The `xr` of the Lean caller is inside `h hc`, and the Rocq witness is computed from that `xr`. **QEX** for `finrank_Zj_of_pin`, `mu0_inhab`, and `zL`. The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 11 / warn 0 / bug 0.**
