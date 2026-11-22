<!-- doc-kind: finding
date: 2026-11-22
Provenance: b1ee6875409faf500a54a92a06ccad736b23e53a
Theorems: `AlpogeBrestDivin.v : bRest_all_r`, `AlpogeBrestDivin.v : link_brest_at_two`, `AlpogeBrestDivin.v : divinN_of_hypV_r`, `AlpogeBrestDivin.v : divin_abs_bound`, `AlpogeBrestDivin.v : divin_abs_needs_abs`, `AlpogeBrestDivin.v : scale_le_product`, `AlpogeBrestDivin.v : scale_le_product_needs_y`, `AlpogeBrestDivin.v : divin_threshold_pack`, `AlpogeBrestDivin.v : log_sq_not_for_every_fn`, `AlpogeBrestDivin.v : log_sq_le_rpc`, `AlpogeBrestDivin.v : divinN_of_hypV_clean`, `AlpogeSkeleton.v : counts`
-->
# Alpöge main line: bRest_all and divinN_of_hypV

Requested: a NACK hunt on `bRest_all` and `divinN_of_hypV`, the next two QEX calls after the transport slice.

The work is in `docs/h1-vacuity/AlpogeBrestDivin.v`. It is within the three-axiom allowlist, with no `Admitted`.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read from source; nothing was built. This does not verify RH. The verdict on the external development is unchanged: **PASS-STATIC / PENDING**.

## bRest_all

`FinalAll.lean:13-46`, called from `LinkBrest.lean:24` with `Cabs = 2`. The conclusion is

```
Closed (D3 3 A) (fun Fm CH => forall hc, TuSize -> DGamSize -> RemainingDivisionBounds Fm Cabs CH)
```

`RemainingDivisionBounds` (`IndefiniteRealisationChoice.lean:158-163`) has `hh` (depending on `CH`), and `bu`, `rr`, `la`, each an `exists x0, forall x >= x0, forall i` tail. `Cabs` is a parameter of the structure. The Lean proof mentions it only in the `show` at lines 45-46; the four fields are filled without a numeric use of `Cabs`. `bRest_all_r` keeps `Cabs` as a parameter. `link_brest_at_two` instantiates it with the literal `2`.

The row premises keep `x1 < x`, `sel <= x`, and the index `i` (`FinalAll.lean:20-26`). `muRank_of_lvl` is applied at the proved fact `0 < 3` (`FinalAll.lean:38`). `funSharp` returns a `CF0` that `hh_of_lvl` consumes.

## divinN_of_hypV

`DivinNOfHypV.lean:117-130`. `LinkN` supplies `C` and a tail `x3`. `HypV` supplies `x1`. `SmallLevelRankEq` supplies `x4`. `log_sq_le_rpow` (`lines 59-74`) supplies `x6`. The bound constant is `|C| + 1`. The threshold is

```
max (max x1 (max x3 x4)) (max x6 (x1 + 1))
```

inside the existential (`line 123`). `divin_threshold_pack` splits that max. `divin_threshold_needs_all` shows a tail of `0` does not serve a tail of `5`.

`divin_abs_bound` is the arithmetic at `divinN_at` lines 105-115. `divin_abs_needs_abs` shows that writing `C` in place of `|C|` fails at `C = -1`, `y = 2`, `B0 = 1`, `Nc = 1`, `log^2 = 1`: `-3 <= -4` is false. `scale_le_product` is `b <= f * m * b * y` (`lines 100-103`). `scale_le_product_needs_y` fails at `y = 1/2`.

`log_sq_not_for_every_fn` shows the log-square bound is false for an arbitrary pair of functions (`lg = 0`, `pw = -1`). Lean names `Real.log` and `Real.rpow`. Those Stdlib names are not written in the checked file: `ln` and `Rpower` make `Print Assumptions` report `Classical_Prop.classic`. `log_sq_le_rpow` is a hypothesis for one `logf` and one `powf`.

## QEX (named hypotheses, Lean citations)

- `funSharp`: `closed_funSharp_thr`, `FinalAll.lean:31`.
- `linkG_frame`: `FinalAll.lean:35`.
- `muRank_of_lvl`: `FinalAll.lean:38`, at `0 < 3`.
- `hh_of_lvl`: `FinalAll.lean:40-41`.
- `bu_rr`: `buRat_rrFull_closed`, `FinalAll.lean:43`.
- `la_of`: `FinalAll.lean:46`.
- `log_sq_le_rpow`: `DivinNOfHypV.lean:59-74`, one `logf` and one `powf`. **Discharged for the clean pair** `Lc`/`rpc` (`theories/LogRpowClean.v`): `log_sq_le_rpc` proves `Lc x² ≤ x^ε` eventually (from `Lc y ≤ y^t/t` with `t = ε/4`), and `divinN_of_hypV_clean` is `divinN_of_hypV_r` with that premise gone.
- `divin_at`: `divinN_at` and `vvRecord`, `DivinNOfHypV.lean:17` and `:79`, fed `|C| + 1` and `x1 + 1 <= x`.
- `hV`, `hN`, `hR`: the outer existentials of `HypV` (`line 10`), `LinkN`, and `SmallLevelRankEq` as read off the `obtain`s at lines 119-121.

## OUTCOME

**QED (refined)** for the record assembly, the literal `Cabs = 2`, `0 < 3`, the `|C| + 1` bound, the scale comparison, the max-of-tails split, and the two False-checks. **No candidate NACK.** `Cabs` is a parameter of `RemainingDivisionBounds`, not a quantity computed from `x`. The `|C| + 1` and the max threshold are inside `divinN_of_hypV`'s existential. **QEX** for the calls listed above. The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 10 / warn 0 / bug 0.**
