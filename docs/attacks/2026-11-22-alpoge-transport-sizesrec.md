<!-- doc-kind: finding
date: 2026-11-22
Provenance: 49d228e9fba1e327324d5c75dbf407a01f7e5af2
Theorems: `AlpogeTransportSizes.v : sizes_exp_upper`, `AlpogeTransportSizes.v : sizes_exp_upper_needs_eps`, `AlpogeTransportSizes.v : sizes_pow4_256`, `AlpogeTransportSizes.v : sizes_pow4_needs_x`, `AlpogeTransportSizes.v : sizes_ez_sixth`, `AlpogeTransportSizes.v : sizes_ez_sixth_needs_nonneg`, `AlpogeTransportSizes.v : rpower_mono_not_for_every_fn`, `AlpogeTransportSizes.v : sizesRec_exponents_r`, `AlpogeTransportSizes.v : transport_link_zero_r`, `AlpogeTransportSizes.v : rows_threshold_inside`, `AlpogeTransportSizes.v : threshold_of_one_misses_another`, `AlpogeSkeleton.v : counts`
-->
# Alpöge main line: transport link zero and sizesRec_at

Requested: a NACK hunt on the two highest-risk QEX calls from the TopShape ranking, `theoremS_transport_link_zero` and `sizesRec_at`.

The work is in `docs/h1-vacuity/AlpogeTransportSizes.v`. It is within the three-axiom allowlist, with no `Admitted`.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read from source; nothing was built. This does not verify RH. The verdict on the external development is unchanged: **PASS-STATIC / PENDING**.

## theoremS_transport_link_zero

`LinkSPos.lean:131-161`, namespace `Formalism.L2.SG.ThmSOwn`. `C0` is a section variable (`LinkSPos.lean:14`), an input with `1 ≤ C0`, not a quantity derived from `x`.

`hc30` (`LinkSPos.lean:141`) is `∀ {eps} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A`. `c30 : List ℝ → CountingConstants` is applied at `Fm.cOut`. `theoremS_link_concrete` then reads `(hc30 Fm)` (`LinkSPos.lean:126`). The constants depend on that member. They do not depend on the scale `x`, on `t`, or on the index `i`.

The row package (`LinkSPos.lean:153-157`) is

```
Closed (fun Fm _ => ∃ xR, ∀ x ≥ xR, Fm.x1 < x → ∀ i, ∃ X, RowsTieP …)
  := closed_of_th (fun _ => 0) (fun _ => 0) fun Fm _ hc _ _ _ =>
       ⟨(sel Fm hc).1, fun x hx0 hx i => ⟨_, rowsTiePT'_of …⟩⟩
```

`closed_of_th` (`ThmSOwn.lean:435-438`) supplies three premises before the payload: `thm Fm.cOut ≤ Fm.CGam`, `th (cOut ++ cMid) ≤ sC'`, and the same for `sCl`. With both functions constantly `0`, those premises are `0 ≤ Fm.CGam`, `0 ≤ sC' Fm`, and `0 ≤ sCl Fm`. The lambda discards them. The `x`-threshold it returns is `(sel Fm hc).1`, chosen after `Fm` and `hc`. `rows_threshold_inside` and `transport_link_zero_r` replay that packaging: `hc30` is applied at the member, then `xR` is defined as `sel1 Fm` inside the existential, and the tail quantifies `i`. `link_of_eval` also takes `1 ≤ C0`.

`threshold_of_one_misses_another` is the control. A threshold `0` that serves one member fails for a member whose selection threshold is `3`, at `x = 1`. A finite class still has a uniform threshold (the maximum). An unbounded family would need the archimedean axiom, which is off the allowlist, so that stronger negative statement is not formalised here.

The same per-member shape appears in the producers this theorem calls and this slice leaves as inventory. `hypOwnE_kppDiagP` (`LinkSPos.lean:21-26`) sets the tail `x0` from `ConcEv`, and `kloostermanDiagonalThreshold` (`LinkSPos.lean:16-19`) is a `max` of `choose` values of a function of the family-constant list (`getD 6`, `getD 13`) and `C0`. `hypOwnL_diagP` (`LinkSPos.lean:64`) takes `xR` to be `max x2 (max x3 (max (sel Fm hc).1 (Fm.x1 + 1)))` inside the member; `thmDLP` / `thDLP` (`LinkSPos.lean:48-55`) are functions of that same list.

## sizesRec_at

`LinkIRROfJoinEx.lean:39-138`. The statement is at one `(Fm, x, i, Cs)`, with `Fm.x1 < x`, `4 ≤ x`, and `6 ≤ Cs`. `eps < 1/52` and `0 < eps` are read from `(Fm.L x i).sc` (`lines 44-45`). Nothing is pulled outside `x`.

The five exponent comparisons (`lines 64-71`) are `sizesRec_exponents_r`. They follow from `rpower_mono` for one function `rp`: `1 <= x -> e1 <= e2 -> rp x e1 <= rp x e2`. That is the statement of Stdlib `Rle_Rpower` (`1 <= e -> n <= m -> Rpower e n <= Rpower e m`). An earlier hypothesis claimed this for every `rp : R -> R -> R`. That proves `False`: `rpower_mono_not_for_every_fn` takes `rp _ e := -e` at `x = 1`, `e1 = 0`, `e2 = 1` and gets `0 <= -1`. The `1 <= x` guard does not save an arbitrary function; it is the guard `Rle_Rpower` uses for `Rpower`. The identifier `Rpower` is not written in the checked theorem: mentioning it makes `Print Assumptions` report `Classical_Prop.classic`, which is off the allowlist. `Rle_Rpower` stays QEX.

| comparison | Lean | needs |
|---|---|---|
| `9/2 + 10 ε + ε/100 ≤ 5` | `h5`, line 64 | `ε < 1/52` (`sizes_exp_upper`; the bound is `ε ≤ 50/1001`) |
| `5 ≤ Cs` and `6 ≤ Cs` | `h56`, `h6` | `6 ≤ Cs` |
| `4 ≤ 9/2 + 10 ε − ε/100` | `h4`, line 68 | `ε ≥ 0` (`sizes_exp_lower_4`) |
| `2 ≤ 2 + 8 ε − ε/100` | `h2`, line 70 | `ε ≥ 0` (`sizes_exp_lower_2`) |
| `256 ≤ x^4` | `hx4p`, line 72 | `x ≥ 4` (`sizes_pow4_256`) |
| `2 * x^5 ≤ x^6` | `hx65`, line 76 | `x ≥ 2`, hence `x ≥ 4` (`sizes_two_x5`) |
| `ez/6 ≤ ez/5 − ez/100` | `hεq`, line 88 | `ez ≥ 0` (`sizes_ez_sixth`) |

Controls, on the same pattern as `cutoff_needs_hN`:

- `sizes_exp_upper_needs_eps`: at `ε = 1` the exponent is `9/2 + 10 + 1/100`, and that is not `≤ 5`.
- `sizes_pow4_needs_x`: `2^4 = 16`, and `256 ≤ 16` is false.
- `sizes_ez_sixth_needs_nonneg`: at `ez = -1`, `ez/6 ≤ ez/5 − ez/100` is false.

`link_irr` (`LinkIRROfJoinEx.lean:157-162`) passes `x ≥ 4` by taking `max (max x0 (sel …).1) (max (Fm.x1 + 1) 4)` inside the member, then calls `sizesRec_at` at that `x` with `Cs = 6`. The `4` is a per-member lower bound on the tail, not a constant claimed uniform in `t` or the level.

## QEX (named hypotheses)

`link_of_eval` matches `theoremS_link_of_evaluation` (`LinkSPos.lean:97-102`): `1 ≤ C0`, `0 ≤ C`, `2 * Cg ≤ A`, `2 ≤ sCl`, `2 * C ≤ sCl`, `StandingHypothesesWithConstants`, `∃ xR, ∀ x, x1 < x → ∀ i, ∃ X : RowsAut`, `ThmSOwn`, `CountAllPointsClass`. It does not take `TuSize`. The literal `C0 = 3` is the `link_alt` instantiation.

- `rpower_mono` is `Rle_Rpower` for one `rp`. Stdlib's proof of `Rle_Rpower`, and the name `Rpower` itself, use `Classical_Prop.classic`.
- `hc30`, `sCl_ge2`, `sCl_twiceC`, `standing_of`, `thmOwn_of`, `countAll_of`, and `link_of_eval`. `linkS_of_standing_hypotheses` and `countOwn_of_rowsPEv` sit inside `link_of_eval`.
- `closed_of_th`'s three side conditions (`0 ≤ CGam`, `0 ≤ sC'`, `0 ≤ sCl`) are not premises of `transport_link_zero_r`. The Lean lambda discards them and returns `⟨(sel Fm hc).1, …⟩`. This theorem packages that existential. It does not re-prove `closed_of_th`.
- Unread producers: `finXC_of`, `selOK_of`, `concEv_of_sel`, `rowsTiePT'_of`, `hypOwnE_kppOff`, `hypOwnE_kppDiagP`, `kernel_diagonal_positive`, `hypOwnS_off`, `hypOwnL_diagP`, `diagonal_positive_final`, `closed_of_large`, `linkThresholds`.
- `Fm.sizes` (`LinkIRROfJoinEx.lean:41`): `SizeN`, `SizeK`, `SizeQD`, `SizeG`, the rank comparisons, and `Real.exp (x^(ez/6)) ≤ host.q` and `≤ host.d` (lines 91-106). The exponent comparisons above do not use those bounds.

## Ledger

`AlpogeSkeleton.v` cites `transport_link_zero_r` and `sizesRec_exponents_r` on the TopG row and `Check`s the theorems. Counts unchanged: 53/53 refined, 46 proved over R. Both lemmas are sub-lemmas of the TopG link facts, not new rows.

## OUTCOME

**QED (refined)** for the exponent arithmetic, the power bounds `256 ≤ x^4` and `2 * x^5 ≤ x^6`, the control that monotonicity for every function is false, and the packaging of `theoremS_link_of_evaluation`. **QEX** for `Rle_Rpower` itself and for the inventory premises above. The false unguarded `rpow_mono` was a transcription, not a gap in the Lean `rpow_le_rpow_of_exponent_le` step, which assumes base `≥ 1`. No candidate NACK of that Lean step. The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 12 / warn 0 / bug 0.**
