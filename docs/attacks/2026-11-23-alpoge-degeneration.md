<!-- doc-kind: finding
date: 2026-11-23
Provenance: 364cd72ce19ac29c02eef28d5f251ac802b14f2f
Theorems: `DegenerationArith.v : odd_mul_iff`, `DegenerationArith.v : nm_sq_split`, `DegenerationArith.v : char_shift_zero`, `DegenerationArith.v : sum_range_odd_half`, `DegenerationArith.v : pow_from_sq`, `DegenerationArith.v : sq_descent_cancel`, `DegenerationArith.v : quad_reduce_exists`, `DegenerationArith.v : rel_pow_iter`, `DegenerationArith.v : unit_norm_pair`, `DegenerationArith.v : pow_iter_of_root`, `DegenerationArith.v : odd_pred_half`, `DegenerationArith.v : no_dvd_from_shift`, `DegenerationArith.v : div_mul_cancel_r`, `DegenerationArith.v : abs_one_ne_zero`, `AlpogeDegeneration.v : sign_pair_cancels`, `AlpogeDegeneration.v : quad_rho_sq_needs_relation`, `AlpogeDegeneration.v : unit_norm_half_escapes`, `AlpogeDegeneration.v : div_cancel_needs_nonzero`, `AlpogeDegeneration.v : half_sum_at_two_fails`, `AlpogeDegeneration.v : odd_six_premise_fails`
-->
# Alpöge degeneration: theta constants and Weil values

Requested: a direct port of the degeneration mains' own arithmetic, the same shape as `rank_zero_of_row_conditions` and `linkIRR_of_join_ex`. The message says 36 main files under `Development.AbelianVarietyTheory.Proofs.DegenerationProofs`, with statement wrappers and single-use helpers folded in. The list that arrived has 20 stems and stops at `IsThetaPtDown`, before that file's importer count. The other names were not in the message, so they were not ported.

The arithmetic is in `theories/DegenerationArith.v`. The port is in `docs/h1-vacuity/AlpogeDegeneration.v`. Both compile with the `nts-flocq` switch (Rocq 9.1.1). The docs pin is 9.2.0. `Print Assumptions` shows `ClassicalDedekindReals.sig_forall_dec` and `FunctionalExtensionality.functional_extensionality_dep` on the real lemmas, and `Closed under the global context` on the nat lemmas. `scripts/audit_axioms.sh` accepts that log. No `Admitted`.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read from `C:\rh`. This does not verify RH. The verdict on the external development is unchanged: **PASS-STATIC / PENDING**.

## What the Lean proofs calculate

`CharSumInv.lean:8-35` (`charSum_inv`). After a left-multiplication bijection identifies the shifted character sum with `S`, the file has `(phi - 1) * S = 0`, then the domain gives `S = 0` when `phi <> 1`. The trivial character sums to the cardinality. `main` at lines 37-45 is a dead representation projector; the live proof is `charSum_inv`.

`IsThetaPtDown.lean:56-71`. `Nat.odd_mul` sends `Odd (n * m)` to `Odd m`. Line 50 rewrites `(n * m) ^ 2 = n * m ^ 2 * n`. The unit and scheme steps stay outside.

`WeilPairingLabelledTorsionUniformTest.lean:16` and `ThetaSystemSumCharacterOrthogonalEqZero.lean:30`. The file's own arithmetic is `(r * N) ^ 2 <> 0` and `(r * N) ^ 2 / (r * N) = r * N`. A uniform exponent `0` is `1`.

`ExistsObjectWithThetaPointOfDegenerationSeries.lean`. The mul and add witnesses of `dvd_pow_sub`, the square-power factor in `dvd_of_dvd_sq`, the cancel in `eq_zero_of_sq` after `A = d * A'`, the split of a `{zeta, rho}` polynomial under `rho ^ 2 = -d`, and `tx_scale`'s divisions `(m * (2 * k)) / 2 = m * k` and `(m * a) / m = a`. Over `R`, `A ^ 2 = -d * B ^ 2` does not force `B = 0`. The port stops at `B ^ 2 = d * (-A' ^ 2)`.

`ExistsPowerSectionOfChartFunctions.lean:250-264` (`prod_cubN_wS`). For odd `k`, the sum of `0 .. k-1` is `((k - 1) / 2) * k`.

`HomTransport.lean:104-107` (`Rel.pow`) is induction from the unit and the product step. Line 161 is `(2 * j + 1 - 1) / 2 = j`.

`AbelianPartValuesTorsionPairingSeparationIntegra.lean`. `(v ^ c) ^ k = 1` from `v ^ k = 1` (lines 29-31). `norm_valF` (lines 121-126) is the same product bound as `norm_unit`. `tors_of_integral` (lines 233-238): an odd integer already at least 2 is at least 3.

`DegenerationValuesIntOfAdmissibleBase.lean:46-51` (`norm_unit`) and `IsProperOfThetaUnitInEveryCoset.lean:61`. Two nonnegative reals, each at most 1, with product 1, are each 1. Line 76 of the coset file: a value of norm 1 is not zero.

`ExistsExtendValuation.lean:87-88`. A prime at least `d + 3` is not 2, and it does not divide `d`.

`ExistsNumDHomDegenerationValuesFieldExtension.lean:116`. `(a / u) * u = a` when `u <> 0`.

`AbelianPartValuesOfExpansionLaws.lean` is the package `brUth_of_laws` (20 lines) and has no separate arithmetic. `ArcTorsionValuesNormsIntegralPositive.lean` (24 lines) calls `norm_θ`, `norm_σ`, `norm_th`, `norm_ψ`, `norm_txT`, and `twist_int`.

## Build log

`C:\rh\build.log` does reach DegenerationProofs, about 52-58s a file. Where `ring` fails the log says to use `ring_nf` (line 9683). These lemmas are that normal form: `lia` and `lra`.

## Controls

`sign_pair_cancels` is `1 + (-1) = 0` with the shift `-1 <> 1`. `one_shift_keeps_two` keeps the sum `2` when the character is `1`. `odd_six_premise_fails` shows `Odd (3 * 2)` is false, while `odd_three_five` keeps both factors odd. `half_sum_at_two_fails` shows the odd half-sum formula at `k = 2` is not the sum. `quad_rho_sq_needs_relation` evaluates `rho ^ 2` at `rho = 1`, `d = 3` as `1`, and `-3 <> 1`. `unit_norm_half_escapes` is `(1/2) * 2 = 1` with `1/2 <> 1`. `div_cancel_needs_nonzero` is `(1/0) * 0 = 0`.

## QEX (named hypotheses)

- `card_monoidHom_of_hasEnoughRootsOfUnity`, `exists_apply_ne_one`, and the `Equiv.mulLeft` bijection in `charSum_inv`.
- `AddChar.sum_eq_zero_of_ne_one` and `thetaSys_FF_mem_finite_perp_proj`.
- `CommPairing.weilIs_pull` and `weilIs_grpPullback_of_comm'`.
- `exists_add_pow_prime_pow` (Freshman's dream), `ZMod.pow_card_pow`, `pow_eq_pow_of_modEq` / `pow_totient`, `prime_coprime_of_not_dvd`, and well-founded `dvdNotUnit`.
- `val_corr`, `val_pull`, `val_one`, `TauValues.main`, `gen_unique'`, and `iota_is_inv` in `ExistsNumOf`.
- `isThetaPt_of_over`, `weilIs_one_left`, `exists_unit_of_isGenSec`, `exists_symLift_one`, `exists_unit_isValueAt`, `ThetaPtExist.exists_isThetaPt`, `isThetaPtOver_of_subsingleton`.
- `IsCub`, `cubN`, and `wS` products around the odd sum.
- `Prime.odd_of_ne_two` and `Nat.exists_infinite_primes`.
- `ZMod.natCast_self` and `zero_pow` in the coset lattice.
- `brUth_of_laws`'s `weilIs_weil` and `isThetaPt_uth`.
- `norm_θ`, `norm_σ`, `norm_th`, `norm_ψ`, `norm_txT`, `twist_int`.
- Terminal scheme theorems sighted and not opened past the statement: `DegenerationValuesIntOfAdmissibleBase.main`, `exists_lift_ext`, `exists_integral_values`, `exists_integral_gauge`, `exists_isFib`, `exists_hom` past the division cancel, `exists_strict`, `GlobalTheory.Ex.brFam`, `GlobalTheory.Ex.AdicNormSum.main`, `integral_values`, `isProper_of_unit_in_cosets` past the norm step, `exists_full_theta`, `GlobalTheory.Ex.NumD.hom_transport` past `Rel.pow` and the odd index.

## Ledger

Degeneration is not a `TopG` sub-lemma. `AlpogeSkeleton.v` is unchanged. Counts unchanged: 53/53 refined, 46 proved over R. README counts are 843 registered modules, 698 under `theories/`. Flocq 145 and the host lane 206 are unchanged. The new module is in `_CoqProject.full` and in `scripts/hunt_probe_smoke.sh`. It is not in the host `_CoqProject`.

## OUTCOME

**QED (refined)** for the character-sum cancellation, the odd-product split, the square order identity, the odd range half-sum, the square-power factor and the descent cancel, the `{zeta, rho}` split under `rho ^ 2 = -d`, the relation iteration, the unit-norm product, the root iteration, the odd chart index, the `d + 3` divisor bound, the division cancel, and `|x| = 1` excluding `0`. **No candidate NACK** on those steps. **QEX** for the names above. The remaining mains implied by "36" were not in the message.

This finding was drafted with AI assistance (Cursor Grok 4.7) and is not yet human-reviewed.

**SUMMARY ok 20 / warn 0 / bug 0.**
