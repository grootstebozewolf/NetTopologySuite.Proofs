<!-- doc-kind: finding
date: 2026-11-22
Provenance: c45d7f6
Theorems: `AlpogeFifthBatch.v : landau_tails_chernoff`, `AlpogeFifthBatch.v : landau_coeff`, `AlpogeFifthBatch.v : sum_A_trivial`, `AlpogeFifthBatch.v : sum_A_nontrivial`, `AlpogeFifthBatch.v : sum_Th`, `AlpogeSkeleton.v : fifth_batch_counts`
-->
# Alpöge main line: 2 more lemmas proved over R, 2 refined from the Lean proof (41/53 refined, 36 proved)

Requested: prove 2 lemmas and refine 2 from the Lean proof. **Done: 2 + 2.**
Everything is within the three-axiom allowlist (`docs/axiom-allowlist.txt`;
`scripts/audit_axioms.sh` OK).

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source; nothing was built.

## Proved over R (`docs/h1-vacuity/AlpogeFifthBatch.v`, Parts A–B)

Both use #1047's allowlist-clean integral library (`CleanIntegralQED.v`).

| Lean lemma | proof | inputs |
|---|---|---|
| `landau_tails_chernoff` (landauTails.lean) | Below the table. | none (Lean's premises only) |
| `landau_coeff` (LandauCoeff.lean) | `(−1)^k Φ^{(k)}(s)/k!` equals the Laplace moment `∫₀^∞ g u^k e^{−su}/k!`. The proof is `RIntInf_scal` (replacing Mathlib's `integral_const_mul`), `RIntInf_ext`, and the sign identity `(−1)^k(−u)^k = u^k`. Complex integrals are pairs of real improper integrals. | `iteratedDeriv_laplace` [inventory, unrefined] |

**How `landau_tails_chernoff` is proved.** For `0 ≤ l < s` and `U ≤ V`, the
integral of `u^k e^{−su}/k!` over `(0,∞) ∖ [U,V]` is taken as
`∫_0^U + ∫_V^∞`.
1. Pointwise: on `[0,U]` the integrand is at most `e^{lU}·g_{s+l}`, and on
   `[V,∞)` at most `e^{−lV}·g_{s−l}`. This is Lean's `key`.
2. Both pieces are compared with `RInt_le` and `RIntInf_le`.
3. The pieces are evaluated with the kernel antiderivative `Gk` (`FTC_C1`)
   and its limit at `∞`.
4. The bound `e^{−x}P_k(x) ≤ 1` (from `exp_ge_Pk`) gives
   `∫_0^U g_{s+l} ≤ (s+l)^{−(k+1)}` and `∫_V^∞ g_{s−l} ≤ (s−l)^{−(k+1)}`.

## Refined from the Lean proof (Parts C–D)

These are refined over an abstract field `K`, which stands for ℂ, so the
proofs are *Closed under the global context* (no axioms).

| Lean lemma | the Lean proof, rebuilt | Mathlib facts named as hypotheses |
|---|---|---|
| `sum_A` (ChCore.lean l.28) | Below the table. | the group identity `hg` (`ext; simp; abel`); `AddChar.map_add_eq_mul`; `AddChar.sum_eq_zero_iff_ne_zero` (`SUM0`); `Equiv.neg A0` (`A0_perm`) |
| `sum_Th` (ChCore.lean l.56) | Below the table. | `phiSet_card` (`\|PhiSet\| = 2\|H\|`, as `nPhi`); the facts above |

**How `sum_A` is rebuilt.** The Lean statement has the form
`if ψ ∈ PsiA A0 then |A0|·ψ(e1 t) else 0`. Here it is split into
`sum_A_trivial` and `sum_A_nontrivial`.
1. The argument is rewritten with `−e1(s+u−t) = e1 t + (0,−s) + (0,−u)`.
2. `ψ(e1 t)·ψ(0,−s)` is factored out of the sum.
3. **Trivial case:** every term is 1, giving `|A0|`.
4. **Non-trivial case:** the sum is reindexed by `u ↦ −u` (`ksum_perm`
   over `Permutation (map neg A0) A0`) and vanishes.

**How `sum_Th` is rebuilt.**
1. The sum over `u ∈ A0` is swapped inside the sums over `s ∈ T2` and the
   characters (`ksum_swap`).
2. `sum_A` is applied per character, in its trivial or non-trivial case
   according to `inPsi`.
3. The constants are collected:
   `(1/(2|H|))·|T2|·|A0|·b = |A0|·b·((|T2|/|H|)/2)`, which is Lean's
   `|A0|·b·(δ2/2)`.

These replace the instance checks `sum_A_instance` and `sum_Th_instance`
(`CoreSliceQED.v`, on `(ℤ/2)⁴`) with the general argument.

## Ledger (`AlpogeSkeleton.v`)

`sum_A` and `sum_Th` are flipped to refined. `counts` now reads 53 total and
**41 refined**. `two_thirds_refined` still holds (`2·53 ≤ 3·41`).
`fifth_batch_counts` checks by computation that the two new proofs over `R`
are refined items, and that the **36** items proved over `R` are distinct.

| status | count |
|---|---|
| refined (of 53) | **41** (+2) |
| proved over `R` | **36** (+2; this includes #1047's `kernel_integral`) |
| refined but not yet proved over `R` | 5: `windowHypU_of_windowHyp`, `landau_window_ineq`, `landau_cauchy`, `sum_A`, `sum_Th` |
| unrefined | 12: `TopG`, `HostExW` (both stated), `large_x_eventually`, `gmA_eq`, `one_char`, `th_le`, `ch_balance`, `ch_top`, `poleData` (stated), `iteratedDeriv_laplace`, `landau_finite`, `landau_pole_asym` (stated) |

`sum_A` and `sum_Th` are refined over an abstract field, not proved over `R`.
Proving them over `R` would need a model of ℂ-valued characters of finite
abelian groups.

## OUTCOME

**QED (2 proved, 2 refined)**, within the allowlist; the audit is OK and
there are no `Admitted`.

The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 4 / warn 0 / bug 0.**
