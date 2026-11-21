<!-- doc-kind: finding
date: 2026-11-21
Provenance: 3a26342
Theorems: `AlpogeRealsQED2.v : exp_Lc`, `AlpogeRealsQED2.v : rpc_mult`, `AlpogeRealsQED2.v : level_of_tiedWin`, `AlpogeRealsQED2.v : core_gm`, `AlpogeRealsQED2.v : formB`, `AlpogeRealsQED2.v : zeroFreeAll_of_topG`, `AlpogeSkeleton.v : next_twelve_proved_are_refined`
-->
# Alpöge main line: the next 12 refined lemmas proved over Stdlib's reals (24/39 in total)

Requested: the next 12 of the refined lemmas, proved to this corpus's
standard (only the three allowlisted axioms). **Done: 12/12.**

Combined with `2026-11-21-alpoge-twelve-over-reals.md`, **24 of the 39
refined ledger items** are now proved over Stdlib's `R`. Every
`Print Assumptions` is a subset of `docs/axiom-allowlist.txt`, and
`scripts/audit_axioms.sh` passes on the file's build log.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source; nothing was built.

## Infrastructure: an allowlist-clean logarithm

The earlier finding showed that Stdlib's `ln` and `Rpower` carry
`Classical_Prop.classic`. That blocked every lemma whose statement mentions
`log` or `rpow`. `AlpogeRealsQED2.v`, Part 0, builds a replacement inside the
allowlist:
- **`Lc y`** is the root of `exp x − y` on `[−1/y, y]` given by Stdlib's
  `IVT`. `IVT`, `derivable_exp` and `Rlt_dec` are allowlist-clean.
- **`exp_Lc`** (`exp (Lc y) = y` for `y > 0`) and **`Lc_exp`**
  (`Lc (exp x) = x`) make `Lc` *the* inverse of `exp` on `(0,∞)`.
- **`rpc x a := exp (a · Lc x)`** comes with the rpow laws the Lean proofs
  use: `rpc_add`, `rpc_mult`, `rpc_one`, `rpc_mono_exp` (for `x ≥ 1`) and
  `rpc_mono_base` (for `a ≥ 0`).
- **`Lc_le_rpc_div`** is `Real.log_le_rpow_div`.

## The twelve (`docs/h1-vacuity/AlpogeRealsQED2.v`)

| # | Lean lemma | premises beyond Lean's own |
|---|---|---|
| 1 | `level_of_tiedWin` | none; `h112`, `hB` and `h` are Lean's premises |
| 2 | `windowHyp_of_rpow_eventually` | none |
| 3 | `windowInequality_of_artinInputs` | `core_gm` (an inventory lemma; item 4 is supplied when composed) |
| 4 | `core_gm` | `ch_core`, `sigA_le` (inventory). The eventual `1 + 4o ≤ x^ε` is **proved** here (`eventually_rpc_ge`), with no `tendsto` needed. |
| 5 | `CharacterBalanceMoves.core` | per-coset bounds (`th_le`, `ch_balance`) and `sum_Th` (inventory) |
| 6 | `tiedCore_of_chainTied` | none |
| 7 | `charFamily_LFunction_ne_zero_of_one_le_re` | the three Mathlib L-function facts it cites |
| 8 | `lemmaL` | `landau_window ∘ windowHypU_of_windowHyp ∘ poleData`, and item 7 (inventory) |
| 9 | `zeroFree_of_rpow_window` | `windowHyp_of_rpow` (inventory: its window integral is calculus) |
| 10 | `formB` | `level_family` (inventory; proved over `R` in the first batch); chains items 9 and 8 |
| 11 | `landau_pole_re_le` | `landau_pole_re_le_bound` and the residue expansion (inventory). The limit step is proved as an Archimedean bound. |
| 12 | `zeroFreeAll_of_topG` (composition) | `TopG` (as `AtWindowScale`), `ch_core`, `sigA_le`, `landau_window` / `poleData`, `windowHyp_of_rpow` and `level_family` (inventory). It **chains items 1, 3, 4, 6, 8, 9, 10**. |

**Inputs and representation.** Inputs marked "inventory" are other ledger
lemmas that the Lean proof calls, named as hypotheses. This is the same
treatment the refinement ledger uses. As before, ℂ appears as pairs of reals,
Finset sums as list sums, and the development's abstract parameters as
section variables.

**The top-level composition.** `zeroFreeAll_of_topG` is now one theorem over
`R` within the allowlist: ZeroFreeAbove (1/2) for the level. It is
conditional only on the unrefined deep inputs listed above:
- `TopG`;
- `ch_core` (whose Q-rebuild is `ch_core_rebuilt`);
- `sigA_le`;
- `landau_window` / `poleData`;
- `windowHyp_of_rpow`;
- `level_family`.

`AlpogeSkeleton.v : next_twelve_proved_are_refined` checks by computation
that the twelve are refined ledger items, and that all 24 proved over `R` are
distinct.

## Ledger status

| status | count |
|---|---|
| refined (of 53) | 39 |
| proved over `R`, three-axiom allowlist | 24 (12 + 12) |
| unrefined | 14 (unchanged) |

The 15 refined items not yet proved over `R` are:
- `ch_core`, `proposition_size_bound`;
- `windowHyp_of_rpow`, `windowHypU_of_windowHyp`;
- `landau_window`, `landau_window_key`, `landau_window_ineq`;
- `kernel_integral`, `landau_tails`, `landau_tails_chernoff`;
- `landau_coeff`;
- `landau_dichotomy`, `landau_nearest`;
- `landau_cauchy`, `landau_pole_re_le_bound`.

Most of them have integrals in their statements or need a large proof port.

## OUTCOME

**QED (12/12)** within the three-axiom standard. The audit is OK and there
are no `Admitted`. The allowlist-clean logarithm removes the `ln` / `rpow`
blocker reported in the previous finding.

The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 12 / warn 0 / bug 0.**
