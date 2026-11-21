<!-- doc-kind: finding
date: 2026-11-21
Provenance: 35f0b8c
Theorems: `LeanSkeletonRebuild.v : core_rebuilt`, `LeanSkeletonRebuild.v : ch_core_rebuilt`, `LeanSkeletonRebuild.v : ch_core_nonvacuous`, `LeanSkeletonRebuild.v : growth_size_bound`
-->
# The core slice: `ch_core` rebuilt (QED, conditional and non-vacuous)

**Target.** `ch_core` (`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:343`)
in the claimed RH/GRH Lean development (mirror
`CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`). It is the √X engine of the
main line:

`GmA ≤ x^(1/2+(C+3)ε) + SigA`

Stop condition set by the owner: **QED or QEX**. Outcome: **QED**,
conditional on named analytic inputs, with non-vacuity shown.

## Structure found in the source

`ch_core` composes two pieces:
1. **`CharacterBalanceMoves.core`** (`ChCore.lean:283`), a finite averaging
   argument:
   - **per coset:** for every `u₀ ∈ A₀`,
     `Σ_t Σ_j Re Th(u₀,t) ≤ Err + 2|TT|·m·b/x`, from `th_le`, `ch_balance`
     and the gap bound `gapA ≤ Err` (the `ch_top` / slope-inequality output);
   - **orthogonality:** `Σ_{u₀} (that sum) = |A₀|·(m·b·δ₂/2)·Σ_t(character sum)`
     (`sum_Th`);
   - **lower bound:** `|TT|·Y ≤ Σ_t(…)` with `Y = G − 4x^(1/2+ε)`
     (`one_char`);
   - **conclusion:** dividing by `|A₀| > 0` gives the **main inequality**
     `|TT|·m·b·(δ₂/2)·Y ≤ Err + 2|TT|·m·b/x`.
2. **`proposition_size_bound`** (`GrowthSizeBound`), already rebuilt in
   PR #1043 as `growth_size_bound`.

## Rocq (`docs/h1-vacuity/LeanSkeletonRebuild.v`, Part 7)

| theorem | content | OUTCOME |
|---|---|---|
| `core_rebuilt` | the averaging: per-coset bounds, the orthogonality identity and the lower bound `Y` imply the main inequality. A list of per-coset sums; cancelling `\|A₀\| > 0`. | **QED, zero axioms** |
| `ch_core_rebuilt` | `core_rebuilt` feeding `growth_size_bound`. With `δ₂ = ρ = nT2/n`, `Y = Gx − 4x^(1/2+ε)`, `w = 1/x` and `x = s²`, the main inequality times 2 is `growth_size_bound`'s `Hmain`; **conclusion `Gx ≤ x^(1/2+(C+3)ε)`** in exponential atoms | **QED, zero axioms** |
| `ch_core_nonvacuous` | **the hypotheses of `ch_core_rebuilt` are jointly satisfiable**. Concrete rationals: `x = 16`, `x^(ε/8) = 3`, `x^(ε/2) = 81`, `x^ε = 6561` (consistent: `e₂² = e`, `e₈⁴ = e₂`), `n = 200`, `nT = 34`, `m = 1`, `k = 16`, `Gx = 0`, … | **QED, zero axioms** |

All three are *Closed under the global context*. `ch_core_rebuilt`'s
section-free statement lists every input as a premise.

## What is assumed (the translation; not re-proved)

- **Analytic inputs**, as premises:
  - the per-coset bounds (`th_le` + `ch_balance` + `gapA ≤ Err`);
  - the orthogonality identity `sum_Th`;
  - `one_char`'s lower bound;
  - the `SizeWindows` constraints, including the √X window
    `x^(1/2−ε) ≤ m ≤ x^(1/2+ε/2)`.
- **Real powers** become atoms (`x^(a+b) = x^a·x^b`, monotone for `x ≥ 1`),
  as in `growth_size_bound`.
- **Non-vacuity** shows the premises are consistent. It says nothing about
  whether the Lean development *establishes* them; that is the
  `ch_top` / `Frame_at` / theta-lift content, still trusted.

## OUTCOME

**QED (conditional, non-vacuous).** The core slice's logic is machine-checked
in Rocq: averaging, then balance, then `Gx ≤ x^(1/2+(C+3)ε)`. Its premises are
shown jointly satisfiable. No QEX was found: no step of `ch_core` failed to
rebuild, and the hypothesis set is not vacuous. The Alpöge verdict stays
**PASS-STATIC / PENDING** (no Lean build), with the main line's logical
skeleton now rebuilt end to end.

**SUMMARY ok 3 / warn 0 / bug 0.**
