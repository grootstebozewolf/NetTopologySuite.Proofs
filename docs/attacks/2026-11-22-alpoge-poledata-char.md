<!-- doc-kind: finding
date: 2026-11-22
Provenance: 6bdadea
Theorems: `AlpogePoleDataChar.v : poleData_abstract_r`, `AlpogePoleDataChar.v : poleData_char_nontriv_r`, `AlpogePoleDataChar.v : poleData_char_triv_r`
-->
# Alpöge main line: poleData_char refined (the inventory input of poleData)

Requested: `poleData_char`. The sixth batch refined `poleData`
(`AlpogeSixthLandau.v : poleData_r`), but took the per-character statement
`poleData_char` (poleData.lean l.137) as an inventory hypothesis
(`CHAR1`/`CHAR2`, in the `CharPole` shape). This finding rebuilds
`poleData_char`'s own proof.

The work is in `docs/h1-vacuity/AlpogePoleDataChar.v`. It is within the
three-axiom allowlist (`scripts/audit_axioms.sh` OK), with no `Admitted`.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source; nothing was built.

## What is rebuilt

| Lean | Rocq | the proof |
|---|---|---|
| `poleData_abstract` (l.22) | `poleData_abstract_r` | Below the table. |
| `poleData_char`, χ ≠ 1 (l.226) | `poleData_char_nontriv_r` | `g = L(χ,·)` with `k = 0`. The Laplace value is `mellin_Gchi_of_ne_one` after `poleData_change`, using `0·(1 − s)` vanishing. |
| `poleData_char`, χ = 1 (l.140) | `poleData_char_triv_r` | `g = (s−1)ζ(s)`, patched to 1 at `s = 1` (`gT`), with `k = 1`. `hgz` (`g w ≠ 0 ↔ ζ w ≠ 0`) is proved. The Laplace value matches `mellin_Gchi_modOne` by `field`: `g′/g = 1/(s−1) + ζ′/ζ`, with `g′(1) = γ`. |

**How `poleData_abstract_r` is proved.** It defines
`Φ s = −(dslope N 1 s)/s`, where `N s = g′/g − s·c + k(1 − s)` and
`c = g′(1)/g(1)`. Four properties follow.
1. **The formula off `s = 1`.** `N 1 = 0`. The case `s = 0` is handled
   separately, because division by 0 gives 0 on both sides.
2. **Analyticity off the zeros of g.** At `ρ = 1` it comes from `dslope`. At
   `ρ ≠ 1` it comes from congruence with `(N s − N 1)/(s − 1)`.
3. **Simple poles.** At a zero of order m, `logDeriv_local` and an explicit
   analytic remainder give residue `m·(−1/(ρ(ρ−1)))`. The remainder is the
   Lean one, `−m·dslope q ρ − (h₀ − s·c + k(1−s))·q`, where
   `q = 1/(s(s−1))`. The punctured-neighbourhood identity is checked by
   `field`.
4. **Isolated zeros.** These follow from the identity theorem and `g(1) ≠ 0`.

All three conclusions are exactly `AlpogeSixthLandau`'s `CharPole`, so they
discharge `poleData_r`'s `CHAR1` and `CHAR2`. The carrier is ℂ = R×R, with
`Cc_field` supplying `field`. `CAnalyticAt` and `EvPunct` are
`AlpogeDeepStatements`' concrete definitions.

## Inputs left as hypotheses

- **[Mathlib] analytic functions:**
  - closure of `AnalyticAt` under `+ − × ÷` and negation; constants and the
    identity map; `AnalyticAt.congr`;
  - `dslope_of_ne`, and analyticity of `dslope`;
  - `Differentiable.analyticAt` and `AnalyticAt.deriv`;
  - the identity theorem and isolated zeros.
- **[Mathlib] ζ and L-functions:**
  - `differentiable_LFunction` and `LFunction_apply_one_ne_zero`;
  - `riemannZeta_residue_one` and differentiability, which make the patched
    `g` entire;
  - `deriv g s = ζ + (s−1)ζ′` for `s ≠ 1`;
  - `tendsto_riemannZeta_sub_one_div`, giving `g′(1) = γ`;
  - `riemannZeta_one_ne_zero`, and `riemannZeta_ne_zero_of_one_le_re`.
- **[inventory]:** `logDeriv_local`, and the two Mellin identities composed
  with `poleData_change`. The Mellin identities are the arithmetic content:
  `mellin_Gchi_modOne` and `mellin_Gchi_of_ne_one`, via `mellin_ramp`.

## Ledger

`AlpogeSkeleton.v` now cites the refinement on the `poleData` row and `Check`s
the three theorems. The counts are unchanged: 53/53 refined and 46 proved
over R. `poleData_char` is a sub-lemma of the `poleData` item, not a ledger
row.

## OUTCOME

**QED (refined).** The deepest inputs still assumed are now the Mellin
identities, `logDeriv_local` and the ζ/L-function facts above. Alongside
them stay the `TopShape` link facts and `askExp`. The Alpöge verdict is
unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 3 / warn 0 / bug 0.**
