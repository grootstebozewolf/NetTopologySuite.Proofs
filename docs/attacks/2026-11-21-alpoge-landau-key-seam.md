<!-- doc-kind: finding
date: 2026-11-21
Provenance: 26a92dc
Theorems: `LandauKeyRebuilt.v : tails_params`, `LandauKeyRebuilt.v : tails_pow_core`, `LandauKeyRebuilt.v : tails_rebuilt`, `LandauKeyRebuilt.v : key_rebuilt`, `LandauKeyRebuilt.v : landau_window_full`
-->
# Alpöge main line: the `KEY` seam of `landau_window` closed

Follows `2026-11-21-alpoge-win-seam-closed.md`. That finding left `LW`
meeting `landau_window_rebuilt` at `KEY`, the coefficient bound produced by
`landau_window_key`. This slice derives `KEY` from the window hypothesis's
consequences and `landau_tails`, and machine-checks `landau_tails`'s
parameter arithmetic. External subject: mirror
`CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read from source; nothing was
built.

## `landau_window_key` and `landau_tails` (read from source)

**`landau_window_key`** (`landauWindow.lean`, l.40–73). It fixes `σ` and `C`
from `landau_tails`, and `C₀` from `PoleData.growth`. Then, for every `η` and
window `U` from `WindowHypU`:

1. `landau_window_ineq` gives norm + Re ≤ `2(σ−θ)^{−k}·∫R e^{−θu}` +
   `2C₀·tail`.
2. `landau_coeff` identifies the Taylor coefficients with Laplace moments.
3. The window bound `∫R e^{−θu} ≤ e^{ηU}` and the tail bound `≤ C/σ^k`
   combine to `(2 + 2C₀|C|)·e^{ηU}/(σ−θ)^k`.

**`landau_tails`** (`landauTails.lean`, l.85–133).

- **Parameters:**
  - `l = 2 + 6/δ`;
  - `M = l(1+δ)`;
  - `σ = M(2+l)`;
  - `k = ⌈(1+δ/2)σU⌉`.
- **Split.** A Chernoff split (`landau_tails_chernoff`) bounds the tail
  integral by `e^{−lV}(σ−2−l)^{−(k+1)} + e^{lU}(σ−2+l)^{−(k+1)}`, with
  `V = (1+δ)U`.
- **Each term.** `landau_tails_pow` (via `σ/a ≤ e^{(σ−a)/a}`) turns each term
  into `e^c/a/σ^k`, provided its exponent satisfies `x + k(σ−a)/a ≤ c`, with
  `c = 1` and `c = 0` respectively.

## Rocq (`docs/h1-vacuity/LandauKeyRebuilt.v`, Stdlib over `Q`)

The six results below are *Closed under the global context*.

| theorem | mirrors | OUTCOME |
|---|---|---|
| `tails_params` | the parameter arithmetic of `landau_tails`. For `k ∈ [(1+δ/2)σU, (1+δ/2)σU+1]` it proves: `2 < σ`; `σ−2±l > 0`; `U ≤ k`; **T1** `k(2+l) ≤ a(1 + l(1+δ)U)`, the first exponent `≤ 1`; and **T2** `lU·b ≤ k(l−2)`, the second exponent `≤ 0`. It also reproduces Lean's identities `(2+l)(M−1) = a`, `(1+δ/2)(2+l) = M−1` and `(1+δ/2)(l−2) = l+1`. | **QED** |
| `ceil_nat` | the choice `k = ⌈X⌉₊`, with `X ≤ k ≤ X+1` | **QED** |
| `tails_pow_core` | `landau_tails_pow` with `exp` abstract (`1+t ≤ e^t`, additive, monotone) | **QED** |
| `tails_rebuilt` | `landau_tails`: the tail integral times `σ^k` is at most `e/(σ−2−l) + 1/(σ−2+l)`, for some `k ≥ U` | **QED** (given `CHER`) |
| `key_rebuilt` | `landau_window_key` gives `KEY` with constant `2 + 2C₀\|C_t\|` | **QED** (conditional) |
| `landau_window_from_windows`, `landau_window_full` | `landau_window` with `KEY` discharged by `key_rebuilt`. In `landau_window_full`, the tails input is also discharged by `tails_rebuilt` at `σ = tsig δ`, the value Lean picks. | **QED** (conditional) |

**Inputs of `landau_window_full`:**
- the `Assembly` inputs except `KEY`, namely `Hle`, `LF`, `HA`, `CAUCHY`,
  `POLE1` and `POLE2`;
- `WI`, i.e. `WindowHypU` plus `landau_coeff` plus `landau_window_ineq`. Its
  pointwise core is `window_ineq_discrete`.
- `XS`, which says `e^{ηU} ≤ s^k` for `U ≤ k` with `η = log s`;
- `CHER`, i.e. `landau_tails_chernoff`, which rests on `kernel_integral`;
- abstract `exp` laws.

## A correction to the earlier rebuild

`LandauWindowRebuilt.v`'s `KEY` quantified over rates `s ≥ 1`. Lean's
`WindowHypU` provides only `η > 0`, i.e. `s = e^η > 1`, so `s = 1` asked for
more than Lean supplies. `KEY` now quantifies over **`s > 1`**:
- `rate` produces `s = (1 + e/d)/2 > 1`;
- `window_contra` still receives `1 ≤ s`;
- `landau_window_rebuilt` recompiles unchanged in substance.

The earlier finding, `landau-window-assembled`, is not yet merged and is
updated accordingly. This tightened a hypothesis of the Rocq rebuild. It
does not affect the Lean development.

## Remaining seams

- **`LW` (`FormBRebuilt.v`) and `landau_window_full`.** Both live in
  different abstractions: an abstract type `C` with an `INT` window integral
  in the first, and points of `Q×Q` with explicit coefficients `A`, `B` in
  the second. Bridging them is `windowHypU_of_windowHyp` (change of
  variables) plus `poleData` (zeros as poles). That bridge is analytic
  representation, not logic, and is not composed.
- **`CH`.** This is `ch_core` to the per-host statement; not composed.
- **`ATWS` (`TopG`).** Not rebuilt.

## OUTCOME

**QED.** `landau_window` now runs in Rocq from the window hypothesis's
consequences (`WI`), through `KEY` and the case split, to `Re ρ ≤ θ`, in one
theorem (`landau_window_full`) with zero axioms. `landau_tails`'s parameter
choices are machine-checked to give both Chernoff exponents the required
bounds.

The audit verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 5 / warn 0 / bug 0.**
