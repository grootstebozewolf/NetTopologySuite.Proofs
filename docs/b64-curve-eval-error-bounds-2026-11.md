# Binary64 Bézier evaluation: a proved stability gap between Horner and de Casteljau

Two algebraically equivalent representations of the same polynomial need not
be numerically equivalent.

Take `pₙ(t) = (1 − 2t)ⁿ`. In the Bernstein basis its coefficients are
`bⱼ = (−1)ʲ`, so the control-value max norm is 1. In the power basis they are
`aᵢ = C(n,i)(−2)ⁱ`, whose absolute sum is

```
Σᵢ |aᵢ| = Σᵢ C(n,i) 2ⁱ = (1 + 2)ⁿ = 3ⁿ
```

That difference survives a formal floating-point analysis. In Rocq/Flocq we
prove binary64 forward-error bounds for Horner evaluation and for de Casteljau
evaluation. On this family, under the stated rounding and safety hypotheses,
the proved Horner main-error bound is at least `3ⁿ/3` times the proved
de Casteljau main-error bound. At n = 30 that factor is `3²⁹ = 68 630 377 364 883`
(about 6.9·10¹³).

This is a statement about **bounds**, not a claim that every Horner evaluation
realises its bound. Direct binary64 measurements do show the same qualitative
separation: at degree 30 the largest errors over 20 000 sampled points were
5.7·10⁻⁵ (Horner) and 7.5·10⁻²² (de Casteljau).

The point is therefore not simply that de Casteljau is stable. The choice of
representation changes what can be *proved* about the numerical behaviour of
an otherwise identical mathematical object.

topic: numerics · claimId: s1-b64-horner-gamma · witness: b64_horner_gamma
topic: numerics · claimId: s1-b64-decasteljau · witness: b64_decasteljau_err
topic: numerics · claimId: s1-b64-bezier-stability · witness: bezier_vs_horner_bound

Provenance: Rocq 9.2.0 + Flocq 4.2.2 (opam switch `nts-flocq`), repo base
`e198ea1`; modules `theories-flocq/B64_HornerGamma.v`,
`B64_DeCasteljau.v`, `B64_BezierStability.v`. Measurements:
`tests/B64CurveEvalMeasure/cmp.py` (CPython IEEE binary64, exact `Fraction`
reference, seed 1).

SUMMARY ok=3 warn=1 bug=0 — three Qed-closed results with the same four
Stdlib-Reals axioms as every module in the Flocq lane (`Print Assumptions` in
each file); the warning is the scope limit in §4 and §5 (bound-versus-bound,
max-norm, Bézier only).

## 1. Starting point: Horner was already proved

`B64_Horner.v` already contained a Qed-closed binary64 Horner bound,
`b64_horner_err`. It covers subnormals through an absolute `2⁻¹⁰⁷⁵` term per
operation, but states the result as a recursion (`hz_E`) rather than in the
conventional γₙ form. The first step was therefore not to re-prove Horner but
to close the gap between that machine-checked result and the textbook one.

## 2. Recovering the textbook Horner bound

Write `N = M + E`, the magnitude bound plus the error bound at one Horner
level. The existing recursion collapses to

```
N' = (1+u)² Z N + (1+u) m + (2+u)·2⁻¹⁰⁷⁵
```

and unrolling it gives, for degree n with `2nu < 1`, `u = 2⁻⁵³`,
`γₖ = k u/(1 − k u)`:

```
|fl(horner cs z) − horner cs z|  ≤  γ₂ₙ · Σᵢ mᵢ Zⁱ  +  2⁻¹⁰⁷⁵ · R
```

with `|cᵢ| ≤ mᵢ`, `|z| ≤ Z`. So the existing binary64 model recovers Higham's
γ₂ₙ Horner result while keeping an explicit absolute term for gradual
underflow; for `Z ≤ 1`, `R ≤ 3n(1+u)²ⁿ`. The overflow guard `hz_safe` is still
assumed, and coefficient and argument rounding remain separate budget lines,
as in `b64_horner_err`.

Formal witnesses (`B64_HornerGamma.v`): `b64_horner_gamma` (the bound),
`hg_N_bound` (the collapse), `hg_gamma2` (`(1+u)²ʲ − 1 ≤ γ₂ⱼ`),
`hg_R_le_unit`, and `hz_horner_R_sum` / `hz_M_is_horner` (Horner over R is the
power sum Σ cᵢ xⁱ, and `hz_M ms Z` is Σ mᵢ Zⁱ).

## 3. de Casteljau: why its bound has a different shape

The crucial difference is that de Casteljau never exposes the power-basis
coefficient growth. For `t ∈ [0,1]` the exact scheme forms convex
combinations of its inputs, so if every control value satisfies `|bᵢ| ≤ M`
then every exact intermediate value stays within `M`. The floating-point error
can then be tracked against a fixed `M` through all n rounds.

Evaluator: `node(x,y) = fl(fl(s·x) + fl(t·y))`, n rounds of the triangular
scheme, `t` a binary64 in [0,1], `s` a binary64 standing for `1 − t`. The
reference is the same control values through exact de Casteljau with weights
`(1−t, t)`.

`b64_decasteljau_err`: control values finite with `|bᵢ| ≤ M`, `|s − (1−t)| ≤ η`,
and the guard `(M+E)·4 + 1 ≤ 2¹⁰⁰⁰` imply the result is finite and

```
error ≤ ((1+κ)ⁿ − 1)·M + 2⁻¹⁰⁷⁵ (3+2u) n (1+κ)ⁿ,     κ = η + (1+η)(2u + u²)
```

* `η = 0` (s = 1−t exactly, e.g. t ∈ [½, 1] by Sterbenz, or a caller supplying
  both weights): `κ = 2u + u²`, main term ≈ `2nu·M`.
* `b64_decasteljau_err_fl`: `s = fl(1 − t)` gives `η = u + 2⁻¹⁰⁷⁵`.
* `b64_decasteljau_gamma`: the `nκ/(1 − nκ)·M` form when `nκ < 1`.
* `dc_scalar` is the one-node step; `dc_iter_inv` carries finiteness and the
  error invariant through the rounds.
* `B64_BezierStability.v : dcR_bern`: the exact reference *is* the Bernstein
  sum Σ bᵢ·`bern n i t`, with `bern` the corpus basis of `BernsteinBasis.v`.

The bound is in the max norm of the control values; nothing in it refers to
power-basis coefficients.

## 4. Same polynomial, exponentially different bounds

Both evaluators target the same real number (`alt_dcR_unit`,
`horner_binomial`: de Casteljau of the ±1 net and Horner of `C(n,i)(−2)ⁱ` both
equal `(1 − 2t)ⁿ`).

```
Bernstein:  bⱼ = (−1)ʲ                      ⇒  M = 1
Power:      aᵢ = C(n,i)(−2)ⁱ, Σ|aᵢ| = 3ⁿ    (hmaj_at_one)

de Casteljau main bound   ≲  6 n u            (≈ 2nu·M)
Horner main bound         ≳  2 n u · 3ⁿ       (the b64_horner_gamma instance)

ratio                     ≥  3ⁿ / 3
```

`bezier_vs_horner_bound` states exactly this for `2nu < 1` and `nκ₀ ≤ ½`:
`dc_main n · 3ⁿ ≤ 3 · horner_main n`, where `horner_main` is the main term of
`b64_horner_gamma` at `ms = hmaj n` (`horner_main_instance`). At n = 30 the
factor is `3²⁹ ≈ 6.9·10¹³`.

**Scope.** This compares two proved upper bounds on one family. It does not
prove Horner *is* that inaccurate, and the de Casteljau bound is a max-norm
bound, weaker than a componentwise Σ|bᵢ|Bᵢⁿ(t) bound.

Measured errors (`cmp.py`; 20 000 points per n, half uniform in [0.2, 0.8],
half within 10⁻³ of the root t = ½):

| n | max err Horner | max err de Casteljau | proved Horner main `2nu·3ⁿ` | proved dC main `6nu` |
|--:|--:|--:|--:|--:|
| 5 | 3.2e-15 | 6.1e-17 | 2.7e-13 | 3.3e-15 |
| 10 | 6.4e-13 | 7.8e-18 | 1.3e-10 | 6.7e-15 |
| 15 | 4.8e-11 | 8.1e-19 | 4.8e-08 | 1.0e-14 |
| 20 | 5.3e-09 | 8.2e-20 | 1.5e-05 | 1.3e-14 |
| 25 | 6.7e-07 | 7.9e-21 | 4.7e-03 | 1.7e-14 |
| 30 | 5.7e-05 | 7.5e-22 | 1.4e+00 | 2.0e-14 |

The measurements are not part of the proof and should not be read as a
tightness result: every measured error sits under its proved bound, and both
bounds are loose by different amounts (de Casteljau's measured error near the
root is far below `6nu` because the exact value there is tiny). They do exhibit
the qualitative behaviour the bounds suggest: Horner error grows rapidly with
degree on this family while de Casteljau stays extremely close to the exact
reference. Binary64 represents every `aᵢ` exactly only up to n = 30
(`C(n,i)2ⁱ < 2⁵³`); beyond that the Horner side would also carry
coefficient-rounding error.

## 5. What this says about geometry representation

A change of polynomial basis can preserve the exact real-valued curve while
changing its floating-point error analysis. Representation is therefore not
only a serialization or API concern: it can be part of the numerical contract
of a geometry implementation. What is established here is one explicit family
where that separation is provable, not a general theorem about all curves.

**Proved here**
- polynomial Bézier evaluation, one coordinate at a time;
- binary64, RNE multiply followed by RNE add;
- the gradual-underflow contribution (`2⁻¹⁰⁷⁵` per operation);
- an explicit overflow guard;
- exact and rounded `1 − t`;
- the exact de Casteljau value equals the Bernstein sum;
- the γ₂ₙ Horner bound and the Horner-versus-de Casteljau bound comparison.

**Not proved here**
- NURBS: rational weights and de Boor (the real-valued span reduction is
  `NurbsBezierSpan.v`);
- FMA variants;
- GEOS or NTS implementation correctness;
- extraction correspondence (no `oracle_bin` mode, no C#/Java port).

`ClothoidResidual.v` could consume `b64_horner_gamma` for its polynomial
residual; that wiring is not done here.

## 6. Draft note for the geos-devel 3.16 thread (not posted)

> Two equivalent representations of one polynomial can have provably different
> binary64 error bounds. For (1−2t)ⁿ the Bernstein coefficients are ±1 and the
> power coefficients sum to 3ⁿ in absolute value; in Rocq/Flocq the proved
> Horner bound exceeds the proved de Casteljau bound by at least 3ⁿ/3 (about
> 6.9·10¹³ at n = 30). The de Casteljau result: n rounds of
> `fl(fl(s·x)+fl(t·y))`, `|bᵢ| ≤ M`, `t ∈ [0,1]` ⟹ error ≤ ((1+κ)ⁿ−1)·M plus
> an underflow floor, κ = 2u+u² when s = 1−t exactly, including subnormals and
> the overflow guard. Measured errors at n = 30: 5.7e-5 (Horner) vs 7.5e-22
> (de Casteljau); the comparison is of upper bounds, not true errors.
> `theories-flocq/B64_DeCasteljau.v` in NetTopologySuite.Proofs. Scope: Bézier
> (not NURBS), max norm, no FMA, proof only.

Posting it is a decision for the repository owner; the claims above are
exactly what the Qed-closed files state.
