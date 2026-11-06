# Binary64 curve-evaluation error bounds: Horner γ₂ₙ, de Casteljau, and the stability gap

topic: numerics · claimId: s1-b64-horner-gamma · witness: b64_horner_gamma
topic: numerics · claimId: s1-b64-decasteljau · witness: b64_decasteljau_err
topic: numerics · claimId: s1-b64-bezier-stability · witness: bezier_vs_horner_bound

Provenance: Rocq 9.2.0 + Flocq 4.2.2 (opam switch `nts-flocq`), repo base
`e198ea1`, modules `theories-flocq/B64_HornerGamma.v`,
`theories-flocq/B64_DeCasteljau.v`, `theories-flocq/B64_BezierStability.v`.
Measurements: `tests/B64CurveEvalMeasure/cmp.py` (CPython IEEE binary64,
exact `Fraction` reference, seed 1).

SUMMARY ok=3 warn=1 bug=0 — three Qed-closed results, same four Stdlib-Reals
axioms as every module in the Flocq lane (`Print Assumptions` in each file);
the one warning is the scope limit in §4 (bound-vs-bound, max-norm).

## 1. What was already there

`B64_Horner.v : b64_horner_err` (claim `s1-b64-horner`) already proves that
binary64 Horner is finite and within a recursive bound `hz_E` of the same
coefficients evaluated exactly at the same argument, including subnormals
(`u|x| + 2⁻¹⁰⁷⁵` per operation). It was not in the textbook shape.

## 2. Horner: the γ₂ₙ-shaped corollary (`B64_HornerGamma.v`)

* `hz_horner_R_sum`: Horner over R *is* the power sum Σ cᵢ xⁱ; `hz_M_is_horner`:
  the majorant `hz_M ms Z` is Σ mᵢ Zⁱ.
* `hg_N_bound`: with N = hz_M + hz_E the recursion collapses to
  `N' = (1+u)² Z N + (1+u) m + (2+u)·2⁻¹⁰⁷⁵`, hence
  `N ≤ (1+u)²ⁿ·hz_M + 2⁻¹⁰⁷⁵·hg_R`.
* `b64_horner_gamma`: for degree n with `2nu < 1`

  `|fl(horner cs z) − horner cs z| ≤ γ₂ₙ · Σ mᵢ Zⁱ + 2⁻¹⁰⁷⁵ · hg_R`,
  `γₖ = k u/(1 − k u)`, `u = 2⁻⁵³`.

  This is Higham's Horner bound. The extra term is the absolute underflow
  floor, which the relative-error model does not have but binary64 does;
  for Z ≤ 1 it is ≤ 3n(1+u)²ⁿ·2⁻¹⁰⁷⁵ (`hg_R_le_unit`). It still assumes the
  `hz_safe` overflow guard and treats coefficient / argument rounding as
  separate budget lines, exactly as `b64_horner_err` does.

## 3. de Casteljau (`B64_DeCasteljau.v`)

Evaluator: `node(x,y) = fl(fl(s·x) + fl(t·y))`, n rounds of the triangular
scheme, `t` a binary64 in [0,1], `s` a binary64 standing for `1 − t`. The
reference is the same control values through exact de Casteljau with weights
`(1−t, t)`.

`b64_decasteljau_err`: control values finite with `|bᵢ| ≤ M`,
`|s − (1−t)| ≤ η`, guard `(M+E)·4 + 1 ≤ 2¹⁰⁰⁰` ⟹ finite and

`error ≤ dc_iter η M n 0 ≤ ((1+κ)ⁿ − 1)·M + 2⁻¹⁰⁷⁵ (3+2u) n (1+κ)ⁿ`,
`κ = η + (1+η)(2u + u²)`.

* `η = 0` (s = 1−t exactly, e.g. t ∈ [½, 1] by Sterbenz, or a caller that
  supplies both): `κ = 2u + u²`, so the main term is ≈ `2nu·M`.
* `b64_decasteljau_err_fl`: `s = fl(1 − t)` gives `η = u + 2⁻¹⁰⁷⁵`.
* `b64_decasteljau_gamma`: `n κ/(1 − nκ)·M` form when `nκ < 1`.
* The step lemma `dc_scalar` carries `fin` through the rounds and the
  invariant `|exact| ≤ M` is the convexity of de Casteljau for `t ∈ [0,1]`.
* `B64_BezierStability.v : dcR_bern`: the exact reference *is* the Bernstein
  sum Σ bᵢ·`bern n i t`, with `bern` the corpus basis of `BernsteinBasis.v`.

The bound is in the max-norm of the control values. There is no factor from
the monomial basis, which is the point of the next section.

## 4. The comparison, and its scope

Family `pₙ(t) = (1−2t)ⁿ`: Bernstein coefficients bⱼ = (−1)ʲ (M = 1); power
coefficients aᵢ = C(n,i)(−2)ⁱ with Σ|aᵢ| = 3ⁿ (`hmaj_at_one`). Both
evaluators target the same real number (`alt_dcR_unit`, `horner_binomial`).
`bezier_vs_horner_bound` (for `2nu < 1`, `nκ₀ ≤ ½`):

`dc_main n · 3ⁿ ≤ 3 · horner_main n`

i.e. the proved Horner main term (≥ 3ⁿ·2nu, the `b64_horner_gamma` instance at
`ms = hmaj n`, `horner_main_instance`) is at least 3ⁿ/3 times the proved
de Casteljau main term (≤ 6nu).

**Scope.** This compares two proved upper bounds. It does not prove that
Horner *is* that inaccurate, and the de Casteljau bound is a max-norm bound,
weaker than a componentwise Σ|bᵢ|Bᵢⁿ(t) bound. Measured errors
(`cmp.py`, 20 000 points per n, half uniform in [0.2, 0.8], half within 10⁻³
of the root t = ½):

| n | max err Horner | max err de Casteljau | proved Horner main `2nu·3ⁿ` | proved dC main `6nu` |
|--:|--:|--:|--:|--:|
| 5 | 3.2e-15 | 6.1e-17 | 2.7e-13 | 3.3e-15 |
| 10 | 6.4e-13 | 7.8e-18 | 1.3e-10 | 6.7e-15 |
| 15 | 4.8e-11 | 8.1e-19 | 4.8e-08 | 1.0e-14 |
| 20 | 5.3e-09 | 8.2e-20 | 1.5e-05 | 1.3e-14 |
| 25 | 6.7e-07 | 7.9e-21 | 4.7e-03 | 1.7e-14 |
| 30 | 5.7e-05 | 7.5e-22 | 1.4e+00 | 2.0e-14 |

Every measured error sits under its proved bound. The two bounds are pessimistic
in different amounts (Horner's measured error tracks its bound within ~4
orders at n = 30; de Casteljau's measured error at the root is far below `6nu`
because the exact value is tiny there), so read the table as "the gap is real
and of the predicted exponential shape", not as a tightness claim. Binary64
represents every aᵢ exactly only up to n = 30 (`C(n,i)2ⁱ < 2⁵³`); beyond that the
Horner side would also carry coefficient-rounding error.

## 5. What this does and does not give GEOS

Gives: a Qed-closed binary64 error bound for evaluating a Bézier / Bernstein
curve component by de Casteljau, with the IEEE-754 ↔ exact-real bridge made
explicit (rounding model, subnormal floor, overflow guard, `fl(1−t)`), and a
Qed-closed γ₂ₙ bound for Horner.

Does not give: any NURBS statement (rational weights, knot insertion — de
Boor is not in this file; the real-valued span reduction is
`NurbsBezierSpan.v`), any extraction / `oracle_bin` mode, any GEOS or NTS
code wiring, or an `FMA` variant (the model is separate RNE multiply and add,
matching `b64_mult` / `b64_plus`). `ClothoidResidual.v` can consume
`b64_horner_gamma` for its polynomial residual; that wiring is not done here.

## 6. Draft note for the geos-devel 3.16 thread (not posted)

> The binary64 evaluation error of a Bézier curve component by de Casteljau
> has a machine-checked bound: n rounds of `fl(fl(s·x)+fl(t·y))`, control
> values with `|bᵢ| ≤ M`, `t ∈ [0,1]` ⟹ error ≤ ((1+κ)ⁿ−1)·M + (underflow
> floor), κ = 2u+u² when s = 1−t exactly (u = 2⁻⁵³), including subnormals and
> the overflow guard. Independently a γ₂ₙ bound for Horner. On (1−2t)ⁿ the
> proved Horner bound exceeds the de Casteljau bound by 3ⁿ/3, and measured
> errors at n = 30 are 5.7e-5 (Horner) vs 7.5e-22 (de Casteljau). Rocq/Flocq,
> `theories-flocq/B64_DeCasteljau.v` in NetTopologySuite.Proofs. Scope: Bézier
> (not NURBS), max-norm, no FMA, proof only.

Posting it is a decision for the repository owner; the claims above are
exactly what the Qed-closed files state.
