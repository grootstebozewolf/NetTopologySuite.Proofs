<!-- doc-kind: finding
date: 2026-11-20
Provenance: 7cebee2124d37d0ff60fa17b8d09ff6ca0ddbab0
Theorems: `QedRoots.v : cert_sound`, `QedRoots.v : cert_hyperbolic`, `QedRoots.v : factor_cert_sound`, `QedRootsExamples.v : P5_neighbourhood_simple_real_rooted`, `QedRootsExamples.v : double_root_box_uncertifiable`, `QedRootsExamples.v : no_real_roots_box_uncertifiable`, `QedRootsRefute.v : laguerre_hyperbolic`, `QedRootsRefute.v : lag_box_cert_sound`, `QedRootsExamples.v : P5up_neighbourhood_not_hyperbolic`
-->
# Hunt: an orientation-like certificate for RH (finite Jensen hyperbolicity)

## Question

Is there a finite, proof-producing invariant for the Riemann ξ-function that
plays the role orientation plays in computational geometry — extracted from
approximate analytic data, reduced to a finite exact sign certificate, robust
once enclosures are tight, weaker than RH when finitely instantiated, and
sensitive to arithmetic structure rather than symmetry alone?

Candidate: hyperbolicity of finite Jensen polynomials

    ξ(1/2 + z) = Σ γ(n)/n! · z^(2n),   J^{d,n}(X) = Σ_{j=0}^d binom(d,j) γ(n+j) X^j

certified by an exact root count from rigorous coefficient enclosures.
Pólya: RH ⇔ J^{d,n} hyperbolic for all d,n. The hunt fixes a finite
F ⊂ ℕ×ℕ, which does not imply RH. **Not an attempt to prove RH.**

### QEX-1 (prior, literature)

> Symmetry alone does not determine critical-line confinement.
> Witness: Davenport–Heilbronn (functional equation s ↔ 1−s, no Euler
> product, zeros off the line).

Any invariant built only from the functional equation / conjugation /
reflection / symmetry-derived zero counting is insufficient.

## Plan (unchanged from the brief)

1. **Probe before ξ** — mint the certificate on an explicit rational
   polynomial; find a sufficient enclosure width. *(this ticket, done)*
2. ξ: rigorous enclosures of γ(n+j), feed the same checker for one (d,n).
3. Davenport–Heilbronn control through the *same* acceptance rule
   (QEX-2A / QEX-2B), invariant frozen before the run.
4. de Bruijn–Newman stays calibration / prior art only.

Non-goals: RH; unbounded zero search; reading finite passes as evidence;
hiding uncertainty behind precision; changing the invariant after the DH run.

## Design decision: sign alternation instead of a Sturm sequence

Toolchain: Rocq 9.2.0 + rocq-stdlib 9.2.0 (no MathComp, no Coquelicot).

The stack has **stdlib Reals only** (no MathComp `real_closed`, no
Coquelicot), so a general Sturm theorem would have to be built from scratch.
For the hyperbolicity question a cheaper exact root count suffices:

> deg P = d, lead P ≠ 0, rational x_0 < … < x_d with
> sign P(x_i) strictly alternating  ⇒  d distinct real roots (IVT, one per
> gap)  ⇒  P = lead·Π(X − r_i)  ⇒  these are *all* the real roots.

The certificate is literally **d+1 exact signs at rational points** — the
orientation-predicate analogue asked for in Q5. Each sign is decided from
the exact rational range of P(x_i) over the coefficient box (Horner with an
exact scalar is exact, the map c ↦ P(x) being linear), so the analytic
uncertainty stays left of the bridge and the predicate is exact.

Trade-off, recorded rather than hidden: the certificate cannot see repeated
roots (see Q4). A Sturm/Sturm–Habicht route would, and remains the upgrade
path if a ξ instance ever needs it; ξ Jensen polynomials are expected to
have simple roots for the instances in view, so the cheap route is the
right first rung.

## Ladder

| step | claim | OUTCOME | artifact |
|---|---|---|---|
| 0 | real-coefficient polynomial, strict sign alternation at d+1 increasing points ⇒ exactly d distinct real roots and full factorisation | QED | `alternating_simple_real_rooted` (IVT via `IVT_cor`, synthetic division `quot_spec`, `factor_from_roots`) |
| 1 | rational box `[lo_j,hi_j]` + rational points; boolean checker `box_cert` (Q, `vm_compute`) | definition | `box_cert`, `ieval`, `isign` |
| 2 | bridge: `box_cert b xs = true` ⇒ **every real** p in the box is simple-real-rooted ⇒ hyperbolic | QED | `cert_sound`, `cert_hyperbolic` |
| 3 | probe P = (X+1)(2X+1)(X+2)(3X+1)(X+3) = 6+41X+97X²+97X³+41X⁴+6X⁵ (self-reciprocal, positive coeffs, negative roots — ξ-Jensen shape); points −4, −5/2, −3/2, −3/4, −2/5, −1/4; signs `[-1;1;-1;1;-1;1]` | QED | `P5_cert`, `P5_signs`, `P5_simple_real_rooted` (proof uses only the 6 signs, never the factored form) |
| 4 | enclosure width: absolute ±1/20 on every coefficient preserves the certificate (min normalised margin \|P(x)\|/Σ\|x\|^j = 8/133 ≈ 0.060 at x = −5/2, −2/5) | QED | `P5_cert_width`, `P5_neighbourhood_simple_real_rooted` |
| 5 | ±1/10 rejected **at these points** (statement about the checker, not a non-hyperbolic witness) | QED (checker = false) | `P5_reject_width` |
| 6 | multiplicity semantics: `hyperbolic` (multiset of roots) and `simple_real_rooted` (NoDup) are separate definitions; (X+1)²(X+2) is hyperbolic yet no box/points ever certify it; X²+1 never certifies | QED | `D3_hyperbolic`, `double_root_box_uncertifiable`, `no_real_roots_box_uncertifiable` |

`Print Assumptions` on `P5_neighbourhood_simple_real_rooted` and
`double_root_box_uncertifiable`: only `ClassicalDedekindReals.sig_not_dec`,
`sig_forall_dec`, `functional_extensionality_dep` (stdlib Reals
foundations). No `Classical_Prop.classic`, no `Admitted`.

Build: graduated from the probe `docs/h1-vacuity/JensenSignCertificate.v`
(now removed) into the corpus as `theories/QedPoly.v`, `QedInterval.v`,
`QedRoots.v`, `QedRootsExamples.v` (in `_CoqProject` and `_CoqProject.full`),
packaged as `packaging/rocq-qed-roots`. See "Programme" below.

| 7 | multiplicities expressible: `factor_cert` (p ≡ c·Π fₖ over Q, each fₖ box-certified, factors may repeat) ⇒ hyperbolic; (X+1)²(X+2) and (2X²+5X+2)²(X+3) certified | QED | `factor_cert_sound`, `D3_hyperbolic`, `Q5_hyperbolic` |

| 8 | refutation: hyperbolic ⇒ Laguerre form p′² − p·p″ ≥ 0 everywhere; `lag_box_cert` (interval upper bound < 0 at one rational x) ⇒ no p in the box is hyperbolic; complete in degree 2 (vertex value = discriminant/2, i.e. Turán) | QED | `laguerre_hyperbolic`, `lag_box_cert_sound`, `quadratic_negative_discriminant_not_hyperbolic` |
| 9 | instances: X²+1 at 0, (X+1)(X²+1) at 1/2; P5 lifted by +3 refuted on a ±1/2 box at −1/4, against P5 itself certified on ±1/20 | QED | `x2_plus_one_not_hyperbolic`, `cubic_not_hyperbolic`, `P5up_neighbourhood_not_hyperbolic` |

Why step 8 matters for the control: QEX-2B ("DH fails while ξ passes")
needs DH's failure to be a *theorem*, not a failed check. The DH run now
has a frozen pair of instruments: `box_cert` (accept) and `lag_box_cert`
(refute), provably never both true on overlapping boxes
(`box_cert_lag_exclusive`). A DH instance that neither accepts nor refutes
is recorded as undecided at that (d,n), not as a separation.

## Programme (reframed 2026-11-20)

Not "formalize RH" but: **the minimal verified computational substrate in
Rocq on which RH-adjacent statements become finite, kernel-checkable
certificates.** Each rung ends independently in QED or QEX.

```
qedinterval → qedpoly → qedroots → qedanalytic → qedjensen → RH experiments
```

| layer | library | status |
|---|---|---|
| qedinterval | `QedInterval.v` (in `rocq-qed-roots` for now) | QED: exact rational enclosure + strict sign; `in_box` is the interface qedanalytic must produce |
| qedpoly | `QedPoly.v` (in `rocq-qed-roots` for now) | QED: eval, synthetic division, factor theorem, Q multiplication |
| qedroots | `QedRoots.v`, `QedRootsRefute.v` → package `rocq-qed-roots` | QED: sign-alternation + factor certificates (accept), Laguerre certificate (refute, complete in degree 2); **OPEN**: Sturm / Cauchy index, squarefree decomposition, refutation complete beyond degree 2 |
| qedanalytic | — | OPEN: certified enclosures of γ(n) (Flocq / interval), producing `in_box` |
| qedjensen | — | OPEN: define J^{d,n}_Ξ, prove the certified coefficients are the intended ones, run `box_cert` |
| DH control | — | OPEN: same `box_cert`, frozen |

`rocq-qed-poly` / `rocq-qed-interval` split out of `rocq-qed-roots` when a
second consumer needs them without roots. "Mint" in the CONTEXT.md sense
(installable from the Rocq opam archive) happens on a
`rocq-qed-roots-v*` release via `.github/workflows/package-qed-roots.yml`.

## Answers to the probe questions

1. **Sturm / Cauchy index / RCF machinery in the stack?** No. The switch
   carries rocq-stdlib + Flocq only. MathComp `real_closed` has root-counting
   machinery but is not installed; adding it is a toolchain decision, not
   taken here. The sign-alternation route needs only stdlib `IVT_cor`.
2. **Coexistence with Flocq?** Moot for now: the probe imports no Flocq and
   compiles in the same switch with the same `-Q` flags as the other probes.
3. **Minimal enclosure→certificate theorem:** `cert_sound` —
   `in_box p b → box_cert b xs = true → simple_real_rooted p`, quantified
   over *real* coefficient lists, so ξ's real γ(n+j) plug in directly once
   rational enclosures are proved.
4. **Repeated roots:** the certificate proves the stronger
   `simple_real_rooted`; `hyperbolic` is derived by a separate lemma and is
   stated with a root multiset. The certificate is sound but incomplete —
   `double_root_box_uncertifiable` shows a repeated-root hyperbolic polynomial
   always fails, so a failure is never read as "not hyperbolic", and
   nothing silently strengthens the target predicate.
5. **Small exact sign list?** Yes: d+1 signs in {−1,+1} at rational points,
   each decided by an exact rational interval (`P5_signs`). This is the
   orientation analogue; robustness is the open condition "every enclosure
   excludes 0".

## Not done (by design, per the brief)

- No ξ coefficient has entered the trusted path. Next rung: rigorous
  rational enclosures of γ(n) (needs a certified evaluation of the
  ξ Taylor coefficients — the analytic-number-theory half), then one
  (d,n) through `box_cert` unchanged.
- Davenport–Heilbronn control not run. The rules applied to it are
  `box_cert` (accept) and `lag_box_cert` (refute) exactly as committed;
  both are now frozen.

SUMMARY ok=9 warn=0 bug=0

OUTCOME: QED (qedroots rung, packaged as rocq-qed-roots) — rational sign certificate: interval-enclosed real coefficients → exact rational sign list → simple real-rootedness → hyperbolicity, all `Qed`. Hunt overall stays OPEN: ξ enclosures and the DH control are the next rungs.

> Superseded-by: docs/attacks/2026-11-20-qedroots-vertex-cert.md
