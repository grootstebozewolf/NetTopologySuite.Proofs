<!-- doc-kind: guide -->
# rocq-qed-roots

Kernel-checked **real-root certificates** for univariate polynomials, from
**rational coefficient enclosures** to an exact conclusion. Stdlib only.

Layer `qedroots` of the qed chain:

```
qedinterval → qedpoly → qedroots → qedanalytic → qedjensen → RH experiments
```

The programme: not "formalize RH", but the minimal verified computational
substrate on which finite RH-adjacent statements (e.g. hyperbolicity of one
Jensen polynomial of ξ) are stated, computed, and kernel-checked. Each rung
ends in QED or QEX on its own. Hunt ticket:
`docs/attacks/2026-11-20-jensen-hyperbolicity-certificate.md`.

`qedpoly` and `qedinterval` currently ship inside this package (their
closure is five files); they split into `rocq-qed-poly` /
`rocq-qed-interval` when a second consumer needs them without roots.

## What it provides

| Module | Contents | Headline |
|---|---|---|
| `QedPoly` | `peval`, `lead`, `prodlin`, synthetic division, continuity; Q-side `pmulQ`, `peqQ` with Q2R transport | `factor_from_roots`, `peval_Q2R_pmulQ` |
| `QedInterval` | `box` of rational coefficient intervals, exact range `ieval`, strict sign `isign`, `in_box` (the interface a future `qedanalytic` must produce) | `ieval_sound`, `isign_mul_neg` |
| `QedRoots` | `hyperbolic` (root multiset), `simple_real_rooted` (distinct, all zeros); `box_cert`, `factor_cert` | **`cert_sound`**, `cert_hyperbolic`, **`factor_cert_sound`**, `cert_roots_in_gaps` |
| `QedRootsRefute` | Formal derivative; Laguerre form `laguerre p x = p′² − p·p″`; `lag_box_cert` (interval upper bound of the Laguerre form < 0 at one rational point) | **`laguerre_hyperbolic`**, **`lag_box_cert_sound`**, `lag_box_cert_of_quadratic_neg_disc`, `quadratic_negative_discriminant_not_hyperbolic`, `box_cert_lag_exclusive` |
| `QedRootsExamples` | P5 = 6+41X+97X²+97X³+41X⁴+6X⁵ with a ±1/20 box; (X+1)²(X+2), (2X²+5X+2)²(X+3) via factors; negative controls | `P5_neighbourhood_simple_real_rooted`, `Q5_hyperbolic`, `double_root_box_uncertifiable` |

### `cert_sound`

```coq
Theorem cert_sound (p : list R) (b : box) (xs : list Q) :
  in_box p b -> box_cert b xs = true -> simple_real_rooted p.
```

`box_cert` checks, in exact rational arithmetic: d+1 increasing points; at
each, the exact enclosure of P(xᵢ) over the box has a strict sign; the
signs alternate; the leading interval excludes 0. The conclusion holds for
**every real** coefficient vector in the box — the certificate is a short
list of exact signs, the analogue of an orientation predicate.

### Multiplicity semantics

`hyperbolic` allows repeated roots; `simple_real_rooted` does not; they are
separate definitions joined by one lemma. `box_cert` (robust) can never
accept a repeated root (`double_root_box_uncertifiable`); `factor_cert`
(exact, over Q) expresses multiplicities as repeated factors. Neither is
claimed complete; a failed check proves nothing.

### Refutation

A failed `box_cert` proves nothing, so refutation has its own certificate.
For hyperbolic p, `L_p(x) = p′(x)² − p(x)p″(x) ≥ 0` everywhere (from
`L_{(X−r)g} = g² + (X−r)² L_g`). `lag_box_cert b x` bounds `L` from above
over the whole box at a rational x; if that bound is negative, **no** real
p in the box is hyperbolic. In degree 2, negative rational discriminant makes
`lag_box_cert` true at `(-b)/(2c)` (`lag_box_cert_of_quadratic_neg_disc`). Example:
`P5up_neighbourhood_not_hyperbolic` — every quintic within ±1/2 of
9+41X+97X²+97X³+41X⁴+6X⁵ is non-hyperbolic, while every quintic within
±1/20 of P5 (constant 6) is hyperbolic.

### Not yet here (OPEN)

Sturm sequences / Cauchy index (root counting for polynomials that are
*not* fully real-rooted), squarefree decomposition, refutation complete
beyond degree 2 (e.g. Newton inequalities / Sturm).

## Build

```sh
./assemble.sh            # vendor the .v files from the corpus (MANIFEST)
make && make install     # or: opam install .   /   dune build   /   nix-build
make package             # self-contained opam source tarball in dist/
```

Axioms (`Print Assumptions cert_sound`): `sig_not_dec`, `sig_forall_dec`,
`functional_extensionality_dep` — the stdlib classical-reals foundation.
No `Admitted`, no `Classical_Prop.classic`.

License: BSD-3-Clause.
