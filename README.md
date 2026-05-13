# NetTopologySuite.Proofs

Mechanically-verified formal proofs of foundational properties of the
algorithms in [NetTopologySuite](https://github.com/NetTopologySuite/NetTopologySuite).

Proofs are written in [Rocq Prover](https://rocq-prover.org/) (formerly Coq).
Every theorem in this repository terminates with `Qed.` — meaning the kernel
has checked the proof and rejected any unsound step. There are no admitted
lemmas. There is no `Axiom` declared beyond the standard library's classical
real arithmetic.

## Why this exists

NetTopologySuite is a port of JTS. JTS is itself a port of academic
computational-geometry algorithms with subtle robustness properties — the
kind that you find a bug in three years later when an unusual coordinate
configuration trips a sign flip. Unit tests sample the behaviour at
finitely many points and produce green CI. Formal proofs cover all of
ℝ² simultaneously.

The intent is not to verify every line of NetTopologySuite. That's
infeasible for a library this size, and most of the C# code is mechanical
plumbing where formal verification adds little value. The intent is to
verify the **load-bearing primitives** — the handful of small algorithms
that, if wrong, make everything above them suspect. Orientation, distance,
the convex-hull invariants, the buffer-curve angle relations.

When someone asks "are you sure the squared-distance optimisation can't
flip a result?", the answer is `Distance.dist_le_iff_dist_sq_le` and the
kernel-checked proof. Not "yes, the tests pass."

## What's in scope right now

### `theories/Distance.v` — Euclidean distance

- `dist_sq_nonneg` — squared distance is non-negative.
- `dist_sq_sym` — distance is symmetric.
- `dist_sq_zero_iff_eq` — two points are at distance zero exactly when their
  coordinates are equal.
- `sq_monotone_nonneg` — on the non-negative reals, squaring is monotone.
- **`dist_le_iff_dist_sq_le`** — for any non-negative threshold *t*,
  `dist(p, q) ≤ t` iff `dist_sq(p, q) ≤ t²`. This is the formal
  justification for the optimisation tracked in
  [locationtech/jts#1111](https://github.com/locationtech/jts/pull/1111) and
  the gap noted for `LineStringSnapper` in the JTS 1.21 alignment audit on
  [NetTopologySuite#828](https://github.com/NetTopologySuite/NetTopologySuite/issues/828).

### `theories/Orientation.v` — orientation predicate

- `cross_antisymmetric` — swapping the second and third arguments of the
  cross product flips the sign. (Justifies "directed orientation" being
  a coherent concept.)
- `cross_collinear_sym` — collinearity is preserved under argument swap.
- `cross_at_P0_is_collinear` / `cross_at_P1_is_collinear` — degenerate
  triangles have zero signed area.
- `cross_translation_invariant` — translating all three points by the
  same vector preserves orientation. (Justifies coordinate-frame
  normalisation never changing topological results.)

## Roadmap

Realistic next targets, ordered by ratio of "stripe of NTS this verifies" to
"effort":

1. **Robust orientation predicate** — Shewchuk-style filter conditions.
   Prove the unfiltered cross product agrees with the DD-arithmetic
   refinement when the filter is satisfied. This is the keystone for the
   library's robustness story.
2. **Convex hull invariants** — for a finite point set *S*, every point
   in *S* lies in the closed convex hull of *S*; the convex hull is
   itself convex; the hull's vertices are a subset of *S*.
3. **DD arithmetic** — addition is associative, multiplication
   distributes over addition under explicit bounds. Connects to
   [Flocq](https://flocq.gitlabpages.inria.fr/) for the floating-point
   model. This is where the "robust geometric predicates" claim becomes
   formally cashed-out.
4. **MIC center-is-interior** — the centre of the maximum inscribed
   circle of a non-degenerate polygon lies strictly in the polygon's
   interior.
5. **Buffer corner relations** — for a positive buffer distance, the
   buffer of a convex corner consists of an arc whose central angle
   equals the exterior angle.

## What this is NOT

- This is **not** a verified implementation of NTS. The C# code is not
  extracted from Rocq. The proofs are over an abstract model of points
  (pairs of reals) and the operations on them. If the C# implementation
  encodes the same mathematical operations, the proofs apply. If it does
  something subtly different (typical example: a fast-path that's not
  exactly equivalent on edge cases), the proofs don't catch it.
- This is **not** a substitute for unit tests. Tests cover behaviour the
  proofs don't reach: floating-point rounding, exceptions, performance,
  cross-platform consistency, interaction with the rest of the runtime.
- This is **not** complete. As of the initial seed it covers two algorithms.
  Growing this catalogue is the work.

## Build

```sh
# One-time setup (macOS via Homebrew):
brew install rocq

# Build all proofs:
coq_makefile -f _CoqProject -o Makefile
make
```

A successful `make` ends with `theories/*.vo` files and no errors. That
output is the certificate: each `.vo` file is a kernel-checked term whose
type is the corresponding theorem statement.

## Licence

BSD-3-Clause, matching NetTopologySuite's licence. See [LICENSE](LICENSE).

NetTopologySuite is itself a derivative work of JTS Topology Suite, which
is dual-licensed under EPL 2.0 / EDL 1.0. The formal specifications in
this repository are derived from NTS source code; where that is the case,
the BSD-3-Clause grant respects NTS's attribution requirements.

## Contributing

Pull requests welcome. New theorems must:

- compile under stock Rocq 9.x with no external dependencies beyond
  the standard library (Flocq is acceptable when DD arithmetic lands);
- terminate with `Qed.` — no `Admitted`, no `Parameter` standing in for
  a missing proof;
- include a header comment naming the NTS module the theorem corresponds
  to, so reviewers can cross-reference.
