# coq-robust-predicates

Machine-checked **robust geometric predicates for binary64 (IEEE-754 double)
coordinates**, with `Qed`-closed soundness against exact arithmetic — extracted
as a small, self-contained Rocq library from
[NetTopologySuite.Proofs](https://github.com/grootstebozewolf/NetTopologySuite.Proofs).

Every theorem ends in `Qed`. The only axioms are the standard classical-reals
decidability and functional extensionality used throughout the parent corpus
(visible in the `Print Assumptions` lines printed at build time).

## What it provides

| Area | Headline result | File |
|---|---|---|
| **2D orientation, exact sign** | `b64_orient2d_exact_sound` — the expansion-based orient2d sign matches the sign of the real determinant `cross_R_BP` | `Orient_b64_exact_full.v` |
| **Adaptive float filter** | `b64_orient_sign_filtered_sound_small_int` — fast floating-point filter is sound vs. `cross_R_BP` in the integer-safe regime | `Orient_b64_exact.v` |
| **Error-free transforms** | `sign_of_expansion_correct` — sign of a nonoverlapping expansion (built from TwoSum / Dekker / fast-expansion-sum) equals the sign of its real value | `B64_Expansion.v` |
| **Segment intersection** | `intersect_*_R_eq_strict_point`, denominator-safety + finiteness lemmas for the binary64 intersection point vs. its real value | `Intersect_b64_exact.v` |
| **Integer overflow bounds** | determinant magnitude bounds for the int-safe regime (0 axioms) | `Orientation.v` (base) |

The library sits **on top of Flocq** (the IEEE-754 substrate) and complements
rather than competes with existing ecosystem packages: GeoCoq is
synthetic/axiomatic (no coordinates or floats), so this is the analytic +
floating-point-robustness layer it does not address. There is currently no
other Rocq/opam package providing verified Shewchuk-style robust predicates
(only unverified C, e.g. Shewchuk's `predicates.c` and `libigl-predicates`).

### Honesty note (Shewchuk Theorem 13)

The textbook *strong*-nonoverlap postcondition of Shewchuk's Theorem 13 is
**false as stated** under this corpus's half-ulp `nonoverlap_strict` predicate
(machine-checked counterexample in the parent corpus). Consequently the
unconditional results shipped here are the ones that do **not** depend on it
(exact orientation in the int-safe / small-int regime). The *adaptive Stage-D
decoder* and its soundness theorem — which do require the general headline —
live in the parent corpus, where that headline is carried as an **explicit,
type-visible hypothesis** rather than a hidden `Admitted`. This package
therefore exposes only fully unconditional `Qed`s.

## Build & install

This package vendors its `.v` files from the corpus via a manifest (so they
never silently drift from the source of record). From a clone of the parent
repo:

```sh
cd packaging/rocq-robust-predicates
./assemble.sh            # copy the 15 source files from the corpus
make                     # build (prints Print Assumptions footprints)
make install             # install to user-contrib under NTS.Proofs[.Flocq]
```

Requirements: `rocq-core >= 9.0` and `coq-flocq >= 4.2.0`.

To produce a standalone opam source tarball (self-contained, no corpus needed
to build it):

```sh
make package             # -> ../coq-robust-predicates.tar.gz
```

## Namespace

Modules keep their provenance namespaces, `NTS.Proofs.*` (exact-real / integer
spec base) and `NTS.Proofs.Flocq.*` (binary64 layer), e.g.:

```coq
From NTS.Proofs.Flocq Require Import Orient_b64_exact_full.
Check b64_orient2d_exact_sound.
```

## Contents (15 files)

Source-of-record paths are listed in [`MANIFEST`](./MANIFEST): 4 exact-real
spec files (`Orientation`, `Segment`, `Distance`, `Intersect`) and 11 binary64
files (`Validate_binary64`, `Orientation_b64`, `B64_bridge`, `B64_lib`,
`Orient_b64_R`, `Orient_b64_sound`, `Orient_b64_exact`, `Orient_b64_exact_full`,
`B64_Expansion`, `Intersect_b64`, `Intersect_b64_exact`). The set is closed
under intra-corpus imports; the only external dependencies are Rocq's Stdlib
and Flocq.

## License

BSD-3-Clause (see [`LICENSE`](./LICENSE)), same as the parent corpus.
