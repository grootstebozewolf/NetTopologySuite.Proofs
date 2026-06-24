# coq-spatial-algebra

A tiny, **dependency-free, axiom-free** Rocq library of spatial-relation
algebra, extracted from
[NetTopologySuite.Proofs](https://github.com/grootstebozewolf/NetTopologySuite.Proofs).

Two independent modules, both `Qed`-closed and **"Closed under the global
context"** (zero axioms — no classical reals, no functional extensionality),
depending only on Rocq's Stdlib (`List` / `Lia` / `ZArith`). No Flocq.

## What it provides

| Module | Contents | Headline results |
|---|---|---|
| **`DE9IM`** | The DE-9IM (Dimensionally Extended 9-Intersection Model) algebra behind OGC / SQL-MM spatial predicates: dimension values, intersection matrices, named relation patterns (`disjoint`, `intersects`, `contains`, `within`, `covers`, …), pattern matching, transpose. | `matrix_transpose_twice`, `matrix_matches_transpose`, `im_contains_transpose_within` (a relation and its converse are transposes) |
| **`RelateIntDetBound`** | The 2D orientation determinant `idet` over integer coordinates, with proven magnitude/overflow bounds for the safe-coordinate regime. | `idet_abs_le_sq`, **`idet_fits_int64_for_int32_coords`** (orient2d over int32 coords never overflows int64) |

These are foundational building blocks for any project doing formal GIS /
spatial-relation reasoning (`DE9IM`) or robust-predicate overflow analysis
(`RelateIntDetBound`). They are independent of each other and of everything
else in the corpus.

## Build & install

The `.v` files are vendored from the corpus via a manifest (so they never
silently drift from the source of record). From a clone of the parent repo:

```sh
cd packaging/rocq-spatial-algebra
./assemble.sh            # copy the 2 source files from the corpus
make                     # build
make install             # install to user-contrib under NTS.Proofs
```

Requirements: `rocq-core >= 9.0` and `rocq-stdlib >= 9.0` (no Flocq).

To produce a standalone opam source tarball (self-contained, no corpus needed):

```sh
make package             # -> dist/coq-spatial-algebra.tar.gz
```

## Usage

```coq
From NTS.Proofs Require Import DE9IM RelateIntDetBound.
Check im_contains_transpose_within.
Check idet_fits_int64_for_int32_coords.
```

## License

BSD-3-Clause (see [`LICENSE`](./LICENSE)), same as the parent corpus.
