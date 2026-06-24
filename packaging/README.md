# Standalone packages

Self-contained, reusable Rocq packages extracted from this corpus. Each is a
low-footprint, well-factored kernel that other projects can depend on without
pulling in the application-level geometry proofs. Every package builds three
ways — **opam**, **dune**, and **nix** — following the
[rocq-community/templates](https://github.com/coq-community/templates) layout.

Sources are vendored on demand from the corpus via a per-package `MANIFEST` +
`assemble.sh` (single source of truth — the `.v` files live in `theories/` and
`theories-flocq/`, never duplicated here), and `make package` produces a
self-contained opam source tarball.

| Package | Files | Deps | Axioms | What it is |
|---|---|---|---|---|
| [`coq-robust-predicates`](./rocq-robust-predicates/) | 15 | Flocq | classical-reals only | Machine-checked robust binary64 geometric predicates (orientation, segment intersection, error-free expansions), sound vs. exact arithmetic. Fills a real ecosystem gap — no verified Rocq package for Shewchuk-style predicates existed before. |
| [`coq-spatial-algebra`](./rocq-spatial-algebra/) | 2 | Stdlib only | **none** (axiom-free) | DE-9IM intersection-matrix algebra + integer orientation-determinant overflow bounds. A tiny, dependency-free entry point for formal GIS / spatial-relation reasoning. |

## Releasing

Each package publishes via its own GitHub Actions workflow
(`.github/workflows/package-*.yml`): a release tagged `robust-predicates-v*`
or `spatial-algebra-v*` builds the source tarball, attaches it (+ sha256) to
the release, and — when an `OPAM_PUBLISH_TOKEN` secret is configured — opens
the opam-repository PR via `opam publish`.

See each package's own `README.md` for build/install details and the headline
theorems it exposes.
