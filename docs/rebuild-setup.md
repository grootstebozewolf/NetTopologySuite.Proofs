# Rebuilding the Rocq/Coq setup

This doc captures how to reproduce the corpus's build environment from
scratch.  Two paths are supported: the **production toolchain** (Rocq
9.1.1 + coq-flocq 4.2.2) used in CI, and the **local sandbox** (Coq
8.18 + Flocq 4.1.3) used during interactive development.  Both paths
have known caveats, documented below.

## Production toolchain

The production build is pinned by `Dockerfile` and the
`.github/workflows/ci.yml` host runner.  Two jobs cover the corpus:

| Job          | Runner            | Builds                  | Toolchain                                                  |
|--------------|-------------------|-------------------------|------------------------------------------------------------|
| `rocq`       | `macos-latest`    | `theories/`             | Rocq 9.1.1 via Homebrew                                    |
| `rocq-flocq` | `ubuntu-latest`   | `theories-flocq/`       | Container: `rocq/rocq-prover:9.1.1-ocaml-4.14.2-flambda` + `coq-flocq.4.2.2` via opam |

The split is about **which runner builds which subdirectory**, not
about which proof standard each file meets.  Both subdirectories follow
the same Admitted policy (CI scripts scan both).

### Local production rebuild via Docker

The `Dockerfile` is the canonical pinned toolchain.  To rebuild
locally:

```bash
docker build -t nts-proofs-flocq:local .
docker run --rm nts-proofs-flocq:local
```

The container's default `CMD` cleans host-leaked build artefacts,
regenerates `Makefile.gen` from `_CoqProject.full`, and builds the full
corpus with `-j2`.  If any `.v` file fails to compile the container
exits non-zero.  Build time on a typical laptop: ~5 min cold (the
`opam install coq-flocq.4.2.2` step dominates), ~1-2 min for subsequent
runs with the image cached.

### Host-only (no Flocq) production rebuild

If you only need to verify `theories/` (no Flocq dependencies), the
Rocq 9.1.1 toolchain can be installed directly:

```bash
# macOS
brew install rocq

# Linux: opam install rocq.9.1.1 or download from rocq-prover.org

# Generate makefile + build
coq_makefile -f _CoqProject -o Makefile
make
```

This mirrors what the `rocq` CI job runs.  Build time: ~30s.

## Local sandbox (Coq 8.18 + Flocq 4.1.3)

The interactive-development sandbox used during this engagement runs
**Coq 8.18 + Flocq 4.1.3** under apt-installed packages.  The
production toolchain (Rocq 9.1.1 + Flocq 4.2.2) was not available via
the apt repos at the time of development, and the inria.fr opam
repository is blocked by the environment's network policy.

The sandbox needs two adjustments to build the production sources:

### 1.  Stdlib → Coq namespace translation

Rocq 9.x uses `From Stdlib Require Import ...`; Coq 8.18 uses
`From Coq Require Import ...`.  Translate via:

```bash
for f in theories-flocq/*.v; do
  sed 's/Stdlib/Coq/g' "$f" > /tmp/proof_test/theories-flocq/$(basename "$f")
done
```

The sandbox project file binds the same logical paths
(`-Q theories-flocq NTS.Proofs.Flocq`).

### 2.  Stub `B64_Pff_bridge.v`

`Flocq.Pff` (the Pff-compatibility layer providing
`b64_TwoSum_correct`, `b64_Dekker_correct`, etc.) is not present in
Flocq 4.1.3.  The sandbox uses a stub at
`/tmp/proof_test/theories-flocq/B64_Pff_bridge.v` that:

- Defines `b64_TwoSum` directly (computable form is portable).
- Declares `b64_TwoSum_correct`, `b64_TwoSum_nonoverlap`,
  `b64_Dekker`, `b64_Dekker_safe`, `b64_Dekker_correct`,
  `b64_Dekker_nonoverlap` as `Axiom` / `Parameter` rather than
  Qed-closed theorems.

The stub is **NOT for commit** -- it's a sandbox-only artifact to let
the rest of the corpus type-check without the real Pff layer.  Files
built against the stub correctly show the stubbed axioms in their
`Print Assumptions` output, which is how the engagement verified that
the production-side audit footprint is the same as the sandbox's
modulo those stub axioms.

### Sandbox build commands

```bash
# Initial setup
mkdir -p /tmp/proof_test/theories-flocq
cp _CoqProject.full /tmp/proof_test/_CoqProject

# Translate sources (run each time you sync from the production tree)
for f in theories-flocq/*.v; do
  sed 's/Stdlib/Coq/g' "$f" > /tmp/proof_test/theories-flocq/$(basename "$f")
done

# (Manually create the stub B64_Pff_bridge.v -- see the file's header
#  in the corpus for the exact axioms it declares.)

# Build
cd /tmp/proof_test
coq_makefile -f _CoqProject -o Makefile.test
make -f Makefile.test
```

The sandbox cannot validate the production-side `Print Assumptions`
footprint exactly (it has extra stub axioms), but it CAN validate
that proof scripts pass the kernel.  This is the right tradeoff for
fast iteration: don't ship the stub, but use it locally for the
red-green-refactor cycle.

## CI scripts

Three guardrail scripts run after the build:

### `scripts/check_admitted.sh`

Enforces the three-tier Admitted system:

- **Tier 1**: Admitted without registry entry → build failure.
- **Tier 2**: Admitted listed in `docs/admitted-counterexamples.txt`
  (with verified counterexample in the same file) → ALLOWED.  Means
  "the theorem as stated is unprovable; here's the witness."
- **Tier 3**: Admitted listed in `docs/admitted-deferred-proofs.txt`
  (with proof structure doc referenced) → ALLOWED.  Means "the theorem
  IS provable; the proof structure is documented; the work is
  multi-session and hasn't been completed yet."

`Axiom`, `Parameter`, and the `admit.` tactic are NEVER allowed.

Exit codes: 0 (all registered), 1 (unregistered Admitted found or
banned keyword present), 2 (file-access error).

### `scripts/audit_axioms.sh`

Per-theorem `Print Assumptions` audit.  Reads a sequential build log
(`make -j1` required), identifies every `Print Assumptions` output
block, and verifies that the axioms named in each block are a subset
of `docs/axiom-allowlist.txt`.

Files listed in `docs/audit-exceptions.txt` are exempt (their
contamination is the known, transitional state being cleared
file-by-file by the parametric-architecture refactor).  Each exception
entry requires a justification comment immediately above the file
line.

Exit codes: 0 (no violations), 1 (disallowed axioms in non-exempted
file), 2 (file-access error).

### `scripts/check_readme_axioms.sh`

Verifies the README's prose claim about "the three standard axioms"
matches `docs/axiom-allowlist.txt` verbatim.  Catches silent drift
between human-maintained README text and the machine-checked
allowlist.

## Project structure

```
NetTopologySuite.Proofs/
├── _CoqProject          # Minimal: theories/ only (no Flocq)
├── _CoqProject.full     # Full: theories/ + theories-flocq/
├── Dockerfile           # Pinned toolchain (Rocq 9.1.1 + Flocq 4.2.2)
├── .github/workflows/ci.yml  # Two-job CI: host runner + container
├── README.md            # Project intro + axiom allowlist claim
├── scripts/
│   ├── check_admitted.sh        # Three-tier Admitted registry
│   ├── audit_axioms.sh          # Per-theorem Print Assumptions audit
│   └── check_readme_axioms.sh   # README/allowlist consistency
├── docs/
│   ├── axiom-allowlist.txt              # Allowed axioms (machine-checked)
│   ├── audit-exceptions.txt             # Files exempt from allowlist
│   ├── admitted-counterexamples.txt     # Tier 2 registry
│   ├── admitted-deferred-proofs.txt     # Tier 3 registry
│   └── (design docs, proof structure docs, retros)
├── theories/            # Pure-Coq theorems (no Flocq)
└── theories-flocq/      # Flocq-dependent theorems
```

## Reproducibility checklist

A fresh clone passes the full CI checks iff:

- [ ] `coq_makefile -f _CoqProject -o Makefile && make` succeeds on
      a host with Rocq 9.1.1 installed (covers `theories/`).
- [ ] `docker build -t img . && docker run img` exits 0 (covers
      `theories-flocq/`).
- [ ] `bash scripts/check_admitted.sh` exits 0 and reports
      `All Admitted theorems registered (N total: X counterexample,
      Y deferred-proof)`.
- [ ] `bash scripts/check_readme_axioms.sh` exits 0.
- [ ] `bash scripts/audit_axioms.sh build.log` (where `build.log` is
      the sequential build's stdout) exits 0.

If any of the above fails on a fresh clone of `main`, that's a
reproducibility bug to fix.

## Known gotchas

- **Don't commit the sandbox stub `B64_Pff_bridge.v`** -- it has
  `Axiom` declarations that would fail
  `scripts/check_admitted.sh`.  The production file (built by CI's
  container) has the real Qed-closed bodies.
- **Don't commit `_CoqProject` modifications** that add the sandbox's
  test files (`B64_Piece5b_Attempt.v`, etc.).  Those are scratch
  files for the interactive workflow.
- **`make -j1` is required for `scripts/audit_axioms.sh`**.  Parallel
  builds interleave the `Print Assumptions` output, breaking the
  per-theorem block parsing.  Production CI uses `-j2` for the build
  itself (audit runs separately).
- **Network policy can block opam**.  The corpus's local sandbox path
  installs Coq + Flocq via apt to avoid this; if you reproduce on a
  network-restricted host without apt support for these packages,
  the production Docker path is the only option.
