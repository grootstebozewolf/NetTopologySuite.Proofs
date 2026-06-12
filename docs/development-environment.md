# Development environment

**New here?** See your role card in [`docs/HELP.md`](HELP.md) or the full [`docs/READING-GUIDE.md`](READING-GUIDE.md). Newbie Nate (and CI / Quality Gatekeeper) paths explicitly need this document.

The canonical build path is the **container** described in the
[Dockerfile](../Dockerfile): Rocq 9.1.1 + Flocq 4.2.2 baked into an
image based on `rocq/rocq-prover:9.1.1-ocaml-4.14.2-flambda`.  CI uses
this image; macOS and Linux developers run it via `podman`/`docker`
locally.

This document captures a **host-install fallback** for environments
where the container build is blocked.  The fallback matches the
container's package versions exactly, so binaries produced by it are
interchangeable with binaries produced by CI.

## When the fallback is needed

The Dockerfile installs two things on top of the upstream rocq image:

1. `apt-get install` of `make git curl vim ca-certificates` from
   Debian repositories (`deb.debian.org`).
2. `opam install coq-flocq.4.2.2` from the `coq-released` opam
   repository (`coq.inria.fr/opam/released`).

Both of these can fail in restricted-network environments:

  - **Debian repos return `403 Forbidden`** for the host
    `deb.debian.org` if the network policy whitelists only a subset of
    distro mirrors (e.g. Ubuntu mirrors but not Debian).
  - **`coq.inria.fr/opam/released` returns `curl exit 60`** if the
    network policy whitelists the default opam repo
    (`opam.ocaml.org`) but not Inria's separately-hosted Coq
    repository.

In both cases the symptom is the Dockerfile failing at step `[2/5]`
(apt) or `[3/5]` (opam install).  The base
`rocq/rocq-prover:9.1.1-ocaml-4.14.2-flambda` image itself remains
pullable, but the Flocq install on top of it cannot complete.

## Host-install fallback

Tested on Ubuntu 24.04 with no Docker access required.  Total time
~5 minutes; the long-pole step is the Flocq build (~2 minutes on a
4-core machine).

### Step 1 — install opam and base OCaml (from Ubuntu apt)

```sh
sudo apt-get update
sudo apt-get install -y opam
```

This pulls `opam 2.1.5-1` + `ocaml 4.14.1` from the standard Ubuntu
repositories.  Ubuntu's `archive.ubuntu.com` is typically reachable
even when `deb.debian.org` is not, because they are separate
top-level distros with separate ACL entries in most policies.

### Step 2 — initialise opam and create the switch

```sh
opam init --bare --no-setup --disable-sandboxing -y
opam switch create nts-flocq ocaml-system.4.14.1 -y
eval $(opam env --switch=nts-flocq)
```

`--disable-sandboxing` is required when running as root (sandboxing
uses `bwrap`, which itself requires unprivileged user namespaces);
omit it for normal-user installs.

The `ocaml-system.4.14.1` package wraps the apt-installed OCaml
compiler, avoiding a full opam-driven OCaml rebuild.

### Step 3 — install Rocq from the default opam repo

```sh
opam install --confirm-level=unsafe-yes rocq-core.9.1.1 rocq-stdlib.9.0.0
```

The default opam repository at `opam.ocaml.org` carries both
packages.  The version pair (`rocq-core.9.1.1` +
`rocq-stdlib.9.0.0`) matches the upstream
`rocq/rocq-prover:9.1.1-ocaml-4.14.2-flambda` image's installed
package list exactly.

> **Why not `rocq-prover.9.1.1`?**  The default opam repo's
> `rocq-prover` package only goes up to `9.0.0` (it is a thin
> metapackage that pulls in `rocq-core` + `rocq-stdlib`; the version
> tracking is independent).  Installing `rocq-core.9.1.1` directly
> bypasses the metapackage and gives the same end result.

### Step 4 — build Flocq from gitlab source

The `coq-released` opam repo (which would normally ship
`coq-flocq.4.2.2`) is at `coq.inria.fr` and is the typical
blocked-host.  But Flocq's source is hosted on Inria's GitLab
(`gitlab.inria.fr/flocq/flocq`), which is a separate top-level
domain reachable through most policies.

```sh
cd /tmp
git clone --depth 1 --branch flocq-4.2.2 https://gitlab.inria.fr/flocq/flocq.git
cd flocq

# Generate configure (the tarball ships with it, but the git repo
# does not -- autoconf is in build-essential).
autoconf

# Configure against the opam-installed rocq.  Rocq 9.1.1 ships
# `rocq` as the binary; Flocq's build expects `coqc`/`coqdep`, so
# we pass the rocq subcommand spellings explicitly.
COQC="rocq c" COQDEP="rocq dep" ./configure

# Build and install.  remake is Flocq's bespoke build driver; it
# accepts standard --jobs= for parallelism.
./remake --jobs=4
./remake install
```

After this, `rocq -where` reports the opam switch's lib dir, and
`<rocq -where>/user-contrib/Flocq/` contains the compiled Flocq
library.  Any `From Flocq Require ...` import in the corpus
resolves through this path.

### Step 5 — build the corpus

```sh
cd /path/to/NetTopologySuite.Proofs
eval $(opam env --switch=nts-flocq)
rocq makefile -f _CoqProject.full -o Makefile.gen
make -f Makefile.gen -j4
```

A successful build ends with `theories-flocq/*.vo` files and the
usual `Print Assumptions` output.

### Step 6 — run the CI gauntlet

```sh
# 1. Three-tier Admitted check.
bash scripts/check_admitted.sh

# 2. Per-theorem axiom audit on an output-synced build log.
make -f Makefile.gen clean
make -f Makefile.gen -j"$(nproc)" --output-sync=target > /tmp/build.log 2>&1
bash scripts/audit_axioms.sh /tmp/build.log

# 3. README <-> allowlist consistency.
bash scripts/check_readme_axioms.sh

# 4. Qed-invariant grep (also run by CI; here just for completeness).
grep -nE "Axiom|Parameter|admit\." theories/ theories-flocq/ \
  --include="*.v" | grep -v ":\(\*"
```

All four should report success.  `audit_axioms.sh` needs each
`ROCQ compile <file>` line contiguous with that file's
`Print Assumptions` blocks; GNU make's `--output-sync=target`
(make >= 4.0) guarantees this for parallel builds by emitting each
target's output atomically.  On a make without `--output-sync`
(e.g. Apple's bundled make 3.81), fall back to a `-j1` build.

## Remote agent containers (Claude Code on the web and similar)

Session-verified on an Ubuntu 24.04.4 LTS remote execution container
(2026-06-11, the `extract_faces` slice-3g session).  Two extra failure
modes appear before the fallback above even starts, plus one shortcut
worth knowing:

1. **The Docker CLI is present but there is no daemon.**  `docker pull`
   fails with `dial unix /var/run/docker.sock: connect: no such file or
   directory`.  Do not chase the daemon -- go straight to the
   host-install fallback.

2. **Pre-existing PPA source lists break `apt-get update` outright.**
   The base image ships third-party PPAs (`deadsnakes`, `ondrej/php`)
   that the network policy 403s, and apt treats the dead repos as fatal
   (exit 100) *before* Step 1's `apt-get install opam` can run, even
   though `archive.ubuntu.com` itself is reachable.  Remove the stale
   lists first:

   ```sh
   rm -f /etc/apt/sources.list.d/*deadsnakes* /etc/apt/sources.list.d/*ondrej*
   apt-get update
   ```

   Then Steps 1-3 proceed as written.  Running as root, remember
   `--disable-sandboxing` on `opam init` (Step 2's note).  The
   unpinned `opam switch create nts-flocq ocaml-system` resolves to
   `ocaml-system.4.14.1` on 24.04, matching the doc's pin.

3. **Skip Flocq (Step 4) for `theories/`-only work.**  The host
   (Stdlib-only) layer has no Flocq imports, and a `Makefile.gen`
   generated from `_CoqProject.full` will happily build a single
   target plus its dependency chain:

   ```sh
   rocq makefile -f _CoqProject.full -o Makefile.gen
   make -f Makefile.gen -j"$(nproc)" theories/<YourFile>.vo
   ```

   For a new file whose imports stay inside `theories/`, this never
   touches `theories-flocq/`, so Steps 1-3 alone (a few minutes of
   wall time, the long pole being the `rocq-core`/`rocq-stdlib`
   build) give a working verify loop.  A per-theorem axiom check
   without a full audit-grade build log is a scratch file of
   `Print Assumptions` lines compiled with
   `rocq c -Q theories NTS.Proofs /tmp/check_axioms.v`.

## What this fallback does NOT change

  - **CI is unaffected.**  GitHub Actions runs the container path on
    the `Build theories-flocq in pinned container` job; the host
    fallback is for local development only.
  - **The Dockerfile remains canonical.**  When network access
    permits, `podman build` / `docker build` followed by `podman run
    --rm nts-proofs` is the simpler path.
  - **Package versions are pinned to the same values.**  `rocq-core
    9.1.1`, `rocq-stdlib 9.0.0`, `coq-flocq 4.2.2`.  Source-built
    Flocq from the `flocq-4.2.2` git tag produces byte-identical
    `.vo` files to the opam-installed one.

## Network policy reference

Hosts known to be reachable in the typical restricted environment:

  - `github.com`, `raw.githubusercontent.com` (300/200)
  - `archive.ubuntu.com`, `us.archive.ubuntu.com` (200)
  - `opam.ocaml.org` (200)
  - `gitlab.inria.fr` (302 -> 200)

Hosts known to be blocked:

  - `deb.debian.org`, `security.debian.org` (403, `host_not_allowed`)
  - `coq.inria.fr` (403 / `curl exit 60`)
  - `ppa.launchpadcontent.net` (variable, typically 403 on
    non-allowlisted PPAs; if the image ships stale PPA source lists
    this 403 makes `apt-get update` itself fail -- see the
    remote-agent-container section above)

The fallback above uses only the reachable hosts and pinned source
versions.
