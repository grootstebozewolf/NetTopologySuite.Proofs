# Container for building NetTopologySuite.Proofs under Rocq 9.1.1 + Flocq.
# Reproducible toolchain so the corpus is not pinned to a specific developer
# laptop's opam state.
#
# Two stages:
#   - `toolchain`: base image + apt tooling + Flocq.  Contains NO corpus
#     sources, so its content is fully determined by this Dockerfile.  CI
#     builds it with `--target toolchain`, publishes it to GHCR under a tag
#     derived from this file's hash, and mounts the live checkout over
#     /workspace at run time.
#   - `full` (default): toolchain + a baked copy of the repo + the
#     clean-and-build CMD.  This is the local-developer and oracle-workflow
#     path; `docker build` with no --target produces it, same as before.

FROM rocq/rocq-prover:9.1.1-ocaml-4.14.2-flambda AS toolchain

# System tooling we want for ergonomic edits inside the container.
USER root
RUN apt-get update && apt-get install -y --no-install-recommends \
        make git curl vim ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Install Flocq via opam.  4.2.0 is the most recent Flocq release at the time
# of writing; if it does not yet support Rocq 9.1.1, pin to whatever opam's
# resolver selects.
USER rocq
RUN opam update -y \
    && opam install --confirm-level=unsafe-yes coq-flocq.4.2.2

WORKDIR /workspace

FROM toolchain AS full
COPY --chown=rocq:rocq . /workspace

# Default action: clean host-leaked build artefacts, regenerate the makefile
# from `_CoqProject.full` (which includes Flocq-dependent modules when those
# are uncommented), then build the entire corpus.  The clean step is
# essential -- copying the host workspace pulls in Makefile.gen.conf with
# macOS-Homebrew paths baked in, which `rocq makefile` re-uses on regeneration
# and which then fail inside the container's Linux filesystem.
CMD ["bash", "-lc", "rm -f Makefile.gen Makefile.gen.conf .Makefile.d .Makefile.gen.d .nra.cache theories/*.vo* theories/*.glob theories/.*.aux theories-flocq/*.vo* theories-flocq/*.glob theories-flocq/.*.aux && rocq makefile -f _CoqProject.full -o Makefile.gen && make -f Makefile.gen -j\"$(nproc)\""]
