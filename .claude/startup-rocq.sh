#!/usr/bin/env bash
set -euo pipefail
eval "$(opam env --switch=nts-flocq)"
ROCQ_VERSION=$(rocq --version 2>/dev/null | head -1 || echo "NOT FOUND")
FLOCQ_VERSION=$(ocamlfind list 2>/dev/null | grep -i flocq | awk '{print $2}' || echo "NOT FOUND")
echo "Rocq:  $ROCQ_VERSION"
echo "Flocq: $FLOCQ_VERSION"
[[ "$ROCQ_VERSION" == *"9.1.1"* ]] || echo "WARNING: expected Rocq 9.1.1"
[[ "$FLOCQ_VERSION" == *"4.2.2"* ]] || echo "WARNING: expected Flocq 4.2.2"
[ ! -f Makefile.gen ] || [ _CoqProject.full -nt Makefile.gen ] && \
  rocq makefile -f _CoqProject.full -o Makefile.gen
make -f Makefile.gen -j"$(nproc)" 2>&1 | tail -10
echo "✓ Environment ready."
