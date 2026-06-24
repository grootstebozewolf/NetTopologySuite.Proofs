#!/usr/bin/env bash
# ===========================================================================
# assemble.sh -- vendor the source-of-record .v files into this package tree.
#
# Copies every path listed in MANIFEST from the NetTopologySuite.Proofs corpus
# into ./theories and ./theories-flocq, preserving the NTS.Proofs /
# NTS.Proofs.Flocq namespaces (so the proof files build unmodified).  Run this
# once before `make` / `make install`, or before producing an opam source
# tarball (`make package`).
#
# Usage:
#   ./assemble.sh [CORPUS_ROOT]
#
# CORPUS_ROOT defaults to the repo root two levels up (this package lives at
# <repo>/packaging/rocq-robust-predicates/).
# ===========================================================================
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
CORPUS="${1:-$(cd "$HERE/../.." && pwd)}"

if [ ! -f "$CORPUS/_CoqProject.full" ]; then
  echo "error: '$CORPUS' does not look like the NetTopologySuite.Proofs root" >&2
  echo "       (no _CoqProject.full found).  Pass the corpus root explicitly:" >&2
  echo "       ./assemble.sh /path/to/NetTopologySuite.Proofs" >&2
  exit 2
fi

n=0
while IFS= read -r f; do
  case "$f" in ''|\#*) continue ;; esac
  if [ ! -f "$CORPUS/$f" ]; then
    echo "error: manifest entry not found in corpus: $f" >&2
    exit 1
  fi
  mkdir -p "$HERE/$(dirname "$f")"
  cp "$CORPUS/$f" "$HERE/$f"
  n=$((n + 1))
done < "$HERE/MANIFEST"

echo "Assembled $n .v files from $CORPUS into $HERE."
echo "Next: make            (build)"
echo "      make install    (install to user-contrib)"
