#!/usr/bin/env bash
# =============================================================================
# scripts/jct-build.sh
# -----------------------------------------------------------------------------
# Convenience: build a single .vo target (and its dependencies) from
# _CoqProject.full, filtering the cosmetic Flocq "is required" loadpath
# warnings that the full project's makefile emits for modules outside the
# requested subtree.  Requires `rocq` (Rocq 9.1.x) on PATH.
#
# Usage:
#   scripts/jct-build.sh theories/JCT.vo
#   scripts/jct-build.sh                 # defaults to theories/JCT.vo
# =============================================================================
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"
TARGET="${1:-theories/JCT.vo}"
rocq makefile -f _CoqProject.full -o Makefile.gen >/dev/null 2>&1
make -f Makefile.gen "$TARGET" -j4 2>&1 \
  | grep -vE "is required|module-not-found|has not been found|from root Stdlib"
