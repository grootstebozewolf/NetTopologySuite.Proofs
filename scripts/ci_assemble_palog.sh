#!/usr/bin/env bash
# =============================================================================
# scripts/ci_assemble_palog.sh
# -----------------------------------------------------------------------------
# Assemble the per-file Print Assumptions chunks (.palog/<file>.log) into
# one audit input on stdout, in project order.
#
# HARD COVERAGE GUARANTEE (this is what keeps guardrail 4 sound under
# incremental builds): every .v listed in _CoqProject.full MUST have a
# chunk.  A missing chunk means the axiom audit would silently lose
# coverage for that file, so this script fails the build instead.  The
# audit itself (scripts/audit_axioms.sh) is order-independent across
# files -- it only needs each file's chunk to be internally contiguous,
# which scripts/ci_update_palog.sh guarantees by construction.
#
# Usage:
#   scripts/ci_assemble_palog.sh > audit_input.log
#
# Exit codes: 0 on success, 1 on missing chunk(s), 2 on usage/IO error.
# =============================================================================

set -uo pipefail

PROJECT="_CoqProject.full"
PALOG_DIR=".palog"

if [ ! -r "$PROJECT" ]; then
  echo "[assemble-palog] cannot read $PROJECT" >&2
  exit 2
fi

missing=0
total=0
while IFS= read -r vfile; do
  total=$((total + 1))
  chunk="$PALOG_DIR/$vfile.log"
  if [ -r "$chunk" ]; then
    cat "$chunk"
  else
    echo "[assemble-palog] MISSING chunk for $vfile" >&2
    missing=$((missing + 1))
  fi
done < <(sed -e 's/#.*//' -e 's/[[:space:]]*$//' -e '/\.v$/!d' "$PROJECT")

if [ "$missing" -gt 0 ]; then
  echo "[assemble-palog] FAIL: $missing of $total project file(s) have no" >&2
  echo "  Print Assumptions chunk -- the axiom audit would lose coverage." >&2
  echo "  This should be impossible after a successful build (a cold cache" >&2
  echo "  builds everything).  If the cache is corrupted, re-run from a" >&2
  echo "  clean cache (push to main rebuilds from clean and re-seeds it)." >&2
  exit 1
fi

echo "[assemble-palog] assembled $total chunk(s), full corpus coverage." >&2
