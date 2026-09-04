#!/usr/bin/env bash
# =============================================================================
# scripts/hunt_probe_smoke.sh
# -----------------------------------------------------------------------------
# Compile Qed-claiming hunt probes under docs/h1-vacuity/ that are NOT in
# _CoqProject / _CoqProject.full (evidence, not product headlines).
#
# Flocq-lane probes need HobbyCounterexample_b64.vo (and its closure)
# already built — after `make full` or the CI flocq corpus compile.
#
# Usage:
#   scripts/hunt_probe_smoke.sh
#
# Exit codes:
#   0  -- every listed probe compiled (theorems end Qed; Print Assumptions emitted).
#   1  -- a probe failed to compile.
#   2  -- toolchain / usage error.
# =============================================================================

set -u

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

if ! command -v rocq >/dev/null 2>&1; then
  if command -v opam >/dev/null 2>&1; then
    eval "$(opam env --switch=nts-flocq 2>/dev/null)" || true
  fi
fi
if ! command -v rocq >/dev/null 2>&1; then
  echo "[hunt-probes] no 'rocq' on PATH (need the flocq toolchain)" >&2
  exit 2
fi

if [ ! -f theories-flocq/HobbyCounterexample_b64.vo ]; then
  echo "[hunt-probes] missing theories-flocq/HobbyCounterexample_b64.vo" >&2
  echo "  build the flocq corpus first (make full / CI rocq-flocq job)." >&2
  exit 2
fi

# Flocq-lane hunt probes (host-lane VacuityCheck / WitnessCheck stay
# `rocq c -Q theories NTS.Proofs` only; they do not need this script).
PROBES=(
  docs/h1-vacuity/HobbyHlemma43Check.v
)

fail=0
for probe in "${PROBES[@]}"; do
  echo "[hunt-probes] rocq c $probe"
  # Marker so scripts/audit_axioms.sh attributes the following PA blocks.
  echo "ROCQ compile $probe"
  if ! rocq c -Q theories NTS.Proofs -Q theories-flocq NTS.Proofs.Flocq "$probe"
  then
    echo "[hunt-probes] FAIL: $probe" >&2
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then
  echo "[hunt-probes] one or more probes failed to compile." >&2
  exit 1
fi
echo "[hunt-probes] OK: ${#PROBES[@]} probe(s) compiled."
exit 0
