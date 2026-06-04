#!/usr/bin/env bash
# =============================================================================
# scripts/buffer_axiom_smoke.sh
# -----------------------------------------------------------------------------
# Self-documenting axiom-count smoke check for the buffer/noder pipeline
# modules (theories/Buffer*.v).  For each module it `Print Assumptions` a
# headline theorem, counts the axioms in the report, and asserts the
# EXPECTED footprint:
#
#   * three axioms (the README classical-reals trio) for every buffer
#     module EXCEPT
#   * BufferJoin.v, which additionally inherits Classical_Prop.classic via
#     atan2 (registered in docs/audit-exceptions.txt) -> four axioms.
#
# This is a STANDALONE helper, deliberately separate from the CI gate
# scripts/audit_axioms.sh (which it does not touch): it documents and
# locks the buffer footprint so future buffer work is self-checking.
#
# Usage:
#   scripts/buffer_axiom_smoke.sh
#
# Requires a Rocq toolchain on PATH (or an `nts-flocq` opam switch) and the
# buffer modules' dependencies already compiled (`.vo` present) -- e.g. after
# `make -f Makefile.gen` on _CoqProject.full, or the container build.
#
# Exit codes:
#   0  -- every buffer module matches its expected axiom count.
#   1  -- one or more modules deviate (axiom leak or unexpected drop).
#   2  -- usage / toolchain / build-artefact error.
# =============================================================================

set -u

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
THEORIES="$REPO_ROOT/theories"

# Best-effort: pick up the project's opam switch if the caller has not.
if ! command -v rocq >/dev/null 2>&1; then
  if command -v opam >/dev/null 2>&1; then
    eval "$(opam env --switch=nts-flocq 2>/dev/null)" || true
  fi
fi
if ! command -v rocq >/dev/null 2>&1; then
  echo "[buffer-axioms] no 'rocq' on PATH (set up the toolchain first)" >&2
  exit 2
fi

# module | headline theorem | expected axiom count
ROWS=(
  "BufferOffset|offset_perp_dist_to_line|3"
  "BufferJoin|corner_arc_sweep_eq_turn_unit|4"
  "BufferMiter|miter_within_limit_iff|3"
  "BufferMiterAngle|miter_cap_iff_sin_half|3"
  "BufferBevel|bevel_length_sq_sin_half|3"
  "BufferEndcap|square_cap_corner_dist_sq|3"
  "BufferAssembly|assemble_closed_closed|3"
  "BufferCorrectness|buffer_correct_conditional|3"
  "RingExtract|face_walk_core|0"
  "BoundedComponent|in_bounded_component_iff|2"
  "RingSimple|ring_simple_of_subset|1"
)

# Axiom-name lines have a module-qualified name then a colon, e.g.
#   ClassicalDedekindReals.sig_not_dec : forall P : Prop, ...
# Continuation/type lines are indented and do not match this anchor.
AX_RE='^[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z0-9_]+)+[[:space:]]*:'

TMPD="$(mktemp -d)"
trap 'rm -rf "$TMPD"' EXIT

printf '%-20s %-34s %8s %8s   %s\n' "MODULE" "HEADLINE" "AXIOMS" "EXPECT" "STATUS"
printf '%s\n' "---------------------------------------------------------------------------------------"

fails=0
for row in "${ROWS[@]}"; do
  IFS='|' read -r mod thm expect <<<"$row"
  probe="$TMPD/probe_$mod.v"
  printf 'From NTS.Proofs Require Import %s.\nPrint Assumptions %s.\n' "$mod" "$thm" > "$probe"
  out="$(rocq c -q -Q "$THEORIES" NTS.Proofs "$probe" 2>&1)"
  rc=$?
  if [ $rc -ne 0 ]; then
    # Distinguish "deps not built" from a genuine error.
    if echo "$out" | grep -q "Unable to locate library"; then
      echo "[buffer-axioms] $mod: dependency .vo missing -- build the corpus first" >&2
      exit 2
    fi
    printf '%-20s %-34s %8s %8s   %s\n' "$mod" "$thm" "?" "$expect" "ERROR"
    echo "$out" | grep -iE "error" | head -3 >&2
    fails=$((fails + 1))
    continue
  fi
  count="$(printf '%s\n' "$out" | grep -cE "$AX_RE")"
  classic="no"
  echo "$out" | grep -q "Classical_Prop.classic" && classic="+classic"
  if [ "$count" -eq "$expect" ]; then
    status="OK ($classic)"
  else
    status="MISMATCH ($classic)"
    fails=$((fails + 1))
  fi
  printf '%-20s %-34s %8s %8s   %s\n' "$mod" "$thm" "$count" "$expect" "$status"
done

echo ""
if [ "$fails" -gt 0 ]; then
  echo "[buffer-axioms] FAIL: $fails module(s) deviate from the expected footprint."
  exit 1
fi
echo "[buffer-axioms] OK: all buffer modules match their expected axiom counts"
echo "                (3-axiom baseline; BufferJoin 4 via atan2, per docs/audit-exceptions.txt)."
exit 0
