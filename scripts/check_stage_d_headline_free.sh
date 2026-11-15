#!/usr/bin/env bash
# =============================================================================
# scripts/check_stage_d_headline_free.sh
# -----------------------------------------------------------------------------
# Mechanical check that the carry_clean Stage D chain does not use the REFUTED
# `fast_expansion_sum_strong_nonoverlap_headline`, directly or transitively.
#
# `Print Assumptions` cannot show this: the headline is a Definition taken as
# a hypothesis, not an Axiom.  So this script compiles the chain in a scratch
# copy of theories-flocq/ from which the headline Definition and EVERY theorem
# that takes it have been deleted:
#
#   Orient_b64_expansion.v   fast_expansion_sum_strong_nonoverlap_headline,
#                            b64_orient2d_expansion_nonoverlap,
#                            b64_orient2d_expansion_sign_correct
#   Orient_b64_stage_d.v     b64_orient_sign_exact_sound,
#                            b64_orient_sign_stage_d_sound
#   Shewchuk_vs_Z2.v         shewchuk_stage_d_agrees_with_exact_intdet,
#                            shewchuk_vs_z2_tiny_headline
#
# and then recompiles, in dependency order, those three files plus
# Orient_b64_expansion_cc.v, Orient_b64_stage_d_cc.v and Orient_b64_grid_cc.v.  If any rebuilt
# theorem reached the headline, its file would fail to compile here.  The
# script also fails if the stripped copies still mention the headline
# outside comments, or if a removed name is missing (the strip went stale).
#
# Needs the flocq corpus built (make full / the CI rocq-flocq compile).
#
# Exit codes:  0 headline-free;  1 a check failed;  2 toolchain / usage.
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
  echo "[headline-free] no 'rocq' on PATH (need the flocq toolchain)" >&2
  exit 2
fi
for vo in theories-flocq/Orient_b64_stage_d_cc.vo theories-flocq/Shewchuk_vs_Z2.vo; do
  if [ ! -f "$vo" ]; then
    echo "[headline-free] missing $vo -- build the flocq corpus first" >&2
    exit 2
  fi
done

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cp -r theories-flocq "$WORK/theories-flocq"
FQ="$WORK/theories-flocq"

# strip FILE NAME...: delete each `Theorem|Definition NAME` block (through its
# terminating `Qed.` for a theorem, or the first line ending in `.` for a
# Definition) and each `Print Assumptions NAME.` line.
strip() {
  local file="$1"; shift
  local name
  for name in "$@"; do
    if ! grep -qE "^(Theorem|Lemma|Definition) ${name}( |$|:)" "$file"; then
      echo "[headline-free] FAIL: ${name} not found in ${file#"$WORK"/} (stale strip list)" >&2
      exit 1
    fi
    awk -v n="$name" '
      BEGIN { skip = 0 }
      skip == 0 && ($0 ~ "^(Theorem|Lemma) " n "( |$|:)") { skip = 1; next }
      skip == 0 && ($0 ~ "^Definition " n "( |$|:)") { skip = 2; if ($0 ~ /\.[ \t]*$/) skip = 0; next }
      skip == 1 { if ($0 ~ /^(Qed|Defined)\./) skip = 0; next }
      skip == 2 { if ($0 ~ /\.[ \t]*$/) skip = 0; next }
      $0 ~ "^Print Assumptions " n "\\." { next }
      { print }
    ' "$file" > "$file.tmp" && mv "$file.tmp" "$file"
  done
}

strip "$FQ/Orient_b64_expansion.v" \
  fast_expansion_sum_strong_nonoverlap_headline \
  b64_orient2d_expansion_nonoverlap \
  b64_orient2d_expansion_sign_correct
strip "$FQ/Orient_b64_stage_d.v" \
  b64_orient_sign_exact_sound \
  b64_orient_sign_stage_d_sound
strip "$FQ/Shewchuk_vs_Z2.v" \
  shewchuk_stage_d_agrees_with_exact_intdet \
  shewchuk_vs_z2_tiny_headline

# No live (non-comment) mention may remain in the rebuilt chain.
STATUS=0
for f in Orient_b64_expansion.v Orient_b64_stage_d.v Orient_b64_expansion_cc.v \
         Orient_b64_stage_d_cc.v Orient_b64_grid_cc.v Shewchuk_vs_Z2.v \
         B64_CarryCleanSign.v B64_NonoverlapSign.v; do
  # drop (* ... *) comments (single- and multi-line), then search
  if perl -0777 -pe 's/\(\*.*?\*\)//gs' "$FQ/$f" \
       | grep -q "fast_expansion_sum_strong_nonoverlap_headline"; then
    echo "[headline-free] FAIL: $f still mentions the headline outside comments" >&2
    STATUS=1
  fi
done
[ "$STATUS" -eq 0 ] || exit 1

for f in Orient_b64_expansion.v Orient_b64_stage_d.v Orient_b64_expansion_cc.v \
         Orient_b64_stage_d_cc.v Orient_b64_grid_cc.v Shewchuk_vs_Z2.v; do
  echo "[headline-free] compile $f (headline and its consumers removed)"
  if ! (cd "$WORK" && rocq c -Q "$REPO_ROOT/theories" NTS.Proofs -Q theories-flocq NTS.Proofs.Flocq \
          "theories-flocq/$f" > "$WORK/$f.log" 2>&1); then
    echo "[headline-free] FAIL: $f does not compile without the headline" >&2
    grep -nE 'Error' -A6 "$WORK/$f.log" | head -30 >&2
    exit 1
  fi
done

echo "[headline-free] OK: carry_clean Stage D chain compiles with the refuted headline and its consumers deleted."
exit 0
