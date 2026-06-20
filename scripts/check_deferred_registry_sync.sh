#!/usr/bin/env bash
# =============================================================================
# scripts/check_deferred_registry_sync.sh
# -----------------------------------------------------------------------------
# Doc <-> registry consistency guard for the Admitted registries.
#
# When a theorem is added to the deferred-proof queue
# (`docs/admitted-deferred-proofs.txt`) — or the counterexample registry —
# the source-of-record prose tends to drift: e.g. TRIAGE_NTS_JTS_ISSUES.md
# kept asserting the "deferred-proof registry is EMPTY (0)" long after three
# `ArcPointDistance.v` residuals were registered.  This guard makes that
# class of drift a CI failure instead of a manual nit.
#
# It checks, against the LIVE counts parsed from the two registries (same
# logic as scripts/check_admitted.sh):
#
#   (a) Emptiness claims.  If the deferred registry is non-empty, no tracked
#       doc may assert it is "EMPTY (0)" / "0 entries" / "registry is empty"
#       as a current fact.
#   (b) Explicit zero-counts.  No tracked line may state "0 deferred[-proof]"
#       or "0 counterexample" while that registry is non-empty.
#
# It deliberately does NOT police arbitrary "<N> counterexample" numbers:
# "Tier-2 counterexample" and friends are labels, not counts.  The high-signal
# failure mode is the stale *emptiness* claim, which is what this guards.
#
# Intentionally-historical mentions (e.g. "the registry was EMPTY at that
# date") are exempt: put the sentinel  <!-- registry-sync:ok -->  on the line.
#
# Exit codes:
#   0  -- docs agree with the registries.
#   1  -- a stale emptiness claim or a wrong count was found.
#   2  -- usage / file-access error.
# =============================================================================

set -u

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
COUNTEREXAMPLE_REGISTRY="$REPO_ROOT/docs/admitted-counterexamples.txt"
DEFERRED_REGISTRY="$REPO_ROOT/docs/admitted-deferred-proofs.txt"

# Source-of-record docs that make claims about the registries.  Extend as
# needed; keep to high-traffic prose where the claims actually live.
TRACKED_DOCS=(
  "README.md"
  "CONTRIBUTING.md"
  "TRIAGE_NTS_JTS_ISSUES.md"
)

SENTINEL="registry-sync:ok"

for f in "$COUNTEREXAMPLE_REGISTRY" "$DEFERRED_REGISTRY"; do
  if [ ! -r "$f" ]; then
    echo "[registry-sync] cannot read $f" >&2
    exit 2
  fi
done

cd "$REPO_ROOT" || exit 2

# Live counts: strip comments + blanks, keep entries with a non-empty first
# '|' field (matches check_admitted.sh's parser).
count_registry() {
  sed -e 's/#.*//' -e '/^[[:space:]]*$/d' "$1" \
    | perl -F'\|' -lane 'my $k=$F[0]; $k=~s/^\s+|\s+$//g; print $k if length $k' \
    | wc -l | tr -d ' '
}

DEF_COUNT="$(count_registry "$DEFERRED_REGISTRY")"
CEX_COUNT="$(count_registry "$COUNTEREXAMPLE_REGISTRY")"

violations=0

for doc in "${TRACKED_DOCS[@]}"; do
  [ -r "$doc" ] || continue

  # (a) Stale emptiness claims — only meaningful when the registry is non-empty.
  # grep -n keeps ORIGINAL line numbers; the sentinel filter drops whole records.
  if [ "$DEF_COUNT" -gt 0 ]; then
    while IFS= read -r hit; do
      [ -z "$hit" ] && continue
      echo "::error::$doc:${hit%%:*} -- claims the deferred-proof registry is empty," \
           "but it has $DEF_COUNT entr$([ "$DEF_COUNT" -eq 1 ] && echo y || echo ies)."
      echo "    line: $(echo "$hit" | cut -d: -f2-)"
      echo "    fix the wording, or mark a historical mention with <!-- $SENTINEL -->"
      violations=$((violations + 1))
    done < <(
      grep -inE 'EMPTY \(0\)|0 entries|registry is (now )?empty|empty deferred-proof registry' "$doc" \
        | grep -ivE 'not[* _]*empty' \
        | grep -vF "$SENTINEL"
    )
  fi

  # (b) Explicit "0 deferred" / "0 counterexample" claims vs the live counts.
  while IFS= read -r hit; do
    [ -z "$hit" ] && continue
    ln="${hit%%:*}"; text="${hit#*:}"
    if echo "$text" | grep -qiE '\b0[[:space:]]+deferred' && [ "$DEF_COUNT" -gt 0 ]; then
      echo "::error::$doc:$ln -- states \"0 deferred...\" but the registry has $DEF_COUNT."
      echo "    fix the count, or mark a historical mention with <!-- $SENTINEL -->"
      violations=$((violations + 1))
    fi
    if echo "$text" | grep -qiE '\b0[[:space:]]+counterexample' && [ "$CEX_COUNT" -gt 0 ]; then
      echo "::error::$doc:$ln -- states \"0 counterexample...\" but the registry has $CEX_COUNT."
      echo "    fix the count, or mark a historical mention with <!-- $SENTINEL -->"
      violations=$((violations + 1))
    fi
  done < <(
    grep -inE '\b0[[:space:]]+(deferred|counterexample)' "$doc" \
      | grep -vF "$SENTINEL"
  )
done

if [ "$violations" -gt 0 ]; then
  echo ""
  echo "[registry-sync] FAIL: $violations doc/registry mismatch(es)."
  echo "  Live registries: $DEF_COUNT deferred-proof, $CEX_COUNT counterexample"
  echo "  (docs/admitted-deferred-proofs.txt, docs/admitted-counterexamples.txt)."
  exit 1
fi

echo "[registry-sync] OK: tracked docs agree with the registries" \
     "($DEF_COUNT deferred-proof, $CEX_COUNT counterexample)."
exit 0
