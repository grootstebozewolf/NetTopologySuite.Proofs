#!/usr/bin/env bash
# =============================================================================
# scripts/check_readme_axioms.sh
# -----------------------------------------------------------------------------
# README <-> allowlist consistency check.  Extracts the axiom names from
# the fenced code block immediately following the README sentence
# "The only axioms used are the three standard ones bundled" (lines 18-29
# at the time of writing) and compares them against
# `docs/axiom-allowlist.txt`.  Fails if the two diverge.
#
# Catches: silent drift of the README's documented axiom claim away from
# the enforced allowlist that CI's audit step honours.
#
# Exit codes:
#   0  -- README's axiom list matches the allowlist exactly.
#   1  -- mismatch.
#   2  -- usage / file-access error.
# =============================================================================

set -u

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
README="$REPO_ROOT/README.md"
ALLOWLIST="$REPO_ROOT/docs/axiom-allowlist.txt"

for f in "$README" "$ALLOWLIST"; do
  if [ ! -r "$f" ]; then
    echo "[readme-axioms] cannot read $f" >&2
    exit 2
  fi
done

TMPDIR_CHECK="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_CHECK"' EXIT

# Allowlist, normalised: strip comments / blank lines / whitespace, sorted.
sed -e 's/#.*//' -e 's/[[:space:]]//g' -e '/^$/d' "$ALLOWLIST" \
  | sort > "$TMPDIR_CHECK/allowlist.normalised"

# README, extract the fenced code block that follows the marker sentence.
# Marker: the line containing 'The only axioms used are'.  We scan
# forward to the next ``` fence, capture lines until the next ``` fence.
awk '
  /The only axioms used are/             { found_marker=1; next }
  found_marker && /^```/ && !in_block    { in_block=1; next }
  found_marker && /^```/ &&  in_block    { exit }
  found_marker && in_block                { print }
' "$README" \
  | sed -e 's/#.*//' -e 's/[[:space:]]//g' -e '/^$/d' \
  | sort > "$TMPDIR_CHECK/readme.normalised"

if [ ! -s "$TMPDIR_CHECK/readme.normalised" ]; then
  echo "[readme-axioms] FAIL: could not extract any axiom names from README.md."
  echo "    Expected a fenced code block immediately after the sentence"
  echo "    'The only axioms used are ...' listing one axiom per line."
  exit 1
fi

if diff -u "$TMPDIR_CHECK/readme.normalised" "$TMPDIR_CHECK/allowlist.normalised" > /tmp/readme_axiom_diff 2>&1; then
  echo "[readme-axioms] OK: README and docs/axiom-allowlist.txt agree."
  exit 0
fi

echo "[readme-axioms] FAIL: README's axiom list does not match docs/axiom-allowlist.txt."
echo ""
echo "Diff (README on the left, allowlist on the right):"
cat /tmp/readme_axiom_diff
exit 1
