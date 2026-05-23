#!/usr/bin/env bash
# =============================================================================
# scripts/check_admitted.sh
# -----------------------------------------------------------------------------
# Two-tier verification of Admitted theorems:
#   - Tier 1 (standard): Admitted without registry entry -> BUILD FAILURE.
#   - Tier 2 (counterexample): Admitted with registry entry referencing
#     a verified counterexample -> ALLOWED, tracked.
#
# Registry: docs/admitted-counterexamples.txt
#   Format: file:theorem_name | counterexample_doc | section_refs
#
# `Axiom`, `Parameter`, and the `admit.` tactic are NEVER allowed --
# the registry covers Admitted theorems only.
#
# Exit codes:
#   0 -- every Admitted is registered (corpus invariant holds).
#   1 -- one or more Admitteds lack registry entries (or
#        Axiom/Parameter/admit. found).
#   2 -- usage / file-access error.
# =============================================================================

set -u

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REGISTRY="$REPO_ROOT/docs/admitted-counterexamples.txt"

if [ ! -r "$REGISTRY" ]; then
  echo "[check_admitted] cannot read $REGISTRY" >&2
  exit 2
fi

cd "$REPO_ROOT" || exit 2

# Build the set of registered "file:theorem_name" keys from the registry.
# Strip comments + blanks, take the first '|' field, trim whitespace.
REGISTERED=$(sed -e 's/#.*//' -e '/^[[:space:]]*$/d' "$REGISTRY" \
  | awk -F'|' '{ gsub(/^[[:space:]]+|[[:space:]]+$/, "", $1); if ($1) print $1 }')

# Hard fail on Axiom / Parameter / admit. (these are never allowed).
if grep -nE '^[[:space:]]*Axiom\b|^[[:space:]]*Parameter\b|\badmit\.' \
     theories/*.v theories-flocq/*.v 2>/dev/null; then
  echo "::error::Found Axiom/Parameter/admit. -- these are never allowed."
  echo "Use Admitted with a registry entry in docs/admitted-counterexamples.txt."
  exit 1
fi

# Find every Admitted in the corpus.  For each, extract the enclosing
# theorem name via a backward scan to the nearest Theorem/Lemma.
violations=0
while IFS= read -r line; do
  [ -z "$line" ] && continue
  file=$(echo "$line" | cut -d: -f1)
  lineno=$(echo "$line" | cut -d: -f2)
  thm=$(awk -v L="$lineno" '
    /^(Theorem|Lemma)[[:space:]]+/ {
      name = $2
      gsub(/[^a-zA-Z0-9_'\''].*/, "", name)
    }
    NR == L { print name; exit }
  ' "$file")
  if [ -z "$thm" ]; then
    echo "::error::$file:$lineno -- Admitted without enclosing Theorem/Lemma." >&2
    violations=$((violations + 1))
    continue
  fi
  key="$file:$thm"
  if ! echo "$REGISTERED" | grep -qxF "$key"; then
    echo "::error::$file:$lineno ($thm) -- not in counterexample registry." >&2
    violations=$((violations + 1))
  fi
done < <(grep -rnE '^[[:space:]]*Admitted[[:space:]]*\.' \
           theories/ theories-flocq/ --include='*.v' 2>/dev/null)

if [ "$violations" -gt 0 ]; then
  echo ""
  echo "Found $violations unregistered Admitted theorem(s)."
  echo "Each Admitted must appear in docs/admitted-counterexamples.txt"
  echo "with a reference to a verified counterexample.  Either add the"
  echo "entry (with section references) or close the proof."
  exit 1
fi

count=$(echo "$REGISTERED" | grep -c .)
echo "All Admitted theorems documented with verified counterexamples ($count entries)."
exit 0
