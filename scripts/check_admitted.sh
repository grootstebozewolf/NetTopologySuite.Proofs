#!/usr/bin/env bash
# =============================================================================
# scripts/check_admitted.sh
# -----------------------------------------------------------------------------
# Three-tier verification of Admitted theorems (see docs/HELP.md, docs/READING-GUIDE.md,
# docs/FOR-AI-AGENTS.md, CONTRIBUTING.md for actor paths and process):
#   - Tier 1 (standard): Admitted without registry entry -> BUILD FAILURE.
#   - Tier 2 (counterexample): Admitted with entry in
#     `docs/admitted-counterexamples.txt` -> ALLOWED.  Means "the theorem
#     as currently stated CANNOT be proved; here's the verified
#     counterexample."  Permanent.
#   - Tier 3 (deferred proof): Admitted with entry in
#     `docs/admitted-deferred-proofs.txt` -> ALLOWED.  Means "the
#     theorem IS provable; the proof structure is documented; the work
#     is multi-session."  Temporary; comes off the registry when proved.
#
# Each Admitted must appear in EXACTLY ONE registry.
#
# `Axiom`, `Parameter`, and the `admit.` tactic are NEVER allowed --
# the registries cover Admitted theorems only.
#
# Exit codes:
#   0 -- every Admitted is registered (corpus invariant holds).
#   1 -- one or more Admitteds lack registry entries (or
#        Axiom/Parameter/admit. found).
#   2 -- usage / file-access error.
# =============================================================================

set -u

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
COUNTEREXAMPLE_REGISTRY="$REPO_ROOT/docs/admitted-counterexamples.txt"
DEFERRED_REGISTRY="$REPO_ROOT/docs/admitted-deferred-proofs.txt"

for f in "$COUNTEREXAMPLE_REGISTRY" "$DEFERRED_REGISTRY"; do
  if [ ! -r "$f" ]; then
    echo "[check_admitted] cannot read $f" >&2
    exit 2
  fi
done

cd "$REPO_ROOT" || exit 2

# Parser: strip comments + blanks, take the first '|' field, trim whitespace.
parse_registry() {
  sed -e 's/#.*//' -e '/^[[:space:]]*$/d' "$1" \
    | awk -F'|' '{ gsub(/^[[:space:]]+|[[:space:]]+$/, "", $1); if ($1) print $1 }'
}

COUNTEREXAMPLE_KEYS=$(parse_registry "$COUNTEREXAMPLE_REGISTRY")
DEFERRED_KEYS=$(parse_registry "$DEFERRED_REGISTRY")

# Hard fail on Axiom / Parameter / admit. (these are never allowed).
if grep -nE '^[[:space:]]*Axiom\b|^[[:space:]]*Parameter\b|\badmit\.' \
     theories/*.v theories-flocq/*.v 2>/dev/null; then
  echo "::error::Found Axiom/Parameter/admit. -- these are never allowed."
  echo "Use Admitted with a registry entry."
  exit 1
fi

# Find every Admitted in the corpus.  For each, extract the enclosing
# theorem name via a backward scan to the nearest Theorem/Lemma.
violations=0
counterex_hits=0
deferred_hits=0
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
  if echo "$COUNTEREXAMPLE_KEYS" | grep -qxF "$key"; then
    counterex_hits=$((counterex_hits + 1))
  elif echo "$DEFERRED_KEYS" | grep -qxF "$key"; then
    deferred_hits=$((deferred_hits + 1))
  else
    echo "::error::$file:$lineno ($thm) -- not in any registry." >&2
    echo "  Either:"
    echo "    - Add a counterexample entry (theorem is unprovable as stated)."
    echo "    - Add a deferred-proof entry (theorem provable, work pending)."
    echo "    - Close the proof."
    violations=$((violations + 1))
  fi
done < <(grep -rnE '^[[:space:]]*Admitted[[:space:]]*\.' \
           theories/ theories-flocq/ --include='*.v' 2>/dev/null)

if [ "$violations" -gt 0 ]; then
  echo ""
  echo "Found $violations unregistered Admitted theorem(s)."
  exit 1
fi

total=$((counterex_hits + deferred_hits))
echo "All Admitted theorems registered ($total total: $counterex_hits counterexample, $deferred_hits deferred-proof)."
exit 0
