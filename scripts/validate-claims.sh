#!/usr/bin/env bash
# =============================================================================
# scripts/validate-claims.sh
# -----------------------------------------------------------------------------
# Keeps docs/verified-claims.md honest (see docs/HELP.md etc. for actors).
# The markdown is a *citable index*,
# not the source of truth -- the .v files are.  This script cross-checks that
# every theorem the doc cites actually exists in the corpus, so a rename or
# removal that orphans a claim fails CI instead of silently rotting.
#
# What it checks:
#   - Every `<Module>.v : <name>` reference in the doc resolves to a file
#     under theories/ or theories-flocq/.
#   - Each cited <name> is defined there as a Theorem/Lemma/Corollary/
#     Definition/Fact/Example/Property/Remark/Inductive/Fixpoint.
#   - `<stem>_{a,b}` brace shorthand is expanded (e.g. b64_intersect_point_{x,y}
#     checks _x and _y).
#
# What it does NOT check:
#   - That the theorem is Qed-closed (the corpus-wide invariant is enforced
#     separately by scripts/check_admitted.sh).
#   - That every theorem in the corpus is documented (the doc is curated,
#     not exhaustive).
#
# Backtick tokens without the `<Module>.v : <name>` shape (axiom names,
# deferred-but-unproved names like hobby_lemma_4_3_no_proper, prose) are
# intentionally ignored -- they are not claims.
#
# Exit non-zero on any orphaned claim.
# =============================================================================
set -uo pipefail

DOC="${1:-docs/verified-claims.md}"

if [ ! -f "$DOC" ]; then
  echo "[validate-claims] ERROR: doc not found: $DOC"
  exit 2
fi

fail=0
checked=0

# Pull every `Module.v : name` reference (name may carry a {a,b} brace group).
# Portable: grep -oE (BSD/GNU) + a read loop, no `grep -P` and no `mapfile`
# (the host CI runner is macOS / bash 3.2 / BSD grep).
refs=()
while IFS= read -r ref; do
  [ -n "$ref" ] && refs+=("$ref")
done < <(grep -oE '`[A-Za-z0-9_]+\.v[[:space:]]*:[[:space:]]*[A-Za-z0-9_{},]+`' "$DOC" \
         | tr -d '`' | sort -u)

if [ "${#refs[@]}" -eq 0 ]; then
  echo "[validate-claims] ERROR: no \`Module.v : name\` claims found in $DOC"
  exit 2
fi

for ref in "${refs[@]}"; do
  base="$(echo "${ref%%:*}" | xargs)"   # Module.v
  name="$(echo "${ref#*:}"  | xargs)"   # theorem name (maybe with {..})

  # Resolve the module to a real path.
  path=""
  for d in theories theories-flocq; do
    if [ -f "$d/$base" ]; then path="$d/$base"; fi
  done
  if [ -z "$path" ]; then
    echo "  ORPHAN (no such file): $base   <- cited as \`$ref\`"
    fail=1
    continue
  fi

  # Expand a {a,b,..} brace group into concrete names.
  names=()
  if [[ "$name" == *"{"* ]]; then
    stem="${name%%\{*}"
    opts="${name#*\{}"; opts="${opts%\}*}"
    IFS=',' read -ra parts <<< "$opts"
    for p in "${parts[@]}"; do names+=("${stem}$(echo "$p" | xargs)"); done
  else
    names+=("$name")
  fi

  for nm in "${names[@]}"; do
    checked=$((checked + 1))
    if ! grep -qE "^[[:space:]]*(Theorem|Lemma|Corollary|Definition|Fact|Example|Property|Remark|Inductive|Fixpoint)[[:space:]]+${nm}([[:space:]]|:|\()" "$path"; then
      echo "  ORPHAN (not defined in $path): $nm"
      fail=1
    fi
  done
done

if [ "$fail" -ne 0 ]; then
  echo "[validate-claims] FAIL: docs/verified-claims.md cites theorems that do not exist."
  echo "  Fix the doc (rename/remove the orphaned claim) or restore the theorem."
  exit 1
fi

echo "[validate-claims] OK: all $checked cited theorems exist in the corpus."
