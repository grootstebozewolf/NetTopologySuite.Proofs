#!/usr/bin/env bash
# =============================================================================
# scripts/theories_changed.sh
# -----------------------------------------------------------------------------
# Local incremental proof-check helper: rebuild only the theories/ .v files
# that changed versus a base ref, PLUS their transitive reverse-dependents
# (every file that imports a changed file, directly or indirectly).
#
# This is a DEVELOPER CONVENIENCE for fast local iteration ("did my edit break
# anything downstream?").  It is NOT the CI gate: CI still compiles the whole
# lane (incrementally on PRs via the content-addressed .vo cache, from clean on
# main), so this can never cause the corpus to be under-checked on merge.
#
# The reverse-dependent set is computed from `rocq dep` (coqdep), so it is
# exact w.r.t. the import graph, not a coarse _CoqProject-order over-approx.
#
# Usage:
#   scripts/theories_changed.sh [BASE_REF]     # default BASE_REF = origin/main
#   CI_VO_PROJECT=_CoqProject.full scripts/theories_changed.sh   # full lane
#
# Env:
#   CI_VO_PROJECT   which _CoqProject to build against (default _CoqProject)
#   DRY_RUN=1       print the .vo targets that would build, don't build
# =============================================================================
set -euo pipefail

BASE="${1:-origin/main}"
PROJECT="${CI_VO_PROJECT:-_CoqProject}"

if ! command -v rocq >/dev/null 2>&1; then
  echo "[theories-changed] no 'rocq' on PATH (set up the toolchain first)" >&2
  exit 2
fi

# Changed .v sources under theories/ (Added/Copied/Modified/Renamed), vs BASE.
mapfile -t CHANGED < <(git diff --name-only --diff-filter=ACMR "$BASE"...HEAD -- 'theories/*.v' 2>/dev/null || true)
if [ "${#CHANGED[@]}" -eq 0 ]; then
  echo "[theories-changed] no changed theories/*.v vs $BASE — nothing to rebuild."
  exit 0
fi
echo "[theories-changed] changed vs $BASE:"
printf '  %s\n' "${CHANGED[@]}"

# Fresh dependency graph for the requested project.
rocq makefile -f "$PROJECT" -o Makefile.gen >/dev/null 2>&1

# Transitive reverse-dependent .vo closure of the changed files, from coqdep.
# NB: the coqdep output is passed as a FILE arg (not piped to stdin) because
# stdin here is the heredoc carrying this python source.
DEPFILE="$(mktemp)"
trap 'rm -f "$DEPFILE"' EXIT
rocq dep -f "$PROJECT" 2>/dev/null > "$DEPFILE"
mapfile -t TARGETS < <(
  python3 - "$DEPFILE" "${CHANGED[@]}" <<'PY'
import sys
depfile = sys.argv[1]
changed = set(sys.argv[2:])
# forward: vo -> set(vo deps); also remember each vo's .v source
deps, src_of_vo = {}, {}
for line in open(depfile, encoding="utf-8"):
    if ":" not in line:
        continue
    lhs, rhs = line.split(":", 1)
    targets = [t for t in lhs.split() if t.endswith(".vo")]
    vodeps  = [d for d in rhs.split() if d.endswith(".vo")]
    vsrcs   = [d for d in rhs.split() if d.endswith(".v")]
    for t in targets:
        deps.setdefault(t, set()).update(vodeps)
        for v in vsrcs:
            src_of_vo[t] = v
# reverse graph
rev = {}
for t, ds in deps.items():
    for d in ds:
        rev.setdefault(d, set()).add(t)
# seed: the .vo of each changed .v
seed = {vo for vo, v in src_of_vo.items() if v in changed}
# BFS over reverse edges
seen = set(seed); stack = list(seed)
while stack:
    cur = stack.pop()
    for up in rev.get(cur, ()):
        if up not in seen:
            seen.add(up); stack.append(up)
for vo in sorted(seen):
    print(vo)
PY
)

if [ "${#TARGETS[@]}" -eq 0 ]; then
  echo "[theories-changed] could not map changes to .vo targets (new file not yet in $PROJECT?)." >&2
  exit 0
fi

echo "[theories-changed] ${#TARGETS[@]} target(s) to rebuild (changed + dependents):"
printf '  %s\n' "${TARGETS[@]}"

if [ "${DRY_RUN:-}" = "1" ]; then
  exit 0
fi

exec make -f Makefile.gen -j"$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2)" "${TARGETS[@]}"
