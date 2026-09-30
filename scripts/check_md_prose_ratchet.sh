#!/usr/bin/env bash
# =============================================================================
# scripts/check_md_prose_ratchet.sh
# -----------------------------------------------------------------------------
# PR-diff ratchet on markdown prose (AGENTS.md).  A PR may only delete .md
# prose, or amend so net non-blank .md lines shrink while content diverges
# to MMF (gate / ticket / claim / fixture).  Global net > 0 fails.
#
# MMF shape (imported, not restated): docs/scout/map-opam-mmf-release-bar.md
#
# On CI pull_request: diff vs origin/${GITHUB_BASE_REF} (fetched if missing).
# Local / no-diff: skip or pass with a clear message (HEAD==base, push event,
# missing base ref, not a git checkout).
#
# Env / args:
#   $1 or MD_PROSE_BASE   override the base ref (default: GITHUB_BASE_REF or
#                         origin/main)
#
# Exit codes:
#   0  -- net non-blank .md lines ≤ 0, or skip (no PR diff).
#   1  -- net-positive markdown prose.
#   2  -- usage / git error on a PR that must be checked.
# =============================================================================

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT" || exit 2

if ! git rev-parse --git-dir >/dev/null 2>&1; then
  echo "[md-prose-ratchet] not a git checkout — skip"
  exit 0
fi

# Push to the default branch is not a PR diff; the PR already ran this gate.
if [ "${GITHUB_EVENT_NAME:-}" = "push" ]; then
  echo "[md-prose-ratchet] push event (not a PR diff) — skip"
  exit 0
fi

if [ -n "${MD_PROSE_BASE:-}" ]; then
  BASE="$MD_PROSE_BASE"
elif [ "${1:-}" != "" ]; then
  BASE="$1"
elif [ -n "${GITHUB_BASE_REF:-}" ]; then
  BASE="origin/${GITHUB_BASE_REF}"
else
  BASE="origin/main"
fi

ensure_base() {
  local ref="$1"
  if git rev-parse --verify "${ref}^{commit}" >/dev/null 2>&1; then
    return 0
  fi
  local name="${ref#origin/}"
  if git fetch --no-tags --depth=1 origin "$name" >/dev/null 2>&1 \
     && git rev-parse --verify "${ref}^{commit}" >/dev/null 2>&1; then
    return 0
  fi
  return 1
}

if ! ensure_base "$BASE"; then
  if [ "${GITHUB_EVENT_NAME:-}" = "pull_request" ]; then
    echo "[md-prose-ratchet] FAIL: cannot resolve base ref $BASE" >&2
    exit 2
  fi
  echo "[md-prose-ratchet] no base ref ($BASE) — skip (local/no-diff)"
  exit 0
fi

HEAD_SHA="$(git rev-parse HEAD)"
BASE_SHA="$(git rev-parse "$BASE")"
if [ "$HEAD_SHA" = "$BASE_SHA" ]; then
  echo "[md-prose-ratchet] HEAD is $BASE — no PR diff, skip"
  exit 0
fi

# Three-dot when we share history (local full clone); two-dot otherwise
# (shallow CI: both trees are enough; GHA PR checkout is the merge commit).
if git merge-base "$BASE" HEAD >/dev/null 2>&1; then
  DIFF_ARGS=("${BASE}...HEAD")
else
  DIFF_ARGS=("$BASE" "HEAD")
fi

python3 - "$BASE" "${DIFF_ARGS[@]}" <<'PY'
import subprocess
import sys

base = sys.argv[1]
diff_range = sys.argv[2:]
cmd = [
    "git",
    "diff",
    "-U0",
    "-M",
    *diff_range,
    "--",
    ":(glob)**/*.md",
]
try:
    diff = subprocess.check_output(cmd, text=True, errors="replace")
except subprocess.CalledProcessError as e:
    print(f"[md-prose-ratchet] FAIL: git diff exited {e.returncode}", file=sys.stderr)
    sys.exit(2)

added = {}
deleted = {}
path = None
for line in diff.splitlines():
    if line.startswith("diff --git "):
        parts = line.split(" ")
        rhs = parts[-1]
        path = rhs[2:] if rhs.startswith("b/") else rhs
        added.setdefault(path, 0)
        deleted.setdefault(path, 0)
        continue
    if line.startswith("+++ ") or line.startswith("--- "):
        continue
    if path is None:
        continue
    if line.startswith("+") and line[1:].strip():
        added[path] = added.get(path, 0) + 1
    elif line.startswith("-") and line[1:].strip():
        deleted[path] = deleted.get(path, 0) + 1

files = sorted(set(added) | set(deleted))
if not files:
    print(f"[md-prose-ratchet] OK: no *.md changes vs {base}")
    sys.exit(0)

tot_a = tot_d = 0
rows = []
for f in files:
    a, d = added.get(f, 0), deleted.get(f, 0)
    tot_a += a
    tot_d += d
    rows.append((f, a, d, a - d))

net = tot_a - tot_d
print(f"[md-prose-ratchet] non-blank *.md lines vs {base} ({' '.join(diff_range)}):")
width = max(len(f) for f in files)
for f, a, d, n in rows:
    sign = f"{n:+d}"
    print(f"  {f:<{width}}  +{a:<4} -{d:<4}  net {sign}")
print(f"  {'total':<{width}}  +{tot_a:<4} -{tot_d:<4}  net {net:+d}")

if net > 0:
    print(
        "[md-prose-ratchet] FAIL: net-positive markdown prose "
        f"({net:+d} non-blank lines). Delete or shrink other .md in this PR, "
        "or move content into an MMF artifact (ticket / claim / fixture / "
        "ci-guard) while keeping global net ≤ 0. See AGENTS.md and "
        "docs/scout/map-opam-mmf-release-bar.md.",
        file=sys.stderr,
    )
    sys.exit(1)

print("[md-prose-ratchet] OK: net non-blank .md lines ≤ 0")
sys.exit(0)
PY
# scratch gate skip-path probe
