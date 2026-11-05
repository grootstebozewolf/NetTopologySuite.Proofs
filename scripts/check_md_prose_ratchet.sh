#!/usr/bin/env bash
# =============================================================================
# scripts/check_md_prose_ratchet.sh
# -----------------------------------------------------------------------------
# PR-diff ratchet on markdown prose (AGENTS.md, issue #1007). Hard global
# net ≤ 0 on non-blank *.md lines vs the base. No soft +N budget. No NLP.
#
# A changed non-blank line is exempt (reported, not counted) when it is:
#   1. A table row: first non-blank character is `|`. Any file, including
#      CONTEXT.md, docs/adr/*, and README.md. Essay lines in those files
#      are NOT exempt.
#   2. An append-only claim-registry row. Paths (small, explicit):
#        docs/verified-claims.md
#        eval/README.md          (claimId table; same row shape)
#      Pattern, either:
#        - table-shaped: first non-blank is `|`
#          (claim rows and that file's separator / header rows)
#        - one-line topic stamp: ^topic:\s+\S.*\bclaimId\s*:
#      Both added and removed matching lines are exempt, so appending a
#      row or replacing one row does not move the net, and deleting rows
#      does not mint prose credit. A non-matching paragraph in the same
#      file is counted. This is not a file-wide waiver.
#   3. A one-line route-doc status bump. Path AND pattern, both required:
#        docs/thm13-priest-route.md
#        ^## Status \([0-9]{4}-[0-9]{2}-[0-9]{2}\): \S
#      The Shewchuk proof-structure status is a wrapped paragraph and is
#      not on this list. The same heading in any other file is counted.
#
# A `|` row inside a claim-registry path is reported as claim-registry,
# not as a generic table row. Other `|` rows stay in the table bucket.
#
# Residual: the exemption is the whole physical line. An essay stuffed
# onto one registry row, one `topic:` stamp, or one status heading is
# exempt. The following line is not.
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
#   --selftest            classifier checks only (no git diff)
#
# Exit codes:
#   0  -- net non-blank .md lines ≤ 0, or skip (no PR diff).
#   1  -- net-positive markdown prose.
#   2  -- usage / git error on a PR that must be checked, or selftest failure.
#
# License: BSD-3-Clause (see LICENSE)
# AI assistance disclosure: AI-drafted; human review pending.
# =============================================================================

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT" || exit 2

py_gate() {
  python3 - "$@" <<'PY'
import re
import subprocess
import sys

CLAIM_REGISTRY = {
    "docs/verified-claims.md",
    "eval/README.md",
}
TOPIC_CLAIM = re.compile(r"^topic:\s+\S.*\bclaimId\s*:")
ROUTE_STATUS = {
    "docs/thm13-priest-route.md": re.compile(
        r"^## Status \(\d{4}-\d{2}-\d{2}\): \S"
    ),
}


def classify(path, line):
    """Return blank | claim-registry | route-status | table | prose | skip."""
    if not line or line[:1] not in "+-":
        return "skip"
    body = line[1:].strip()
    if not body:
        return "blank"
    if path in CLAIM_REGISTRY and (
        body.startswith("|") or TOPIC_CLAIM.match(body)
    ):
        return "claim-registry"
    pat = ROUTE_STATUS.get(path)
    if pat is not None and pat.match(body):
        return "route-status"
    if body.startswith("|"):
        return "table"
    return "prose"


def selftest():
    cases = [
        ("README.md", "+ essay line", "prose"),
        ("README.md", "+ | a | b |", "table"),
        ("CONTEXT.md", "+ a paragraph of essay", "prose"),
        ("CONTEXT.md", "+ | still | a | table |", "table"),
        ("docs/adr/ADR-0007-sheet-hen-cook-noding-model.md",
         "+ not a table", "prose"),
        ("docs/verified-claims.md",
         "+ | `Foo.v : bar` | meaning |", "claim-registry"),
        ("docs/verified-claims.md",
         "+ topic: arc · claimId: 69-a · witness: x", "claim-registry"),
        ("docs/verified-claims.md",
         "+ **Essay paragraph about a theorem.**", "prose"),
        ("docs/verified-claims.md",
         "+ topic: no id here", "prose"),
        ("eval/README.md", "+ | `65-a` | buffer |", "claim-registry"),
        ("eval/README.md", "+ Production home for 65-a.", "prose"),
        ("docs/thm13-priest-route.md",
         "+ ## Status (2026-11-05): closed — bound proved", "route-status"),
        ("docs/thm13-priest-route.md",
         "- ## Status (2026-10-29): open — one QEX along the way",
         "route-status"),
        ("docs/thm13-priest-route.md",
         "+ Priest's statement continues here.", "prose"),
        ("docs/thm13-priest-route.md",
         "+ ## Status: open", "prose"),
        ("CONTEXT.md",
         "+ ## Status (2026-11-05): closed", "prose"),
        ("docs/verified-claims.md", "+    ", "blank"),
    ]
    for path, line, expect in cases:
        got = classify(path, line)
        if got != expect:
            print(
                f"[md-prose-ratchet] selftest fail: {path} {line!r} "
                f"-> {got}, want {expect}",
                file=sys.stderr,
            )
            return 2
    # Append of a claim row is free; one essay line is not.
    added = deleted = 0
    for path, line in (
        ("docs/verified-claims.md", "+ | `Foo.v : bar` | m |"),
        ("README.md", "+ new essay sentence"),
        ("docs/thm13-priest-route.md",
         "+ ## Status (2026-11-05): closed — bound proved"),
    ):
        kind = classify(path, line)
        if kind != "prose":
            continue
        if line.startswith("+"):
            added += 1
        else:
            deleted += 1
    if added - deleted != 1:
        print(
            f"[md-prose-ratchet] selftest net fail: {added - deleted}",
            file=sys.stderr,
        )
        return 2
    return 0


rc = selftest()
if rc != 0:
    sys.exit(rc)
if len(sys.argv) > 1 and sys.argv[1] == "--selftest":
    print("[md-prose-ratchet] selftest ok")
    sys.exit(0)

base = sys.argv[1]
diff_range = sys.argv[2:]
cmd = [
    "git", "diff", "-U0", "-M",
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
exempt = {"claim-registry": 0, "route-status": 0, "table": 0}
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
    kind = classify(path, line)
    if kind in exempt:
        exempt[kind] += 1
        continue
    if kind != "prose":
        continue
    if line.startswith("+"):
        added[path] = added.get(path, 0) + 1
    elif line.startswith("-"):
        deleted[path] = deleted.get(path, 0) + 1

if any(exempt.values()):
    print(
        "[md-prose-ratchet] exempt: "
        f"{exempt['claim-registry']} claim-registry row(s), "
        f"{exempt['route-status']} route-status line(s), "
        f"{exempt['table']} table row(s)"
    )

files = sorted(
    f for f in set(added) | set(deleted) if added.get(f, 0) or deleted.get(f, 0)
)
if not files:
    print(f"[md-prose-ratchet] OK: no counted *.md prose vs {base}")
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
    print(f"  {f:<{width}}  +{a:<4} -{d:<4}  net {n:+d}")
print(f"  {'total':<{width}}  +{tot_a:<4} -{tot_d:<4}  net {net:+d}")

if net > 0:
    print(
        "[md-prose-ratchet] FAIL: net-positive markdown prose "
        f"({net:+d} non-blank lines). Delete or shrink other .md in this PR. "
        "Exempt: `|` table rows, append-only claim-registry rows "
        "(docs/verified-claims.md, eval/README.md), and the "
        "`## Status (YYYY-MM-DD):` line in docs/thm13-priest-route.md. "
        "CONTEXT/ADR/README essays are counted. No soft +N budget. "
        "See AGENTS.md and docs/scout/map-opam-mmf-release-bar.md.",
        file=sys.stderr,
    )
    sys.exit(1)

print("[md-prose-ratchet] OK: net non-blank .md lines ≤ 0")
sys.exit(0)
PY
}

if [ "${1:-}" = "--selftest" ]; then
  py_gate --selftest
  exit $?
fi

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

py_gate "$BASE" "${DIFF_ARGS[@]}"
