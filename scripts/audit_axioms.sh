#!/usr/bin/env bash
# =============================================================================
# scripts/audit_axioms.sh
# -----------------------------------------------------------------------------
# Per-theorem axiom audit.  Reads a build log with *per-file contiguous*
# output, identifies every `Print Assumptions` output block, and verifies
# that the axioms named in each block are a subset of
# `docs/axiom-allowlist.txt`.  Files listed in `docs/audit-exceptions.txt`
# are exempted (their contamination is the known, transitional state
# being cleared file-by-file by the parametric-architecture refactor).
#
# Usage:
#   scripts/audit_axioms.sh <build.log>
#
# The build log must keep each `ROCQ compile <file>` line contiguous
# with that file's subsequent `Axioms:` / `Closed under the global
# context` blocks (no interleaving from concurrent compiles).  Either
# of these produces such a log:
#
#   make -f Makefile.gen -j"$(nproc)" --output-sync=target   # fast (GNU make >= 4.0)
#   make -f Makefile.gen -j1                                 # sequential fallback
#
# `--output-sync=target` buffers each target's whole recipe output and
# emits it atomically, so parallel builds are safe to audit.  The
# attribution only depends on per-file contiguity, not on global build
# order.  See guardrail-4 rationale in commit history (the May 2026
# axiom-leak investigation showed plain -j2 logs interleave).
#
# Exit codes:
#   0  -- no violations.
#   1  -- one or more non-exempted PA blocks contain disallowed axioms.
#   2  -- usage / file-access error.
# =============================================================================

set -u

if [ $# -ne 1 ]; then
  echo "usage: $0 <build.log>" >&2
  exit 2
fi

BUILD_LOG="$1"
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ALLOWLIST="$REPO_ROOT/docs/axiom-allowlist.txt"
EXCEPTIONS="$REPO_ROOT/docs/audit-exceptions.txt"

for f in "$BUILD_LOG" "$ALLOWLIST" "$EXCEPTIONS"; do
  if [ ! -r "$f" ]; then
    echo "[axioms-audit] cannot read $f" >&2
    exit 2
  fi
done

# Materialise stripped versions of the allowlist and exceptions in a
# temp dir, so we can grep -qFx against them without re-parsing every
# lookup.
TMPDIR_AUDIT="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_AUDIT"' EXIT
ALLOWED_FILE="$TMPDIR_AUDIT/allowed"
EXEMPT_FILE="$TMPDIR_AUDIT/exempt"
sed -e 's/#.*//' -e 's/[[:space:]]//g' -e '/^$/d' "$ALLOWLIST"  > "$ALLOWED_FILE"
sed -e 's/#.*//' -e 's/[[:space:]]//g' -e '/^$/d' "$EXCEPTIONS" > "$EXEMPT_FILE"

is_allowed() {
  grep -qFx -- "$1" "$ALLOWED_FILE"
}

is_exempt_file() {
  grep -qFx -- "$1" "$EXEMPT_FILE"
}

# Per-block state.
current_file=""
in_block=0
block_axioms=""

violations_total=0
violations_files=""

flush_block() {
  if [ -z "$block_axioms" ]; then
    block_axioms=""
    in_block=0
    return
  fi
  if is_exempt_file "$current_file"; then
    block_axioms=""
    in_block=0
    return
  fi
  local disallowed=""
  local ax
  while IFS= read -r ax; do
    [ -z "$ax" ] && continue
    if ! is_allowed "$ax"; then
      if [ -z "$disallowed" ]; then
        disallowed="$ax"
      else
        disallowed="$disallowed
$ax"
      fi
    fi
  done <<EOF
$block_axioms
EOF
  if [ -n "$disallowed" ]; then
    echo "[axioms-audit] VIOLATION in $current_file"
    while IFS= read -r ax; do
      echo "    disallowed axiom: $ax"
    done <<EOF
$disallowed
EOF
    violations_total=$((violations_total + 1))
    case " $violations_files " in
      *" $current_file "*) ;;
      *) violations_files="$violations_files $current_file" ;;
    esac
  fi
  block_axioms=""
  in_block=0
}

while IFS= read -r line; do
  case "$line" in
    "ROCQ compile "*)
      flush_block
      current_file="${line#ROCQ compile }"
      continue
      ;;
    "Axioms:")
      flush_block
      in_block=1
      continue
      ;;
    "Closed under the global context")
      flush_block
      continue
      ;;
  esac
  if [ "$in_block" -eq 1 ]; then
    # Block-internal line.  Axiom-name lines have the shape
    #     <Module.path.name> : <type ...>
    # where the name MUST contain at least one `.` (module-path
    # separator).  This excludes lines like `Warning: ...`, `File "...":`,
    # and other Coq diagnostic output that happens to contain a colon.
    if echo "$line" | grep -qE '^[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z][A-Za-z0-9_]*)+[[:space:]]*:'; then
      ax="$(echo "$line" | sed -e 's/[[:space:]]*:.*//' -e 's/[[:space:]]//g')"
      if [ -z "$block_axioms" ]; then
        block_axioms="$ax"
      else
        block_axioms="$block_axioms
$ax"
      fi
    fi
    # Blank line closes the block.
    if [ -z "$line" ]; then
      flush_block
    fi
  fi
done < "$BUILD_LOG"

flush_block

if [ "$violations_total" -gt 0 ]; then
  echo ""
  echo "[axioms-audit] FAIL: $violations_total file(s) with non-exempt violations:$violations_files"
  exit 1
fi

echo "[axioms-audit] OK: all per-theorem PA blocks satisfy the allowlist (or are exempted)."
exit 0
