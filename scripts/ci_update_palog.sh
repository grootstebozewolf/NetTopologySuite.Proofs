#!/usr/bin/env bash
# =============================================================================
# scripts/ci_update_palog.sh
# -----------------------------------------------------------------------------
# Split an output-synced build log into per-file Print Assumptions chunks.
#
# Usage:
#   scripts/ci_update_palog.sh <build.log>
#
# The log must come from `make --output-sync=target` (or -j1), so each
# `ROCQ compile <file>` line is contiguous with that file's compile output,
# including its `Axioms:` / `Closed under the global context` blocks.
# Every file that was (re)compiled in this run gets its chunk REPLACED at
# .palog/<file>.log; files that make skipped keep their cached chunks.
# scripts/ci_assemble_palog.sh later concatenates one chunk per project
# file (failing hard on any gap) to feed scripts/audit_axioms.sh.
#
# A chunk is therefore always the verbatim audit-relevant output of the
# same compile that produced the file's cached .vo -- same provenance, so
# auditing cached chunks is exactly as strong as auditing a fresh
# sequential log.
#
# Exit codes: 0 on success, 2 on usage/IO error.
# =============================================================================

set -euo pipefail

if [ $# -ne 1 ] || [ ! -r "$1" ]; then
  echo "usage: $0 <build.log>" >&2
  exit 2
fi
LOG="$1"
PALOG_DIR=".palog"

# Pre-create the chunk directories for every directory that appears in the
# project file (comment text is stripped first -- prose may end in `.v`).
sed -e 's/#.*//' -e 's/[[:space:]]*$//' -e '/\.v$/!d' _CoqProject.full \
  | while IFS= read -r vfile; do
      dirname "$PALOG_DIR/$vfile"
    done | sort -u | xargs -r mkdir -p

# Chunk writer: a new `ROCQ compile <file>` line closes the previous chunk
# and truncates+opens the new one (awk's `>` truncates only on first open,
# then appends).  Lines before the first marker (coqdep, make banners) are
# dropped.  close() keeps the open-file count at one regardless of corpus
# size.
awk -v palog="$PALOG_DIR" '
  /^ROCQ compile / {
    if (out != "") close(out)
    file = substr($0, 14)
    out = palog "/" file ".log"
    printf "" > out
  }
  out != "" { print > out }
' "$LOG"

updated=$(grep -c '^ROCQ compile ' "$LOG" || true)
echo "[update-palog] refreshed $updated chunk(s) from $LOG."
