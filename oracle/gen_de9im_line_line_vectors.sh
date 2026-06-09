#!/bin/sh
# Emit the static Romanschek line–line DE-9IM oracle vector file.
# Regenerate: sh oracle/gen_de9im_line_line_vectors.sh > oracle/de9im_line_line_vectors.txt
set -e
ROOT="$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)"
exec cat "$ROOT/oracle/de9im_line_line_vectors.txt"