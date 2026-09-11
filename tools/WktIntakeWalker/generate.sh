#!/usr/bin/env bash
# Generate ANTLR Java sources from the pinned grammars-v4 #4997 .g4 files.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
GEN="$ROOT/java/org/nts/proofs/intake/gen"
JAR="${ANTLR_JAR:-$ROOT/.antlr/antlr-4.13.2-complete.jar}"
mkdir -p "$(dirname "$JAR")" "$GEN"
if [ ! -f "$JAR" ]; then
  curl -fsSL -o "$JAR" https://www.antlr.org/download/antlr-4.13.2-complete.jar
fi
java -jar "$JAR" -Dlanguage=Java -visitor -no-listener \
  -o "$GEN" -package org.nts.proofs.intake.gen \
  "$ROOT/grammar/wktLexer.g4" "$ROOT/grammar/wktParser.g4"
rm -f "$GEN"/*.interp "$GEN"/*.tokens
echo "generated $GEN"
