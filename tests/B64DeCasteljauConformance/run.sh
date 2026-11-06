#!/usr/bin/env bash
# Reproduce the de Casteljau proof-to-code conformance run end to end.
#   tests/B64DeCasteljauConformance/run.sh [CORPUS_DIR]
# Needs: Rocq 9.x + Flocq with theories-flocq built (see scripts/rebuild_oracle_ffi.sh),
# OCaml (ocamlfind), python3, dotnet SDK 8+.  Exit 0 = zero mismatches.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"; cd "$ROOT"
DIR="${1:-$(mktemp -d)}"
# 1. extract the Rocq evaluator (includes B64_DeCasteljauEval.dc_eval) and build the oracle
if command -v rocq >/dev/null 2>&1; then COQC="rocq c"; else COQC=coqc; fi
$COQC -Q theories NTS.Proofs -Q theories-flocq NTS.Proofs.Flocq theories-flocq/Validate_binary64_extract.v
make -C oracle oracle_bin
# 2. corpus + the oracle's answers
python3 tests/B64DeCasteljauConformance/corpus.py --oracle oracle/oracle_bin --out "$DIR"
# 3. FMA absence in the oracle binary (OCaml native code)
if objdump -d oracle/oracle_bin | grep -qiE 'vfmadd|vfmsub|vfnmadd|vfnmsub'; then
  echo "!! oracle_bin contains FMA instructions"; exit 1; fi
# 4. C# port replays the corpus bit for bit (also reports the FMA canary)
dotnet run --project tests/B64DeCasteljauConformance -c Release -- "$DIR"
