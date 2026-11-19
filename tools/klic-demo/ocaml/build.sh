#!/usr/bin/env bash
# Build the extracted hot-pixel kernel: tools/klic-demo/ocaml/hotpixel_q
# Needs only a stock OCaml compiler (ocamlopt); no Rocq, no opam packages.
set -euo pipefail
cd "$(dirname "$0")"
out="$(pwd)/${1:-hotpixel_q}"
tmp="$(mktemp -d)"
cp hotpixel_q.mli hotpixel_q.ml main.ml "$tmp/"
if command -v ocamlopt >/dev/null 2>&1; then C=ocamlopt; else C=ocamlc; fi  # bytecode fallback
(cd "$tmp" && "$C" -w -a -o hotpixel_q hotpixel_q.mli hotpixel_q.ml main.ml)
cp "$tmp/hotpixel_q" "$out"
rm -rf "$tmp"
echo "built: $out ($C, OCaml $("$C" -version))"
