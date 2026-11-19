#!/usr/bin/env bash
# Regenerate tools/klic-demo/ocaml/hotpixel_q.ml from the Rocq sources.
# Run from the repo root once theories-flocq/HotPixel_Q_exec.vo is built
# (make -f Makefile.gen theories-flocq/HotPixel_Q_exec.vo).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
rm -f tools/klic-demo/ocaml/hotpixel_q.ml tools/klic-demo/ocaml/hotpixel_q.mli
rocq compile -Q theories NTS.Proofs -Q theories-flocq NTS.Proofs.Flocq \
  tools/klic-demo/rocq/Extract_HotPixel_Q.v
rm -f tools/klic-demo/rocq/Extract_HotPixel_Q.vo tools/klic-demo/rocq/Extract_HotPixel_Q.vok \
      tools/klic-demo/rocq/Extract_HotPixel_Q.vos tools/klic-demo/rocq/Extract_HotPixel_Q.glob \
      tools/klic-demo/rocq/.Extract_HotPixel_Q.aux
echo "extracted: tools/klic-demo/ocaml/hotpixel_q.ml"
