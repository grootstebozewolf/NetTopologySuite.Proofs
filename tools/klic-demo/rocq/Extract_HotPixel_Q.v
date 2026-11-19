(* ============================================================================
   tools/klic-demo/rocq/Extract_HotPixel_Q.v
   ----------------------------------------------------------------------------
   Extracts the executable Q twin (theories-flocq/HotPixel_Q_exec.v) to OCaml
   for the KLIC hot-pixel demo.  NO extraction overrides: Z, positive and Q
   extract as the Stdlib inductive types, so every arithmetic step the demo
   relies on is the extracted Rocq definition, not a native shim.  The only
   hand-written OCaml is tools/klic-demo/ocaml/main.ml (text I/O: decimal
   digit <-> Z conversion built from the extracted Z.add / Z.mul / Z.div_eucl).

   Regenerate (from the repo root, after building HotPixel_Q_exec.vo):
     bash tools/klic-demo/rocq/extract.sh
   CI checks the committed hotpixel_q.ml is byte-identical to a fresh run.

   License: BSD-3-Clause.  NetTopologySuite.Proofs contributors.
   ========================================================================== *)

From Stdlib Require Import ZArith QArith.
From Stdlib Require Extraction.
From NTS.Proofs.Flocq Require Import HotPixel_Q_exec.

Extraction Language OCaml.
Set Extraction Output Directory "tools/klic-demo/ocaml".

Extraction "hotpixel_q.ml"
  q_round_ne q_snap_coord q_snap q_snap_disp
  q_touches_closed q_passes_through_closed q_seg_intersection
  Z.add Z.mul Z.opp Z.div_eucl Z.of_nat Qred.
