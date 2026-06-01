(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ArcPixel_b64_compute
   ----------------------------------------------------------------------------
   COMPUTATIONAL (extractable) binary64 arc / hot-pixel predicate -- the oracle
   compute path for the RocqRefRunner ARC_PASSES_THROUGH_PIXEL mode.

   Mirrors `arc_passes_through_hot_pixel` (theories/ArcHotPixel.v:95): the
   six-way disjunction of four pixel-edge arc-chord crossings plus the two
   arc-endpoint containment tests, in the sufficient-filter realisation the
   driver uses (edge tests via the inCircle sign-product
   `b64_chord_crosses_arc_circle`; endpoint tests via the half-open hot-pixel
   membership -- bottom + left CLOSED, top + right OPEN, Phase 2 convention).

   Replaces the driver's hand-rolled `in_hot_pixel_halfopen` and the local
   `crosses` glue in `run_arc_passes_through_pixel`.  Pixel layout at centre C,
   side `scale`, radius r = scale/2:
     bl=(cx-r,cy-r) br=(cx+r,cy-r) tr=(cx+r,cy+r) tl=(cx-r,cy+r).

   SOUNDNESS STATUS.  SUFFICIENT only (TRUE => the arc passes through the
   pixel, modulo the deferred b64_inCircle sign bridge and the S4 IVT bridge
   `arc_chord_intersect_sound`); FALSE is inconclusive.  This file provides
   the de-hand-rolled, single-sourced compute path, bit-exact with the
   previous native kernels.  docs/oracle-handroll-migration.md item 4.
   ========================================================================== *)

From Flocq Require Import IEEE754.Binary.
From NTS.Proofs.Flocq Require Import Validate_binary64.        (* b64_*, BPoint, mkBP *)
From NTS.Proofs.Flocq Require Import HotPixel_b64.             (* b64_lt, b64_half *)
From NTS.Proofs.Flocq Require Import ArcCircle_b64_compute.    (* b64_chord_crosses_arc_circle *)

(* Half-open hot-pixel membership: bottom + left CLOSED (>=), top + right
   OPEN (<).  Mirrors driver.ml's in_hot_pixel_halfopen. *)
Definition b64_in_hot_pixel_halfopen (P C : BPoint) (scale : binary64) : bool :=
  let r := b64_mult scale b64_half in
  andb (andb (b64_le (b64_minus (bx C) r) (bx P))
             (b64_lt (bx P) (b64_plus (bx C) r)))
       (andb (b64_le (b64_minus (by_ C) r) (by_ P))
             (b64_lt (by_ P) (b64_plus (by_ C) r))).

Definition b64_arc_passes_through_hot_pixel
    (S M E C : BPoint) (scale : binary64) : bool :=
  let r  := b64_mult scale b64_half in
  let bl := mkBP (b64_minus (bx C) r) (b64_minus (by_ C) r) in
  let br := mkBP (b64_plus  (bx C) r) (b64_minus (by_ C) r) in
  let tr := mkBP (b64_plus  (bx C) r) (b64_plus  (by_ C) r) in
  let tl := mkBP (b64_minus (bx C) r) (b64_plus  (by_ C) r) in
  orb (orb (orb (b64_chord_crosses_arc_circle S M E bl br)
                (b64_chord_crosses_arc_circle S M E br tr))
           (orb (b64_chord_crosses_arc_circle S M E tr tl)
                (b64_chord_crosses_arc_circle S M E tl bl)))
      (orb (b64_in_hot_pixel_halfopen S C scale)
           (b64_in_hot_pixel_halfopen E C scale)).
