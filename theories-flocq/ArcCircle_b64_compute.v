(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ArcCircle_b64_compute
   ----------------------------------------------------------------------------
   COMPUTATIONAL (extractable) binary64 arc-circle sign-product predicate --
   the oracle compute path for the RocqRefRunner ARC_CHORD_CROSSES_CIRCLE mode.

   Mirrors `chord_crosses_arc_circle` (theories/ArcIntersect.v:129)

       sP := inCircle_R (arc_start) (arc_mid) (arc_end) P ;
       sQ := inCircle_R (arc_start) (arc_mid) (arc_end) Q ;
       sP * sQ < 0

   on the `b64_*` layer, using the extracted `b64_inCircle`.  The arc is taken
   as its three control BPoints (S, M, E) directly, matching the oracle wire
   protocol (no CircularArc record at the b64 boundary).  Replaces the
   driver's hand-rolled `sp *. sq < 0.0` glue.

   SOUNDNESS STATUS.  This is a SUFFICIENT-condition filter: when it returns
   true, the chord crosses the arc's circumcircle (the IVT witness
   `chord_crosses_arc_circle_implies_circle_intersection`, ArcIntersectIVT.v);
   false does NOT imply non-crossing.  The bridge from the rounded b64 sign
   product to the R-side `chord_crosses_arc_circle` rides on the deferred
   `b64_inCircle` sign-exactness (docs/oracle-handroll-migration.md items 2/3);
   this file provides the de-hand-rolled, single-sourced compute path, bit-
   exact with the previous native glue.
   ========================================================================== *)

From Flocq Require Import IEEE754.Binary.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import HotPixel_b64.            (* b64_lt *)
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute. (* b64_zero *)
From NTS.Proofs.Flocq Require Import InCircle_b64_compute.    (* b64_inCircle *)

Definition b64_chord_crosses_arc_circle (S M E P Q : BPoint) : bool :=
  b64_lt (b64_mult (b64_inCircle S M E P) (b64_inCircle S M E Q)) b64_zero.
