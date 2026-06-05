(* ============================================================================
   NetTopologySuite.Proofs.Flocq.HotPixelConvex_b64
   ----------------------------------------------------------------------------
   Dovetail with `in_hot_pixel_convex` (theories/HotPixel.v, clean lane
   b468ad6) on the binary64 / oracle side.

   Context.  docs/oracle-soundness-finding.md established (grounded, oracle-
   confirmed) that the rounded Liang-Barsky filter the oracle runs
   over-accepts within O(ulp) of tangency -- the unsoundness lives entirely in
   the EDGE / t-bound DIVISION (`b64_div`).  The complementary ENDPOINT route
   is division-free; `in_hot_pixel_convex` is its geometric backbone: the
   half-open pixel is convex, so two in-pixel endpoints put the WHOLE segment
   in the pixel.

   These seams lift that to the b64-bridged points the oracle reasons about
   (`BP2P`), and pin the midpoint case (t = 1/2) -- which is exactly the
   midpoint witness `b64_liang_barsky_touches_halfopen` uses (`xmid < xhi`,
   `ymid < yhi`).  Both are unconditional and rounding-free at the geometry
   level (no `b64_div`), so unlike the edge route they are exactly sound.
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance HotPixel.
From NTS.Proofs.Flocq Require Import Validate_binary64 Intersect_b64.

Local Open Scope R_scope.

(* Both bridged endpoints in the pixel ⇒ every point of the bridged segment is
   in the pixel.  Specialisation of in_hot_pixel_convex to BP2P points. *)
Lemma b64_both_endpoints_in_pixel_whole_segment :
  forall (P0 P1 C : BPoint) (scale t : R),
    0 <= t <= 1 ->
    in_hot_pixel (BP2P P0) (BP2P C) scale ->
    in_hot_pixel (BP2P P1) (BP2P C) scale ->
    in_hot_pixel (segment_point (BP2P P0) (BP2P P1) t) (BP2P C) scale.
Proof.
  intros P0 P1 C scale t Ht H0 H1.
  exact (in_hot_pixel_convex (BP2P P0) (BP2P P1) (BP2P C) scale t Ht H0 H1).
Qed.

(* Midpoint case: the witness the half-open filter checks (xmid < xhi). *)
Corollary b64_midpoint_in_pixel_of_endpoints :
  forall (P0 P1 C : BPoint) (scale : R),
    in_hot_pixel (BP2P P0) (BP2P C) scale ->
    in_hot_pixel (BP2P P1) (BP2P C) scale ->
    in_hot_pixel (segment_point (BP2P P0) (BP2P P1) (1 / 2)) (BP2P C) scale.
Proof.
  intros P0 P1 C scale H0 H1.
  apply b64_both_endpoints_in_pixel_whole_segment; [ lra | exact H0 | exact H1 ].
Qed.
