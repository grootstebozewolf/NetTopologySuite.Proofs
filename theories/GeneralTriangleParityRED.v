(* ============================================================================
   NetTopologySuite.Proofs.GeneralTriangleParityRED
   ----------------------------------------------------------------------------
   RED for the arbitrary-triangle ray-parity programme: the queued parity target
   `GeneralTriangleParity.gtri_parity_spec` is FALSE AS STATED.

   `gtri_parity_spec ax ay bx by_ cx cy` asserts, for ALL points p,

       point_in_ring p (gtri_ring ...)  <->  0 < gtri ... p

   i.e. the rightward-ray parity test decides EXACTLY the *strict* algebraic
   interior (all three inward signed areas positive).  This is too strong: the
   ray-parity `point_in_ring` is a HALF-OPEN membership test (it includes part
   of the boundary), exactly as the rectangle case made explicit in
   `RectangleJCT.point_in_ring_rect_iff`
       point_in_ring p rect  <->  (y0 < py p < y1 /\ x0 <= px p < hyp_x ...)
   -- note `x0 <= px` (LEFT edge INCLUDED) versus the strict interior.

   Witness: the CCW triangle A=(0,0), B=(4,0), C=(0,4) and the point (0,2) on
   its LEFT edge C--A.  There:
     - `point_in_ring (0,2)` is TRUE -- the rightward ray crosses the hypotenuse
       B--C exactly once (the left edge it lies on does not count, px is not
       strictly less than the edge's x), so the parity is odd; yet
     - `gtri (0,2) = 0` (the third inward slack gsC vanishes -- the point is on
       the edge, not strictly inside), so `0 < gtri (0,2)` is FALSE.

   Hence the biconditional fails (TRUE <-> FALSE), refuting `gtri_parity_spec`.

   CONSEQUENCE / corrected target.  The provable parity characterisation for an
   arbitrary triangle is the HALF-OPEN one (à la `point_in_ring_rect_iff`), not
   `<-> 0 < gtri`.  The single TRUE and downstream-useful direction is

       0 < gtri p  /\  ray_avoids_vertices p (gtri_ring ...)  ->  point_in_ring p

   (strict interior, under the rightward-ray genericity guard -- the guard is
   also genuinely needed: a strict-interior point whose height equals a vertex's
   makes the ray graze that vertex and miscounts, cf.
   `JCT_VertexGrazingCounterexample.v`).  That guarded direction is what yields
   the triangle hole-nesting headline `hole_inside_outer_triangle`
   (the analogue of `HoleInsideOuterRect.hole_inside_outer_rect`), the genuine
   next GREEN slice for the `hole_inside_outer` residual of `extract_rings_valid`.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import RectangleJCT GeneralTriangleSeparation GeneralTriangleParity.
Import ListNotations.

Local Open Scope R_scope.

(* The witness point (0,2) on the left edge C--A of triangle (0,0),(4,0),(0,4). *)

(* It IS in the ray-parity ring: the hypotenuse B--C crosses the rightward ray
   once, the other two edges do not. *)
Lemma red_pir_witness :
  point_in_ring (mkPoint 0 2) (gtri_ring 0 0 4 0 0 4).
Proof.
  unfold point_in_ring. rewrite ring_edges_gtri.
  (* edges: [ ((0,0),(4,0)) ; ((4,0),(0,4)) ; ((0,4),(0,0)) ] *)
  apply rpo_skip.
  - (* bottom A--B does not cross *)
    rewrite (edge_cross_sign 0 0 4 0 (mkPoint 0 2)); cbn [px py].
    intros [[Hy _] | [Hy _]]; lra.
  - apply rpo_cross.
    + (* hypotenuse B--C crosses *)
      rewrite (edge_cross_sign 4 0 0 4 (mkPoint 0 2)); cbn [px py].
      left; repeat split; nra.
    + apply rpe_skip.
      * (* left C--A does not cross (point lies on it: px not strictly less) *)
        rewrite (edge_cross_sign 0 4 0 0 (mkPoint 0 2)); cbn [px py].
        intros [[Hy _] | [_ Hs]]; nra.
      * apply rpe_nil.
Qed.

(* But it is NOT strictly inside: the inward slack gsC vanishes (on the edge). *)
Lemma red_gtri_witness_zero :
  gtri 0 0 4 0 0 4 (mkPoint 0 2) = 0.
Proof.
  unfold gtri, gsA, gsB, gsC; cbn [px py].
  assert (HA : (4 - 0) * (2 - 0) - (0 - 0) * (0 - 0) = 8) by nra.
  assert (HB : (0 - 4) * (2 - 0) - (4 - 0) * (0 - 4) = 8) by nra.
  assert (HC : (0 - 0) * (2 - 4) - (0 - 4) * (0 - 0) = 0) by nra.
  rewrite HA, HB, HC.
  unfold Rmin; repeat destruct (Rle_dec _ _); lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The RED: the queued spec is false as stated.                                *)
(* -------------------------------------------------------------------------- *)

Theorem gtri_parity_spec_false :
  ~ gtri_parity_spec 0 0 4 0 0 4.
Proof.
  unfold gtri_parity_spec. intro H.
  destruct (H (mkPoint 0 2)) as [Hfwd _].
  pose proof (Hfwd red_pir_witness) as Hpos.
  rewrite red_gtri_witness_zero in Hpos.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions gtri_parity_spec_false.
