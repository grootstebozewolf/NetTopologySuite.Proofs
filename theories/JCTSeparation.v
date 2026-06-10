(* ============================================================================
   NetTopologySuite.Proofs.JCTSeparation
   ----------------------------------------------------------------------------
   H1 PROPER, part 7: THE SEPARATION CLAUSE OF THE JORDAN CURVE THEOREM,
   unconditional -- and the escape residual discharged on every total family.

   The transport engine + the half-open parity kernel give, for EVERY closed
   ring (no simplicity needed):

     parity_constant_on_components :
       guarded endpoints of a complement path have EQUAL strict parity;

     odd_even_separated :
       an odd-parity (inside) point and an even-parity (outside) point are
       NEVER connected within the complement.

   This is precisely the separation clause that PR #82 added to the corpus's
   `JCT_two_components_cont` hypothesis -- the "the two components are
   genuinely distinct" half of the Jordan Curve Theorem -- now a THEOREM
   rather than a clause of a named hypothesis.

   Second deliverable: the final residual `even_parity_escapes` is TRUE on
   every family with a total seam -- rectangle, arbitrary CCW triangle,
   right triangle -- each by the family's field trichotomy (positive: the
   interior parity theorem contradicts evenness; zero: the skeleton
   contradicts the complement; negative: the family's escape engine).  So
   the remaining H1 residual (`escape_descent` / `even_parity_escapes` for
   general simple rings) is verified non-vacuous and consistent on every
   family the corpus can decide.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import RectangleJCT RectangleSeparation RectangleOffringSeam.
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity.
From NTS.Proofs Require Import GeneralTriangleHoleNesting GeneralTriangleJCT.
From NTS.Proofs Require Import GeneralTriangleExterior GeneralTriangleOffringSeam.
From NTS.Proofs Require Import ConvexOffringSeam RightTriangleJCT.
From NTS.Proofs Require Import JCTParityTransport JCTHalfOpenParity.
From NTS.Proofs Require Import JCTGenericStability JCTLevelJump JCTTrappedHalf.
From NTS.Proofs Require Import JCTSeamAssembly JCTEscapeDescent.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  Parity is constant on complement components (guarded endpoints).
   --------------------------------------------------------------------------- *)

Theorem parity_constant_on_components : forall (r : Ring) (p q : Point),
  ring_closed r ->
  ray_avoids_vertices p r ->
  ray_avoids_vertices q r ->
  connected_in_complement_cont r p q ->
  (point_in_ring p r <-> point_in_ring q r).
Proof.
  intros r p q Hclosed Hgp Hgq [g [Hgc [Hg0 [Hg1 Hcompl]]]].
  pose proof (invariant_transport_along_path
                (fun z => point_in_ring_ho z r) g
                (fun z => point_in_ring_ho_dec z r)
                (ho_parity_locally_constant_holds r Hclosed g Hgc Hcompl))
    as Hiff.
  rewrite Hg0, Hg1 in Hiff.
  rewrite <- (point_in_ring_ho_agrees p r Hgp),
          <- (point_in_ring_ho_agrees q r Hgq).
  exact Hiff.
Qed.

(* THE SEPARATION CLAUSE OF THE JCT, unconditional for closed rings: inside
   and outside (by parity) never meet through the complement. *)
Corollary odd_even_separated : forall (r : Ring) (p q : Point),
  ring_closed r ->
  ray_avoids_vertices p r ->
  ray_avoids_vertices q r ->
  point_in_ring p r ->
  ~ point_in_ring q r ->
  ~ connected_in_complement_cont r p q.
Proof.
  intros r p q Hclosed Hgp Hgq Hin Hout Hconn.
  apply Hout.
  exact (proj1 (parity_constant_on_components r p q Hclosed Hgp Hgq Hconn) Hin).
Qed.

(* And the geometric-flavoured corollary: a guarded geometric-interior point
   never connects to a guarded even-parity point. *)
Corollary geometric_interior_even_separated : forall (r : Ring) (p q : Point),
  ring_closed r ->
  ring_complement r p ->
  ray_avoids_vertices p r ->
  ray_avoids_vertices q r ->
  point_in_ring p r ->
  ~ point_in_ring q r ->
  geometric_interior_cont p r /\ ~ connected_in_complement_cont r p q.
Proof.
  intros r p q Hclosed Hcompl Hgp Hgq Hin Hout.
  split.
  - exact (point_in_ring_imp_geometric_cont r p Hclosed Hcompl Hgp Hin).
  - exact (odd_even_separated r p q Hclosed Hgp Hgq Hin Hout).
Qed.

(* ---------------------------------------------------------------------------
   §2  The escape residual holds on every total family.
   --------------------------------------------------------------------------- *)

Theorem rect_even_parity_escapes : forall (x0 y0 x1 y1 : R) (p : Point),
  x0 < x1 -> y0 < y1 ->
  ring_complement (rect_ring x0 y0 x1 y1) p ->
  even_parity_escapes (rect_ring x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hcompl Hnin Hbnd.
  destruct (Rtotal_order (box_min x0 y0 x1 y1 p) 0) as [Hneg | [Hz | Hpos]].
  - (* exterior: the axis-aligned escapes *)
    destruct (box_min_neg_inv x0 y0 x1 y1 p Hneg) as [H | [H | [H | H]]].
    + refine (escape_beyond_x_low _ _ x0 _ H Hbnd).
      intros v Hv;
        exact (proj1 (proj1 (rect_image_bounds x0 y0 x1 y1 v Hx01 Hy01 Hv))).
    + refine (escape_beyond_x_high _ _ x1 _ H Hbnd).
      intros v Hv;
        exact (proj2 (proj1 (rect_image_bounds x0 y0 x1 y1 v Hx01 Hy01 Hv))).
    + refine (escape_beyond_y_low _ _ y0 _ H Hbnd).
      intros v Hv;
        exact (proj1 (proj2 (rect_image_bounds x0 y0 x1 y1 v Hx01 Hy01 Hv))).
    + refine (escape_beyond_y_high _ _ y1 _ H Hbnd).
      intros v Hv;
        exact (proj2 (proj2 (rect_image_bounds x0 y0 x1 y1 v Hx01 Hy01 Hv))).
  - exact (box_min_nonzero_off_skeleton x0 y0 x1 y1 p Hx01 Hy01 Hcompl Hz).
  - (* interior would be odd: contradiction with evenness *)
    apply Hnin. apply box_min_pos_iff in Hpos.
    apply (point_in_ring_rect_iff x0 y0 x1 y1 p Hx01 Hy01).
    split; [ tauto | split; [ lra | tauto ] ].
Qed.

Theorem gtri_even_parity_escapes : forall (ax ay bx by_ cx cy : R) (p : Point),
  0 < gdbl ax ay bx by_ cx cy ->
  ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
  ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
  even_parity_escapes (gtri_ring ax ay bx by_ cx cy) p.
Proof.
  intros ax ay bx by_ cx cy p Hccw Hcompl Hrav Hnin Hbnd.
  destruct (Rtotal_order (gtri ax ay bx by_ cx cy p) 0) as [Hneg | [Hz | Hpos]].
  - exact (gtri_exterior_escapes ax ay bx by_ cx cy p Hccw Hneg Hbnd).
  - apply Hcompl.
    exact (gtri_zero_imp_ring_image ax ay bx by_ cx cy Hccw p Hz).
  - apply Hnin.
    exact (gtri_interior_in_ring ax ay bx by_ cx cy p Hpos Hrav).
Qed.

Theorem rtri_even_parity_escapes : forall (x0 y0 x1 y1 : R) (p : Point),
  x0 < x1 -> y0 < y1 ->
  ring_complement (rtri_ring x0 y0 x1 y1) p ->
  ray_avoids_vertices p (rtri_ring x0 y0 x1 y1) ->
  even_parity_escapes (rtri_ring x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hcompl Hrav.
  rewrite rtri_ring_is_gtri in *.
  apply gtri_even_parity_escapes; try assumption.
  unfold gdbl. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions parity_constant_on_components.
Print Assumptions odd_even_separated.
Print Assumptions rect_even_parity_escapes.
Print Assumptions gtri_even_parity_escapes.
