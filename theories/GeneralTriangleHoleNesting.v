(* ============================================================================
   NetTopologySuite.Proofs.GeneralTriangleHoleNesting
   ----------------------------------------------------------------------------
   GREEN for the arbitrary-triangle parity (correcting the RED of
   GeneralTriangleParityRED.v): the TRUE, downstream-useful direction of the
   ray-parity test, and the triangle hole-nesting headline it yields.

   The RED showed `point_in_ring p <-> 0 < gtri p` is false (the ray test is
   half-open).  The clean TRUE characterisation, for a point on the interior
   SIDE of all three edges (`0 < gtri p`, i.e. all three inward slacks positive),
   is in terms of the three DIRECTED height bands of the edges:

     `gtri_band_in_ring`:
        0 < gtri p ->
        (ay < py p < by_  \/  by_ < py p < cy  \/  cy < py p < ay) ->
        point_in_ring p (gtri_ring ...)

   Why: with every slack positive, `edge_cross_sign` collapses each edge's
   ray-crossing to exactly its directed band condition (the slack-sign disjunct
   that would fire on the other orientation is ruled out by `0 < slack`).  The
   three directed bands are pairwise disjoint, so a point in ONE band makes
   EXACTLY ONE edge cross the rightward ray -> odd parity -> `point_in_ring`.

   This is the triangle analogue of `RectangleJCT.point_in_ring_rect_iff`'s
   membership condition (`y0 < py < y1 /\ x0 <= px < hyp_x`): the directed band
   plays the role the explicit y-range played there.  Composing with `In p hole`
   gives `hole_inside_outer_triangle`, the analogue of
   `HoleInsideOuterRect.hole_inside_outer_rect` -- a concrete, unconditional
   discharge of `hole_inside_outer` for a triangular outer ring, chipping the
   polygonal-JCT residual of `extract_rings_valid`.

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

(* For an interior-SIDE point (all three inward slacks positive), each edge
   crosses the rightward ray iff py lies in that edge's directed height band. *)
Lemma gtri_band_in_ring : forall ax ay bx by_ cx cy p,
  0 < gtri ax ay bx by_ cx cy p ->
  (ay < py p < by_ \/ by_ < py p < cy \/ cy < py p < ay) ->
  point_in_ring p (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros ax ay bx by_ cx cy p Hint Hband.
  apply gtri_pos_iff in Hint. destruct Hint as [HA [HB HC]].
  unfold gsA in HA; unfold gsB in HB; unfold gsC in HC.
  unfold point_in_ring; rewrite ring_edges_gtri.
  (* Per-edge: crossing <-> directed band (the other slack-disjunct is dead). *)
  assert (EAB : edge_crosses_ray p (mkPoint ax ay, mkPoint bx by_)
                <-> ay < py p < by_).
  { rewrite (edge_cross_sign ax ay bx by_ p). split.
    - intros [[Hy _] | [_ Hs]]; [ exact Hy | lra ].
    - intro Hy; left; split; [ exact Hy | lra ]. }
  assert (EBC : edge_crosses_ray p (mkPoint bx by_, mkPoint cx cy)
                <-> by_ < py p < cy).
  { rewrite (edge_cross_sign bx by_ cx cy p). split.
    - intros [[Hy _] | [_ Hs]]; [ exact Hy | lra ].
    - intro Hy; left; split; [ exact Hy | lra ]. }
  assert (ECA : edge_crosses_ray p (mkPoint cx cy, mkPoint ax ay)
                <-> cy < py p < ay).
  { rewrite (edge_cross_sign cx cy ax ay p). split.
    - intros [[Hy _] | [_ Hs]]; [ exact Hy | lra ].
    - intro Hy; left; split; [ exact Hy | lra ]. }
  destruct Hband as [Hb | [Hb | Hb]].
  - (* AB band: AB crosses, BC and CA do not. *)
    apply rpo_cross; [ rewrite EAB; exact Hb | ].
    apply rpe_skip; [ rewrite EBC; intros [? ?]; lra | ].
    apply rpe_skip; [ rewrite ECA; intros [? ?]; lra | ].
    apply rpe_nil.
  - (* BC band. *)
    apply rpo_skip; [ rewrite EAB; intros [? ?]; lra | ].
    apply rpo_cross; [ rewrite EBC; exact Hb | ].
    apply rpe_skip; [ rewrite ECA; intros [? ?]; lra | ].
    apply rpe_nil.
  - (* CA band. *)
    apply rpo_skip; [ rewrite EAB; intros [? ?]; lra | ].
    apply rpo_skip; [ rewrite EBC; intros [? ?]; lra | ].
    apply rpo_cross; [ rewrite ECA; exact Hb | ].
    apply rpe_nil.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: triangular outer ring contains its hole, UNCONDITIONALLY.         *)
(*                                                                            *)
(* The analogue of HoleInsideOuterRect.hole_inside_outer_rect: a hole with a   *)
(* vertex on the interior side of all three edges and in one of the directed   *)
(* height bands is nested inside the triangle.  No JCT hypothesis.             *)
(* -------------------------------------------------------------------------- *)

Theorem hole_inside_outer_triangle : forall ax ay bx by_ cx cy (hole : Ring) p,
  In p hole ->
  0 < gtri ax ay bx by_ cx cy p ->
  (ay < py p < by_ \/ by_ < py p < cy \/ cy < py p < ay) ->
  hole_inside_outer (gtri_ring ax ay bx by_ cx cy) hole.
Proof.
  intros ax ay bx by_ cx cy hole p Hin Hint Hband.
  exists p. split; [ exact Hin | apply gtri_band_in_ring; assumption ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Sanity: the CCW reference triangle (0,0),(4,0),(0,4) contains a square hole. *)
(* The centroid-ish interior vertex (1,1) sits in the CA band (cy=4 ... ay=0 is *)
(* the wrong sense; it is the AB band ay=0 < 1 < by_=0? no -- use the live band).*)
(* -------------------------------------------------------------------------- *)

Example hole_inside_outer_triangle_example :
  hole_inside_outer (gtri_ring 0 0 4 0 0 4)
                    [ mkPoint 1 1 ; mkPoint 2 1 ; mkPoint 2 2 ; mkPoint 1 2 ; mkPoint 1 1 ].
Proof.
  apply (hole_inside_outer_triangle 0 0 4 0 0 4 _ (mkPoint 1 1)).
  - cbn [In]; auto.
  - apply (proj2 (gtri_pos_iff 0 0 4 0 0 4 (mkPoint 1 1))).
    unfold gsA, gsB, gsC; cbn [px py]; repeat split; lra.
  - (* py = 1, bands: ay=0<1<by_=0 (no); by_=0<1<cy=4 (YES); cy=4<1<ay=0 (no) *)
    right; left; cbn [px py]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions gtri_band_in_ring.
Print Assumptions hole_inside_outer_triangle.
