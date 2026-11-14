(* ============================================================================
   NetTopologySuite.Proofs.Flocq.OverlayCorrectnessGuarded
   ----------------------------------------------------------------------------
   The JCT hypothesis H1 of the OverlayNG headline, restated under the
   guards the JCT lane found necessary and proved; and the headline restated
   at the noded input over the real face extractor.

   `overlay_ng_correct_conditional` (OverlayCorrectness.v) takes as H1

     forall q r, ring_closed r -> ring_simple r ->
       point_in_ring q r <-> geometric_interior_cont q r

   which is false (docs/h1-vacuity/OverlayH1ContQEX.v : overlay_H1_refuted:
   the notch hexagon, a horizontal edge at the ray height).  Ray parity
   also fails on the ring itself (JCT_OnEdgeCounterexample.v) and where the
   ray grazes a vertex (JCT_VertexGrazingCounterexample.v).  So the
   headline is vacuous, and so is its H_bridge (its H1 premise is false).

   `overlay_H1_guarded` adds exactly the guards under which the polygonal
   Jordan seam is proved (JCTEscapeDescentHolds.v : parity_seam_offring_taut,
   packaged as RelateNGJordanTrueRegion.v : taut_seam_at):

     ring guards   ring_taut, ring_core_nodup, no_horizontal_edges,
                   ring_has_minimum_points
     point guards  ring_complement (off the ring), ray_avoids_vertices

   `overlay_H1_guarded_holds` proves it outright.  It is not vacuous: every
   guarded ring has a guarded point on each side
   (`overlay_H1_guarded_nonvacuous`), and a concrete triangle satisfies
   every ring guard (`overlay_H1_guarded_triangle`).

   `overlay_ng_correct_guarded` (§3) is the headline at
   `noded_labeled_graph A B` over the face extractor `extract_faces`: output
   validity is proved from the guard set of `extract_rings_valid_of_guards`;
   the semantic bridge (point_set of the output = boolean_op A B) is a premise
   about this input and is the whole open content.  H1 is NOT a premise: a
   proved Prop as a premise is inert.  `overlay_H1_guarded_holds` stands as
   the JCT fact a future proof of the bridge can use -- only on guarded rings:
   `no_horizontal_edges` excludes every axis-aligned ring, and snapping can
   create horizontal darts
   (SnapRoundingGuardAudit.v : snap_can_introduce_horizontal_dart).

   No Admitted / Axiom / Parameter.  Reals axioms plus Flocq's `classic`
   through the noded_labeled_graph closure; `extract_rings_valid_of_guards`
   adds what its own Print Assumptions lists.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs        Require Import Distance Overlay OverlayGraph.
From NTS.Proofs        Require Import PointInRingTangents PointInRingCorrect JordanCurveSeam.
From NTS.Proofs        Require Import GeneralTriangleSeparation.
From NTS.Proofs        Require Import JCTTautClearance JCTRingCycle JCTHugStep.
From NTS.Proofs        Require Import RelateNGJordanTrueRegion TriangleTautBridge.
From NTS.Proofs        Require Import Dart ExtractFaces FaceTwinAware NoShortFaces EdgeConnectivity
                              HBridgeCoreSlice VertexGeneralPosition.
From NTS.Proofs.Flocq  Require Import HobbyTheorem_b64 OverlayBridge OverlayBridgeUnconditional.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  H1, guarded, and proved.                                               *)
(* -------------------------------------------------------------------------- *)

Definition overlay_H1_guarded : Prop :=
  forall (q : Point) (r : Ring),
    ring_taut r -> ring_core_nodup r -> no_horizontal_edges r ->
    ring_has_minimum_points r ->
    ring_complement r q -> ray_avoids_vertices q r ->
    point_in_ring q r <-> geometric_interior_cont q r.

Theorem overlay_H1_guarded_holds : overlay_H1_guarded.
Proof.
  intros q r Htaut Hnd Hnoh Hmin Hcompl Hrav.
  symmetry.
  exact (taut_seam_at r q Htaut Hnd Hnoh Hmin Hcompl Hrav).
Qed.

(* The guards still leave the old H1's shape: closed and simple. *)
Lemma overlay_H1_guards_imply_closed_simple : forall r : Ring,
  ring_taut r -> ring_core_nodup r -> ring_closed r /\ ring_simple r.
Proof.
  intros r Htaut Hnd. split.
  - exact (ring_core_nodup_closed r Hnd).
  - exact (ring_taut_implies_simple r Htaut).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Non-vacuity.                                                           *)
(* -------------------------------------------------------------------------- *)

(* Every guarded ring has a guarded point inside and one outside, so the
   guarded H1 constrains both directions of the biconditional. *)
Theorem overlay_H1_guarded_nonvacuous : forall r : Ring,
  ring_taut r -> ring_core_nodup r -> no_horizontal_edges r ->
  ring_has_minimum_points r ->
  exists p_in p_out : Point,
    ring_complement r p_in /\ ray_avoids_vertices p_in r /\
    ring_complement r p_out /\ ray_avoids_vertices p_out r /\
    geometric_interior_cont p_in r /\ ~ geometric_interior_cont p_out r.
Proof.
  intros r Htaut Hnd Hnoh Hmin.
  destruct (relateng_jordan_true_region_taut r Htaut Hnd Hnoh Hmin)
    as (h & p_in & p_out & _ & _ & _ & _ & Hc_in & Hc_out & Hr_in & Hr_out
        & Hpir_in & _ & Hpir_out & _ & _).
  exists p_in, p_out.
  split; [exact Hc_in|]. split; [exact Hr_in|].
  split; [exact Hc_out|]. split; [exact Hr_out|].
  split.
  - exact (proj1 (overlay_H1_guarded_holds p_in r Htaut Hnd Hnoh Hmin
                    Hc_in Hr_in) Hpir_in).
  - intro Hgi. apply Hpir_out.
    exact (proj2 (overlay_H1_guarded_holds p_out r Htaut Hnd Hnoh Hmin
                    Hc_out Hr_out) Hgi).
Qed.

(* A concrete ring meets every ring guard: the CCW triangle (0,0) (4,1)
   (1,3), whose vertex heights are pairwise distinct. *)
Theorem overlay_H1_guarded_triangle :
  let r := gtri_ring 0 0 4 1 1 3 in
  ring_taut r /\ ring_core_nodup r /\ no_horizontal_edges r /\
  ring_has_minimum_points r.
Proof.
  assert (Hccw : 0 < gdbl 0 0 4 1 1 3) by (unfold gdbl; lra).
  cbv zeta. repeat split.
  - exact (tri_ring_taut _ _ _ _ _ _ Hccw).
  - exact (tri_core_nodup _ _ _ _ _ _ Hccw).
  - apply tri_no_horizontal_edges; lra.
  - unfold ring_has_minimum_points, gtri_ring. cbn. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The headline, at this input, over the real extractor.                  *)
(*                                                                            *)
(* The first version of this theorem kept H2 and H_bridge quantified over ALL *)
(* topology graphs, over the placeholder `extract` (every result edge in one  *)
(* ring).  Both are false (docs/h1-vacuity/OverlayGuardedVacuityQEX.v): a     *)
(* one-edge graph breaks H2, and the empty graph makes a universal H_bridge   *)
(* deny every point.  Passing it the proved guarded H1 added nothing.         *)
(*                                                                            *)
(* Restated: the noded graph `noded_labeled_graph A B` only, the face         *)
(* extractor `extract_faces`, and the guard set of                            *)
(* `extract_rings_valid_of_guards`.  Validity of the output is then PROVED.   *)
(* The semantic bridge is a premise about this one input; it is the whole     *)
(* open content, and the second conjunct is just that premise.                *)
(* -------------------------------------------------------------------------- *)

Theorem overlay_ng_correct_guarded :
  forall (A B : Geometry) (op : BooleanOp) (p : Point),
    well_noded_darts (result_edges op (noded_labeled_graph A B)) ->
    no_spurs (result_darts op (noded_labeled_graph A B)) ->
    edge_2_connected (result_edges op (noded_labeled_graph A B)) ->
    pairwise_no_proper_cross_twin_aware
      (darts_of (result_edges op (noded_labeled_graph A B))) ->
    no_horizontal_darts
      (darts_of (result_edges op (noded_labeled_graph A B))) ->
    no_foreign_vertex_twin_aware
      (darts_of (result_edges op (noded_labeled_graph A B))) ->
    (* H_bridge (semantic gap), for this input only. *)
    (point_set (extract_faces op (noded_labeled_graph A B)) p <->
     boolean_op op A B p) ->
    valid_geometry (extract_faces op (noded_labeled_graph A B)) /\
    (point_set (extract_faces op (noded_labeled_graph A B)) p <->
     boolean_op op A B p).
Proof.
  intros A B op p Hwn Hns H2ec Hpw Hnh Hnfv H_bridge.
  split; [| exact H_bridge].
  intros poly Hin.
  exact (extract_rings_valid_of_guards op A B Hwn Hns H2ec Hpw Hnh Hnfv poly Hin).
Qed.

Print Assumptions overlay_H1_guarded_holds.
Print Assumptions overlay_H1_guarded_nonvacuous.
Print Assumptions overlay_H1_guarded_triangle.
Print Assumptions overlay_ng_correct_guarded.
