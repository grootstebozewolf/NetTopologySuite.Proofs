(* ============================================================================
   NetTopologySuite.Proofs.Flocq.OverlayCorrectnessGuarded
   ----------------------------------------------------------------------------
   The OverlayNG headline with its JCT hypothesis H1 restated under the
   guards the JCT lane found necessary, and discharged.

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

   `overlay_ng_correct_guarded` is the headline with H1 gone from the
   premises: H_bridge receives the guarded H1 as a proved fact.  What
   stays open is unchanged and now honest:
     - H2       extract is valid on every valid topology graph;
     - H_bridge point_set (extract op g) <-> boolean_op op A B, which can
                use H1 only on guarded rings.  The guards are restrictive:
                `no_horizontal_edges` excludes every axis-aligned ring, and
                snapping can create horizontal darts
                (SnapRoundingGuardAudit.v : snap_can_introduce_horizontal_dart).
   Discharging H_bridge therefore needs either guarded overlay output or a
   half-open-parity H1 that drops the horizontal guard.

   No Admitted / Axiom / Parameter.  Reals axioms plus Flocq's `classic`
   through the noded_labeled_graph closure, as OverlayCorrectness.v.

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
From NTS.Proofs.Flocq  Require Import HobbyTheorem_b64 OverlayBridge.
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
(* §3  The headline, H1 discharged.                                           *)
(* -------------------------------------------------------------------------- *)

Theorem overlay_ng_correct_guarded :
  forall (A B : Geometry) (op : BooleanOp) (p : Point),
    valid_geometry A ->
    valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    (* H2 (DCEL gap), unchanged. *)
    (forall (op' : BooleanOp) (g : TopologyGraph),
       valid_topology_graph g ->
       valid_geometry (extract op' g)) ->
    (* H_bridge (semantic gap): may use H1 only on guarded rings. *)
    (forall (g : TopologyGraph),
       valid_topology_graph g ->
       correct_labels op g A B ->
       valid_geometry (extract op g) ->
       overlay_H1_guarded ->
       (point_set (extract op g) p <-> boolean_op op A B p)) ->
    point_set (extract op (noded_labeled_graph A B)) p <->
    boolean_op op A B p.
Proof.
  intros A B op p _ _ _ H2 H_bridge.
  apply H_bridge.
  - apply valid_topology_graph_noded_labeled_graph.
  - apply correct_labels_all_ops.
  - apply H2. apply valid_topology_graph_noded_labeled_graph.
  - exact overlay_H1_guarded_holds.
Qed.

Print Assumptions overlay_H1_guarded_holds.
Print Assumptions overlay_H1_guarded_nonvacuous.
Print Assumptions overlay_H1_guarded_triangle.
Print Assumptions overlay_ng_correct_guarded.
