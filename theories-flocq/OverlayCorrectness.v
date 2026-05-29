(* ============================================================================
   NetTopologySuite.Proofs.Flocq.OverlayCorrectness
   ----------------------------------------------------------------------------
   Phase 3 Milestone 5 Session 15: overlay_ng_correct_conditional -- the
   headline correctness theorem for the OverlayNG pipeline, stated as a
   Qed-closed conditional theorem mirroring `hobby_theorem_4_1_conditional`
   (Phase 2's Link 1 conditional headline).

   The theorem says: given valid input geometries A and B, a fully-intersected
   noded arrangement, and three named structural hypotheses encapsulating the
   thesis-shaped gaps (JCT for polygons + DCEL ring-assembly correctness + a
   semantic bridge from edge-level to point-set-level), the OverlayNG output's
   point-set agrees with the boolean-op semantics on A and B.

   The structural composition proven Qed-closed in this file:

     - valid_topology_graph_noded_labeled_graph (M4, Qed):
         the noded labelled graph is valid.
     - correct_labels_all_ops (M5 S4-S7, Qed):
         every edge's label correctly indicates op-membership.
     - H1 (JCT gap, named):
         point_in_ring agrees with geometric interior on valid rings.
     - H2 (DCEL gap, named):
         extract assembles valid polygons.
     - H_bridge (consolidated semantic gap, named):
         on any valid + correctly-labeled graph with valid extract output,
         point_set (extract op g) matches boolean_op op A B (under H1).

   THREE named gaps, all stated in Coq (H1 + H2 + H_bridge as Section-local
   hypotheses), zero Admitted in the body, zero Axiom / Parameter pulls.

   ----------------------------------------------------------------------------
   H1 framing decision (per docs/m5-s15-conditional-headline-prompt.md).

   `geometric_interior` does NOT exist in the corpus (no JCT toolkit).  The
   Section opens a single opaque `Variable geometric_interior : Point ->
   Ring -> Prop`.  When the Section closes, every Section-bound theorem
   becomes universally quantified over this Variable -- the consumer
   instantiates with whatever topological-interior Prop they have on hand.

   Section-bound Variable is NOT an Axiom / Parameter / Admit; the corpus's
   epistemic invariant is preserved.  Print Assumptions on the closed
   theorem shows the README-allowlist plus the Flocq classical-reals
   transitive pull (the snap layer's Classical_Prop.classic via
   noded_labeled_graph's definitional closure).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From NTS.Proofs        Require Import Distance.
From NTS.Proofs        Require Import Overlay.
From NTS.Proofs        Require Import OverlayGraph.
From NTS.Proofs.Flocq  Require Import HobbyTheorem_b64.
From NTS.Proofs.Flocq  Require Import OverlayBridge.

(* -------------------------------------------------------------------------- *)
(* §1  The conditional headline.                                              *)
(*                                                                            *)
(* Section-scoped to keep the JCT-shaped Variable `geometric_interior` local. *)
(* On Section close, the theorem's signature carries the Variable as an       *)
(* additional `forall geometric_interior, ...` quantification.                 *)
(* -------------------------------------------------------------------------- *)

Section OverlayCorrectness.

  (* JCT gap (H1 input): the topological-interior predicate.  Opaque inside
     this Section; concrete consumers instantiate it from their JCT toolkit. *)
  Variable geometric_interior : Point -> Ring -> Prop.

  (* ------------------------------------------------------------------------ *)
  (* §1.1  The headline theorem.                                              *)
  (*                                                                          *)
  (* THREE named hypotheses:                                                  *)
  (*   H1 (JCT): point_in_ring captures geometric interior on valid rings.   *)
  (*   H2 (DCEL valid polygons): extract assembles valid polygons.          *)
  (*   H_bridge (semantic): point_set of extract agrees with boolean_op,    *)
  (*     given the above + correct labels + valid graph.                    *)
  (*                                                                          *)
  (* The proof composes the two M4/M5 Qed-closed structural pieces with     *)
  (* the three hypotheses, instantiating H_bridge on the concrete graph     *)
  (* `noded_labeled_graph A B`.                                              *)
  (* ------------------------------------------------------------------------ *)

  Theorem overlay_ng_correct_conditional :
    forall (A B : Geometry) (op : BooleanOp) (p : Point),
      valid_geometry A ->
      valid_geometry B ->
      fully_intersected (noded_segments A B) ->
      (* H1 (JCT gap): point_in_ring captures topological interior on
         valid rings.  Stand-in for `point_in_ring_correct` in the audit
         doc; registered as deferred via the audit doc's §4.2 (no Coq
         deferred-proof entry since the JCT toolkit is absent). *)
      (forall (q : Point) (r : Ring),
         ring_closed r -> ring_simple r ->
         point_in_ring q r <-> geometric_interior q r) ->
      (* H2 (DCEL gap): for any valid topology graph, extract assembles
         a valid geometry.  Stand-in for the future `extract_rings_valid`
         theorem (audit doc §4.3 / §5.2). *)
      (forall (op' : BooleanOp) (g : TopologyGraph),
         valid_topology_graph g ->
         valid_geometry (extract op' g)) ->
      (* H_bridge (semantic gap): on any valid + correctly-labeled graph
         whose extract is valid, point_set (extract op g) matches
         boolean_op op A B under the JCT hypothesis.  This consolidated
         hypothesis encapsulates the load-bearing semantic claim that
         DCEL face-traversal + JCT for polygons jointly discharge. *)
      (forall (g : TopologyGraph),
         valid_topology_graph g ->
         correct_labels op g A B ->
         valid_geometry (extract op g) ->
         (forall (q : Point) (r : Ring),
            ring_closed r -> ring_simple r ->
            point_in_ring q r <-> geometric_interior q r) ->
         (point_set (extract op g) p <-> boolean_op op A B p)) ->
      point_set (extract op (noded_labeled_graph A B)) p <->
      boolean_op op A B p.
  Proof.
    intros A B op p _ _ _ H1 H2 H_bridge.
    apply H_bridge.
    - apply valid_topology_graph_noded_labeled_graph.
    - apply correct_labels_all_ops.
    - apply H2. apply valid_topology_graph_noded_labeled_graph.
    - exact H1.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* §1.2  Option B corollary: one-direction forward implication.             *)
  (*                                                                          *)
  (* Two-line derivation from the iff.  Useful for downstream consumers       *)
  (* that need only the forward direction (point in OverlayNG output implies  *)
  (* point in boolean-op result) without the converse.                         *)
  (* ------------------------------------------------------------------------ *)

  Corollary overlay_ng_correct_forward :
    forall (A B : Geometry) (op : BooleanOp) (p : Point),
      valid_geometry A ->
      valid_geometry B ->
      fully_intersected (noded_segments A B) ->
      (forall (q : Point) (r : Ring),
         ring_closed r -> ring_simple r ->
         point_in_ring q r <-> geometric_interior q r) ->
      (forall (op' : BooleanOp) (g : TopologyGraph),
         valid_topology_graph g ->
         valid_geometry (extract op' g)) ->
      (forall (g : TopologyGraph),
         valid_topology_graph g ->
         correct_labels op g A B ->
         valid_geometry (extract op g) ->
         (forall (q : Point) (r : Ring),
            ring_closed r -> ring_simple r ->
            point_in_ring q r <-> geometric_interior q r) ->
         (point_set (extract op g) p <-> boolean_op op A B p)) ->
      point_set (extract op (noded_labeled_graph A B)) p ->
      boolean_op op A B p.
  Proof.
    intros A B op p HA HB Hfi H1 H2 H_bridge Hin.
    apply (overlay_ng_correct_conditional A B op p HA HB Hfi H1 H2 H_bridge).
    exact Hin.
  Qed.

  (* Symmetric backward corollary. *)
  Corollary overlay_ng_correct_backward :
    forall (A B : Geometry) (op : BooleanOp) (p : Point),
      valid_geometry A ->
      valid_geometry B ->
      fully_intersected (noded_segments A B) ->
      (forall (q : Point) (r : Ring),
         ring_closed r -> ring_simple r ->
         point_in_ring q r <-> geometric_interior q r) ->
      (forall (op' : BooleanOp) (g : TopologyGraph),
         valid_topology_graph g ->
         valid_geometry (extract op' g)) ->
      (forall (g : TopologyGraph),
         valid_topology_graph g ->
         correct_labels op g A B ->
         valid_geometry (extract op g) ->
         (forall (q : Point) (r : Ring),
            ring_closed r -> ring_simple r ->
            point_in_ring q r <-> geometric_interior q r) ->
         (point_set (extract op g) p <-> boolean_op op A B p)) ->
      boolean_op op A B p ->
      point_set (extract op (noded_labeled_graph A B)) p.
  Proof.
    intros A B op p HA HB Hfi H1 H2 H_bridge Hin.
    apply (overlay_ng_correct_conditional A B op p HA HB Hfi H1 H2 H_bridge).
    exact Hin.
  Qed.

End OverlayCorrectness.

(* -------------------------------------------------------------------------- *)
(* §2  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions overlay_ng_correct_conditional.
Print Assumptions overlay_ng_correct_forward.
Print Assumptions overlay_ng_correct_backward.
