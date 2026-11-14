(* ============================================================================
   docs/h1-vacuity/OverlayH1ContQEX.v  --  hunt probe (QEX), not a product module
   ----------------------------------------------------------------------------
   `overlay_ng_correct_conditional` (theories-flocq/OverlayCorrectness.v) takes
   as H1, verbatim:

     forall (q : Point) (r : Ring),
       ring_closed r -> ring_simple r ->
       point_in_ring q r <-> geometric_interior_cont q r

   The re-pointing onto `geometric_interior_cont` (PR #81 follow-up) cured the
   first vacuity (`geometric_interior_stdlib` is identically false, see
   VacuityCheck.v), and the source header now calls H1 "an honest,
   satisfiable (and still-undischarged) JCT gap".  It is not satisfiable:
   H1 carries none of the guards the JCT lane later found necessary
   (`no_horizontal_edge_at`, `ray_avoids_vertices`, off-ring).  The notch
   hexagon of `JCT_HorizontalEdgeCounterexample.v` is closed and simple, and
   ray parity says "inside" at an exterior point.  So H1 is false, and the
   headline is vacuous a second time.

   `overlay_ng_correct_conditional_vacuous` restates this against the
   theorem's own premise list, so the probe breaks if the statement changes.

   SUMMARY: bug — H1 of overlay_ng_correct_conditional is refuted (Qed).
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import JCT_HorizontalEdgeCounterexample.
From NTS.Proofs Require Import OverlayGraph.
From NTS.Proofs.Flocq Require Import HobbyTheorem_b64 OverlayBridge OverlayCorrectness.

Definition overlay_H1 : Prop :=
  forall (q : Point) (r : Ring),
    ring_closed r -> ring_simple r ->
    point_in_ring q r <-> geometric_interior_cont q r.

Theorem overlay_H1_refuted : ~ overlay_H1.
Proof.
  intros H.
  destruct notch_refutes_parity_without_guard as [Hin Hnot].
  apply Hnot.
  apply (proj1 (H pext notch notch_ring_closed notch_ring_simple)).
  exact Hin.
Qed.

(* Every instantiation of the headline's premise list is contradictory: the
   conclusion holds of every A B op p only because nothing satisfies H1. *)
Theorem overlay_ng_correct_conditional_vacuous :
  forall (A B : Geometry) (op : BooleanOp) (p : Point),
    valid_geometry A -> valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    (forall (q : Point) (r : Ring),
       ring_closed r -> ring_simple r ->
       point_in_ring q r <-> geometric_interior_cont q r) ->
    False.
Proof.
  intros A B op p _ _ _ H1. exact (overlay_H1_refuted H1).
Qed.

(* The same premise, checked to be the one the headline consumes: the
   headline applied to it type-checks (a statement drift breaks this). *)
Definition overlay_headline_consumes_H1 :=
  fun A B op p HA HB Hfi (H1 : overlay_H1) H2 Hb =>
    overlay_ng_correct_conditional A B op p HA HB Hfi H1 H2 Hb.

Print Assumptions overlay_H1_refuted.
Print Assumptions overlay_ng_correct_conditional_vacuous.
