(* ============================================================================
   docs/h1-vacuity/OverlayGuardedVacuityQEX.v  --  hunt probe (QEX), not a product module
   ----------------------------------------------------------------------------
   Review of PR #1024: the overlay headlines stay vacuous even with H1 fixed.

   1. H2 of `overlay_ng_correct_conditional` (and of the first
      `overlay_ng_correct_guarded`) is false.  `valid_topology_graph` only asks
      that edge endpoints are listed vertices; a one-edge graph labelled
      in_left extracts, under Union, to the 2-point ring [p; q], which fails
      `ring_has_minimum_points` (`overlay_H2_refuted`).

   2. A semantic bridge quantified over ALL graphs is false whenever the
      result is non-empty: the empty graph is valid, has vacuously correct
      labels and extracts to the empty (valid) geometry, whose point set is
      empty (`overlay_universal_bridge_forces_empty`).  An extra premise that
      holds -- such as the proved guarded H1 -- changes nothing.

   The fix (theories-flocq/OverlayCorrectnessGuarded.v): state the headline
   at `g := noded_labeled_graph A B` only, over the real extractor
   `extract_faces`, with validity from the guard set.

   SUMMARY: bug — overlay H2 refuted; universal H_bridge forces an empty result (Qed).
   Credit: counterexample shapes from the PR #1024 review.
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals List Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph PointInRingTangents JordanCurveSeam.
From NTS.Proofs.Flocq Require Import HobbyTheorem_b64 OverlayBridge OverlayCorrectness.
Import ListNotations.
Local Open Scope R_scope.

Definition g1 : TopologyGraph :=
  mkTopologyGraph [mkPoint 0 0; mkPoint 1 0]
                  [(mkPoint 0 0, mkPoint 1 0, mkEdgeLabel true false)].

Theorem overlay_H2_refuted :
  ~ (forall op' g, valid_topology_graph g -> valid_geometry (extract op' g)).
Proof.
  intro H2.
  assert (Hv : valid_topology_graph g1).
  { intros p q l [Heq | []]. inversion Heq; subst. cbn. auto. }
  pose proof (H2 Union g1 Hv) as Hp. unfold valid_geometry in Hp. cbn in Hp.
  destruct (Hp _ (or_introl eq_refl)) as (_ & _ & Hmin & _).
  unfold ring_has_minimum_points in Hmin. cbn in Hmin. lia.
Qed.

(* `overlay_ng_correct_conditional` takes exactly this H2 (its fifth
   premise), so it is vacuous on H2 alone, whatever H1 says. *)
Theorem overlay_ng_correct_conditional_vacuous_H2 :
  forall (A B : Geometry) (op : BooleanOp) (p : Point),
    valid_geometry A -> valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    (forall (q : Point) (r : Ring),
       ring_closed r -> ring_simple r ->
       point_in_ring q r <-> geometric_interior_cont q r) ->
    (forall (op' : BooleanOp) (g : TopologyGraph),
       valid_topology_graph g -> valid_geometry (extract op' g)) ->
    False.
Proof. intros A B op p _ _ _ _ H2. exact (overlay_H2_refuted H2). Qed.

Theorem overlay_universal_bridge_forces_empty :
  forall (A B : Geometry) (op : BooleanOp) (p : Point) (Extra : Prop),
    Extra ->
    (forall g, valid_topology_graph g -> correct_labels op g A B ->
       valid_geometry (extract op g) -> Extra ->
       (point_set (extract op g) p <-> boolean_op op A B p)) ->
    ~ boolean_op op A B p.
Proof.
  intros A B op p Extra HE Hb Hp.
  pose proof (Hb empty_graph valid_topology_graph_empty) as H.
  rewrite extract_empty_graph in H.
  destruct H as [_ Hback].
  - intros ? ? ? Hin. cbn in Hin. destruct Hin.
  - intros ? [].
  - exact HE.
  - destruct (Hback Hp) as (? & [] & _).
Qed.

Print Assumptions overlay_H2_refuted.
Print Assumptions overlay_universal_bridge_forces_empty.
