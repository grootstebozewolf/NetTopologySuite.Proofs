(* ============================================================================
   NetTopologySuite.Proofs.ArcSBiarcWitness
   ----------------------------------------------------------------------------
   Rung 2 of the directed-approximation ladder
   (docs/directed-approximation-2026-11.md): a concrete S-type biarc whose
   chord polygon is NEITHER an over- nor an under-approximation.

   The biarc: two semicircles meeting at (2,0) with the same vertical tangent
   (G1), curving in opposite senses.
       a1 : (0,0) -> (1,-1) -> (2,0)   centre (1,0), bulges BELOW the chord
       a2 : (2,0) -> (3, 1) -> (4,0)   centre (3,0), bulges ABOVE the chord
   The region R lies above the curve, with chord polygon P = [0,4] x [0,2].
   Relative to R, a1 bulges OUT (its segment is added to P) and a2 bulges IN
   (its segment is carved out of P): R = (P u seg a1) \ seg a2.

   That decomposition is ASSUMED (rung 4); what is proved is the arithmetic:
   both arcs are valid, they bulge on opposite sides of their chords, and the
   mixed-direction witness points exist, so `chord_neither_of_mixed` applies.
   No Axiom / Admitted.
   ========================================================================== *)
From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient
  ArcControlTriangleInSegment DirectedApprox.
Open Scope R_scope.

Definition a1 : CircularArc :=
  mkCircularArc (mkPoint 0 0) (mkPoint 1 (-1)) (mkPoint 2 0).
Definition a2 : CircularArc :=
  mkCircularArc (mkPoint 2 0) (mkPoint 3 1) (mkPoint 4 0).

Lemma a1_valid : valid_arc a1.
Proof. unfold valid_arc, a1; simpl; lra. Qed.
Lemma a2_valid : valid_arc a2.
Proof. unfold valid_arc, a2; simpl; lra. Qed.

(* They share the join node. *)
Lemma sbiarc_join : arc_end a1 = arc_start a2.
Proof. reflexivity. Qed.

Lemma a1_center : arc_center a1 = mkPoint 1 0.
Proof. unfold arc_center, a1; simpl. f_equal; field. Qed.
Lemma a2_center : arc_center a2 = mkPoint 3 0.
Proof. unfold arc_center, a2; simpl. f_equal; field. Qed.

(* Opposite bulge senses: mids sit on opposite sides of their chords. *)
Lemma sbiarc_opposite_senses :
  arc_side_chord a1 (arc_mid a1) * arc_side_chord a2 (arc_mid a2) < 0.
Proof. unfold arc_side_chord, cross_R_pt, a1, a2; simpl; lra. Qed.

(* Model sets. *)
Definition P_poly (q : Point) : Prop := 0 <= px q <= 4 /\ 0 <= py q <= 2.
Definition O_seg (q : Point) : Prop := in_circular_segment a1 q.
Definition I_seg (q : Point) : Prop := in_circular_segment a2 q.

Definition o_wit : Point := mkPoint 1 (-1/2).
Definition i_wit : Point := mkPoint 3 (1/2).

Lemma o_wit_in_O : O_seg o_wit.
Proof.
  unfold O_seg, in_circular_segment, arc_interior_side, arc_side_chord,
    cross_R_pt, dist_sq, o_wit; rewrite a1_center; unfold a1; simpl; split; lra.
Qed.

Lemma o_wit_not_P : ~ P_poly o_wit.
Proof. unfold P_poly, o_wit; simpl; lra. Qed.

Lemma o_wit_not_I : ~ I_seg o_wit.
Proof.
  unfold I_seg, in_circular_segment, arc_interior_side, arc_side_chord,
    cross_R_pt, o_wit, a2; simpl; intros [H _]; lra.
Qed.

Lemma i_wit_in_I : I_seg i_wit.
Proof.
  unfold I_seg, in_circular_segment, arc_interior_side, arc_side_chord,
    cross_R_pt, dist_sq, i_wit; rewrite a2_center; unfold a2; simpl; split; lra.
Qed.

Lemma i_wit_in_P : P_poly i_wit.
Proof. unfold P_poly, i_wit; simpl; lra. Qed.

(* HEADLINE: the S-biarc's chord polygon is neither over nor under. *)
Theorem sbiarc_chord_neither :
  ~ over_on (fun _ => True)
      (fun x => (P_poly x \/ O_seg x) /\ ~ I_seg x) P_poly /\
  ~ under_on (fun _ => True)
      (fun x => (P_poly x \/ O_seg x) /\ ~ I_seg x) P_poly.
Proof.
  apply chord_neither_of_mixed.
  - exists o_wit. exact (conj o_wit_in_O (conj o_wit_not_P o_wit_not_I)).
  - exists i_wit. split; [exact i_wit_in_I | exact i_wit_in_P].
Qed.

Print Assumptions sbiarc_chord_neither.
