(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixBezier3
   ----------------------------------------------------------------------------
   Esri 300 Bezier3Curve × line regime→witness — chord seed.

   `bezier3_fill` SELECTS one of the witness matrices per `Bezier3Regime`.
   Constant facts only; no geometry→matrix claim.

   Mirrors RelateMatrixClothoid.v exactly in shape.

   No `Admitted`, no `Axiom`, no `Parameter`.
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import DE9IM Distance RelateBezier3.
Open Scope R_scope.

Inductive Bezier3Regime : Type :=
| B3R_ChordDisjoint
| B3R_ChordProperCross
| B3R_ChordShare.

Definition bezier3_fill (r : Bezier3Regime) : IntersectionMatrix :=
  match r with
  | B3R_ChordDisjoint    => b3c_matrix_disjoint
  | B3R_ChordProperCross => b3c_matrix_point_ii
  | B3R_ChordShare       => b3c_matrix_point_ii
  end.

Lemma bezier3_fill_disjoint_eq :
  bezier3_fill B3R_ChordDisjoint = b3c_matrix_disjoint.
Proof. reflexivity. Qed.

Lemma bezier3_fill_proper_cross_eq :
  bezier3_fill B3R_ChordProperCross = b3c_matrix_point_ii.
Proof. reflexivity. Qed.

Lemma bezier3_fill_share_eq :
  bezier3_fill B3R_ChordShare = b3c_matrix_point_ii.
Proof. reflexivity. Qed.

Definition classify_bezier3 (c : Bezier3Chord) (P Q : Point)
    (r : Bezier3Regime) : Prop :=
  match r with
  | B3R_ChordDisjoint    => bezier3_chord_rejected c P Q
  | B3R_ChordProperCross => bezier3_chord_proper_cross c P Q
  | B3R_ChordShare       => bezier3_chord_share c P Q
  end.

Theorem bezier3_fill_disjoint_witness :
  im_disjoint (bezier3_fill B3R_ChordDisjoint).
Proof.
  rewrite bezier3_fill_disjoint_eq. exact b3c_matrix_disjoint_witness.
Qed.

Theorem bezier3_fill_proper_cross_witness :
  im_crosses (bezier3_fill B3R_ChordProperCross) /\
  im_intersects (bezier3_fill B3R_ChordProperCross).
Proof.
  rewrite bezier3_fill_proper_cross_eq.
  split; [exact b3c_matrix_point_ii_crosses | exact b3c_matrix_point_ii_intersects].
Qed.

Theorem bezier3_fill_share_witness :
  im_intersects (bezier3_fill B3R_ChordShare).
Proof.
  rewrite bezier3_fill_share_eq. exact b3c_matrix_point_ii_intersects.
Qed.

Print Assumptions bezier3_fill_disjoint_witness.
Print Assumptions bezier3_fill_proper_cross_witness.
Print Assumptions bezier3_fill_share_witness.
