(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixClothoid
   ----------------------------------------------------------------------------
   Issue #67 session 10b (S10b): clothoid×line regime→witness — chord seed.

   `clothoid_fill` SELECTS (does not compute from geometry) one of the S10b
   witness matrices per `ClothoidRegime`.  The `*_fill_witness` facts are
   constant; the regime hypothesis is not consumed, and no geometry→matrix
   claim is made.

   No `Admitted`, no `Axiom`, no `Parameter`.
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import DE9IM Distance RelateClothoid.
Open Scope R_scope.

Inductive ClothoidRegime : Type :=
| CLR_ChordDisjoint
| CLR_ChordProperCross
| CLR_ChordShare.

Definition clothoid_fill (r : ClothoidRegime) : IntersectionMatrix :=
  match r with
  | CLR_ChordDisjoint    => cl_matrix_disjoint
  | CLR_ChordProperCross => cl_matrix_point_ii
  | CLR_ChordShare       => cl_matrix_point_ii
  end.

Lemma clothoid_fill_disjoint_eq :
  clothoid_fill CLR_ChordDisjoint = cl_matrix_disjoint.
Proof. reflexivity. Qed.

Lemma clothoid_fill_proper_cross_eq :
  clothoid_fill CLR_ChordProperCross = cl_matrix_point_ii.
Proof. reflexivity. Qed.

Lemma clothoid_fill_share_eq :
  clothoid_fill CLR_ChordShare = cl_matrix_point_ii.
Proof. reflexivity. Qed.

Definition classify_clothoid (c : ClothoidChord) (P Q : Point)
    (r : ClothoidRegime) : Prop :=
  match r with
  | CLR_ChordDisjoint    => clothoid_chord_rejected c P Q
  | CLR_ChordProperCross => clothoid_chord_proper_cross c P Q
  | CLR_ChordShare       => clothoid_chord_share c P Q
  end.

(* Constant witness facts: the selected witness satisfies the regime's
   predicate.  No geometry hypothesis; no geometry→matrix claim. *)
Theorem clothoid_fill_disjoint_witness :
  im_disjoint (clothoid_fill CLR_ChordDisjoint).
Proof.
  rewrite clothoid_fill_disjoint_eq. exact cl_matrix_disjoint_witness.
Qed.

Theorem clothoid_fill_proper_cross_witness :
  im_crosses (clothoid_fill CLR_ChordProperCross) /\
  im_intersects (clothoid_fill CLR_ChordProperCross).
Proof.
  rewrite clothoid_fill_proper_cross_eq.
  split; [exact cl_matrix_point_ii_crosses | exact cl_matrix_point_ii_intersects].
Qed.

Theorem clothoid_fill_share_witness :
  im_intersects (clothoid_fill CLR_ChordShare).
Proof.
  rewrite clothoid_fill_share_eq. exact cl_matrix_point_ii_intersects.
Qed.

Print Assumptions clothoid_fill_disjoint_witness.
Print Assumptions clothoid_fill_proper_cross_witness.
Print Assumptions clothoid_fill_share_witness.