(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixClothoid
   ----------------------------------------------------------------------------
   Issue #67 session 10b (S10b): clothoid×line matrix fill — chord seed.

   Sixth computed fill API: `clothoid_fill` reusing S10b witness matrices.

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

Theorem clothoid_fill_disjoint_sound :
  forall (c : ClothoidChord) (P Q : Point),
    clothoid_chord_rejected c P Q ->
    im_disjoint (clothoid_fill CLR_ChordDisjoint).
Proof.
  intros c P Q H.
  rewrite clothoid_fill_disjoint_eq.
  exact (clothoid_chord_rejected_disjoint_sound c P Q H).
Qed.

Theorem clothoid_fill_proper_cross_sound :
  forall (c : ClothoidChord) (P Q : Point),
    clothoid_chord_proper_cross c P Q ->
    im_crosses (clothoid_fill CLR_ChordProperCross) /\
    im_intersects (clothoid_fill CLR_ChordProperCross).
Proof.
  intros c P Q H.
  rewrite clothoid_fill_proper_cross_eq.
  exact (clothoid_chord_proper_cross_sound c P Q H).
Qed.

Theorem clothoid_fill_share_sound :
  forall (c : ClothoidChord) (P Q : Point),
    clothoid_chord_share c P Q ->
    im_intersects (clothoid_fill CLR_ChordShare).
Proof.
  intros c P Q H.
  rewrite clothoid_fill_share_eq.
  exact (clothoid_chord_share_intersects_sound c P Q H).
Qed.

Theorem classify_clothoid_disjoint_fill_sound :
  forall (c : ClothoidChord) (P Q : Point),
    classify_clothoid c P Q CLR_ChordDisjoint ->
    im_disjoint (clothoid_fill CLR_ChordDisjoint).
Proof.
  intros c P Q H. unfold classify_clothoid in H.
  exact (clothoid_fill_disjoint_sound c P Q H).
Qed.

Theorem classify_clothoid_proper_cross_fill_sound :
  forall (c : ClothoidChord) (P Q : Point),
    classify_clothoid c P Q CLR_ChordProperCross ->
    im_crosses (clothoid_fill CLR_ChordProperCross) /\
    im_intersects (clothoid_fill CLR_ChordProperCross).
Proof.
  intros c P Q H. unfold classify_clothoid in H.
  exact (clothoid_fill_proper_cross_sound c P Q H).
Qed.

Theorem classify_clothoid_share_fill_sound :
  forall (c : ClothoidChord) (P Q : Point),
    classify_clothoid c P Q CLR_ChordShare ->
    im_intersects (clothoid_fill CLR_ChordShare).
Proof.
  intros c P Q H. unfold classify_clothoid in H.
  exact (clothoid_fill_share_sound c P Q H).
Qed.

Print Assumptions clothoid_fill_proper_cross_sound.