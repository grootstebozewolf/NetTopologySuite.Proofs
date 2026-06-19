(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixEllipticArc
   ----------------------------------------------------------------------------
   Esri 300 EllipticArc × line regime→witness selection — chord seed.

   `elliptic_arc_fill` SELECTS (does not compute from geometry) one of the
   witness matrices per `EllipticArcRegime`.  The `*_fill_witness` facts are
   constant; the regime hypothesis is not consumed, and no geometry→matrix
   claim is made.

   Follows the exact pattern of RelateMatrixClothoid.v (and RelateMatrixArcChord.v).

   No `Admitted`, no `Axiom`, no `Parameter`.
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import DE9IM Distance RelateEllipticArc.
Open Scope R_scope.

Inductive EllipticArcRegime : Type :=
| EAR_ChordDisjoint
| EAR_ChordProperCross
| EAR_ChordShare.

Definition elliptic_arc_fill (r : EllipticArcRegime) : IntersectionMatrix :=
  match r with
  | EAR_ChordDisjoint    => eac_matrix_disjoint
  | EAR_ChordProperCross => eac_matrix_point_ii
  | EAR_ChordShare       => eac_matrix_point_ii
  end.

Lemma elliptic_arc_fill_disjoint_eq :
  elliptic_arc_fill EAR_ChordDisjoint = eac_matrix_disjoint.
Proof. reflexivity. Qed.

Lemma elliptic_arc_fill_proper_cross_eq :
  elliptic_arc_fill EAR_ChordProperCross = eac_matrix_point_ii.
Proof. reflexivity. Qed.

Lemma elliptic_arc_fill_share_eq :
  elliptic_arc_fill EAR_ChordShare = eac_matrix_point_ii.
Proof. reflexivity. Qed.

Definition classify_elliptic_arc (c : EllipticArcChord) (P Q : Point)
    (r : EllipticArcRegime) : Prop :=
  match r with
  | EAR_ChordDisjoint    => elliptic_arc_chord_rejected c P Q
  | EAR_ChordProperCross => elliptic_arc_chord_proper_cross c P Q
  | EAR_ChordShare       => elliptic_arc_chord_share c P Q
  end.

(* Constant witness facts: the selected witness satisfies the regime's
   predicate.  No geometry hypothesis; no geometry→matrix claim. *)
Theorem elliptic_arc_fill_disjoint_witness :
  im_disjoint (elliptic_arc_fill EAR_ChordDisjoint).
Proof.
  rewrite elliptic_arc_fill_disjoint_eq. exact eac_matrix_disjoint_witness.
Qed.

Theorem elliptic_arc_fill_proper_cross_witness :
  im_crosses (elliptic_arc_fill EAR_ChordProperCross) /\
  im_intersects (elliptic_arc_fill EAR_ChordProperCross).
Proof.
  rewrite elliptic_arc_fill_proper_cross_eq.
  split; [exact eac_matrix_point_ii_crosses | exact eac_matrix_point_ii_intersects].
Qed.

Theorem elliptic_arc_fill_share_witness :
  im_intersects (elliptic_arc_fill EAR_ChordShare).
Proof.
  rewrite elliptic_arc_fill_share_eq. exact eac_matrix_point_ii_intersects.
Qed.

Print Assumptions elliptic_arc_fill_disjoint_witness.
Print Assumptions elliptic_arc_fill_proper_cross_witness.
Print Assumptions elliptic_arc_fill_share_witness.
