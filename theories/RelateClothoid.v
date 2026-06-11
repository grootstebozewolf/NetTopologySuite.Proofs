(* ============================================================================
   NetTopologySuite.Proofs.RelateClothoid
   ----------------------------------------------------------------------------
   Issue #67 session 10b (S10b): clothoid×line DE-9IM soundness — chord seed.

   Minimal clothoid relate carrier: a G¹ Hermite clothoid transition is
   approximated by its chord (`cc_start`–`cc_end`) for DE-9IM witness soundness,
   mirroring S10's Option-B chord path.  Solver well-posedness on the monotone
   branch re-exports `ClothoidResidual.clothoid_residual_unique_root`.

   Delivers:

     - `ClothoidChord` + chord-as-segment regime predicates
     - Canonical witness matrices (S2 `ll_matrix_*` reuse)
     - `clothoid_L_unique_on_branch` — conditional Halley/L uniqueness link

   Honest scoping: no `ClothoidSegment` geometry type or Flocq intersection
   yet; full clothoid-clothoid relate is S11+.  Matrix fill via
   `RelateMatrixClothoid.v`.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance Segment Intersect ClothoidResidual
  RelateLineLine.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Minimal clothoid chord carrier.                                            *)
(* -------------------------------------------------------------------------- *)

Record ClothoidChord : Type := mkClothoidChord {
  cc_start : Point;
  cc_end   : Point
}.

Definition clothoid_chord_proper_cross (c : ClothoidChord) (P Q : Point) : Prop :=
  segments_proper_cross (cc_start c) (cc_end c) P Q.

Definition clothoid_chord_rejected (c : ClothoidChord) (P Q : Point) : Prop :=
  segments_rejected (cc_start c) (cc_end c) P Q.

Definition clothoid_chord_share (c : ClothoidChord) (P Q : Point) : Prop :=
  segments_share (cc_start c) (cc_end c) P Q.

(* -------------------------------------------------------------------------- *)
(* Witness matrices (S2 reuse).                                               *)
(* -------------------------------------------------------------------------- *)

Definition cl_matrix_disjoint : IntersectionMatrix := ll_matrix_disjoint.
Definition cl_matrix_point_ii : IntersectionMatrix := ll_matrix_point_ii.

Lemma cl_matrix_disjoint_witness :
  im_disjoint cl_matrix_disjoint.
Proof.
  unfold cl_matrix_disjoint. exact ll_matrix_disjoint_witness.
Qed.

Lemma cl_matrix_point_ii_intersects :
  im_intersects cl_matrix_point_ii.
Proof.
  unfold cl_matrix_point_ii. exact ll_matrix_point_ii_intersects.
Qed.

(* -------------------------------------------------------------------------- *)
(* Chord-path DE-9IM soundness (S2 delegate).                                 *)
(* -------------------------------------------------------------------------- *)

Theorem clothoid_chord_proper_cross_sound :
  forall (c : ClothoidChord) (P Q : Point),
    clothoid_chord_proper_cross c P Q ->
    im_crosses cl_matrix_point_ii /\
    im_intersects cl_matrix_point_ii.
Proof.
  intros c P Q H.
  unfold clothoid_chord_proper_cross, cl_matrix_point_ii in *.
  exact (line_line_proper_cross_sound (cc_start c) (cc_end c) P Q H).
Qed.

Theorem clothoid_chord_rejected_disjoint_sound :
  forall (c : ClothoidChord) (P Q : Point),
    clothoid_chord_rejected c P Q ->
    im_disjoint cl_matrix_disjoint.
Proof.
  intros c P Q Hrej.
  unfold clothoid_chord_rejected, cl_matrix_disjoint in *.
  destruct (line_line_rejection_disjoint_sound (cc_start c) (cc_end c) P Q Hrej) as [Hdisj _].
  exact Hdisj.
Qed.

Theorem clothoid_chord_share_intersects_sound :
  forall (c : ClothoidChord) (P Q : Point),
    clothoid_chord_share c P Q ->
    im_intersects cl_matrix_point_ii.
Proof.
  intros c P Q Hshare.
  unfold clothoid_chord_share, cl_matrix_point_ii in *.
  exact (line_line_share_intersects_sound (cc_start c) (cc_end c) P Q Hshare).
Qed.

(* -------------------------------------------------------------------------- *)
(* Solver well-posedness link (conditional, from ClothoidResidual).           *)
(* -------------------------------------------------------------------------- *)

Theorem clothoid_L_unique_on_branch :
  forall (f : R -> R) (f' : R -> R) (kappa : R),
    (forall L : R, derivable_pt_lim f L (f' L)) ->
    (forall L : R, 0 < L -> Rabs (kappa * L) <= PI -> 0 < f' L) ->
    (forall a b : R,
       a < b ->
       (forall c : R, a <= c <= b -> derivable_pt_lim f c (f' c)) ->
       exists c : R, f b - f a = f' c * (b - a) /\ a < c < b) ->
    forall L1 L2 : R,
      0 < L1 -> 0 < L2 ->
      Rabs (kappa * L1) <= PI -> Rabs (kappa * L2) <= PI ->
      f L1 = 0 -> f L2 = 0 ->
      L1 = L2.
Proof.
  intros f f' kappa Hderiv Hfpos Hmvt L1 L2 HL1 HL2 Hb1 Hb2 Hf1 Hf2.
  exact (clothoid_residual_unique_root f f' kappa Hderiv Hfpos Hmvt
           L1 L2 HL1 HL2 Hb1 Hb2 Hf1 Hf2).
Qed.

Lemma clothoid_chord_rejected_not_share :
  forall (c : ClothoidChord) (P Q : Point),
    clothoid_chord_rejected c P Q ->
    ~ clothoid_chord_share c P Q.
Proof.
  intros c P Q Hrej Hshare.
  unfold clothoid_chord_rejected, clothoid_chord_share in *.
  destruct (line_line_rejection_disjoint_sound (cc_start c) (cc_end c) P Q Hrej) as [_ Hnoshare].
  exact (Hnoshare Hshare).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions clothoid_chord_proper_cross_sound.
Print Assumptions clothoid_L_unique_on_branch.