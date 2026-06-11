(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixLineLine
   ----------------------------------------------------------------------------
   Issue #67 session 8 (S8): line×line matrix fill — guarded segment pairs.

   Second computed DE-9IM matrix-fill API in the Relate arc: a regime-indexed
   function `line_pair_fill` whose outputs equal the S2 witness matrices from
   `RelateLineLine.v`.  Classification remains Prop-level on segment geometry;
   WKT→matrix computation and Romanschek paper matrices are oracle pins (S3),
   not fill targets yet.

   Delivers:

     - `LinePairRegime` + `line_pair_fill`
     - `classify_line_pair` linking regimes to S2 geometry guards
     - Fill = witness equalities
     - Compute-path soundness (rewrite to S2 predicate lemmas)
     - Mutual-exclusion lemmas for rejection vs share / proper cross / overlap

   Honest scoping: closed segments; endpoint-only Touches witness lives in
   `RelateBoundary.v` (S4b).  Area-line fill is S9 (`RelateMatrixAreaLine.v`).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance RelateLineLine.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Regime enum + matrix fill.                                                 *)
(* -------------------------------------------------------------------------- *)

Inductive LinePairRegime : Type :=
| LPR_Disjoint
| LPR_ProperCross
| LPR_Share
| LPR_CollinearOverlap.

Definition line_pair_fill (r : LinePairRegime) : IntersectionMatrix :=
  match r with
  | LPR_Disjoint         => ll_matrix_disjoint
  | LPR_ProperCross      => ll_matrix_point_ii
  | LPR_Share            => ll_matrix_point_ii
  | LPR_CollinearOverlap => ll_matrix_overlap_ii
  end.

Lemma line_pair_fill_disjoint_eq :
  line_pair_fill LPR_Disjoint = ll_matrix_disjoint.
Proof. reflexivity. Qed.

Lemma line_pair_fill_proper_cross_eq :
  line_pair_fill LPR_ProperCross = ll_matrix_point_ii.
Proof. reflexivity. Qed.

Lemma line_pair_fill_share_eq :
  line_pair_fill LPR_Share = ll_matrix_point_ii.
Proof. reflexivity. Qed.

Lemma line_pair_fill_collinear_overlap_eq :
  line_pair_fill LPR_CollinearOverlap = ll_matrix_overlap_ii.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Classifier — mirrors S2 guards.                                            *)
(* -------------------------------------------------------------------------- *)

Definition classify_line_pair (A B C D : Point) (r : LinePairRegime) : Prop :=
  match r with
  | LPR_Disjoint         => segments_rejected A B C D
  | LPR_ProperCross      => segments_proper_cross A B C D
  | LPR_Share            => segments_share A B C D
  | LPR_CollinearOverlap =>
      segments_collinear A B C D /\
      segments_interior_collinear_overlap A B C D
  end.

Lemma proper_cross_not_rejected :
  forall A B C D : Point,
    segments_proper_cross A B C D ->
    ~ segments_rejected A B C D.
Proof.
  intros A B C D [Hab Hcd] Hrej.
  unfold segments_rejected in Hrej.
  destruct Hrej as [Habpos | Hcdpos].
  - lra.
  - lra.
Qed.

Lemma collinear_overlap_not_proper_cross :
  forall A B C D : Point,
    segments_collinear A B C D ->
    segments_interior_collinear_overlap A B C D ->
    ~ segments_proper_cross A B C D.
Proof.
  intros A B C D Hcol _ Hcross.
  destruct Hcol as [Hac [Had [_ _]]].
  destruct Hcross as [Hprod _].
  rewrite Hac, Had in Hprod. lra.
Qed.

Lemma rejection_not_share :
  forall A B C D : Point,
    segments_rejected A B C D ->
    ~ segments_share A B C D.
Proof.
  intros A B C D Hrej Hshare.
  destruct (line_line_rejection_disjoint_sound A B C D Hrej) as [_ Hnoshare].
  exact (Hnoshare Hshare).
Qed.

Lemma share_not_rejected :
  forall A B C D : Point,
    segments_share A B C D ->
    ~ segments_rejected A B C D.
Proof.
  intros A B C D Hshare Hrej.
  exact (rejection_not_share A B C D Hrej Hshare).
Qed.

Lemma collinear_overlap_not_rejected :
  forall A B C D : Point,
    segments_collinear A B C D ->
    segments_interior_collinear_overlap A B C D ->
    ~ segments_rejected A B C D.
Proof.
  intros A B C D Hcol Hov Hrej.
  pose proof (line_line_collinear_overlap_share A B C D Hcol Hov) as Hshare.
  exact (share_not_rejected A B C D Hshare Hrej).
Qed.

(* -------------------------------------------------------------------------- *)
(* Compute-path soundness.                                                    *)
(* -------------------------------------------------------------------------- *)

Theorem line_fill_disjoint_sound :
  forall A B C D : Point,
    segments_rejected A B C D ->
    im_disjoint (line_pair_fill LPR_Disjoint).
Proof.
  intros A B C D Hrej.
  rewrite line_pair_fill_disjoint_eq.
  destruct (line_line_rejection_disjoint_sound A B C D Hrej) as [Hdisj _].
  exact Hdisj.
Qed.

Theorem line_fill_proper_cross_sound :
  forall A B C D : Point,
    segments_proper_cross A B C D ->
    im_crosses (line_pair_fill LPR_ProperCross) /\
    im_intersects (line_pair_fill LPR_ProperCross).
Proof.
  intros A B C D Hcross.
  rewrite line_pair_fill_proper_cross_eq.
  exact (line_line_proper_cross_sound A B C D Hcross).
Qed.

Theorem line_fill_share_sound :
  forall A B C D : Point,
    segments_share A B C D ->
    im_intersects (line_pair_fill LPR_Share).
Proof.
  intros A B C D Hshare.
  rewrite line_pair_fill_share_eq.
  exact (line_line_share_intersects_sound A B C D Hshare).
Qed.

Theorem line_fill_collinear_overlap_sound :
  forall A B C D : Point,
    segments_collinear A B C D ->
    segments_interior_collinear_overlap A B C D ->
    im_overlaps (line_pair_fill LPR_CollinearOverlap).
Proof.
  intros A B C D Hcol Hov.
  rewrite line_pair_fill_collinear_overlap_eq.
  exact (line_line_collinear_overlap_sound A B C D Hcol Hov).
Qed.

Theorem classify_disjoint_fill_sound :
  forall A B C D : Point,
    classify_line_pair A B C D LPR_Disjoint ->
    im_disjoint (line_pair_fill LPR_Disjoint).
Proof.
  intros A B C D H. unfold classify_line_pair in H.
  exact (line_fill_disjoint_sound A B C D H).
Qed.

Theorem classify_proper_cross_fill_sound :
  forall A B C D : Point,
    classify_line_pair A B C D LPR_ProperCross ->
    im_crosses (line_pair_fill LPR_ProperCross) /\
    im_intersects (line_pair_fill LPR_ProperCross).
Proof.
  intros A B C D H. unfold classify_line_pair in H.
  exact (line_fill_proper_cross_sound A B C D H).
Qed.

Theorem classify_share_fill_sound :
  forall A B C D : Point,
    classify_line_pair A B C D LPR_Share ->
    im_intersects (line_pair_fill LPR_Share).
Proof.
  intros A B C D H. unfold classify_line_pair in H.
  exact (line_fill_share_sound A B C D H).
Qed.

Theorem classify_collinear_overlap_fill_sound :
  forall A B C D : Point,
    classify_line_pair A B C D LPR_CollinearOverlap ->
    im_overlaps (line_pair_fill LPR_CollinearOverlap).
Proof.
  intros A B C D H. unfold classify_line_pair in H.
  destruct H as [Hcol Hov].
  exact (line_fill_collinear_overlap_sound A B C D Hcol Hov).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions line_fill_disjoint_sound.
Print Assumptions line_fill_proper_cross_sound.
Print Assumptions line_fill_share_sound.
Print Assumptions line_fill_collinear_overlap_sound.