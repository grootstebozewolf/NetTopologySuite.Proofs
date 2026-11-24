(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLinePinned
   ----------------------------------------------------------------------------
   Issue #67 S15j: line×line point-set DE-9IM bridge — meet-layer
   cell-dimension pinning.

   Split (2026-08) from the former monolithic RelateNodingLineLine.v; the
   original §-numbers are preserved so the S15 session retros stay accurate.
   RelateNodingLineLine.v remains as the re-export umbrella.

   `line_cell_true_dim` / `line_cell_ok_pinned` with the forward bridge to
   `line_cell_ok`; II/BB regime pins for every `LinePairRegime`; the
   `LPR_Share` fill refused for int×bnd-only contact
   (`line_pair_fill_share_ii_not_pinned_int_bnd_only`); the Touches
   fill is `LPR_Touches` (67-d).

   Sections: §19 (meet-layer cell-dimension pinning, S15j).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Lia.
Import ListNotations.
From NTS.Proofs Require Import DE9IM Distance Orientation Segment Intersect
  RelateLineLine RelateBoundary RelateMatrixLineLine
  RelateNodingLineLineStrata RelateNodingLineLineMeet.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §19  Meet-layer cell-dimension pinning (S15j).                               *)
(* -------------------------------------------------------------------------- *)

Definition line_stratum_meet_nonempty (sX sY : LineStratum)
    (A B C D : Point) : Prop :=
  exists p : Point, seg_in_stratum sX A B p /\ seg_in_stratum sY C D p.

Definition line_cell_ok_pinned (d : DimValue) (sX sY : LineStratum)
    (A B C D : Point) : Prop :=
  match sX, sY with
  | LSInt, LSInt =>
      match d with
      | None => ~ line_stratum_meet_nonempty LSInt LSInt A B C D
      | Some 0%nat => line_stratum_meet_nonempty LSInt LSInt A B C D /\
                    ~ segments_interior_collinear_overlap A B C D
      | Some 1%nat => segments_interior_collinear_overlap A B C D /\ C <> D
      | Some (S (S _)) => False
      end
  | LSBnd, LSBnd =>
      match d with
      | None => ~ line_stratum_meet_nonempty LSBnd LSBnd A B C D
      | Some 0%nat => line_stratum_meet_nonempty LSBnd LSBnd A B C D
      | Some (S _) => False
      end
  | _, _ => False
  end.

Definition line_cell_true_dim (sX sY : LineStratum) (A B C D : Point) (d : DimValue) : Prop :=
  line_cell_ok_pinned d sX sY A B C D.

Lemma line_cell_ok_pinned_ii_some1 :
  forall A B C D,
    line_cell_ok_pinned (Some 1%nat) LSInt LSInt A B C D ->
    segments_interior_collinear_overlap A B C D /\ C <> D.
Proof.
  intros A B C D H. simpl in H. exact H.
Qed.

Lemma line_cell_ok_pinned_ii_some0 :
  forall A B C D,
    line_cell_ok_pinned (Some 0%nat) LSInt LSInt A B C D ->
    line_stratum_meet_nonempty LSInt LSInt A B C D /\
    ~ segments_interior_collinear_overlap A B C D.
Proof.
  intros A B C D H. simpl in H. exact H.
Qed.

Lemma line_cell_ok_pinned_ii_none :
  forall A B C D,
    line_cell_ok_pinned None LSInt LSInt A B C D ->
    ~ line_stratum_meet_nonempty LSInt LSInt A B C D.
Proof.
  intros A B C D H. simpl in H. exact H.
Qed.

Lemma line_cell_ok_pinned_bb_some0 :
  forall A B C D,
    line_cell_ok_pinned (Some 0%nat) LSBnd LSBnd A B C D ->
    line_stratum_meet_nonempty LSBnd LSBnd A B C D.
Proof.
  intros A B C D H. simpl in H. exact H.
Qed.

Lemma line_cell_ok_pinned_bb_none :
  forall A B C D,
    line_cell_ok_pinned None LSBnd LSBnd A B C D ->
    ~ line_stratum_meet_nonempty LSBnd LSBnd A B C D.
Proof.
  intros A B C D H. simpl in H. exact H.
Qed.

Lemma line_cell_ok_pinned_implies_ok_ii :
  forall d A B C D,
    line_cell_ok_pinned d LSInt LSInt A B C D ->
    line_cell_ok d LSInt LSInt A B C D.
Proof.
  intros d A B C D Hpin. unfold line_cell_ok_pinned in Hpin.
  destruct d as [n|] eqn:Hd.
  - destruct n as [| n2] eqn:Hn; try contradiction Hpin.
    + destruct Hpin as [Hne _].
      destruct Hne as [p [HsX HsY]].
      subst d. simpl.
      exact (line_cell_ok_dim0 LSInt LSInt A B C D p HsX HsY).
    + destruct n2 as [| n3] eqn:Hn2.
      * destruct Hpin as [Hov HneCD]. destruct Hov as [HAC HAD].
        subst d. simpl.
        pose proof (collinear_overlap_midpoint_strict_ab A B C D HAC HAD HneCD)
          as HsX.
        pose proof (collinear_overlap_midpoint_strict_cd C D HneCD) as HsY.
        exact (line_cell_ok_dim1 LSInt LSInt A B C D (midpoint C D) HsX HsY).
      * exfalso. subst d. simpl in Hpin. exact Hpin.
  - subst d. simpl.
    apply (line_cell_ok_none_when LSInt LSInt A B C D).
    intro Hex. apply Hpin. exact Hex.
Qed.

Lemma line_cell_ok_pinned_implies_ok_bb :
  forall d A B C D,
    line_cell_ok_pinned d LSBnd LSBnd A B C D ->
    line_cell_ok d LSBnd LSBnd A B C D.
Proof.
  intros d A B C D Hpin. unfold line_cell_ok_pinned in Hpin.
  destruct d as [n|] eqn:Hd.
  - destruct n eqn:Hn; [| contradiction Hpin].
    destruct Hpin as [p [HsX HsY]].
    subst d. simpl.
    exact (line_cell_ok_dim0 LSBnd LSBnd A B C D p HsX HsY).
  - subst d. simpl.
    apply (line_cell_ok_none_when LSBnd LSBnd A B C D).
    intro Hex. apply Hpin. exact Hex.
Qed.

Theorem line_cell_ok_pinned_implies_ok :
  forall d sX sY A B C D,
    line_cell_ok_pinned d sX sY A B C D ->
    line_cell_ok d sX sY A B C D.
Proof.
  intros d sX sY A B C D Hpin.
  unfold line_cell_ok_pinned in Hpin.
  destruct sX as [| |], sY as [| |]; try contradiction Hpin.
  - apply line_cell_ok_pinned_implies_ok_ii. exact Hpin.
  - apply line_cell_ok_pinned_implies_ok_bb. exact Hpin.
Qed.

Lemma proper_cross_not_collinear_overlap :
  forall A B C D,
    segments_proper_cross A B C D ->
    ~ segments_interior_collinear_overlap A B C D.
Proof.
  intros A B C D [Hab _] [HAC HAD].
  assert (Hc0 : cross A B C = 0) by (apply between_implies_on_line; exact HAC).
  assert (Hd0 : cross A B D = 0) by (apply between_implies_on_line; exact HAD).
  rewrite Hc0 in Hab. lra.
Qed.

Theorem proper_cross_ii_dim_pinned :
  forall A B C D,
    segments_proper_cross A B C D ->
    line_cell_ok_pinned (Some 0%nat) LSInt LSInt A B C D.
Proof.
  intros A B C D Hcross.
  simpl. split.
  - destruct (proper_cross_interior_share A B C D Hcross) as [X [HAB HCD]].
    exists X. split; assumption.
  - apply proper_cross_not_collinear_overlap. exact Hcross.
Qed.

Theorem proper_cross_not_ii_dim1 :
  forall A B C D,
    segments_proper_cross A B C D ->
    ~ line_cell_ok_pinned (Some 1%nat) LSInt LSInt A B C D.
Proof.
  intros A B C D Hcross Hpin.
  apply (line_cell_ok_pinned_ii_some1 A B C D) in Hpin.
  destruct Hpin as [Hov _].
  apply (proper_cross_not_collinear_overlap A B C D Hcross). exact Hov.
Qed.

Theorem collinear_overlap_ii_dim_pinned :
  forall A B C D,
    segments_interior_collinear_overlap A B C D ->
    C <> D ->
    line_cell_ok_pinned (Some 1%nat) LSInt LSInt A B C D.
Proof.
  intros A B C D Hov Hne. simpl. split; assumption.
Qed.

Theorem no_share_ii_dim_pinned :
  forall A B C D,
    ~ segments_share A B C D ->
    line_cell_ok_pinned None LSInt LSInt A B C D.
Proof.
  intros A B C D Hnoshare. simpl.
  intro Hne.
  apply (no_share_no_int_int A B C D Hnoshare).
  destruct Hne as [p [HAB HCD]]. exists p; split; assumption.
Qed.

Theorem share_interior_ii_dim_pinned :
  forall A B C D,
    segments_interior_share A B C D ->
    ~ segments_interior_collinear_overlap A B C D ->
    line_cell_ok_pinned (Some 0%nat) LSInt LSInt A B C D.
Proof.
  intros A B C D Hint Hnov. simpl. split.
  - destruct Hint as [X [HAB HCD]].
    exists X. split; assumption.
  - exact Hnov.
Qed.

Theorem endpoint_contact_bb_dim_pinned :
  forall A B C D,
    segments_endpoint_contact A B C D ->
    line_cell_ok_pinned (Some 0%nat) LSBnd LSBnd A B C D.
Proof.
  intros A B C D [X [HAB [HCD [HendAB HendCD]]]]. simpl.
  exists X. split.
  - unfold seg_in_stratum. simpl. exact HendAB.
  - unfold seg_in_stratum. simpl. exact HendCD.
Qed.

Theorem disjoint_bb_dim_pinned :
  forall A B C D,
    ~ segments_share A B C D ->
    line_cell_ok_pinned None LSBnd LSBnd A B C D.
Proof.
  intros A B C D Hnoshare. simpl.
  intro Hne.
  apply (no_share_no_bnd_bnd A B C D Hnoshare).
  destruct Hne as [p [HAB HCD]]. exists p; split; assumption.
Qed.

Theorem classify_proper_cross_ii_dim_pinned :
  forall A B C D,
    classify_line_pair A B C D LPR_ProperCross ->
    line_cell_ok_pinned (im_ii (line_pair_fill LPR_ProperCross)) LSInt LSInt A B C D.
Proof.
  intros A B C D Hcross.
  rewrite line_pair_fill_proper_cross_eq.
  unfold im_ii, ll_matrix_point_ii. simpl.
  apply proper_cross_ii_dim_pinned. exact Hcross.
Qed.

Theorem classify_collinear_overlap_ii_dim_pinned :
  forall A B C D,
    classify_line_pair A B C D LPR_CollinearOverlap ->
    C <> D ->
    line_cell_ok_pinned (im_ii (line_pair_fill LPR_CollinearOverlap)) LSInt LSInt A B C D.
Proof.
  intros A B C D [Hcol Hov] Hne.
  rewrite line_pair_fill_collinear_overlap_eq.
  unfold im_ii, ll_matrix_overlap_ii. simpl.
  apply collinear_overlap_ii_dim_pinned; assumption.
Qed.

Theorem classify_disjoint_ii_dim_pinned :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    line_cell_ok_pinned (im_ii (line_pair_fill LPR_Disjoint)) LSInt LSInt A B C D.
Proof.
  intros A B C D Hdisj.
  rewrite line_pair_fill_disjoint_eq.
  unfold im_ii, ll_matrix_disjoint. simpl.
  apply no_share_ii_dim_pinned.
  intro Hshare. apply (rejection_not_share A B C D Hdisj Hshare).
Qed.

Theorem classify_share_interior_ii_dim_pinned :
  forall A B C D,
    classify_line_pair A B C D LPR_Share ->
    segments_interior_share A B C D ->
    ~ segments_interior_collinear_overlap A B C D ->
    line_cell_ok_pinned (im_ii (line_pair_fill LPR_Share)) LSInt LSInt A B C D.
Proof.
  intros A B C D _ Hint Hnov.
  rewrite line_pair_fill_share_eq.
  unfold im_ii, ll_matrix_point_ii. simpl.
  apply share_interior_ii_dim_pinned; assumption.
Qed.

Theorem line_pair_fill_share_ii_not_pinned_int_bnd_only :
  forall A B C D,
    segments_int_bnd_contact A B C D ->
    ~ segments_interior_share A B C D ->
    ~ line_cell_ok_pinned (im_ii (line_pair_fill LPR_Share)) LSInt LSInt A B C D.
Proof.
  intros A B C D Hint Hnoint Hpin.
  rewrite line_pair_fill_share_eq in Hpin.
  unfold im_ii, ll_matrix_point_ii in Hpin. simpl in Hpin.
  destruct (line_cell_ok_pinned_ii_some0 A B C D Hpin) as [Hne _].
  destruct Hne as [p [HAB HCD]].
  apply Hnoint.
  exists p. split; assumption.
Qed.

Theorem line_pair_regime_disjoint_not_share :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    ~ classify_line_pair A B C D LPR_Share.
Proof.
  intros A B C D Hdisj Hshare.
  apply (rejection_not_share A B C D Hdisj).
  destruct Hshare as [X [HAB HCD]]. exists X; split; assumption.
Qed.

Theorem line_pair_regime_overlap_not_proper_cross :
  forall A B C D,
    classify_line_pair A B C D LPR_CollinearOverlap ->
    ~ classify_line_pair A B C D LPR_ProperCross.
Proof.
  intros A B C D [Hcol Hov] Hcross.
  apply (collinear_overlap_not_proper_cross A B C D Hcol Hov). exact Hcross.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions line_cell_ok_pinned_implies_ok.
Print Assumptions proper_cross_ii_dim_pinned.
Print Assumptions classify_proper_cross_ii_dim_pinned.
Print Assumptions classify_collinear_overlap_ii_dim_pinned.
Print Assumptions line_pair_fill_share_ii_not_pinned_int_bnd_only.
