(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLineCapstone
   ----------------------------------------------------------------------------
   Issue #67 S15k: line×line point-set DE-9IM bridge — collection
   relate-matrix pipeline capstone.

   Split (2026-08) from the former monolithic RelateNodingLineLine.v; the
   original §-numbers are preserved so the S15 session retros stay accurate.
   RelateNodingLineLine.v remains as the re-export umbrella.

   Fold-assign interface, generic fold soundness headline, regime-driven
   wrapper, test-10 pointset + fold=oracle + intersects; meet-layer pinned
   corollary on witness pairs.

   Honest gaps (remaining S15l+): prepared evaluate hook (identity already
   Qed).  Touches-vs-Share fill split is `LPR_Touches` (67-d), one
   orientation; its exterior cells are the honesty gap.
   Exterior-row true-dimension pinning landed in RelateNodingLineLineExtPinned.

   Sections: §20 (collection relate-matrix pipeline capstone, S15k).

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
  RelateNodingLineLineStrata RelateNodingLineLineMeet RelateNodingLineLineRows
  RelateNodingLineLineCollection RelateNodingLineLinePinned.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §20  Collection relate-matrix pipeline capstone (S15k).                      *)
(* -------------------------------------------------------------------------- *)

Definition line_pair_matrix_assign
    (assign : Point -> Point -> Point -> Point -> IntersectionMatrix)
    (A B C D : Point) : IntersectionMatrix :=
  assign A B C D.

Definition line_collection_matrix_fold_assign
    (assign : Point -> Point -> Point -> Point -> IntersectionMatrix)
    (segsA segsB : list Segment2) : IntersectionMatrix :=
  line_collection_matrix_fold assign segsA segsB.

Definition line_pair_matrix_of_regime (r : LinePairRegime) : IntersectionMatrix :=
  line_pair_fill r.

Lemma line_collection_matrix_fold_segsB_const :
  forall assign m A B segsB,
    (forall A' B' C' D', assign A' B' C' D' = m) ->
    (exists C D, In (C, D) segsB) ->
    line_collection_matrix_fold_segsB assign A B segsB = m.
Proof.
  intros assign m A B segsB Hconst HexB.
  induction segsB as [| [C D] rest IH]; simpl.
  - destruct HexB as [C [D H]]. simpl in H. destruct H.
  - destruct rest as [| [C1 D1] rest'].
    + rewrite matrix_dim_join_empty_right. apply Hconst.
    + assert (Hrest : line_collection_matrix_fold_segsB assign A B
        ((C1, D1) :: rest') = m).
      { apply IH. exists C1, D1. simpl. left. reflexivity. }
      rewrite (Hconst A B C D). rewrite Hrest.
      rewrite matrix_dim_join_idem. reflexivity.
Qed.

Lemma line_collection_matrix_fold_const :
  forall assign m segsA segsB,
    (forall A B C D, assign A B C D = m) ->
    (exists A B, In (A, B) segsA) ->
    (exists C D, In (C, D) segsB) ->
    line_collection_matrix_fold assign segsA segsB = m.
Proof.
  intros assign m segsA segsB Hconst HexA HexB.
  revert HexA.
  induction segsA as [| [A0 B0] segsA' IH]; simpl; intros HexA.
  - destruct HexA as [A [B H]]. simpl in H. destruct H.
  - assert (Hsb := line_collection_matrix_fold_segsB_const assign m A0 B0 segsB
      Hconst HexB).
    destruct segsA' as [| [A1 B1] rest].
    + rewrite matrix_dim_join_empty_left. exact Hsb.
    + assert (Htail : line_collection_matrix_fold assign ((A1, B1) :: rest) segsB = m).
      { apply IH. exists A1, B1. simpl. left. reflexivity. }
      rewrite Htail. rewrite Hsb. rewrite matrix_dim_join_idem. reflexivity.
Qed.

Theorem line_collection_relate_matrix_fold_sound :
  forall assign segsA segsB,
    (exists A B, In (A, B) segsA) ->
    (exists C D, In (C, D) segsB) ->
    (forall A B C D,
       In (A, B) segsA ->
       In (C, D) segsB ->
       line_de9im_pointset A B C D (line_pair_matrix_assign assign A B C D)) ->
    line_collection_de9im_pointset segsA segsB
      (line_collection_matrix_fold_assign assign segsA segsB).
Proof.
  intros assign segsA segsB HexA HexB Hpair.
  unfold line_collection_matrix_fold_assign, line_pair_matrix_assign.
  eauto using line_collection_matrix_fold_sound.
Qed.

Theorem line_collection_relate_matrix_fold_implies_rows :
  forall assign segsA segsB,
    (exists A B, In (A, B) segsA) ->
    (exists C D, In (C, D) segsB) ->
    (forall A B C D,
       In (A, B) segsA ->
       In (C, D) segsB ->
       line_de9im_pointset A B C D (line_pair_matrix_assign assign A B C D)) ->
    line_collection_cell_ok segsA segsB (im_bi (line_collection_matrix_fold_assign assign segsA segsB)) LSBnd LSInt /\
    line_collection_cell_ok segsA segsB (im_ie (line_collection_matrix_fold_assign assign segsA segsB)) LSInt LSExt /\
    line_collection_cell_ok segsA segsB (im_ei (line_collection_matrix_fold_assign assign segsA segsB)) LSExt LSInt /\
    line_collection_cell_ok segsA segsB (im_ee (line_collection_matrix_fold_assign assign segsA segsB)) LSExt LSExt.
Proof.
  intros assign segsA segsB HexA HexB Hpair.
  apply line_collection_de9im_pointset_implies_rows.
  eauto using line_collection_relate_matrix_fold_sound.
Qed.

Theorem line_collection_relate_matrix_regime_fold_sound :
  forall segsA segsB
         (regime : Point -> Point -> Point -> Point -> LinePairRegime),
    (exists A B, In (A, B) segsA) ->
    (exists C D, In (C, D) segsB) ->
    (forall A B C D,
       In (A, B) segsA ->
       In (C, D) segsB ->
       classify_line_pair A B C D (regime A B C D)) ->
    (forall A B C D,
       In (A, B) segsA ->
       In (C, D) segsB ->
       classify_line_pair A B C D (regime A B C D) ->
       line_de9im_pointset A B C D (line_pair_matrix_of_regime (regime A B C D))) ->
    line_collection_de9im_pointset segsA segsB
      (line_collection_matrix_fold_assign
         (fun A B C D => line_pair_matrix_of_regime (regime A B C D)) segsA segsB).
Proof.
  intros segsA segsB regime HexA HexB Hclass Hregime.
  apply line_collection_relate_matrix_fold_sound.
  - exact HexA.
  - exact HexB.
  - intros A B C D HinA HinB.
    specialize (Hregime A B C D HinA HinB (Hclass A B C D HinA HinB)).
    unfold line_pair_matrix_assign, line_pair_matrix_of_regime in Hregime.
    exact Hregime.
Qed.

Theorem classify_disjoint_pair_de9im_pointset_test10 :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    A <> B ->
    C <> D ->
    segments_bnd_int_contact A B C D ->
    line_de9im_pointset A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hdisj HneAB HneCD Hbnd.
  unfold line_de9im_pointset.
  destruct (classify_disjoint_test10_empty_meet_rows A B C D Hdisj)
    as [Hii [Hib Hbb]].
  destruct (classify_disjoint_paper_test10_exterior_rows A B C D Hdisj HneAB HneCD)
    as [Hie [Hei [Hbe [Heb Hee]]]].
  assert (Hbi : line_cell_ok (im_bi ll_matrix_paper_test10) LSBnd LSInt A B C D).
  { unfold im_bi, ll_matrix_paper_test10, line_bi_point_cell. simpl.
    apply segments_bnd_int_bi_cell. exact Hbnd. }
  unfold line_ie_dim1_cell, line_ei_dim1_cell, line_be_dim0_cell,
    line_eb_dim0_cell, line_ee_dim2_cell in Hie, Hei, Hbe, Heb, Hee.
  split; [ exact Hii | split; [ exact Hib | split; [ exact Hie | split;
    [ exact Hbi | split; [ exact Hbb | split; [ exact Hbe | split;
    [ exact Hei | split; [ exact Heb | exact Hee ] ] ] ] ] ] ] ].
Qed.

Theorem line_collection_relate_matrix_test10 :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    A <> B ->
    C <> D ->
    line_collection_bnd_int_contact segsA segsB ->
    line_collection_all_no_share segsA segsB ->
    line_collection_de9im_pointset segsA segsB ll_matrix_paper_test10 /\
    line_collection_matrix_fold_assign
      (fun _ _ _ _ => ll_matrix_paper_test10) segsA segsB =
      ll_matrix_paper_test10.
Proof.
  intros segsA segsB A B C D HinA HinB HneAB HneCD Hbndint Hnoshare.
  split.
  - apply (line_collection_test10_de9im_pointset segsA segsB A B C D); assumption.
  - apply line_collection_matrix_fold_const.
    + intros. reflexivity.
    + exists A. exists B. exact HinA.
    + exists C. exists D. exact HinB.
Qed.

Theorem line_collection_relate_matrix_test10_intersects :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    A <> B ->
    C <> D ->
    line_collection_all_no_share segsA segsB ->
    line_collection_bnd_int_contact segsA segsB ->
    im_intersects (line_collection_matrix_fold_assign
      (fun _ _ _ _ => ll_matrix_paper_test10) segsA segsB).
Proof.
  intros segsA segsB A B C D HinA HinB HneAB HneCD Hnoshare Hbndint.
  destruct (line_collection_relate_matrix_test10 segsA segsB A B C D HinA HinB
      HneAB HneCD Hbndint Hnoshare) as [_ Hfold].
  rewrite Hfold.
  apply (line_collection_test10_intersects segsA segsB A B C D); assumption.
Qed.

Theorem line_collection_relate_matrix_test10_meet_pinned :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    classify_line_pair A B C D LPR_Disjoint ->
    line_collection_all_no_share segsA segsB ->
    line_cell_ok_pinned (im_ii ll_matrix_paper_test10) LSInt LSInt A B C D /\
    line_cell_ok_pinned (im_bb ll_matrix_paper_test10) LSBnd LSBnd A B C D.
Proof.
  intros segsA segsB A B C D HinA HinB Hdisj Hnoshare.
  assert (Hns : ~ segments_share A B C D).
  { apply Hnoshare; assumption. }
  split.
  - unfold im_ii, ll_matrix_paper_test10. simpl.
    apply no_share_ii_dim_pinned. exact Hns.
  - unfold im_bb, ll_matrix_paper_test10. simpl.
    apply disjoint_bb_dim_pinned. exact Hns.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions line_collection_relate_matrix_fold_sound.
Print Assumptions line_collection_relate_matrix_test10.
Print Assumptions line_collection_relate_matrix_test10_intersects.
Print Assumptions line_collection_relate_matrix_regime_fold_sound.
