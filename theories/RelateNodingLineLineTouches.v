(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLineTouches
   ----------------------------------------------------------------------------
   Issue #67 subtask 67-d (S15l+): Touches-vs-Share fill split.

   S15j recorded that `line_pair_fill LPR_Share` (II = 0) is not the
   true dimension of an int×bnd contact
   (`line_pair_fill_share_ii_not_pinned_int_bnd_only`).  This module
   is the fill that contact selects: `LPR_Touches` maps to
   `ll_matrix_touches_endpoint` (II empty, IB = 0).  `LPR_Share` stays
   the interior-share point matrix.  The two fills are not equal.

   Witness: T-junction AB = (0,0)–(2,0), CD = (1,0)–(1,1).  The kiss
   (1,0) is strict-interior on AB and the start of CD.  The open
   interiors miss.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok
   ========================================================================== *)

(* WITNESS {"claimId":"67-d","topic":"relate","lemma":"classify_touches_ib_cell","title":"Int×bnd line×line contact fills the Touches matrix (II empty, IB=0), not the Share point-II matrix","file":"theories/RelateNodingLineLineTouches.v"} *)
(* mutation-seed: 670415 *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance Segment
  RelateLineLine RelateBoundary RelateMatrixLineLine
  RelateNodingLineLineStrata RelateNodingLineLineMeet
  RelateNodingLineLinePinned.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Classifier arm ↔ the S15 meet predicate.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma segments_int_bnd_only_contact :
  forall A B C D,
    segments_int_bnd_only A B C D ->
    segments_int_bnd_contact A B C D /\
    ~ segments_interior_share A B C D.
Proof.
  intros A B C D [[p [Hint Hbnd]] Hnoshare].
  split; [ | exact Hnoshare ].
  exists p. split.
  - unfold seg_in_stratum. exact Hint.
  - unfold seg_in_stratum. exact Hbnd.
Qed.

Theorem classify_touches_ib_cell :
  forall A B C D,
    classify_line_pair A B C D LPR_Touches ->
    line_ib_point_cell A B C D (line_pair_fill LPR_Touches).
Proof.
  intros A B C D Htou.
  unfold classify_line_pair in Htou.
  destruct (segments_int_bnd_only_contact A B C D Htou) as [Hcontact _].
  rewrite line_pair_fill_touches_eq.
  apply segments_int_bnd_touches_ib_cell. exact Hcontact.
Qed.

Theorem classify_touches_ii_empty :
  forall A B C D,
    classify_line_pair A B C D LPR_Touches ->
    line_cell_ok (im_ii (line_pair_fill LPR_Touches)) LSInt LSInt A B C D.
Proof.
  intros A B C D Htou.
  unfold classify_line_pair in Htou.
  destruct (segments_int_bnd_only_contact A B C D Htou) as [_ Hnoshare].
  rewrite line_pair_fill_touches_eq.
  unfold im_ii, ll_matrix_touches_endpoint. simpl.
  apply line_cell_ok_none_when.
  intros [p [HpAB HpCD]].
  apply Hnoshare. exists p. split; assumption.
Qed.

Theorem classify_touches_share_fill_refused :
  forall A B C D,
    classify_line_pair A B C D LPR_Touches ->
    ~ line_cell_ok_pinned (im_ii (line_pair_fill LPR_Share)) LSInt LSInt A B C D.
Proof.
  intros A B C D Htou.
  unfold classify_line_pair in Htou.
  destruct (segments_int_bnd_only_contact A B C D Htou) as [Hcontact Hnoshare].
  apply line_pair_fill_share_ii_not_pinned_int_bnd_only; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* T-junction witness.                                                        *)
(* -------------------------------------------------------------------------- *)

Definition touch_pin_A : Point := mkPoint 0 0.
Definition touch_pin_B : Point := mkPoint 2 0.
Definition touch_pin_C : Point := mkPoint 1 0.
Definition touch_pin_D : Point := mkPoint 1 1.

Lemma touch_pin_AB_neq : touch_pin_A <> touch_pin_B.
Proof.
  unfold touch_pin_A, touch_pin_B. intro H.
  apply (f_equal px) in H. simpl in H. lra.
Qed.

Lemma touch_pin_mid_is_C :
  midpoint touch_pin_A touch_pin_B = touch_pin_C.
Proof.
  unfold midpoint, touch_pin_A, touch_pin_B, touch_pin_C. simpl.
  f_equal; lra.
Qed.

Lemma touch_pin_contact : segments_int_bnd_only touch_pin_A touch_pin_B
  touch_pin_C touch_pin_D.
Proof.
  split.
  - exists (midpoint touch_pin_A touch_pin_B). split.
    + apply between_strict_midpoint. apply touch_pin_AB_neq.
    + rewrite touch_pin_mid_is_C.
      split; [ apply between_P0 | left; reflexivity ].
  - intros [X [HAB HCD]].
    destruct HAB as [t [[Ht0 Ht1] [Hx Hy]]].
    destruct HCD as [s [[Hs0 Hs1] [Hx2 Hy2]]].
    unfold touch_pin_A, touch_pin_B, touch_pin_C, touch_pin_D in *.
    simpl in Hx, Hy, Hx2, Hy2. lra.
Qed.

Theorem touch_junction_classifies :
  classify_line_pair touch_pin_A touch_pin_B touch_pin_C touch_pin_D LPR_Touches.
Proof.
  unfold classify_line_pair. apply touch_pin_contact.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions classify_touches_ib_cell.
Print Assumptions classify_touches_ii_empty.
Print Assumptions classify_touches_share_fill_refused.
Print Assumptions touch_junction_classifies.
Print Assumptions line_fill_touches_witness.
