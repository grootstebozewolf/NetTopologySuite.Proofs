(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLine
   ----------------------------------------------------------------------------
   Issue #67 session 15a (S15a): line×line point-set DE-9IM bridge.

   First RelateNG-noding rung: closed-segment strata (strict interior /
   endpoint boundary / exterior) and a 9-cell `line_de9im_pointset`
   specification, bridged to the S8 regime→witness selection for the
   disjoint and proper-cross regimes.

   Delivers:

     - `LineStratum` + `seg_in_stratum` / `line_cell_ok` / `line_de9im_pointset`
     - `two_segments_exterior_meet` (bounded segments share an exterior point)
     - Meet-layer bridges:
         `segments_rejected` / `LPR_Disjoint` ⇒ four interior/boundary-meet
         cells empty (`line_no_ib_meet`);
         `segments_proper_cross` / `LPR_ProperCross` ⇒ II = 0-dimensional
         point cell (`line_ii_point_cell`)

   Honest gaps (deferred S15b+):

     - S8 `ll_matrix_disjoint` / `ll_matrix_point_ii` leave exterior-row
       cells `None` (non-OGC simplification; cf. Romanschek paper test 10/13
       with EE = 2 in `RelateLineLine.v`).
     - Proper-cross IB/BI/BB emptiness and `LPR_Share` /
       `LPR_CollinearOverlap` full-matrix bridges (S15b).
     - Cell *dimension* pinning (II = 0 vs 1) beyond nonempty/empty.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance Orientation Segment Intersect
  RelateLineLine RelateBoundary RelateMatrixLineLine.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Segment strata (closed segment point-set topology).                    *)
(* -------------------------------------------------------------------------- *)

Inductive LineStratum : Type := LSInt | LSBnd | LSExt.

Definition seg_in_stratum (s : LineStratum) (P0 P1 p : Point) : Prop :=
  match s with
  | LSInt => between_strict P0 P1 p
  | LSBnd => on_segment_endpoint P0 P1 p
  | LSExt => ~ between P0 P1 p
  end.

Lemma between_strict_implies_between :
  forall P0 P1 Q, between_strict P0 P1 Q -> between P0 P1 Q.
Proof.
  intros P0 P1 Q [t [Ht [Hx Hy]]].
  exists t. repeat split; try lra; assumption.
Qed.

Lemma endpoint_implies_between :
  forall P0 P1 Q, on_segment_endpoint P0 P1 Q -> between P0 P1 Q.
Proof.
  intros P0 P1 Q [H _]. exact H.
Qed.

Lemma between_py_le_max :
  forall P0 P1 Q, between P0 P1 Q ->
    py Q <= Rmax (py P0) (py P1).
Proof.
  intros P0 P1 Q Hbet.
  destruct Hbet as [t Ht].
  destruct Ht as [Ht0 [Ht1 [Hx Hy]]].
  rewrite Hy. destruct (Rle_dec (py P0) (py P1)) as [Hle | Hgt].
  - rewrite Rmax_right; [ nra | exact Hle ].
  - rewrite Rmax_left; [ nra | lra ].
Qed.

Lemma above_segment_not_on :
  forall P0 P1 p b,
    (forall Q, between P0 P1 Q -> py Q <= b) ->
    b < py p ->
    ~ between P0 P1 p.
Proof.
  intros P0 P1 p b Hbound Hgt Hbet.
  apply (Rlt_not_le (py p) b); [ exact Hgt | ].
  apply Hbound. exact Hbet.
Qed.

Lemma segment_exterior_above :
  forall P0 P1 b p,
    (forall Q, between P0 P1 Q -> py Q <= b) ->
    py p = b + 1 ->
    seg_in_stratum LSExt P0 P1 p.
Proof.
  intros P0 P1 b p Hbound Hpy.
  unfold seg_in_stratum. simpl.
  apply above_segment_not_on with (b := b); [ exact Hbound | ].
  rewrite Hpy. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Point-set DE-9IM specification for a segment pair.                     *)
(* -------------------------------------------------------------------------- *)

Definition line_cell_ok (d : DimValue) (sX sY : LineStratum)
    (A B C D : Point) : Prop :=
  dim_value_ok d /\
  (dim_nonempty d <->
   exists p : Point, seg_in_stratum sX A B p /\ seg_in_stratum sY C D p).

Definition line_de9im_pointset (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ii m) LSInt LSInt A B C D /\
  line_cell_ok (im_ib m) LSInt LSBnd A B C D /\
  line_cell_ok (im_ie m) LSInt LSExt A B C D /\
  line_cell_ok (im_bi m) LSBnd LSInt A B C D /\
  line_cell_ok (im_bb m) LSBnd LSBnd A B C D /\
  line_cell_ok (im_be m) LSBnd LSExt A B C D /\
  line_cell_ok (im_ei m) LSExt LSInt A B C D /\
  line_cell_ok (im_eb m) LSExt LSBnd A B C D /\
  line_cell_ok (im_ee m) LSExt LSExt A B C D.

Definition line_no_ib_meet (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ii m) LSInt LSInt A B C D /\
  line_cell_ok (im_ib m) LSInt LSBnd A B C D /\
  line_cell_ok (im_bi m) LSBnd LSInt A B C D /\
  line_cell_ok (im_bb m) LSBnd LSBnd A B C D.

Definition line_point_ii_ib_meet (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ii m) LSInt LSInt A B C D /\
  line_cell_ok (im_ib m) LSInt LSBnd A B C D /\
  line_cell_ok (im_bi m) LSBnd LSInt A B C D /\
  line_cell_ok (im_bb m) LSBnd LSBnd A B C D.

Lemma line_cell_ok_none_when :
  forall sX sY A B C D,
    ~ (exists p : Point, seg_in_stratum sX A B p /\ seg_in_stratum sY C D p) ->
    line_cell_ok None sX sY A B C D.
Proof.
  intros sX sY A B C D Hempty. split; [ exact I | ].
  split.
  - intro Hdn. exfalso. apply Hdn. reflexivity.
  - intros Hex. exfalso. apply Hempty. exact Hex.
Qed.

Lemma line_cell_ok_dim0 :
  forall sX sY A B C D p,
    seg_in_stratum sX A B p ->
    seg_in_stratum sY C D p ->
    line_cell_ok (Some 0%nat) sX sY A B C D.
Proof.
  intros sX sY A B C D p HsX HsY.
  split.
  - unfold dim_value_ok. simpl. repeat constructor.
  - split; [ intros _; exists p; split; assumption | ].
    intros [p' [Hp' _]]. intro H. discriminate H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Exterior meet — two bounded segments share an exterior point.          *)
(* -------------------------------------------------------------------------- *)

Definition segment_py_ub (P0 P1 : Point) : R :=
  Rmax (py P0) (py P1).

Lemma two_segments_exterior_meet :
  forall A B C D : Point,
    exists p : Point,
      seg_in_stratum LSExt A B p /\ seg_in_stratum LSExt C D p.
Proof.
  intros A B C D.
  set (b := Rmax (segment_py_ub A B) (segment_py_ub C D)).
  exists (mkPoint 0 (b + 1)).
  split.
  - apply segment_exterior_above with (b := b).
    + intros Q Hbet. eapply Rle_trans.
      * apply between_py_le_max; exact Hbet.
      * apply Rmax_l.
    + reflexivity.
  - apply segment_exterior_above with (b := b).
    + intros Q Hbet. eapply Rle_trans.
      * apply between_py_le_max; exact Hbet.
      * apply Rmax_r.
    + reflexivity.
Qed.

Lemma line_de9im_ee_inhabited :
  forall A B C D m,
    line_de9im_pointset A B C D m ->
    dim_nonempty (im_ee m).
Proof.
  intros A B C D m H.
  destruct H as [_ [_ [_ [_ [_ [_ [_ [_ Hee]]]]]]]].
  destruct (two_segments_exterior_meet A B C D) as [p [HA HB]].
  apply Hee. exists p. split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  No-share ⇒ meet cells empty (disjoint regime geometry).                *)
(* -------------------------------------------------------------------------- *)

Lemma int_bnd_share :
  forall A B C D p,
    seg_in_stratum LSInt A B p ->
    seg_in_stratum LSBnd C D p ->
    segments_share A B C D.
Proof.
  intros A B C D p HAB HCD.
  exists p. split.
  - apply between_strict_implies_between; exact HAB.
  - apply endpoint_implies_between; exact HCD.
Qed.

Lemma bnd_int_share :
  forall A B C D p,
    seg_in_stratum LSBnd A B p ->
    seg_in_stratum LSInt C D p ->
    segments_share A B C D.
Proof.
  intros A B C D p HAB HCD.
  exists p. split.
  - apply endpoint_implies_between; exact HAB.
  - apply between_strict_implies_between; exact HCD.
Qed.

Lemma bnd_bnd_share :
  forall A B C D p,
    seg_in_stratum LSBnd A B p ->
    seg_in_stratum LSBnd C D p ->
    segments_share A B C D.
Proof.
  intros A B C D p HAB HCD.
  exists p. split; apply endpoint_implies_between; assumption.
Qed.

Lemma int_int_share :
  forall A B C D p,
    seg_in_stratum LSInt A B p ->
    seg_in_stratum LSInt C D p ->
    segments_share A B C D.
Proof.
  intros A B C D p HAB HCD.
  exists p. split; apply between_strict_implies_between; assumption.
Qed.

Lemma no_share_no_int_int :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ (exists p : Point, seg_in_stratum LSInt A B p /\ seg_in_stratum LSInt C D p).
Proof.
  intros A B C D Hnoshare [p [HAB HCD]].
  apply Hnoshare. exact (int_int_share A B C D p HAB HCD).
Qed.

Lemma no_share_no_int_bnd :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ (exists p : Point, seg_in_stratum LSInt A B p /\ seg_in_stratum LSBnd C D p).
Proof.
  intros A B C D Hnoshare [p [HAB HCD]].
  apply Hnoshare. exact (int_bnd_share A B C D p HAB HCD).
Qed.

Lemma no_share_no_bnd_int :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ (exists p : Point, seg_in_stratum LSBnd A B p /\ seg_in_stratum LSInt C D p).
Proof.
  intros A B C D Hnoshare [p [HAB HCD]].
  apply Hnoshare. exact (bnd_int_share A B C D p HAB HCD).
Qed.

Lemma no_share_no_bnd_bnd :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ (exists p : Point, seg_in_stratum LSBnd A B p /\ seg_in_stratum LSBnd C D p).
Proof.
  intros A B C D Hnoshare [p [HAB HCD]].
  apply Hnoshare. exact (bnd_bnd_share A B C D p HAB HCD).
Qed.

Theorem segments_no_share_line_no_ib_meet :
  forall A B C D,
    ~ segments_share A B C D ->
    line_no_ib_meet A B C D ll_matrix_disjoint.
Proof.
  intros A B C D Hnoshare.
  unfold line_no_ib_meet, ll_matrix_disjoint. simpl.
  split; [ apply (line_cell_ok_none_when LSInt LSInt A B C D)
           | split; [ apply (line_cell_ok_none_when LSInt LSBnd A B C D)
                    | split; [ apply (line_cell_ok_none_when LSBnd LSInt A B C D)
                             | apply (line_cell_ok_none_when LSBnd LSBnd A B C D) ] ] ].
  all: eauto using no_share_no_int_int, no_share_no_int_bnd,
    no_share_no_bnd_int, no_share_no_bnd_bnd.
Qed.

Theorem classify_disjoint_line_no_ib_meet :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    line_no_ib_meet A B C D (line_pair_fill LPR_Disjoint).
Proof.
  intros A B C D Hdisj.
  rewrite line_pair_fill_disjoint_eq.
  apply segments_no_share_line_no_ib_meet.
  intro Hshare. apply (rejection_not_share A B C D Hdisj Hshare).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Proper cross ⇒ II point cell + empty other meet cells.                 *)
(* -------------------------------------------------------------------------- *)

Lemma open_param_between_strict_ab :
  forall P0 P1 Q,
    (exists t : R,
       0 < t < 1 /\
       px Q = (1 - t) * px P0 + t * px P1 /\
       py Q = (1 - t) * py P0 + t * py P1) ->
    between_strict P0 P1 Q.
Proof.
  intros P0 P1 Q [t Ht]. exists t. exact Ht.
Qed.

Lemma proper_cross_interior_share :
  forall A B C D,
    segments_proper_cross A B C D ->
    segments_interior_share A B C D.
Proof.
  intros A B C D [Hab Hcd].
  exists (strict_intersection_point A B C D).
  split.
  - apply open_param_between_strict_ab.
    eauto using strict_intersection_point_open_ab.
  - apply open_param_between_strict_ab.
    eauto using strict_intersection_point_open_cd.
Qed.

Definition line_ii_point_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ii m) LSInt LSInt A B C D.

Theorem segments_proper_cross_line_ii_cell :
  forall A B C D,
    segments_proper_cross A B C D ->
    line_ii_point_cell A B C D ll_matrix_point_ii.
Proof.
  intros A B C D Hcross.
  unfold line_ii_point_cell, ll_matrix_point_ii. simpl.
  destruct (proper_cross_interior_share A B C D Hcross) as [X [HAB HCD]].
  apply (line_cell_ok_dim0 LSInt LSInt A B C D X HAB HCD).
Qed.

Theorem classify_proper_cross_line_ii_cell :
  forall A B C D,
    classify_line_pair A B C D LPR_ProperCross ->
    line_ii_point_cell A B C D (line_pair_fill LPR_ProperCross).
Proof.
  intros A B C D Hcross.
  rewrite line_pair_fill_proper_cross_eq.
  apply segments_proper_cross_line_ii_cell. exact Hcross.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Matrix well-formedness corollary.                                      *)
(* -------------------------------------------------------------------------- *)

Theorem line_de9im_matrix_ok :
  forall A B C D m,
    line_de9im_pointset A B C D m -> matrix_ok m.
Proof.
  intros A B C D m H.
  destruct H as [Hii [Hib [Hie [Hbi [Hbb [Hbe [Hei [Heb Hee]]]]]]]].
  unfold matrix_ok. repeat split;
    [ apply (proj1 Hii) | apply (proj1 Hib) | apply (proj1 Hie)
    | apply (proj1 Hbi) | apply (proj1 Hbb) | apply (proj1 Hbe)
    | apply (proj1 Hei) | apply (proj1 Heb) | apply (proj1 Hee) ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions classify_disjoint_line_no_ib_meet.
Print Assumptions classify_proper_cross_line_ii_cell.
Print Assumptions two_segments_exterior_meet.
Print Assumptions line_de9im_ee_inhabited.