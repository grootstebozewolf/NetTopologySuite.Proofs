(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLine
   ----------------------------------------------------------------------------
   Issue #67 session 15a–15f (S15a–S15f): line×line point-set DE-9IM bridge.

   First RelateNG-noding rung: closed-segment strata (strict interior /
   endpoint boundary / exterior) and a 9-cell `line_de9im_pointset`
   specification, bridged to the S8 regime→witness selection and the S4b
   Touches / Romanschek oracle matrices.

   Delivers:

     - `LineStratum` + `seg_in_stratum` / `line_cell_ok` / `line_de9im_pointset`
     - `two_segments_exterior_meet` (bounded segments share an exterior point)
     - Meet-layer bridges:
         `segments_rejected` / `LPR_Disjoint` ⇒ four interior/boundary-meet
         cells empty (`line_no_ib_meet`);
         `segments_proper_cross` / `LPR_ProperCross` ⇒ II = 0-dimensional
         point cell with IB/BI/BB empty (`line_point_ii_ib_meet`);
         `segments_interior_share` / `LPR_Share` (interior) ⇒ II = 0-dim point
         cell for `ll_matrix_point_ii`;
         `LPR_CollinearOverlap` (with `C <> D`) ⇒ II = 1-dimensional cell
         for `ll_matrix_overlap_ii`; degenerate `C = D` routes to
         `ll_matrix_point_ii`; shared-endpoint overlap ⇒ BB = 0-dim cell;
         T-junction int×bnd contact ⇒ IB = 0-dim for
         `ll_matrix_touches_endpoint`; mutual endpoint contact ⇒ BB = 0-dim;
         Romanschek EE = 2 exterior cell for any bounded segment pair;
         no-share midpoints ⇒ IE/EI = 1-dim (OGC exterior rows);
         JTS#1175 negative: no-share ⇒ point-set BI empty (test 10 BI=0
         not derivable here); bnd×int share ⇒ BI = 0-dim;
         endpoint exterior to other segment ⇒ BE/EB = 0-dim;
         JTS#1175 collection cross-product BI witness (bnd×int contact
         across segment lists); nominated-pair no-share ⇏ BI = 0-dim

   Honest gaps (deferred S15g+):

     - Full IE/EI/BE/EB from `line_pair_fill` alone; collection union
       semantics and matrix aggregation over segment cross-products.
     - `line_pair_fill LPR_Share` vs Touches / overlap witnesses;
       full cell-dimension pinning.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
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

Lemma seg_in_stratum_bnd_left :
  forall P0 P1, seg_in_stratum LSBnd P0 P1 P0.
Proof.
  intros P0 P1. unfold seg_in_stratum. simpl.
  split; [ apply between_P0 | left; reflexivity ].
Qed.

Lemma seg_in_stratum_bnd_right :
  forall P0 P1, seg_in_stratum LSBnd P0 P1 P1.
Proof.
  intros P0 P1. unfold seg_in_stratum. simpl.
  split; [ apply between_P1 | right; reflexivity ].
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

Lemma line_cell_ok_dim1 :
  forall sX sY A B C D p,
    seg_in_stratum sX A B p ->
    seg_in_stratum sY C D p ->
    line_cell_ok (Some 1%nat) sX sY A B C D.
Proof.
  intros sX sY A B C D p HsX HsY.
  split.
  - unfold dim_value_ok. simpl. repeat constructor.
  - split; [ intros _; exists p; split; assumption | ].
    intros [p' [Hp' _]]. intro H. discriminate H.
Qed.

Lemma line_cell_ok_dim2 :
  forall sX sY A B C D p,
    seg_in_stratum sX A B p ->
    seg_in_stratum sY C D p ->
    line_cell_ok (Some 2%nat) sX sY A B C D.
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

Lemma between_strict_implies_on_line :
  forall P0 P1 Q, between_strict P0 P1 Q -> cross P0 P1 Q = 0.
Proof.
  intros P0 P1 Q Hstrict.
  apply between_implies_on_line.
  apply between_strict_implies_between. exact Hstrict.
Qed.

Lemma endpoint_implies_on_line :
  forall P0 P1 Q, on_segment_endpoint P0 P1 Q -> cross P0 P1 Q = 0.
Proof.
  intros P0 P1 Q [Hbet [Heq | Heq]].
  - subst Q. apply cross_at_P0_is_collinear.
  - subst Q. apply cross_at_P1_is_collinear.
Qed.

Lemma between_strict_of_between_not_endpoints :
  forall P0 P1 Q,
    between P0 P1 Q ->
    Q <> P0 -> Q <> P1 ->
    between_strict P0 P1 Q.
Proof.
  intros P0 P1 Q [t [Ht0 [Ht1 [Hx Hy]]]] Hne0 Hne1.
  destruct (Rlt_dec 0 t) as [Htpos | Htpos].
  - destruct (Rlt_dec t 1) as [Htlt | Htlt].
    + exists t. repeat split; [exact Htpos | exact Htlt | assumption | assumption].
    + exfalso. apply Hne1. assert (Ht : t = 1) by lra.
      subst t. destruct P0, P1, Q; simpl in Hx, Hy. f_equal; lra.
  - exfalso. apply Hne0. assert (Ht : t = 0) by lra.
    subst t. destruct P0, Q; simpl in Hx, Hy. f_equal; lra.
Qed.

Lemma midpoint_not_endpoint_when_distinct :
  forall P0 P1,
    P0 <> P1 ->
    midpoint P0 P1 <> P0 /\ midpoint P0 P1 <> P1.
Proof.
  intros P0 P1 Hne.
  split; intro Heq.
  - apply Hne. destruct P0 as [x0 y0], P1 as [x1 y1].
    simpl in Heq. unfold midpoint in Heq. simpl in Heq.
    inversion Heq. subst. f_equal; lra.
  - apply Hne. destruct P0 as [x0 y0], P1 as [x1 y1].
    simpl in Heq. unfold midpoint in Heq. simpl in Heq.
    inversion Heq. subst. f_equal; lra.
Qed.

Lemma between_strict_midpoint :
  forall P0 P1, P0 <> P1 -> between_strict P0 P1 (midpoint P0 P1).
Proof.
  intros P0 P1 Hne.
  apply between_strict_of_between_not_endpoints.
  - apply midpoint_between.
  - destruct (midpoint_not_endpoint_when_distinct P0 P1 Hne) as [H0 _]. exact H0.
  - destruct (midpoint_not_endpoint_when_distinct P0 P1 Hne) as [_ H1]. exact H1.
Qed.

Lemma proper_cross_no_int_bnd :
  forall A B C D,
    segments_proper_cross A B C D ->
    ~ (exists p : Point, seg_in_stratum LSInt A B p /\ seg_in_stratum LSBnd C D p).
Proof.
  intros A B C D [Hprod _] [p [HAB [Hbet [HeqC | HeqD]]]].
  - rewrite HeqC in HAB.
    assert (Hc0 : cross A B C = 0) by (apply between_strict_implies_on_line; exact HAB).
    rewrite Hc0 in Hprod. lra.
  - rewrite HeqD in HAB.
    assert (Hd0 : cross A B D = 0) by (apply between_strict_implies_on_line; exact HAB).
    rewrite Hd0 in Hprod. lra.
Qed.

Lemma proper_cross_no_bnd_int :
  forall A B C D,
    segments_proper_cross A B C D ->
    ~ (exists p : Point, seg_in_stratum LSBnd A B p /\ seg_in_stratum LSInt C D p).
Proof.
  intros A B C D [_ Hprod] [p [[Hbet [HeqA | HeqB]] HCD]].
  - rewrite HeqA in HCD.
    assert (Hc0 : cross C D A = 0) by (apply between_strict_implies_on_line; exact HCD).
    rewrite Hc0 in Hprod. lra.
  - rewrite HeqB in HCD.
    assert (Hd0 : cross C D B = 0) by (apply between_strict_implies_on_line; exact HCD).
    rewrite Hd0 in Hprod. lra.
Qed.

Lemma proper_cross_no_bnd_bnd :
  forall A B C D,
    segments_proper_cross A B C D ->
    ~ (exists p : Point, seg_in_stratum LSBnd A B p /\ seg_in_stratum LSBnd C D p).
Proof.
  intros A B C D [Hab _] [p [HAB HCD]].
  unfold seg_in_stratum in HAB, HCD. simpl in HAB, HCD.
  destruct HAB as [_ [-> | ->]]; destruct HCD as [_ [-> | ->]];
    simpl in Hab;
    rewrite ?cross_at_P0_is_collinear, ?cross_at_P1_is_collinear in Hab;
    lra.
Qed.

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

Theorem segments_proper_cross_line_point_ii_ib_meet :
  forall A B C D,
    segments_proper_cross A B C D ->
    line_point_ii_ib_meet A B C D ll_matrix_point_ii.
Proof.
  intros A B C D Hcross.
  unfold line_point_ii_ib_meet, ll_matrix_point_ii. simpl.
  split.
  - apply segments_proper_cross_line_ii_cell. exact Hcross.
  - split.
    + apply (line_cell_ok_none_when LSInt LSBnd A B C D).
      eauto using proper_cross_no_int_bnd.
    + split.
      * apply (line_cell_ok_none_when LSBnd LSInt A B C D).
        eauto using proper_cross_no_bnd_int.
      * apply (line_cell_ok_none_when LSBnd LSBnd A B C D).
        eauto using proper_cross_no_bnd_bnd.
Qed.

Theorem classify_proper_cross_line_point_ii_ib_meet :
  forall A B C D,
    classify_line_pair A B C D LPR_ProperCross ->
    line_point_ii_ib_meet A B C D (line_pair_fill LPR_ProperCross).
Proof.
  intros A B C D Hcross.
  rewrite line_pair_fill_proper_cross_eq.
  apply segments_proper_cross_line_point_ii_ib_meet. exact Hcross.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Collinear overlap ⇒ II 1-dimensional cell (distinct endpoints).        *)
(* -------------------------------------------------------------------------- *)

Definition line_ii_dim1_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ii m) LSInt LSInt A B C D.

Lemma between_ab_midpoint_param :
  forall A B C D s t,
    0 <= s -> s <= 1 ->
    px C = (1 - s) * px A + s * px B ->
    py C = (1 - s) * py A + s * py B ->
    0 <= t -> t <= 1 ->
    px D = (1 - t) * px A + t * px B ->
    py D = (1 - t) * py A + t * py B ->
    px (midpoint C D) = (1 - (s + t) / 2) * px A + (s + t) / 2 * px B /\
    py (midpoint C D) = (1 - (s + t) / 2) * py A + (s + t) / 2 * py B.
Proof.
  intros A B C D s t _ _ HxC HyC _ _ HxD HyD.
  split.
  - unfold midpoint. cbn. rewrite HxC, HxD. field.
  - unfold midpoint. cbn. rewrite HyC, HyD. field.
Qed.

Lemma collinear_overlap_midpoint_strict_ab :
  forall A B C D,
    between A B C ->
    between A B D ->
    C <> D ->
    seg_in_stratum LSInt A B (midpoint C D).
Proof.
  intros A B C D HAC HAD Hne.
  unfold seg_in_stratum. simpl.
  destruct HAC as [s [Hs0 [Hs1 [HxC HyC]]]].
  destruct HAD as [t [Ht0 [Ht1 [HxD HyD]]]].
  destruct (between_ab_midpoint_param A B C D s t Hs0 Hs1 HxC HyC Ht0 Ht1 HxD HyD)
    as [HxM HyM].
  exists ((s + t) / 2). repeat split.
  - assert (Hpos : 0 < s + t).
    { apply Rnot_le_lt. intro Hle.
      assert (Hs : s = 0) by lra. assert (Ht : t = 0) by lra.
      subst s t. simpl in HxC, HyC, HxD, HyD.
      destruct A as [ax ay]. destruct C as [cx cy]. destruct D as [dx dy].
      simpl in HxC, HyC, HxD, HyD.
      exfalso. apply Hne.
      f_equal; lra. }
    lra.
  - assert (Hlt2 : s + t < 2).
    { apply Rnot_le_lt. intro Hle.
      assert (Hs : s = 1) by lra. assert (Ht : t = 1) by lra.
      subst s t. simpl in HxC, HyC, HxD, HyD.
      destruct B as [bx b_y]. destruct C as [cx cy]. destruct D as [dx dy].
      simpl in HxC, HyC, HxD, HyD.
      exfalso. apply Hne.
      f_equal; lra. }
    lra.
  - exact HxM.
  - exact HyM.
Qed.

Lemma collinear_overlap_midpoint_strict_cd :
  forall C D,
    C <> D ->
    seg_in_stratum LSInt C D (midpoint C D).
Proof.
  intros C D Hne.
  unfold seg_in_stratum. simpl.
  apply between_strict_midpoint. exact Hne.
Qed.

Theorem segments_collinear_overlap_line_ii_cell :
  forall A B C D,
    segments_collinear A B C D ->
    segments_interior_collinear_overlap A B C D ->
    C <> D ->
    line_ii_dim1_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D _ [HAC HAD] Hne.
  unfold line_ii_dim1_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim1 LSInt LSInt A B C D (midpoint C D)).
  - apply collinear_overlap_midpoint_strict_ab; assumption.
  - apply collinear_overlap_midpoint_strict_cd. exact Hne.
Qed.

Theorem classify_collinear_overlap_line_ii_cell :
  forall A B C D,
    classify_line_pair A B C D LPR_CollinearOverlap ->
    C <> D ->
    line_ii_dim1_cell A B C D (line_pair_fill LPR_CollinearOverlap).
Proof.
  intros A B C D [Hcol Hov] Hne.
  rewrite line_pair_fill_collinear_overlap_eq.
  apply segments_collinear_overlap_line_ii_cell; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Interior share ⇒ II point cell (share regime, strict-interior witness). *)
(* -------------------------------------------------------------------------- *)

Theorem segments_interior_share_line_ii_cell :
  forall A B C D,
    segments_interior_share A B C D ->
    line_ii_point_cell A B C D ll_matrix_point_ii.
Proof.
  intros A B C D [X [HAB HCD]].
  unfold line_ii_point_cell, ll_matrix_point_ii. simpl.
  apply (line_cell_ok_dim0 LSInt LSInt A B C D X).
  - unfold seg_in_stratum. simpl. exact HAB.
  - unfold seg_in_stratum. simpl. exact HCD.
Qed.

Theorem classify_share_interior_line_ii_cell :
  forall A B C D,
    classify_line_pair A B C D LPR_Share ->
    segments_interior_share A B C D ->
    line_ii_point_cell A B C D (line_pair_fill LPR_Share).
Proof.
  intros A B C D _ Hshare.
  rewrite line_pair_fill_share_eq.
  apply segments_interior_share_line_ii_cell. exact Hshare.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  Degenerate collinear overlap (`C = D`) ⇒ point II cell.                *)
(* -------------------------------------------------------------------------- *)

Lemma between_strict_self :
  forall P, between_strict P P P.
Proof.
  intros P. exists (1 / 2). split.
  - split; lra.
  - split; simpl; ring.
Qed.

Lemma between_strict_same_endpoints :
  forall P Q, between_strict P P Q -> Q = P.
Proof.
  intros P Q [t [Ht [Hx Hy]]].
  destruct P, Q. simpl in Hx, Hy. f_equal; lra.
Qed.

Theorem segments_collinear_overlap_CeqD_point_ii_cell :
  forall A B C D,
    C = D ->
    between_strict A B C ->
    line_ii_point_cell A B C D ll_matrix_point_ii.
Proof.
  intros A B C D Heq Hstrict.
  subst D.
  unfold line_ii_point_cell, ll_matrix_point_ii. simpl.
  apply (line_cell_ok_dim0 LSInt LSInt A B C C C).
  - unfold seg_in_stratum. simpl. exact Hstrict.
  - unfold seg_in_stratum. simpl. apply between_strict_self.
Qed.

Theorem classify_collinear_overlap_CeqD_point_ii_cell :
  forall A B C D,
    classify_line_pair A B C D LPR_CollinearOverlap ->
    C = D ->
    between_strict A B C ->
    line_ii_point_cell A B C D ll_matrix_point_ii.
Proof.
  intros A B C D _ Heq Hstrict.
  apply segments_collinear_overlap_CeqD_point_ii_cell; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §9  Collinear overlap — BB point cell at a shared segment endpoint.        *)
(* -------------------------------------------------------------------------- *)

Definition line_bb_point_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_bb m) LSBnd LSBnd A B C D.

Theorem collinear_overlap_endpoint_A_C_bb_cell :
  forall A B C D, A = C -> line_bb_point_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D Heq.
  subst C.
  unfold line_bb_point_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim0 LSBnd LSBnd A B A D A).
  - apply seg_in_stratum_bnd_left.
  - apply seg_in_stratum_bnd_left.
Qed.

Theorem collinear_overlap_endpoint_A_D_bb_cell :
  forall A B C D, A = D -> line_bb_point_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D Heq.
  subst D.
  unfold line_bb_point_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim0 LSBnd LSBnd A B C A A).
  - apply seg_in_stratum_bnd_left.
  - apply seg_in_stratum_bnd_right.
Qed.

Theorem collinear_overlap_endpoint_B_C_bb_cell :
  forall A B C D, B = C -> line_bb_point_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D Heq.
  subst C.
  unfold line_bb_point_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim0 LSBnd LSBnd A B B D B).
  - apply seg_in_stratum_bnd_right.
  - apply seg_in_stratum_bnd_left.
Qed.

Theorem collinear_overlap_endpoint_B_D_bb_cell :
  forall A B C D, B = D -> line_bb_point_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D Heq.
  subst D.
  unfold line_bb_point_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim0 LSBnd LSBnd A B C B B).
  - apply seg_in_stratum_bnd_right.
  - apply seg_in_stratum_bnd_right.
Qed.

Theorem classify_collinear_overlap_shared_endpoint_bb_cell :
  forall A B C D,
    classify_line_pair A B C D LPR_CollinearOverlap ->
    (A = C \/ A = D \/ B = C \/ B = D) ->
    line_bb_point_cell A B C D (line_pair_fill LPR_CollinearOverlap).
Proof.
  intros A B C D _ [HAC | [HAD | [HBC | HBD]]].
  - rewrite line_pair_fill_collinear_overlap_eq.
    apply collinear_overlap_endpoint_A_C_bb_cell. exact HAC.
  - rewrite line_pair_fill_collinear_overlap_eq.
    apply collinear_overlap_endpoint_A_D_bb_cell. exact HAD.
  - rewrite line_pair_fill_collinear_overlap_eq.
    apply collinear_overlap_endpoint_B_C_bb_cell. exact HBC.
  - rewrite line_pair_fill_collinear_overlap_eq.
    apply collinear_overlap_endpoint_B_D_bb_cell. exact HBD.
Qed.

(* -------------------------------------------------------------------------- *)
(* §10  T-junction / endpoint contact — Touches and overlap BB witnesses.       *)
(* -------------------------------------------------------------------------- *)

Definition segments_int_bnd_contact (A B C D : Point) : Prop :=
  exists p : Point, seg_in_stratum LSInt A B p /\ seg_in_stratum LSBnd C D p.

Definition line_ib_point_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ib m) LSInt LSBnd A B C D.

Theorem segments_int_bnd_touches_ib_cell :
  forall A B C D,
    segments_int_bnd_contact A B C D ->
    line_ib_point_cell A B C D ll_matrix_touches_endpoint.
Proof.
  intros A B C D [p [HAB HCD]].
  unfold line_ib_point_cell, ll_matrix_touches_endpoint. simpl.
  apply (line_cell_ok_dim0 LSInt LSBnd A B C D p); assumption.
Qed.

Theorem segments_share_int_bnd_touches_ib_cell :
  forall A B C D,
    segments_share A B C D ->
    segments_int_bnd_contact A B C D ->
    line_ib_point_cell A B C D ll_matrix_touches_endpoint.
Proof.
  intros A B C D _ Hint.
  apply segments_int_bnd_touches_ib_cell. exact Hint.
Qed.

Theorem segments_endpoint_contact_bb_cell :
  forall A B C D,
    segments_endpoint_contact A B C D ->
    line_bb_point_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D [X [HAB [HCD [HendAB HendCD]]]].
  unfold line_bb_point_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim0 LSBnd LSBnd A B C D X).
  - unfold seg_in_stratum. simpl. exact HendAB.
  - unfold seg_in_stratum. simpl. exact HendCD.
Qed.

Theorem segments_share_endpoint_contact_bb_cell :
  forall A B C D,
    segments_share A B C D ->
    segments_endpoint_contact A B C D ->
    line_bb_point_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D _ Hcontact.
  apply segments_endpoint_contact_bb_cell. exact Hcontact.
Qed.

(* -------------------------------------------------------------------------- *)
(* §11  OGC exterior row — EE = 2 for Romanschek / bounded segment pairs.     *)
(* -------------------------------------------------------------------------- *)

Definition line_ee_dim2_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ee m) LSExt LSExt A B C D.

Theorem segments_bounded_ee_dim2_cell :
  forall A B C D,
    line_ee_dim2_cell A B C D
      {| im_ii := ll_cell_empty; im_ib := ll_cell_empty; im_ie := ll_cell_empty;
         im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_cell_empty;
         im_ei := ll_cell_empty; im_eb := ll_cell_empty; im_ee := ll_dim2 |}.
Proof.
  intros A B C D.
  unfold line_ee_dim2_cell, ll_dim2. simpl.
  destruct (two_segments_exterior_meet A B C D) as [p [HA HB]].
  apply (line_cell_ok_dim2 LSExt LSExt A B C D p); assumption.
Qed.

Theorem paper_matrix_ee_dim2_cell :
  forall A B C D (m : IntersectionMatrix),
    im_ee m = Some 2%nat ->
    line_ee_dim2_cell A B C D m.
Proof.
  intros A B C D m Heq.
  unfold line_ee_dim2_cell. rewrite Heq. simpl.
  destruct (two_segments_exterior_meet A B C D) as [p [HA HB]].
  apply (line_cell_ok_dim2 LSExt LSExt A B C D p); assumption.
Qed.

Theorem paper_test10_ee_dim2_cell :
  forall A B C D, line_ee_dim2_cell A B C D ll_matrix_paper_test10.
Proof.
  intros. apply paper_matrix_ee_dim2_cell. reflexivity.
Qed.

Theorem paper_test13_ee_dim2_cell :
  forall A B C D, line_ee_dim2_cell A B C D ll_matrix_paper_test13.
Proof.
  intros. apply paper_matrix_ee_dim2_cell. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §12  OGC exterior rows + JTS#1175 BI negative (no-share regime).           *)
(* -------------------------------------------------------------------------- *)

Definition line_ie_dim1_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ie m) LSInt LSExt A B C D.

Definition line_ei_dim1_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ei m) LSExt LSInt A B C D.

Definition line_be_dim0_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_be m) LSBnd LSExt A B C D.

Definition line_eb_dim0_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_eb m) LSExt LSBnd A B C D.

Definition line_bi_point_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_bi m) LSBnd LSInt A B C D.

Definition segments_bnd_int_contact (A B C D : Point) : Prop :=
  exists p : Point, seg_in_stratum LSBnd A B p /\ seg_in_stratum LSInt C D p.

Lemma int_on_cd_share :
  forall A B C D p,
    seg_in_stratum LSInt A B p ->
    between C D p ->
    segments_share A B C D.
Proof.
  intros A B C D p HAB Hbet.
  exists p. split.
  - apply between_strict_implies_between. exact HAB.
  - exact Hbet.
Qed.

Lemma int_on_ab_share :
  forall A B C D p,
    seg_in_stratum LSInt C D p ->
    between A B p ->
    segments_share A B C D.
Proof.
  intros A B C D p HCD Hbet.
  exists p. split.
  - exact Hbet.
  - apply between_strict_implies_between. exact HCD.
Qed.

Lemma no_share_interior_not_on_cd :
  forall A B C D p,
    seg_in_stratum LSInt A B p ->
    ~ segments_share A B C D ->
    ~ between C D p.
Proof.
  intros A B C D p HAB Hnoshare Hbet.
  apply Hnoshare. eauto using int_on_cd_share.
Qed.

Lemma no_share_interior_not_on_ab :
  forall A B C D p,
    seg_in_stratum LSInt C D p ->
    ~ segments_share A B C D ->
    ~ between A B p.
Proof.
  intros A B C D p HCD Hnoshare Hbet.
  apply Hnoshare. eauto using int_on_ab_share.
Qed.

Theorem no_share_midpoint_ie_cell :
  forall A B C D,
    A <> B ->
    ~ segments_share A B C D ->
    line_ie_dim1_cell A B C D
      {| im_ii := ll_cell_empty; im_ib := ll_cell_empty; im_ie := ll_dim1;
         im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_cell_empty;
         im_ei := ll_cell_empty; im_eb := ll_cell_empty; im_ee := ll_cell_empty |}.
Proof.
  intros A B C D Hne Hnoshare.
  unfold line_ie_dim1_cell. simpl.
  apply (line_cell_ok_dim1 LSInt LSExt A B C D (midpoint A B)).
  - apply between_strict_midpoint. exact Hne.
  - unfold seg_in_stratum. simpl.
    intro Hbet. apply Hnoshare.
    apply int_on_cd_share with (p := midpoint A B).
    + apply between_strict_midpoint. exact Hne.
    + exact Hbet.
Qed.

Theorem no_share_midpoint_ei_cell :
  forall A B C D,
    C <> D ->
    ~ segments_share A B C D ->
    line_ei_dim1_cell A B C D
      {| im_ii := ll_cell_empty; im_ib := ll_cell_empty; im_ie := ll_cell_empty;
         im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_cell_empty;
         im_ei := ll_dim1; im_eb := ll_cell_empty; im_ee := ll_cell_empty |}.
Proof.
  intros A B C D Hne Hnoshare.
  unfold line_ei_dim1_cell. simpl.
  apply (line_cell_ok_dim1 LSExt LSInt A B C D (midpoint C D)).
  - unfold seg_in_stratum. simpl.
    intro Hbet. apply Hnoshare.
    apply int_on_ab_share with (p := midpoint C D).
    + apply between_strict_midpoint. exact Hne.
    + exact Hbet.
  - apply between_strict_midpoint. exact Hne.
Qed.

Theorem classify_disjoint_midpoint_ie_ei_cells :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    A <> B ->
    C <> D ->
    line_ie_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_ei_dim1_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hdisj HneAB HneCD.
  unfold line_ie_dim1_cell, line_ei_dim1_cell, ll_matrix_paper_test10. simpl.
  split.
  - apply no_share_midpoint_ie_cell.
    + exact HneAB.
    + intro Hshare. apply (rejection_not_share A B C D Hdisj Hshare).
  - apply no_share_midpoint_ei_cell.
    + exact HneCD.
    + intro Hshare. apply (rejection_not_share A B C D Hdisj Hshare).
Qed.

Theorem segments_bnd_int_bi_cell :
  forall A B C D,
    segments_bnd_int_contact A B C D ->
    line_bi_point_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D [p [HAB HCD]].
  unfold line_bi_point_cell, ll_matrix_paper_test10. simpl.
  apply (line_cell_ok_dim0 LSBnd LSInt A B C D p); assumption.
Qed.

Theorem jts1175_no_share_pointset_bi_empty :
  forall A B C D,
    ~ segments_share A B C D ->
    line_cell_ok None LSBnd LSInt A B C D.
Proof.
  intros. apply (line_cell_ok_none_when LSBnd LSInt A B C D).
  eauto using no_share_no_bnd_int.
Qed.

Theorem endpoint_a_exterior_be_cell :
  forall A B C D,
    ~ between C D A ->
    line_be_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hext.
  unfold line_be_dim0_cell, ll_matrix_paper_test10. simpl.
  apply (line_cell_ok_dim0 LSBnd LSExt A B C D A).
  - apply seg_in_stratum_bnd_left.
  - unfold seg_in_stratum. simpl. exact Hext.
Qed.

Theorem endpoint_b_exterior_be_cell :
  forall A B C D,
    ~ between C D B ->
    line_be_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hext.
  unfold line_be_dim0_cell, ll_matrix_paper_test10. simpl.
  apply (line_cell_ok_dim0 LSBnd LSExt A B C D B).
  - apply seg_in_stratum_bnd_right.
  - unfold seg_in_stratum. simpl. exact Hext.
Qed.

Theorem endpoint_c_exterior_eb_cell :
  forall A B C D,
    ~ between A B C ->
    line_eb_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hext.
  unfold line_eb_dim0_cell, ll_matrix_paper_test10. simpl.
  apply (line_cell_ok_dim0 LSExt LSBnd A B C D C).
  - unfold seg_in_stratum. simpl. exact Hext.
  - apply seg_in_stratum_bnd_left.
Qed.

Theorem endpoint_d_exterior_eb_cell :
  forall A B C D,
    ~ between A B D ->
    line_eb_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hext.
  unfold line_eb_dim0_cell, ll_matrix_paper_test10. simpl.
  apply (line_cell_ok_dim0 LSExt LSBnd A B C D D).
  - unfold seg_in_stratum. simpl. exact Hext.
  - apply seg_in_stratum_bnd_right.
Qed.

Theorem paper_test10_ie_ei_ee_cells :
  forall A B C D,
    A <> B ->
    C <> D ->
    ~ segments_share A B C D ->
    line_ie_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_ei_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_ee_dim2_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D HneAB HneCD Hnoshare.
  split.
  - unfold line_ie_dim1_cell, ll_matrix_paper_test10. simpl.
    apply no_share_midpoint_ie_cell; assumption.
  - split.
    + unfold line_ei_dim1_cell, ll_matrix_paper_test10. simpl.
      apply no_share_midpoint_ei_cell; assumption.
    + apply paper_test10_ee_dim2_cell.
Qed.

(* -------------------------------------------------------------------------- *)
(* §13  Matrix well-formedness corollary.                                     *)
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
(* §14  JTS#1175 collection BI witness + nominated-pair limitation.           *)
(* -------------------------------------------------------------------------- *)

Definition Segment2 : Type := (Point * Point)%type.

Definition line_collection_bnd_int_contact (segsA segsB : list Segment2) : Prop :=
  exists A B C D,
    In (A, B) segsA /\ In (C, D) segsB /\
    segments_bnd_int_contact A B C D.

Lemma bnd_int_contact_implies_segments_share :
  forall A B C D,
    segments_bnd_int_contact A B C D ->
    segments_share A B C D.
Proof.
  intros A B C D [p [Hbnd Hint]].
  exists p. split.
  - apply endpoint_implies_between. exact Hbnd.
  - apply between_strict_implies_between. exact Hint.
Qed.

Lemma no_share_no_bnd_int_contact :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ segments_bnd_int_contact A B C D.
Proof.
  intros A B C D Hnoshare Hcontact.
  apply Hnoshare. eauto using bnd_int_contact_implies_segments_share.
Qed.

Lemma bi_point_cell_implies_bnd_int_contact :
  forall A B C D d,
    line_cell_ok d LSBnd LSInt A B C D ->
    dim_nonempty d ->
    segments_bnd_int_contact A B C D.
Proof.
  intros A B C D d Hcell Hdn.
  destruct Hcell as [_ Hiff].
  destruct Hiff as [Hto _].
  destruct (Hto Hdn) as [p [Hbnd Hint]].
  exists p. split; assumption.
Qed.

Lemma bi_point_cell_implies_bnd_int_contact_matrix :
  forall A B C D m,
    line_bi_point_cell A B C D m ->
    dim_nonempty (im_bi m) ->
    segments_bnd_int_contact A B C D.
Proof.
  intros A B C D m Hbi Hdn.
  unfold line_bi_point_cell in Hbi.
  eauto using bi_point_cell_implies_bnd_int_contact.
Qed.

Theorem jts1175_no_share_nominated_pair_bi_empty :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ line_bi_point_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hnoshare Hbi.
  apply no_share_no_bnd_int_contact with (A := A) (B := B) (C := C) (D := D).
  - exact Hnoshare.
  - unfold line_bi_point_cell, ll_matrix_paper_test10 in Hbi.
    simpl in Hbi.
    apply (bi_point_cell_implies_bnd_int_contact A B C D (ll_dim0) Hbi).
    simpl. discriminate.
Qed.

Theorem line_collection_bnd_int_bi_cell :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    segments_bnd_int_contact A B C D ->
    line_bi_point_cell A B C D ll_matrix_paper_test10.
Proof.
  intros segsA segsB A B C D _ _ Hcontact.
  apply segments_bnd_int_bi_cell. exact Hcontact.
Qed.

Theorem jts1175_collection_bi_witness :
  forall segsA segsB,
    line_collection_bnd_int_contact segsA segsB ->
    exists A B C D,
      In (A, B) segsA /\
      In (C, D) segsB /\
      line_bi_point_cell A B C D ll_matrix_paper_test10.
Proof.
  intros segsA segsB [A [B [C [D [HinA [HinB Hcontact]]]]]].
  exists A; exists B; exists C; exists D.
  split; [exact HinA | split; [exact HinB | ]].
  apply (line_collection_bnd_int_bi_cell segsA segsB A B C D HinA HinB Hcontact).
Qed.

Theorem mod2_endpoint_bnd_int_bi_cell :
  forall A B C D,
    mod2_is_boundary_node 1 ->
    segments_bnd_int_contact A B C D ->
    line_bi_point_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D _ Hcontact.
  apply segments_bnd_int_bi_cell. exact Hcontact.
Qed.

Theorem classify_disjoint_exterior_be_eb_cells :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    ~ between C D A ->
    ~ between C D B ->
    ~ between A B C ->
    ~ between A B D ->
    line_be_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_eb_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D _ HextA HextB HextC HextD.
  split.
  - apply endpoint_a_exterior_be_cell. exact HextA.
  - apply endpoint_c_exterior_eb_cell. exact HextC.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions classify_disjoint_line_no_ib_meet.
Print Assumptions classify_proper_cross_line_ii_cell.
Print Assumptions classify_proper_cross_line_point_ii_ib_meet.
Print Assumptions classify_collinear_overlap_line_ii_cell.
Print Assumptions classify_share_interior_line_ii_cell.
Print Assumptions classify_collinear_overlap_CeqD_point_ii_cell.
Print Assumptions classify_collinear_overlap_shared_endpoint_bb_cell.
Print Assumptions segments_int_bnd_touches_ib_cell.
Print Assumptions segments_endpoint_contact_bb_cell.
Print Assumptions paper_matrix_ee_dim2_cell.
Print Assumptions classify_disjoint_midpoint_ie_ei_cells.
Print Assumptions jts1175_no_share_pointset_bi_empty.
Print Assumptions segments_bnd_int_bi_cell.
Print Assumptions paper_test10_ie_ei_ee_cells.
Print Assumptions bnd_int_contact_implies_segments_share.
Print Assumptions jts1175_no_share_nominated_pair_bi_empty.
Print Assumptions jts1175_collection_bi_witness.
Print Assumptions mod2_endpoint_bnd_int_bi_cell.
Print Assumptions classify_disjoint_exterior_be_eb_cells.
Print Assumptions two_segments_exterior_meet.
Print Assumptions line_de9im_ee_inhabited.