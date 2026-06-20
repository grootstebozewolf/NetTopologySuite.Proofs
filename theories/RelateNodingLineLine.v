(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLine
   ----------------------------------------------------------------------------
   Issue #67 session 15a–15k (S15a–S15k): line×line point-set DE-9IM bridge.

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
         across segment lists); nominated-pair no-share ⇏ BI = 0-dim;
         collection existential union (`line_collection_de9im_pointset`)
         + test-10 row aggregation + `dim_value_join` max cell algebra;
         S15h–k: per-pair test-10 fill bridges, `matrix_dim_join` fold
         soundness, II/BB dimension pinning, collection relate-matrix
         capstone (fold-assign + test-10 pointset/fold/intersects)

   S15h (§16): per-pair 9-cell noding bridges — disjoint test-10 exterior
     rows + meet fill; Share vs Touches IB disambiguation; regime-keyed
     `line_de9im_pointset` packaging (proper-cross meet layer, overlap
     meet + EE).  Test-10 BI = 0-dim remains collection-level (JTS#1175).

   S15i (§17–§18): `matrix_dim_join` + collection cell join soundness +
     cross-product `line_collection_matrix_fold`; test-10 full 9-cell
     `line_collection_de9im_pointset` capstone.

   S15j (§19): meet-layer cell-dimension pinning — `line_cell_true_dim` /
     `line_cell_ok_pinned` with forward bridge to `line_cell_ok`; II/BB
     regime pins; `LPR_Share` vs Touches fill mismatch documented.

   S15k (§20): collection relate-matrix pipeline capstone — fold-assign
     interface, generic fold soundness headline, regime-driven wrapper,
     test-10 pointset + fold=oracle + intersects; meet-layer pinned
     corollary on witness pairs.

   Honest gaps (deferred S15l+):

     - Prepared evaluate hook; exterior-row true-dimension pinning;
       new `LinePairRegime` for Touches-vs-Share at fill API.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Lia.
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
(* §15  Collection union semantics (existential cross-product aggregation).   *)
(* -------------------------------------------------------------------------- *)

Definition line_collection_all_no_share (segsA segsB : list Segment2) : Prop :=
  forall A B C D,
    In (A, B) segsA -> In (C, D) segsB -> ~ segments_share A B C D.

Definition line_collection_cell_ok (segsA segsB : list Segment2)
    (d : DimValue) (sX sY : LineStratum) : Prop :=
  exists A B C D,
    In (A, B) segsA /\ In (C, D) segsB /\
    line_cell_ok d sX sY A B C D.

Definition line_collection_de9im_pointset (segsA segsB : list Segment2)
    (m : IntersectionMatrix) : Prop :=
  line_collection_cell_ok segsA segsB (im_ii m) LSInt LSInt /\
  line_collection_cell_ok segsA segsB (im_ib m) LSInt LSBnd /\
  line_collection_cell_ok segsA segsB (im_ie m) LSInt LSExt /\
  line_collection_cell_ok segsA segsB (im_bi m) LSBnd LSInt /\
  line_collection_cell_ok segsA segsB (im_bb m) LSBnd LSBnd /\
  line_collection_cell_ok segsA segsB (im_be m) LSBnd LSExt /\
  line_collection_cell_ok segsA segsB (im_ei m) LSExt LSInt /\
  line_collection_cell_ok segsA segsB (im_eb m) LSExt LSBnd /\
  line_collection_cell_ok segsA segsB (im_ee m) LSExt LSExt.

Definition dim_value_join (d1 d2 : DimValue) : DimValue :=
  match d1, d2 with
  | None, d => d
  | d, None => d
  | Some n1, Some n2 => Some (Nat.max n1 n2)
  end.

Lemma dim_value_join_none_left :
  forall d, dim_value_join None d = d.
Proof. intros [n|]; reflexivity. Qed.

Lemma dim_value_join_none_right :
  forall d, dim_value_join d None = d.
Proof. intros [n|]; reflexivity. Qed.

Lemma dim_value_join_commut :
  forall d1 d2, dim_value_join d1 d2 = dim_value_join d2 d1.
Proof.
  intros d1 d2. destruct d1 as [n1|], d2 as [n2|]; simpl; try reflexivity.
  f_equal. lia.
Qed.

Lemma dim_value_join_assoc :
  forall d1 d2 d3,
    dim_value_join (dim_value_join d1 d2) d3 =
    dim_value_join d1 (dim_value_join d2 d3).
Proof.
  intros d1 d2 d3.
  destruct d1 as [n1|], d2 as [n2|], d3 as [n3|]; simpl; try reflexivity.
  f_equal. lia.
Qed.

Lemma dim_value_join_idem :
  forall d, dim_value_join d d = d.
Proof.
  intros [n|]; simpl; [| reflexivity].
  f_equal. lia.
Qed.

Theorem line_collection_pair_cell_sub :
  forall segsA segsB A B C D d sX sY,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_cell_ok d sX sY A B C D ->
    line_collection_cell_ok segsA segsB d sX sY.
Proof.
  intros segsA segsB A B C D d sX sY HinA HinB Hcell.
  exists A; exists B; exists C; exists D.
  split; [exact HinA | split; [exact HinB | exact Hcell]].
Qed.

Theorem line_collection_bnd_int_bi_cell_ok :
  forall segsA segsB,
    line_collection_bnd_int_contact segsA segsB ->
    line_collection_cell_ok segsA segsB (ll_dim0) LSBnd LSInt.
Proof.
  intros segsA segsB [A [B [C [D [HinA [HinB Hcontact]]]]]].
  exists A; exists B; exists C; exists D.
  split; [exact HinA | split; [exact HinB | ]].
  apply segments_bnd_int_bi_cell in Hcontact.
  unfold line_bi_point_cell, ll_matrix_paper_test10 in Hcontact.
  simpl in Hcontact. exact Hcontact.
Qed.

Theorem line_collection_no_share_ie_cell :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    A <> B ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB (ll_dim1) LSInt LSExt.
Proof.
  intros segsA segsB A B C D HinA HinB Hne Hnoshare.
  exists A; exists B; exists C; exists D.
  split; [exact HinA | split; [exact HinB | ]].
  apply no_share_midpoint_ie_cell.
  - exact Hne.
  - apply Hnoshare; assumption.
Qed.

Theorem line_collection_no_share_ei_cell :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    C <> D ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB (ll_dim1) LSExt LSInt.
Proof.
  intros segsA segsB A B C D HinA HinB Hne Hnoshare.
  exists A; exists B; exists C; exists D.
  split; [exact HinA | split; [exact HinB | ]].
  apply no_share_midpoint_ei_cell.
  - exact Hne.
  - apply Hnoshare; assumption.
Qed.

Theorem line_collection_ee_dim2_cell :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_collection_cell_ok segsA segsB (ll_dim2) LSExt LSExt.
Proof.
  intros segsA segsB A B C D HinA HinB.
  exists A; exists B; exists C; exists D.
  split; [exact HinA | split; [exact HinB | apply segments_bounded_ee_dim2_cell]].
Qed.

Theorem line_collection_test10_de9im_rows :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    A <> B ->
    C <> D ->
    line_collection_bnd_int_contact segsA segsB ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB (im_bi ll_matrix_paper_test10) LSBnd LSInt /\
    line_collection_cell_ok segsA segsB (im_ie ll_matrix_paper_test10) LSInt LSExt /\
    line_collection_cell_ok segsA segsB (im_ei ll_matrix_paper_test10) LSExt LSInt /\
    line_collection_cell_ok segsA segsB (im_ee ll_matrix_paper_test10) LSExt LSExt.
Proof.
  intros segsA segsB A B C D HinA HinB HneAB HneCD Hbndint Hnoshare.
  split.
  - apply line_collection_bnd_int_bi_cell_ok. exact Hbndint.
  - split.
    + apply (line_collection_no_share_ie_cell segsA segsB A B C D); assumption.
    + split.
      * apply (line_collection_no_share_ei_cell segsA segsB A B C D); assumption.
      * apply (line_collection_ee_dim2_cell segsA segsB A B C D); assumption.
Qed.

Theorem line_collection_test10_intersects :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    A <> B ->
    line_collection_all_no_share segsA segsB ->
    line_collection_bnd_int_contact segsA segsB ->
    im_intersects ll_matrix_paper_test10.
Proof.
  intros segsA segsB A B C D HinA HinB HneAB Hnoshare Hbndint.
  unfold im_intersects. right; right; left.
  apply intersects3_matches_some_ie with (n := 1%nat).
  unfold ll_matrix_paper_test10. simpl. reflexivity.
Qed.

Theorem line_collection_classify_disjoint_test10_rows :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    classify_line_pair A B C D LPR_Disjoint ->
    A <> B ->
    C <> D ->
    line_collection_bnd_int_contact segsA segsB ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB (im_bi ll_matrix_paper_test10) LSBnd LSInt /\
    line_collection_cell_ok segsA segsB (im_ie ll_matrix_paper_test10) LSInt LSExt /\
    line_collection_cell_ok segsA segsB (im_ei ll_matrix_paper_test10) LSExt LSInt /\
    line_collection_cell_ok segsA segsB (im_ee ll_matrix_paper_test10) LSExt LSExt.
Proof.
  intros segsA segsB A B C D HinA HinB _ HneAB HneCD Hbndint Hnoshare.
  apply (line_collection_test10_de9im_rows segsA segsB A B C D); assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §16  Per-pair 9-cell noding bridges (S15h).                                *)
(* -------------------------------------------------------------------------- *)

Lemma no_share_endpoint_a_exterior_cd :
  forall A B C D, ~ segments_share A B C D -> ~ between C D A.
Proof.
  intros A B C D Hnoshare Hbet.
  apply Hnoshare. exists A. split.
  - apply endpoint_implies_between. apply seg_in_stratum_bnd_left.
  - exact Hbet.
Qed.

Lemma no_share_endpoint_b_exterior_cd :
  forall A B C D, ~ segments_share A B C D -> ~ between C D B.
Proof.
  intros A B C D Hnoshare Hbet.
  apply Hnoshare. exists B. split.
  - apply endpoint_implies_between. apply seg_in_stratum_bnd_right.
  - exact Hbet.
Qed.

Lemma no_share_endpoint_c_exterior_ab :
  forall A B C D, ~ segments_share A B C D -> ~ between A B C.
Proof.
  intros A B C D Hnoshare Hbet.
  apply Hnoshare. exists C. split.
  - exact Hbet.
  - apply endpoint_implies_between. apply seg_in_stratum_bnd_left.
Qed.

Lemma no_share_endpoint_d_exterior_ab :
  forall A B C D, ~ segments_share A B C D -> ~ between A B D.
Proof.
  intros A B C D Hnoshare Hbet.
  apply Hnoshare. exists D. split.
  - exact Hbet.
  - apply endpoint_implies_between. apply seg_in_stratum_bnd_right.
Qed.

Theorem separated_segments_endpoint_exterior_be_eb :
  forall A B C D,
    ~ segments_share A B C D ->
    line_be_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_eb_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hnoshare.
  split.
  - apply endpoint_a_exterior_be_cell.
    exact (no_share_endpoint_a_exterior_cd A B C D Hnoshare).
  - apply endpoint_c_exterior_eb_cell.
    exact (no_share_endpoint_c_exterior_ab A B C D Hnoshare).
Qed.

Theorem classify_disjoint_paper_test10_exterior_rows :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    A <> B ->
    C <> D ->
    line_ie_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_ei_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_be_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_eb_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_ee_dim2_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hdisj HneAB HneCD.
  assert (Hnoshare : ~ segments_share A B C D).
  { intro Hshare. apply (rejection_not_share A B C D). exact Hdisj. exact Hshare. }
  destruct (classify_disjoint_midpoint_ie_ei_cells A B C D Hdisj HneAB HneCD)
    as [Hie Hei].
  destruct (separated_segments_endpoint_exterior_be_eb A B C D Hnoshare)
    as [Hbe Heb].
  split.
  - exact Hie.
  - split.
    + exact Hei.
    + split.
      * exact Hbe.
      * split.
        -- exact Heb.
        -- apply paper_test10_ee_dim2_cell.
Qed.

Theorem classify_disjoint_test10_empty_meet_rows :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    line_cell_ok (im_ii ll_matrix_paper_test10) LSInt LSInt A B C D /\
    line_cell_ok (im_ib ll_matrix_paper_test10) LSInt LSBnd A B C D /\
    line_cell_ok (im_bb ll_matrix_paper_test10) LSBnd LSBnd A B C D.
Proof.
  intros A B C D Hdisj.
  assert (Hnoshare : ~ segments_share A B C D).
  { intro Hshare. apply (rejection_not_share A B C D). exact Hdisj. exact Hshare. }
  unfold im_ii, im_ib, im_bb, ll_matrix_paper_test10. simpl.
  repeat split.
  all: apply (line_cell_ok_none_when _ _ A B C D);
    eauto using no_share_no_int_int, no_share_no_int_bnd, no_share_no_bnd_bnd.
Qed.

Theorem classify_disjoint_line_de9im_pointset_test10 :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    A <> B ->
    C <> D ->
    line_no_ib_meet A B C D (line_pair_fill LPR_Disjoint) /\
    line_ie_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_ei_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_be_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_eb_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_ee_dim2_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hdisj HneAB HneCD.
  split.
  - apply classify_disjoint_line_no_ib_meet. exact Hdisj.
  - apply classify_disjoint_paper_test10_exterior_rows; assumption.
Qed.

Theorem classify_share_endpoint_only_touches_ib :
  forall A B C D,
    classify_line_pair A B C D LPR_Share ->
    segments_int_bnd_contact A B C D ->
    line_ib_point_cell A B C D ll_matrix_touches_endpoint.
Proof.
  intros A B C D _ Hcontact.
  apply segments_int_bnd_touches_ib_cell. exact Hcontact.
Qed.

Theorem classify_share_interior_vs_touches :
  forall A B C D,
    classify_line_pair A B C D LPR_Share ->
    segments_interior_share A B C D ->
    line_ii_point_cell A B C D (line_pair_fill LPR_Share).
Proof.
  intros A B C D Hshare Hint.
  apply classify_share_interior_line_ii_cell; assumption.
Qed.

Theorem classify_share_int_bnd_touches_vs_interior :
  forall A B C D,
    classify_line_pair A B C D LPR_Share ->
    segments_int_bnd_contact A B C D ->
    ~ segments_interior_share A B C D ->
    line_ib_point_cell A B C D ll_matrix_touches_endpoint.
Proof.
  intros A B C D Hshare Hcontact Hnoint.
  apply classify_share_endpoint_only_touches_ib; assumption.
Qed.

Theorem classify_proper_cross_line_de9im_pointset :
  forall A B C D,
    classify_line_pair A B C D LPR_ProperCross ->
    line_point_ii_ib_meet A B C D (line_pair_fill LPR_ProperCross).
Proof.
  intros A B C D Hcross.
  apply classify_proper_cross_line_point_ii_ib_meet. exact Hcross.
Qed.

Theorem segments_collinear_overlap_ee_dim0_cell :
  forall A B C D,
    line_cell_ok (im_ee ll_matrix_overlap_ii) LSExt LSExt A B C D.
Proof.
  intros A B C D.
  unfold im_ee, ll_matrix_overlap_ii. simpl.
  destruct (two_segments_exterior_meet A B C D) as [p [HA HB]].
  apply (line_cell_ok_dim0 LSExt LSExt A B C D p); assumption.
Qed.

Theorem classify_collinear_overlap_line_de9im_pointset :
  forall A B C D,
    classify_line_pair A B C D LPR_CollinearOverlap ->
    C <> D ->
    line_ii_dim1_cell A B C D (line_pair_fill LPR_CollinearOverlap) /\
    line_cell_ok (im_ee (line_pair_fill LPR_CollinearOverlap)) LSExt LSExt A B C D.
Proof.
  intros A B C D Hov Hne.
  rewrite line_pair_fill_collinear_overlap_eq.
  split.
  - apply classify_collinear_overlap_line_ii_cell; assumption.
  - apply segments_collinear_overlap_ee_dim0_cell.
Qed.

(* -------------------------------------------------------------------------- *)
(* §17  Matrix max-join + collection cell join soundness (S15i).              *)
(* -------------------------------------------------------------------------- *)

Definition matrix_dim_join (m1 m2 : IntersectionMatrix) : IntersectionMatrix :=
  {| im_ii := dim_value_join (im_ii m1) (im_ii m2);
     im_ib := dim_value_join (im_ib m1) (im_ib m2);
     im_ie := dim_value_join (im_ie m1) (im_ie m2);
     im_bi := dim_value_join (im_bi m1) (im_bi m2);
     im_bb := dim_value_join (im_bb m1) (im_bb m2);
     im_be := dim_value_join (im_be m1) (im_be m2);
     im_ei := dim_value_join (im_ei m1) (im_ei m2);
     im_eb := dim_value_join (im_eb m1) (im_eb m2);
     im_ee := dim_value_join (im_ee m1) (im_ee m2) |}.

Lemma matrix_dim_join_commut :
  forall m1 m2, matrix_dim_join m1 m2 = matrix_dim_join m2 m1.
Proof.
  intros m1 m2.
  destruct m1 as [ii1 ib1 ie1 bi1 bb1 be1 ei1 eb1 ee1].
  destruct m2 as [ii2 ib2 ie2 bi2 bb2 be2 ei2 eb2 ee2].
  unfold matrix_dim_join. simpl. f_equal.
  all: apply dim_value_join_commut.
Qed.

Lemma matrix_dim_join_assoc :
  forall m1 m2 m3,
    matrix_dim_join (matrix_dim_join m1 m2) m3 =
    matrix_dim_join m1 (matrix_dim_join m2 m3).
Proof.
  intros m1 m2 m3.
  destruct m1 as [ii1 ib1 ie1 bi1 bb1 be1 ei1 eb1 ee1].
  destruct m2 as [ii2 ib2 ie2 bi2 bb2 be2 ei2 eb2 ee2].
  destruct m3 as [ii3 ib3 ie3 bi3 bb3 be3 ei3 eb3 ee3].
  unfold matrix_dim_join. simpl. f_equal.
  all: apply dim_value_join_assoc.
Qed.

Lemma matrix_dim_join_empty_left :
  forall m, matrix_dim_join ll_matrix_disjoint m = m.
Proof.
  intros m.
  destruct m as [ii ib ie bi bb be ei eb ee].
  unfold matrix_dim_join, ll_matrix_disjoint. simpl. f_equal.
  all: apply dim_value_join_none_left.
Qed.

Lemma matrix_dim_join_empty_right :
  forall m, matrix_dim_join m ll_matrix_disjoint = m.
Proof.
  intros m. rewrite matrix_dim_join_commut.
  apply matrix_dim_join_empty_left.
Qed.

Lemma matrix_dim_join_idem :
  forall m, matrix_dim_join m m = m.
Proof.
  intros m.
  destruct m as [ii ib ie bi bb be ei eb ee].
  unfold matrix_dim_join. simpl. f_equal.
  all: apply dim_value_join_idem.
Qed.

Lemma dim_value_ok_join :
  forall d1 d2,
    dim_value_ok d1 ->
    dim_value_ok d2 ->
    dim_value_ok (dim_value_join d1 d2).
Proof.
  intros d1 d2 Hd1 Hd2.
  destruct d1 as [n1|], d2 as [n2|]; simpl; try tauto.
  simpl. unfold dim_value_ok in Hd1, Hd2. simpl in Hd1, Hd2.
  unfold dim_value_ok. simpl.
  destruct (Nat.le_gt_cases n1 n2) as [Hle | Hgt].
  - rewrite Nat.max_r by lia. exact Hd2.
  - rewrite Nat.max_l by lia. exact Hd1.
Qed.

Lemma matrix_dim_join_ok :
  forall m1 m2, matrix_ok m1 -> matrix_ok m2 -> matrix_ok (matrix_dim_join m1 m2).
Proof.
  intros m1 m2.
  intros [Hii1 [Hib1 [Hie1 [Hbi1 [Hbb1 [Hbe1 [Hei1 [Heb1 Hee1]]]]]]]].
  intros [Hii2 [Hib2 [Hie2 [Hbi2 [Hbb2 [Hbe2 [Hei2 [Heb2 Hee2]]]]]]]].
  unfold matrix_ok, matrix_dim_join. repeat split.
  all: apply dim_value_ok_join; assumption.
Qed.

Lemma line_cell_ok_max_dim_right :
  forall n1 n2 sX sY A B C D,
    (n1 <= n2)%nat ->
    line_cell_ok (Some n2) sX sY A B C D ->
    line_cell_ok (Some (Nat.max n1 n2)) sX sY A B C D.
Proof.
  intros n1 n2 sX sY A B C D Hle [Hdok [Hdn Hex]].
  assert (Heq : Nat.max n1 n2 = n2) by lia.
  split.
  - rewrite Heq. exact Hdok.
  - rewrite Heq. split; assumption.
Qed.

Lemma line_cell_ok_max_dim_left :
  forall n1 n2 sX sY A B C D,
    (n2 <= n1)%nat ->
    line_cell_ok (Some n1) sX sY A B C D ->
    line_cell_ok (Some (Nat.max n1 n2)) sX sY A B C D.
Proof.
  intros n1 n2 sX sY A B C D Hle [Hdok [Hdn Hex]].
  assert (Heq : Nat.max n1 n2 = n1) by lia.
  split.
  - rewrite Heq. exact Hdok.
  - rewrite Heq. split; assumption.
Qed.

Theorem line_collection_cell_ok_dim_join :
  forall segsA segsB d1 d2 sX sY,
    line_collection_cell_ok segsA segsB d1 sX sY ->
    line_collection_cell_ok segsA segsB d2 sX sY ->
    line_collection_cell_ok segsA segsB (dim_value_join d1 d2) sX sY.
Proof.
  intros segsA segsB d1 d2 sX sY H1 H2.
  destruct d1 as [n1|], d2 as [n2|]; simpl.
  - destruct (Nat.le_gt_cases n1 n2) as [Hle | Hgt].
    + destruct H2 as [A [B [C [D [HinA [HinB Hcell]]]]]].
      exists A; exists B; exists C; exists D.
      split; [exact HinA | split; [exact HinB | ]].
      apply (line_cell_ok_max_dim_right n1 n2 sX sY A B C D Hle).
      exact Hcell.
    + destruct H1 as [A [B [C [D [HinA [HinB Hcell]]]]]].
      exists A; exists B; exists C; exists D.
      split; [exact HinA | split; [exact HinB | ]].
      apply (line_cell_ok_max_dim_left n1 n2 sX sY A B C D).
      * lia.
      * exact Hcell.
  - exact H1.
  - exact H2.
  - exact H1.
Qed.

Lemma line_de9im_pointset_collection_cells :
  forall segsA segsB A B C D m,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_de9im_pointset A B C D m ->
    line_collection_cell_ok segsA segsB (im_ii m) LSInt LSInt /\
    line_collection_cell_ok segsA segsB (im_ib m) LSInt LSBnd /\
    line_collection_cell_ok segsA segsB (im_ie m) LSInt LSExt /\
    line_collection_cell_ok segsA segsB (im_bi m) LSBnd LSInt /\
    line_collection_cell_ok segsA segsB (im_bb m) LSBnd LSBnd /\
    line_collection_cell_ok segsA segsB (im_be m) LSBnd LSExt /\
    line_collection_cell_ok segsA segsB (im_ei m) LSExt LSInt /\
    line_collection_cell_ok segsA segsB (im_eb m) LSExt LSBnd /\
    line_collection_cell_ok segsA segsB (im_ee m) LSExt LSExt.
Proof.
  intros segsA segsB A B C D m HinA HinB Hps.
  destruct Hps as [Hii [Hib [Hie [Hbi [Hbb [Hbe [Hei [Heb Hee]]]]]]]].
  repeat split.
  all: apply (line_collection_pair_cell_sub segsA segsB A B C D); assumption.
Qed.

Theorem line_collection_de9im_pointset_join :
  forall segsA segsB m1 m2,
    line_collection_de9im_pointset segsA segsB m1 ->
    line_collection_de9im_pointset segsA segsB m2 ->
    line_collection_de9im_pointset segsA segsB (matrix_dim_join m1 m2).
Proof.
  intros segsA segsB m1 m2 H1 H2.
  destruct H1 as [Hii1 [Hib1 [Hie1 [Hbi1 [Hbb1 [Hbe1 [Hei1 [Heb1 Hee1]]]]]]]].
  destruct H2 as [Hii2 [Hib2 [Hie2 [Hbi2 [Hbb2 [Hbe2 [Hei2 [Heb2 Hee2]]]]]]]].
  unfold line_collection_de9im_pointset, matrix_dim_join. simpl.
  repeat split.
  all: apply line_collection_cell_ok_dim_join; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §18  Cross-product matrix fold (S15i).                                       *)
(* -------------------------------------------------------------------------- *)

Fixpoint line_collection_matrix_fold_segsB
    (assign : Point -> Point -> Point -> Point -> IntersectionMatrix)
    (A B : Point) (segsB : list Segment2) : IntersectionMatrix :=
  match segsB with
  | nil => ll_matrix_disjoint
  | (C, D) :: rest =>
      matrix_dim_join (assign A B C D)
        (line_collection_matrix_fold_segsB assign A B rest)
  end.

Fixpoint line_collection_matrix_fold
    (assign : Point -> Point -> Point -> Point -> IntersectionMatrix)
    (segsA segsB : list Segment2) : IntersectionMatrix :=
  match segsA with
  | nil => ll_matrix_disjoint
  | (A, B) :: rest =>
      matrix_dim_join
        (line_collection_matrix_fold assign rest segsB)
        (line_collection_matrix_fold_segsB assign A B segsB)
  end.

Lemma line_collection_cell_ok_segsB_cons :
  forall segsA segsB C0 D0 d sX sY,
    line_collection_cell_ok segsA segsB d sX sY ->
    line_collection_cell_ok segsA ((C0, D0) :: segsB) d sX sY.
Proof.
  intros segsA segsB C0 D0 d sX sY H.
  destruct H as [A [B [C [D [HinA [HinB Hcell]]]]]].
  exists A; exists B; exists C; exists D.
  split.
  - exact HinA.
  - split.
    + right. exact HinB.
    + exact Hcell.
Qed.

Lemma line_collection_de9im_pointset_segsB_cons :
  forall segsA segsB C0 D0 m,
    line_collection_de9im_pointset segsA segsB m ->
    line_collection_de9im_pointset segsA ((C0, D0) :: segsB) m.
Proof.
  intros segsA segsB C0 D0 m H.
  destruct H as [Hii [Hib [Hie [Hbi [Hbb [Hbe [Hei [Heb Hee]]]]]]]].
  repeat split.
  all: apply line_collection_cell_ok_segsB_cons with (C0 := C0) (D0 := D0); assumption.
Qed.

Lemma line_collection_cell_ok_segsA_cons :
  forall segsA segsB A0 B0 d sX sY,
    line_collection_cell_ok segsA segsB d sX sY ->
    line_collection_cell_ok ((A0, B0) :: segsA) segsB d sX sY.
Proof.
  intros segsA segsB A0 B0 d sX sY H.
  destruct H as [A [B [C [D [HinA [HinB Hcell]]]]]].
  exists A; exists B; exists C; exists D.
  split.
  - right. exact HinA.
  - split; [exact HinB | exact Hcell].
Qed.

Lemma line_collection_de9im_pointset_segsA_cons :
  forall segsA segsB A0 B0 m,
    line_collection_de9im_pointset segsA segsB m ->
    line_collection_de9im_pointset ((A0, B0) :: segsA) segsB m.
Proof.
  intros segsA segsB A0 B0 m H.
  destruct H as [Hii [Hib [Hie [Hbi [Hbb [Hbe [Hei [Heb Hee]]]]]]]].
  repeat split.
  all: apply line_collection_cell_ok_segsA_cons with (A0 := A0) (B0 := B0); assumption.
Qed.

Lemma line_de9im_pointset_implies_collection :
  forall segsA segsB A B C D m,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_de9im_pointset A B C D m ->
    line_collection_de9im_pointset segsA segsB m.
Proof.
  intros segsA segsB A B C D m HinA HinB Hps.
  destruct (line_de9im_pointset_collection_cells segsA segsB A B C D m HinA HinB Hps)
    as [Hii [Hib [Hie [Hbi [Hbb [Hbe [Hei [Heb Hee]]]]]]]].
  repeat split; assumption.
Qed.

Lemma line_collection_matrix_fold_segsB_sound :
  forall assign segsA segsB A B,
    In (A, B) segsA ->
    (forall C D,
       In (C, D) segsB ->
       line_de9im_pointset A B C D (assign A B C D)) ->
    (exists C D, In (C, D) segsB) ->
    line_collection_de9im_pointset segsA segsB
      (line_collection_matrix_fold_segsB assign A B segsB).
Proof.
  intros assign segsA segsB A B HinA Hpair HexB.
  induction segsB as [| [C D] rest IH]; simpl.
  - destruct HexB as [C [D H]]. simpl in H. destruct H.
  - destruct HexB as [C0 [D0 HinB]].
    destruct HinB as [Hhead | Htail].
    + inversion Hhead. subst C0 D0.
      destruct rest as [| [C1 D1] rest'].
      * rewrite matrix_dim_join_empty_right.
        apply (line_de9im_pointset_implies_collection segsA ((C, D) :: nil) A B C D
            (assign A B C D)).
        exact HinA. left. reflexivity. apply Hpair. left. reflexivity.
      * apply line_collection_de9im_pointset_join.
        -- apply (line_de9im_pointset_implies_collection segsA ((C, D) :: (C1, D1) :: rest')
            A B C D (assign A B C D)).
           exact HinA. left. reflexivity. apply Hpair. left. reflexivity.
        -- apply line_collection_de9im_pointset_segsB_cons with (C0 := C) (D0 := D).
           apply IH.
           intros C' D' HinB'. apply Hpair. right. exact HinB'.
           exists C1. exists D1. left. reflexivity.
    + apply line_collection_de9im_pointset_join.
      -- apply (line_de9im_pointset_implies_collection segsA ((C, D) :: rest)
          A B C D (assign A B C D)).
         exact HinA. left. reflexivity. apply Hpair. left. reflexivity.
      -- apply line_collection_de9im_pointset_segsB_cons with (C0 := C) (D0 := D).
         apply IH.
         intros C' D' HinB'. apply Hpair. right. exact HinB'.
         exists C0. exists D0. exact Htail.
Qed.

Theorem line_collection_matrix_fold_sound :
  forall assign segsA segsB,
    (exists A B, In (A, B) segsA) ->
    (exists C D, In (C, D) segsB) ->
    (forall A B C D,
       In (A, B) segsA ->
       In (C, D) segsB ->
       line_de9im_pointset A B C D (assign A B C D)) ->
    line_collection_de9im_pointset segsA segsB
      (line_collection_matrix_fold assign segsA segsB).
Proof.
  intros assign segsA segsB HexA HexB Hpair.
  induction segsA as [| [A0 B0] rest IH]; simpl.
  - destruct HexA as [A [B H]]. simpl in H. destruct H.
  - destruct rest as [| [A1 B1] rest'].
    + simpl. rewrite matrix_dim_join_empty_left.
      apply line_collection_matrix_fold_segsB_sound.
      * left. reflexivity.
      * intros C D HinB. apply Hpair; [left; reflexivity | exact HinB].
      * exact HexB.
    + apply line_collection_de9im_pointset_join.
      * apply line_collection_de9im_pointset_segsA_cons with (A0 := A0) (B0 := B0).
        apply IH.
        -- exists A1. exists B1. left. reflexivity.
        -- intros A B C D HinA HinB.
           apply Hpair; [right; exact HinA | exact HinB].
      * apply line_collection_matrix_fold_segsB_sound.
        -- left. reflexivity.
        -- intros C D HinB. apply Hpair; [left; reflexivity | exact HinB].
        -- exact HexB.
Qed.

Theorem line_collection_de9im_pointset_implies_rows :
  forall segsA segsB m,
    line_collection_de9im_pointset segsA segsB m ->
    line_collection_cell_ok segsA segsB (im_bi m) LSBnd LSInt /\
    line_collection_cell_ok segsA segsB (im_ie m) LSInt LSExt /\
    line_collection_cell_ok segsA segsB (im_ei m) LSExt LSInt /\
    line_collection_cell_ok segsA segsB (im_ee m) LSExt LSExt.
Proof.
  intros segsA segsB m H.
  destruct H as [_ [_ [Hie [Hbi [_ [_ [Hei [_ Hee]]]]]]]].
  repeat split; assumption.
Qed.

Theorem line_collection_no_share_empty_meet_cells :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB None LSInt LSInt /\
    line_collection_cell_ok segsA segsB None LSInt LSBnd /\
    line_collection_cell_ok segsA segsB None LSBnd LSBnd.
Proof.
  intros segsA segsB A B C D HinA HinB Hnoshare.
  assert (Hns : ~ segments_share A B C D).
  { apply Hnoshare; assumption. }
  split.
  - apply (line_collection_pair_cell_sub segsA segsB A B C D None LSInt LSInt HinA HinB).
    apply (line_cell_ok_none_when LSInt LSInt A B C D).
    eauto using no_share_no_int_int.
  - split.
    + apply (line_collection_pair_cell_sub segsA segsB A B C D None LSInt LSBnd HinA HinB).
      apply (line_cell_ok_none_when LSInt LSBnd A B C D).
      eauto using no_share_no_int_bnd.
    + apply (line_collection_pair_cell_sub segsA segsB A B C D None LSBnd LSBnd HinA HinB).
      apply (line_cell_ok_none_when LSBnd LSBnd A B C D).
      eauto using no_share_no_bnd_bnd.
Qed.

Theorem line_collection_be_eb_test10_cells :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB (im_be ll_matrix_paper_test10) LSBnd LSExt /\
    line_collection_cell_ok segsA segsB (im_eb ll_matrix_paper_test10) LSExt LSBnd.
Proof.
  intros segsA segsB A B C D HinA HinB Hnoshare.
  assert (Hns : ~ segments_share A B C D).
  { apply Hnoshare; assumption. }
  destruct (separated_segments_endpoint_exterior_be_eb A B C D Hns)
    as [Hbe Heb].
  split.
  - apply (line_collection_pair_cell_sub segsA segsB A B C D
      (im_be ll_matrix_paper_test10) LSBnd LSExt HinA HinB).
    unfold im_be, ll_matrix_paper_test10 in Hbe. simpl. exact Hbe.
  - apply (line_collection_pair_cell_sub segsA segsB A B C D
      (im_eb ll_matrix_paper_test10) LSExt LSBnd HinA HinB).
    unfold im_eb, ll_matrix_paper_test10 in Heb. simpl. exact Heb.
Qed.

Theorem line_collection_test10_de9im_pointset :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    A <> B ->
    C <> D ->
    line_collection_bnd_int_contact segsA segsB ->
    line_collection_all_no_share segsA segsB ->
    line_collection_de9im_pointset segsA segsB ll_matrix_paper_test10.
Proof.
  intros segsA segsB A B C D HinA HinB HneAB HneCD Hbndint Hnoshare.
  unfold line_collection_de9im_pointset.
  destruct (line_collection_no_share_empty_meet_cells segsA segsB A B C D HinA HinB Hnoshare)
    as [Hii [Hib Hbb]].
  destruct (line_collection_test10_de9im_rows segsA segsB A B C D HinA HinB HneAB HneCD Hbndint Hnoshare)
    as [Hbi [Hie [Hei Hee]]].
  destruct (line_collection_be_eb_test10_cells segsA segsB A B C D HinA HinB Hnoshare)
    as [Hbe Heb].
  repeat split.
  - unfold im_ii, ll_matrix_paper_test10. simpl. exact Hii.
  - unfold im_ib, ll_matrix_paper_test10. simpl. exact Hib.
  - exact Hie.
  - exact Hbi.
  - unfold im_bb, ll_matrix_paper_test10. simpl. exact Hbb.
  - exact Hbe.
  - exact Hei.
  - exact Heb.
  - exact Hee.
Qed.

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
Print Assumptions line_collection_pair_cell_sub.
Print Assumptions line_collection_bnd_int_bi_cell_ok.
Print Assumptions line_collection_test10_de9im_rows.
Print Assumptions line_collection_test10_intersects.
Print Assumptions line_collection_classify_disjoint_test10_rows.
Print Assumptions two_segments_exterior_meet.
Print Assumptions line_de9im_ee_inhabited.
Print Assumptions separated_segments_endpoint_exterior_be_eb.
Print Assumptions classify_disjoint_paper_test10_exterior_rows.
Print Assumptions classify_disjoint_line_de9im_pointset_test10.
Print Assumptions classify_share_endpoint_only_touches_ib.
Print Assumptions classify_share_interior_vs_touches.
Print Assumptions classify_proper_cross_line_de9im_pointset.
Print Assumptions classify_collinear_overlap_line_de9im_pointset.
Print Assumptions matrix_dim_join_ok.
Print Assumptions line_collection_de9im_pointset_join.
Print Assumptions line_collection_matrix_fold_sound.
Print Assumptions line_collection_test10_de9im_pointset.
Print Assumptions line_cell_ok_pinned_implies_ok.
Print Assumptions proper_cross_ii_dim_pinned.
Print Assumptions classify_proper_cross_ii_dim_pinned.
Print Assumptions classify_collinear_overlap_ii_dim_pinned.
Print Assumptions line_pair_fill_share_ii_not_pinned_int_bnd_only.
Print Assumptions line_collection_relate_matrix_fold_sound.
Print Assumptions line_collection_relate_matrix_test10.
Print Assumptions line_collection_relate_matrix_test10_intersects.
Print Assumptions line_collection_relate_matrix_regime_fold_sound.