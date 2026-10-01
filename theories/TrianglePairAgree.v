(* NetTopologySuite.Proofs.TrianglePairAgree
   For each of the five concrete triangle_pair_fill arms, every cell
   the fill fixes is compared with tri_de9im. Equality is stated where
   it holds. Where it does not, both values are stated.
   The fills are pattern tokens, not these triangles' matrices:
   - Disjoint is the all-empty line matrix. II IB BI BB agree (all F).
     IE BE EI EB EE do not: tri_de9im is 2, 1, 2, 1, 2. EE is Dim2.
   - Overlap is II=2, BB=1, EE=2, and the other six cells F.
     Only II and EE agree. The triangles cross, so IB = BI = 1 and
     BB = 0; the four exterior side cells are 2, 1, 2, 1.
   - Contains is 2FFFFFFF2. II BI BB EI EB EE agree. The inner
     boundary meets the outer interior (IB = 1) and the outer
     triangle meets the exterior (IE = 2, BE = 1).
   - TouchEdge is II=F, BB=1, EE=2, rest F. II IB BI BB EE agree.
     Each triangle meets the other's exterior, so IE EI = 2 and
     BE EB = 1.
   - TouchVertex reuses that BB=1 token. II IB BI EE agree. The
     contact is one point (BB = 0). Exterior cells mismatch as
     in TouchEdge.
   Coordinates: fxA0 fxA1 fxA2 = (0,0)(1,0)(0,1). Disjoint partner
   (2,0)(3,0)(2,1). Overlap (1/4,1/4)(5/4,1/4)(1/4,5/4). Contains
   (1/4,1/4)(1/2,1/4)(1/4,1/2). TouchEdge (1,0)(1,1)(0,1).
   TouchVertex (0,0)(2,0)(0,2) against (0,0)(-2,0)(0,-2).
   tri_de9im_fill_ii_fixtures is one sample pair per arm. The regime
   implication fails on TPR_Contains: contains_b asks only that A be
   CCW and that B's three vertices lie in A's open triangle. A
   clockwise triangle strictly inside A is still TPR_Contains.
   tri_open of a clockwise listing is empty, so ii_entry is DimF,
   while the Contains fill's II cell is Dim2.
   Registered only in _CoqProject.full. RelateMatrixTriangle imports
   GeneralTriangleSeparation, which is outside the host _CoqProject.
   The pinned flocq job compiles _CoqProject.full.
   topic: relate
   claimId: none
   3-axiom. No Admitted. No Jordan in this file's own proof.
   AI-drafted (Cursor Grok 4.7).
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra List Bool.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex ConvexClip DE9IM
  RelateLineLine RelateAreaArea RelateMatrixTriangle TrianglePairCommon
  TrianglePairClip TrianglePairEdge TrianglePairBound TrianglePairExterior.
Local Open Scope R_scope.

Definition disB0 : Point := mkPoint 2 0.
Definition disB1 : Point := mkPoint 3 0.
Definition disB2 : Point := mkPoint 2 1.
Definition ovB0 : Point := mkPoint (1/4) (1/4).
Definition ovB1 : Point := mkPoint (5/4) (1/4).
Definition ovB2 : Point := mkPoint (1/4) (5/4).
Definition coB0 : Point := mkPoint (1/4) (1/4).
Definition coB1 : Point := mkPoint (1/2) (1/4).
Definition coB2 : Point := mkPoint (1/4) (1/2).
Definition teB0 : Point := mkPoint 1 0.
Definition teB1 : Point := mkPoint 1 1.
Definition teB2 : Point := mkPoint 0 1.
Definition tvA0 : Point := mkPoint 0 0.
Definition tvA1 : Point := mkPoint 2 0.
Definition tvA2 : Point := mkPoint 0 2.
Definition tvB0 : Point := mkPoint 0 0.
Definition tvB1 : Point := mkPoint (-2) 0.
Definition tvB2 : Point := mkPoint 0 (-2).

Ltac crs := unfold cross; simpl; lra.

Lemma pos_mix : forall t a b,
  0 <= t <= 1 -> 0 < a -> 0 < b -> 0 < (1 - t) * a + t * b.
Proof.
  intros t a b [Ht0 Ht1] Ha Hb.
  destruct (Req_dec t 0) as [->|Ht0']; [lra|].
  destruct (Req_dec t 1) as [->|Ht1']; [lra|].
  assert (0 < 1 - t) by lra.
  assert (0 < t) by lra.
  assert (0 < (1 - t) * a) by (apply Rmult_lt_0_compat; assumption).
  assert (0 < t * b) by (apply Rmult_lt_0_compat; assumption).
  lra.
Qed.

Lemma open_seg : forall A B C P Q X,
  tri_open A B C P -> tri_open A B C Q -> on_seg P Q X ->
  tri_open A B C X.
Proof.
  intros A B C P Q X [Hpab [Hpbc Hpca]] [Hqab [Hqbc Hqca]]
    [t [[Ht0 Ht1] ->]].
  unfold tri_open. repeat split; rewrite cross_combo;
    apply pos_mix; try assumption; split; assumption.
Qed.

Lemma tri_open_not_bd : forall A B C X,
  tri_open A B C X -> ~ on_bd A B C X.
Proof.
  intros A B C X [Hab [Hbc Hca]] [Hs|[Hs|Hs]].
  - apply on_seg_cross0 in Hs. lra.
  - apply on_seg_cross0 in Hs. lra.
  - apply on_seg_cross0 in Hs. lra.
Qed.

Lemma overlap_collinear_false : forall A B D E tD tE,
  A <> B -> D <> E ->
  D = convex_combination A B tD ->
  E = convex_combination A B tE ->
  ~ Rmax 0 (Rmin tD tE) < Rmin 1 (Rmax tD tE) ->
  overlap_pos_b A B D E = false.
Proof.
  intros A B D E tD tE HAB HDE HD HE Hlt.
  unfold overlap_pos_b.
  rewrite (point_eqb_false_neq A B HAB).
  rewrite (point_eqb_false_neq D E HDE).
  assert (Hd0 : cross A B D = 0) by (rewrite HD; apply cross_combo0).
  assert (He0 : cross A B E = 0) by (rewrite HE; apply cross_combo0).
  destruct (Req_dec_T (cross A B D) 0) as [_|Hn]; [| contradiction].
  destruct (Req_dec_T (cross A B E) 0) as [_|Hn]; [| contradiction].
  rewrite HD, HE.
  rewrite (seg_t_combo A B tD (dist_pos_neq A B HAB)).
  rewrite (seg_t_combo A B tE (dist_pos_neq A B HAB)).
  destruct (Rlt_dec (Rmax 0 (Rmin tD tE)) (Rmin 1 (Rmax tD tE)));
    [contradiction | reflexivity].
Qed.

Lemma tv_ov_base :
  overlap_pos_b tvA0 tvA1 tvB0 tvB1 = false.
Proof.
  apply overlap_collinear_false with (tD := 0) (tE := -1).
  - apply pts_neq. left. crs.
  - apply pts_neq. left. crs.
  - rewrite combo_left. reflexivity.
  - unfold tvA0, tvA1, tvB1, convex_combination. simpl. f_equal; ring.
  - rewrite (Rmin_right 0 (-1)) by lra.
    rewrite (Rmax_left 0 (-1)) by lra.
    rewrite (Rmin_right 1 0) by lra. lra.
Qed.

Lemma tv_ov_side :
  overlap_pos_b tvA2 tvA0 tvB2 tvB0 = false.
Proof.
  apply overlap_collinear_false with (tD := 2) (tE := 1).
  - apply pts_neq. right. crs.
  - apply pts_neq. right. crs.
  - unfold tvA2, tvA0, tvB2, convex_combination. simpl. f_equal; ring.
  - rewrite combo_right. unfold tvA0, tvB0. reflexivity.
  - rewrite (Rmin_right 2 1) by lra.
    rewrite (Rmax_right 0 1) by lra.
    rewrite (Rmax_left 2 1) by lra.
    rewrite (Rmin_left 1 2) by lra. lra.
Qed.

Lemma dis_entries :
  ii_entry fxA0 fxA1 fxA2 disB0 disB1 disB2 = DimF /\
  ib_entry fxA0 fxA1 fxA2 disB0 disB1 disB2 = DimF /\
  ie_entry fxA0 fxA1 fxA2 disB0 disB1 disB2 = Dim2 /\
  bi_entry fxA0 fxA1 fxA2 disB0 disB1 disB2 = DimF /\
  bb_entry fxA0 fxA1 fxA2 disB0 disB1 disB2 = DimF /\
  be_entry fxA0 fxA1 fxA2 disB0 disB1 disB2 = Dim1 /\
  ei_entry fxA0 fxA1 fxA2 disB0 disB1 disB2 = Dim2 /\
  eb_entry fxA0 fxA1 fxA2 disB0 disB1 disB2 = Dim1 /\
  ee_entry fxA0 fxA1 fxA2 disB0 disB1 disB2 = Dim2.
Proof.
  assert (HA : 0 < cross fxA0 fxA1 fxA2) by crs.
  assert (HB : 0 < cross disB0 disB1 disB2) by crs.
  destruct ii_entry_fixtures as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hii _]]]]]]]]].
  assert (HoutA : ~ in_tri disB0 disB1 disB2 fxA0).
  { apply out_of_cross; [exact HB|]. right. right. crs. }
  assert (HoutB : ~ in_tri fxA0 fxA1 fxA2 disB0).
  { apply out_of_cross; [exact HA|]. right. left. crs. }
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  { exact Hii. }
  { apply ib_dimF_miss; try assumption. apply bd_misses_open.
    - right. left. split; crs.
    - right. left. split; crs.
    - right. left. split; crs. }
  { apply (proj2 (ie_cell_iff _ _ _ _ _ _ HA HB)). left. exact HoutA. }
  { unfold bi_entry. apply ib_dimF_miss; try assumption.
    apply bd_misses_open.
    - right. right. split; crs.
    - right. right. split; crs.
    - right. right. split; crs. }
  { apply bb_dimF_strict; try assumption. right. left. repeat split; crs. }
  { apply (proj2 (be_cell_iff _ _ _ _ _ _ HA HB)). left. exact HoutA. }
  { apply (proj2 (ei_cell_iff _ _ _ _ _ _ HA HB)). left. exact HoutB. }
  { apply (proj2 (eb_cell_iff _ _ _ _ _ _ HA HB)). left. exact HoutB. }
  { apply ee_always. }
Qed.

Lemma ov_entries :
  ii_entry fxA0 fxA1 fxA2 ovB0 ovB1 ovB2 = Dim2 /\
  ib_entry fxA0 fxA1 fxA2 ovB0 ovB1 ovB2 = Dim1 /\
  ie_entry fxA0 fxA1 fxA2 ovB0 ovB1 ovB2 = Dim2 /\
  bi_entry fxA0 fxA1 fxA2 ovB0 ovB1 ovB2 = Dim1 /\
  bb_entry fxA0 fxA1 fxA2 ovB0 ovB1 ovB2 = Dim0 /\
  be_entry fxA0 fxA1 fxA2 ovB0 ovB1 ovB2 = Dim1 /\
  ei_entry fxA0 fxA1 fxA2 ovB0 ovB1 ovB2 = Dim2 /\
  eb_entry fxA0 fxA1 fxA2 ovB0 ovB1 ovB2 = Dim1 /\
  ee_entry fxA0 fxA1 fxA2 ovB0 ovB1 ovB2 = Dim2.
Proof.
  assert (HA : 0 < cross fxA0 fxA1 fxA2) by crs.
  assert (HB : 0 < cross ovB0 ovB1 ovB2) by crs.
  destruct ii_entry_fixtures as [Hii _].
  assert (HoutA : ~ in_tri ovB0 ovB1 ovB2 fxA0).
  { apply out_of_cross; [exact HB|]. left. crs. }
  assert (HoutB : ~ in_tri fxA0 fxA1 fxA2 ovB1).
  { apply out_of_cross; [exact HA|]. right. left. crs. }
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  { exact Hii. }
  { apply ib_dim1_at with (X := mkPoint (1/2) (1/4)); try assumption.
    - unfold tri_open. repeat split; crs.
    - left. exists (1/4). split; [lra|].
      unfold convex_combination. simpl. f_equal; field. }
  { apply (proj2 (ie_cell_iff _ _ _ _ _ _ HA HB)). left. exact HoutA. }
  { unfold bi_entry.
    apply ib_dim1_at with (X := mkPoint (1/2) (1/2)); try assumption.
    - unfold tri_open. repeat split; crs.
    - right. left. exists (1/2). split; [lra|].
      unfold convex_combination. simpl. f_equal; field. }
  { apply bb_dim0_flags.
    - unfold bb_overlap, e3. simpl.
      rewrite (overlap_pos_cross fxA0 fxA1 ovB0 ovB1) by crs.
      rewrite (overlap_pos_cross fxA0 fxA1 ovB1 ovB2) by crs.
      rewrite (overlap_pos_cross fxA0 fxA1 ovB2 ovB0) by crs.
      rewrite (overlap_pos_cross fxA1 fxA2 ovB0 ovB1) by crs.
      rewrite (overlap_pos_cross fxA1 fxA2 ovB1 ovB2) by crs.
      rewrite (overlap_pos_cross fxA1 fxA2 ovB2 ovB0) by crs.
      rewrite (overlap_pos_cross fxA2 fxA0 ovB0 ovB1) by crs.
      rewrite (overlap_pos_cross fxA2 fxA0 ovB1 ovB2) by crs.
      rewrite (overlap_pos_cross fxA2 fxA0 ovB2 ovB0) by crs.
      reflexivity.
    - apply bb_touch_spec.
      exists (fxA1, fxA2), (ovB0, ovB1). repeat split.
      + unfold e3. simpl. auto.
      + unfold e3. simpl. auto.
      + simpl. apply orb_true_iff. left.
        apply proper_cross_b_true; crs. }
  { apply (proj2 (be_cell_iff _ _ _ _ _ _ HA HB)). left. exact HoutA. }
  { apply (proj2 (ei_cell_iff _ _ _ _ _ _ HA HB)). right. left. exact HoutB. }
  { apply (proj2 (eb_cell_iff _ _ _ _ _ _ HA HB)). right. left. exact HoutB. }
  { apply ee_always. }
Qed.

Lemma co_entries :
  ii_entry fxA0 fxA1 fxA2 coB0 coB1 coB2 = Dim2 /\
  ib_entry fxA0 fxA1 fxA2 coB0 coB1 coB2 = Dim1 /\
  ie_entry fxA0 fxA1 fxA2 coB0 coB1 coB2 = Dim2 /\
  bi_entry fxA0 fxA1 fxA2 coB0 coB1 coB2 = DimF /\
  bb_entry fxA0 fxA1 fxA2 coB0 coB1 coB2 = DimF /\
  be_entry fxA0 fxA1 fxA2 coB0 coB1 coB2 = Dim1 /\
  ei_entry fxA0 fxA1 fxA2 coB0 coB1 coB2 = DimF /\
  eb_entry fxA0 fxA1 fxA2 coB0 coB1 coB2 = DimF /\
  ee_entry fxA0 fxA1 fxA2 coB0 coB1 coB2 = Dim2.
Proof.
  assert (HA : 0 < cross fxA0 fxA1 fxA2) by crs.
  assert (HB : 0 < cross coB0 coB1 coB2) by crs.
  assert (Ho0 : tri_open fxA0 fxA1 fxA2 coB0).
  { unfold tri_open. repeat split; crs. }
  assert (Ho1 : tri_open fxA0 fxA1 fxA2 coB1).
  { unfold tri_open. repeat split; crs. }
  assert (Ho2 : tri_open fxA0 fxA1 fxA2 coB2).
  { unfold tri_open. repeat split; crs. }
  assert (Hii : ii_entry fxA0 fxA1 fxA2 coB0 coB1 coB2 = Dim2).
  { apply ii_entry_dim2_witness with (X := mkPoint (1/3) (1/3));
      try assumption; unfold tri_open; repeat split; crs. }
  assert (HoutA : ~ in_tri coB0 coB1 coB2 fxA0).
  { apply out_of_cross; [exact HB|]. left. crs. }
  destruct (be_boundary_closed coB0 coB1 coB2 fxA0 fxA1 fxA2 HB HA
    (tri_open_closed _ _ _ _ HA Ho0)
    (tri_open_closed _ _ _ _ HA Ho1)
    (tri_open_closed _ _ _ _ HA Ho2)) as [Heb Hei].
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  { exact Hii. }
  { apply ib_dim1_at with (X := mkPoint (3/8) (1/4)); try assumption.
    - unfold tri_open. repeat split; crs.
    - left. exists (1/2). split; [lra|].
      unfold convex_combination. simpl. f_equal; field. }
  { apply (proj2 (ie_cell_iff _ _ _ _ _ _ HA HB)). left. exact HoutA. }
  { unfold bi_entry. apply ib_dimF_miss; try assumption.
    apply bd_misses_open.
    - left. split; crs.
    - right. left. split; crs.
    - right. right. split; crs. }
  { apply bb_dimF_iff; try assumption. intros [X [Hbig Hsmall]].
    assert (Hop : tri_open fxA0 fxA1 fxA2 X).
    { destruct Hsmall as [Hs|[Hs|Hs]].
      - apply open_seg with (P := coB0) (Q := coB1); assumption.
      - apply open_seg with (P := coB1) (Q := coB2); assumption.
      - apply open_seg with (P := coB2) (Q := coB0); assumption. }
    exact (tri_open_not_bd _ _ _ _ Hop Hbig). }
  { apply (proj2 (be_cell_iff _ _ _ _ _ _ HA HB)). left. exact HoutA. }
  { unfold ei_entry. exact Hei. }
  { unfold eb_entry. exact Heb. }
  { apply ee_always. }
Qed.

Lemma te_entries :
  ii_entry fxA0 fxA1 fxA2 teB0 teB1 teB2 = DimF /\
  ib_entry fxA0 fxA1 fxA2 teB0 teB1 teB2 = DimF /\
  ie_entry fxA0 fxA1 fxA2 teB0 teB1 teB2 = Dim2 /\
  bi_entry fxA0 fxA1 fxA2 teB0 teB1 teB2 = DimF /\
  bb_entry fxA0 fxA1 fxA2 teB0 teB1 teB2 = Dim1 /\
  be_entry fxA0 fxA1 fxA2 teB0 teB1 teB2 = Dim1 /\
  ei_entry fxA0 fxA1 fxA2 teB0 teB1 teB2 = Dim2 /\
  eb_entry fxA0 fxA1 fxA2 teB0 teB1 teB2 = Dim1 /\
  ee_entry fxA0 fxA1 fxA2 teB0 teB1 teB2 = Dim2.
Proof.
  assert (HA : 0 < cross fxA0 fxA1 fxA2) by crs.
  assert (HB : 0 < cross teB0 teB1 teB2) by crs.
  destruct ii_entry_fixtures as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hii _]]]]]]]]]].
  assert (HoutA : ~ in_tri teB0 teB1 teB2 fxA0).
  { apply out_of_cross; [exact HB|]. right. right. crs. }
  assert (HoutB : ~ in_tri fxA0 fxA1 fxA2 teB1).
  { apply out_of_cross; [exact HA|]. right. left. crs. }
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  { exact Hii. }
  { apply ib_dimF_miss; try assumption. apply bd_misses_open.
    - right. left. split; crs.
    - right. left. split; crs.
    - right. left. split; crs. }
  { apply (proj2 (ie_cell_iff _ _ _ _ _ _ HA HB)). left. exact HoutA. }
  { unfold bi_entry. apply ib_dimF_miss; try assumption.
    apply bd_misses_open.
    - right. right. split; crs.
    - right. right. split; crs.
    - right. right. split; crs. }
  { apply (proj2 (bb_dim1_iff _ _ _ _ _ _ HA HB)).
    exists fxA1, fxA2. split.
    - apply pts_neq. left. crs.
    - split.
      + exists (fxA1, fxA2). split.
        * unfold e3. simpl. auto.
        * intros X HX. exact HX.
      + exists (teB2, teB0). split.
        * unfold e3. simpl. auto.
        * intros X HX. apply on_seg_sym. exact HX. }
  { apply (proj2 (be_cell_iff _ _ _ _ _ _ HA HB)). left. exact HoutA. }
  { apply (proj2 (ei_cell_iff _ _ _ _ _ _ HA HB)). right. left. exact HoutB. }
  { apply (proj2 (eb_cell_iff _ _ _ _ _ _ HA HB)). right. left. exact HoutB. }
  { apply ee_always. }
Qed.

Lemma tv_entries :
  ii_entry tvA0 tvA1 tvA2 tvB0 tvB1 tvB2 = DimF /\
  ib_entry tvA0 tvA1 tvA2 tvB0 tvB1 tvB2 = DimF /\
  ie_entry tvA0 tvA1 tvA2 tvB0 tvB1 tvB2 = Dim2 /\
  bi_entry tvA0 tvA1 tvA2 tvB0 tvB1 tvB2 = DimF /\
  bb_entry tvA0 tvA1 tvA2 tvB0 tvB1 tvB2 = Dim0 /\
  be_entry tvA0 tvA1 tvA2 tvB0 tvB1 tvB2 = Dim1 /\
  ei_entry tvA0 tvA1 tvA2 tvB0 tvB1 tvB2 = Dim2 /\
  eb_entry tvA0 tvA1 tvA2 tvB0 tvB1 tvB2 = Dim1 /\
  ee_entry tvA0 tvA1 tvA2 tvB0 tvB1 tvB2 = Dim2.
Proof.
  assert (HA : 0 < cross tvA0 tvA1 tvA2) by crs.
  assert (HB : 0 < cross tvB0 tvB1 tvB2) by crs.
  destruct ii_entry_fixtures as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hii]]]]]]]]]].
  assert (HoutA : ~ in_tri tvB0 tvB1 tvB2 tvA1).
  { apply out_of_cross; [exact HB|]. right. right. crs. }
  assert (HoutB : ~ in_tri tvA0 tvA1 tvA2 tvB1).
  { apply out_of_cross; [exact HA|]. right. right. crs. }
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  { exact Hii. }
  { apply ib_dimF_miss; try assumption. apply bd_misses_open.
    - left. split; crs.
    - left. split; crs.
    - left. split; crs. }
  { apply (proj2 (ie_cell_iff _ _ _ _ _ _ HA HB)). right. left. exact HoutA. }
  { unfold bi_entry. apply ib_dimF_miss; try assumption.
    apply bd_misses_open.
    - right. right. split; crs.
    - right. right. split; crs.
    - right. right. split; crs. }
  { apply bb_dim0_flags.
    - unfold bb_overlap, e3. simpl.
      rewrite tv_ov_base.
      rewrite (overlap_pos_not_end tvA0 tvA1 tvB1 tvB2) by crs.
      rewrite (overlap_pos_cross tvA0 tvA1 tvB2 tvB0) by crs.
      rewrite (overlap_pos_cross tvA1 tvA2 tvB0 tvB1) by crs.
      rewrite (overlap_pos_cross tvA1 tvA2 tvB1 tvB2) by crs.
      rewrite (overlap_pos_cross tvA1 tvA2 tvB2 tvB0) by crs.
      rewrite (overlap_pos_not_end tvA2 tvA0 tvB0 tvB1) by crs.
      rewrite (overlap_pos_cross tvA2 tvA0 tvB1 tvB2) by crs.
      rewrite tv_ov_side. reflexivity.
    - apply bb_touch_spec.
      exists (tvA0, tvA1), (tvB0, tvB1). repeat split.
      + unfold e3. simpl. auto.
      + unfold e3. simpl. auto.
      + simpl. apply orb_true_iff. right.
        apply orb_true_iff. left. apply orb_true_iff. left.
        apply orb_true_iff. left.
        apply on_seg_b_iff. exists 0. split; [lra|].
        rewrite combo_left. reflexivity. }
  { apply (proj2 (be_cell_iff _ _ _ _ _ _ HA HB)). right. left. exact HoutA. }
  { apply (proj2 (ei_cell_iff _ _ _ _ _ _ HA HB)). right. left. exact HoutB. }
  { apply (proj2 (eb_cell_iff _ _ _ _ _ _ HA HB)). right. left. exact HoutB. }
  { apply ee_always. }
Qed.

Ltac close_cell :=
  unfold tri_de9im, triangle_pair_fill; simpl;
  try assumption;
  unfold aa_matrix_disjoint, aa_matrix_partial_overlap, aa_matrix_contains,
    aa_matrix_touch_vertical, ll_matrix_disjoint; simpl;
  unfold ll_cell_empty, aa_cell_empty, aa_dim1, aa_dim2, DimF, Dim0, Dim1, Dim2;
  reflexivity.

Theorem tri_de9im_fill_arms :
  im_ii (tri_de9im fxA0 fxA1 fxA2 disB0 disB1 disB2)
    = im_ii (triangle_pair_fill TPR_Disjoint) /\
  im_ib (tri_de9im fxA0 fxA1 fxA2 disB0 disB1 disB2)
    = im_ib (triangle_pair_fill TPR_Disjoint) /\
  im_bi (tri_de9im fxA0 fxA1 fxA2 disB0 disB1 disB2)
    = im_bi (triangle_pair_fill TPR_Disjoint) /\
  im_bb (tri_de9im fxA0 fxA1 fxA2 disB0 disB1 disB2)
    = im_bb (triangle_pair_fill TPR_Disjoint) /\
  im_ie (tri_de9im fxA0 fxA1 fxA2 disB0 disB1 disB2) = Dim2 /\
  im_ie (triangle_pair_fill TPR_Disjoint) = DimF /\
  im_be (tri_de9im fxA0 fxA1 fxA2 disB0 disB1 disB2) = Dim1 /\
  im_be (triangle_pair_fill TPR_Disjoint) = DimF /\
  im_ei (tri_de9im fxA0 fxA1 fxA2 disB0 disB1 disB2) = Dim2 /\
  im_ei (triangle_pair_fill TPR_Disjoint) = DimF /\
  im_eb (tri_de9im fxA0 fxA1 fxA2 disB0 disB1 disB2) = Dim1 /\
  im_eb (triangle_pair_fill TPR_Disjoint) = DimF /\
  im_ee (tri_de9im fxA0 fxA1 fxA2 disB0 disB1 disB2) = Dim2 /\
  im_ee (triangle_pair_fill TPR_Disjoint) = DimF /\
  im_ii (tri_de9im fxA0 fxA1 fxA2 ovB0 ovB1 ovB2)
    = im_ii (triangle_pair_fill TPR_Overlap) /\
  im_ee (tri_de9im fxA0 fxA1 fxA2 ovB0 ovB1 ovB2)
    = im_ee (triangle_pair_fill TPR_Overlap) /\
  im_ib (tri_de9im fxA0 fxA1 fxA2 ovB0 ovB1 ovB2) = Dim1 /\
  im_ib (triangle_pair_fill TPR_Overlap) = DimF /\
  im_ie (tri_de9im fxA0 fxA1 fxA2 ovB0 ovB1 ovB2) = Dim2 /\
  im_ie (triangle_pair_fill TPR_Overlap) = DimF /\
  im_bi (tri_de9im fxA0 fxA1 fxA2 ovB0 ovB1 ovB2) = Dim1 /\
  im_bi (triangle_pair_fill TPR_Overlap) = DimF /\
  im_bb (tri_de9im fxA0 fxA1 fxA2 ovB0 ovB1 ovB2) = Dim0 /\
  im_bb (triangle_pair_fill TPR_Overlap) = Dim1 /\
  im_be (tri_de9im fxA0 fxA1 fxA2 ovB0 ovB1 ovB2) = Dim1 /\
  im_be (triangle_pair_fill TPR_Overlap) = DimF /\
  im_ei (tri_de9im fxA0 fxA1 fxA2 ovB0 ovB1 ovB2) = Dim2 /\
  im_ei (triangle_pair_fill TPR_Overlap) = DimF /\
  im_eb (tri_de9im fxA0 fxA1 fxA2 ovB0 ovB1 ovB2) = Dim1 /\
  im_eb (triangle_pair_fill TPR_Overlap) = DimF /\
  im_ii (tri_de9im fxA0 fxA1 fxA2 coB0 coB1 coB2)
    = im_ii (triangle_pair_fill TPR_Contains) /\
  im_bi (tri_de9im fxA0 fxA1 fxA2 coB0 coB1 coB2)
    = im_bi (triangle_pair_fill TPR_Contains) /\
  im_bb (tri_de9im fxA0 fxA1 fxA2 coB0 coB1 coB2)
    = im_bb (triangle_pair_fill TPR_Contains) /\
  im_ei (tri_de9im fxA0 fxA1 fxA2 coB0 coB1 coB2)
    = im_ei (triangle_pair_fill TPR_Contains) /\
  im_eb (tri_de9im fxA0 fxA1 fxA2 coB0 coB1 coB2)
    = im_eb (triangle_pair_fill TPR_Contains) /\
  im_ee (tri_de9im fxA0 fxA1 fxA2 coB0 coB1 coB2)
    = im_ee (triangle_pair_fill TPR_Contains) /\
  im_ib (tri_de9im fxA0 fxA1 fxA2 coB0 coB1 coB2) = Dim1 /\
  im_ib (triangle_pair_fill TPR_Contains) = DimF /\
  im_ie (tri_de9im fxA0 fxA1 fxA2 coB0 coB1 coB2) = Dim2 /\
  im_ie (triangle_pair_fill TPR_Contains) = DimF /\
  im_be (tri_de9im fxA0 fxA1 fxA2 coB0 coB1 coB2) = Dim1 /\
  im_be (triangle_pair_fill TPR_Contains) = DimF /\
  im_ii (tri_de9im fxA0 fxA1 fxA2 teB0 teB1 teB2)
    = im_ii (triangle_pair_fill TPR_TouchEdge) /\
  im_ib (tri_de9im fxA0 fxA1 fxA2 teB0 teB1 teB2)
    = im_ib (triangle_pair_fill TPR_TouchEdge) /\
  im_bi (tri_de9im fxA0 fxA1 fxA2 teB0 teB1 teB2)
    = im_bi (triangle_pair_fill TPR_TouchEdge) /\
  im_bb (tri_de9im fxA0 fxA1 fxA2 teB0 teB1 teB2)
    = im_bb (triangle_pair_fill TPR_TouchEdge) /\
  im_ee (tri_de9im fxA0 fxA1 fxA2 teB0 teB1 teB2)
    = im_ee (triangle_pair_fill TPR_TouchEdge) /\
  im_ie (tri_de9im fxA0 fxA1 fxA2 teB0 teB1 teB2) = Dim2 /\
  im_ie (triangle_pair_fill TPR_TouchEdge) = DimF /\
  im_be (tri_de9im fxA0 fxA1 fxA2 teB0 teB1 teB2) = Dim1 /\
  im_be (triangle_pair_fill TPR_TouchEdge) = DimF /\
  im_ei (tri_de9im fxA0 fxA1 fxA2 teB0 teB1 teB2) = Dim2 /\
  im_ei (triangle_pair_fill TPR_TouchEdge) = DimF /\
  im_eb (tri_de9im fxA0 fxA1 fxA2 teB0 teB1 teB2) = Dim1 /\
  im_eb (triangle_pair_fill TPR_TouchEdge) = DimF /\
  im_ii (tri_de9im tvA0 tvA1 tvA2 tvB0 tvB1 tvB2)
    = im_ii (triangle_pair_fill TPR_TouchVertex) /\
  im_ib (tri_de9im tvA0 tvA1 tvA2 tvB0 tvB1 tvB2)
    = im_ib (triangle_pair_fill TPR_TouchVertex) /\
  im_bi (tri_de9im tvA0 tvA1 tvA2 tvB0 tvB1 tvB2)
    = im_bi (triangle_pair_fill TPR_TouchVertex) /\
  im_ee (tri_de9im tvA0 tvA1 tvA2 tvB0 tvB1 tvB2)
    = im_ee (triangle_pair_fill TPR_TouchVertex) /\
  im_ie (tri_de9im tvA0 tvA1 tvA2 tvB0 tvB1 tvB2) = Dim2 /\
  im_ie (triangle_pair_fill TPR_TouchVertex) = DimF /\
  im_bb (tri_de9im tvA0 tvA1 tvA2 tvB0 tvB1 tvB2) = Dim0 /\
  im_bb (triangle_pair_fill TPR_TouchVertex) = Dim1 /\
  im_be (tri_de9im tvA0 tvA1 tvA2 tvB0 tvB1 tvB2) = Dim1 /\
  im_be (triangle_pair_fill TPR_TouchVertex) = DimF /\
  im_ei (tri_de9im tvA0 tvA1 tvA2 tvB0 tvB1 tvB2) = Dim2 /\
  im_ei (triangle_pair_fill TPR_TouchVertex) = DimF /\
  im_eb (tri_de9im tvA0 tvA1 tvA2 tvB0 tvB1 tvB2) = Dim1 /\
  im_eb (triangle_pair_fill TPR_TouchVertex) = DimF.
Proof.
  destruct dis_entries as [Dii [Dib [Die [Dbi [Dbb [Dbe [Dei [Deb Dee]]]]]]]].
  destruct ov_entries as [Oii [Oib [Oie [Obi [Obb [Obe [Oei [Oeb Oee]]]]]]]].
  destruct co_entries as [Cii [Cib [Cie [Cbi [Cbb [Cbe [Cei [Ceb Cee]]]]]]]].
  destruct te_entries as [Eii [Eib [Eie [Ebi [Ebb [Ebe [Eei [Eeb Eee]]]]]]]].
  destruct tv_entries as [Vii [Vib [Vie [Vbi [Vbb [Vbe [Vei [Veb Vee]]]]]]]].
  repeat split; close_cell.
Qed.

Theorem tri_de9im_fill_ii_fixtures :
  im_ii (tri_de9im fxA0 fxA1 fxA2 disB0 disB1 disB2)
    = im_ii (triangle_pair_fill TPR_Disjoint) /\
  im_ii (tri_de9im fxA0 fxA1 fxA2 ovB0 ovB1 ovB2)
    = im_ii (triangle_pair_fill TPR_Overlap) /\
  im_ii (tri_de9im fxA0 fxA1 fxA2 coB0 coB1 coB2)
    = im_ii (triangle_pair_fill TPR_Contains) /\
  im_ii (tri_de9im fxA0 fxA1 fxA2 teB0 teB1 teB2)
    = im_ii (triangle_pair_fill TPR_TouchEdge) /\
  im_ii (tri_de9im tvA0 tvA1 tvA2 tvB0 tvB1 tvB2)
    = im_ii (triangle_pair_fill TPR_TouchVertex).
Proof.
  destruct dis_entries as [Dii _].
  destruct ov_entries as [Oii _].
  destruct co_entries as [Cii _].
  destruct te_entries as [Eii _].
  destruct tv_entries as [Vii _].
  repeat split; close_cell.
Qed.

Print Assumptions pos_mix.
Print Assumptions open_seg.
Print Assumptions tri_open_not_bd.
Print Assumptions overlap_collinear_false.
Print Assumptions tv_ov_base.
Print Assumptions tv_ov_side.
Print Assumptions dis_entries.
Print Assumptions ov_entries.
Print Assumptions co_entries.
Print Assumptions te_entries.
Print Assumptions tv_entries.
Print Assumptions tri_de9im_fill_arms.
Print Assumptions tri_de9im_fill_ii_fixtures.
