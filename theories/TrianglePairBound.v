(* NetTopologySuite.Proofs.TrianglePairBound
   DE-9IM boundary cells I∩B, B∩I and B∩B for a CCW triangle pair.
   Each cell is an edge-contact test on the clip_halfplane machinery
   (seg_clip_tri / clip_correct). Exterior cells are T1c; the general
   ii_entry_agrees_concrete bridge stays deferred.
   topic: relate
   claimId: tri-de9im-b
   witness: bound_cells_iff
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7), human-reviewed.
   License: BSD-3-Clause *)

From Stdlib Require Import Reals Lra Lia List Bool.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex
  ConvexClip ConvexClipPoly ConvexClipComplete
  DE9IM TrianglePairCommon TrianglePairClip TrianglePairEdge.
Local Open Scope R_scope.

Definition Dim1 : DimValue := Some 1%nat.
Definition Dim0 : DimValue := Some 0%nat.

Definition on_bd (A B C X : Point) : Prop :=
  on_seg A B X \/ on_seg B C X \/ on_seg C A X.

Definition e3 (A B C : Point) : list (Point * Point) :=
  [(A, B); (B, C); (C, A)].

Definition ib_hit (A B C D E F : Point) : bool :=
  edge_meets_open_b A B C D E
  || edge_meets_open_b A B C E F
  || edge_meets_open_b A B C F D.

Definition ib_entry (A B C D E F : Point) : DimValue :=
  if ib_hit A B C D E F then Dim1 else DimF.

Definition bi_entry (A B C D E F : Point) : DimValue :=
  ib_entry D E F A B C.

Definition bb_overlap (A B C D E F : Point) : bool :=
  existsb (fun e =>
    existsb (fun f =>
      overlap_pos_b (fst e) (snd e) (fst f) (snd f)) (e3 D E F))
    (e3 A B C).

Definition bb_touch (A B C D E F : Point) : bool :=
  existsb (fun e =>
    existsb (fun f =>
      proper_cross_b (fst e) (snd e) (fst f) (snd f)
      || endpoint_on_b (fst e) (snd e) (fst f) (snd f)) (e3 D E F))
    (e3 A B C).

Definition bb_entry (A B C D E F : Point) : DimValue :=
  if bb_overlap A B C D E F then Dim1
  else if bb_touch A B C D E F then Dim0 else DimF.

(* T1c reads vertex containment off these three booleans. Exterior cells
   and ii_entry_agrees_concrete (that import would pull RelateMatrixTriangle)
   are the next letter. *)
Definition vtx_in_open_b (A B C X : Point) : bool := tri_open_b A B C X.
Definition vtx_on_bd_b (A B C X : Point) : bool :=
  on_seg_b A B X || on_seg_b B C X || on_seg_b C A X.
Definition vtx_out_b (A B C X : Point) : bool :=
  negb (vtx_in_open_b A B C X || vtx_on_bd_b A B C X).

Lemma vtx_cover : forall A B C X,
  vtx_in_open_b A B C X = true \/
  vtx_on_bd_b A B C X = true \/
  vtx_out_b A B C X = true.
Proof.
  intros A B C X. unfold vtx_out_b.
  destruct (vtx_in_open_b A B C X || vtx_on_bd_b A B C X) eqn:E.
  - apply orb_true_iff in E. destruct E as [E|E].
    + left. exact E.
    + right. left. exact E.
  - right. right. reflexivity.
Qed.

Lemma in_tri_conv : forall A B C P Q t,
  0 <= t <= 1 -> in_tri A B C P -> in_tri A B C Q ->
  in_tri A B C (convex_combination P Q t).
Proof.
  intros A B C P Q t Ht HP HQ. apply in_tri_hull3. apply in_hull_conv.
  - apply in_tri_hull3. exact HP.
  - apply in_tri_hull3. exact HQ.
  - exact Ht.
Qed.

Lemma on_bd_in_tri : forall A B C X, on_bd A B C X -> in_tri A B C X.
Proof.
  intros A B C X [H|[H|H]].
  - apply on_edge_in_tri. exact H.
  - destruct H as [t [Ht ->]]. exists 0, (1 - t), t.
    repeat split; try lra.
    unfold bary3, convex_combination. destruct A, B, C. simpl. f_equal; ring.
  - destruct H as [t [Ht ->]]. exists t, 0, (1 - t).
    repeat split; try lra.
    unfold bary3, convex_combination. destruct A, B, C. simpl. f_equal; ring.
Qed.

Lemma e3_neq : forall A B C e,
  0 < cross A B C -> In e (e3 A B C) -> fst e <> snd e.
Proof.
  intros A B C e Hd Hin.
  destruct (edge_sep A B C Hd) as [Hab [Hbc Hca]].
  simpl in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; simpl; assumption.
Qed.

Lemma seg_e3_bd : forall A B C e X,
  In e (e3 A B C) -> on_seg (fst e) (snd e) X -> on_bd A B C X.
Proof.
  intros A B C e X Hin Hs. simpl in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; simpl in Hs;
    [left | right; left | right; right]; exact Hs.
Qed.

Lemma bd_e3_seg : forall A B C X,
  on_bd A B C X -> exists e, In e (e3 A B C) /\ on_seg (fst e) (snd e) X.
Proof.
  intros A B C X [H|[H|H]].
  - exists (A, B). split; [simpl; left; reflexivity | exact H].
  - exists (B, C). split; [simpl; right; left; reflexivity | exact H].
  - exists (C, A). split; [simpl; right; right; left; reflexivity | exact H].
Qed.

Lemma ib_cell_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  ib_entry A B C D E F = Dim1 <->
  exists X, tri_open A B C X /\ on_bd D E F X.
Proof.
  intros A B C D E F HA HB. split.
  - unfold ib_entry. destruct (ib_hit A B C D E F) eqn:Hh; [| intros contra; discriminate].
    intros _. unfold ib_hit in Hh.
    apply orb_true_iff in Hh. destruct Hh as [Hh|Hh].
    apply orb_true_iff in Hh. destruct Hh as [Hh|Hh].
    + destruct (edge_sep D E F HB) as [Hde _].
      apply edge_open_iff in Hh; try assumption.
      destruct Hh as [X [Ho Hs]]. exists X. split; [exact Ho | left; exact Hs].
    + destruct (edge_sep D E F HB) as [_ [Hef _]].
      apply edge_open_iff in Hh; try assumption.
      destruct Hh as [X [Ho Hs]]. exists X. split; [exact Ho | right; left; exact Hs].
    + destruct (edge_sep D E F HB) as [_ [_ Hfd]].
      apply edge_open_iff in Hh; try assumption.
      destruct Hh as [X [Ho Hs]]. exists X. split; [exact Ho | right; right; exact Hs].
  - intros [X [Ho Hbnd]]. unfold ib_entry.
    assert (Hit : ib_hit A B C D E F = true).
    { unfold ib_hit. destruct Hbnd as [Hs|[Hs|Hs]].
      - destruct (edge_sep D E F HB) as [Hde _].
        apply orb_true_iff. left. apply orb_true_iff. left.
        apply edge_open_iff; try assumption. exists X. split; assumption.
      - destruct (edge_sep D E F HB) as [_ [Hef _]].
        apply orb_true_iff. left. apply orb_true_iff. right.
        apply edge_open_iff; try assumption. exists X. split; assumption.
      - destruct (edge_sep D E F HB) as [_ [_ Hfd]].
        apply orb_true_iff. right.
        apply edge_open_iff; try assumption. exists X. split; assumption. }
    rewrite Hit. reflexivity.
Qed.

Lemma bi_cell_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  bi_entry A B C D E F = Dim1 <->
  exists X, tri_open D E F X /\ on_bd A B C X.
Proof.
  intros A B C D E F HA HB. unfold bi_entry. apply ib_cell_iff; assumption.
Qed.

Lemma bb_overlap_spec : forall A B C D E F,
  bb_overlap A B C D E F = true <->
  exists e f, In e (e3 A B C) /\ In f (e3 D E F) /\
    overlap_pos_b (fst e) (snd e) (fst f) (snd f) = true.
Proof.
  intros A B C D E F. unfold bb_overlap. split.
  - intros H. apply existsb_exists in H. destruct H as [e [He Hf]].
    apply existsb_exists in Hf. destruct Hf as [f [Hf Ho]].
    exists e, f. repeat split; assumption.
  - intros [e [f [He [Hf Ho]]]].
    apply existsb_exists. exists e. split; [exact He|].
    apply existsb_exists. exists f. split; assumption.
Qed.

Lemma bb_touch_spec : forall A B C D E F,
  bb_touch A B C D E F = true <->
  exists e f, In e (e3 A B C) /\ In f (e3 D E F) /\
    (proper_cross_b (fst e) (snd e) (fst f) (snd f)
     || endpoint_on_b (fst e) (snd e) (fst f) (snd f)) = true.
Proof.
  intros A B C D E F. unfold bb_touch. split.
  - intros H. apply existsb_exists in H. destruct H as [e [He Hf]].
    apply existsb_exists in Hf. destruct Hf as [f [Hf Ho]].
    exists e, f. repeat split; assumption.
  - intros [e [f [He [Hf Ho]]]].
    apply existsb_exists. exists e. split; [exact He|].
    apply existsb_exists. exists f. split; assumption.
Qed.

Lemma overlap_segment_bd : forall A B C D E F,
  bb_overlap A B C D E F = true ->
  exists P Q, P <> Q /\
    (exists e, In e (e3 A B C) /\
       forall X, on_seg P Q X -> on_seg (fst e) (snd e) X) /\
    (exists f, In f (e3 D E F) /\
       forall X, on_seg P Q X -> on_seg (fst f) (snd f) X).
Proof.
  intros A B C D E F H.
  apply bb_overlap_spec in H. destruct H as [e [f [He [Hf Ho]]]].
  destruct (overlap_segment (fst e) (snd e) (fst f) (snd f) Ho)
    as [P [Q [Hpq Hall]]].
  exists P, Q. split; [exact Hpq|]. split.
  - exists e. split; [exact He|]. intros X Hs. exact (proj1 (Hall X Hs)).
  - exists f. split; [exact Hf|]. intros X Hs. exact (proj2 (Hall X Hs)).
Qed.

Lemma span_pos : forall x y a b,
  0 <= x <= 1 -> 0 <= y <= 1 -> x <> y ->
  Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
  Rmax 0 (Rmin a b) < Rmin 1 (Rmax a b).
Proof.
  intros x y a b [Hx0 Hx1] [Hy0 Hy1] Hne [Hxlo Hxhi] [Hylo Hyhi].
  set (u := Rmin x y). set (v := Rmax x y).
  assert (Huv : u < v).
  { unfold u, v. destruct (Rle_dec x y) as [H|H].
    - rewrite (Rmin_left x y H), (Rmax_right x y H).
      destruct (Req_dec x y); [contradiction | lra].
    - assert (Hyx : y < x) by (apply Rnot_le_lt; exact H).
      rewrite (Rmin_right x y (Rlt_le _ _ Hyx)).
      rewrite (Rmax_left x y (Rlt_le _ _ Hyx)). lra. }
  assert (Hu0 : 0 <= u).
  { unfold u. destruct (Rle_dec x y) as [H|H].
    - rewrite (Rmin_left x y H). exact Hx0.
    - rewrite (Rmin_right x y (Rlt_le _ _ (Rnot_le_lt _ _ H))). exact Hy0. }
  assert (Hv1 : v <= 1).
  { unfold v. destruct (Rle_dec x y) as [H|H].
    - rewrite (Rmax_right x y H). exact Hy1.
    - rewrite (Rmax_left x y (Rlt_le _ _ (Rnot_le_lt _ _ H))). exact Hx1. }
  assert (Hmu : Rmin a b <= u).
  { unfold u. destruct (Rle_dec x y) as [H|H].
    - rewrite (Rmin_left x y H). exact Hxlo.
    - rewrite (Rmin_right x y (Rlt_le _ _ (Rnot_le_lt _ _ H))). exact Hylo. }
  assert (HvM : v <= Rmax a b).
  { unfold v. destruct (Rle_dec x y) as [H|H].
    - rewrite (Rmax_right x y H). exact Hyhi.
    - rewrite (Rmax_left x y (Rlt_le _ _ (Rnot_le_lt _ _ H))). exact Hxhi. }
  assert (Hlo : Rmax 0 (Rmin a b) <= u).
  { destruct (Rle_dec 0 (Rmin a b)) as [Hm|Hm].
    - rewrite (Rmax_right 0 (Rmin a b) Hm). exact Hmu.
    - rewrite (Rmax_left 0 (Rmin a b) (Rlt_le _ _ (Rnot_le_lt _ _ Hm))). exact Hu0. }
  assert (Hhi : v <= Rmin 1 (Rmax a b)).
  { destruct (Rle_dec 1 (Rmax a b)) as [HM|HM].
    - rewrite (Rmin_left 1 (Rmax a b) HM). exact Hv1.
    - rewrite (Rmin_right 1 (Rmax a b) (Rlt_le _ _ (Rnot_le_lt _ _ HM))). exact HvM. }
  lra.
Qed.

Lemma cross_combo0 : forall A B t, cross A B (convex_combination A B t) = 0.
Proof.
  intros A B t. rewrite cross_combo.
  rewrite (cross_at_P0_is_collinear A B).
  replace (cross A B B) with 0 by (unfold cross; ring). ring.
Qed.

Lemma seg_ends : forall P Q, on_seg P Q P /\ on_seg P Q Q.
Proof.
  intros P Q. split.
  - exists 0. split; [lra | symmetry; apply combo_left].
  - exists 1. split; [lra | symmetry; apply combo_right].
Qed.

Lemma subseg_overlap : forall A B D E P Q,
  A <> B -> D <> E -> P <> Q ->
  on_seg A B P -> on_seg A B Q ->
  on_seg D E P -> on_seg D E Q ->
  overlap_pos_b A B D E = true.
Proof.
  intros A B D E P Q HAB HDE HPQ HPAB HQAB HPDE HQDE.
  assert (Hc : cross P Q D = 0 /\ cross P Q E = 0).
  { apply (line_cross_transfer D E P Q HDE);
      apply on_seg_cross0; assumption. }
  destruct HPAB as [tp [Htp Hp]].
  destruct HQAB as [tq [Htq Hq]].
  destruct HPDE as [rp [Hrp Hpr]].
  destruct HQDE as [rq [Hrq Hqr]].
  assert (Htpq : tp <> tq).
  { intros Eeq. apply HPQ. rewrite Hp, Hq, Eeq. reflexivity. }
  destruct Hc as [HcD HcE].
  assert (Hdpq := dist_pos_neq P Q HPQ).
  assert (HD0 : D = convex_combination P Q (seg_t P Q D))
    by (apply on_line_combo; assumption).
  assert (HE0 : E = convex_combination P Q (seg_t P Q E))
    by (apply on_line_combo; assumption).
  set (sD := seg_t P Q D). set (sE := seg_t P Q E).
  assert (HDab : D = convex_combination A B ((1 - sD) * tp + sD * tq)).
  { rewrite HD0. unfold sD. rewrite Hp, Hq. apply combo_affine. }
  assert (HEab : E = convex_combination A B ((1 - sE) * tp + sE * tq)).
  { rewrite HE0. unfold sE. rewrite Hp, Hq. apply combo_affine. }
  assert (HzABD : cross A B D = 0) by (rewrite HDab; apply cross_combo0).
  assert (HzABE : cross A B E = 0) by (rewrite HEab; apply cross_combo0).
  assert (HdAB := dist_pos_neq A B HAB).
  set (tD := seg_t A B D). set (tE := seg_t A B E).
  assert (EtD : D = convex_combination A B tD) by (apply on_line_combo; assumption).
  assert (EtE : E = convex_combination A B tE) by (apply on_line_combo; assumption).
  assert (EsD : tD = (1 - sD) * tp + sD * tq).
  { apply (combo_inj A B); [exact HAB|]. rewrite <- EtD. exact HDab. }
  assert (EsE : tE = (1 - sE) * tp + sE * tq).
  { apply (combo_inj A B); [exact HAB|]. rewrite <- EtE. exact HEab. }
  assert (Hpm : tp = (1 - rp) * tD + rp * tE).
  { apply (combo_inj A B); [exact HAB|]. rewrite <- Hp, Hpr, EtD, EtE.
    apply combo_affine. }
  assert (Hqm : tq = (1 - rq) * tD + rq * tE).
  { apply (combo_inj A B); [exact HAB|]. rewrite <- Hq, Hqr, EtD, EtE.
    apply combo_affine. }
  assert (Hxp : Rmin tD tE <= tp <= Rmax tD tE).
  { rewrite Hpm. apply mix_bounds. exact Hrp. }
  assert (Hxq : Rmin tD tE <= tq <= Rmax tD tE).
  { rewrite Hqm. apply mix_bounds. exact Hrq. }
  apply overlap_pos_b_true; try assumption.
  apply (span_pos tp tq tD tE); try assumption.
Qed.

Lemma edges_of_segment : forall A B C D E F P Q,
  0 < cross A B C -> 0 < cross D E F -> P <> Q ->
  (exists e, In e (e3 A B C) /\
     forall X, on_seg P Q X -> on_seg (fst e) (snd e) X) ->
  (exists f, In f (e3 D E F) /\
     forall X, on_seg P Q X -> on_seg (fst f) (snd f) X) ->
  bb_overlap A B C D E F = true.
Proof.
  intros A B C D E F P Q HA HB HPQ [e [He HallA]] [f [Hf HallB]].
  assert (HP : on_seg P Q P /\ on_seg P Q Q) by (apply (seg_ends P Q)).
  apply bb_overlap_spec. exists e, f. repeat split; try assumption.
  apply (subseg_overlap (fst e) (snd e) (fst f) (snd f) P Q).
  - apply (e3_neq A B C e); assumption.
  - apply (e3_neq D E F f); assumption.
  - exact HPQ.
  - apply HallA. apply (proj1 HP).
  - apply HallA. apply (proj2 HP).
  - apply HallB. apply (proj1 HP).
  - apply HallB. apply (proj2 HP).
Qed.

Lemma contact_bool : forall A B C D E F X,
  0 < cross A B C -> 0 < cross D E F ->
  on_bd A B C X -> on_bd D E F X ->
  bb_overlap A B C D E F = true \/ bb_touch A B C D E F = true.
Proof.
  intros A B C D E F X HA HB HXA HXB.
  destruct (bd_e3_seg A B C X HXA) as [e [He HsA]].
  destruct (bd_e3_seg D E F X HXB) as [f [Hf HsB]].
  assert (Hne1 : fst e <> snd e) by (apply (e3_neq A B C e); assumption).
  assert (Hne2 : fst f <> snd f) by (apply (e3_neq D E F f); assumption).
  destruct (edge_touch_class (fst e) (snd e) (fst f) (snd f) Hne1 Hne2)
    as [Ho|[Hp|Hee]].
  { exists X. split; assumption. }
  - left. apply bb_overlap_spec. exists e, f. repeat split; assumption.
  - right. apply bb_touch_spec. exists e, f. repeat split; try assumption.
    rewrite Hp. reflexivity.
  - right. apply bb_touch_spec. exists e, f. repeat split; try assumption.
    rewrite Hee. rewrite orb_true_r. reflexivity.
Qed.

Lemma touch_gives_point : forall A B C D E F,
  bb_touch A B C D E F = true ->
  exists X, on_bd A B C X /\ on_bd D E F X.
Proof.
  intros A B C D E F H.
  apply bb_touch_spec in H. destruct H as [e [f [He [Hf Ht]]]].
  apply orb_true_iff in Ht. destruct Ht as [Ht|Ht].
  - destruct (proper_cross_share _ _ _ _ Ht) as [X [HsA HsB]].
    exists X. split; [apply seg_e3_bd with (e := e) | apply seg_e3_bd with (e := f)];
      assumption.
  - destruct (endpoint_share _ _ _ _ Ht) as [X [HsA HsB]].
    exists X. split; [apply seg_e3_bd with (e := e) | apply seg_e3_bd with (e := f)];
      assumption.
Qed.

Lemma bb_dim1_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  bb_entry A B C D E F = Dim1 <->
  exists P Q, P <> Q /\
    (exists e, In e (e3 A B C) /\
       forall X, on_seg P Q X -> on_seg (fst e) (snd e) X) /\
    (exists f, In f (e3 D E F) /\
       forall X, on_seg P Q X -> on_seg (fst f) (snd f) X).
Proof.
  intros A B C D E F HA HB. split.
  - unfold bb_entry. destruct (bb_overlap A B C D E F) eqn:Ho.
    + intros _. apply overlap_segment_bd. exact Ho.
    + destruct (bb_touch A B C D E F); intros contra; discriminate.
  - intros [P [Q [HPQ [He Hf]]]].
    assert (Ho : bb_overlap A B C D E F = true).
    { apply (edges_of_segment A B C D E F P Q); assumption. }
    unfold bb_entry. rewrite Ho. reflexivity.
Qed.

Lemma bb_dimF_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  bb_entry A B C D E F = DimF <->
  ~ exists X, on_bd A B C X /\ on_bd D E F X.
Proof.
  intros A B C D E F HA HB. split.
  - intros Hent [X [HA1 HB1]].
    destruct (contact_bool A B C D E F X HA HB HA1 HB1) as [Ho|Ht].
    + unfold bb_entry in Hent. rewrite Ho in Hent. discriminate.
    + unfold bb_entry in Hent. destruct (bb_overlap A B C D E F).
      * discriminate.
      * rewrite Ht in Hent. discriminate.
  - intros Hempty. unfold bb_entry.
    destruct (bb_overlap A B C D E F) eqn:Ho.
    + exfalso. apply Hempty.
      destruct (overlap_segment_bd A B C D E F Ho) as [P [Q [_ [He Hf]]]].
      destruct He as [e [Hin Hall]]. destruct Hf as [f [Hinf Hallf]].
      assert (HP : on_seg P Q P) by apply (proj1 (seg_ends P Q)).
      exists P. split.
      * apply seg_e3_bd with (e := e); [exact Hin | apply Hall; exact HP].
      * apply seg_e3_bd with (e := f); [exact Hinf | apply Hallf; exact HP].
    + destruct (bb_touch A B C D E F) eqn:Ht.
      * exfalso. apply Hempty. apply touch_gives_point. exact Ht.
      * reflexivity.
Qed.

Lemma bb_dim0_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  bb_entry A B C D E F = Dim0 <->
  (exists X, on_bd A B C X /\ on_bd D E F X) /\
  bb_entry A B C D E F <> Dim1.
Proof.
  intros A B C D E F HA HB. split.
  - intros Hent. split.
    + unfold bb_entry in Hent.
      destruct (bb_overlap A B C D E F) eqn:Ho; [discriminate|].
      destruct (bb_touch A B C D E F) eqn:Ht; [| discriminate].
      apply touch_gives_point. exact Ht.
    + intros E1. rewrite E1 in Hent. discriminate.
  - intros [[X [HXA HXB]] Hnot].
    destruct (contact_bool A B C D E F X HA HB HXA HXB) as [Ho|Ht].
    + exfalso. apply Hnot. unfold bb_entry. rewrite Ho. reflexivity.
    + unfold bb_entry. destruct (bb_overlap A B C D E F) eqn:Ho2.
      * exfalso. apply Hnot. unfold bb_entry. rewrite Ho2. reflexivity.
      * rewrite Ht. reflexivity.
Qed.

Theorem bound_cells_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  (ib_entry A B C D E F = Dim1 <->
     exists X, tri_open A B C X /\ on_bd D E F X) /\
  (bi_entry A B C D E F = Dim1 <->
     exists X, tri_open D E F X /\ on_bd A B C X) /\
  (bb_entry A B C D E F = Dim1 <->
     exists P Q, P <> Q /\
       (exists e, In e (e3 A B C) /\
          forall X, on_seg P Q X -> on_seg (fst e) (snd e) X) /\
       (exists f, In f (e3 D E F) /\
          forall X, on_seg P Q X -> on_seg (fst f) (snd f) X)) /\
  (bb_entry A B C D E F = Dim0 <->
     (exists X, on_bd A B C X /\ on_bd D E F X) /\
     bb_entry A B C D E F <> Dim1) /\
  (bb_entry A B C D E F = DimF <->
     ~ exists X, on_bd A B C X /\ on_bd D E F X).
Proof.
  intros A B C D E F HA HB.
  split; [| split; [| split; [| split]]].
  - apply ib_cell_iff; assumption.
  - apply bi_cell_iff; assumption.
  - apply bb_dim1_iff; assumption.
  - apply bb_dim0_iff; assumption.
  - apply bb_dimF_iff; assumption.
Qed.

Lemma ib_in_tri_inter : forall A B C D E F X,
  0 < cross A B C -> 0 < cross D E F ->
  tri_open A B C X -> on_bd D E F X ->
  in_hull (tri_inter A B C D E F) X.
Proof.
  intros A B C D E F X HA HB Ho Hb.
  apply tri_inter_correct; try assumption. split.
  - apply tri_open_in; assumption.
  - apply on_bd_in_tri. exact Hb.
Qed.

Lemma ib_dim1_at : forall A B C D E F X,
  0 < cross A B C -> 0 < cross D E F ->
  tri_open A B C X -> on_bd D E F X ->
  ib_entry A B C D E F = Dim1.
Proof.
  intros A B C D E F X HA HB Ho Hb.
  apply ib_cell_iff; try assumption. exists X. split; assumption.
Qed.

Lemma edge_blocks_open : forall A B C P Q,
  (cross A B P <= 0 /\ cross A B Q <= 0) \/
  (cross B C P <= 0 /\ cross B C Q <= 0) \/
  (cross C A P <= 0 /\ cross C A Q <= 0) ->
  forall X, on_seg P Q X -> ~ tri_open A B C X.
Proof.
  intros A B C P Q H X Hs [Hab [Hbc Hca]].
  destruct H as [[Hp Hq]|[[Hp Hq]|[Hp Hq]]].
  - apply (Rle_not_lt 0 (cross A B X)).
    + apply (seg_slack_nonpos A B P Q X); assumption.
    + exact Hab.
  - apply (Rle_not_lt 0 (cross B C X)).
    + apply (seg_slack_nonpos B C P Q X); assumption.
    + exact Hbc.
  - apply (Rle_not_lt 0 (cross C A X)).
    + apply (seg_slack_nonpos C A P Q X); assumption.
    + exact Hca.
Qed.

Lemma bd_misses_open : forall A B C D E F,
  ((cross A B D <= 0 /\ cross A B E <= 0) \/
   (cross B C D <= 0 /\ cross B C E <= 0) \/
   (cross C A D <= 0 /\ cross C A E <= 0)) ->
  ((cross A B E <= 0 /\ cross A B F <= 0) \/
   (cross B C E <= 0 /\ cross B C F <= 0) \/
   (cross C A E <= 0 /\ cross C A F <= 0)) ->
  ((cross A B F <= 0 /\ cross A B D <= 0) \/
   (cross B C F <= 0 /\ cross B C D <= 0) \/
   (cross C A F <= 0 /\ cross C A D <= 0)) ->
  forall X, on_bd D E F X -> ~ tri_open A B C X.
Proof.
  intros A B C D E F Hde Hef Hfd X [Hs|[Hs|Hs]].
  - apply (edge_blocks_open A B C D E Hde X Hs).
  - apply (edge_blocks_open A B C E F Hef X Hs).
  - apply (edge_blocks_open A B C F D Hfd X Hs).
Qed.

Lemma ib_dimF_miss : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  (forall X, on_bd D E F X -> ~ tri_open A B C X) ->
  ib_entry A B C D E F = DimF.
Proof.
  intros A B C D E F HA HB Hmiss. unfold ib_entry.
  destruct (ib_hit A B C D E F) eqn:Hh.
  - exfalso.
    assert (Hent : ib_entry A B C D E F = Dim1).
    { unfold ib_entry. rewrite Hh. reflexivity. }
    apply ib_cell_iff in Hent; try assumption.
    destruct Hent as [X [Ho Hb]]. exact (Hmiss X Hb Ho).
  - reflexivity.
Qed.

Lemma seg_slack_neg : forall p q P Q X,
  cross p q P < 0 -> cross p q Q < 0 -> on_seg P Q X -> cross p q X < 0.
Proof.
  intros p q P Q X Hp Hq [t [[Ht0 Ht1] ->]].
  rewrite cross_combo.
  destruct (Req_dec t 0) as [->|Hn0].
  - replace ((1 - 0) * cross p q P + 0 * cross p q Q) with (cross p q P) by ring.
    exact Hp.
  - destruct (Req_dec t 1) as [->|Hn1].
    + replace ((1 - 1) * cross p q P + 1 * cross p q Q) with (cross p q Q) by ring.
      exact Hq.
    + assert (H1 : (1 - t) * cross p q P < (1 - t) * 0).
      { apply Rmult_lt_compat_l; lra. }
      assert (H2 : t * cross p q Q < t * 0).
      { apply Rmult_lt_compat_l; lra. }
      replace ((1 - t) * 0) with 0 in H1 by ring.
      replace (t * 0) with 0 in H2 by ring. lra.
Qed.

Lemma seg_strict_out : forall p q D E F X,
  cross p q D < 0 -> cross p q E < 0 -> cross p q F < 0 ->
  on_bd D E F X -> cross p q X < 0.
Proof.
  intros p q D E F X Hd He Hf [Hs|[Hs|Hs]].
  - apply (seg_slack_neg p q D E X); assumption.
  - apply (seg_slack_neg p q E F X); assumption.
  - apply (seg_slack_neg p q F D X); assumption.
Qed.

Lemma ib_dimF_strict : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  (cross A B D < 0 /\ cross A B E < 0 /\ cross A B F < 0) \/
  (cross B C D < 0 /\ cross B C E < 0 /\ cross B C F < 0) \/
  (cross C A D < 0 /\ cross C A E < 0 /\ cross C A F < 0) ->
  ib_entry A B C D E F = DimF.
Proof.
  intros A B C D E F HA HB H.
  apply ib_dimF_miss; try assumption.
  destruct H as [[Hd [He Hf]] | [[Hd [He Hf]] | [Hd [He Hf]]]].
  - apply bd_misses_open; left; split; apply Rlt_le; assumption.
  - apply bd_misses_open; right; left; split; apply Rlt_le; assumption.
  - apply bd_misses_open; right; right; split; apply Rlt_le; assumption.
Qed.

Lemma bb_dimF_strict : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  (cross A B D < 0 /\ cross A B E < 0 /\ cross A B F < 0) \/
  (cross B C D < 0 /\ cross B C E < 0 /\ cross B C F < 0) \/
  (cross C A D < 0 /\ cross C A E < 0 /\ cross C A F < 0) ->
  bb_entry A B C D E F = DimF.
Proof.
  intros A B C D E F HA HB H.
  apply bb_dimF_iff; try assumption. intros [X [HXA HXB]].
  apply on_bd_in_tri in HXA.
  apply tri_slack_hull in HXA; [| exact HA].
  destruct HXA as [Hab [Hbc Hca]].
  destruct H as [[Hd [He Hf]] | [[Hd [He Hf]] | [Hd [He Hf]]]].
  - exact (Rlt_not_le 0 (cross A B X)
      (seg_strict_out A B D E F X Hd He Hf HXB) Hab).
  - exact (Rlt_not_le 0 (cross B C X)
      (seg_strict_out B C D E F X Hd He Hf HXB) Hbc).
  - exact (Rlt_not_le 0 (cross C A X)
      (seg_strict_out C A D E F X Hd He Hf HXB) Hca).
Qed.

Lemma bb_dim1_ab_de : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  overlap_pos_b A B D E = true ->
  bb_entry A B C D E F = Dim1.
Proof.
  intros A B C D E F HA HB Ho. unfold bb_entry.
  assert (Hov : bb_overlap A B C D E F = true).
  { apply bb_overlap_spec. exists (A, B), (D, E). repeat split.
    - simpl. left. reflexivity.
    - simpl. left. reflexivity.
    - exact Ho. }
  rewrite Hov. reflexivity.
Qed.

Lemma overlap_pos_not_end : forall A B D E,
  cross A B E <> 0 -> overlap_pos_b A B D E = false.
Proof.
  intros A B D E H. unfold overlap_pos_b.
  destruct (point_eqb A B); [reflexivity|].
  destruct (point_eqb D E); [reflexivity|].
  destruct (Req_dec_T (cross A B D) 0) as [_|]; [| reflexivity].
  destruct (Req_dec_T (cross A B E) 0) as [Hz|]; [contradiction | reflexivity].
Qed.

Lemma overlap_pos_off : forall A B D E,
  cross A B D <> 0 \/ cross A B E <> 0 ->
  overlap_pos_b A B D E = false.
Proof.
  intros A B D E [H|H].
  - apply overlap_pos_cross. exact H.
  - apply overlap_pos_not_end. exact H.
Qed.

Lemma overlap_span_false : forall A B D E,
  A <> B -> D <> E ->
  cross A B D = 0 -> cross A B E = 0 ->
  Rmin 1 (Rmax (seg_t A B D) (seg_t A B E)) <=
    Rmax 0 (Rmin (seg_t A B D) (seg_t A B E)) ->
  overlap_pos_b A B D E = false.
Proof.
  intros A B D E HAB HDE Hd He Hle. unfold overlap_pos_b.
  rewrite (point_eqb_false_neq A B HAB).
  rewrite (point_eqb_false_neq D E HDE).
  destruct (Req_dec_T (cross A B D) 0) as [_|Hn]; [| contradiction].
  destruct (Req_dec_T (cross A B E) 0) as [_|Hn]; [| contradiction].
  destruct (Rlt_dec (Rmax 0 (Rmin (seg_t A B D) (seg_t A B E)))
                    (Rmin 1 (Rmax (seg_t A B D) (seg_t A B E))))
    as [Hlt|]; [| reflexivity].
  exfalso. exact (Rle_not_lt _ _ Hle Hlt).
Qed.

Lemma bb_overlap_none : forall A B C D E F,
  overlap_pos_b A B D E = false ->
  overlap_pos_b A B E F = false ->
  overlap_pos_b A B F D = false ->
  overlap_pos_b B C D E = false ->
  overlap_pos_b B C E F = false ->
  overlap_pos_b B C F D = false ->
  overlap_pos_b C A D E = false ->
  overlap_pos_b C A E F = false ->
  overlap_pos_b C A F D = false ->
  bb_overlap A B C D E F = false.
Proof.
  intros A B C D E F H1 H2 H3 H4 H5 H6 H7 H8 H9.
  unfold bb_overlap, e3. simpl.
  rewrite H1, H2, H3, H4, H5, H6, H7, H8, H9. reflexivity.
Qed.

Lemma bb_touch_ab_de : forall A B C D E F,
  endpoint_on_b A B D E = true ->
  bb_touch A B C D E F = true.
Proof.
  intros A B C D E F H. apply bb_touch_spec.
  exists (A, B), (D, E). repeat split.
  - simpl. left. reflexivity.
  - simpl. left. reflexivity.
  - simpl. rewrite H. rewrite orb_true_r. reflexivity.
Qed.

Lemma bb_dim0_flags : forall A B C D E F,
  bb_overlap A B C D E F = false ->
  bb_touch A B C D E F = true ->
  bb_entry A B C D E F = Dim0.
Proof.
  intros A B C D E F Ho Ht. unfold bb_entry. rewrite Ho, Ht. reflexivity.
Qed.

Lemma pts_neq : forall x1 y1 x2 y2,
  x1 <> x2 \/ y1 <> y2 -> mkPoint x1 y1 <> mkPoint x2 y2.
Proof.
  intros x1 y1 x2 y2 [H|H] E.
  - apply H. apply (f_equal px) in E. exact E.
  - apply H. apply (f_equal py) in E. exact E.
Qed.

Ltac bound_area := unfold cross; simpl; lra.
Ltac bound_off :=
  apply overlap_pos_off;
  first [ left; unfold cross; simpl; let H := fresh "Heq" in intros H; lra
        | right; unfold cross; simpl; let H := fresh "Heq" in intros H; lra ].

(* Exterior cells (T1c) and ii_entry_agrees_concrete stay deferred.
   The pairs below are the concrete check: the swapped nest, 522-j in
   both orders, a disjoint pair, and a shared vertex. *)
Lemma bound_entry_fixtures :
  ib_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = Dim1 /\
  bi_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = DimF /\
  bb_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = Dim1 /\
  ib_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = DimF /\
  bi_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = Dim1 /\
  bb_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = Dim1 /\
  ib_entry (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = Dim1 /\
  bi_entry (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = Dim1 /\
  bb_entry (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = Dim0 /\
  ib_entry (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) = Dim1 /\
  bi_entry (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) = Dim1 /\
  bb_entry (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) = Dim0 /\
  ib_entry (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) = DimF /\
  bi_entry (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) = DimF /\
  bb_entry (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) = DimF /\
  ib_entry (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1)
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) = DimF /\
  bi_entry (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1)
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) = DimF /\
  bb_entry (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1)
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) = DimF /\
  ib_entry (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 2 0) (mkPoint 1 1) = DimF /\
  bi_entry (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 2 0) (mkPoint 1 1) = DimF /\
  bb_entry (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 2 0) (mkPoint 1 1) = Dim0.
Proof.
  repeat split.
  - apply ib_dim1_at with (X := mkPoint (5/2) (1/2)).
    + bound_area.
    + bound_area.
    + unfold tri_open, cross; simpl; lra.
    + right. left. exists (1/2). split; [lra|].
      unfold convex_combination. simpl. f_equal; lra.
  - unfold bi_entry. apply ib_dimF_miss; try bound_area. apply bd_misses_open.
    + left. split; bound_area.
    + right. left. split; bound_area.
    + right. right. split; bound_area.
  - apply bb_dim1_ab_de; try bound_area.
    apply overlap_same. apply pts_neq. left. lra.
  - apply ib_dimF_miss; try bound_area. apply bd_misses_open.
    + left. split; bound_area.
    + right. left. split; bound_area.
    + right. right. split; bound_area.
  - unfold bi_entry. apply ib_dim1_at with (X := mkPoint (5/2) (1/2)).
    + bound_area.
    + bound_area.
    + unfold tri_open, cross; simpl; lra.
    + right. left. exists (1/2). split; [lra|].
      unfold convex_combination. simpl. f_equal; lra.
  - apply bb_dim1_ab_de; try bound_area.
    apply overlap_same. apply pts_neq. left. lra.
  - apply ib_dim1_at with (X := mkPoint (3/5) (1/5)).
    + bound_area.
    + bound_area.
    + unfold tri_open, cross; simpl; lra.
    + left. exists (1/5). split; [lra|].
      unfold convex_combination. simpl. f_equal; lra.
  - unfold bi_entry. apply ib_dim1_at with (X := mkPoint 1 1).
    + bound_area.
    + bound_area.
    + unfold tri_open, cross; simpl; lra.
    + right. left. exists (1/2). split; [lra|].
      unfold convex_combination. simpl. f_equal; lra.
  - apply bb_dim0_flags.
    + apply bb_overlap_none; bound_off.
    + apply bb_touch_ab_de. apply endpoint_on_intro. left.
      exact (proj1 (seg_ends (mkPoint 0 0) (mkPoint 2 0))).
  - apply ib_dim1_at with (X := mkPoint 1 1).
    + bound_area.
    + bound_area.
    + unfold tri_open, cross; simpl; lra.
    + right. left. exists (1/2). split; [lra|].
      unfold convex_combination. simpl. f_equal; lra.
  - unfold bi_entry. apply ib_dim1_at with (X := mkPoint (3/5) (1/5)).
    + bound_area.
    + bound_area.
    + unfold tri_open, cross; simpl; lra.
    + left. exists (1/5). split; [lra|].
      unfold convex_combination. simpl. f_equal; lra.
  - apply bb_dim0_flags.
    + apply bb_overlap_none; bound_off.
    + apply bb_touch_ab_de. apply endpoint_on_intro. left.
      exact (proj1 (seg_ends (mkPoint 0 0) (mkPoint 3 1))).
  - apply ib_dimF_strict; [bound_area | bound_area | right; left; repeat split; bound_area].
  - unfold bi_entry.
    apply ib_dimF_strict; [bound_area | bound_area | right; right; repeat split; bound_area].
  - apply bb_dimF_strict; [bound_area | bound_area | right; left; repeat split; bound_area].
  - apply ib_dimF_strict; [bound_area | bound_area | right; right; repeat split; bound_area].
  - unfold bi_entry.
    apply ib_dimF_strict; [bound_area | bound_area | right; left; repeat split; bound_area].
  - apply bb_dimF_strict; [bound_area | bound_area | right; right; repeat split; bound_area].
  - apply ib_dimF_miss; try bound_area. apply bd_misses_open.
    + left. split; bound_area.
    + right. left. split; bound_area.
    + right. left. split; bound_area.
  - unfold bi_entry. apply ib_dimF_miss; try bound_area. apply bd_misses_open.
    + left. split; bound_area.
    + right. right. split; bound_area.
    + right. right. split; bound_area.
  - apply bb_dim0_flags.
    + apply bb_overlap_none.
      * apply overlap_span_false.
        -- apply pts_neq. left. lra.
        -- apply pts_neq. left. lra.
        -- bound_area.
        -- bound_area.
        -- set (A0 := mkPoint 0 0). set (B0 := mkPoint 1 0).
           set (E0 := mkPoint 2 0).
           assert (HAB : A0 <> B0) by (apply pts_neq; left; unfold A0, B0; lra).
           assert (HtD : seg_t A0 B0 B0 = 1) by (apply seg_t_right; exact HAB).
           assert (HtE : seg_t A0 B0 E0 = 2).
           { rewrite <- (seg_t_combo A0 B0 2 (dist_pos_neq A0 B0 HAB)).
             f_equal. unfold A0, B0, E0, convex_combination. simpl. f_equal; lra. }
           rewrite HtD, HtE.
           rewrite (Rmax_right 1 2) by lra.
           rewrite (Rmin_left 1 2) by lra.
           rewrite (Rmax_right 0 1) by lra. lra.
      * bound_off.
      * bound_off.
      * bound_off.
      * bound_off.
      * bound_off.
      * bound_off.
      * bound_off.
      * bound_off.
    + apply bb_touch_ab_de. apply endpoint_on_intro. left.
      exact (proj2 (seg_ends (mkPoint 0 0) (mkPoint 1 0))).
Qed.

(* Assumptions: sig_not_dec, sig_forall_dec, functional_extensionality_dep. *)
Print Assumptions vtx_cover.
Print Assumptions in_tri_conv.
Print Assumptions on_bd_in_tri.
Print Assumptions e3_neq.
Print Assumptions seg_e3_bd.
Print Assumptions bd_e3_seg.
Print Assumptions ib_cell_iff.
Print Assumptions bi_cell_iff.
Print Assumptions bb_overlap_spec.
Print Assumptions bb_touch_spec.
Print Assumptions overlap_segment_bd.
Print Assumptions span_pos.
Print Assumptions cross_combo0.
Print Assumptions seg_ends.
Print Assumptions subseg_overlap.
Print Assumptions edges_of_segment.
Print Assumptions contact_bool.
Print Assumptions touch_gives_point.
Print Assumptions bb_dim1_iff.
Print Assumptions bb_dimF_iff.
Print Assumptions bb_dim0_iff.
Print Assumptions bound_cells_iff.
Print Assumptions ib_in_tri_inter.
Print Assumptions ib_dim1_at.
Print Assumptions edge_blocks_open.
Print Assumptions bd_misses_open.
Print Assumptions ib_dimF_miss.
Print Assumptions seg_slack_neg.
Print Assumptions seg_strict_out.
Print Assumptions ib_dimF_strict.
Print Assumptions bb_dimF_strict.
Print Assumptions bb_dim1_ab_de.
Print Assumptions overlap_pos_not_end.
Print Assumptions overlap_pos_off.
Print Assumptions overlap_span_false.
Print Assumptions bb_overlap_none.
Print Assumptions bb_touch_ab_de.
Print Assumptions bb_dim0_flags.
Print Assumptions pts_neq.
Print Assumptions bound_entry_fixtures.
