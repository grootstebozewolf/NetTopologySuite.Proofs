(* NetTopologySuite.Proofs.TrianglePairMatrix
   Nine-cell correctness of tri_de9im. Each cell is cell_ok against the
   semantic point set: DimF iff empty; Dim0 a point and no positive
   segment; Dim1 a positive segment and no open triangle; Dim2 an open
   triangle. tri_de9im is CCW. tri_de9im_orient_correct is the either-
   winding consumer. Family witness for tri-de9im-a, tri-de9im-b and
   tri-de9im-c.
   topic: relate
   claimId: tri-de9im-a
   witness: tri_de9im_correct
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7).
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra List Bool.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex ConvexClip
  DE9IM TrianglePairCommon TrianglePairClip TrianglePairEdge
  TrianglePairBound TrianglePairExterior.
Local Open Scope R_scope.
Definition pos_seg (S : Point -> Prop) : Prop :=
  exists P Q, P <> Q /\ forall X, on_seg P Q X -> S X.
Definition open2 (S : Point -> Prop) : Prop :=
  exists P Q R, 0 < cross P Q R /\ forall X, tri_open P Q R X -> S X.
Definition cell_ok (d : DimValue) (S : Point -> Prop) : Prop :=
  (d = DimF <-> ~ exists X, S X) /\
  ((exists X, S X) ->
     (d = Dim0 /\ ~ pos_seg S) \/
     (d = Dim1 /\ pos_seg S /\ ~ open2 S) \/
     (d = Dim2 /\ open2 S)).
Definition set_ii (A B C D E F X : Point) : Prop :=
  tri_open A B C X /\ tri_open D E F X.
Definition set_ib (A B C D E F X : Point) : Prop :=
  tri_open A B C X /\ on_bd D E F X.
Definition set_ie (A B C D E F X : Point) : Prop :=
  tri_open A B C X /\ ~ in_tri D E F X.
Definition set_bi (A B C D E F X : Point) : Prop :=
  on_bd A B C X /\ tri_open D E F X.
Definition set_bb (A B C D E F X : Point) : Prop :=
  on_bd A B C X /\ on_bd D E F X.
Definition set_be (A B C D E F X : Point) : Prop :=
  on_bd A B C X /\ ~ in_tri D E F X.
Definition set_ei (A B C D E F X : Point) : Prop :=
  ~ in_tri A B C X /\ tri_open D E F X.
Definition set_eb (A B C D E F X : Point) : Prop :=
  ~ in_tri A B C X /\ on_bd D E F X.
Definition set_ee (A B C D E F X : Point) : Prop :=
  ~ in_tri A B C X /\ ~ in_tri D E F X.
Lemma slack_pos_room : forall sx sg t,
  0 < sx -> 0 <= t -> t < seg_room sx sg ->
  0 < (1 - t) * sx + t * sg.
Proof.
  intros sx sg t Hs Ht0 Ht. unfold seg_room in Ht.
  destruct (Rle_dec 0 (sg - sx)) as [Hg|Hg].
  - replace ((1 - t) * sx + t * sg) with (sx + t * (sg - sx)) by ring.
    assert (0 <= t * (sg - sx)) by (apply Rmult_le_pos; lra). lra.
  - apply Rnot_le_lt in Hg.
    assert (Hnz : sx - sg <> 0) by lra.
    replace ((1 - t) * sx + t * sg)
      with ((sx - sg) * (sx / (sx - sg) - t)) by (field; exact Hnz).
    apply Rmult_lt_0_compat; lra.
Qed.
Lemma seg_from_open : forall A B C I V t,
  0 < cross A B C -> tri_open A B C I -> in_tri A B C V -> 0 <= t < 1 ->
  tri_open A B C (convex_combination I V t).
Proof.
  intros A B C I V t Hd HI HV Ht.
  destruct HI as [Hab [Hbc Hca]].
  destruct (proj2 (tri_slack_hull A B C V Hd) HV) as [Vab [Vbc Vca]].
  repeat split; rewrite cross_combo.
  - assert (0 < (1 - t) * cross A B I) by (apply Rmult_lt_0_compat; lra).
    assert (0 <= t * cross A B V) by (apply Rmult_le_pos; lra). lra.
  - assert (0 < (1 - t) * cross B C I) by (apply Rmult_lt_0_compat; lra).
    assert (0 <= t * cross B C V) by (apply Rmult_le_pos; lra). lra.
  - assert (0 < (1 - t) * cross C A I) by (apply Rmult_lt_0_compat; lra).
    assert (0 <= t * cross C A V) by (apply Rmult_le_pos; lra). lra.
Qed.
Definition eroom (p q X V : Point) : R := seg_room (cross p q X) (cross p q V).
Definition troom (A B C X V : Point) : R :=
  Rmin (eroom A B X V) (Rmin (eroom B C X V) (eroom C A X V)).
Lemma troom_pos : forall A B C X V,
  tri_open A B C X -> 0 < troom A B C X V.
Proof.
  intros A B C X V [Hab [Hbc Hca]]. unfold troom, eroom.
  apply Rmin_pos; [apply seg_room_pos; exact Hab|].
  apply Rmin_pos; apply seg_room_pos; assumption.
Qed.
Lemma nudge_tri_open : forall A B C X V t,
  0 < cross A B C -> tri_open A B C X ->
  0 < t -> t < troom A B C X V ->
  tri_open A B C (convex_combination X V t).
Proof.
  intros A B C X V t Hd HX Ht0 Ht.
  destruct HX as [Hab [Hbc Hca]]. unfold troom in Ht.
  assert (H1 : t < eroom A B X V).
  { eapply Rlt_le_trans; [exact Ht|]. apply Rmin_l. }
  assert (HbcR : t < Rmin (eroom B C X V) (eroom C A X V)).
  { eapply Rlt_le_trans; [exact Ht|]. apply Rmin_r. }
  assert (H2 : t < eroom B C X V).
  { eapply Rlt_le_trans; [exact HbcR|]. apply Rmin_l. }
  assert (H3 : t < eroom C A X V).
  { eapply Rlt_le_trans; [exact HbcR|]. apply Rmin_r. }
  unfold eroom in H1, H2, H3.
  repeat split; rewrite cross_combo; apply slack_pos_room; try lra; assumption.
Qed.
Lemma tri_open_bary : forall A B C P Q R a b c,
  tri_open A B C P -> tri_open A B C Q -> tri_open A B C R ->
  0 <= a -> 0 <= b -> 0 <= c -> a + b + c = 1 ->
  tri_open A B C (bary3 a b c P Q R).
Proof.
  intros A B C P Q R a b c HP HQ HR Ha Hb Hc Hs.
  destruct HP as [Pap [Pbc Pca]]. destruct HQ as [Qap [Qbc Qca]].
  destruct HR as [Rap [Rbc Rca]].
  assert (Hsum : forall sP sQ sR,
      0 < sP -> 0 < sQ -> 0 < sR ->
      0 < a * sP + b * sQ + c * sR).
  { intros sP sQ sR HsP HsQ HsR.
    destruct (Req_dec_T (a * sP + b * sQ + c * sR) 0) as [Hz|Hnz].
    - assert (0 <= a * sP) by (apply Rmult_le_pos; lra).
      assert (0 <= b * sQ) by (apply Rmult_le_pos; lra).
      assert (0 <= c * sR) by (apply Rmult_le_pos; lra).
      assert (Ea : a * sP = 0) by lra.
      assert (Eb : b * sQ = 0) by lra.
      assert (Ec : c * sR = 0) by lra.
      apply Rmult_integral in Ea. apply Rmult_integral in Eb.
      apply Rmult_integral in Ec.
      destruct Ea as [->|Hbad]; [| lra].
      destruct Eb as [->|Hbad]; [| lra].
      destruct Ec as [->|Hbad]; [| lra]. lra.
    - assert (0 <= a * sP + b * sQ + c * sR).
      { apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat|];
          apply Rmult_le_pos; lra. }
      lra. }
  repeat split; rewrite cross_bary3 by exact Hs; apply Hsum; assumption.
Qed.
Lemma neg_bary : forall p q P Q R a b c,
  cross p q P < 0 -> cross p q Q < 0 -> cross p q R < 0 ->
  0 <= a -> 0 <= b -> 0 <= c -> a + b + c = 1 ->
  cross p q (bary3 a b c P Q R) < 0.
Proof.
  intros p q P Q R a b c Hp Hq Hr Ha Hb Hc Hs.
  rewrite cross_bary3 by exact Hs.
  destruct (Req_dec_T (a * cross p q P + b * cross p q Q + c * cross p q R) 0)
    as [Hz|Hnz].
  - assert (a * cross p q P <= 0).
    { replace 0 with (a * 0) by ring. apply Rmult_le_compat_l; lra. }
    assert (b * cross p q Q <= 0).
    { replace 0 with (b * 0) by ring. apply Rmult_le_compat_l; lra. }
    assert (c * cross p q R <= 0).
    { replace 0 with (c * 0) by ring. apply Rmult_le_compat_l; lra. }
    assert (Ea : a * cross p q P = 0) by lra.
    assert (Eb : b * cross p q Q = 0) by lra.
    assert (Ec : c * cross p q R = 0) by lra.
    apply Rmult_integral in Ea. apply Rmult_integral in Eb.
    apply Rmult_integral in Ec.
    destruct Ea as [->|Hbad]; [| lra].
    destruct Eb as [->|Hbad]; [| lra].
    destruct Ec as [->|Hbad]; [| lra]. lra.
  - assert (a * cross p q P + b * cross p q Q + c * cross p q R <= 0).
    { assert (a * cross p q P <= 0).
      { replace 0 with (a * 0) by ring. apply Rmult_le_compat_l; lra. }
      assert (b * cross p q Q <= 0).
      { replace 0 with (b * 0) by ring. apply Rmult_le_compat_l; lra. }
      assert (c * cross p q R <= 0).
      { replace 0 with (c * 0) by ring. apply Rmult_le_compat_l; lra. }
      lra. }
    lra.
Qed.
Lemma below_min6 : forall t a b c d e f,
  t < Rmin a (Rmin b (Rmin c (Rmin d (Rmin e f)))) ->
  t < a /\ t < b /\ t < c /\ t < d /\ t < e /\ t < f.
Proof.
  intros t a b c d e f Ht.
  assert (Ha : t < a) by (eapply Rlt_le_trans; [exact Ht|apply Rmin_l]).
  assert (R1 : t < Rmin b (Rmin c (Rmin d (Rmin e f)))).
  { eapply Rlt_le_trans; [exact Ht|apply Rmin_r]. }
  assert (Hb : t < b) by (eapply Rlt_le_trans; [exact R1|apply Rmin_l]).
  assert (R2 : t < Rmin c (Rmin d (Rmin e f))).
  { eapply Rlt_le_trans; [exact R1|apply Rmin_r]. }
  assert (Hc : t < c) by (eapply Rlt_le_trans; [exact R2|apply Rmin_l]).
  assert (R3 : t < Rmin d (Rmin e f)).
  { eapply Rlt_le_trans; [exact R2|apply Rmin_r]. }
  assert (Hd : t < d) by (eapply Rlt_le_trans; [exact R3|apply Rmin_l]).
  assert (R4 : t < Rmin e f).
  { eapply Rlt_le_trans; [exact R3|apply Rmin_r]. }
  assert (He : t < e) by (eapply Rlt_le_trans; [exact R4|apply Rmin_l]).
  assert (Hf : t < f) by (eapply Rlt_le_trans; [exact R4|apply Rmin_r]).
  repeat split; assumption.
Qed.
Lemma tri_open_of_three : forall A B C P Q R,
  tri_open A B C P -> tri_open A B C Q -> tri_open A B C R ->
  0 < cross P Q R ->
  forall Y, tri_open P Q R Y -> tri_open A B C Y.
Proof.
  intros A B C P Q R HP HQ HR Htri Y HY.
  destruct (tri_bary_recon P Q R Y) as [Hs HYB]; [lra|].
  set (a := cross Q R Y / cross P Q R) in *.
  set (b := cross R P Y / cross P Q R) in *.
  set (c := cross P Q Y / cross P Q R) in *.
  destruct HY as [Ypq [Yqr Yrp]].
  assert (Ha : 0 < a).
  { unfold a. apply Rmult_lt_0_compat; [exact Yqr|apply Rinv_0_lt_compat; exact Htri]. }
  assert (Hb : 0 < b).
  { unfold b. apply Rmult_lt_0_compat; [exact Yrp|apply Rinv_0_lt_compat; exact Htri]. }
  assert (Hc : 0 < c).
  { unfold c. apply Rmult_lt_0_compat; [exact Ypq|apply Rinv_0_lt_compat; exact Htri]. }
  rewrite HYB. apply tri_open_bary; try exact Hs; try assumption.
  - apply Rlt_le. exact Ha. - apply Rlt_le. exact Hb. - apply Rlt_le. exact Hc.
Qed.
Lemma subtri_in : forall A B C X t,
  0 < cross A B C -> tri_open A B C X -> 0 < t ->
  t < troom A B C X A -> t < troom A B C X B -> t < troom A B C X C ->
  0 < cross (convex_combination X A t)
            (convex_combination X B t)
            (convex_combination X C t) /\
  tri_open A B C (convex_combination X A t) /\
  tri_open A B C (convex_combination X B t) /\
  tri_open A B C (convex_combination X C t) /\
  (forall Y,
     tri_open (convex_combination X A t)
              (convex_combination X B t)
              (convex_combination X C t) Y ->
     tri_open A B C Y).
Proof.
  intros A B C X t HA HX Ht HtA HtB HtC.
  set (P := convex_combination X A t) in *.
  set (Q := convex_combination X B t) in *.
  set (R := convex_combination X C t) in *.
  assert (HP : tri_open A B C P) by (apply nudge_tri_open; assumption).
  assert (HQ : tri_open A B C Q) by (apply nudge_tri_open; assumption).
  assert (HR : tri_open A B C R) by (apply nudge_tri_open; assumption).
  assert (Htri : 0 < cross P Q R).
  { unfold P, Q, R. rewrite cross_nudge.
    apply Rmult_lt_0_compat; [| exact HA]. apply Rmult_lt_0_compat; exact Ht. }
  split; [exact Htri|]. split; [exact HP|]. split; [exact HQ|]. split; [exact HR|].
  apply (tri_open_of_three A B C P Q R HP HQ HR Htri).
Qed.
Lemma open2_both : forall A B C D E F X,
  0 < cross A B C -> 0 < cross D E F ->
  tri_open A B C X -> tri_open D E F X ->
  open2 (set_ii A B C D E F).
Proof.
  intros A B C D E F X HA HB HXA HXB.
  set (m := Rmin (troom A B C X A)
            (Rmin (troom A B C X B)
            (Rmin (troom A B C X C)
            (Rmin (troom D E F X A)
            (Rmin (troom D E F X B) (troom D E F X C)))))).
  assert (Hm : 0 < m).
  { unfold m.
    apply Rmin_pos; [apply troom_pos; exact HXA|].
    apply Rmin_pos; [apply troom_pos; exact HXA|].
    apply Rmin_pos; [apply troom_pos; exact HXA|].
    apply Rmin_pos; [apply troom_pos; exact HXB|].
    apply Rmin_pos; [apply troom_pos; exact HXB|].
    apply troom_pos; exact HXB. }
  set (t := m / 2).
  assert (Ht : 0 < t /\ t < m) by (unfold t; lra).
  destruct (below_min6 t _ _ _ _ _ _ (proj2 Ht))
    as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  destruct (subtri_in A B C X t HA HXA (proj1 Ht) H1 H2 H3)
    as [Htri [HPa [HQa [HRa HinA]]]].
  set (P := convex_combination X A t) in *.
  set (Q := convex_combination X B t) in *.
  set (R := convex_combination X C t) in *.
  assert (Ht0 : 0 < t) by exact (proj1 Ht).
  assert (HPd : tri_open D E F P).
  { unfold P. apply nudge_tri_open; try assumption; exact Ht0. }
  assert (HQd : tri_open D E F Q).
  { unfold Q. apply nudge_tri_open; try assumption; exact Ht0. }
  assert (HRd : tri_open D E F R).
  { unfold R. apply nudge_tri_open; try assumption; exact Ht0. }
  exists P, Q, R. split; [exact Htri|]. intros Y HY. split.
  - apply HinA. exact HY. - apply (tri_open_of_three D E F P Q R HPd HQd HRd Htri Y HY).
Qed.
Lemma open2_neg_line : forall A B C D E F X p q,
  0 < cross A B C -> 0 < cross D E F -> tri_open A B C X ->
  cross p q X < 0 ->
  (forall Y, cross p q Y < 0 -> ~ in_tri D E F Y) ->
  open2 (set_ie A B C D E F).
Proof.
  intros A B C D E F X p q HA HB HX Hneg Hout.
  destruct (neg_prefix (cross p q X) (cross p q A) Hneg) as [tA [HtA HallA]].
  destruct (neg_prefix (cross p q X) (cross p q B) Hneg) as [tB [HtB HallB]].
  destruct (neg_prefix (cross p q X) (cross p q C) Hneg) as [tC [HtC HallC]].
  set (m := Rmin (troom A B C X A)
            (Rmin (troom A B C X B)
            (Rmin (troom A B C X C) (Rmin tA (Rmin tB tC))))).
  assert (Hm : 0 < m).
  { unfold m.
    apply Rmin_pos; [apply troom_pos; exact HX|].
    apply Rmin_pos; [apply troom_pos; exact HX|].
    apply Rmin_pos; [apply troom_pos; exact HX|].
    apply Rmin_pos; [exact (proj1 HtA)|].
    apply Rmin_pos; [exact (proj1 HtB)|exact (proj1 HtC)]. }
  set (t := m / 2).
  assert (Ht : 0 < t /\ t < m) by (unfold t; lra).
  destruct (below_min6 t _ _ _ _ _ _ (proj2 Ht))
    as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  destruct (subtri_in A B C X t HA HX (proj1 Ht) H1 H2 H3)
    as [Htri [HP [HQ [HR Hin]]]].
  set (P := convex_combination X A t) in *.
  set (Q := convex_combination X B t) in *.
  set (R := convex_combination X C t) in *.
  assert (HleA : 0 <= t <= tA) by lra.
  assert (HleB : 0 <= t <= tB) by lra.
  assert (HleC : 0 <= t <= tC) by lra.
  assert (HPn : cross p q P < 0).
  { unfold P. rewrite cross_combo. apply HallA. exact HleA. }
  assert (HQn : cross p q Q < 0).
  { unfold Q. rewrite cross_combo. apply HallB. exact HleB. }
  assert (HRn : cross p q R < 0).
  { unfold R. rewrite cross_combo. apply HallC. exact HleC. }
  exists P, Q, R. split; [exact Htri|].
  intros Y HY. split.
  - apply Hin. exact HY. - apply Hout.
    destruct (tri_bary_recon P Q R Y) as [Hs HYB]; [lra|].
    set (a := cross Q R Y / cross P Q R) in *.
    set (b := cross R P Y / cross P Q R) in *.
    set (c := cross P Q Y / cross P Q R) in *.
    destruct HY as [Ypq [Yqr Yrp]].
    assert (Ha : 0 <= a).
    { unfold a. apply Rlt_le, Rmult_lt_0_compat;
        [exact Yqr|apply Rinv_0_lt_compat; exact Htri]. }
    assert (Hb : 0 <= b).
    { unfold b. apply Rlt_le, Rmult_lt_0_compat;
        [exact Yrp|apply Rinv_0_lt_compat; exact Htri]. }
    assert (Hc : 0 <= c).
    { unfold c. apply Rlt_le, Rmult_lt_0_compat;
        [exact Ypq|apply Rinv_0_lt_compat; exact Htri]. }
    rewrite HYB. apply neg_bary; assumption.
Qed.
Lemma open2_out : forall A B C D E F X,
  0 < cross A B C -> 0 < cross D E F ->
  tri_open A B C X -> ~ in_tri D E F X ->
  open2 (set_ie A B C D E F).
Proof.
  intros A B C D E F X HA HB HX Hout.
  destruct (not_in_cross D E F X HB Hout) as [Hc|[Hc|Hc]].
  - apply (open2_neg_line A B C D E F X D E); try assumption.
    intros Y HY. apply (out_of_cross D E F Y HB). left. exact HY.
  - apply (open2_neg_line A B C D E F X E F); try assumption.
    intros Y HY. apply (out_of_cross D E F Y HB). right. left. exact HY.
  - apply (open2_neg_line A B C D E F X F D); try assumption.
    intros Y HY. apply (out_of_cross D E F Y HB). right. right. exact HY.
Qed.
Lemma open2_ee : forall A B C D E F, open2 (set_ee A B C D E F).
Proof.
  intros A B C D E F.
  set (mA := Rmax (px A) (Rmax (px B) (px C))).
  set (mD := Rmax (px D) (Rmax (px E) (px F))).
  set (far := Rmax mA mD + 1).
  set (P := mkPoint (far + 1) 0).
  set (Q := mkPoint (far + 2) 0).
  set (R := mkPoint (far + 1) 1).
  assert (Htri : 0 < cross P Q R) by (unfold P, Q, R, cross; simpl; lra).
  exists P, Q, R. split; [exact Htri|].
  intros Y HY.
  destruct (tri_bary_recon P Q R Y) as [Hs HYB]; [lra|].
  set (a := cross Q R Y / cross P Q R) in *.
  set (b := cross R P Y / cross P Q R) in *.
  set (c := cross P Q Y / cross P Q R) in *.
  destruct HY as [Ypq [Yqr Yrp]].
  assert (Hb : 0 <= b).
  { unfold b. apply Rlt_le, Rmult_lt_0_compat;
      [exact Yrp|apply Rinv_0_lt_compat; exact Htri]. }
  assert (Hpx : far + 1 <= px Y).
  { rewrite HYB. unfold bary3, P, Q, R. simpl.
    replace (a * (far + 1) + b * (far + 2) + c * (far + 1))
      with ((a + b + c) * (far + 1) + b) by ring.
    rewrite Hs. lra. }
  split.
  - intros Hin.
    assert (Hle : px Y <= mA) by (apply (px_in_tri_le A B C Y Hin)).
    assert (Hlt : mA < px Y).
    { apply Rlt_le_trans with (r2 := far + 1); [| exact Hpx].
      assert (Hm : mA <= Rmax mA mD) by apply Rmax_l. unfold far. lra. }
    exact (Rlt_not_le (px Y) mA Hlt Hle).
  - intros Hin.
    assert (Hle : px Y <= mD) by (apply (px_in_tri_le D E F Y Hin)).
    assert (Hlt : mD < px Y).
    { apply Rlt_le_trans with (r2 := far + 1); [| exact Hpx].
      assert (Hm : mD <= Rmax mA mD) by apply Rmax_r. unfold far. lra. }
    exact (Rlt_not_le (px Y) mD Hlt Hle).
Qed.
Lemma vertex_off_line : forall D E P Q R,
  points_distinct D E -> 0 < cross P Q R ->
  cross D E P <> 0 \/ cross D E Q <> 0 \/ cross D E R <> 0.
Proof.
  intros D E P Q R Hd Harea.
  destruct (Req_dec_T (cross D E P) 0) as [Hp|Hp];
  destruct (Req_dec_T (cross D E Q) 0) as [Hq|Hq];
  destruct (Req_dec_T (cross D E R) 0) as [Hr|Hr].
  - exfalso. apply (Rlt_not_eq 0 (cross P Q R) Harea).
    symmetry. apply (three_on_line D E P Q R Hd Hp Hq Hr).
  - right. right. exact Hr. - right. left. exact Hq. - right. left. exact Hq. - left. exact Hp. - left. exact Hp. - left. exact Hp. - left. exact Hp.
Qed.
Lemma vertex_off_pt : forall D E P Q R,
  points_distinct D E -> 0 < cross P Q R ->
  exists V, in_tri P Q R V /\ cross D E V <> 0.
Proof.
  intros D E P Q R Hd Hp.
  destruct (vertex_off_line D E P Q R Hd Hp) as [H|[H|H]].
  - exists P. split; [| exact H]. apply vertex_in_tri. simpl. left. reflexivity.
  - exists Q. split; [| exact H]. apply vertex_in_tri. simpl. right. left. reflexivity. - exists R. split; [| exact H].
    apply vertex_in_tri. simpl. right. right. left. reflexivity.
Qed.
Lemma aff_two_roots : forall s u t1 t2,
  t1 <> t2 ->
  (1 - t1) * s + t1 * u = 0 ->
  (1 - t2) * s + t2 * u = 0 ->
  s = 0.
Proof.
  intros s u t1 t2 Hneq H1 H2.
  assert (E : ((1 - t1) * s + t1 * u) - ((1 - t2) * s + t2 * u)
              = (t2 - t1) * (s - u)) by ring.
  assert (Hz : (t2 - t1) * (s - u) = 0) by lra.
  apply Rmult_integral in Hz. destruct Hz as [Ht|Hu].
  - exfalso. apply Hneq. symmetry. apply Rminus_diag_uniq. exact Ht. - assert (Hsu : s = u) by (apply Rminus_diag_uniq; exact Hu).
    rewrite <- Hsu in H1.
    replace ((1 - t1) * s + t1 * s) with s in H1 by ring. exact H1.
Qed.
Lemma pick_one : forall s u,
  s <> 0 ->
  (1 - 1 / 2) * s + (1 / 2) * u <> 0 \/
  (1 - 1 / 3) * s + (1 / 3) * u <> 0.
Proof.
  intros s u Hs.
  destruct (Req_dec_T ((1 - 1 / 2) * s + (1 / 2) * u) 0) as [H2|H2];
  destruct (Req_dec_T ((1 - 1 / 3) * s + (1 / 3) * u) 0) as [H3|H3].
  - exfalso. apply Hs.
    apply (aff_two_roots s u (1 / 2) (1 / 3)); try lra; assumption.
  - right. exact H3. - left. exact H2. - left. exact H2.
Qed.
Lemma pick_safe_t : forall s1 u1 s2 u2,
  s1 <> 0 -> s2 <> 0 ->
  ((1 - 1 / 2) * s1 + (1 / 2) * u1 <> 0 /\
   (1 - 1 / 2) * s2 + (1 / 2) * u2 <> 0) \/
  ((1 - 1 / 3) * s1 + (1 / 3) * u1 <> 0 /\
   (1 - 1 / 3) * s2 + (1 / 3) * u2 <> 0) \/
  ((1 - 1 / 4) * s1 + (1 / 4) * u1 <> 0 /\
   (1 - 1 / 4) * s2 + (1 / 4) * u2 <> 0).
Proof.
  intros s1 u1 s2 u2 Hs1 Hs2.
  set (f := fun (s u t : R) => (1 - t) * s + t * u).
  assert (H :
    (f s1 u1 (1 / 2) <> 0 /\ f s2 u2 (1 / 2) <> 0) \/
    (f s1 u1 (1 / 3) <> 0 /\ f s2 u2 (1 / 3) <> 0) \/
    (f s1 u1 (1 / 4) <> 0 /\ f s2 u2 (1 / 4) <> 0)).
  { destruct (Req_dec_T (f s1 u1 (1 / 2)) 0) as [A2|A2].
    - destruct (Req_dec_T (f s1 u1 (1 / 3)) 0) as [A3|A3].
      + exfalso. apply Hs1. unfold f in A2, A3.
        apply (aff_two_roots s1 u1 (1 / 2) (1 / 3)); [lra|exact A2|exact A3].
      + destruct (Req_dec_T (f s2 u2 (1 / 3)) 0) as [B3|B3].
        * destruct (Req_dec_T (f s1 u1 (1 / 4)) 0) as [A4|A4].
          -- exfalso. apply Hs1. unfold f in A2, A4.
             apply (aff_two_roots s1 u1 (1 / 2) (1 / 4)); [lra|exact A2|exact A4].
          -- destruct (Req_dec_T (f s2 u2 (1 / 4)) 0) as [B4|B4].
             ++ exfalso. apply Hs2. unfold f in B3, B4.
                apply (aff_two_roots s2 u2 (1 / 3) (1 / 4)); [lra|exact B3|exact B4].
             ++ right. right. split; assumption.
        * right. left. split; assumption.
    - destruct (Req_dec_T (f s2 u2 (1 / 2)) 0) as [B2|B2].
      + destruct (Req_dec_T (f s2 u2 (1 / 3)) 0) as [B3|B3].
        * exfalso. apply Hs2. unfold f in B2, B3.
          apply (aff_two_roots s2 u2 (1 / 2) (1 / 3)); [lra|exact B2|exact B3].
        * destruct (Req_dec_T (f s1 u1 (1 / 3)) 0) as [A3|A3].
          -- destruct (Req_dec_T (f s1 u1 (1 / 4)) 0) as [A4|A4].
             ++ exfalso. apply Hs1. unfold f in A3, A4.
                apply (aff_two_roots s1 u1 (1 / 3) (1 / 4)); [lra|exact A3|exact A4].
             ++ destruct (Req_dec_T (f s2 u2 (1 / 4)) 0) as [B4|B4].
                ** exfalso. apply Hs2. unfold f in B2, B4.
                   apply (aff_two_roots s2 u2 (1 / 2) (1 / 4)); [lra|exact B2|exact B4].
                ** right. right. split; assumption.
          -- right. left. split; assumption.
      + left. split; assumption. }
  unfold f in H. exact H.
Qed.
Lemma pick_keep : forall s u,
  s <> 0 -> exists t, 0 < t < 1 /\ (1 - t) * s + t * u <> 0.
Proof.
  intros s u Hs. destruct (pick_one s u Hs) as [H|H].
  - exists (1 / 2). split; [lra|exact H]. - exists (1 / 3). split; [lra|exact H].
Qed.
Lemma off_by : forall a b, a <> 0 -> b <> 0 -> a * b <> 0.
Proof.
  intros a b Ha Hb Hz. apply Rmult_integral in Hz. destruct Hz; contradiction.
Qed.
Lemma on_bd_some_cross0 : forall D E F X,
  on_bd D E F X ->
  cross D E X = 0 \/ cross E F X = 0 \/ cross F D X = 0.
Proof.
  intros D E F X [H|[H|H]]; [left|right; left|right; right];
    apply on_seg_cross0; exact H.
Qed.
Lemma not_all_edge_cross0 : forall D E F X,
  0 < cross D E F ->
  ~ (cross D E X = 0 /\ cross E F X = 0 /\ cross F D X = 0).
Proof.
  intros D E F X Hd [H1 [H2 H3]].
  assert (Hs := cross_sum3 D E F X). lra.
Qed.
Lemma crosses_off_bd : forall D E F Y,
  cross D E Y <> 0 -> cross E F Y <> 0 -> cross F D Y <> 0 ->
  ~ on_bd D E F Y.
Proof.
  intros D E F Y H1 H2 H3 Hb.
  destruct (on_bd_some_cross0 D E F Y Hb) as [H|[H|H]]; contradiction.
Qed.
Lemma mix_off_two : forall c1d c1e c2d c2e,
  c1d <> 0 -> c2e <> 0 ->
  exists s, 0 < s < 1 /\
    (1 - s) * c1d + s * c1e <> 0 /\
    (1 - s) * c2d + s * c2e <> 0.
Proof.
  intros c1d c1e c2d c2e H1 H2.
  destruct (Req_dec_T c2d 0) as [Z2|N2].
  - destruct (pick_one c1d c1e H1) as [P2|P3].
    + exists (1 / 2). split; [lra|]. split; [exact P2|].
      rewrite Z2.
      replace ((1 - 1 / 2) * 0 + (1 / 2) * c2e) with ((1 / 2) * c2e) by lra.
      apply off_by; [lra|exact H2].
    + exists (1 / 3). split; [lra|]. split; [exact P3|].
      rewrite Z2.
      replace ((1 - 1 / 3) * 0 + (1 / 3) * c2e) with ((1 / 3) * c2e) by lra.
      apply off_by; [lra|exact H2].
  - destruct (Req_dec_T c1e 0) as [Z1|N1].
    + destruct (pick_one c2d c2e N2) as [P2|P3].
      * exists (1 / 2). split; [lra|]. split.
        -- rewrite Z1.
           replace ((1 - 1 / 2) * c1d + (1 / 2) * 0) with ((1 / 2) * c1d) by lra.
           apply off_by; [lra|exact H1].
        -- exact P2.
      * exists (1 / 3). split; [lra|]. split.
        -- rewrite Z1.
           replace ((1 - 1 / 3) * c1d + (1 / 3) * 0) with ((2 / 3) * c1d) by lra.
           apply off_by; [lra|exact H1].
        -- exact P3.
    + destruct (pick_safe_t c1d c1e c2d c2e H1 N2) as [[A B]|[[A B]|[A B]]].
      * exists (1 / 2). split; [lra|]. split; assumption. * exists (1 / 3). split; [lra|]. split; assumption.
      * exists (1 / 4). split; [lra|]. split; assumption.
Qed.
Lemma flee_one : forall D E F P Q R I V,
  0 < cross P Q R -> tri_open P Q R I -> in_tri P Q R V ->
  cross D E I = 0 -> cross D E V <> 0 ->
  cross E F I <> 0 -> cross F D I <> 0 ->
  exists Y, tri_open P Q R Y /\ ~ on_bd D E F Y.
Proof.
  intros D E F P Q R I V Hp HI HV Hde HV0 Hef Hfd.
  assert (Ht : exists t, 0 < t < 1 /\
      (1 - t) * cross E F I + t * cross E F V <> 0 /\
      (1 - t) * cross F D I + t * cross F D V <> 0).
  { destruct (pick_safe_t (cross E F I) (cross E F V)
                          (cross F D I) (cross F D V) Hef Hfd)
      as [[A B]|[[A B]|[A B]]].
    - exists (1 / 2). split; [lra|]. split; assumption. - exists (1 / 3). split; [lra|]. split; assumption.
    - exists (1 / 4). split; [lra|]. split; assumption. }
  destruct Ht as [t [Htb [HefY HfdY]]].
  set (Y := convex_combination I V t). exists Y. split.
  - apply seg_from_open; try assumption. lra. - apply crosses_off_bd.
    + unfold Y. rewrite cross_combo. rewrite Hde.
      replace ((1 - t) * 0 + t * cross D E V) with (t * cross D E V) by ring.
      apply off_by; [lra|exact HV0].
    + unfold Y. rewrite cross_combo. exact HefY. + unfold Y. rewrite cross_combo. exact HfdY.
Qed.
Lemma flee_two : forall D E F P Q R I,
  0 < cross D E F -> 0 < cross P Q R -> tri_open P Q R I ->
  cross D E I = 0 -> cross E F I = 0 -> cross F D I <> 0 ->
  exists Y, tri_open P Q R Y /\ ~ on_bd D E F Y.
Proof.
  intros D E F P Q R I Hd Hp HI Hde Hef Hfd.
  assert (HD : points_distinct D E) by (apply (ccw_edge_distinct D E F); exact Hd).
  assert (HE : points_distinct E F).
  { apply (ccw_edge_distinct E F D). rewrite <- (cross_cycle D E F). exact Hd. }
  destruct (vertex_off_pt D E P Q R HD Hp) as [Vp [HVpTri HVp]].
  destruct (vertex_off_pt E F P Q R HE Hp) as [Wp [HWpTri HWp]].
  destruct (mix_off_two (cross D E Vp) (cross D E Wp)
                        (cross E F Vp) (cross E F Wp) HVp HWp)
    as [s [Hs [HdeM HefM]]].
  set (M := convex_combination Vp Wp s).
  assert (HMin : in_tri P Q R M).
  { apply in_tri_conv; try assumption. lra. }
  assert (HdeMz : cross D E M <> 0).
  { unfold M. rewrite cross_combo. exact HdeM. }
  assert (HefMz : cross E F M <> 0).
  { unfold M. rewrite cross_combo. exact HefM. }
  destruct (pick_keep (cross F D I) (cross F D M) Hfd) as [t [Ht Hkeep]].
  set (Y := convex_combination I M t).
  exists Y. split.
  - apply seg_from_open; try assumption. lra. - apply crosses_off_bd.
    + unfold Y. rewrite cross_combo. rewrite Hde.
      replace ((1 - t) * 0 + t * cross D E M) with (t * cross D E M) by ring.
      apply off_by; [lra|exact HdeMz].
    + unfold Y. rewrite cross_combo. rewrite Hef.
      replace ((1 - t) * 0 + t * cross E F M) with (t * cross E F M) by ring.
      apply off_by; [lra|exact HefMz].
    + unfold Y. rewrite cross_combo. exact Hkeep.
Qed.
Lemma bd_out_rot : forall A B C Y,
  ~ on_bd B C A Y -> ~ on_bd A B C Y.
Proof.
  intros A B C Y Hn [H|[H|H]]; apply Hn; [right; right|left|right; left]; exact H.
Qed.
Lemma bd_out_rot2 : forall A B C Y,
  ~ on_bd C A B Y -> ~ on_bd A B C Y.
Proof.
  intros A B C Y Hn [H|[H|H]]; apply Hn; [right; left|right; right|left]; exact H.
Qed.
Lemma open_off_bd : forall D E F P Q R,
  0 < cross D E F -> 0 < cross P Q R ->
  exists Y, tri_open P Q R Y /\ ~ on_bd D E F Y.
Proof.
  intros D E F P Q R Hd Hp.
  set (I := inner_pt P Q R).
  assert (HI : tri_open P Q R I) by (apply inner_open; exact Hp).
  assert (HFD : points_distinct F D).
  { apply (ccw_edge_distinct F D E). rewrite <- (cross_cycle2 D E F). exact Hd. }
  assert (HE : points_distinct E F).
  { apply (ccw_edge_distinct E F D). rewrite <- (cross_cycle D E F). exact Hd. }
  destruct (Req_dec_T (cross D E I) 0) as [Hde|Hde];
  destruct (Req_dec_T (cross E F I) 0) as [Hef|Hef];
  destruct (Req_dec_T (cross F D I) 0) as [Hfd|Hfd].
  - exfalso. apply (not_all_edge_cross0 D E F I Hd). repeat split; assumption. - apply (flee_two D E F P Q R I Hd Hp HI Hde Hef Hfd).
  - destruct (flee_two F D E P Q R I) as [Y [HY HN]].
    + rewrite <- (cross_cycle2 D E F). exact Hd. + exact Hp. + exact HI. + exact Hfd. + exact Hde. + exact Hef.
    + exists Y. split; [exact HY|]. apply bd_out_rot2. exact HN.
  - destruct (vertex_off_pt D E P Q R (ccw_edge_distinct D E F Hd) Hp)
      as [V [HVTri HV]].
    apply (flee_one D E F P Q R I V Hp HI HVTri Hde HV Hef Hfd).
  - destruct (flee_two E F D P Q R I) as [Y [HY HN]].
    + rewrite <- (cross_cycle D E F). exact Hd. + exact Hp. + exact HI. + exact Hef. + exact Hfd. + exact Hde.
    + exists Y. split; [exact HY|]. apply bd_out_rot. exact HN.
  - destruct (vertex_off_pt E F P Q R HE Hp) as [V [HVTri HV]].
    destruct (flee_one E F D P Q R I V) as [Y [HY HN]].
    + exact Hp. + exact HI. + exact HVTri. + exact Hef. + exact HV. + exact Hfd. + exact Hde. + exists Y. split; [exact HY|]. apply bd_out_rot. exact HN.
  - destruct (vertex_off_pt F D P Q R HFD Hp) as [V [HVTri HV]].
    destruct (flee_one F D E P Q R I V) as [Y [HY HN]].
    + exact Hp. + exact HI. + exact HVTri. + exact Hfd. + exact HV. + exact Hde. + exact Hef. + exists Y. split; [exact HY|]. apply bd_out_rot2. exact HN.
  - exists I. split; [exact HI|]. apply crosses_off_bd; assumption.
Qed.
Lemma open2_not_bd : forall D E F (S : Point -> Prop),
  0 < cross D E F -> (forall X, S X -> on_bd D E F X) -> ~ open2 S.
Proof.
  intros D E F S Hd HS [P [Q [R [Hp Hall]]]].
  destruct (open_off_bd D E F P Q R Hd Hp) as [Y [HY Hnot]].
  apply Hnot. apply HS. apply Hall. exact HY.
Qed.
Lemma on_seg_between : forall A B P Q X p q,
  P = convex_combination A B p -> Q = convex_combination A B q ->
  0 <= p <= 1 -> 0 <= q <= 1 -> on_seg P Q X -> on_seg A B X.
Proof.
  intros A B P Q X p q -> -> Hp Hq [s [Hs ->]]. rewrite combo_affine.
  exists ((1 - s) * p + s * q). split; [| reflexivity].
  destruct Hp as [Hp0 Hp1], Hq as [Hq0 Hq1], Hs as [Hs0 Hs1]. split.
  - apply Rplus_le_le_0_compat; apply Rmult_le_pos; lra. - assert ((1 - s) * p <= (1 - s) * 1) by (apply Rmult_le_compat_l; lra).
    assert (s * q <= s * 1) by (apply Rmult_le_compat_l; lra). lra.
Qed.
Lemma both_on_edge : forall A B P Q,
  on_seg A B P -> on_seg A B Q ->
  forall X, on_seg P Q X -> on_seg A B X.
Proof.
  intros A B P Q [p [Hp HP]] [q [Hq HQ]] X HX.
  apply (on_seg_between A B P Q X p q); assumption.
Qed.
Lemma cross_ab_of_bc : forall A B C q,
  cross A B (convex_combination B C q) = q * cross A B C.
Proof.
  intros. rewrite cross_combo.
  replace (cross A B B) with 0 by (unfold cross; ring). ring.
Qed.
Lemma cross_bc_of_ab : forall A B C p,
  cross B C (convex_combination A B p) = (1 - p) * cross A B C.
Proof.
  intros. rewrite cross_combo.
  replace (cross B C B) with 0 by (unfold cross; ring).
  rewrite <- (cross_cycle A B C). ring.
Qed.
Lemma cross_ca_of_ab : forall A B C p,
  cross C A (convex_combination A B p) = p * cross A B C.
Proof.
  intros. rewrite cross_combo.
  replace (cross C A A) with 0 by (unfold cross; ring).
  rewrite <- (cross_cycle2 A B C). ring.
Qed.
Lemma cross_ca_of_bc : forall A B C q,
  cross C A (convex_combination B C q) = (1 - q) * cross A B C.
Proof.
  intros. rewrite cross_combo.
  replace (cross C A C) with 0 by (unfold cross; ring).
  rewrite <- (cross_cycle2 A B C). ring.
Qed.
Lemma half_mul_eq0 : forall b c,
  c <> 0 -> (1 / 2) * b * c = 0 -> b = 0.
Proof.
  intros b c Hc Hz. apply Rmult_integral in Hz. destruct Hz as [Hz|Hz].
  - apply Rmult_integral in Hz. destruct Hz as [Hz|Hz]; [lra|exact Hz]. - exfalso. apply Hc. exact Hz.
Qed.
Lemma mid_on : forall P Q, on_seg P Q (convex_combination P Q (1 / 2)).
Proof. intros. exists (1 / 2). split; [lra|reflexivity]. Qed.
Lemma bridge_ab_bc : forall A B C P Q,
  0 < cross A B C -> on_seg A B P -> on_seg B C Q ->
  on_bd A B C (convex_combination P Q (1 / 2)) ->
  (forall X, on_seg P Q X -> on_seg A B X) \/
  (forall X, on_seg P Q X -> on_seg B C X) \/
  (forall X, on_seg P Q X -> on_seg C A X).
Proof.
  intros A B C P Q Hd HP HQ Hmid.
  destruct HP as [p [Hp ->]]. destruct HQ as [q [Hq ->]].
  set (X := convex_combination (convex_combination A B p)
                               (convex_combination B C q) (1 / 2)).
  assert (Hnz : cross A B C <> 0).
  { apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
  assert (Hab : cross A B X = (1 / 2) * q * cross A B C).
  { unfold X. rewrite cross_combo. rewrite cross_combo0.
    rewrite (cross_ab_of_bc A B C q). field. }
  assert (Hbc : cross B C X = (1 / 2) * (1 - p) * cross A B C).
  { unfold X. rewrite cross_combo. rewrite cross_combo0.
    rewrite (cross_bc_of_ab A B C p). field. }
  assert (Hca : cross C A X = (1 / 2) * (p + 1 - q) * cross A B C).
  { unfold X. rewrite cross_combo.
    rewrite (cross_ca_of_ab A B C p). rewrite (cross_ca_of_bc A B C q). field. }
  destruct (on_bd_some_cross0 A B C X Hmid) as [Hz|[Hz|Hz]].
  - left.
    assert (Hq0 : q = 0).
    { apply (half_mul_eq0 q (cross A B C) Hnz). rewrite <- Hab. exact Hz. }
    intros Y HY.
    apply (on_seg_between A B (convex_combination A B p)
             (convex_combination B C q) Y p 1).
    + reflexivity. + rewrite Hq0. rewrite combo_left. symmetry. apply combo_right. + exact Hp. + lra. + exact HY.
  - right. left.
    assert (Hp1 : p = 1).
    { assert (E0 : 1 - p = 0).
      { apply (half_mul_eq0 (1 - p) (cross A B C) Hnz). rewrite <- Hbc. exact Hz. }
      lra. }
    intros Y HY.
    apply (on_seg_between B C (convex_combination A B p)
             (convex_combination B C q) Y 0 q).
    + rewrite Hp1. rewrite combo_right. symmetry. apply combo_left. + reflexivity. + lra. + exact Hq. + exact HY.
  - right. right.
    assert (Hs0 : p + 1 - q = 0).
    { apply (half_mul_eq0 (p + 1 - q) (cross A B C) Hnz). rewrite <- Hca. exact Hz. }
    assert (Hp0 : p = 0) by (destruct Hp as [HpLo HpHi]; destruct Hq as [HqLo HqHi]; lra).
    assert (Hq1 : q = 1) by (destruct Hp as [HpLo HpHi]; destruct Hq as [HqLo HqHi]; lra).
    intros Y HY.
    apply (on_seg_between C A (convex_combination A B p)
             (convex_combination B C q) Y 1 0).
    + rewrite Hp0. rewrite combo_left. symmetry. apply combo_right. + rewrite Hq1. rewrite combo_right. symmetry. apply combo_left. + lra. + lra. + exact HY.
Qed.
Lemma bridge_rev : forall A B C P Q,
  0 < cross A B C -> on_seg B C P -> on_seg A B Q ->
  (forall X, on_seg P Q X -> on_bd A B C X) ->
  (forall X, on_seg P Q X -> on_seg A B X) \/
  (forall X, on_seg P Q X -> on_seg B C X) \/
  (forall X, on_seg P Q X -> on_seg C A X).
Proof.
  intros A B C P Q Hd Hp Hq Hall.
  assert (Hmid : on_bd A B C (convex_combination Q P (1 / 2))).
  { apply Hall. apply on_seg_sym. apply mid_on. }
  destruct (bridge_ab_bc A B C Q P Hd Hq Hp Hmid) as [Ha|[Hb|Hc]].
  - left. intros X HX. apply Ha. apply on_seg_sym. exact HX. - right. left. intros X HX. apply Hb. apply on_seg_sym. exact HX.
  - right. right. intros X HX. apply Hc. apply on_seg_sym. exact HX.
Qed.
Lemma on_bd_rot : forall A B C X, on_bd A B C X -> on_bd B C A X.
Proof.
  intros A B C X [H|[H|H]]; [right; right|left|right; left]; exact H.
Qed.
Lemma on_bd_rot2 : forall A B C X, on_bd A B C X -> on_bd C A B X.
Proof.
  intros A B C X [H|[H|H]]; [right; left|right; right|left]; exact H.
Qed.
Lemma edge_of_or : forall A B C P Q,
  (forall X, on_seg P Q X -> on_seg A B X) \/
  (forall X, on_seg P Q X -> on_seg B C X) \/
  (forall X, on_seg P Q X -> on_seg C A X) ->
  exists e, In e (e3 A B C) /\
    forall X, on_seg P Q X -> on_seg (fst e) (snd e) X.
Proof.
  intros A B C P Q [H|[H|H]].
  - exists (A, B). split; [| exact H]. unfold e3. simpl. left. reflexivity. - exists (B, C). split; [| exact H]. unfold e3. simpl. right. left. reflexivity.
  - exists (C, A). split; [| exact H].
    unfold e3. simpl. right. right. left. reflexivity.
Qed.
Lemma bd_seg_edge : forall A B C P Q,
  0 < cross A B C ->
  (forall X, on_seg P Q X -> on_bd A B C X) ->
  exists e, In e (e3 A B C) /\
    forall X, on_seg P Q X -> on_seg (fst e) (snd e) X.
Proof.
  intros A B C P Q Hd Hall.
  assert (HP : on_bd A B C P) by (apply Hall; exact (proj1 (seg_ends P Q))).
  assert (HQ : on_bd A B C Q) by (apply Hall; exact (proj2 (seg_ends P Q))).
  destruct (bd_e3_seg A B C P HP) as [eP [HeP HonP]].
  destruct (bd_e3_seg A B C Q HQ) as [eQ [HeQ HonQ]].
  simpl in HeP, HeQ.
  destruct HeP as [<-|[<-|[<-|[]]]]; destruct HeQ as [<-|[<-|[<-|[]]]].
  - apply edge_of_or. left. apply both_on_edge; assumption. - apply edge_of_or. apply (bridge_ab_bc A B C P Q Hd HonP HonQ).
    apply Hall. apply mid_on.
  - destruct (bridge_rev C A B P Q) as [H|[H|H]].
    + rewrite <- (cross_cycle2 A B C). exact Hd. + exact HonP. + exact HonQ. + intros Z HZ. apply on_bd_rot2. apply Hall. exact HZ.
    + apply edge_of_or. right. right. exact H. + apply edge_of_or. left. exact H. + apply edge_of_or. right. left. exact H.
  - apply edge_of_or. apply (bridge_rev A B C P Q Hd HonP HonQ Hall). - apply edge_of_or. right. left. apply both_on_edge; assumption.
  - destruct (bridge_ab_bc B C A P Q) as [H|[H|H]].
    + rewrite <- (cross_cycle A B C). exact Hd. + exact HonP. + exact HonQ. + apply on_bd_rot. apply Hall. apply mid_on.
    + apply edge_of_or. right. left. exact H. + apply edge_of_or. right. right. exact H. + apply edge_of_or. left. exact H.
  - destruct (bridge_ab_bc C A B P Q) as [H|[H|H]].
    + rewrite <- (cross_cycle2 A B C). exact Hd. + exact HonP. + exact HonQ. + apply on_bd_rot2. apply Hall. apply mid_on.
    + apply edge_of_or. right. right. exact H. + apply edge_of_or. left. exact H. + apply edge_of_or. right. left. exact H.
  - destruct (bridge_rev B C A P Q) as [H|[H|H]].
    + rewrite <- (cross_cycle A B C). exact Hd. + exact HonP. + exact HonQ. + intros Z HZ. apply on_bd_rot. apply Hall. exact HZ.
    + apply edge_of_or. right. left. exact H. + apply edge_of_or. right. right. exact H. + apply edge_of_or. left. exact H.
  - apply edge_of_or. right. right. apply both_on_edge; assumption.
Qed.
Lemma small_step : forall room,
  0 < room ->
  0 < Rmin (room / 2) (1 / 2) /\
  Rmin (room / 2) (1 / 2) < room /\
  Rmin (room / 2) (1 / 2) < 1.
Proof.
  intros room Hr. split; [| split].
  - apply Rmin_pos; lra. - eapply Rle_lt_trans; [apply Rmin_l|]. lra. - eapply Rle_lt_trans; [apply Rmin_r|]. lra.
Qed.
Lemma prefix_open : forall A B C X V t s,
  0 < cross A B C -> tri_open A B C X ->
  0 < t -> t < troom A B C X V -> 0 <= s <= 1 ->
  tri_open A B C (convex_combination X (convex_combination X V t) s).
Proof.
  intros A B C X V t s Hd HX Ht Htr Hs. rewrite combo_scale.
  destruct (Req_dec_T (s * t) 0) as [Hz|Hnz].
  - rewrite Hz. rewrite combo_left. exact HX. - apply nudge_tri_open; try assumption.
    + destruct (Req_dec_T s 0) as [Hs0|Hs0].
      * exfalso. apply Hnz. rewrite Hs0. ring. * apply Rmult_lt_0_compat; lra.
    + assert (s * t <= t).
      { rewrite <- (Rmult_1_l t) at 2. apply Rmult_le_compat_r; lra. }
      lra.
Qed.
Lemma back_on : forall V W p r,
  0 <= p <= 1 -> 0 <= r <= 1 ->
  on_seg V W (convex_combination (convex_combination V W p) V r).
Proof.
  intros V W p r Hp Hr. exists ((1 - r) * p). split.
  - destruct Hp as [Hp0 Hp1], Hr as [Hr0 Hr1]. split.
    + apply Rmult_le_pos; lra. + replace 1 with (1 * 1) by ring.
      apply Rle_trans with (r2 := 1 * p); [| lra].
      apply Rmult_le_compat_r; lra.
  - unfold convex_combination. destruct V, W. simpl. f_equal; ring.
Qed.
Lemma edge_pos_open : forall A B C V W X,
  0 < cross A B C -> V <> W ->
  tri_open A B C X -> on_seg V W X ->
  exists P Q, P <> Q /\
    forall Y, on_seg P Q Y -> tri_open A B C Y /\ on_seg V W Y.
Proof.
  intros A B C V W X Hd HVW HX Hon.
  destruct (point_eqb X V) eqn:EX.
  - apply point_eqb_true in EX. subst X.
    set (room := troom A B C V W).
    destruct (small_step room (troom_pos A B C V W HX)) as [Ht0 [Htr Ht1]].
    set (t := Rmin (room / 2) (1 / 2)).
    set (Q := convex_combination V W t).
    exists V, Q. split.
    + unfold Q. apply not_eq_sym. apply combo_neq; [exact HVW|exact Ht0]. + intros Y [s [Hs ->]]. split.
      * apply (prefix_open A B C V W t s); try assumption. * unfold Q. rewrite combo_scale. exists (s * t). split; [| reflexivity].
        split.
        -- apply Rmult_le_pos; [exact (proj1 Hs)|apply Rlt_le; exact Ht0].
        -- apply Rle_trans with (r2 := 1 * t).
           ++ apply Rmult_le_compat_r; [apply Rlt_le; exact Ht0|exact (proj2 Hs)].
           ++ rewrite Rmult_1_l. apply Rlt_le. exact Ht1.
  - assert (HXV : X <> V).
    { intros Heq. subst X. rewrite point_eqb_refl in EX. discriminate. }
    destruct Hon as [p [Hp ->]].
    set (room := troom A B C (convex_combination V W p) V).
    destruct (small_step room
                (troom_pos A B C (convex_combination V W p) V HX))
      as [Ht0 [Htr Ht1]].
    set (t := Rmin (room / 2) (1 / 2)).
    set (Q := convex_combination (convex_combination V W p) V t).
    exists (convex_combination V W p), Q. split.
    + unfold Q. apply not_eq_sym. apply combo_neq; [exact HXV|exact Ht0]. + intros Y [s [Hs ->]]. split.
      * apply prefix_open; try assumption. * unfold Q. rewrite combo_scale. apply back_on; try assumption.
        split.
        -- apply Rmult_le_pos; [exact (proj1 Hs)|apply Rlt_le; exact Ht0].
        -- apply Rle_trans with (r2 := 1 * t).
           ++ apply Rmult_le_compat_r; [apply Rlt_le; exact Ht0|exact (proj2 Hs)].
           ++ rewrite Rmult_1_l. apply Rlt_le. exact Ht1.
Qed.
Lemma cell_ok_equiv : forall d S T,
  (forall X, S X <-> T X) -> cell_ok d S -> cell_ok d T.
Proof.
  intros d S T Heq [Hempty Hdim]. split.
  - split.
    + intros Hd [X HT]. apply (proj1 Hempty Hd). exists X. apply Heq. exact HT. + intros HT. apply (proj2 Hempty). intros [X HS]. apply HT.
      exists X. apply Heq. exact HS.
  - intros [X HT].
    assert (HS : exists Z, S Z).
    { exists X. apply Heq. exact HT. }
    destruct (Hdim HS) as [H0|[H1|H2]].
    + left. destruct H0 as [Hd Hpos]. split; [exact Hd|].
      intros [P [Q [Hpq Hall]]]. apply Hpos. exists P, Q. split; [exact Hpq|].
      intros Y HY. apply Heq. apply Hall. exact HY.
    + right. left. destruct H1 as [Hd [Hpos Hopen]]. split; [exact Hd|]. split.
      * destruct Hpos as [P [Q [Hpq Hall]]]. exists P, Q. split; [exact Hpq|].
        intros Y HY. apply Heq. apply Hall. exact HY.
      * intros [P [Q [R [Hp Hall]]]]. apply Hopen. exists P, Q, R.
        split; [exact Hp|]. intros Y HY. apply Heq. apply Hall. exact HY.
    + right. right. destruct H2 as [Hd Hopen]. split; [exact Hd|].
      destruct Hopen as [P [Q [R [Hp Hall]]]]. exists P, Q, R. split; [exact Hp|].
      intros Y HY. apply Heq. apply Hall. exact HY.
Qed.
Lemma cell_ii : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  cell_ok (im_ii (tri_de9im A B C D E F)) (set_ii A B C D E F).
Proof.
  intros A B C D E F HA HB.
  assert (Hent : im_ii (tri_de9im A B C D E F) = ii_entry A B C D E F)
    by (unfold tri_de9im; reflexivity).
  rewrite Hent. unfold cell_ok, set_ii. split.
  - split.
    + intros Hd [X [HoA HoB]].
      assert (H2 : ii_entry A B C D E F = Dim2).
      { unfold ii_entry.
        destruct (Rlt_dec 0 (poly_area2 (tri_inter A B C D E F))) as [Hp|Hp].
        - reflexivity. - exfalso. apply Hp. apply (proj1 (ii_nonempty_iff A B C D E F HA HB)).
          exists X. split; assumption. }
      rewrite H2 in Hd. discriminate.
    + intros Hempty. unfold ii_entry.
      destruct (Rlt_dec 0 (poly_area2 (tri_inter A B C D E F))) as [Hp|Hp].
      * exfalso. apply Hempty. apply (proj2 (ii_nonempty_iff A B C D E F HA HB) Hp). * reflexivity.
  - intros [X [HoA HoB]]. right. right. split.
    + unfold ii_entry.
      destruct (Rlt_dec 0 (poly_area2 (tri_inter A B C D E F))) as [Hp|Hp].
      * reflexivity. * exfalso. apply Hp. apply (proj1 (ii_nonempty_iff A B C D E F HA HB)).
        exists X. split; assumption.
    + apply (open2_both A B C D E F X); assumption.
Qed.
Lemma cell_ib : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  cell_ok (im_ib (tri_de9im A B C D E F)) (set_ib A B C D E F).
Proof.
  intros A B C D E F HA HB.
  destruct (bound_cells_iff A B C D E F HA HB) as [Hib _].
  assert (Hent : im_ib (tri_de9im A B C D E F) = ib_entry A B C D E F)
    by (unfold tri_de9im; reflexivity).
  rewrite Hent. unfold cell_ok, set_ib. split.
  - split.
    + intros Hd Hne. rewrite (proj2 Hib Hne) in Hd. discriminate. + intros Hempty. unfold ib_entry. destruct (ib_hit A B C D E F) eqn:Hh.
      * exfalso. apply Hempty. apply (proj1 Hib).
        unfold ib_entry. rewrite Hh. reflexivity.
      * reflexivity.
  - intros [X [Ho Hb]]. right. left. split; [| split].
    + apply (proj2 Hib). exists X. split; assumption. + destruct (bd_e3_seg D E F X Hb) as [e [He Hon]].
      assert (Hne : fst e <> snd e) by (apply (e3_neq D E F e HB He)).
      destruct (edge_pos_open A B C (fst e) (snd e) X HA Hne Ho Hon)
        as [P [Q [Hpq Hall]]].
      exists P, Q. split; [exact Hpq|]. intros Y HY.
      destruct (Hall Y HY) as [Hopen Hedge]. split; [exact Hopen|].
      apply (seg_e3_bd D E F e Y He Hedge).
    + apply (open2_not_bd D E F (set_ib A B C D E F) HB).
      intros Y [_ HbY]. exact HbY.
Qed.
Lemma cell_ie : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  cell_ok (im_ie (tri_de9im A B C D E F)) (set_ie A B C D E F).
Proof.
  intros A B C D E F HA HB.
  assert (Hent : im_ie (tri_de9im A B C D E F) = ie_entry A B C D E F)
    by (unfold tri_de9im; reflexivity).
  rewrite Hent. unfold cell_ok, set_ie. split.
  - split.
    + intros Hd Hne. rewrite (proj2 (ie_open_iff A B C D E F HA HB) Hne) in Hd.
      discriminate.
    + intros Hempty. unfold ie_entry. destruct (ie_hit A B C D E F) eqn:Hh.
      * exfalso. apply Hempty. apply (proj1 (ie_open_iff A B C D E F HA HB)).
        unfold ie_entry. rewrite Hh. reflexivity.
      * reflexivity.
  - intros [X [Ho Hout]]. right. right. split.
    + apply (proj2 (ie_open_iff A B C D E F HA HB)). exists X. split; assumption. + apply (open2_out A B C D E F X); assumption.
Qed.
Lemma cell_bb : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  cell_ok (im_bb (tri_de9im A B C D E F)) (set_bb A B C D E F).
Proof.
  intros A B C D E F HA HB.
  destruct (bound_cells_iff A B C D E F HA HB) as [_ [_ [Hb1 [Hb0 HbF]]]].
  assert (Hent : im_bb (tri_de9im A B C D E F) = bb_entry A B C D E F)
    by (unfold tri_de9im; reflexivity).
  rewrite Hent. unfold cell_ok, set_bb. split.
  - exact HbF. - intros Hex. destruct (bb_overlap A B C D E F) eqn:Ho.
    + right. left. split; [| split].
      * unfold bb_entry. rewrite Ho. reflexivity. * destruct (overlap_segment_bd A B C D E F Ho) as [P [Q [Hneq [He Hf]]]].
        exists P, Q. split; [exact Hneq|]. intros X HX.
        destruct He as [e [Hin HeX]]. destruct Hf as [f [Hinf HfX]]. split.
        -- apply (seg_e3_bd A B C e X Hin). apply HeX. exact HX.
        -- apply (seg_e3_bd D E F f X Hinf). apply HfX. exact HX.
      * apply (open2_not_bd A B C (fun X => on_bd A B C X /\ on_bd D E F X) HA).
        intros Y [Ha _]. exact Ha.
    + destruct (bb_touch A B C D E F) eqn:Ht.
      * left. split.
        -- unfold bb_entry. rewrite Ho, Ht. reflexivity.
        -- intros [P [Q [Hneq Hall]]].
           assert (H1 : bb_entry A B C D E F = Dim1).
           { apply (proj2 Hb1). exists P, Q. split; [exact Hneq|]. split.
             - apply (bd_seg_edge A B C P Q HA).
               intros X HX. exact (proj1 (Hall X HX)).
             - apply (bd_seg_edge D E F P Q HB).
               intros X HX. exact (proj2 (Hall X HX)). }
           unfold bb_entry in H1. rewrite Ho, Ht in H1. discriminate.
      * exfalso. apply (proj1 HbF).
        -- unfold bb_entry. rewrite Ho, Ht. reflexivity.
        -- exact Hex.
Qed.
Lemma be_point_dim1 : forall A B C D E F X,
  0 < cross A B C -> 0 < cross D E F ->
  on_bd A B C X -> ~ in_tri D E F X ->
  be_entry A B C D E F = Dim1.
Proof.
  intros A B C D E F X HA HB Hb Hout.
  apply be_cell_iff; try assumption.
  destruct (in_tri_dec D E F A HB) as [Ha|Ha]; [| left; exact Ha].
  destruct (in_tri_dec D E F B HB) as [Hv|Hv]; [| right; left; exact Hv].
  destruct (in_tri_dec D E F C HB) as [Hc|Hc]; [| right; right; exact Hc].
  exfalso. apply Hout.
  apply (verts_in_subset A B C D E F X HB Ha Hv Hc).
  apply on_bd_in_tri. exact Hb.
Qed.
Lemma cell_be : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  cell_ok (im_be (tri_de9im A B C D E F)) (set_be A B C D E F).
Proof.
  intros A B C D E F HA HB.
  assert (Hent : im_be (tri_de9im A B C D E F) = be_entry A B C D E F)
    by (unfold tri_de9im; reflexivity).
  rewrite Hent. unfold cell_ok, set_be. split.
  - split.
    + intros Hd [X [Hb Hout]].
      rewrite (be_point_dim1 A B C D E F X HA HB Hb Hout) in Hd. discriminate.
    + intros Hempty. unfold be_entry. destruct (ie_hit A B C D E F) eqn:Hh.
      * exfalso. apply Hempty.
        destruct (proj1 (be_bd_iff A B C D E F HA HB))
          as [P [Q [Hneq [He Hout]]]].
        { unfold be_entry. rewrite Hh. reflexivity. }
        assert (HP : on_seg P Q P) by exact (proj1 (seg_ends P Q)).
        destruct He as [e [Hin Hsub]]. exists P. split.
        -- apply (seg_e3_bd A B C e P Hin). apply Hsub. exact HP.
        -- apply Hout. exact HP.
      * reflexivity.
  - intros [X [Hb Hout]]. right. left. split; [| split].
    + apply (be_point_dim1 A B C D E F X HA HB Hb Hout). + destruct (proj1 (be_bd_iff A B C D E F HA HB)
                 (be_point_dim1 A B C D E F X HA HB Hb Hout))
        as [P [Q [Hneq [He HoutS]]]].
      exists P, Q. split; [exact Hneq|]. intros Y HY.
      destruct He as [e [Hin Hsub]]. split.
      * apply (seg_e3_bd A B C e Y Hin). apply Hsub. exact HY. * apply HoutS. exact HY.
    + apply (open2_not_bd A B C (fun Z => on_bd A B C Z /\ ~ in_tri D E F Z) HA).
      intros Z [Hz _]. exact Hz.
Qed.
Lemma cell_bi : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  cell_ok (im_bi (tri_de9im A B C D E F)) (set_bi A B C D E F).
Proof.
  intros A B C D E F HA HB.
  assert (Him : im_bi (tri_de9im A B C D E F) =
                im_ib (tri_de9im D E F A B C)).
  { unfold tri_de9im, bi_entry. reflexivity. }
  rewrite Him. apply cell_ok_equiv with (S := set_ib D E F A B C).
  - intros X. unfold set_bi, set_ib. tauto. - apply cell_ib; assumption.
Qed.
Lemma cell_ei : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  cell_ok (im_ei (tri_de9im A B C D E F)) (set_ei A B C D E F).
Proof.
  intros A B C D E F HA HB.
  assert (Him : im_ei (tri_de9im A B C D E F) =
                im_ie (tri_de9im D E F A B C)).
  { unfold tri_de9im, ei_entry. reflexivity. }
  rewrite Him. apply cell_ok_equiv with (S := set_ie D E F A B C).
  - intros X. unfold set_ei, set_ie. tauto. - apply cell_ie; assumption.
Qed.
Lemma cell_eb : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  cell_ok (im_eb (tri_de9im A B C D E F)) (set_eb A B C D E F).
Proof.
  intros A B C D E F HA HB.
  assert (Him : im_eb (tri_de9im A B C D E F) =
                im_be (tri_de9im D E F A B C)).
  { unfold tri_de9im, eb_entry. reflexivity. }
  rewrite Him. apply cell_ok_equiv with (S := set_be D E F A B C).
  - intros X. unfold set_eb, set_be. tauto. - apply cell_be; assumption.
Qed.
Lemma cell_ee : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  cell_ok (im_ee (tri_de9im A B C D E F)) (set_ee A B C D E F).
Proof.
  intros A B C D E F HA HB.
  assert (Hent : im_ee (tri_de9im A B C D E F) = Dim2).
  { unfold tri_de9im, ee_entry. reflexivity. }
  rewrite Hent. unfold cell_ok. split.
  - split.
    + intros Hd. discriminate. + intros Hempty. exfalso. apply Hempty. apply ee_witness.
  - intros _. right. right. split; [reflexivity|]. apply open2_ee.
Qed.
Theorem tri_de9im_correct : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  cell_ok (im_ii (tri_de9im A B C D E F)) (set_ii A B C D E F) /\
  cell_ok (im_ib (tri_de9im A B C D E F)) (set_ib A B C D E F) /\
  cell_ok (im_ie (tri_de9im A B C D E F)) (set_ie A B C D E F) /\
  cell_ok (im_bi (tri_de9im A B C D E F)) (set_bi A B C D E F) /\
  cell_ok (im_bb (tri_de9im A B C D E F)) (set_bb A B C D E F) /\
  cell_ok (im_be (tri_de9im A B C D E F)) (set_be A B C D E F) /\
  cell_ok (im_ei (tri_de9im A B C D E F)) (set_ei A B C D E F) /\
  cell_ok (im_eb (tri_de9im A B C D E F)) (set_eb A B C D E F) /\
  cell_ok (im_ee (tri_de9im A B C D E F)) (set_ee A B C D E F).
Proof.
  intros A B C D E F HA HB.
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
  - apply cell_ii; assumption. - apply cell_ib; assumption. - apply cell_ie; assumption. - apply cell_bi; assumption. - apply cell_bb; assumption.
  - apply cell_be; assumption. - apply cell_ei; assumption. - apply cell_eb; assumption. - apply cell_ee; assumption.
Qed.
Lemma orient_pos_area : forall A B C A' B' C',
  cross A B C <> 0 -> orient_ccw A B C = ((A', B'), C') ->
  0 < cross A' B' C'.
Proof.
  intros A B C A' B' C' Hne Heq. unfold orient_ccw in Heq.
  destruct (Rlt_dec (cross A B C) 0) as [Hlt|Hge].
  - inversion Heq. subst A' B' C'. apply orient_swap_pos. exact Hlt. - inversion Heq. subst A' B' C'.
    assert (Hle : 0 <= cross A B C) by (apply Rnot_lt_le; exact Hge).
    destruct (Rle_lt_or_eq_dec 0 (cross A B C) Hle) as [Hpos|Heq0].
    + exact Hpos. + exfalso. apply Hne. symmetry. exact Heq0.
Qed.
Theorem tri_de9im_orient_correct : forall A B C D E F A' B' C' D' E' F',
  cross A B C <> 0 -> cross D E F <> 0 ->
  orient_ccw A B C = ((A', B'), C') ->
  orient_ccw D E F = ((D', E'), F') ->
  tri_de9im_orient A B C D E F = tri_de9im A' B' C' D' E' F' /\
  cell_ok (im_ii (tri_de9im_orient A B C D E F)) (set_ii A' B' C' D' E' F') /\
  cell_ok (im_ib (tri_de9im_orient A B C D E F)) (set_ib A' B' C' D' E' F') /\
  cell_ok (im_ie (tri_de9im_orient A B C D E F)) (set_ie A' B' C' D' E' F') /\
  cell_ok (im_bi (tri_de9im_orient A B C D E F)) (set_bi A' B' C' D' E' F') /\
  cell_ok (im_bb (tri_de9im_orient A B C D E F)) (set_bb A' B' C' D' E' F') /\
  cell_ok (im_be (tri_de9im_orient A B C D E F)) (set_be A' B' C' D' E' F') /\
  cell_ok (im_ei (tri_de9im_orient A B C D E F)) (set_ei A' B' C' D' E' F') /\
  cell_ok (im_eb (tri_de9im_orient A B C D E F)) (set_eb A' B' C' D' E' F') /\
  cell_ok (im_ee (tri_de9im_orient A B C D E F)) (set_ee A' B' C' D' E' F').
Proof.
  intros A B C D E F A' B' C' D' E' F' HA HB HoA HoD.
  assert (HAp : 0 < cross A' B' C') by (apply (orient_pos_area A B C); assumption).
  assert (HDp : 0 < cross D' E' F') by (apply (orient_pos_area D E F); assumption).
  assert (Heq : tri_de9im_orient A B C D E F = tri_de9im A' B' C' D' E' F').
  { unfold tri_de9im_orient. rewrite HoA, HoD. reflexivity. }
  split; [exact Heq|]. rewrite Heq. apply tri_de9im_correct; assumption.
Qed.

Print Assumptions slack_pos_room.
Print Assumptions seg_from_open.
Print Assumptions troom_pos.
Print Assumptions nudge_tri_open.
Print Assumptions tri_open_bary.
Print Assumptions neg_bary.
Print Assumptions below_min6.
Print Assumptions tri_open_of_three.
Print Assumptions subtri_in.
Print Assumptions open2_both.
Print Assumptions open2_neg_line.
Print Assumptions open2_out.
Print Assumptions open2_ee.
Print Assumptions vertex_off_line.
Print Assumptions vertex_off_pt.
Print Assumptions aff_two_roots.
Print Assumptions pick_one.
Print Assumptions pick_safe_t.
Print Assumptions pick_keep.
Print Assumptions off_by.
Print Assumptions on_bd_some_cross0.
Print Assumptions not_all_edge_cross0.
Print Assumptions crosses_off_bd.
Print Assumptions mix_off_two.
Print Assumptions flee_one.
Print Assumptions flee_two.
Print Assumptions bd_out_rot.
Print Assumptions bd_out_rot2.
Print Assumptions open_off_bd.
Print Assumptions open2_not_bd.
Print Assumptions on_seg_between.
Print Assumptions both_on_edge.
Print Assumptions cross_ab_of_bc.
Print Assumptions cross_bc_of_ab.
Print Assumptions cross_ca_of_ab.
Print Assumptions cross_ca_of_bc.
Print Assumptions half_mul_eq0.
Print Assumptions mid_on.
Print Assumptions bridge_ab_bc.
Print Assumptions bridge_rev.
Print Assumptions on_bd_rot.
Print Assumptions on_bd_rot2.
Print Assumptions edge_of_or.
Print Assumptions bd_seg_edge.
Print Assumptions small_step.
Print Assumptions prefix_open.
Print Assumptions back_on.
Print Assumptions edge_pos_open.
Print Assumptions cell_ok_equiv.
Print Assumptions cell_ii.
Print Assumptions cell_ib.
Print Assumptions cell_ie.
Print Assumptions cell_bb.
Print Assumptions be_point_dim1.
Print Assumptions cell_be.
Print Assumptions cell_bi.
Print Assumptions cell_ei.
Print Assumptions cell_eb.
Print Assumptions cell_ee.
Print Assumptions tri_de9im_correct.
Print Assumptions orient_pos_area.
Print Assumptions tri_de9im_orient_correct.
