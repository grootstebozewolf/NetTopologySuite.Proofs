(* NetTopologySuite.Proofs.TrianglePairExterior
   DE-9IM exterior cells for a triangle pair, and the nine-cell matrix.
   tri_de9im takes CCW vertices. tri_de9im_orient swaps a clockwise
   triple before calling it. I∩E is an open point of A outside closed B.
   B∩E is a positive-length subsegment of A's boundary outside closed B.
   E∩I and E∩B are the swap. E∩E is constantly dimension 2, witnessed
   nonempty. A vertex only on the boundary of B stays closed
   (be_boundary_closed).
   topic: relate
   claimId: tri-de9im-c
   witness: exterior_cells_iff
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7).
   License: BSD-3-Clause *)

From Stdlib Require Import Reals Lra Lia List Bool.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex ConvexClip
  DE9IM TrianglePairCommon TrianglePairClip TrianglePairEdge TrianglePairBound.
Local Open Scope R_scope.

Definition inner_pt (A B C : Point) : Point :=
  bary3 (1 / 2) (1 / 4) (1 / 4) A B C.

Lemma inner_open : forall A B C,
  0 < cross A B C -> tri_open A B C (inner_pt A B C).
Proof.
  intros A B C Hd. unfold inner_pt, tri_open. repeat split.
  - rewrite cross_bary3 by lra.
    rewrite (cross_at_P0_is_collinear A B).
    replace (cross A B B) with 0 by (unfold cross; ring). lra.
  - rewrite cross_bary3 by lra.
    rewrite (cross_at_P0_is_collinear B C).
    replace (cross B C C) with 0 by (unfold cross; ring).
    rewrite <- (cross_cycle A B C). lra.
  - rewrite cross_bary3 by lra.
    rewrite (cross_at_P0_is_collinear C A).
    replace (cross C A A) with 0 by (unfold cross; ring).
    rewrite <- (cross_cycle2 A B C). lra.
Qed.

Lemma near_open : forall A B C V t,
  0 < cross A B C -> in_tri A B C V -> 0 < t <= 1 ->
  tri_open A B C (convex_combination V (inner_pt A B C) t).
Proof.
  intros A B C V t Hd HV Ht.
  destruct (inner_open A B C Hd) as [Iab [Ibc Ica]].
  destruct (proj2 (tri_slack_hull A B C V Hd) HV) as [Vab [Vbc Vca]].
  repeat split; rewrite cross_combo.
  - apply Rplus_le_lt_0_compat.
    + apply Rmult_le_pos; lra.
    + apply Rmult_lt_0_compat; lra.
  - apply Rplus_le_lt_0_compat.
    + apply Rmult_le_pos; lra.
    + apply Rmult_lt_0_compat; lra.
  - apply Rplus_le_lt_0_compat.
    + apply Rmult_le_pos; lra.
    + apply Rmult_lt_0_compat; lra.
Qed.

Lemma neg_prefix : forall s u, s < 0 ->
  exists t, 0 < t <= 1 /\
    forall r, 0 <= r <= t -> (1 - r) * s + r * u < 0.
Proof.
  intros s u Hs.
  destruct (Rle_dec u s) as [Hu|Hu].
  - exists 1. split; [lra|]. intros r Hr.
    assert ((1 - r) * s + r * u <= (1 - r) * s + r * s).
    { apply Rplus_le_compat_l. apply Rmult_le_compat_l; lra. }
    replace ((1 - r) * s + r * s) with s in * by ring. lra.
  - assert (Hsu : s < u) by (apply Rnot_le_lt; exact Hu).
    set (den := u - s).
    assert (Hden : 0 < den) by (unfold den; lra).
    set (t := Rmin (1 / 2) ((- s) / (2 * den))).
    assert (Hroot : 0 < (- s) / (2 * den)).
    { apply Rdiv_lt_0_compat; lra. }
    assert (Ht0 : 0 < t).
    { unfold t. destruct (Rle_dec (1 / 2) ((- s) / (2 * den))) as [Hle|Hlt].
      - rewrite (Rmin_left _ _ Hle). lra.
      - rewrite (Rmin_right _ _ (Rlt_le _ _ (Rnot_le_lt _ _ Hlt))). exact Hroot. }
    assert (Ht1 : t <= 1 / 2) by (unfold t; apply Rmin_l).
    assert (Hcap : t <= (- s) / (2 * den)) by (unfold t; apply Rmin_r).
    exists t. split; [lra|]. intros r Hr.
    assert (Hrden : r * den <= (- s) / 2).
    { apply Rle_trans with (r2 := t * den).
      - apply Rmult_le_compat_r; [apply Rlt_le; exact Hden | lra].
      - apply Rle_trans with (r2 := ((- s) / (2 * den)) * den).
        + apply Rmult_le_compat_r; [apply Rlt_le; exact Hden | exact Hcap].
        + replace (((- s) / (2 * den)) * den) with ((- s) / 2) by (field; lra).
          lra. }
    replace ((1 - r) * s + r * u) with (s + r * den) by (unfold den; ring).
    apply Rle_lt_trans with (r2 := s + (- s) / 2).
    + apply Rplus_le_compat_l. exact Hrden.
    + lra.
Qed.

Lemma cross0_on_edge : forall A B C X,
  0 < cross A B C ->
  0 <= cross B C X -> 0 <= cross C A X -> cross A B X = 0 ->
  on_seg A B X.
Proof.
  intros A B C X Hd Hbc Hca Hz.
  assert (Hsum : cross B C X + cross C A X = cross A B C).
  { rewrite <- (cross_sum3 A B C X). rewrite Hz. ring. }
  set (t := cross C A X / cross A B C).
  assert (Ht0 : 0 <= t).
  { unfold t. apply Rmult_le_pos; [exact Hca |].
    apply Rlt_le, Rinv_0_lt_compat. exact Hd. }
  assert (Ht1 : t <= 1).
  { apply Rmult_le_reg_r with (r := cross A B C); [exact Hd|].
    unfold t, Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  destruct (tri_bary_recon A B C X) as [Hs Hx]; [lra|].
  set (d := cross A B C) in *.
  set (a := cross B C X / d) in *.
  set (b := cross C A X / d) in *.
  set (c := cross A B X / d) in *.
  assert (Hb : b = t) by (unfold t, b, d; reflexivity).
  assert (Hc0 : c = 0) by (unfold c; rewrite Hz; field; lra).
  assert (Ha : a = 1 - t).
  { assert (Es : a + b + c = 1) by exact Hs. rewrite Hb, Hc0 in Es. lra. }
  exists t. split; [lra|].
  rewrite Hx, Hc0, Ha, Hb.
  unfold bary3, convex_combination. destruct A, B, C, X. simpl. f_equal; ring.
Qed.

Lemma in_tri_open_or_bd : forall A B C X,
  0 < cross A B C -> in_tri A B C X ->
  tri_open A B C X \/ on_bd A B C X.
Proof.
  intros A B C X Hd Hin.
  destruct (proj2 (tri_slack_hull A B C X Hd) Hin) as [Hab [Hbc Hca]].
  destruct (Rle_lt_or_eq_dec 0 (cross A B X) Hab) as [Habp|Hab0].
  - destruct (Rle_lt_or_eq_dec 0 (cross B C X) Hbc) as [Hbcp|Hbc0].
    + destruct (Rle_lt_or_eq_dec 0 (cross C A X) Hca) as [Hcap|Hca0].
      * left. repeat split; assumption.
      * right. right. right.
        apply (cross0_on_edge C A B X).
        -- rewrite <- (cross_cycle2 A B C). exact Hd.
        -- exact Hab.
        -- exact Hbc.
        -- symmetry. exact Hca0.
    + right. right. left.
      apply (cross0_on_edge B C A X).
      -- rewrite <- (cross_cycle A B C). exact Hd.
      -- exact Hca.
      -- exact Hab.
      -- symmetry. exact Hbc0.
  - right. left.
    apply (cross0_on_edge A B C X).
    + exact Hd.
    + exact Hbc.
    + exact Hca.
    + symmetry. exact Hab0.
Qed.

Lemma vtx_on_bd_iff : forall A B C X,
  vtx_on_bd_b A B C X = true <-> on_bd A B C X.
Proof.
  intros A B C X. unfold vtx_on_bd_b, on_bd. split.
  - intros H. apply orb_true_iff in H. destruct H as [H|H].
    apply orb_true_iff in H. destruct H as [H|H].
    + left. apply on_seg_b_iff. exact H.
    + right. left. apply on_seg_b_iff. exact H.
    + right. right. apply on_seg_b_iff. exact H.
  - intros [H|[H|H]]; apply orb_true_iff.
    + left. apply orb_true_iff. left. apply on_seg_b_iff. exact H.
    + left. apply orb_true_iff. right. apply on_seg_b_iff. exact H.
    + right. apply on_seg_b_iff. exact H.
Qed.

Lemma vtx_out_iff : forall A B C X,
  0 < cross A B C ->
  vtx_out_b A B C X = true <-> ~ in_tri A B C X.
Proof.
  intros A B C X Hd. unfold vtx_out_b. split.
  - intros Hout Hin.
    destruct (in_tri_open_or_bd A B C X Hd Hin) as [Ho|Hb].
    + unfold vtx_in_open_b in Hout.
      rewrite (proj2 (tri_open_b_true A B C X) Ho) in Hout.
      simpl in Hout. discriminate.
    + rewrite (proj2 (vtx_on_bd_iff A B C X) Hb) in Hout.
      rewrite orb_true_r in Hout. discriminate.
  - intros Hout.
    assert (Ho : vtx_in_open_b A B C X = false).
    { destruct (vtx_in_open_b A B C X) eqn:E; [| reflexivity].
      exfalso. apply Hout. apply tri_open_in; [exact Hd|].
      apply (proj1 (tri_open_b_true A B C X) E). }
    assert (Hb : vtx_on_bd_b A B C X = false).
    { destruct (vtx_on_bd_b A B C X) eqn:E; [| reflexivity].
      exfalso. apply Hout. apply on_bd_in_tri.
      apply (proj1 (vtx_on_bd_iff A B C X) E). }
    rewrite Ho, Hb. reflexivity.
Qed.

Lemma boundary_vertex_not_out : forall A B C X,
  0 < cross A B C -> on_bd A B C X -> vtx_out_b A B C X = false.
Proof.
  intros A B C X Hd Hb.
  destruct (vtx_out_b A B C X) eqn:E; [| reflexivity].
  exfalso. apply (proj1 (vtx_out_iff A B C X Hd) E).
  apply on_bd_in_tri. exact Hb.
Qed.

Lemma not_in_cross : forall A B C X,
  0 < cross A B C -> ~ in_tri A B C X ->
  cross A B X < 0 \/ cross B C X < 0 \/ cross C A X < 0.
Proof.
  intros A B C X Hd Hout.
  destruct (Rlt_dec (cross A B X) 0) as [Ha|Ha]; [left; exact Ha|].
  destruct (Rlt_dec (cross B C X) 0) as [Hb|Hb]; [right; left; exact Hb|].
  destruct (Rlt_dec (cross C A X) 0) as [Hc|Hc]; [right; right; exact Hc|].
  exfalso. apply Hout. apply (proj1 (tri_slack_hull A B C X Hd)).
  repeat split; apply Rnot_lt_le; assumption.
Qed.

Lemma out_of_cross : forall A B C X,
  0 < cross A B C ->
  cross A B X < 0 \/ cross B C X < 0 \/ cross C A X < 0 ->
  ~ in_tri A B C X.
Proof.
  intros A B C X Hd Hneg Hin.
  destruct (proj2 (tri_slack_hull A B C X Hd) Hin) as [Ha [Hb Hc]].
  destruct Hneg as [Hn|[Hn|Hn]].
  - exact (Rlt_not_le 0 (cross A B X) Hn Ha).
  - exact (Rlt_not_le 0 (cross B C X) Hn Hb).
  - exact (Rlt_not_le 0 (cross C A X) Hn Hc).
Qed.

Lemma verts_in_subset : forall A B C D E F X,
  0 < cross D E F ->
  in_tri D E F A -> in_tri D E F B -> in_tri D E F C ->
  in_tri A B C X -> in_tri D E F X.
Proof.
  intros A B C D E F X Hd Ha Hb Hc Hx.
  destruct Hx as [a [b [c [Hna [Hnb [Hnc [Hs HX]]]]]]].
  destruct (proj2 (tri_slack_hull D E F A Hd) Ha) as [Aa [Ab Ac]].
  destruct (proj2 (tri_slack_hull D E F B Hd) Hb) as [Ba [Bb Bc]].
  destruct (proj2 (tri_slack_hull D E F C Hd) Hc) as [Ca [Cb Cc]].
  apply (proj1 (tri_slack_hull D E F X Hd)). rewrite HX.
  repeat split; rewrite cross_bary3 by exact Hs.
  - apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat|];
      apply Rmult_le_pos; assumption.
  - apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat|];
      apply Rmult_le_pos; assumption.
  - apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat|];
      apply Rmult_le_pos; assumption.
Qed.

Lemma spread_vertex : forall A B C D E F V,
  0 < cross A B C -> 0 < cross D E F ->
  in_tri A B C V -> ~ in_tri D E F V ->
  exists X, tri_open A B C X /\ ~ in_tri D E F X.
Proof.
  intros A B C D E F V HA HB HV Hout.
  set (I := inner_pt A B C).
  destruct (not_in_cross D E F V HB Hout) as [Hc|[Hc|Hc]].
  - destruct (neg_prefix (cross D E V) (cross D E I) Hc) as [t [Ht Hall]].
    exists (convex_combination V I t). split.
    + apply near_open; assumption.
    + apply (out_of_cross D E F); [exact HB|]. left.
      rewrite cross_combo. apply Hall. lra.
  - destruct (neg_prefix (cross E F V) (cross E F I) Hc) as [t [Ht Hall]].
    exists (convex_combination V I t). split.
    + apply near_open; assumption.
    + apply (out_of_cross D E F); [exact HB|]. right. left.
      rewrite cross_combo. apply Hall. lra.
  - destruct (neg_prefix (cross F D V) (cross F D I) Hc) as [t [Ht Hall]].
    exists (convex_combination V I t). split.
    + apply near_open; assumption.
    + apply (out_of_cross D E F); [exact HB|]. right. right.
      rewrite cross_combo. apply Hall. lra.
Qed.

Definition ie_hit (A B C D E F : Point) : bool :=
  vtx_out_b D E F A || vtx_out_b D E F B || vtx_out_b D E F C.

Definition ie_entry (A B C D E F : Point) : DimValue :=
  if ie_hit A B C D E F then Dim2 else DimF.

Definition be_entry (A B C D E F : Point) : DimValue :=
  if ie_hit A B C D E F then Dim1 else DimF.

Definition ei_entry (A B C D E F : Point) : DimValue :=
  ie_entry D E F A B C.

Definition eb_entry (A B C D E F : Point) : DimValue :=
  be_entry D E F A B C.

Definition ee_entry (A B C D E F : Point) : DimValue := Dim2.

Lemma ie_hit_spec : forall A B C D E F,
  0 < cross D E F ->
  ie_hit A B C D E F = true <->
  ~ in_tri D E F A \/ ~ in_tri D E F B \/ ~ in_tri D E F C.
Proof.
  intros A B C D E F Hd. unfold ie_hit. split.
  - intros H. apply orb_true_iff in H. destruct H as [H|H].
    apply orb_true_iff in H. destruct H as [H|H].
    + left. apply (proj1 (vtx_out_iff D E F A Hd) H).
    + right. left. apply (proj1 (vtx_out_iff D E F B Hd) H).
    + right. right. apply (proj1 (vtx_out_iff D E F C Hd) H).
  - intros [H|[H|H]]; apply orb_true_iff.
    + left. apply orb_true_iff. left.
      apply (proj2 (vtx_out_iff D E F A Hd) H).
    + left. apply orb_true_iff. right.
      apply (proj2 (vtx_out_iff D E F B Hd) H).
    + right. apply (proj2 (vtx_out_iff D E F C Hd) H).
Qed.

Lemma ie_cell_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  ie_entry A B C D E F = Dim2 <->
  ~ in_tri D E F A \/ ~ in_tri D E F B \/ ~ in_tri D E F C.
Proof.
  intros A B C D E F HA HB. unfold ie_entry. split.
  - destruct (ie_hit A B C D E F) eqn:Hh; [| intros contra; discriminate].
    intros _. exact (proj1 (ie_hit_spec A B C D E F HB) Hh).
  - intros H. rewrite (proj2 (ie_hit_spec A B C D E F HB) H). reflexivity.
Qed.

Lemma be_cell_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  be_entry A B C D E F = Dim1 <->
  ~ in_tri D E F A \/ ~ in_tri D E F B \/ ~ in_tri D E F C.
Proof.
  intros A B C D E F HA HB. unfold be_entry. split.
  - destruct (ie_hit A B C D E F) eqn:Hh; [| intros contra; discriminate].
    intros _. exact (proj1 (ie_hit_spec A B C D E F HB) Hh).
  - intros H. rewrite (proj2 (ie_hit_spec A B C D E F HB) H). reflexivity.
Qed.

Lemma ei_cell_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  ei_entry A B C D E F = Dim2 <->
  ~ in_tri A B C D \/ ~ in_tri A B C E \/ ~ in_tri A B C F.
Proof.
  intros A B C D E F HA HB. unfold ei_entry. apply ie_cell_iff; assumption.
Qed.

Lemma eb_cell_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  eb_entry A B C D E F = Dim1 <->
  ~ in_tri A B C D \/ ~ in_tri A B C E \/ ~ in_tri A B C F.
Proof.
  intros A B C D E F HA HB. unfold eb_entry. apply be_cell_iff; assumption.
Qed.

Lemma in_tri_dec : forall A B C X,
  0 < cross A B C -> {in_tri A B C X} + {~ in_tri A B C X}.
Proof.
  intros A B C X Hd.
  destruct (Rle_dec 0 (cross A B X)) as [Hab|Hab];
  destruct (Rle_dec 0 (cross B C X)) as [Hbc|Hbc];
  destruct (Rle_dec 0 (cross C A X)) as [Hca|Hca].
  - left. apply (proj1 (tri_slack_hull A B C X Hd)). repeat split; assumption.
  - right. apply (out_of_cross A B C X Hd). right. right. apply Rnot_le_lt. exact Hca.
  - right. apply (out_of_cross A B C X Hd). right. left. apply Rnot_le_lt. exact Hbc.
  - right. apply (out_of_cross A B C X Hd). right. left. apply Rnot_le_lt. exact Hbc.
  - right. apply (out_of_cross A B C X Hd). left. apply Rnot_le_lt. exact Hab.
  - right. apply (out_of_cross A B C X Hd). left. apply Rnot_le_lt. exact Hab.
  - right. apply (out_of_cross A B C X Hd). left. apply Rnot_le_lt. exact Hab.
  - right. apply (out_of_cross A B C X Hd). left. apply Rnot_le_lt. exact Hab.
Qed.

Lemma ie_open_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  ie_entry A B C D E F = Dim2 <->
  exists X, tri_open A B C X /\ ~ in_tri D E F X.
Proof.
  intros A B C D E F HA HB. split.
  - intros Hent.
    destruct (proj1 (ie_cell_iff A B C D E F HA HB) Hent) as [H|[H|H]].
    + apply spread_vertex with (V := A); try assumption.
      apply vertex_in_tri. simpl. left. reflexivity.
    + apply spread_vertex with (V := B); try assumption.
      apply vertex_in_tri. simpl. right. left. reflexivity.
    + apply spread_vertex with (V := C); try assumption.
      apply vertex_in_tri. simpl. right. right. left. reflexivity.
  - intros [X [Ho Hout]].
    apply ie_cell_iff; try assumption.
    assert (Hall : ~ (in_tri D E F A /\ in_tri D E F B /\ in_tri D E F C)).
    { intros [Ha [Hb Hc]]. apply Hout.
      apply (verts_in_subset A B C D E F X HB Ha Hb Hc).
      apply tri_open_in; [exact HA | exact Ho]. }
    destruct (in_tri_dec D E F A HB) as [Ha|Ha];
    destruct (in_tri_dec D E F B HB) as [Hb|Hb];
    destruct (in_tri_dec D E F C HB) as [Hc|Hc].
    + exfalso. apply Hall. repeat split; assumption.
    + right. right. exact Hc.
    + right. left. exact Hb.
    + right. left. exact Hb.
    + left. exact Ha.
    + left. exact Ha.
    + left. exact Ha.
    + left. exact Ha.
Qed.

Lemma vertex_on_bd : forall A B C,
  on_bd A B C A /\ on_bd A B C B /\ on_bd A B C C.
Proof.
  intros A B C. split; [| split].
  - left. exact (proj1 (seg_ends A B)).
  - right. left. exact (proj1 (seg_ends B C)).
  - right. right. exact (proj1 (seg_ends C A)).
Qed.

Lemma combo_scale : forall V W t s,
  convex_combination V (convex_combination V W t) s =
  convex_combination V W (s * t).
Proof.
  intros V W t s. unfold convex_combination.
  destruct V as [vx vy], W as [wx wy]. simpl. f_equal; ring.
Qed.

Lemma seg_on_edge : forall V W Q t,
  Q = convex_combination V W t -> 0 <= t <= 1 ->
  forall X, on_seg V Q X -> on_seg V W X.
Proof.
  intros V W Q t HQ Ht X [s [Hs HX]].
  exists (s * t). split.
  - destruct Hs as [Hs0 Hs1]. destruct Ht as [Ht0 Ht1]. split.
    + apply Rmult_le_pos; assumption.
    + apply Rle_trans with (r2 := s).
      * assert (Hst : s * t <= s * 1).
        { apply Rmult_le_compat_l; [exact Hs0 | exact Ht1]. }
        rewrite Rmult_1_r in Hst. exact Hst.
      * exact Hs1.
  - rewrite HX, HQ. apply combo_scale.
Qed.

Lemma combo_neq : forall V W t,
  V <> W -> 0 < t -> convex_combination V W t <> V.
Proof.
  intros V W t HV Ht Heq.
  assert (Ez : t = 0).
  { apply (combo_inj V W t 0 HV). rewrite (combo_left V W). exact Heq. }
  lra.
Qed.

Lemma neg_cross_prefix : forall (bad : Point -> R) D E F V W,
  0 < cross D E F -> V <> W -> bad V < 0 ->
  (forall X, bad X < 0 -> ~ in_tri D E F X) ->
  (forall r, bad (convex_combination V W r) =
     (1 - r) * bad V + r * bad W) ->
  exists P Q, P <> Q /\
    (forall X, on_seg P Q X -> on_seg V W X) /\
    (forall X, on_seg P Q X -> ~ in_tri D E F X).
Proof.
  intros bad D E F V W Harea HVW Hneg Hout Hlin.
  destruct (neg_prefix (bad V) (bad W) Hneg) as [t [Ht Hall]].
  set (Q := convex_combination V W t).
  exists V, Q. split; [| split].
  - intro Heq. symmetry in Heq.
    exact (combo_neq V W t HVW (proj1 Ht) Heq).
  - intros X HX.
    assert (HQ : Q = convex_combination V W t) by reflexivity.
    apply (seg_on_edge V W Q t HQ).
    + split; [apply Rlt_le; exact (proj1 Ht) | exact (proj2 Ht)].
    + exact HX.
  - intros X [s [Hs HX]]. apply Hout.
    assert (HQ : Q = convex_combination V W t) by reflexivity.
    rewrite HX, HQ, combo_scale, Hlin. apply Hall. split.
    + apply Rmult_le_pos; [exact (proj1 Hs) | apply Rlt_le; exact (proj1 Ht)].
    + assert (Hle : s * t <= 1 * t).
      { apply Rmult_le_compat_r; [apply Rlt_le; exact (proj1 Ht) | exact (proj2 Hs)]. }
      rewrite Rmult_1_l in Hle. exact Hle.
Qed.

Lemma edge_out_prefix : forall D E F V W,
  0 < cross D E F -> V <> W -> ~ in_tri D E F V ->
  exists P Q, P <> Q /\
    (forall X, on_seg P Q X -> on_seg V W X) /\
    (forall X, on_seg P Q X -> ~ in_tri D E F X).
Proof.
  intros D E F V W Harea HVW Hout.
  destruct (not_in_cross D E F V Harea Hout) as [Hc|[Hc|Hc]].
  - apply (neg_cross_prefix (fun X => cross D E X) D E F V W Harea HVW Hc).
    + intros X HX. apply (out_of_cross D E F X Harea). left. exact HX.
    + intros r. apply (cross_combo D E V W r).
  - apply (neg_cross_prefix (fun X => cross E F X) D E F V W Harea HVW Hc).
    + intros X HX. apply (out_of_cross D E F X Harea). right. left. exact HX.
    + intros r. apply (cross_combo E F V W r).
  - apply (neg_cross_prefix (fun X => cross F D X) D E F V W Harea HVW Hc).
    + intros X HX. apply (out_of_cross D E F X Harea). right. right. exact HX.
    + intros r. apply (cross_combo F D V W r).
Qed.

Lemma be_bd_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  be_entry A B C D E F = Dim1 <->
  exists P Q, P <> Q /\
    (exists e, In e (e3 A B C) /\
       forall X, on_seg P Q X -> on_seg (fst e) (snd e) X) /\
    (forall X, on_seg P Q X -> ~ in_tri D E F X).
Proof.
  intros A B C D E F HA HB. split.
  - intros Hent.
    destruct (proj1 (be_cell_iff A B C D E F HA HB) Hent) as [H|[H|H]].
    + destruct (edge_sep A B C HA) as [Hab _].
      destruct (edge_out_prefix D E F A B HB Hab H)
        as [P [Q [Hneq [Hon Hout]]]].
      exists P, Q. split; [exact Hneq|]. split; [| exact Hout].
      exists (A, B). split; [| simpl; exact Hon].
      unfold e3. simpl. left. reflexivity.
    + destruct (edge_sep A B C HA) as [_ [Hbc _]].
      destruct (edge_out_prefix D E F B C HB Hbc H)
        as [P [Q [Hneq [Hon Hout]]]].
      exists P, Q. split; [exact Hneq|]. split; [| exact Hout].
      exists (B, C). split; [| simpl; exact Hon].
      unfold e3. simpl. right. left. reflexivity.
    + destruct (edge_sep A B C HA) as [_ [_ Hca]].
      destruct (edge_out_prefix D E F C A HB Hca H)
        as [P [Q [Hneq [Hon Hout]]]].
      exists P, Q. split; [exact Hneq|]. split; [| exact Hout].
      exists (C, A). split; [| simpl; exact Hon].
      unfold e3. simpl. right. right. left. reflexivity.
  - intros [P [Q [_ [He Hout]]]].
    destruct He as [e [Hin Hsub]].
    assert (Hend : on_seg P Q P) by exact (proj1 (seg_ends P Q)).
    assert (Hb : on_bd A B C P).
    { apply (seg_e3_bd A B C e P Hin). apply Hsub. exact Hend. }
    assert (Hp : ~ in_tri D E F P) by (apply Hout; exact Hend).
    apply be_cell_iff; try assumption.
    assert (Hall : ~ (in_tri D E F A /\ in_tri D E F B /\ in_tri D E F C)).
    { intros [Ha [Hbv Hc]]. apply Hp.
      apply (verts_in_subset A B C D E F P HB Ha Hbv Hc).
      apply on_bd_in_tri. exact Hb. }
    destruct (in_tri_dec D E F A HB) as [Ha|Ha];
    destruct (in_tri_dec D E F B HB) as [Hbv|Hbv];
    destruct (in_tri_dec D E F C HB) as [Hc|Hc].
    + exfalso. apply Hall. repeat split; assumption.
    + right. right. exact Hc.
    + right. left. exact Hbv.
    + right. left. exact Hbv.
    + left. exact Ha.
    + left. exact Ha.
    + left. exact Ha.
    + left. exact Ha.
Qed.

Lemma ei_open_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  ei_entry A B C D E F = Dim2 <->
  exists X, tri_open D E F X /\ ~ in_tri A B C X.
Proof.
  intros A B C D E F HA HB. unfold ei_entry.
  apply (ie_open_iff D E F A B C HB HA).
Qed.

Lemma eb_bd_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  eb_entry A B C D E F = Dim1 <->
  exists P Q, P <> Q /\
    (exists e, In e (e3 D E F) /\
       forall X, on_seg P Q X -> on_seg (fst e) (snd e) X) /\
    (forall X, on_seg P Q X -> ~ in_tri A B C X).
Proof.
  intros A B C D E F HA HB. unfold eb_entry.
  apply (be_bd_iff D E F A B C HB HA).
Qed.

Lemma be_boundary_closed : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  in_tri D E F A -> in_tri D E F B -> in_tri D E F C ->
  be_entry A B C D E F = DimF /\ ie_entry A B C D E F = DimF.
Proof.
  intros A B C D E F HA HB Ha Hb Hc.
  assert (Hhit : ie_hit A B C D E F = false).
  { destruct (ie_hit A B C D E F) eqn:Eh; [| reflexivity].
    destruct (proj1 (ie_hit_spec A B C D E F HB) Eh) as [H|[H|H]].
    - exfalso. exact (H Ha).
    - exfalso. exact (H Hb).
    - exfalso. exact (H Hc). }
  unfold be_entry, ie_entry. rewrite Hhit. split; reflexivity.
Qed.

Lemma ee_always : forall A B C D E F,
  ee_entry A B C D E F = Dim2.
Proof. intros. reflexivity. Qed.

Lemma px_in_tri_le : forall A B C X,
  in_tri A B C X -> px X <= Rmax (px A) (Rmax (px B) (px C)).
Proof.
  intros A B C X [a [b [c [Ha [Hb [Hc [Hs ->]]]]]]].
  set (m := Rmax (px A) (Rmax (px B) (px C))).
  assert (HAm : px A <= m) by (unfold m; apply Rmax_l).
  assert (HBm : px B <= m).
  { unfold m. apply Rle_trans with (r2 := Rmax (px B) (px C)).
    - apply Rmax_l.
    - apply Rmax_r. }
  assert (HCm : px C <= m).
  { unfold m. apply Rle_trans with (r2 := Rmax (px B) (px C)).
    - apply Rmax_r.
    - apply Rmax_r. }
  unfold bary3. simpl.
  apply Rle_trans with (r2 := a * m + b * m + c * m).
  - apply Rplus_le_compat; [apply Rplus_le_compat |].
    + apply Rmult_le_compat_l; assumption.
    + apply Rmult_le_compat_l; assumption.
    + apply Rmult_le_compat_l; assumption.
  - replace (a * m + b * m + c * m) with ((a + b + c) * m) by ring.
    rewrite Hs. lra.
Qed.

Lemma ee_witness : forall A B C D E F,
  exists X, ~ in_tri A B C X /\ ~ in_tri D E F X.
Proof.
  intros A B C D E F.
  set (mA := Rmax (px A) (Rmax (px B) (px C))).
  set (mD := Rmax (px D) (Rmax (px E) (px F))).
  set (far := Rmax mA mD + 1).
  exists (mkPoint far 0). split.
  - intros Hin.
    assert (Hlt : mA < far).
    { assert (Hm : mA <= Rmax mA mD) by apply Rmax_l. unfold far. lra. }
    assert (Hle : far <= mA).
    { replace far with (px (mkPoint far 0)) by reflexivity.
      apply (px_in_tri_le A B C). exact Hin. }
    exact (Rlt_not_le far mA Hlt Hle).
  - intros Hin.
    assert (Hlt : mD < far).
    { assert (Hm : mD <= Rmax mA mD) by apply Rmax_r. unfold far. lra. }
    assert (Hle : far <= mD).
    { replace far with (px (mkPoint far 0)) by reflexivity.
      apply (px_in_tri_le D E F). exact Hin. }
    exact (Rlt_not_le far mD Hlt Hle).
Qed.

Definition tri_de9im (A B C D E F : Point) : IntersectionMatrix :=
  {| im_ii := ii_entry A B C D E F;
     im_ib := ib_entry A B C D E F;
     im_ie := ie_entry A B C D E F;
     im_bi := bi_entry A B C D E F;
     im_bb := bb_entry A B C D E F;
     im_be := be_entry A B C D E F;
     im_ei := ie_entry D E F A B C;
     im_eb := be_entry D E F A B C;
     im_ee := ee_entry A B C D E F |}.

Lemma tri_de9im_entries : forall A B C D E F,
  im_ii (tri_de9im A B C D E F) = ii_entry A B C D E F /\
  im_ib (tri_de9im A B C D E F) = ib_entry A B C D E F /\
  im_ie (tri_de9im A B C D E F) = ie_entry A B C D E F /\
  im_bi (tri_de9im A B C D E F) = bi_entry A B C D E F /\
  im_bb (tri_de9im A B C D E F) = bb_entry A B C D E F /\
  im_be (tri_de9im A B C D E F) = be_entry A B C D E F /\
  im_ei (tri_de9im A B C D E F) = ei_entry A B C D E F /\
  im_eb (tri_de9im A B C D E F) = eb_entry A B C D E F /\
  im_ee (tri_de9im A B C D E F) = ee_entry A B C D E F.
Proof.
  intros. unfold tri_de9im, ei_entry, eb_entry. repeat split; reflexivity.
Qed.

Definition orient_ccw (A B C : Point) : Point * Point * Point :=
  if Rlt_dec (cross A B C) 0 then ((A, C), B) else ((A, B), C).

Definition tri_de9im_orient (A B C D E F : Point) : IntersectionMatrix :=
  match orient_ccw A B C with
  | ((A', B'), C') =>
      match orient_ccw D E F with
      | ((D', E'), F') => tri_de9im A' B' C' D' E' F'
      end
  end.

Lemma orient_ccw_pos : forall A B C,
  0 < cross A B C -> orient_ccw A B C = ((A, B), C).
Proof.
  intros A B C H. unfold orient_ccw.
  destruct (Rlt_dec (cross A B C) 0) as [Hlt|Hnot].
  - exfalso. apply (Rlt_not_le 0 (cross A B C) Hlt). apply Rlt_le. exact H.
  - reflexivity.
Qed.

Lemma orient_ccw_neg : forall A B C,
  cross A B C < 0 -> orient_ccw A B C = ((A, C), B).
Proof.
  intros A B C H. unfold orient_ccw.
  destruct (Rlt_dec (cross A B C) 0) as [Hlt|Hnot].
  - reflexivity.
  - exfalso. exact (Hnot H).
Qed.

Lemma orient_swap_pos : forall A B C,
  cross A B C < 0 -> 0 < cross A C B.
Proof.
  intros A B C H. rewrite (cross_swap A C B). lra.
Qed.

Lemma tri_de9im_orient_ccw : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  tri_de9im_orient A B C D E F = tri_de9im A B C D E F.
Proof.
  intros A B C D E F HA HB. unfold tri_de9im_orient.
  rewrite (orient_ccw_pos A B C HA).
  rewrite (orient_ccw_pos D E F HB).
  reflexivity.
Qed.

Theorem exterior_cells_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  (ie_entry A B C D E F = Dim2 <->
     exists X, tri_open A B C X /\ ~ in_tri D E F X) /\
  (be_entry A B C D E F = Dim1 <->
     exists P Q, P <> Q /\
       (exists e, In e (e3 A B C) /\
          forall X, on_seg P Q X -> on_seg (fst e) (snd e) X) /\
       (forall X, on_seg P Q X -> ~ in_tri D E F X)) /\
  (ei_entry A B C D E F = Dim2 <->
     exists X, tri_open D E F X /\ ~ in_tri A B C X) /\
  (eb_entry A B C D E F = Dim1 <->
     exists P Q, P <> Q /\
       (exists e, In e (e3 D E F) /\
          forall X, on_seg P Q X -> on_seg (fst e) (snd e) X) /\
       (forall X, on_seg P Q X -> ~ in_tri A B C X)) /\
  (ee_entry A B C D E F = Dim2) /\
  (exists X, ~ in_tri A B C X /\ ~ in_tri D E F X).
Proof.
  intros A B C D E F HA HB.
  split; [| split; [| split; [| split; [| split]]]].
  - apply ie_open_iff; assumption.
  - apply be_bd_iff; assumption.
  - apply ei_open_iff; assumption.
  - apply eb_bd_iff; assumption.
  - apply ee_always.
  - apply ee_witness.
Qed.

Ltac ext_area := unfold cross; simpl; lra.
Ltac ext_notin_ab :=
  apply out_of_cross; [ext_area | left; unfold cross; simpl; lra].
Ltac ext_notin_bc :=
  apply out_of_cross; [ext_area | right; left; unfold cross; simpl; lra].
Ltac ext_notin_ca :=
  apply out_of_cross; [ext_area | right; right; unfold cross; simpl; lra].
Ltac ext_vtx1 := apply vertex_in_tri; simpl; left; reflexivity.
Ltac ext_vtx2 := apply vertex_in_tri; simpl; right; left; reflexivity.
Ltac ext_open := apply tri_open_in; unfold tri_open, cross; simpl; lra.

Lemma exterior_entry_fixtures :
  ie_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = Dim2 /\
  be_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = Dim1 /\
  ie_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = DimF /\
  be_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = DimF /\
  ie_entry (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) = Dim2 /\
  be_entry (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) = Dim1 /\
  ie_entry (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1)
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) = Dim2 /\
  be_entry (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1)
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) = Dim1 /\
  ie_entry (mkPoint 1 1) (mkPoint 2 1) (mkPoint 1 2)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = DimF /\
  be_entry (mkPoint 1 1) (mkPoint 2 1) (mkPoint 1 2)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = DimF /\
  ie_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 1 1) (mkPoint 2 1) (mkPoint 1 2) = Dim2 /\
  be_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 1 1) (mkPoint 2 1) (mkPoint 1 2) = Dim1 /\
  ie_entry (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = Dim2 /\
  be_entry (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = Dim1 /\
  ie_entry (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) = Dim2 /\
  be_entry (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) = Dim1 /\
  ee_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = Dim2 /\
  ee_entry (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) = Dim2 /\
  ee_entry (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = Dim2 /\
  im_ie (tri_de9im (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)) = Dim2 /\
  im_be (tri_de9im (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)) = Dim1 /\
  im_ee (tri_de9im (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)) = Dim2.
Proof.
  (* ee_entry and im_ee reduce to Dim2, so split closes them. *)
  repeat split.
  - apply (proj2 (ie_cell_iff (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
      (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) ltac:(ext_area) ltac:(ext_area))).
    right. right. ext_notin_bc.
  - apply (proj2 (be_cell_iff (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
      (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) ltac:(ext_area) ltac:(ext_area))).
    right. right. ext_notin_bc.
  - apply (proj2 (be_boundary_closed (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
      (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) ltac:(ext_area) ltac:(ext_area)
      ltac:(ext_vtx1) ltac:(ext_vtx2) ltac:(ext_open))).
  - apply (proj1 (be_boundary_closed (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
      (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) ltac:(ext_area) ltac:(ext_area)
      ltac:(ext_vtx1) ltac:(ext_vtx2) ltac:(ext_open))).
  - apply (proj2 (ie_cell_iff (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
      (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) ltac:(ext_area) ltac:(ext_area))).
    left. ext_notin_ca.
  - apply (proj2 (be_cell_iff (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
      (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) ltac:(ext_area) ltac:(ext_area))).
    left. ext_notin_ca.
  - apply (proj2 (ie_cell_iff (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1)
      (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) ltac:(ext_area) ltac:(ext_area))).
    left. ext_notin_bc.
  - apply (proj2 (be_cell_iff (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1)
      (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) ltac:(ext_area) ltac:(ext_area))).
    left. ext_notin_bc.
  - apply (proj2 (be_boundary_closed (mkPoint 1 1) (mkPoint 2 1) (mkPoint 1 2)
      (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) ltac:(ext_area) ltac:(ext_area)
      ltac:(ext_open) ltac:(ext_open) ltac:(ext_open))).
  - apply (proj1 (be_boundary_closed (mkPoint 1 1) (mkPoint 2 1) (mkPoint 1 2)
      (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) ltac:(ext_area) ltac:(ext_area)
      ltac:(ext_open) ltac:(ext_open) ltac:(ext_open))).
  - apply (proj2 (ie_cell_iff (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
      (mkPoint 1 1) (mkPoint 2 1) (mkPoint 1 2) ltac:(ext_area) ltac:(ext_area))).
    left. ext_notin_ab.
  - apply (proj2 (be_cell_iff (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
      (mkPoint 1 1) (mkPoint 2 1) (mkPoint 1 2) ltac:(ext_area) ltac:(ext_area))).
    left. ext_notin_ab.
  - apply (proj2 (ie_cell_iff (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
      (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) ltac:(ext_area) ltac:(ext_area))).
    right. right. ext_notin_ca.
  - apply (proj2 (be_cell_iff (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
      (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) ltac:(ext_area) ltac:(ext_area))).
    right. right. ext_notin_ca.
  - apply (proj2 (ie_cell_iff (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)
      (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) ltac:(ext_area) ltac:(ext_area))).
    right. left. ext_notin_bc.
  - apply (proj2 (be_cell_iff (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)
      (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) ltac:(ext_area) ltac:(ext_area))).
    right. left. ext_notin_bc.
  - unfold tri_de9im. simpl.
    apply (proj2 (ie_cell_iff (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
      (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) ltac:(ext_area) ltac:(ext_area))).
    right. right. ext_notin_bc.
  - unfold tri_de9im. simpl.
    apply (proj2 (be_cell_iff (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
      (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) ltac:(ext_area) ltac:(ext_area))).
    right. right. ext_notin_bc.
Qed.

(* Assumptions: sig_not_dec, sig_forall_dec, functional_extensionality_dep. *)
Print Assumptions inner_open.
Print Assumptions near_open.
Print Assumptions neg_prefix.
Print Assumptions cross0_on_edge.
Print Assumptions in_tri_open_or_bd.
Print Assumptions vtx_on_bd_iff.
Print Assumptions vtx_out_iff.
Print Assumptions boundary_vertex_not_out.
Print Assumptions not_in_cross.
Print Assumptions out_of_cross.
Print Assumptions verts_in_subset.
Print Assumptions spread_vertex.
Print Assumptions ie_hit_spec.
Print Assumptions ie_cell_iff.
Print Assumptions be_cell_iff.
Print Assumptions ei_cell_iff.
Print Assumptions eb_cell_iff.
Print Assumptions in_tri_dec.
Print Assumptions ie_open_iff.
Print Assumptions vertex_on_bd.
Print Assumptions combo_scale.
Print Assumptions seg_on_edge.
Print Assumptions combo_neq.
Print Assumptions neg_cross_prefix.
Print Assumptions edge_out_prefix.
Print Assumptions be_bd_iff.
Print Assumptions ei_open_iff.
Print Assumptions eb_bd_iff.
Print Assumptions be_boundary_closed.
Print Assumptions ee_always.
Print Assumptions px_in_tri_le.
Print Assumptions ee_witness.
Print Assumptions tri_de9im_entries.
Print Assumptions orient_ccw_pos.
Print Assumptions orient_ccw_neg.
Print Assumptions orient_swap_pos.
Print Assumptions tri_de9im_orient_ccw.
Print Assumptions exterior_cells_iff.
Print Assumptions exterior_entry_fixtures.
