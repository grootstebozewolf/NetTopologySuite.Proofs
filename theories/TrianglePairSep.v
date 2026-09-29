(* NetTopologySuite.Proofs.TrianglePairSep
   Wedge half of the separating-edge follow-up. sat_iff is deferred:
   the cQ = 0 leaf, the Z2 orbit, and the boundary mixture are open.
   Not Admitted. I∩B / B∩I / B∩B are T1b. Exterior cells are T1c.
   topic: relate
   claimId: tri-de9im-a
   witness: none
   3-axiom host. No Jordan.
   AI-drafted (Cursor Grok 4.7), human-reviewed.
   License: BSD-3-Clause *)

From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex Centroid
  ConvexClip TrianglePairCommon.
Local Open Scope R_scope.

Lemma sep_nb_A : forall A B C P Q,
  cross P Q A * cross A B C =
    - (cross A B P * cross C A Q - cross A B Q * cross C A P).
Proof.
  intros A B C P Q. unfold cross.
  destruct A, B, C, P, Q. simpl. ring.
Qed.

Lemma sep_nb_B : forall A B C P Q,
  cross P Q B * cross A B C =
    - (cross A B P * cross C A Q - cross A B Q * cross C A P
       + cross A B C * (cross A B Q - cross A B P)).
Proof.
  intros A B C P Q. unfold cross.
  destruct A, B, C, P, Q. simpl. ring.
Qed.

Lemma sep_nb_C : forall A B C P Q,
  cross P Q C * cross A B C =
    - (cross A B P * cross C A Q - cross A B Q * cross C A P
       + cross A B C * (cross C A P - cross C A Q)).
Proof.
  intros A B C P Q. unfold cross.
  destruct A, B, C, P, Q. simpl. ring.
Qed.

Lemma nb_outer : forall A B C P Q,
  0 < cross A B C ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  0 < cross C A P ->
  0 <= cross A B P * cross C A Q - cross A B Q * cross C A P ->
  outer3 P Q A B C.
Proof.
  intros A B C P Q Hd HpN HqP HpB Hnb.
  set (Nb := cross A B P * cross C A Q - cross A B Q * cross C A P) in *.
  assert (HbQ : cross C A Q < 0).
  { destruct (Rle_dec 0 (cross C A Q)) as [Hq|Hq].
    - assert (Hpos : 0 <= ((- cross A B P) * cross C A Q)).
      { apply Rmult_le_pos; lra. }
      assert (Hleft : cross A B P * cross C A Q <= 0).
      { assert (E : cross A B P * cross C A Q
                    + (- cross A B P) * cross C A Q = 0) by ring.
        lra. }
      assert (Hright : 0 < cross A B Q * cross C A P).
      { apply Rmult_lt_0_compat; assumption. }
      unfold Nb in Hnb. lra.
    - apply Rnot_le_lt. exact Hq. }
  assert (HgapB : 0 < cross C A P - cross C A Q) by lra.
  assert (HgapC : 0 < cross A B Q - cross A B P) by lra.
  assert (HA : cross P Q A * cross A B C = - Nb) by (apply sep_nb_A).
  assert (HB : cross P Q B * cross A B C = - (Nb + cross A B C * (cross A B Q - cross A B P))).
  { rewrite sep_nb_B. unfold Nb. ring. }
  assert (HC : cross P Q C * cross A B C = - (Nb + cross A B C * (cross C A P - cross C A Q))).
  { rewrite sep_nb_C. unfold Nb. ring. }
  assert (HAp : Nb + cross A B C * (cross A B Q - cross A B P) > 0).
  { apply Rplus_le_lt_0_compat; [exact Hnb |]. apply Rmult_lt_0_compat; assumption. }
  assert (HCp : Nb + cross A B C * (cross C A P - cross C A Q) > 0).
  { apply Rplus_le_lt_0_compat; [exact Hnb |]. apply Rmult_lt_0_compat; assumption. }
  repeat split.
  - apply Rmult_le_reg_r with (r := cross A B C); [exact Hd |].
    rewrite HA. lra.
  - apply Rmult_le_reg_r with (r := cross A B C); [exact Hd |].
    rewrite HB. lra.
  - apply Rmult_le_reg_r with (r := cross A B C); [exact Hd |].
    rewrite HC. lra.
Qed.


Lemma cross_centroid3 : forall p q A B C,
  cross p q (centroid3 A B C) =
    (cross p q A + cross p q B + cross p q C) / 3.
Proof.
  intros p q A B C. unfold centroid3, cross.
  destruct p, q, A, B, C. simpl. field.
Qed.

Lemma vertex_in_tri : forall A B C V,
  In V [A; B; C] -> in_tri A B C V.
Proof.
  intros A B C V Hin. apply in_tri_hull3. apply in_hull_in. exact Hin.
Qed.

Lemma slack_pos_room : forall sx sg t,
  0 < sx -> 0 <= t -> t < seg_room sx sg ->
  0 < (1 - t) * sx + t * sg.
Proof.
  intros sx sg t Hs Ht0 Ht. unfold seg_room in Ht.
  destruct (Rle_dec 0 (sg - sx)) as [Hg|Hg].
  - replace ((1 - t) * sx + t * sg) with (sx + t * (sg - sx)) by ring.
    assert (0 <= t * (sg - sx)) by (apply Rmult_le_pos; lra).
    lra.
  - apply Rnot_le_lt in Hg.
    assert (Hd : 0 < sx - sg) by lra.
    assert (Hnz : sx - sg <> 0).
    { apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
    replace ((1 - t) * sx + t * sg)
      with ((sx - sg) * (sx / (sx - sg) - t)) by (field; exact Hnz).
    apply Rmult_lt_0_compat; lra.
Qed.

Lemma tri_vertex_slack : forall A B C,
  cross A B A = 0 /\ cross B C A = cross A B C /\ cross C A A = 0.
Proof.
  intros A B C. repeat split.
  - apply cross_third_eq_first.
  - rewrite <- cross_cycle. reflexivity.
  - apply cross_third_eq_second.
Qed.

Lemma slack_mix_pos : forall sV sG t,
  0 <= sV -> 0 < sG -> 0 < t -> t <= 1 ->
  0 < (1 - t) * sV + t * sG.
Proof.
  intros sV sG t Hv Hg Ht0 Ht1.
  assert (H1 : 0 <= (1 - t) * sV) by (apply Rmult_le_pos; lra).
  assert (H2 : 0 < t * sG) by (apply Rmult_lt_0_compat; assumption).
  lra.
Qed.

Lemma own_centroid_open : forall A B C,
  0 < cross A B C -> tri_open A B C (centroid3 A B C).
Proof.
  intros A B C Hd. repeat split; rewrite cross_centroid3.
  - rewrite (cross_third_eq_first A B). rewrite (cross_third_eq_second A B).
    apply Rdiv_lt_0_compat; lra.
  - rewrite (cross_third_eq_second B C). rewrite (cross_third_eq_first B C).
    replace (cross B C A) with (cross A B C) by apply cross_cycle.
    apply Rdiv_lt_0_compat; lra.
  - rewrite (cross_third_eq_second C A). rewrite (cross_third_eq_first C A).
    replace (cross C A B) with (cross A B C) by apply cross_cycle2.
    apply Rdiv_lt_0_compat; lra.
Qed.

Lemma meet_vertex : forall A B C D E F V,
  0 < cross A B C -> 0 < cross D E F ->
  In V [D; E; F] ->
  tri_open A B C V ->
  exists X, tri_open A B C X /\ tri_open D E F X.
Proof.
  intros A B C D E F V HA HB Hin HV.
  set (G := centroid3 D E F).
  assert (HG : tri_open D E F G) by (unfold G; apply own_centroid_open; exact HB).
  destruct HV as [Hab [Hbc Hca]].
  destruct HG as [Gab [Gbc Gca]].
  assert (Vin : in_tri D E F V) by (apply vertex_in_tri; exact Hin).
  assert (SV : 0 <= cross D E V /\ 0 <= cross E F V /\ 0 <= cross F D V).
  { apply (proj2 (tri_slack_hull D E F V HB)). exact Vin. }
  destruct SV as [SVde [SVef SVfd]].
  set (rooms :=
    [ seg_room (cross A B V) (cross A B G);
      seg_room (cross B C V) (cross B C G);
      seg_room (cross C A V) (cross C A G) ]).
  set (t := rmin_list rooms).
  assert (Ht : 0 < t).
  { unfold t, rooms. apply rmin_list_pos. intros s Hs. simpl in Hs.
    destruct Hs as [<-|[<-|[<-|[]]]].
    - apply seg_room_pos. exact Hab.
    - apply seg_room_pos. exact Hbc.
    - apply seg_room_pos. exact Hca. }
  assert (Ht1 : t <= 1 / 2) by (unfold t; apply rmin_list_half).
  assert (Ht0 : 0 < t) by exact Ht.
  assert (RAB : t <= seg_room (cross A B V) (cross A B G)).
  { unfold t. apply rmin_list_le. unfold rooms. simpl. left. reflexivity. }
  assert (RBC : t <= seg_room (cross B C V) (cross B C G)).
  { unfold t. apply rmin_list_le. unfold rooms. simpl. right. left. reflexivity. }
  assert (RCA : t <= seg_room (cross C A V) (cross C A G)).
  { unfold t. apply rmin_list_le. unfold rooms. simpl. right. right. left. reflexivity. }
  (* Half the bound is strictly below every room and at most 1/4. *)
  set (u := t / 2).
  assert (Hu : 0 < u) by (unfold u; lra).
  assert (Hu1 : u <= 1) by (unfold u; lra).
  assert (HuAB : u < seg_room (cross A B V) (cross A B G)).
  { unfold u. assert (t / 2 < t) by lra.
    apply Rlt_le_trans with (r2 := t); assumption. }
  assert (HuBC : u < seg_room (cross B C V) (cross B C G)).
  { unfold u. apply Rlt_le_trans with (r2 := t); [lra | exact RBC]. }
  assert (HuCA : u < seg_room (cross C A V) (cross C A G)).
  { unfold u. apply Rlt_le_trans with (r2 := t); [lra | exact RCA]. }
  set (X := convex_combination V G u).
  exists X. split.
  - unfold X. repeat split; rewrite cross_combo.
    + apply slack_pos_room; [exact Hab | lra | exact HuAB].
    + apply slack_pos_room; [exact Hbc | lra | exact HuBC].
    + apply slack_pos_room; [exact Hca | lra | exact HuCA].
  - unfold X. repeat split; rewrite cross_combo.
    + apply slack_mix_pos; [exact SVde | exact Gab | exact Hu | exact Hu1].
    + apply slack_mix_pos; [exact SVef | exact Gbc | exact Hu | exact Hu1].
    + apply slack_mix_pos; [exact SVfd | exact Gca | exact Hu | exact Hu1].
Qed.

(* -------------------------------------------------------------------------- *)
(* A proper edge crossing puts a point in both open triangles.                *)
(* -------------------------------------------------------------------------- *)

Definition pdot (p q : Point) : R := px p * px q + py p * py q.

Definition left_n (p q : Point) : Point :=
  mkPoint (- (py q - py p)) (px q - px p).

Definition shift (h v : Point) (t : R) : Point :=
  mkPoint (px h + t * px v) (py h + t * py v).

Lemma pdot_left_sq : forall p q,
  pdot (left_n p q) (left_n p q) = dist_sq p q.
Proof. intros. unfold pdot, left_n, dist_sq. simpl. ring. Qed.

Lemma cross_shift : forall p q h v t,
  cross p q (shift h v t) = cross p q h + t * pdot (left_n p q) v.
Proof.
  intros. unfold cross, shift, pdot, left_n.
  destruct p, q, h, v. simpl. ring.
Qed.

Lemma sum_sqr_zero : forall x y, x * x + y * y = 0 -> x = 0 /\ y = 0.
Proof.
  intros x y H.
  assert (Hx : 0 <= x * x) by apply sqr_nonneg.
  assert (Hy : 0 <= y * y) by apply sqr_nonneg.
  assert (Ex : x * x = 0) by lra.
  assert (Ey : y * y = 0) by lra.
  split; apply sqr_eq_zero; assumption.
Qed.

Lemma dist_sq_pos_points : forall p q,
  points_distinct p q -> 0 < dist_sq p q.
Proof.
  intros p q Hdis.
  pose proof (dist_sq_nonneg p q) as Hnn.
  destruct (Req_dec (dist_sq p q) 0) as [Hz|Hnz].
  - exfalso. unfold dist_sq in Hz.
    destruct (sum_sqr_zero _ _ Hz) as [Hx Hy].
    destruct Hdis as [Hpx|Hpy].
    + apply Hpx. lra.
    + apply Hpy. lra.
  - lra.
Qed.

Lemma cross_ooo : forall o z, cross o o z = 0.
Proof. intros. unfold cross. ring. Qed.

Lemma ccw_edge_distinct : forall A B C,
  0 < cross A B C -> points_distinct A B.
Proof.
  intros A B C H. destruct (point_eqb A B) eqn:E.
  - apply point_eqb_true in E. subst B. rewrite cross_ooo in H. lra.
  - apply point_eqb_false_distinct. exact E.
Qed.

Lemma edge_len_pos : forall A B C,
  0 < cross A B C -> 0 < dist_sq A B.
Proof.
  intros A B C H. apply dist_sq_pos_points. apply (ccw_edge_distinct A B C H).
Qed.

Lemma opp_div_open : forall fa fb,
  fa * fb < 0 ->
  fa - fb <> 0 /\ 0 < fa / (fa - fb) /\ fa / (fa - fb) < 1.
Proof.
  intros fa fb Hneg.
  destruct (Rlt_dec 0 fa) as [Hfa|Hfa].
  - assert (Hfb : fb < 0).
    { destruct (Rle_dec 0 fb) as [Hfb|Hfb].
      - assert (0 <= fa * fb) by (apply Rmult_le_pos; lra). lra.
      - apply Rnot_le_lt. exact Hfb. }
    assert (Hd : 0 < fa - fb) by lra.
    split; [lra |]. split.
    + unfold Rdiv. apply Rmult_lt_0_compat; [exact Hfa | apply Rinv_0_lt_compat; exact Hd].
    + apply Rmult_lt_reg_r with (r := fa - fb); [exact Hd |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; lra.
  - apply Rnot_lt_le in Hfa.
    assert (Hfa0 : fa < 0).
    { destruct (Req_dec fa 0) as [Z|]; [| lra]. subst fa. lra. }
    assert (Hfb : 0 < fb).
    { destruct (Rle_dec fb 0) as [Hfb|Hfb].
      - assert (E : fa * fb = (- fa) * (- fb)) by ring.
        assert (0 <= (- fa) * (- fb)) by (apply Rmult_le_pos; lra).
        lra.
      - apply Rnot_le_lt. exact Hfb. }
    assert (Hd : 0 < - (fa - fb)) by lra.
    assert (Heq : fa / (fa - fb) = (- fa) / (- (fa - fb))) by (field; lra).
    split; [lra |]. rewrite Heq. split.
    + unfold Rdiv. apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hd].
    + apply Rmult_lt_reg_r with (r := - (fa - fb)); [exact Hd |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; lra.
Qed.

Lemma line_hit_comm : forall A B D E,
  cross A B D <> cross A B E ->
  cross D E A <> cross D E B ->
  line_hit A B D E = line_hit D E A B.
Proof.
  intros A B D E HAB HDE.
  destruct A as [ax ay], B as [bx by_], D as [dx dy], E as [ex ey].
  unfold line_hit, cross in *. simpl in *. f_equal; field; lra.
Qed.

Lemma proper_open_point : forall A B D E,
  cross A B D * cross A B E < 0 ->
  cross D E A * cross D E B < 0 ->
  exists h t s,
    0 < t < 1 /\ 0 < s < 1 /\
    h = convex_combination A B t /\
    h = convex_combination D E s.
Proof.
  intros A B D E HAB HDE.
  destruct (opp_div_open (cross D E A) (cross D E B) HDE)
    as [Hne1 [Ht0 Ht1]].
  destruct (opp_div_open (cross A B D) (cross A B E) HAB)
    as [Hne2 [Hs0 Hs1]].
  set (t := cross D E A / (cross D E A - cross D E B)).
  set (s := cross A B D / (cross A B D - cross A B E)).
  set (h := line_hit A B D E).
  assert (Ecomm : h = line_hit D E A B).
  { unfold h. apply line_hit_comm; lra. }
  exists h, t, s. split; [split; assumption |]. split; [split; assumption |]. split.
  - unfold h, t. rewrite line_hit_combo. reflexivity.
  - rewrite Ecomm. unfold s. rewrite line_hit_combo. reflexivity.
Qed.

Lemma open_seg_slacks : forall A B C X t,
  0 < cross A B C ->
  0 < t < 1 ->
  X = convex_combination A B t ->
  cross A B X = 0 /\ 0 < cross B C X /\ 0 < cross C A X.
Proof.
  intros A B C X t Hd Ht Hx. destruct Ht as [Ht0 Ht1]. subst X.
  assert (Hab : cross A B (convex_combination A B t) = 0).
  { rewrite cross_combo. rewrite cross_third_eq_first.
    assert (E : cross A B B = 0) by (unfold cross; ring). rewrite E. ring. }
  assert (Hbc : cross B C (convex_combination A B t) = (1 - t) * cross A B C).
  { rewrite cross_combo. rewrite cross_third_eq_first.
    assert (EA : cross B C A = cross A B C) by (rewrite <- cross_cycle; reflexivity).
    rewrite EA. ring. }
  assert (Hca : cross C A (convex_combination A B t) = t * cross A B C).
  { rewrite cross_combo. rewrite cross_third_eq_second.
    assert (EB : cross C A B = cross A B C) by (rewrite <- cross_cycle2; reflexivity).
    rewrite EB. ring. }
  repeat split.
  - exact Hab.
  - rewrite Hbc. apply Rmult_lt_0_compat; lra.
  - rewrite Hca. apply Rmult_lt_0_compat; assumption.
Qed.

Lemma lagrange_dot : forall n1 n2,
  pdot n1 n1 * pdot n2 n2 - pdot n1 n2 * pdot n1 n2 =
    (px n1 * py n2 - py n1 * px n2) * (px n1 * py n2 - py n1 * px n2).
Proof. intros. unfold pdot. destruct n1, n2. simpl. ring. Qed.

Lemma left_cross_diff : forall A B D E,
  px (left_n A B) * py (left_n D E) - py (left_n A B) * px (left_n D E) =
    cross A B E - cross A B D.
Proof. intros. unfold left_n, cross. destruct A, B, D, E. simpl. ring. Qed.

Lemma sqr_pos_neq : forall x, x <> 0 -> 0 < x * x.
Proof.
  intros x Hx.
  pose proof (sqr_nonneg x) as Hnn.
  destruct (Req_dec (x * x) 0) as [Hz|Hnz].
  - apply sqr_eq_zero in Hz. contradiction.
  - lra.
Qed.

Lemma inward_pair : forall n1 n2,
  0 < pdot n1 n1 ->
  0 < pdot n2 n2 ->
  px n1 * py n2 - py n1 * px n2 <> 0 ->
  exists v, 0 < pdot n1 v /\ 0 < pdot n2 v.
Proof.
  intros n1 n2 Ha Hb Hcr.
  set (d := pdot n1 n2).
  set (a2 := pdot n1 n1).
  set (b2 := pdot n2 n2).
  destruct (Rle_dec 0 d) as [Hd|Hd].
  - set (v := mkPoint (px n1 + px n2) (py n1 + py n2)).
    exists v. split.
    + assert (E : pdot n1 v = a2 + d).
      { unfold v, a2, d, pdot. destruct n1 as [x1 y1], n2 as [x2 y2]. simpl. ring. }
      rewrite E. apply Rplus_lt_le_0_compat; [unfold a2; exact Ha | exact Hd].
    + assert (E : pdot n2 v = b2 + d).
      { unfold v, b2, d, pdot. destruct n1 as [x1 y1], n2 as [x2 y2]. simpl. ring. }
      rewrite E. apply Rplus_lt_le_0_compat; [unfold b2; exact Hb | exact Hd].
  - apply Rnot_le_lt in Hd. unfold d in Hd.
    assert (Hdisc : 0 < pdot n1 n1 * pdot n2 n2 - pdot n1 n2 * pdot n1 n2).
    { rewrite lagrange_dot. apply sqr_pos_neq. exact Hcr. }
    assert (Ea : pdot n1 n1 <> 0).
    { intro Hz. rewrite Hz in Ha. apply (Rlt_irrefl 0). exact Ha. }
    assert (Ed : - pdot n1 n2 <> 0).
    { intro Hz. apply (f_equal Ropp) in Hz.
      rewrite Ropp_involutive, Ropp_0 in Hz. rewrite Hz in Hd.
      exact (Rlt_irrefl 0 Hd). }
    set (alpha := (pdot n1 n1 * pdot n2 n2 + pdot n1 n2 * pdot n1 n2)
                    / (2 * pdot n1 n1 * (- pdot n1 n2))).
    set (v := mkPoint (alpha * px n1 + px n2) (alpha * py n1 + py n2)).
    assert (E1 : pdot n1 v =
        (pdot n1 n1 * pdot n2 n2 - pdot n1 n2 * pdot n1 n2)
          / (2 * (- pdot n1 n2))).
    { assert (Ev : pdot n1 v = alpha * pdot n1 n1 + pdot n1 n2).
      { unfold v, pdot. destruct n1 as [x1 y1], n2 as [x2 y2]. simpl. ring. }
      rewrite Ev. unfold alpha. field. split.
      - intro Hz. rewrite Hz in Hd. exact (Rlt_irrefl 0 Hd).
      - exact Ea. }
    assert (E2 : pdot n2 v =
        (pdot n1 n1 * pdot n2 n2 - pdot n1 n2 * pdot n1 n2)
          / (2 * pdot n1 n1)).
    { assert (Ev : pdot n2 v = alpha * pdot n1 n2 + pdot n2 n2).
      { unfold v, pdot. destruct n1 as [x1 y1], n2 as [x2 y2]. simpl. ring. }
      rewrite Ev. unfold alpha. field. split.
      - exact Ea.
      - intro Hz. rewrite Hz in Hd. exact (Rlt_irrefl 0 Hd). }
    exists v. split.
    + rewrite E1. apply Rdiv_lt_0_compat.
      * exact Hdisc.
      * lra.
    + rewrite E2. apply Rdiv_lt_0_compat; [exact Hdisc |].
      apply Rmult_lt_0_compat; [lra | exact Ha].
Qed.

Definition step_room (s0 ds : R) : R :=
  if Rle_dec 0 ds then 1 else s0 / (2 * (- ds)).

Lemma step_room_pos : forall s0 ds, 0 < s0 -> 0 < step_room s0 ds.
Proof.
  intros s0 ds Hs. unfold step_room.
  destruct (Rle_dec 0 ds) as [_|Hds].
  - lra.
  - apply Rnot_le_lt in Hds.
    apply Rdiv_lt_0_compat; lra.
Qed.

Lemma slack_step_pos : forall s0 ds t,
  0 < s0 -> 0 < t -> t <= step_room s0 ds -> 0 < s0 + t * ds.
Proof.
  intros s0 ds t Hs Ht Hle. unfold step_room in Hle.
  destruct (Rle_dec 0 ds) as [Hd|Hd].
  - assert (0 <= t * ds) by (apply Rmult_le_pos; lra). lra.
  - apply Rnot_le_lt in Hd.
    assert (Hden : 0 < 2 * (- ds)) by lra.
    assert (Ht2 : t * (2 * (- ds)) <= s0).
    { apply Rmult_le_reg_r with (r := / (2 * (- ds))).
      - apply Rinv_0_lt_compat. exact Hden.
      - replace (t * (2 * (- ds)) * / (2 * (- ds))) with t by (field; lra).
        unfold Rdiv in Hle. exact Hle. }
    assert (E : t * (2 * (- ds)) = 2 * (t * (- ds))) by ring.
    lra.
Qed.

Lemma wedge_edges : forall A B C D E F,
  0 < cross A B C ->
  0 < cross D E F ->
  cross A B D * cross A B E < 0 ->
  cross D E A * cross D E B < 0 ->
  exists X, tri_open A B C X /\ tri_open D E F X.
Proof.
  intros A B C D E F HA HB HAB HDE.
  destruct (proper_open_point A B D E HAB HDE) as [h [t [s [Ht [Hs [HtX HsX]]]]]].
  destruct (open_seg_slacks A B C h t HA Ht HtX) as [Hab0 [Hbc0 Hca0]].
  destruct (open_seg_slacks D E F h s HB Hs HsX) as [Hde0 [Hef0 Hfd0]].
  set (n1 := left_n A B).
  set (n2 := left_n D E).
  assert (Hn1 : 0 < pdot n1 n1).
  { unfold n1. rewrite pdot_left_sq. apply edge_len_pos with (C := C). exact HA. }
  assert (Hn2 : 0 < pdot n2 n2).
  { unfold n2. rewrite pdot_left_sq. apply edge_len_pos with (C := F). exact HB. }
  assert (Hcr : px n1 * py n2 - py n1 * px n2 <> 0).
  { unfold n1, n2. rewrite left_cross_diff. intro Heq.
    assert (Heq' : cross A B E = cross A B D) by lra.
    assert (Hsq : cross A B D * cross A B E = cross A B D * cross A B D)
      by (rewrite Heq'; ring).
    assert (0 <= cross A B D * cross A B D) by apply sqr_nonneg.
    lra. }
  destruct (inward_pair n1 n2 Hn1 Hn2 Hcr) as [v [Hv1 Hv2]].
  set (dBC := pdot (left_n B C) v).
  set (dCA := pdot (left_n C A) v).
  set (dEF := pdot (left_n E F) v).
  set (dFD := pdot (left_n F D) v).
  set (r1 := step_room (cross B C h) dBC).
  set (r2 := step_room (cross C A h) dCA).
  set (r3 := step_room (cross E F h) dEF).
  set (r4 := step_room (cross F D h) dFD).
  set (u := Rmin (Rmin r1 r2) (Rmin r3 r4)).
  assert (Hu : 0 < u).
  { unfold u. apply Rmin_pos; apply Rmin_pos; apply step_room_pos; assumption. }
  assert (Hu1 : u <= r1).
  { unfold u. apply Rle_trans with (r2 := Rmin r1 r2); apply Rmin_l. }
  assert (Hu2 : u <= r2).
  { unfold u. apply Rle_trans with (r2 := Rmin r1 r2).
    - apply Rmin_l.
    - apply Rmin_r. }
  assert (Hu3 : u <= r3).
  { unfold u. apply Rle_trans with (r2 := Rmin r3 r4).
    - apply Rmin_r.
    - apply Rmin_l. }
  assert (Hu4 : u <= r4).
  { unfold u. apply Rle_trans with (r2 := Rmin r3 r4); apply Rmin_r. }
  set (X := shift h v u).
  exists X. split; unfold X, tri_open.
  - repeat split.
    + rewrite cross_shift. unfold n1 in Hv1.
      assert (Heq1 : cross A B h + u * pdot (left_n A B) v = u * pdot n1 v).
      { unfold n1. rewrite Hab0. ring. }
      rewrite Heq1. apply Rmult_lt_0_compat; assumption.
    + rewrite cross_shift. unfold r1, dBC in Hu1.
      apply slack_step_pos; assumption.
    + rewrite cross_shift. unfold r2, dCA in Hu2.
      apply slack_step_pos; assumption.
  - repeat split.
    + rewrite cross_shift. unfold n2 in Hv2.
      assert (Heq2 : cross D E h + u * pdot (left_n D E) v = u * pdot n2 v).
      { unfold n2. rewrite Hde0. ring. }
      rewrite Heq2. apply Rmult_lt_0_compat; assumption.
    + rewrite cross_shift. unfold r3, dEF in Hu3.
      apply slack_step_pos; assumption.
    + rewrite cross_shift. unfold r4, dFD in Hu4.
      apply slack_step_pos; assumption.
Qed.

(* Assumptions: sig_not_dec, sig_forall_dec, functional_extensionality_dep. *)
Print Assumptions sep_nb_A.
Print Assumptions sep_nb_B.
Print Assumptions sep_nb_C.
Print Assumptions nb_outer.
Print Assumptions cross_centroid3.
Print Assumptions vertex_in_tri.
Print Assumptions slack_pos_room.
Print Assumptions tri_vertex_slack.
Print Assumptions slack_mix_pos.
Print Assumptions own_centroid_open.
Print Assumptions meet_vertex.
Print Assumptions pdot_left_sq.
Print Assumptions cross_shift.
Print Assumptions sum_sqr_zero.
Print Assumptions dist_sq_pos_points.
Print Assumptions cross_ooo.
Print Assumptions ccw_edge_distinct.
Print Assumptions edge_len_pos.
Print Assumptions opp_div_open.
Print Assumptions line_hit_comm.
Print Assumptions proper_open_point.
Print Assumptions open_seg_slacks.
Print Assumptions lagrange_dot.
Print Assumptions left_cross_diff.
Print Assumptions sqr_pos_neq.
Print Assumptions inward_pair.
Print Assumptions step_room_pos.
Print Assumptions slack_step_pos.
Print Assumptions wedge_edges.
