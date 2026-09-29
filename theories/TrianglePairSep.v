(* NetTopologySuite.Proofs.TrianglePairSep
   Follow-up letter after T1a. Separating edge or interior meet for two
   positive triangles. sat_iff is not yet stated. Boundary cells and
   exterior cells are T1b and T1c. Not registered until sat_iff is Qed.
   topic: relate
   claimId: tri-de9im-a
   witness: TrianglePairClip.ii_nonempty_iff
   3-axiom host. No Admitted. No Jordan.
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

(* -------------------------------------------------------------------------- *)
(* A CCW edge that straddles a cap separates, or the interiors meet.          *)
(* -------------------------------------------------------------------------- *)

Lemma na_nb_sum : forall A B C P Q,
  (cross A B P * cross B C Q - cross A B Q * cross B C P)
  + (cross A B P * cross C A Q - cross A B Q * cross C A P)
  = cross A B C * (cross A B P - cross A B Q).
Proof. intros. unfold cross. destruct A, B, C, P, Q. simpl. ring. Qed.

Lemma cross_pq_B_na : forall A B C P Q,
  cross P Q B * cross A B C =
    cross A B P * cross B C Q - cross A B Q * cross B C P.
Proof. intros. unfold cross. destruct A, B, C, P, Q. simpl. ring. Qed.

Lemma pqc_na : forall A B C P Q,
  cross P Q C * cross A B C =
    (cross A B P * cross B C Q - cross A B Q * cross B C P)
    + cross A B C * (cross B C P - cross B C Q).
Proof. intros. unfold cross. destruct A, B, C, P, Q. simpl. ring. Qed.

Lemma au_aq_id : forall A B C P Q U,
  (cross B C U - cross B C Q) * (cross A B Q - cross A B P)
  = cross P Q U * cross A B C
    + (cross A B Q - cross A B U) * (cross B C P - cross B C Q).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma qu_B_minus_A : forall A B C Q U,
  cross Q U B * cross A B C =
    cross Q U A * cross A B C
    + cross A B C * (cross A B Q - cross A B U).
Proof. intros. unfold cross. destruct A, B, C, Q, U. simpl. ring. Qed.

Lemma qu_C_minus_B : forall A B C Q U,
  cross Q U C * cross A B C =
    cross Q U B * cross A B C
    + cross A B C * (cross B C Q - cross B C U).
Proof. intros. unfold cross. destruct A, B, C, Q, U. simpl. ring. Qed.

Lemma up_b_from_qu : forall A B C P Q U,
  cross U P B * cross A B Q * cross A B C
  + cross A B P * cross Q U B * cross A B C
  + cross A B U
      * (cross A B P * cross B C Q - cross A B Q * cross B C P) = 0.
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma aq_neg : forall A B C P Q,
  cross A B P < 0 ->
  0 < cross A B Q ->
  0 < cross B C P ->
  0 <= cross A B P * cross B C Q - cross A B Q * cross B C P ->
  cross B C Q < 0.
Proof.
  intros A B C P Q Hp Hq Ha Hna.
  destruct (Rle_dec 0 (cross B C Q)) as [Hq0|Hq0].
  - assert (Hle : cross A B P * cross B C Q <= cross A B P * 0).
    { apply Rmult_le_compat_neg_l; lra. }
    assert (Hpos : 0 < cross A B Q * cross B C P).
    { apply Rmult_lt_0_compat; assumption. }
    replace (cross A B P * 0) with 0 in Hle by ring. lra.
  - apply Rnot_le_lt. exact Hq0.
Qed.

Lemma au_gt_aq : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < cross A B Q ->
  cross A B U < cross A B Q ->
  cross B C Q < cross B C P ->
  cross B C Q < cross B C U.
Proof.
  intros A B C P Q U Hd Hs Hc HcU Ha.
  assert (Hid := au_aq_id A B C P Q U).
  assert (Hden : 0 < cross A B Q - cross A B P) by lra.
  apply Rmult_lt_reg_r with (r := cross A B Q - cross A B P).
  - exact Hden.
  - assert (Hpos : 0 < cross P Q U * cross A B C
                     + (cross A B Q - cross A B U)
                       * (cross B C P - cross B C Q)).
    { apply Rplus_lt_0_compat.
      - apply Rmult_lt_0_compat; assumption.
      - apply Rmult_lt_0_compat; lra. }
    rewrite <- Hid in Hpos. lra.
Qed.

Lemma touch_line_open : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross P Q B = 0 ->
  0 < cross Q U B ->
  0 < cross U P B ->
  0 < cross P Q A ->
  0 < cross P Q C ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U HA HB HpqB HquB HupB HpqA HpqC.
  set (G := centroid3 A B C).
  assert (HG : tri_open A B C G) by (unfold G; apply own_centroid_open; exact HA).
  destruct HG as [GAB [GBC GCA]].
  assert (HPQG : 0 < cross P Q G).
  { unfold G. rewrite cross_centroid3. rewrite HpqB.
    assert (Hs : 0 < cross P Q A + 0 + cross P Q C) by lra.
    unfold Rdiv. apply Rmult_lt_0_compat; [exact Hs | apply Rinv_0_lt_compat; lra]. }
  set (rQU := seg_room (cross Q U B) (cross Q U G)).
  set (rUP := seg_room (cross U P B) (cross U P G)).
  assert (HrQU : 0 < rQU) by (unfold rQU; apply seg_room_pos; exact HquB).
  assert (HrUP : 0 < rUP) by (unfold rUP; apply seg_room_pos; exact HupB).
  set (u := Rmin (Rmin rQU rUP / 2) (1 / 2)).
  assert (Hu : 0 < u).
  { unfold u. apply Rmin_pos; [ | lra].
    apply Rmult_lt_0_compat; [apply Rmin_pos; assumption | lra]. }
  assert (Hu1 : u <= 1).
  { unfold u. apply Rle_trans with (r2 := 1 / 2); [apply Rmin_r | lra]. }
  assert (Hhalf : 0 < Rmin rQU rUP) by (apply Rmin_pos; assumption).
  assert (HuQU : u < rQU).
  { apply Rlt_le_trans with (r2 := Rmin rQU rUP).
    - apply Rle_lt_trans with (r2 := Rmin rQU rUP / 2).
      + unfold u. apply Rmin_l.
      + apply Rmult_lt_reg_r with (r := 2); [lra |].
        field_simplify; lra.
    - apply Rmin_l. }
  assert (HuUP : u < rUP).
  { apply Rlt_le_trans with (r2 := Rmin rQU rUP).
    - apply Rle_lt_trans with (r2 := Rmin rQU rUP / 2).
      + unfold u. apply Rmin_l.
      + apply Rmult_lt_reg_r with (r := 2); [lra |].
        field_simplify; lra.
    - apply Rmin_r. }
  set (X := convex_combination B G u).
  exists X. split.
  - unfold X. repeat split; rewrite cross_combo.
    + replace (cross A B B) with 0 by (symmetry; apply cross_third_eq_second).
      replace ((1 - u) * 0 + u * cross A B G) with (u * cross A B G) by ring.
      apply Rmult_lt_0_compat; assumption.
    + replace (cross B C B) with 0 by (symmetry; apply cross_third_eq_first).
      replace ((1 - u) * 0 + u * cross B C G) with (u * cross B C G) by ring.
      apply Rmult_lt_0_compat; assumption.
    + apply slack_mix_pos.
      * rewrite <- cross_cycle2. apply Rlt_le. exact HA.
      * exact GCA.
      * exact Hu.
      * exact Hu1.
  - unfold X. repeat split; rewrite cross_combo.
    + rewrite HpqB. replace ((1 - u) * 0 + u * cross P Q G) with (u * cross P Q G) by ring.
      apply Rmult_lt_0_compat; assumption.
    + apply slack_pos_room; [exact HquB | lra | exact HuQU].
    + apply slack_pos_room; [exact HupB | lra | exact HuUP].
Qed.

Lemma na_cap_closed_u : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  cross A B U <= 0 ->
  0 < cross B C P ->
  0 <= cross A B P * cross B C Q - cross A B Q * cross B C P ->
  some_outer A B C P Q U \/ exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu HaP Hna.
  assert (Haq : cross B C Q < 0) by (apply aq_neg with (A := A) (B := B) (C := C) (P := P); assumption).
  assert (Hau : cross B C Q < cross B C U).
  { apply au_gt_aq with (A := A) (B := B) (C := C) (P := P) (Q := Q) (U := U); lra. }
  destruct (Rle_dec (cross Q U B) 0) as [HquB|HquB].
  - left. do 4 right. left. repeat split.
    + apply Rlt_le.
      assert (E := qu_B_minus_A A B C Q U).
      apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      replace (cross Q U A * cross A B C) with
        (cross Q U B * cross A B C
         - cross A B C * (cross A B Q - cross A B U)) by lra.
      assert (0 < cross A B C * (cross A B Q - cross A B U)).
      { apply Rmult_lt_0_compat; lra. }
      assert (Hble : cross Q U B * cross A B C <= 0 * cross A B C).
      { apply Rmult_le_compat_r; lra. }
      replace (0 * cross A B C) with 0 in Hble by ring. lra.
    + apply Rmult_le_reg_r with (r := cross A B C); [exact Hd |].
      replace (0 * cross A B C) with 0 by ring.
      assert (Hble : cross Q U B * cross A B C <= 0 * cross A B C).
      { apply Rmult_le_compat_r; lra. }
      replace (0 * cross A B C) with 0 in Hble by ring. exact Hble.
    + apply Rlt_le.
      assert (E := qu_C_minus_B A B C Q U).
      apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      replace (cross Q U C * cross A B C) with
        (cross Q U B * cross A B C
         + cross A B C * (cross B C Q - cross B C U)) by lra.
      assert (Hneg : cross B C Q - cross B C U < 0) by lra.
      assert (Hmul : cross A B C * (cross B C Q - cross B C U) < cross A B C * 0).
      { apply Rmult_lt_compat_l; [exact Hd | exact Hneg]. }
      replace (cross A B C * 0) with 0 in Hmul by ring.
      assert (Hble : cross Q U B * cross A B C <= 0 * cross A B C).
      { apply Rmult_le_compat_r; lra. }
      replace (0 * cross A B C) with 0 in Hble by ring. lra.
  - apply Rnot_le_lt in HquB.
    assert (HupB : 0 < cross U P B).
    { assert (E := up_b_from_qu A B C P Q U).
      assert (Hrhs : 0 < - cross A B P * cross Q U B * cross A B C
                       + - cross A B U
                         * (cross A B P * cross B C Q - cross A B Q * cross B C P)).
      { apply Rplus_lt_le_0_compat.
        - apply Rmult_lt_0_compat.
          + apply Rmult_lt_0_compat; lra.
          + exact Hd.
        - apply Rmult_le_pos; lra. }
      assert (Hprod : 0 < cross U P B * cross A B Q * cross A B C) by lra.
      apply Rmult_lt_reg_r with (r := cross A B Q * cross A B C).
      - apply Rmult_lt_0_compat; assumption.
      - replace (0 * (cross A B Q * cross A B C)) with 0 by ring.
        replace (cross U P B * (cross A B Q * cross A B C))
          with (cross U P B * cross A B Q * cross A B C) by ring.
        exact Hprod. }
    destruct (Rle_lt_or_eq_dec 0
                (cross A B P * cross B C Q - cross A B Q * cross B C P) Hna)
      as [HnaP|Hna0].
    + right.
      assert (Hopen : tri_open P Q U B).
      { repeat split; try assumption.
        apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
        rewrite cross_pq_B_na. replace (0 * cross A B C) with 0 by ring.
        exact HnaP. }
      destruct (meet_vertex P Q U A B C B Hs Hd
                  (or_intror (or_introl eq_refl)) Hopen) as [X [HXu HXa]].
      exists X. split; assumption.
    + right. apply touch_line_open; try assumption.
      * assert (E0 : cross P Q B * cross A B C = 0).
        { rewrite cross_pq_B_na. rewrite <- Hna0. ring. }
        apply Rmult_eq_reg_l with (r := cross A B C).
        -- replace (cross A B C * cross P Q B)
             with (cross P Q B * cross A B C) by ring.
           replace (cross A B C * 0) with 0 by ring. exact E0.
        -- apply not_eq_sym. apply Rlt_not_eq. exact Hd.
      * assert (EA := sep_nb_A A B C P Q).
        assert (Nb_neg : cross A B P * cross C A Q - cross A B Q * cross C A P < 0).
        { assert (Es := na_nb_sum A B C P Q).
          assert (Hlt : cross A B P - cross A B Q < 0) by lra.
          assert (Hprod : cross A B C * (cross A B P - cross A B Q)
                          < cross A B C * 0).
          { apply Rmult_lt_compat_l; [exact Hd | exact Hlt]. }
          replace (cross A B C * 0) with 0 in Hprod by ring.
          rewrite <- Hna0 in Es. lra. }
        apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
        rewrite EA. replace (0 * cross A B C) with 0 by ring. lra.
      * apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
        rewrite pqc_na. rewrite <- Hna0.
        replace (0 * cross A B C) with 0 by ring.
        assert (Hgap : 0 < cross B C P - cross B C Q) by lra.
        assert (Hmul : 0 < cross A B C * (cross B C P - cross B C Q)).
        {         apply Rmult_lt_0_compat; [exact Hd | exact Hgap]. }
        lra.
Qed.

Lemma gap_cp_cross : forall A B C P U,
  (cross B C U * cross C A P - cross C A U * cross B C P) * cross A B P
  = (cross A B P * cross B C U - cross A B U * cross B C P)
      * (cross A B C - cross A B P)
    + cross B C P * cross A B C * (cross A B U - cross A B P).
Proof. intros. unfold cross. destruct A, B, C, P, U. simpl. ring. Qed.

Lemma cross_up_A : forall A B C P U,
  cross U P A * cross A B C =
    cross A B P * cross C A U - cross A B U * cross C A P.
Proof. intros. unfold cross. destruct A, B, C, P, U. simpl. ring. Qed.

Lemma cross_up_B : forall A B C P U,
  cross U P B * cross A B C =
    - (cross A B P * cross B C U - cross A B U * cross B C P).
Proof. intros. unfold cross. destruct A, B, C, P, U. simpl. ring. Qed.

Lemma cross_up_C : forall A B C P U,
  cross U P C * cross A B C =
    cross B C U * cross C A P - cross C A U * cross B C P.
Proof. intros. unfold cross. destruct A, B, C, P, U. simpl. ring. Qed.

Lemma quA_nb : forall A B C P Q U,
  cross Q U A * cross A B P * cross A B C =
      cross A B U * (cross A B P * cross C A Q - cross A B Q * cross C A P)
    - cross A B Q * (cross A B P * cross C A U - cross A B U * cross C A P).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma prod_neg : forall a b, a < 0 -> 0 < b -> a * b < 0.
Proof.
  intros a b Ha Hb.
  assert (E : a * b < 0 * b) by (apply Rmult_lt_compat_r; assumption).
  replace (0 * b) with 0 in E by ring. exact E.
Qed.

Lemma prod_pos_neg : forall a b, 0 < a -> b < 0 -> a * b < 0.
Proof.
  intros a b Ha Hb.
  assert (E : a * b < a * 0) by (apply Rmult_lt_compat_l; assumption).
  replace (a * 0) with 0 in E by ring. exact E.
Qed.

Lemma wedge_c_succ : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  cross A B P * cross B C Q - cross A B Q * cross B C P < 0 ->
  cross A B P * cross C A Q - cross A B Q * cross C A P < 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hna Hnb.
  apply wedge_edges; try assumption.
  - apply prod_neg; assumption.
  - assert (HA : 0 < cross P Q A).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      rewrite sep_nb_A. replace (0 * cross A B C) with 0 by ring. lra. }
    assert (HB : cross P Q B < 0).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      rewrite cross_pq_B_na. replace (0 * cross A B C) with 0 by ring.
      exact Hna. }
    apply prod_pos_neg; assumption.
Qed.

Lemma up_outer_na : forall A B C P U,
  0 < cross A B C ->
  cross A B P < 0 ->
  cross A B P < cross A B U ->
  0 < cross B C P ->
  0 <= cross A B P * cross B C U - cross A B U * cross B C P ->
  outer3 U P A B C.
Proof.
  intros A B C P U Hd Hp Hlt HaP Hna.
  set (Na := cross A B P * cross B C U - cross A B U * cross B C P) in *.
  set (Gap := cross B C U * cross C A P - cross C A U * cross B C P).
  assert (Hgap : Gap < 0).
  { assert (E := gap_cp_cross A B C P U).
    unfold Na, Gap in E.
    assert (H2 : 0 < cross B C P * cross A B C * (cross A B U - cross A B P)).
    { apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; assumption | lra]. }
    assert (H1a : 0 <= cross A B P * cross B C U - cross A B U * cross B C P)
      by exact Hna.
    assert (H1b : 0 <= cross A B C - cross A B P) by lra.
    assert (H1 : 0 <= (cross A B P * cross B C U - cross A B U * cross B C P)
                   * (cross A B C - cross A B P))
      by (apply Rmult_le_pos; assumption).
    assert (Hprod : 0 < Gap * cross A B P).
    { unfold Gap. rewrite E.
      apply Rplus_le_lt_0_compat; [exact H1 | exact H2]. }
    destruct (Rle_dec 0 Gap) as [Hg|Hg].
    - assert (Hle : cross A B P * Gap <= cross A B P * 0).
      { apply Rmult_le_compat_neg_l; lra. }
      replace (cross A B P * 0) with 0 in Hle by ring.
      assert (Gap * cross A B P = cross A B P * Gap) by ring. lra.
    - apply Rnot_le_lt. exact Hg. }
  assert (Hnb : cross A B P * cross C A U - cross A B U * cross C A P < 0).
  { assert (Es := na_nb_sum A B C P U).
    assert (Hlt' : cross A B P - cross A B U < 0) by lra.
    assert (Hmul : cross A B C * (cross A B P - cross A B U) < 0).
    { assert (E1 : cross A B C * (cross A B P - cross A B U)
                   < cross A B C * 0).
      { apply Rmult_lt_compat_l; [exact Hd | exact Hlt']. }
      replace (cross A B C * 0) with 0 in E1 by ring. exact E1. }
    apply Rplus_lt_reg_l with
      (r := cross A B P * cross B C U - cross A B U * cross B C P).
    replace ((cross A B P * cross B C U - cross A B U * cross B C P) + 0)
      with (cross A B P * cross B C U - cross A B U * cross B C P) by ring.
    rewrite Es.
    apply Rlt_le_trans with (r2 := 0); [exact Hmul | exact Hna]. }
  repeat split.
  - apply Rlt_le.
    apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_A. replace (0 * cross A B C) with 0 by ring. exact Hnb.
  - apply Rmult_le_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_B. replace (0 * cross A B C) with 0 by ring.
    assert (Hle : - Na <= - 0) by (apply Ropp_le_contravar; exact Hna).
    replace (- 0) with 0 in Hle by ring. unfold Na in Hle. exact Hle.
  - apply Rlt_le.
    apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_C. replace (0 * cross A B C) with 0 by ring.
    unfold Gap in Hgap. exact Hgap.
Qed.

Lemma nb_of_sum : forall A B C P Q,
  cross A B P < cross A B Q ->
  0 < cross A B C ->
  0 <= cross A B P * cross B C Q - cross A B Q * cross B C P ->
  cross A B P * cross C A Q - cross A B Q * cross C A P < 0.
Proof.
  intros A B C P Q Hlt Hd Hna.
  assert (Es := na_nb_sum A B C P Q).
  assert (Hmul : cross A B C * (cross A B P - cross A B Q) < 0).
  { assert (Hdiff : cross A B P - cross A B Q < 0) by lra.
    assert (E1 : cross A B C * (cross A B P - cross A B Q)
                 < cross A B C * 0).
    { apply Rmult_lt_compat_l; assumption. }
    replace (cross A B C * 0) with 0 in E1 by ring. exact E1. }
  apply Rplus_lt_reg_l with
    (r := cross A B P * cross B C Q - cross A B Q * cross B C P).
  replace ((cross A B P * cross B C Q - cross A B Q * cross B C P) + 0)
    with (cross A B P * cross B C Q - cross A B Q * cross B C P) by ring.
  rewrite Es.
  apply Rlt_le_trans with (r2 := 0); [exact Hmul | exact Hna].
Qed.

Lemma openA_nbU : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  0 < cross A B U ->
  0 < cross B C P ->
  0 <= cross A B P * cross B C Q - cross A B Q * cross B C P ->
  0 < cross A B P * cross C A U - cross A B U * cross C A P ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu HaP HnaQ HnbU.
  assert (HnbQ : cross A B P * cross C A Q - cross A B Q * cross C A P < 0).
  { apply nb_of_sum; try assumption; lra. }
  assert (HpqA : 0 < cross P Q A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite sep_nb_A. replace (0 * cross A B C) with 0 by ring. lra. }
  assert (HupA : 0 < cross U P A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_A. replace (0 * cross A B C) with 0 by ring. exact HnbU. }
  assert (HquA : 0 < cross Q U A).
  { assert (E := quA_nb A B C P Q U).
    assert (Hleft : cross A B U
                      * (cross A B P * cross C A Q - cross A B Q * cross C A P) < 0).
    { apply prod_pos_neg; assumption. }
    assert (Hnonneg : 0 <= cross A B Q
                        * (cross A B P * cross C A U - cross A B U * cross C A P)).
    { apply Rmult_le_pos; [apply Rlt_le; exact Hq | apply Rlt_le; exact HnbU]. }
    assert (Hneg : - (cross A B Q
                        * (cross A B P * cross C A U - cross A B U * cross C A P)) <= 0).
    { apply Ropp_le_contravar in Hnonneg.
      replace (- 0) with 0 in Hnonneg by ring. exact Hnonneg. }
    assert (Hrhs0 : cross A B U
                      * (cross A B P * cross C A Q - cross A B Q * cross C A P)
                    + - (cross A B Q
                          * (cross A B P * cross C A U
                             - cross A B U * cross C A P)) < 0 + 0).
    { apply Rplus_lt_le_compat; [exact Hleft | exact Hneg]. }
    assert (Hrhs : cross A B U
                     * (cross A B P * cross C A Q - cross A B Q * cross C A P)
                   - cross A B Q
                     * (cross A B P * cross C A U - cross A B U * cross C A P) < 0).
    { replace 0 with (0 + 0) by ring.
      replace (cross A B U
                 * (cross A B P * cross C A Q - cross A B Q * cross C A P)
               - cross A B Q
                 * (cross A B P * cross C A U - cross A B U * cross C A P))
        with (cross A B U
                * (cross A B P * cross C A Q - cross A B Q * cross C A P)
              + - (cross A B Q
                     * (cross A B P * cross C A U - cross A B U * cross C A P)))
        by ring.
      exact Hrhs0. }
    assert (Hprod : cross Q U A * cross A B P * cross A B C < 0).
    { rewrite E. exact Hrhs. }
    assert (Hden : cross A B P * cross A B C < 0) by (apply prod_neg; assumption).
    destruct (Rle_dec (cross Q U A) 0) as [Hqle|Hqlt].
    - assert (Hge : cross A B P * cross A B C * 0 <=
                    cross A B P * cross A B C * cross Q U A).
      { apply Rmult_le_compat_neg_l; [apply Rlt_le; exact Hden | exact Hqle]. }
      replace (cross A B P * cross A B C * 0) with 0 in Hge by ring.
      assert (Heq : cross Q U A * cross A B P * cross A B C =
                    cross A B P * cross A B C * cross Q U A) by ring.
      rewrite Heq in Hprod.
      exfalso. apply (Rlt_not_le _ _ Hprod). exact Hge.
    - apply Rnot_le_lt. exact Hqlt. }
  destruct (meet_vertex P Q U A B C A Hs Hd
              (or_introl eq_refl)
              (conj HpqA (conj HquA HupA))) as [X [HXu HXa]].
  exists X. split; assumption.
Qed.

Lemma wedge_c_pred : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B U ->
  cross A B P * cross B C U - cross A B U * cross B C P < 0 ->
  cross A B P * cross C A U - cross A B U * cross C A P < 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hu Hna Hnb.
  assert (Hmeet : exists X, tri_open A B C X /\ tri_open U P Q X).
  { apply wedge_edges; try assumption.
    - rewrite cross_cycle. exact Hs.
    - apply prod_pos_neg; [exact Hu | exact Hp].
    - assert (HA : cross U P A < 0).
      { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
        rewrite cross_up_A. replace (0 * cross A B C) with 0 by ring.
        exact Hnb. }
      assert (HB : 0 < cross U P B).
      { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
        rewrite cross_up_B. replace (0 * cross A B C) with 0 by ring.
        assert (Hopp : - 0 <
            - (cross A B P * cross B C U - cross A B U * cross B C P)).
        { apply Ropp_lt_contravar. exact Hna. }
        replace (- 0) with 0 in Hopp by ring. exact Hopp. }
      apply prod_neg; assumption. }
  destruct Hmeet as [X [HXa HXu]].
  destruct HXu as [Hup [Hpq Hqu]].
  exists X. split; [exact HXa | repeat split; assumption].
Qed.

Lemma some_outer_ab : forall A B C P Q U,
  outer3 A B P Q U -> some_outer A B C P Q U.
Proof. intros. left. assumption. Qed.

Lemma some_outer_pq : forall A B C P Q U,
  outer3 P Q A B C -> some_outer A B C P Q U.
Proof. intros. do 3 right. left. assumption. Qed.

Lemma some_outer_qu : forall A B C P Q U,
  outer3 Q U A B C -> some_outer A B C P Q U.
Proof. intros. do 4 right. left. assumption. Qed.

Lemma some_outer_up : forall A B C P Q U,
  outer3 U P A B C -> some_outer A B C P Q U.
Proof. intros. do 5 right. assumption. Qed.

Lemma qua_bb : forall A B C Q U,
  cross Q U A * cross A B C =
    cross C A Q * cross A B U - cross A B Q * cross C A U.
Proof. intros. unfold cross. destruct A, B, C, Q, U. simpl. ring. Qed.

Lemma qu_b_gap : forall A B C Q U,
  (cross Q U B - cross Q U A) * cross A B C =
    cross A B C * (cross A B Q - cross A B U).
Proof. intros. unfold cross. destruct A, B, C, Q, U. simpl. ring. Qed.

Lemma qu_c_gap : forall A B C Q U,
  (cross Q U C - cross Q U A) * cross A B C =
    cross A B C * (cross C A U - cross C A Q).
Proof. intros. unfold cross. destruct A, B, C, Q, U. simpl. ring. Qed.

Lemma s_qua_id : forall A B C P Q U,
  cross P Q U * cross A B C =
    cross Q U A * cross A B C
    - cross A B P * (cross C A Q - cross C A U)
    + cross C A P * (cross A B Q - cross A B U).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma b_gap_from_s : forall A B C P Q U,
  - cross A B P * (cross C A Q - cross C A U) =
    cross P Q U * cross A B C
    - cross Q U A * cross A B C
    + cross C A P * (cross A B U - cross A B Q).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma pqa_cu_id : forall A B C P Q U,
  (cross C A P * cross A B Q - cross A B P * cross C A Q) * cross A B U =
    - cross A B P
        * (cross C A Q * cross A B U - cross A B Q * cross C A U)
    - cross A B Q
        * (cross A B P * cross C A U - cross A B U * cross C A P).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma bU_of_nb : forall A B C P U,
  cross A B P < 0 ->
  0 < cross A B U ->
  0 < cross C A P ->
  0 <= cross A B P * cross C A U - cross A B U * cross C A P ->
  cross C A U < 0.
Proof.
  intros A B C P U Hp Hu Hb Hnb.
  destruct (Rle_dec 0 (cross C A U)) as [Hge|Hlt].
  - assert (Hle : cross A B P * cross C A U <= cross A B P * 0).
    { apply Rmult_le_compat_neg_l; lra. }
    replace (cross A B P * 0) with 0 in Hle by ring.
    assert (Hpos : 0 < cross A B U * cross C A P).
    { apply Rmult_lt_0_compat; assumption. }
    assert (Hdiff : cross A B P * cross C A U < cross A B U * cross C A P).
    { apply Rle_lt_trans with (r2 := 0); assumption. }
    assert (Hsum : cross A B P * cross C A U
                   + - (cross A B U * cross C A P)
                   < cross A B U * cross C A P
                   + - (cross A B U * cross C A P)).
    { apply Rplus_lt_compat_r. exact Hdiff. }
    replace (cross A B U * cross C A P + - (cross A B U * cross C A P))
      with 0 in Hsum by ring.
    replace (cross A B P * cross C A U + - (cross A B U * cross C A P))
      with (cross A B P * cross C A U - cross A B U * cross C A P)
      in Hsum by ring.
    exfalso. apply (Rlt_not_le _ _ Hsum). exact Hnb.
  - apply Rnot_le_lt. exact Hlt.
Qed.

(* Vertex A of ABC lies on line UP, strictly left of PQ and QU, and B is
   strictly left of UP. A short step toward B, with a smaller step toward C,
   lands in both open triangles. *)
Lemma touch_up_A : forall A B C P Q U,
  0 < cross A B C ->
  cross U P A = 0 ->
  0 < cross P Q A ->
  0 < cross Q U A ->
  0 < cross U P B ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd HupA HpqA HquA HupB.
  set (alpha := Rmin (step_room (cross U P B) (cross U P C)) (1 / 2)).
  assert (Halpha : 0 < alpha).
  { unfold alpha. apply Rmin_pos; [| lra].
    apply step_room_pos. exact HupB. }
  assert (HalphaR : alpha <= step_room (cross U P B) (cross U P C)).
  { unfold alpha. apply Rmin_l. }
  assert (HupMix : 0 < cross U P B + alpha * cross U P C).
  { apply slack_step_pos; assumption. }
  set (dsPQ := cross P Q B + alpha * cross P Q C
               - (1 + alpha) * cross P Q A).
  set (dsQU := cross Q U B + alpha * cross Q U C
               - (1 + alpha) * cross Q U A).
  assert (Hden : 0 < 1 + alpha) by lra.
  assert (Hdenz : 1 + alpha <> 0).
  { apply not_eq_sym. apply Rlt_not_eq. exact Hden. }
  set (cap := 1 / (2 * (1 + alpha))).
  assert (Hcap : 0 < cap).
  { unfold cap. apply Rdiv_lt_0_compat; [lra |].
    apply Rmult_lt_0_compat; lra. }
  set (t := Rmin (Rmin (step_room (cross P Q A) dsPQ)
                       (step_room (cross Q U A) dsQU)) cap).
  assert (Ht : 0 < t).
  { unfold t. apply Rmin_pos; [| exact Hcap].
    apply Rmin_pos; apply step_room_pos; assumption. }
  assert (HtPQ : t <= step_room (cross P Q A) dsPQ).
  { unfold t. apply Rle_trans with
      (r2 := Rmin (step_room (cross P Q A) dsPQ)
                  (step_room (cross Q U A) dsQU)).
    - apply Rmin_l.
    - apply Rmin_l. }
  assert (HtQU : t <= step_room (cross Q U A) dsQU).
  { unfold t. apply Rle_trans with
      (r2 := Rmin (step_room (cross P Q A) dsPQ)
                  (step_room (cross Q U A) dsQU)).
    - apply Rmin_l.
    - apply Rmin_r. }
  assert (Htcap : t <= cap) by (unfold t; apply Rmin_r).
  assert (Hhalf : t * (1 + alpha) <= 1 / 2).
  { apply Rle_trans with (r2 := cap * (1 + alpha)).
    - apply Rmult_le_compat_r; [apply Rlt_le; exact Hden | exact Htcap].
    - unfold cap. field_simplify; lra. }
  set (s := alpha * t).
  assert (Hs0 : 0 < s) by (unfold s; apply Rmult_lt_0_compat; assumption).
  assert (Hrest : 0 < 1 - t - s).
  { unfold s. assert (t * (1 + alpha) <= 1 / 2) by exact Hhalf. lra. }
  set (X := bary3 (1 - t - s) t s A B C).
  assert (Hw : (1 - t - s) + t + s = 1) by ring.
  exists X. split.
  - repeat split.
    + unfold X. rewrite (cross_bary3 A B A B C (1 - t - s) t s Hw).
      replace (cross A B A) with 0 by (symmetry; apply cross_third_eq_first).
      replace (cross A B B) with 0 by (symmetry; apply cross_third_eq_second).
      replace ((1 - t - s) * 0 + t * 0 + s * cross A B C)
        with (s * cross A B C) by ring.
      apply Rmult_lt_0_compat; assumption.
    + unfold X. rewrite (cross_bary3 B C A B C (1 - t - s) t s Hw).
      replace (cross B C A) with (cross A B C) by apply cross_cycle.
      replace (cross B C B) with 0 by (symmetry; apply cross_third_eq_first).
      replace (cross B C C) with 0 by (symmetry; apply cross_third_eq_second).
      replace ((1 - t - s) * cross A B C + t * 0 + s * 0)
        with ((1 - t - s) * cross A B C) by ring.
      apply Rmult_lt_0_compat; assumption.
    + unfold X. rewrite (cross_bary3 C A A B C (1 - t - s) t s Hw).
      replace (cross C A A) with 0 by (symmetry; apply cross_third_eq_second).
      replace (cross C A B) with (cross A B C) by apply cross_cycle2.
      replace (cross C A C) with 0 by (symmetry; apply cross_third_eq_first).
      replace ((1 - t - s) * 0 + t * cross A B C + s * 0)
        with (t * cross A B C) by ring.
      apply Rmult_lt_0_compat; assumption.
  - repeat split.
    + unfold X. rewrite (cross_bary3 P Q A B C (1 - t - s) t s Hw).
      replace ((1 - t - s) * cross P Q A + t * cross P Q B + s * cross P Q C)
        with (cross P Q A + t * dsPQ) by (unfold s, dsPQ; ring).
      apply slack_step_pos; assumption.
    + unfold X. rewrite (cross_bary3 Q U A B C (1 - t - s) t s Hw).
      replace ((1 - t - s) * cross Q U A + t * cross Q U B + s * cross Q U C)
        with (cross Q U A + t * dsQU) by (unfold s, dsQU; ring).
      apply slack_step_pos; assumption.
    + unfold X. rewrite (cross_bary3 U P A B C (1 - t - s) t s Hw).
      rewrite HupA.
      replace ((1 - t - s) * 0 + t * cross U P B + s * cross U P C)
        with (t * (cross U P B + alpha * cross U P C)) by (unfold s; ring).
      apply Rmult_lt_0_compat; assumption.
Qed.

Lemma pqa_prod_cu : forall A B C P Q U,
  (cross P Q A * cross A B C) * cross A B U =
    (- cross A B P) * (cross Q U A * cross A B C)
    + (- cross A B Q)
        * (cross A B P * cross C A U - cross A B U * cross C A P).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma qu_outer_qua : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  cross A B Q <= 0 ->
  0 < cross A B U ->
  0 < cross C A P ->
  cross Q U A <= 0 ->
  outer3 Q U A B C.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu HbP Hqa.
  assert (HquB : cross Q U B < 0).
  { assert (Hlt : (cross Q U B - cross Q U A) * cross A B C
                  < 0 * cross A B C).
    { rewrite qu_b_gap. replace (0 * cross A B C) with 0 by ring.
      apply prod_pos_neg; [exact Hd | lra]. }
    apply Rmult_lt_reg_r in Hlt; [| exact Hd]. lra. }
  assert (Hbg : 0 < cross C A Q - cross C A U).
  { assert (HcP : 0 < - cross A B P) by lra.
    assert (Hpos : 0 < - cross A B P * (cross C A Q - cross C A U)).
    { rewrite b_gap_from_s.
      assert (H1 : 0 < cross P Q U * cross A B C).
      { apply Rmult_lt_0_compat; assumption. }
      assert (Hnqa : 0 <= - cross Q U A).
      { assert (Hopp : - 0 <= - cross Q U A).
        { apply Ropp_le_contravar. exact Hqa. }
        replace (- 0) with 0 in Hopp by ring. exact Hopp. }
      assert (H2 : 0 <= - cross Q U A * cross A B C).
      { apply Rmult_le_pos; [exact Hnqa | apply Rlt_le; exact Hd]. }
      assert (H3 : 0 < cross C A P * (cross A B U - cross A B Q)).
      { apply Rmult_lt_0_compat; [exact HbP | lra]. }
      assert (H13 : 0 < cross P Q U * cross A B C
                      + cross C A P * (cross A B U - cross A B Q)).
      { apply Rplus_lt_0_compat; assumption. }
      assert (Hsum : 0 < cross P Q U * cross A B C
                        + cross C A P * (cross A B U - cross A B Q)
                        + - cross Q U A * cross A B C).
      { apply Rplus_lt_le_0_compat; [exact H13 | exact H2]. }
      replace (cross P Q U * cross A B C
               - cross Q U A * cross A B C
               + cross C A P * (cross A B U - cross A B Q))
        with (cross P Q U * cross A B C
              + cross C A P * (cross A B U - cross A B Q)
              + - cross Q U A * cross A B C) by ring.
      exact Hsum. }
    apply Rmult_lt_reg_l with (r := - cross A B P); [exact HcP |].
    replace ((- cross A B P) * 0) with 0 by ring.
    exact Hpos. }
  assert (HquC : cross Q U C < 0).
  { assert (Hlt : (cross Q U C - cross Q U A) * cross A B C
                  < 0 * cross A B C).
    { rewrite qu_c_gap. replace (0 * cross A B C) with 0 by ring.
      apply prod_pos_neg; [exact Hd | lra]. }
    apply Rmult_lt_reg_r in Hlt; [| exact Hd]. lra. }
  repeat split; [exact Hqa | apply Rlt_le; exact HquB | apply Rlt_le; exact HquC].
Qed.

Lemma pqa_of_qua : forall A B C P Q U,
  0 < cross A B C ->
  cross A B P < 0 ->
  cross A B Q <= 0 ->
  0 < cross A B U ->
  0 < cross Q U A ->
  0 <= cross A B P * cross C A U - cross A B U * cross C A P ->
  0 < cross P Q A.
Proof.
  intros A B C P Q U Hd Hp Hq Hu Hqa Hnb.
  assert (E := pqa_prod_cu A B C P Q U).
  assert (H1 : 0 < (- cross A B P) * (cross Q U A * cross A B C)).
  { apply Rmult_lt_0_compat; [lra | apply Rmult_lt_0_compat; assumption]. }
  assert (Hnq : 0 <= - cross A B Q).
  { assert (Hopp : - 0 <= - cross A B Q).
    { apply Ropp_le_contravar. exact Hq. }
    replace (- 0) with 0 in Hopp by ring. exact Hopp. }
  assert (H2 : 0 <= (- cross A B Q)
                 * (cross A B P * cross C A U - cross A B U * cross C A P)).
  { apply Rmult_le_pos; assumption. }
  assert (Hsum : 0 < (- cross A B P) * (cross Q U A * cross A B C)
                    + (- cross A B Q)
                      * (cross A B P * cross C A U
                         - cross A B U * cross C A P)).
  { apply Rplus_lt_le_0_compat; assumption. }
  assert (Hprod : 0 < (cross P Q A * cross A B C) * cross A B U).
  { rewrite E. exact Hsum. }
  apply Rmult_lt_reg_r with (r := cross A B U); [exact Hu |].
  replace (0 * cross A B U) with 0 by ring.
  apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
  replace (0 * cross A B C) with 0 by ring.
  replace ((cross P Q A * cross A B U) * cross A B C)
    with ((cross P Q A * cross A B C) * cross A B U) by ring.
  exact Hprod.
Qed.

Lemma succ_line_A : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  0 < cross A B U ->
  0 < cross B C P ->
  0 <= cross A B P * cross B C Q - cross A B Q * cross B C P ->
  cross A B P * cross B C U - cross A B U * cross B C P < 0 ->
  cross A B P * cross C A U - cross A B U * cross C A P = 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu HaP Hna HnaU Hnb0.
  assert (HnbQ : cross A B P * cross C A Q - cross A B Q * cross C A P < 0).
  { apply nb_of_sum; try assumption; lra. }
  assert (HpqA : 0 < cross P Q A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite sep_nb_A. replace (0 * cross A B C) with 0 by ring. lra. }
  assert (HquA : 0 < cross Q U A).
  { assert (E := quA_nb A B C P Q U).
    rewrite Hnb0 in E.
    assert (Hrhs : cross A B U
                     * (cross A B P * cross C A Q - cross A B Q * cross C A P)
                   < 0).
    { apply prod_pos_neg; assumption. }
    assert (E0 : cross Q U A * cross A B P * cross A B C < 0).
    { rewrite E.
      replace (cross A B U
                 * (cross A B P * cross C A Q - cross A B Q * cross C A P)
               - cross A B Q * 0)
        with (cross A B U
                * (cross A B P * cross C A Q - cross A B Q * cross C A P))
        by ring.
      exact Hrhs. }
    assert (Hden : cross A B P * cross A B C < 0) by (apply prod_neg; assumption).
    destruct (Rle_dec (cross Q U A) 0) as [Hqle|Hqlt].
    - assert (Hge : cross A B P * cross A B C * 0 <=
                    cross A B P * cross A B C * cross Q U A).
      { apply Rmult_le_compat_neg_l; [apply Rlt_le; exact Hden | exact Hqle]. }
      replace (cross A B P * cross A B C * 0) with 0 in Hge by ring.
      assert (Heqa : cross Q U A * cross A B P * cross A B C =
                     cross A B P * cross A B C * cross Q U A) by ring.
      rewrite Heqa in E0.
      exfalso. apply (Rlt_not_le _ _ E0). exact Hge.
    - apply Rnot_le_lt. exact Hqlt. }
  assert (HupA : cross U P A = 0).
  { assert (E0 : cross U P A * cross A B C = 0).
    { rewrite cross_up_A. exact Hnb0. }
    apply Rmult_eq_reg_l with (r := cross A B C).
    - replace (cross A B C * cross U P A)
        with (cross U P A * cross A B C) by ring.
      replace (cross A B C * 0) with 0 by ring. exact E0.
    - apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
  assert (HupB : 0 < cross U P B).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_B. replace (0 * cross A B C) with 0 by ring.
    assert (Hopp : - 0 <
        - (cross A B P * cross B C U - cross A B U * cross B C P)).
    { apply Ropp_lt_contravar. exact HnaU. }
    replace (- 0) with 0 in Hopp by ring. exact Hopp. }
  apply touch_up_A; assumption.
Qed.

Lemma cap_succ : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  0 < cross B C P ->
  0 < cross C A P ->
  some_outer A B C P Q U \/ exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq HaP HbP.
  destruct (Rle_dec 0 (cross A B P * cross B C Q - cross A B Q * cross B C P))
    as [Hna|Hna].
  - destruct (Rle_dec (cross A B U) 0) as [Hu|Hu].
    + apply na_cap_closed_u; assumption.
    + apply Rnot_le_lt in Hu.
      destruct (Rle_dec 0
                  (cross A B P * cross B C U - cross A B U * cross B C P))
        as [HnaU|HnaU].
      * left. apply some_outer_up.
        apply up_outer_na; try assumption; lra.
      * apply Rnot_le_lt in HnaU.
        destruct (Rle_dec 0
                    (cross A B P * cross C A U - cross A B U * cross C A P))
          as [HnbU|HnbU].
        -- destruct (Rle_lt_or_eq_dec 0
                       (cross A B P * cross C A U
                        - cross A B U * cross C A P) HnbU) as [Hgt|Heq].
           ++ right. apply openA_nbU; try assumption; lra.
           ++ right. apply succ_line_A; try assumption.
              symmetry. exact Heq.
        -- apply Rnot_le_lt in HnbU.
           right. apply wedge_c_pred; assumption.
  - apply Rnot_le_lt in Hna.
    destruct (Rle_dec 0 (cross A B P * cross C A Q - cross A B Q * cross C A P))
      as [Hnb|Hnb].
    + left. apply some_outer_pq. apply nb_outer; assumption.
    + apply Rnot_le_lt in Hnb.
      right. apply wedge_c_succ; assumption.
Qed.

Lemma cap_pred : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  cross A B Q <= 0 ->
  0 < cross A B U ->
  0 < cross B C P ->
  0 < cross C A P ->
  some_outer A B C P Q U \/ exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu HaP HbP.
  destruct (Rle_dec 0 (cross A B P * cross B C U - cross A B U * cross B C P))
    as [HnaU|HnaU].
  - left. apply some_outer_up. apply up_outer_na; try assumption; lra.
  - apply Rnot_le_lt in HnaU.
    destruct (Rle_dec 0 (cross A B P * cross C A U - cross A B U * cross C A P))
      as [HnbU|HnbU].
    + destruct (Rle_dec (cross Q U A) 0) as [Hqa|Hqa].
      * left. apply some_outer_qu. apply (qu_outer_qua A B C P Q U); assumption.
      * apply Rnot_le_lt in Hqa.
        assert (HpqA : 0 < cross P Q A).
        { apply (pqa_of_qua A B C P Q U); assumption. }
        destruct (Rle_lt_or_eq_dec 0
                    (cross A B P * cross C A U - cross A B U * cross C A P)
                    HnbU) as [Hgt|Heq].
        -- right.
           assert (HupA : 0 < cross U P A).
           { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
             rewrite cross_up_A. replace (0 * cross A B C) with 0 by ring.
             exact Hgt. }
           destruct (meet_vertex P Q U A B C A Hs Hd
                      (or_introl eq_refl)
                      (conj HpqA (conj Hqa HupA))) as [X [HXu HXa]].
           exists X. split; assumption.
        -- right.
           assert (HupA0 : cross U P A = 0).
           { assert (E0 : cross U P A * cross A B C = 0).
             { rewrite cross_up_A. symmetry. exact Heq. }
             apply Rmult_eq_reg_l with (r := cross A B C).
             - replace (cross A B C * cross U P A)
                 with (cross U P A * cross A B C) by ring.
               replace (cross A B C * 0) with 0 by ring. exact E0.
             - apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
           assert (HupB : 0 < cross U P B).
           { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
             rewrite cross_up_B. replace (0 * cross A B C) with 0 by ring.
             assert (Hopp : - 0 <
                 - (cross A B P * cross B C U - cross A B U * cross B C P)).
             { apply Ropp_lt_contravar. exact HnaU. }
             replace (- 0) with 0 in Hopp by ring. exact Hopp. }
           apply touch_up_A; assumption.
    + apply Rnot_le_lt in HnbU.
      right. apply wedge_c_pred; assumption.
Qed.

Lemma cap_ab : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross B C P ->
  0 < cross C A P ->
  some_outer A B C P Q U \/ exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp HaP HbP.
  destruct (Rlt_dec 0 (cross A B Q)) as [Hq|Hq].
  - apply cap_succ; assumption.
  - apply Rnot_lt_le in Hq.
    destruct (Rlt_dec 0 (cross A B U)) as [Hu|Hu].
    + apply cap_pred; assumption.
    + apply Rnot_lt_le in Hu.
      left. apply some_outer_ab. repeat split.
      * apply Rlt_le. exact Hp.
      * exact Hq.
      * exact Hu.
Qed.

Lemma tri_open_rot : forall A B C X,
  tri_open A B C X -> tri_open B C A X.
Proof.
  intros A B C X [Hab [Hbc Hca]]. repeat split; assumption.
Qed.

Lemma tri_open_rot2 : forall A B C X,
  tri_open A B C X -> tri_open C A B X.
Proof.
  intros A B C X [Hab [Hbc Hca]]. repeat split; assumption.
Qed.

Lemma outer3_rot : forall p q a b c,
  outer3 p q a b c -> outer3 p q b c a.
Proof.
  intros p q a b c [H1 [H2 H3]]. repeat split; assumption.
Qed.

Lemma outer3_rot2 : forall p q a b c,
  outer3 p q a b c -> outer3 p q c a b.
Proof.
  intros p q a b c [H1 [H2 H3]]. repeat split; assumption.
Qed.

Lemma some_outer_swap : forall A B C P Q U,
  some_outer P Q U A B C -> some_outer A B C P Q U.
Proof.
  intros A B C P Q U [H|[H|[H|[H|[H|H]]]]].
  - do 3 right. left. exact H.
  - do 4 right. left. exact H.
  - do 5 right. exact H.
  - left. exact H.
  - right. left. exact H.
  - do 2 right. left. exact H.
Qed.

Lemma meet_swap : forall A B C P Q U,
  (exists X, tri_open P Q U X /\ tri_open A B C X) ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U [X [Hs Ht]]. exists X. split; assumption.
Qed.

Lemma meet_rot_T : forall A B C P Q U,
  (exists X, tri_open B C A X /\ tri_open P Q U X) ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U [X [Ht Hs]].
  exists X. split; [| exact Hs].
  destruct Ht as [Hbc [Hca Hab]]. repeat split; assumption.
Qed.

Lemma meet_rot_S : forall A B C P Q U,
  (exists X, tri_open A B C X /\ tri_open Q U P X) ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U [X [Ht Hs]].
  exists X. split; [exact Ht |].
  destruct Hs as [Hqu [Hup Hpq]]. repeat split; assumption.
Qed.

(* P sits in the exterior corner at A, Q at B, U at C. Vertex A of ABC
   is then strictly inside triangle PQU. *)
Lemma surround_open_A : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross B C P -> cross C A P < 0 -> cross A B P < 0 ->
  cross B C Q < 0 -> 0 < cross C A Q -> cross A B Q < 0 ->
  cross B C U < 0 -> cross C A U < 0 -> 0 < cross A B U ->
  tri_open P Q U A.
Proof.
  intros A B C P Q U Hd HaP HbP HcP HaQ HbQ HcQ HaU HbU HcU.
  repeat split.
  - apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite sep_nb_A. replace (0 * cross A B C) with 0 by ring.
    assert (H1 : 0 < (- cross A B P) * cross C A Q).
    { apply Rmult_lt_0_compat; lra. }
    assert (Hnq : 0 < - cross A B Q) by lra.
    assert (Hnp : 0 < - cross C A P) by lra.
    assert (H2 : 0 < (- cross A B Q) * (- cross C A P)).
    { apply Rmult_lt_0_compat; assumption. }
    replace ((- cross A B Q) * (- cross C A P))
      with (cross A B Q * cross C A P) in H2 by ring.
    assert (Hsum : 0 < (- cross A B P) * cross C A Q
                      + cross A B Q * cross C A P).
    { apply Rplus_lt_0_compat; assumption. }
    replace (- (cross A B P * cross C A Q - cross A B Q * cross C A P))
      with ((- cross A B P) * cross C A Q + cross A B Q * cross C A P)
      by ring.
    exact Hsum.
  - apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite qua_bb. replace (0 * cross A B C) with 0 by ring.
    assert (Eb := cross_sum3 A B C Q).
    assert (Eu := cross_sum3 A B C U).
    set (ap := - cross B C Q).
    set (cq := - cross A B Q).
    set (au := - cross B C U).
    set (bu := - cross C A U).
    assert (Hap : 0 < ap) by (unfold ap; lra).
    assert (Hcq : 0 < cq) by (unfold cq; lra).
    assert (Hau : 0 < au) by (unfold au; lra).
    assert (Hbu : 0 < bu) by (unfold bu; lra).
    assert (EbQ : cross C A Q = cross A B C + ap + cq).
    { unfold ap, cq.
      replace (cross A B C - cross B C Q - cross A B Q)
        with (cross A B C + - cross B C Q + - cross A B Q) by ring.
      assert (Esum : cross A B Q + cross B C Q + cross C A Q = cross A B C)
        by exact Eb.
      lra. }
    assert (EcU : cross A B U = cross A B C + au + bu).
    { unfold au, bu.
      assert (Esum : cross A B U + cross B C U + cross C A U = cross A B C)
        by exact Eu.
      lra. }
    rewrite EbQ, EcU.
    assert (Hdd : 0 < cross A B C * cross A B C).
    { apply Rmult_lt_0_compat; assumption. }
    assert (H1 : 0 < cross A B C * au) by (apply Rmult_lt_0_compat; assumption).
    assert (H2 : 0 < cross A B C * bu) by (apply Rmult_lt_0_compat; assumption).
    assert (H3 : 0 < cross A B C * ap) by (apply Rmult_lt_0_compat; assumption).
    assert (H4 : 0 < cross A B C * cq) by (apply Rmult_lt_0_compat; assumption).
    assert (H5 : 0 < ap * au) by (apply Rmult_lt_0_compat; assumption).
    assert (H6 : 0 < ap * bu) by (apply Rmult_lt_0_compat; assumption).
    assert (H7 : 0 < cq * au) by (apply Rmult_lt_0_compat; assumption).
    assert (S01 : 0 < cross A B C * cross A B C + cross A B C * au).
    { apply Rplus_lt_0_compat; assumption. }
    assert (S02 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu).
    { apply Rplus_lt_0_compat; [exact S01 | exact H2]. }
    assert (S03 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap).
    { apply Rplus_lt_0_compat; [exact S02 | exact H3]. }
    assert (S04 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq).
    { apply Rplus_lt_0_compat; [exact S03 | exact H4]. }
    assert (S05 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq + ap * au).
    { apply Rplus_lt_0_compat; [exact S04 | exact H5]. }
    assert (S06 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq + ap * au + ap * bu).
    { apply Rplus_lt_0_compat; [exact S05 | exact H6]. }
    assert (S07 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq + ap * au + ap * bu + cq * au).
    { apply Rplus_lt_0_compat; [exact S06 | exact H7]. }
    assert (HeqS : (cross A B C + ap + cq) * (cross A B C + au + bu)
                   - cross A B Q * cross C A U
                 = cross A B C * cross A B C
                   + cross A B C * au + cross A B C * bu
                   + cross A B C * ap + cross A B C * cq
                   + ap * au + ap * bu + cq * au).
    { unfold ap, cq, au, bu. ring. }
    rewrite <- HeqS in S07. exact S07.
  - apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_A. replace (0 * cross A B C) with 0 by ring.
    assert (H1 : 0 < cross A B P * cross C A U).
    { assert (Hn1 : 0 < - cross A B P) by lra.
      assert (Hn2 : 0 < - cross C A U) by lra.
      assert (Hp : 0 < (- cross A B P) * (- cross C A U)).
      { apply Rmult_lt_0_compat; assumption. }
      replace ((- cross A B P) * (- cross C A U))
        with (cross A B P * cross C A U) in Hp by ring.
      exact Hp. }
    assert (H2 : 0 < cross A B U * (- cross C A P)).
    { apply Rmult_lt_0_compat; [exact HcU | lra]. }
    assert (Hsum : 0 < cross A B P * cross C A U
                      + cross A B U * (- cross C A P)).
    { apply Rplus_lt_0_compat; assumption. }
    replace (cross A B P * cross C A U - cross A B U * cross C A P)
      with (cross A B P * cross C A U + cross A B U * (- cross C A P))
      by ring.
    exact Hsum.
Qed.

(* A strict spike has exactly one positive slack. skA sits in the
   exterior corner at A, and likewise for skB and skC. *)
Definition skA (A B C X : Point) : Prop :=
  0 < cross B C X /\ cross C A X < 0 /\ cross A B X < 0.
Definition skB (A B C X : Point) : Prop :=
  cross B C X < 0 /\ 0 < cross C A X /\ cross A B X < 0.
Definition skC (A B C X : Point) : Prop :=
  cross B C X < 0 /\ cross C A X < 0 /\ 0 < cross A B X.

Lemma skB_rot : forall A B C X, skB A B C X -> skA B C A X.
Proof. intros A B C X [Ha [Hb Hc]]. repeat split; assumption. Qed.

Lemma skC_rot : forall A B C X, skC A B C X -> skB B C A X.
Proof. intros A B C X [Ha [Hb Hc]]. repeat split; assumption. Qed.

Lemma skA_rot : forall A B C X, skA A B C X -> skC B C A X.
Proof. intros A B C X [Ha [Hb Hc]]. repeat split; assumption. Qed.

Lemma spikes_ccw : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skA A B C P -> skB A B C Q -> skC A B C U ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  destruct Hp as [HaP [HbP HcP]].
  destruct Hq as [HaQ [HbQ HcQ]].
  destruct Hu as [HaU [HbU HcU]].
  assert (Hopen : tri_open P Q U A).
  { apply (surround_open_A A B C P Q U); assumption. }
  destruct (meet_vertex P Q U A B C A Hs Hd (or_introl eq_refl) Hopen)
    as [X [HsX HtX]].
  exists X. split; assumption.
Qed.

Lemma spikes_ccw_rot : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skB A B C P -> skC A B C Q -> skA A B C U ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply meet_rot_T.
  apply spikes_ccw.
  - replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd.
  - exact Hs.
  - apply skB_rot. exact Hp.
  - apply skC_rot. exact Hq.
  - apply skA_rot. exact Hu.
Qed.

Lemma spikes_ccw_rot2 : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skC A B C P -> skA A B C Q -> skB A B C U ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply meet_rot_T.
  apply spikes_ccw_rot.
  - replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd.
  - exact Hs.
  - apply skC_rot. exact Hp.
  - apply skA_rot. exact Hq.
  - apply skB_rot. exact Hu.
Qed.

Lemma spikes_cw_false : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skA A B C P -> skC A B C Q -> skB A B C U -> False.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  destruct Hp as [HaP [HbP HcP]].
  destruct Hq as [HaQ [HbQ HcQ]].
  destruct Hu as [HaU [HbU HcU]].
  assert (Hopen : tri_open P U Q A).
  { apply (surround_open_A A B C P U Q); assumption. }
  destruct Hopen as [Hpu [Huq Hqp]].
  assert (Hpq : cross P Q A < 0).
  { assert (E := cross_swap_first_two Q P A). lra. }
  assert (Hqu : cross Q U A < 0).
  { assert (E := cross_swap_first_two U Q A). lra. }
  assert (Hup : cross U P A < 0).
  { assert (E := cross_swap_first_two P U A). lra. }
  assert (Esum := cross_sum3 P Q U A). lra.
Qed.

Lemma spikes_cw_rot_false : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skB A B C P -> skA A B C Q -> skC A B C U -> False.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply (spikes_cw_false B C A P Q U).
  - replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd.
  - exact Hs.
  - apply skB_rot. exact Hp.
  - apply skA_rot. exact Hq.
  - apply skC_rot. exact Hu.
Qed.

Lemma spikes_cw_rot2_false : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skC A B C P -> skB A B C Q -> skA A B C U -> False.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply (spikes_cw_false C A B P Q U).
  - replace (cross C A B) with (cross A B C) by apply cross_cycle2. exact Hd.
  - exact Hs.
  - apply (skB_rot B C A). apply skC_rot. exact Hp.
  - apply (skA_rot B C A). apply skB_rot. exact Hq.
  - apply (skC_rot B C A). apply skA_rot. exact Hu.
Qed.

Local Ltac le_c :=
  match goal with
  | H : skA ?A ?B ?C ?X |- cross ?A ?B ?X <= 0 =>
      destruct H as [? [? Hc]]; apply Rlt_le; exact Hc
  | H : skB ?A ?B ?C ?X |- cross ?A ?B ?X <= 0 =>
      destruct H as [? [? Hc]]; apply Rlt_le; exact Hc
  end.

Local Ltac le_a :=
  match goal with
  | H : skB ?A ?B ?C ?X |- cross ?B ?C ?X <= 0 =>
      destruct H as [Ha [? ?]]; apply Rlt_le; exact Ha
  | H : skC ?A ?B ?C ?X |- cross ?B ?C ?X <= 0 =>
      destruct H as [Ha [? ?]]; apply Rlt_le; exact Ha
  end.

Local Ltac le_b :=
  match goal with
  | H : skA ?A ?B ?C ?X |- cross ?C ?A ?X <= 0 =>
      destruct H as [? [Hb ?]]; apply Rlt_le; exact Hb
  | H : skC ?A ?B ?C ?X |- cross ?C ?A ?X <= 0 =>
      destruct H as [? [Hb ?]]; apply Rlt_le; exact Hb
  end.

Local Ltac out_c :=
  left; apply some_outer_ab; unfold outer3; repeat split; le_c.
Local Ltac out_a :=
  left; unfold some_outer; right; left; unfold outer3; repeat split; le_a.
Local Ltac out_b :=
  left; unfold some_outer; do 2 right; left; unfold outer3; repeat split; le_b.

Lemma spikes_cert : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  (skA A B C P \/ skB A B C P \/ skC A B C P) ->
  (skA A B C Q \/ skB A B C Q \/ skC A B C Q) ->
  (skA A B C U \/ skB A B C U \/ skC A B C U) ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  destruct Hp as [Pa|[Pb|Pc]]; destruct Hq as [Qa|[Qb|Qc]];
  destruct Hu as [Ua|[Ub|Uc]].
  - out_c. (* AAA *)
  - out_c. (* AAB *)
  - out_b. (* AAC *)
  - out_c. (* ABA *)
  - out_c. (* ABB *)
  - apply or_intror. apply (spikes_ccw A B C P Q U); assumption. (* ABC *)
  - out_b. (* ACA *)
  - exfalso. apply (spikes_cw_false A B C P Q U); assumption. (* ACB *)
  - out_b. (* ACC *)
  - out_c. (* BAA *)
  - out_c. (* BAB *)
  - exfalso. apply (spikes_cw_rot_false A B C P Q U); assumption. (* BAC *)
  - out_c. (* BBA *)
  - out_c. (* BBB *)
  - out_a. (* BBC *)
  - apply or_intror. apply (spikes_ccw_rot A B C P Q U); assumption. (* BCA *)
  - out_a. (* BCB *)
  - out_a. (* BCC *)
  - out_b. (* CAA *)
  - apply or_intror. apply (spikes_ccw_rot2 A B C P Q U); assumption. (* CAB *)
  - out_b. (* CAC *)
  - exfalso. apply (spikes_cw_rot2_false A B C P Q U); assumption. (* CBA *)
  - out_a. (* CBB *)
  - out_a. (* CBC *)
  - out_b. (* CCA *)
  - out_a. (* CCB *)
  - out_a. (* CCC *)
Qed.

Lemma qu_gap_b : forall A B C Q U,
  0 < cross A B C ->
  cross Q U B - cross Q U A = cross A B Q - cross A B U.
Proof.
  intros A B C Q U Hd.
  assert (E := qu_b_gap A B C Q U).
  apply Rmult_eq_reg_l with (r := cross A B C).
  - replace (cross A B C * (cross Q U B - cross Q U A))
      with ((cross Q U B - cross Q U A) * cross A B C) by ring.
    exact E.
  - apply not_eq_sym. apply Rlt_not_eq. exact Hd.
Qed.

Lemma qu_gap_c : forall A B C Q U,
  0 < cross A B C ->
  cross Q U C - cross Q U A = cross C A U - cross C A Q.
Proof.
  intros A B C Q U Hd.
  assert (E := qu_c_gap A B C Q U).
  apply Rmult_eq_reg_l with (r := cross A B C).
  - replace (cross A B C * (cross Q U C - cross Q U A))
      with ((cross Q U C - cross Q U A) * cross A B C) by ring.
    exact E.
  - apply not_eq_sym. apply Rlt_not_eq. exact Hd.
Qed.

(* P lies on line AB, strictly beyond A: c = 0, b < 0, a > 0. *)
Lemma z1_pqA : forall A B C P Q,
  cross A B P = 0 ->
  cross P Q A * cross A B C = cross A B Q * cross C A P.
Proof.
  intros A B C P Q Hc.
  assert (E := sep_nb_A A B C P Q). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma z1_pqB : forall A B C P Q,
  cross A B P = 0 ->
  cross P Q B * cross A B C = - cross A B Q * cross B C P.
Proof.
  intros A B C P Q Hc.
  assert (E := cross_pq_B_na A B C P Q). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma z1_upA : forall A B C P U,
  cross A B P = 0 ->
  cross U P A * cross A B C = - cross A B U * cross C A P.
Proof.
  intros A B C P U Hc.
  assert (E := cross_up_A A B C P U). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma z1_upB : forall A B C P U,
  cross A B P = 0 ->
  cross U P B * cross A B C = cross A B U * cross B C P.
Proof.
  intros A B C P U Hc.
  assert (E := cross_up_B A B C P U). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma wedge_cab : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross C A P * cross C A Q < 0 ->
  cross P Q C * cross P Q A < 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hca Hpq.
  assert (Hm : exists X, tri_open C A B X /\ tri_open P Q U X).
  { apply wedge_edges; try assumption.
    replace (cross C A B) with (cross A B C) by apply cross_cycle2. exact Hd. }
  destruct Hm as [X [Ht HsX]].
  exists X. split; [| exact HsX].
  apply tri_open_rot. exact Ht.
Qed.

Lemma wedge_bca : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross B C P * cross B C Q < 0 ->
  cross P Q B * cross P Q C < 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hbc Hpq.
  assert (Hm : exists X, tri_open B C A X /\ tri_open P Q U X).
  { apply wedge_edges; try assumption.
    replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd. }
  destruct Hm as [X [Ht HsX]].
  exists X. split; [| exact HsX].
  destruct Ht as [H1 [H2 H3]]. repeat split; assumption.
Qed.

Lemma z1_succ : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross A B P = 0 -> cross C A P < 0 -> 0 < cross B C P ->
  0 < cross A B Q -> cross A B U < 0 ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs HcP HbP HaP Hq Hu.
  assert (HPQA : cross P Q A < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqA A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_pos_neg; assumption. }
  assert (HPQB : cross P Q B < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqB A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_neg; [lra | exact HaP]. }
  destruct (Rlt_dec 0 (cross C A U)) as [HbU|HbU].
  - assert (HUPA : cross U P A < 0).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      rewrite (z1_upA A B C P U HcP).
      replace (0 * cross A B C) with 0 by ring.
      apply prod_pos_neg; [lra | exact HbP]. }
    assert (HUPB : cross U P B < 0).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      rewrite (z1_upB A B C P U HcP).
      replace (0 * cross A B C) with 0 by ring.
      apply prod_neg; assumption. }
    assert (HUPC : cross U P C < 0).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      assert (E := cross_up_C A B C P U).
      assert (Ea := cross_sum3 A B C P). rewrite HcP in Ea.
      assert (Eu := cross_sum3 A B C U).
      replace (0 * cross A B C) with 0 by ring.
      (* UPC * Δ = Δ * (bP - bU) - cU * bP *)
      assert (Hrew : cross U P C * cross A B C =
          cross A B C * (cross C A P - cross C A U)
          - cross A B U * cross C A P).
      { rewrite E.
        replace (cross B C U) with
          (cross A B C - cross C A U - cross A B U) by lra.
        replace (cross B C P) with
          (cross A B C - cross C A P) by lra.
        ring. }
      rewrite Hrew.
      assert (H1 : cross A B C * (cross C A P - cross C A U) < 0).
      { apply prod_pos_neg; [exact Hd | lra]. }
      assert (H2 : - cross A B U * cross C A P < 0).
      { apply prod_pos_neg; [lra | exact HbP]. }
      replace (cross A B C * (cross C A P - cross C A U)
                 - cross A B U * cross C A P)
        with (cross A B C * (cross C A P - cross C A U)
              + (- cross A B U * cross C A P)) by ring.
      replace 0 with (0 + 0) by ring.
      apply Rplus_lt_compat; assumption. }
    left. apply some_outer_up. repeat split; apply Rlt_le; assumption.
  - apply Rnot_lt_le in HbU.
    destruct (Rlt_dec 0 (cross P Q C)) as [HC|HC].
    + destruct (Rlt_dec 0 (cross C A Q)) as [HbQ|HbQ].
      * right. apply wedge_cab; try assumption.
        -- apply prod_neg; assumption.
        -- assert (Hprod : cross P Q A * cross P Q C < 0).
           { apply prod_neg; [exact HPQA | exact HC]. }
           replace (cross P Q C * cross P Q A)
             with (cross P Q A * cross P Q C) by ring.
           exact Hprod.
      * apply Rnot_lt_le in HbQ.
        left. unfold some_outer. right. right. left.
        repeat split; [apply Rlt_le; exact HbP | exact HbQ | exact HbU].
    + apply Rnot_lt_le in HC.
      left. apply some_outer_pq. repeat split; [apply Rlt_le; exact HPQA |
        apply Rlt_le; exact HPQB | exact HC].
Qed.

Lemma face_pos : forall sM sV u,
  0 <= sM -> 0 <= sV -> 0 < u -> u < 1 ->
  (sM = 0 -> 0 < sV) ->
  0 < (1 - u) * sM + u * sV.
Proof.
  intros sM sV u Hm Hv Hu Hu1 Hlift.
  destruct (Rle_lt_or_eq_dec 0 sM Hm) as [Hgt|Heq].
  - apply Rplus_lt_le_0_compat; [apply Rmult_lt_0_compat; lra | apply Rmult_le_pos; lra].
  - apply slack_mix_pos; [rewrite <- Heq; lra | apply Hlift; symmetry; exact Heq | exact Hu | lra].
Qed.

Lemma nudge_meet : forall A B C D E F M V,
  0 < cross A B C ->
  tri_open A B C M ->
  0 <= cross D E M -> 0 <= cross E F M -> 0 <= cross F D M ->
  0 <= cross D E V -> 0 <= cross E F V -> 0 <= cross F D V ->
  (cross D E M = 0 -> 0 < cross D E V) ->
  (cross E F M = 0 -> 0 < cross E F V) ->
  (cross F D M = 0 -> 0 < cross F D V) ->
  exists X, tri_open A B C X /\ tri_open D E F X.
Proof.
  intros A B C D E F M V Hd HM HdeM HefM HfdM HdeV HefV HfdV Lde Lef Lfd.
  destruct HM as [HmAB [HmBC HmCA]].
  set (rooms :=
    [ seg_room (cross A B M) (cross A B V);
      seg_room (cross B C M) (cross B C V);
      seg_room (cross C A M) (cross C A V) ]).
  set (t := rmin_list rooms).
  assert (Ht : 0 < t).
  { unfold t, rooms. apply rmin_list_pos. intros s Hin. simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]]; apply seg_room_pos; assumption. }
  set (u := t / 2).
  assert (Hu : 0 < u) by (unfold u; lra).
  assert (Hu1 : u < 1).
  { assert (Hh := rmin_list_half rooms). unfold u, t in *. lra. }
  assert (HuAB : u < seg_room (cross A B M) (cross A B V)).
  { apply Rlt_le_trans with (r2 := t); [unfold u; lra | unfold t].
    apply rmin_list_le. unfold rooms. simpl. left. reflexivity. }
  assert (HuBC : u < seg_room (cross B C M) (cross B C V)).
  { apply Rlt_le_trans with (r2 := t); [unfold u; lra | unfold t].
    apply rmin_list_le. unfold rooms. simpl. right. left. reflexivity. }
  assert (HuCA : u < seg_room (cross C A M) (cross C A V)).
  { apply Rlt_le_trans with (r2 := t); [unfold u; lra | unfold t].
    apply rmin_list_le. unfold rooms. simpl. right. right. left. reflexivity. }
  set (X := convex_combination M V u). exists X. split.
  - repeat split; unfold X; rewrite cross_combo.
    + apply slack_pos_room; [exact HmAB | apply Rlt_le; exact Hu | exact HuAB].
    + apply slack_pos_room; [exact HmBC | apply Rlt_le; exact Hu | exact HuBC].
    + apply slack_pos_room; [exact HmCA | apply Rlt_le; exact Hu | exact HuCA].
  - repeat split; unfold X; rewrite cross_combo.
    + apply face_pos; assumption.
    + apply face_pos; assumption.
    + apply face_pos; assumption.
Qed.

Lemma z1_pred : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross A B P = 0 -> cross C A P < 0 -> 0 < cross B C P ->
  cross A B Q < 0 -> 0 < cross A B U ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs HcP HbP HaP Hq Hu.
  assert (HPQA : 0 < cross P Q A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqA A B C P Q HcP). replace (0 * cross A B C) with 0 by ring.
    replace (cross A B Q * cross C A P)
      with ((- cross A B Q) * (- cross C A P)) by ring.
    apply Rmult_lt_0_compat; lra. }
  assert (HUPA : 0 < cross U P A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_upA A B C P U HcP). replace (0 * cross A B C) with 0 by ring.
    replace (- cross A B U * cross C A P)
      with (cross A B U * (- cross C A P)) by ring.
    apply Rmult_lt_0_compat; lra. }
  destruct (Rlt_dec 0 (cross Q U A)) as [HQA|HQA].
  - right.
    destruct (meet_vertex P Q U A B C A Hs Hd (or_introl eq_refl)
                (conj HPQA (conj HQA HUPA))) as [X [HsX HtX]].
    exists X. split; assumption.
  - apply Rnot_lt_le in HQA.
    assert (HQUB : cross Q U B < 0).
    { assert (E := qu_gap_b A B C Q U Hd). lra. }
    destruct (Rlt_dec 0 (cross Q U C)) as [HQC|HQC].
    + assert (HbQ : cross C A Q < 0).
      { destruct (Rle_dec 0 (cross C A Q)) as [Hge|Hlt];
          [| apply Rnot_le_lt; exact Hlt].
        assert (Hgc := qu_gap_c A B C Q U Hd). exfalso.
        destruct (Rlt_dec (cross C A U) 0) as [Hun|Hup].
        - assert (E := Hgc). assert (HQ : cross Q U C < 0) by lra.
          apply (Rlt_asym 0 (cross Q U C) HQC HQ).
        - apply Rnot_lt_le in Hup.
          assert (Eneg : cross Q U A * cross A B C =
              cross C A Q * cross A B U + (- cross A B Q) * cross C A U).
          { rewrite (qua_bb A B C Q U). ring. }
          assert (Hle : cross Q U A * cross A B C <= 0).
          { apply Rle_trans with (r2 := 0 * cross A B C).
            - apply Rmult_le_compat_r; [apply Rlt_le; exact Hd | exact HQA].
            - replace (0 * cross A B C) with 0 by ring. apply Rle_refl. }
          destruct (Rle_lt_or_eq_dec 0 (cross C A Q) Hge) as [Hqb|Hqe].
          + assert (Hpos : 0 < cross C A Q * cross A B U
                             + (- cross A B Q) * cross C A U).
            { apply Rplus_lt_le_0_compat.
              - apply Rmult_lt_0_compat; [exact Hqb | exact Hu].
              - apply Rmult_le_pos; lra. }
            apply (Rle_not_lt 0 _ Hle). rewrite Eneg. exact Hpos.
          + destruct (Rle_lt_or_eq_dec 0 (cross C A U) Hup) as [Hub|Hue].
            * assert (Hpos : 0 < cross C A Q * cross A B U
                               + (- cross A B Q) * cross C A U).
              { rewrite <- Hqe.
                replace (0 * cross A B U + (- cross A B Q) * cross C A U)
                  with ((- cross A B Q) * cross C A U) by ring.
                apply Rmult_lt_0_compat; lra. }
              apply (Rle_not_lt 0 _ Hle). rewrite Eneg. exact Hpos.
            * assert (Hz : cross Q U A = 0).
              { apply Rmult_eq_reg_l with (r := cross A B C).
                - replace (cross A B C * cross Q U A)
                    with (cross Q U A * cross A B C) by ring.
                  rewrite Eneg. rewrite <- Hqe. rewrite <- Hue. ring.
                - apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
              assert (Hc0 : cross Q U C = 0).
              { assert (E := Hgc). rewrite Hz in E. rewrite <- Hqe in E.
                rewrite <- Hue in E. lra. }
              apply (Rlt_not_eq 0 (cross Q U C) HQC). symmetry. exact Hc0. }
      destruct (Rlt_dec 0 (cross C A U)) as [HbU|HbU].
      * right.
        destruct (Rle_lt_or_eq_dec _ _ HQA) as [Hqa|Hqe].
        -- assert (Hm : exists X, tri_open A B C X /\ tri_open Q U P X).
           { apply wedge_cab; try assumption.
             - replace (cross Q U P) with (cross P Q U)
                 by (rewrite cross_cycle; reflexivity). exact Hs.
             - apply prod_neg; assumption.
             - apply prod_pos_neg; [exact HQC | exact Hqa]. }
           destruct Hm as [X [Ht HsX]]. exists X. split;
             [exact Ht | apply tri_open_rot; apply tri_open_rot; exact HsX].
        -- assert (HaQ : 0 < cross B C Q).
           { assert (E := cross_sum3 A B C Q). lra. }
           destruct (Rlt_dec 0 (cross B C U)) as [HaU|HaU].
           ++ destruct (meet_vertex A B C P Q U U Hd Hs
                         (or_intror (or_intror (or_introl eq_refl)))
                         (conj Hu (conj HaU HbU))) as [X [Ht HsX]].
              exists X. split; assumption.
           ++ apply Rnot_lt_le in HaU.
              destruct (Rle_lt_or_eq_dec _ _ HaU) as [HaUn|HaU0].
              ** assert (Hm : exists X, tri_open B C A X /\ tri_open Q U P X).
                 { apply wedge_edges.
                   - replace (cross B C A) with (cross A B C)
                       by apply cross_cycle. exact Hd.
                   - replace (cross Q U P) with (cross P Q U)
                       by (rewrite cross_cycle; reflexivity). exact Hs.
                   - apply prod_pos_neg; [exact HaQ | exact HaUn].
                   - apply prod_neg; [exact HQUB | exact HQC]. }
                 destruct Hm as [X [Ht HsX]]. exists X. split.
                 --- destruct Ht as [H1 [H2 H3]]. repeat split; assumption.
                 --- destruct HsX as [H1 [H2 H3]]. repeat split; assumption.
              ** set (Mpt := convex_combination A U (1 / 2)).
                 assert (HMopen : tri_open A B C Mpt).
                 { repeat split; unfold Mpt; rewrite cross_combo.
                   - rewrite (cross_third_eq_first A B). lra.
                   - rewrite HaU0. rewrite <- (cross_cycle A B C). lra.
                   - rewrite (cross_third_eq_second C A). lra. }
                 assert (HpqM : 0 < cross P Q Mpt).
                 { unfold Mpt. rewrite cross_combo. lra. }
                 assert (HupM : 0 < cross U P Mpt).
                 { unfold Mpt. rewrite cross_combo.
                   rewrite (cross_third_eq_first U P). lra. }
                 assert (HquM : cross Q U Mpt = 0).
                 { unfold Mpt. rewrite cross_combo. rewrite Hqe.
                   rewrite (cross_third_eq_second Q U). ring. }
                 assert (HquP : 0 < cross Q U P).
                 { replace (cross Q U P) with (cross P Q U)
                     by (rewrite cross_cycle; reflexivity). exact Hs. }
                 apply (nudge_meet A B C P Q U Mpt P Hd HMopen).
                 --- apply Rlt_le. exact HpqM.
                 --- rewrite HquM. apply Rle_refl.
                 --- apply Rlt_le. exact HupM.
                 --- rewrite (cross_third_eq_first P Q). apply Rle_refl.
                 --- apply Rlt_le. exact HquP.
                 --- rewrite (cross_third_eq_second U P). apply Rle_refl.
                 --- intros Hz. exfalso. apply (Rlt_not_eq 0 _ HpqM).
                     symmetry. exact Hz.
                 --- intros _. exact HquP.
                 --- intros Hz. exfalso. apply (Rlt_not_eq 0 _ HupM).
                     symmetry. exact Hz.
      * apply Rnot_lt_le in HbU.
        left. unfold some_outer. right. right. left. repeat split.
        -- apply Rlt_le. exact HbP.
        -- apply Rlt_le. exact HbQ.
        -- exact HbU.
    + apply Rnot_lt_le in HQC.
      left. apply some_outer_qu. repeat split; [exact HQA | apply Rlt_le; exact HQUB | exact HQC].
Qed.

Lemma some_outer_rot_T : forall A B C P Q U,
  some_outer B C A P Q U -> some_outer A B C P Q U.
Proof.
  intros A B C P Q U [H|[H|[H|[H|[H|H]]]]].
  - right. left. exact H.
  - do 2 right. left. exact H.
  - left. exact H.
  - apply some_outer_pq. apply outer3_rot. apply outer3_rot. exact H.
  - apply some_outer_qu. apply outer3_rot. apply outer3_rot. exact H.
  - apply some_outer_up. apply outer3_rot. apply outer3_rot. exact H.
Qed.

Lemma some_outer_rot2_T : forall A B C P Q U,
  some_outer C A B P Q U -> some_outer A B C P Q U.
Proof.
  intros A B C P Q U H.
  apply (some_outer_rot_T A B C).
  apply (some_outer_rot_T B C A). exact H.
Qed.

Lemma some_outer_rot_S : forall A B C P Q U,
  some_outer A B C Q U P -> some_outer A B C P Q U.
Proof.
  intros A B C P Q U [H|[H|[H|[H|[H|H]]]]].
  - left. apply outer3_rot. apply outer3_rot. exact H.
  - right. left. apply outer3_rot. apply outer3_rot. exact H.
  - do 2 right. left. apply outer3_rot. apply outer3_rot. exact H.
  - apply some_outer_qu. exact H.
  - apply some_outer_up. exact H.
  - apply some_outer_pq. exact H.
Qed.

(* P on line AB. The signed area of PQU splits across the QU slacks at A and B. *)
Lemma z1_area : forall A B C P Q U,
  0 < cross A B C ->
  cross A B P = 0 ->
  cross P Q U * cross A B C =
    cross B C P * cross Q U A + cross C A P * cross Q U B.
Proof.
  intros A B C P Q U Hd HcP.
  assert (E := s_qua_id A B C P Q U).
  rewrite HcP in E. ring_simplify in E.
  assert (G := qu_gap_b A B C Q U Hd).
  assert (Sa := cross_sum3 A B C P). rewrite HcP in Sa.
  assert (E1 : cross P Q U * cross A B C =
      cross A B C * cross Q U A
      + cross C A P * (cross Q U B - cross Q U A)).
  { rewrite E. rewrite G. ring. }
  replace (cross B C P) with (cross A B C - cross C A P) by lra.
  rewrite E1. ring.
Qed.

Lemma z1_nonpos : forall A B C P Q U,
  cross A B P = 0 ->
  cross A B Q <= 0 ->
  cross A B U <= 0 ->
  some_outer A B C P Q U.
Proof.
  intros A B C P Q U HcP Hq Hu.
  apply some_outer_ab. repeat split; [rewrite HcP; apply Rle_refl | exact Hq | exact Hu].
Qed.

(* P beyond A on line AB, and both Q and U strictly on C's side of AB. *)
Lemma z1_pos : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross A B P = 0 -> cross C A P < 0 -> 0 < cross B C P ->
  0 < cross A B Q -> 0 < cross A B U ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs HcP HbP HaP Hq Hu.
  assert (HPQA : cross P Q A < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqA A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_pos_neg; assumption. }
  assert (HPQB : cross P Q B < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqB A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_neg; [lra | exact HaP]. }
  destruct (Rlt_dec 0 (cross P Q C)) as [HPC|HPC].
  - destruct (Rlt_dec 0 (cross C A Q)) as [HbQ|HbQ].
    + right. apply wedge_cab; try assumption.
      * apply prod_neg; assumption.
      * apply prod_pos_neg; [exact HPC | exact HPQA].
    + apply Rnot_lt_le in HbQ.
      destruct (Rlt_dec (cross B C Q) 0) as [HaQn|HaQ].
      * right. apply wedge_bca; try assumption.
        -- apply prod_pos_neg; [exact HaP | exact HaQn].
        -- apply prod_neg; [exact HPQB | exact HPC].
      * apply Rnot_lt_le in HaQ.
        destruct (Rlt_dec 0 (cross C A U)) as [HbU|HbU].
        -- assert (HQA : cross Q U A < 0).
           { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
             rewrite (qua_bb A B C Q U).
             replace (0 * cross A B C) with 0 by ring.
             assert (Hle : cross C A Q * cross A B U <= 0).
             { assert (Hc : cross C A Q * cross A B U <= 0 * cross A B U).
               { apply Rmult_le_compat_r; [apply Rlt_le; exact Hu | exact HbQ]. }
               replace (0 * cross A B U) with 0 in Hc by ring. exact Hc. }
             assert (Hneg : - (cross A B Q * cross C A U) < 0).
             { assert (Hp : 0 < cross A B Q * cross C A U).
               { apply Rmult_lt_0_compat; assumption. }
               lra. }
             assert (Hsum : cross C A Q * cross A B U
                            - cross A B Q * cross C A U < 0) by lra.
             exact Hsum. }
           assert (HQUB : cross Q U B < 0).
           { assert (E := z1_area A B C P Q U Hd HcP).
             assert (Hap : cross B C P * cross Q U A < 0).
             { apply prod_pos_neg; [exact HaP | exact HQA]. }
             assert (Hbp : 0 < cross C A P * cross Q U B).
             { assert (Hsd : 0 < cross P Q U * cross A B C).
               { apply Rmult_lt_0_compat; assumption. }
               assert (Hdiff : 0 < cross P Q U * cross A B C
                                 - cross B C P * cross Q U A) by lra.
               replace (cross P Q U * cross A B C - cross B C P * cross Q U A)
                 with (cross C A P * cross Q U B) in Hdiff by (rewrite E; ring).
               exact Hdiff. }
             destruct (Rle_dec 0 (cross Q U B)) as [Hge|Hlt].
             - exfalso.
               assert (Hle : cross C A P * cross Q U B <= cross C A P * 0).
               { apply Rmult_le_compat_neg_l; lra. }
               replace (cross C A P * 0) with 0 in Hle by ring.
               apply (Rle_not_lt 0 _ Hle). exact Hbp.
             - apply Rnot_le_lt. exact Hlt. }
           destruct (Rlt_dec 0 (cross Q U C)) as [HQC|HQC].
           ++ destruct (Rle_lt_or_eq_dec _ _ HbQ) as [HbQn|HbQ0].
              ** right.
                 assert (Hm : exists X, tri_open C A B X /\ tri_open Q U P X).
                 { apply wedge_edges.
                   - replace (cross C A B) with (cross A B C) by apply cross_cycle2.
                     exact Hd.
                   - replace (cross Q U P) with (cross P Q U)
                       by (rewrite cross_cycle; reflexivity). exact Hs.
                   - apply prod_neg; assumption.
                   - apply prod_pos_neg; [exact HQC | exact HQA]. }
                 destruct Hm as [X [Ht HsX]]. exists X. split.
                 --- apply tri_open_rot. exact Ht.
                 --- apply tri_open_rot. apply tri_open_rot. exact HsX.
              ** assert (HaQpos : 0 < cross B C Q).
                 { destruct (Rle_lt_or_eq_dec 0 (cross B C Q) HaQ) as [Hgt|Heq].
                   - exact Hgt.
                   - exfalso.
                     assert (HcQd : cross A B Q = cross A B C).
                     { assert (Es := cross_sum3 A B C Q). lra. }
                     assert (Ebb := qua_bb A B C Q U).
                     rewrite HbQ0 in Ebb. rewrite HcQd in Ebb.
                     assert (Hqa : cross Q U A = - cross C A U).
                     { apply Rmult_eq_reg_l with (r := cross A B C).
                       - replace (cross A B C * cross Q U A)
                           with (cross Q U A * cross A B C) by ring.
                         rewrite Ebb. ring.
                       - apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
                     assert (Hz : cross Q U C = 0).
                     { assert (Egc := qu_gap_c A B C Q U Hd).
                       rewrite Hqa in Egc. rewrite HbQ0 in Egc. lra. }
                     apply (Rlt_not_eq 0 (cross Q U C) HQC). symmetry. exact Hz. }
                 right.
                 set (room := seg_room (cross B C Q) (cross B C U)).
                 assert (Hroom : 0 < room).
                 { unfold room. apply seg_room_pos. exact HaQpos. }
                 set (t := Rmin (room / 2) (1 / 2)).
                 assert (Ht0 : 0 < t).
                 { unfold t. apply Rmin_pos; lra. }
                 assert (Ht1 : t < 1).
                 { assert (Hle : t <= 1 / 2) by (unfold t; apply Rmin_r). lra. }
                 assert (Htroom : t < room).
                 { assert (Hle : t <= room / 2) by (unfold t; apply Rmin_l).
                   apply Rle_lt_trans with (r2 := room / 2); [exact Hle | lra]. }
                 set (Mpt := convex_combination Q U t).
                 assert (HcM : 0 < cross A B Mpt).
                 { unfold Mpt. rewrite cross_combo.
                   assert (H1 : 0 < (1 - t) * cross A B Q).
                   { apply Rmult_lt_0_compat; lra. }
                   assert (H2 : 0 < t * cross A B U).
                   { apply Rmult_lt_0_compat; assumption. }
                   lra. }
                 assert (HbM : 0 < cross C A Mpt).
                 { unfold Mpt. rewrite cross_combo. rewrite HbQ0.
                   replace ((1 - t) * 0 + t * cross C A U)
                     with (t * cross C A U) by ring.
                   apply Rmult_lt_0_compat; assumption. }
                 assert (HaM : 0 < cross B C Mpt).
                 { unfold Mpt. rewrite cross_combo.
                   apply slack_pos_room; [exact HaQpos | apply Rlt_le; exact Ht0 |
                     exact Htroom]. }
                 assert (HpqM : 0 < cross P Q Mpt).
                 { unfold Mpt. rewrite cross_combo.
                   rewrite (cross_third_eq_second P Q).
                   replace ((1 - t) * 0 + t * cross P Q U)
                     with (t * cross P Q U) by ring.
                   apply Rmult_lt_0_compat; assumption. }
                 assert (HupM : 0 < cross U P Mpt).
                 { unfold Mpt. rewrite cross_combo.
                   rewrite (cross_third_eq_first U P).
                   replace (cross U P Q) with (cross P Q U)
                     by (rewrite <- cross_cycle; reflexivity).
                   replace ((1 - t) * cross P Q U + t * 0)
                     with ((1 - t) * cross P Q U) by ring.
                   apply Rmult_lt_0_compat; lra. }
                 assert (HquM : cross Q U Mpt = 0).
                 { unfold Mpt. rewrite cross_combo.
                   rewrite (cross_third_eq_first Q U).
                   rewrite (cross_third_eq_second Q U). ring. }
                 assert (HquP : 0 < cross Q U P).
                 { replace (cross Q U P) with (cross P Q U)
                     by (rewrite cross_cycle; reflexivity). exact Hs. }
                 apply (nudge_meet A B C P Q U Mpt P Hd).
                 --- repeat split; assumption.
                 --- apply Rlt_le. exact HpqM.
                 --- rewrite HquM. apply Rle_refl.
                 --- apply Rlt_le. exact HupM.
                 --- rewrite (cross_third_eq_first P Q). apply Rle_refl.
                 --- apply Rlt_le. exact HquP.
                 --- rewrite (cross_third_eq_second U P). apply Rle_refl.
                 --- intros Hz. exfalso.
                     apply (Rlt_not_eq 0 _ HpqM). symmetry. exact Hz.
                 --- intros _. exact HquP.
                 --- intros Hz. exfalso.
                     apply (Rlt_not_eq 0 _ HupM). symmetry. exact Hz.
           ++ apply Rnot_lt_le in HQC.
              left. apply some_outer_qu. repeat split;
                [apply Rlt_le; exact HQA | apply Rlt_le; exact HQUB | exact HQC].
        -- apply Rnot_lt_le in HbU.
           left. unfold some_outer. do 2 right. left. repeat split.
           ++ apply Rlt_le. exact HbP.
           ++ exact HbQ.
           ++ exact HbU.
  - apply Rnot_lt_le in HPC.
    left. apply some_outer_pq. repeat split;
      [apply Rlt_le; exact HPQA | apply Rlt_le; exact HPQB | exact HPC].
Qed.

(* U lies on line AB as well, on the same side of A as P, and Q is strictly
   on C's side. The far vertex U is then strictly outside edge CA. *)
Lemma z1_cu0 : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross A B P = 0 -> cross C A P < 0 -> 0 < cross B C P ->
  0 < cross A B Q -> cross A B U = 0 ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs HcP HbP HaP Hq HcU.
  assert (HPQA : cross P Q A < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqA A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_pos_neg; assumption. }
  assert (HPQB : cross P Q B < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqB A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_neg; [lra | exact HaP]. }
  assert (Hsd : cross P Q U * cross A B C =
      cross A B C * cross Q U A + cross C A P * cross A B Q).
  { assert (E := z1_area A B C P Q U Hd HcP).
    assert (G := qu_gap_b A B C Q U Hd). rewrite HcU in G.
    assert (Sa := cross_sum3 A B C P). rewrite HcP in Sa.
    rewrite E. replace (cross Q U B) with (cross Q U A + cross A B Q) by lra.
    replace (cross B C P) with (cross A B C - cross C A P) by lra. ring. }
  assert (HQA : 0 < cross Q U A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    replace (0 * cross A B C) with 0 by ring.
    assert (Hpos : 0 < cross P Q U * cross A B C
                     - cross C A P * cross A B Q).
    { assert (Hs0 : 0 < cross P Q U * cross A B C).
      { apply Rmult_lt_0_compat; assumption. }
      assert (Hn : cross C A P * cross A B Q < 0) by (apply prod_neg; assumption).
      lra. }
    replace (cross Q U A * cross A B C)
      with (cross P Q U * cross A B C - cross C A P * cross A B Q)
      by (rewrite Hsd; ring).
    exact Hpos. }
  assert (HbU : cross C A U < 0).
  {     assert (E0 : cross Q U A * cross A B C =
        - cross A B Q * cross C A U).
    { assert (E := qua_bb A B C Q U). rewrite HcU in E. ring_simplify in E.
      exact E. }
    assert (Hlt : cross A B Q * cross C A U < 0).
    { assert (Hp : 0 < cross Q U A * cross A B C).
      { apply Rmult_lt_0_compat; assumption. }
      rewrite E0 in Hp. lra. }
    destruct (Rle_dec 0 (cross C A U)) as [Hge|HltU].
    - exfalso.
      assert (Hge0 : 0 <= cross A B Q * cross C A U).
      { apply Rmult_le_pos; [apply Rlt_le; exact Hq | exact Hge]. }
      apply (Rle_not_lt (cross A B Q * cross C A U) 0 Hge0). exact Hlt.
    - apply Rnot_le_lt. exact HltU. }
  assert (HaU : 0 < cross B C U).
  { assert (E := cross_sum3 A B C U). rewrite HcU in E. lra. }
  destruct (Rlt_dec 0 (cross C A Q)) as [HbQ|HbQ].
  - destruct (Rlt_dec 0 (cross P Q C)) as [HPC|HPC].
    + destruct (Rlt_dec (cross B C Q) 0) as [HaQn|HaQ].
      * right. apply wedge_bca; try assumption.
        -- apply prod_pos_neg; [exact HaP | exact HaQn].
        -- apply prod_neg; [exact HPQB | exact HPC].
      * apply Rnot_lt_le in HaQ.
        destruct (Rle_lt_or_eq_dec 0 (cross B C Q) HaQ) as [HaQgt|HaQ0].
        -- right.
           destruct (meet_vertex A B C P Q U Q Hd Hs
                      (or_intror (or_introl eq_refl))
                      (conj Hq (conj HaQgt HbQ))) as [X [Ht HsX]].
           exists X. split; assumption.
        -- right.
           set (room := seg_room (cross C A Q) (cross C A U)).
           assert (Hroom : 0 < room).
           { unfold room. apply seg_room_pos. exact HbQ. }
           set (t := Rmin (room / 2) (1 / 2)).
           assert (Ht0 : 0 < t).
           { unfold t. apply Rmin_pos; lra. }
           assert (Ht1 : t < 1).
           { assert (Hle : t <= 1 / 2) by (unfold t; apply Rmin_r). lra. }
           assert (Htroom : t < room).
           { assert (Hle : t <= room / 2) by (unfold t; apply Rmin_l).
             apply Rle_lt_trans with (r2 := room / 2); [exact Hle | lra]. }
           set (Mpt := convex_combination Q U t).
           assert (HcM : 0 < cross A B Mpt).
           { unfold Mpt. rewrite cross_combo. rewrite HcU.
             replace ((1 - t) * cross A B Q + t * 0)
               with ((1 - t) * cross A B Q) by ring.
             apply Rmult_lt_0_compat; lra. }
           assert (HaM : 0 < cross B C Mpt).
           { unfold Mpt. rewrite cross_combo. rewrite <- HaQ0.
             replace ((1 - t) * 0 + t * cross B C U)
               with (t * cross B C U) by ring.
             apply Rmult_lt_0_compat; assumption. }
           assert (HbM : 0 < cross C A Mpt).
           { unfold Mpt. rewrite cross_combo.
             apply slack_pos_room; [exact HbQ | apply Rlt_le; exact Ht0 |
               exact Htroom]. }
           assert (HpqM : 0 < cross P Q Mpt).
           { unfold Mpt. rewrite cross_combo.
             rewrite (cross_third_eq_second P Q).
             replace ((1 - t) * 0 + t * cross P Q U)
               with (t * cross P Q U) by ring.
             apply Rmult_lt_0_compat; assumption. }
           assert (HupM : 0 < cross U P Mpt).
           { unfold Mpt. rewrite cross_combo.
             rewrite (cross_third_eq_first U P).
             replace (cross U P Q) with (cross P Q U)
               by (rewrite <- cross_cycle; reflexivity).
             replace ((1 - t) * cross P Q U + t * 0)
               with ((1 - t) * cross P Q U) by ring.
             apply Rmult_lt_0_compat; lra. }
           assert (HquM : cross Q U Mpt = 0).
           { unfold Mpt. rewrite cross_combo.
             rewrite (cross_third_eq_first Q U).
             rewrite (cross_third_eq_second Q U). ring. }
           assert (HquP : 0 < cross Q U P).
           { replace (cross Q U P) with (cross P Q U)
               by (rewrite cross_cycle; reflexivity). exact Hs. }
           apply (nudge_meet A B C P Q U Mpt P Hd).
           --- repeat split; assumption.
           --- apply Rlt_le. exact HpqM.
           --- rewrite HquM. apply Rle_refl.
           --- apply Rlt_le. exact HupM.
           --- rewrite (cross_third_eq_first P Q). apply Rle_refl.
           --- apply Rlt_le. exact HquP.
           --- rewrite (cross_third_eq_second U P). apply Rle_refl.
           --- intros Hz. exfalso.
               apply (Rlt_not_eq 0 _ HpqM). symmetry. exact Hz.
           --- intros _. exact HquP.
           --- intros Hz. exfalso.
               apply (Rlt_not_eq 0 _ HupM). symmetry. exact Hz.
    + apply Rnot_lt_le in HPC.
      left. apply some_outer_pq. repeat split;
        [apply Rlt_le; exact HPQA | apply Rlt_le; exact HPQB | exact HPC].
  - apply Rnot_lt_le in HbQ.
    left. unfold some_outer. do 2 right. left. repeat split.
    + apply Rlt_le. exact HbP.
    + exact HbQ.
    + apply Rlt_le. exact HbU.
Qed.
