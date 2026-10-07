(* NetTopologySuite.Proofs.TrianglePairSepCap
   Cap and outer-edge half of the separating-edge follow-up.
   sat_iff is deferred. Not Admitted.
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
From NTS.Proofs Require Export TrianglePairSep.
Local Open Scope R_scope.

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

(* Assumptions: sig_not_dec, sig_forall_dec, functional_extensionality_dep. *)
Print Assumptions na_nb_sum.
Print Assumptions cross_pq_B_na.
Print Assumptions pqc_na.
Print Assumptions au_aq_id.
Print Assumptions qu_B_minus_A.
Print Assumptions qu_C_minus_B.
Print Assumptions up_b_from_qu.
Print Assumptions aq_neg.
Print Assumptions au_gt_aq.
Print Assumptions touch_line_open.
Print Assumptions na_cap_closed_u.
Print Assumptions gap_cp_cross.
Print Assumptions cross_up_A.
Print Assumptions cross_up_B.
Print Assumptions cross_up_C.
Print Assumptions quA_nb.
Print Assumptions prod_neg.
Print Assumptions prod_pos_neg.
Print Assumptions wedge_c_succ.
Print Assumptions up_outer_na.
Print Assumptions nb_of_sum.
Print Assumptions openA_nbU.
Print Assumptions wedge_c_pred.
Print Assumptions some_outer_ab.
Print Assumptions some_outer_pq.
Print Assumptions some_outer_qu.
Print Assumptions some_outer_up.
Print Assumptions qua_bb.
Print Assumptions qu_b_gap.
Print Assumptions qu_c_gap.
Print Assumptions s_qua_id.
Print Assumptions b_gap_from_s.
Print Assumptions pqa_cu_id.
Print Assumptions bU_of_nb.
Print Assumptions touch_up_A.
Print Assumptions pqa_prod_cu.
Print Assumptions qu_outer_qua.
Print Assumptions pqa_of_qua.
Print Assumptions succ_line_A.
Print Assumptions cap_succ.
Print Assumptions cap_pred.
Print Assumptions cap_ab.
