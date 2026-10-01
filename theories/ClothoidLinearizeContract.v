(* ============================================================================
   NetTopologySuite.Proofs.ClothoidLinearizeContract
   ----------------------------------------------------------------------------
   Uniform arc-length samples of a host clothoid inhabit Linearizes.
   Both Hausdorff directions use the same parameter chord, with
   tol = kappa_max * h^2 / 8. n >= 2. Reverse symmetry swaps sd and ed.
   claimId: 0007-clothoid-linearize. witness: clothoid_linearizes.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia List PeanoNat ZArith.
From NTS.Proofs Require Import Distance Linearise LinearizeContract
  SheetHenClothoidCore ClothoidFresnelInc ClothoidLinearize.
Import ListNotations.
Local Open Scope R_scope.
Lemma ts_01 : forall n k, (n <> 0)%nat -> (k <= n)%nat ->
  0 <= cloth_ts n k <= 1.
Proof.
  intros n k Hn Hk. unfold cloth_ts. split.
  - apply Rmult_le_pos; [apply pos_INR|].
    apply Rlt_le, Rinv_0_lt_compat, lt_0_INR. lia.
  - apply Rmult_le_reg_r with (INR n); [apply lt_0_INR; lia|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply not_0_INR; lia).
    rewrite Rmult_1_r, Rmult_1_l. apply le_INR. exact Hk.
Qed.
Lemma lin_len : forall c n, length (cloth_lin_pts c n) = S n.
Proof.
  intros. unfold cloth_lin_pts. rewrite length_map, length_seq. reflexivity.
Qed.
Lemma lin_nth : forall c n k d, (k <= n)%nat ->
  nth k (cloth_lin_pts c n) d = cloth_eval c (cloth_ts n k).
Proof.
  intros c n k d Hk. unfold cloth_lin_pts.
  rewrite (@nth_indep Point
            (map (fun j => cloth_eval c (cloth_ts n j)) (seq 0 (S n)))
            k d (cloth_eval c (cloth_ts n 0%nat)))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth (fun j => cloth_eval c (cloth_ts n j)) (seq 0 (S n)) 0%nat k).
  rewrite seq_nth by lia. cbn. reflexivity.
Qed.
Lemma cloth_s_affine : forall c u v,
  cloth_s c u - cloth_s c v = (u - v) * (cloth_ed c - cloth_sd c).
Proof. intros. unfold cloth_s. ring. Qed.
Lemma cloth_s_seg : forall c t, 0 <= t <= 1 ->
  Rmin (cloth_sd c) (cloth_ed c) <= cloth_s c t <=
  Rmax (cloth_sd c) (cloth_ed c).
Proof.
  intros c t Ht. unfold cloth_s.
  destruct (Rle_dec (cloth_sd c) (cloth_ed c)) as [H|H].
  - rewrite (Rmin_left _ _ H), (Rmax_right _ _ H). split.
    + apply Rle_trans with (cloth_sd c + 0).
      * rewrite Rplus_0_r. apply Rle_refl.
      * apply Rplus_le_compat_l. apply Rmult_le_pos; lra.
    + apply Rle_trans with (cloth_sd c + (cloth_ed c - cloth_sd c)).
      * apply Rplus_le_compat_l.
        rewrite <- (Rmult_1_l (cloth_ed c - cloth_sd c)) at 2.
        apply Rmult_le_compat_r; lra.
      * replace (cloth_sd c + (cloth_ed c - cloth_sd c))
          with (cloth_ed c).
        -- apply Rle_refl.
        -- ring.
  - apply Rnot_le_lt in H.
    assert (He : cloth_ed c <= cloth_sd c) by lra.
    rewrite (Rmin_right _ _ He), (Rmax_left _ _ He). split.
    + assert (Hp : 0 <= (cloth_sd c - cloth_ed c) * (1 - t))
        by (apply Rmult_le_pos; lra).
      apply (Rplus_le_compat_r (cloth_ed c)) in Hp.
      rewrite Rplus_0_l in Hp.
      replace ((cloth_sd c - cloth_ed c) * (1 - t) + cloth_ed c)
        with (cloth_sd c + t * (cloth_ed c - cloth_sd c)) in Hp by ring.
      exact Hp.
    + assert (Hp : 0 <= t * (cloth_sd c - cloth_ed c))
        by (apply Rmult_le_pos; lra).
      apply Ropp_le_contravar in Hp.
      rewrite Ropp_0, Ropp_mult_distr_r, Ropp_minus_distr in Hp.
      apply (Rplus_le_compat_l (cloth_sd c)) in Hp.
      rewrite Rplus_0_r in Hp. exact Hp.
Qed.
Lemma station_rad : forall c t, 0 <= t <= 1 ->
  Rabs (cloth_s c t) <= cloth_rad c.
Proof.
  intros c t Ht. unfold cloth_rad. apply abs_seg. apply cloth_s_seg. exact Ht.
Qed.
Lemma seg_swap : forall a b lam, seg_at a b lam = seg_at b a (1 - lam).
Proof. intros. unfold seg_at. apply (f_equal2 mkPoint); cbn; ring. Qed.
Lemma cloth_P_rev : forall c s, cloth_P (cloth_rev c) s = cloth_P c s.
Proof.
  intros c s. destruct c as [pl A sd ed m0 m1].
  unfold cloth_rev.
  cbn [cloth_place cloth_A cloth_sd cloth_ed cloth_m0 cloth_m1].
  unfold cloth_P, cloth_Px, cloth_Py.
  rewrite (cloth_Icos_same_place pl A ed sd sd ed m0 m1 m0 m1 s).
  rewrite (cloth_Isin_same_place pl A ed sd sd ed m0 m1 m0 m1 s).
  rewrite (cloth_cos0_same pl A ed sd sd ed m0 m1 m0 m1).
  rewrite (cloth_sin0_same pl A ed sd sd ed m0 m1 m0 m1).
  reflexivity.
Qed.
Lemma cloth_s_rev : forall c t, cloth_s (cloth_rev c) t = cloth_s c (1 - t).
Proof. intros. unfold cloth_rev, cloth_s. cbn. ring. Qed.
Lemma cloth_eval_rev : forall c t,
  cloth_eval (cloth_rev c) t = cloth_eval c (1 - t).
Proof.
  intros. unfold cloth_eval. rewrite cloth_s_rev, cloth_P_rev. reflexivity.
Qed.
Lemma lin_rev_nth : forall c n k, (k <= n)%nat ->
  nth k (rev (cloth_lin_pts c n)) (cloth_eval c 0) =
  cloth_eval c (cloth_ts n (n - k)%nat).
Proof.
  intros c n k Hk.
  assert (Hlen : (k < length (cloth_lin_pts c n))%nat).
  { rewrite lin_len. lia. }
  rewrite (@rev_nth Point (cloth_lin_pts c n) (cloth_eval c 0) k Hlen).
  rewrite lin_len. replace (S n - S k)%nat with (n - k)%nat by lia.
  apply lin_nth. lia.
Qed.
Lemma param_slot : forall n t, (2 <= n)%nat -> 0 <= t <= 1 ->
  exists k, (k < n)%nat /\ cloth_ts n k <= t <= cloth_ts n (S k).
Proof.
  intros n t Hn Ht.
  destruct (Req_dec t 1) as [->|Ht1].
  - exists (n - 1)%nat. split; [lia|]. split.
    + unfold cloth_ts. apply Rmult_le_reg_r with (INR n);
        [apply lt_0_INR; lia|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply not_0_INR; lia).
      rewrite Rmult_1_r, Rmult_1_l. rewrite minus_INR by lia.
      rewrite INR_1. lra.
    + unfold cloth_ts. replace (S (n - 1)) with n by lia.
      cut (INR n / INR n = 1).
      * intros E. rewrite E. apply Rle_refl.
      * field. apply not_0_INR. lia.
  - set (x := t * INR n).
    assert (Hx : 0 <= x < INR n).
    { unfold x. split.
      - apply Rmult_le_pos; [lra|apply pos_INR].
      - rewrite <- (Rmult_1_l (INR n)) at 2.
        apply Rmult_lt_compat_r; [apply lt_0_INR; lia|lra]. }
    destruct (archimed x) as [Hgt Hle].
    set (z := (up x - 1)%Z).
    assert (Hz : (0 <= z)%Z).
    { unfold z. destruct (Z_lt_le_dec (up x) 1) as [Hlt|Hge].
      - exfalso. assert (Hle0 : (up x <= 0)%Z) by lia.
        apply IZR_le in Hle0. replace (IZR 0) with 0 in Hle0 by reflexivity. lra.
      - lia. }
    set (k := Z.to_nat z).
    assert (Eik : INR k = IZR (up x) - 1).
    { unfold k. rewrite INR_IZR_INZ, Z2Nat.id by exact Hz.
      unfold z. rewrite minus_IZR. replace (IZR 1) with 1 by reflexivity.
      reflexivity. }
    assert (Hkn : (k < n)%nat).
    { apply INR_lt. rewrite Eik.
      apply Rle_lt_trans with x; [|exact (proj2 Hx)]. lra. }
    exists k. split; [exact Hkn|]. unfold x in Hgt, Hle, Eik. split.
    + unfold cloth_ts. apply Rmult_le_reg_r with (INR n);
        [apply lt_0_INR; lia|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply not_0_INR; lia).
      rewrite Rmult_1_r. rewrite Eik.
      apply Rplus_le_reg_r with 1.
      replace (IZR (up (t * INR n)) - 1 + 1) with (IZR (up (t * INR n))) by ring.
      apply Rplus_le_reg_l with (- (t * INR n)).
      replace (- (t * INR n) + IZR (up (t * INR n)))
        with (IZR (up (t * INR n)) - t * INR n) by ring.
      replace (- (t * INR n) + (t * INR n + 1)) with 1 by ring.
      exact Hle.
    + unfold cloth_ts. rewrite S_INR.
      apply Rmult_le_reg_r with (INR n); [apply lt_0_INR; lia|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply not_0_INR; lia).
      rewrite Rmult_1_r. rewrite Eik.
      replace (IZR (up (t * INR n)) - 1 + 1) with (IZR (up (t * INR n))) by ring.
      apply Rlt_le. exact Hgt.
Qed.
Lemma sample_near : forall c n k t, cloth_wf c ->
  (n <> 0)%nat -> (k < n)%nat ->
  cloth_ts n k <= t <= cloth_ts n (S k) ->
  dist (cloth_eval c t)
    (seg_at (cloth_eval c (cloth_ts n k))
            (cloth_eval c (cloth_ts n (S k)))
            ((t - cloth_ts n k) / (cloth_ts n (S k) - cloth_ts n k)))
  <= cloth_tol c n.
Proof.
  intros c n k t Hwf Hn Hk Hbin.
  set (tk := cloth_ts n k). set (tS := cloth_ts n (S k)).
  set (lam := (t - tk) / (tS - tk)).
  set (delta := cloth_ed c - cloth_sd c).
  set (sk := cloth_s c tk). set (sS := cloth_s c tS). set (st := cloth_s c t).
  assert (Htk : 0 <= tk <= 1) by (unfold tk; apply ts_01; lia).
  assert (HtS : 0 <= tS <= 1) by (unfold tS; apply ts_01; lia).
  assert (Ht01 : 0 <= t <= 1).
  { split.
    - apply Rle_trans with tk; [exact (proj1 Htk)|exact (proj1 Hbin)].
    - apply Rle_trans with tS; [exact (proj2 Hbin)|exact (proj2 HtS)]. }
  assert (Hden : tS - tk = / INR n).
  { unfold tS, tk, cloth_ts. rewrite S_INR. field. apply not_0_INR. lia. }
  assert (Hdenp : 0 < tS - tk).
  { rewrite Hden. apply Rinv_0_lt_compat, lt_0_INR. lia. }
  assert (Hdlt : sS - sk = (tS - tk) * delta).
  { unfold sS, sk, delta. apply cloth_s_affine. }
  assert (Hstep : Rabs (sS - sk) = cloth_hstep c n).
  { rewrite Hdlt, Hden. unfold cloth_hstep, delta.
    rewrite Rabs_mult, (Rabs_pos_eq (/ INR n))
      by (apply Rlt_le, Rinv_0_lt_compat, lt_0_INR; lia).
    unfold Rdiv. rewrite Rmult_comm. reflexivity. }
  destruct (Req_EM_T delta 0) as [Hz|Hnz].
  - assert (Hs0 : forall u, cloth_s c u = cloth_sd c).
    { intro u. unfold cloth_s. unfold delta in Hz. rewrite Hz. ring. }
    assert (Ep : cloth_eval c t = cloth_eval c tk).
    { unfold cloth_eval. rewrite !Hs0. reflexivity. }
    assert (Es : cloth_eval c tS = cloth_eval c tk).
    { unfold cloth_eval. rewrite !Hs0. reflexivity. }
    rewrite Ep, Es. unfold seg_at.
    replace (mkPoint ((1 - lam) * px (cloth_eval c tk) + lam * px (cloth_eval c tk))
                     ((1 - lam) * py (cloth_eval c tk) + lam * py (cloth_eval c tk)))
      with (cloth_eval c tk).
    + unfold dist, dist_sq. cbn.
      rewrite !Rminus_diag, !Rmult_0_l, Rplus_0_l, sqrt_0.
      unfold cloth_tol, cloth_hstep. unfold delta in Hz. rewrite Hz.
      unfold Rdiv. rewrite Rabs_R0. rewrite (Rmult_0_l (/ INR n)).
      rewrite (Rmult_0_r (cloth_kappa_max c)).
      rewrite (Rmult_0_l 0). rewrite (Rmult_0_l (/ 8)). apply Rle_refl.
    + destruct (cloth_eval c tk) as [x y]. apply (f_equal2 mkPoint); cbn; ring.
  - assert (Hdenz : tS - tk <> 0).
    { intro Hz0. rewrite Hz0 in Hdenp. apply (Rlt_irrefl 0 Hdenp). }
    assert (Hss : sS <> sk).
    { intro E. apply Hnz. apply (Rmult_eq_reg_l (tS - tk)).
      - rewrite Rmult_0_r. rewrite <- Hdlt. rewrite E. ring.
      - exact Hdenz. }
    destruct (Rle_dec sk sS) as [Hord|Hrev].
    + assert (Hgap : 0 <= sS - sk).
      { apply (Rplus_le_compat_r (- sk)) in Hord.
        rewrite Rplus_opp_r in Hord. unfold Rminus. exact Hord. }
      assert (Hdel : 0 <= delta).
      { apply Rmult_le_reg_l with (tS - tk); [exact Hdenp|].
        rewrite Rmult_0_r. rewrite <- Hdlt. exact Hgap. }
      assert (Hst : sk <= st <= sS).
      { unfold delta in Hdel. split.
        - unfold sk, st, cloth_s, delta. apply Rplus_le_compat_l.
          apply Rmult_le_compat_r; [exact Hdel|exact (proj1 Hbin)].
        - unfold st, sS, cloth_s, delta. apply Rplus_le_compat_l.
          apply Rmult_le_compat_r; [exact Hdel|exact (proj2 Hbin)]. }
      assert (Elam : (st - sk) / (sS - sk) = lam).
      { unfold lam, st, sk, sS, delta. rewrite !cloth_s_affine.
        field. split; [exact Hdenz|exact Hnz]. }
      unfold cloth_eval. fold sk sS st. rewrite <- Elam. eapply Rle_trans.
      * apply (chord_near c sk sS st Hwf).
        -- apply station_rad. exact Htk.
        -- apply station_rad. exact HtS.
        -- exact Hst.
      * assert (Eba : sS - sk = cloth_hstep c n).
        { rewrite <- Hstep. symmetry. apply Rabs_right. apply Rle_ge. exact Hgap. }
        rewrite Eba. unfold cloth_tol. apply Rle_refl.
    + assert (HsS : sS < sk) by (apply Rnot_le_lt; exact Hrev).
      assert (Hgap : 0 <= sk - sS).
      { apply Rlt_le in HsS. apply (Rplus_le_compat_r (- sS)) in HsS.
        rewrite Rplus_opp_r in HsS. unfold Rminus. exact HsS. }
      assert (Hneg : sS - sk <= 0).
      { apply Ropp_le_contravar in Hgap. rewrite Ropp_0 in Hgap.
        unfold Rminus in Hgap. rewrite Ropp_plus_distr, Ropp_involutive in Hgap.
        rewrite Rplus_comm in Hgap. unfold Rminus. exact Hgap. }
      assert (Hdel : delta <= 0).
      { apply Rmult_le_reg_l with (tS - tk); [exact Hdenp|].
        rewrite Rmult_0_r. rewrite <- Hdlt. exact Hneg. }
      assert (Hst : sS <= st <= sk).
      { unfold delta in Hdel. split.
        - unfold sS, st, cloth_s, delta. apply Rplus_le_compat_l.
          rewrite (Rmult_comm tS), (Rmult_comm t).
          apply Rmult_le_compat_neg_l; [exact Hdel|exact (proj2 Hbin)].
        - unfold st, sk, cloth_s, delta. apply Rplus_le_compat_l.
          rewrite (Rmult_comm t), (Rmult_comm tk).
          apply Rmult_le_compat_neg_l; [exact Hdel|exact (proj1 Hbin)]. }
      assert (Hsw : tk - tS <> 0).
      { intro E. apply Hdenz.
        replace (tS - tk) with (- (tk - tS)).
        - rewrite E. rewrite Ropp_0. reflexivity.
        - unfold Rminus. rewrite Ropp_plus_distr, Ropp_involutive.
          rewrite Rplus_comm. reflexivity. }
      assert (Elam : (st - sS) / (sk - sS) = 1 - lam).
      { unfold lam, st, sk, sS, delta. rewrite !cloth_s_affine. field.
        repeat split.
        - exact Hdenz.
        - unfold delta in Hnz. exact Hnz.
        - exact Hsw. }
      unfold cloth_eval. fold sk sS.
      rewrite (seg_swap (cloth_P c sk) (cloth_P c sS) lam).
      replace (1 - lam) with ((st - sS) / (sk - sS))
        by (rewrite Elam; reflexivity).
      eapply Rle_trans.
      * apply (chord_near c sS sk st Hwf).
        -- apply station_rad. exact HtS.
        -- apply station_rad. exact Htk.
        -- exact Hst.
      * assert (Eba : sk - sS = cloth_hstep c n).
        { rewrite <- Hstep. rewrite Rabs_minus_sym. symmetry.
          apply Rabs_right. apply Rle_ge. exact Hgap. }
        rewrite Eba. unfold cloth_tol. apply Rle_refl.
Qed.
Lemma ts_gap : forall n k, (n <> 0)%nat ->
  cloth_ts n (S k) - cloth_ts n k = / INR n.
Proof.
  intros n k Hn. unfold cloth_ts. rewrite S_INR. field. apply not_0_INR. exact Hn.
Qed.
Lemma curve_near : forall c n, cloth_wf c -> (2 <= n)%nat ->
  within_eps (curve_shape (cloth_eval c)) (poly_shape (cloth_lin_pts c n))
    (cloth_tol c n).
Proof.
  intros c n Hwf Hn p [t [Ht Hp]].
  destruct (param_slot n t Hn Ht) as [k [Hk Hbin]].
  set (tk := cloth_ts n k). set (tS := cloth_ts n (S k)).
  set (lam := (t - tk) / (tS - tk)).
  assert (Hden : 0 < tS - tk).
  { unfold tS, tk. rewrite ts_gap by lia.
    apply Rinv_0_lt_compat, lt_0_INR. lia. }
  assert (Hlo : 0 <= t - tk).
  { destruct Hbin as [Hb _]. apply (Rplus_le_compat_r (- tk)) in Hb.
    rewrite Rplus_opp_r in Hb. unfold Rminus. exact Hb. }
  assert (Hhi : t - tk <= tS - tk).
  { destruct Hbin as [_ Hb]. apply (Rplus_le_compat_r (- tk)) in Hb.
    unfold Rminus. exact Hb. }
  assert (Hlam : 0 <= lam <= 1).
  { unfold lam. split.
    - apply Rmult_le_pos; [exact Hlo|].
      apply Rlt_le, Rinv_0_lt_compat. exact Hden.
    - apply Rmult_le_reg_r with (tS - tk); [exact Hden|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l.
      + rewrite Rmult_1_r, Rmult_1_l. exact Hhi.
      + intro E. rewrite E in Hden. apply (Rlt_irrefl 0 Hden). }
  exists (seg_at (nth k (cloth_lin_pts c n) (cloth_eval c 0))
                 (nth (S k) (cloth_lin_pts c n) (cloth_eval c 0)) lam).
  split.
  - exists k, lam, (cloth_eval c 0). split; [|split].
    + rewrite lin_len. lia.
    + exact Hlam.
    + reflexivity.
  - rewrite Hp, !lin_nth by lia. unfold tk, tS, lam.
    apply sample_near; try assumption; lia.
Qed.
Lemma poly_near : forall c n, cloth_wf c -> (2 <= n)%nat ->
  within_eps (poly_shape (cloth_lin_pts c n)) (curve_shape (cloth_eval c))
    (cloth_tol c n).
Proof.
  intros c n Hwf Hn q [k [lam [d [Hk [Hlam Hq]]]]].
  assert (Hkn : (k < n)%nat).
  { rewrite lin_len in Hk. lia. }
  set (tk := cloth_ts n k). set (tS := cloth_ts n (S k)).
  set (t := tk + lam * (tS - tk)).
  assert (Hden : 0 < tS - tk).
  { unfold tS, tk. rewrite ts_gap by lia.
    apply Rinv_0_lt_compat, lt_0_INR. lia. }
  assert (Hbin : tk <= t <= tS).
  { unfold t. split.
    - apply Rle_trans with (tk + 0).
      + rewrite Rplus_0_r. apply Rle_refl.
      + apply Rplus_le_compat_l. apply Rmult_le_pos.
        * exact (proj1 Hlam).
        * apply Rlt_le. exact Hden.
    - apply Rle_trans with (tk + 1 * (tS - tk)).
      + apply Rplus_le_compat_l. apply Rmult_le_compat_r.
        * apply Rlt_le. exact Hden.
        * exact (proj2 Hlam).
      + rewrite Rmult_1_l. unfold Rminus. rewrite Rplus_comm.
        rewrite Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r.
        apply Rle_refl. }
  assert (Ht : 0 <= t <= 1).
  { assert (Htk : 0 <= tk <= 1).
    { unfold tk. apply ts_01; lia. }
    assert (HtS : 0 <= tS <= 1).
    { unfold tS. apply ts_01; lia. }
    split.
    - apply Rle_trans with tk; [exact (proj1 Htk)|exact (proj1 Hbin)].
    - apply Rle_trans with tS; [exact (proj2 Hbin)|exact (proj2 HtS)]. }
  assert (Elam : (t - tk) / (tS - tk) = lam).
  { unfold t.
    assert (Ecut : tk + lam * (tS - tk) - tk = lam * (tS - tk)).
    { unfold Rminus. rewrite Rplus_comm. rewrite <- Rplus_assoc.
      rewrite Rplus_opp_l. rewrite Rplus_0_l. reflexivity. }
    rewrite Ecut. unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_r.
    - rewrite Rmult_1_r. reflexivity.
    - intro E. rewrite E in Hden. apply (Rlt_irrefl 0 Hden). }
  exists (cloth_eval c t). split.
  - exists t. split; [exact Ht|reflexivity].
  - rewrite Hq.
    rewrite (@nth_indep Point (cloth_lin_pts c n) k d (cloth_eval c 0))
      by (rewrite lin_len; lia).
    rewrite (@nth_indep Point (cloth_lin_pts c n) (S k) d (cloth_eval c 0))
      by (rewrite lin_len; lia).
    rewrite !lin_nth by lia. rewrite <- Elam. rewrite dist_sym.
    unfold tk, tS. apply sample_near; try assumption; lia.
Qed.
Lemma cloth_hausdorff : forall c n, cloth_wf c -> (2 <= n)%nat ->
  hausdorff_le (curve_shape (cloth_eval c)) (poly_shape (cloth_lin_pts c n))
    (cloth_tol c n).
Proof.
  intros c n Hwf Hn. split; [apply curve_near|apply poly_near]; assumption.
Qed.
(* WITNESS {"claimId":"0007-clothoid-linearize","topic":"curves","lemma":"clothoid_linearizes","title":"Uniform clothoid densifier inhabits Linearizes at ts k = k/n, tol kappa_max*h^2/8, h=|ed-sd|/n; kappa_max = max(|kappa(sd)|,|kappa(ed)|) via cloth_signed_is_sigma; reverse swaps sd and ed","file":"theories/ClothoidLinearizeContract.v","witness":"clothoid_linearizes","board":"ADR-0007"} *)
Theorem clothoid_linearizes : forall c n, cloth_wf c -> (2 <= n)%nat ->
  Linearizes (cloth_eval c) (cloth_eval (cloth_rev c))
    (cloth_lin_pts c n) (cloth_ts n) n (cloth_tol c n).
Proof.
  intros c n Hwf Hn. apply Build_Linearizes.
  - exact Hn.
  - apply lin_len.
  - split.
    + unfold cloth_ts, Rdiv. rewrite INR_0, Rmult_0_l. reflexivity.
    + unfold cloth_ts. field. apply not_0_INR. lia.
  - intros i j Hij. destruct Hij as [Hij Hjn].
    unfold cloth_ts, Rdiv.
    apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat, lt_0_INR; lia|].
    apply lt_INR. exact Hij.
  - intros k Hk. apply lin_nth. exact Hk.
  - apply cloth_hausdorff; assumption.
  - intros t. apply cloth_eval_rev.
  - intros k Hk. rewrite (lin_rev_nth c n k Hk), cloth_eval_rev.
    replace (1 - (1 - cloth_ts n (n - k)%nat))
      with (cloth_ts n (n - k)%nat).
    + reflexivity.
    + unfold Rminus. rewrite Ropp_plus_distr, Ropp_involutive.
      rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
      reflexivity.
Qed.

Print Assumptions ts_01.
Print Assumptions lin_len.
Print Assumptions lin_nth.
Print Assumptions cloth_s_affine.
Print Assumptions cloth_s_seg.
Print Assumptions station_rad.
Print Assumptions seg_swap.
Print Assumptions cloth_P_rev.
Print Assumptions cloth_s_rev.
Print Assumptions cloth_eval_rev.
Print Assumptions lin_rev_nth.
Print Assumptions param_slot.
Print Assumptions sample_near.
Print Assumptions ts_gap.
Print Assumptions curve_near.
Print Assumptions poly_near.
Print Assumptions cloth_hausdorff.
Print Assumptions clothoid_linearizes.
