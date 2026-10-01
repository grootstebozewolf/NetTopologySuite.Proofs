(* ============================================================================
   NetTopologySuite.Proofs.ClothoidLengthAbs
   ----------------------------------------------------------------------------
   Metric length of a host clothoid. The station parameter is arc length,
   so the t-speed of cloth_eval on [0,1] is the constant |ed − sd|.
   lip_speed_is_curve_length turns that constant into is_curve_length.

   claimId: 0007-clothoid-length
   witness: clothoid_length_abs
   3-axiom host. No Admitted / Axiom / Parameter. No RiemannInt.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import Distance LipInt SheetHenClothoidCore
  ClothoidTangent MetricSpeed CurveLength.
Local Open Scope R_scope.

Lemma cloth_sigma_sq : forall c, cloth_sigma c * cloth_sigma c = 1.
Proof.
  intro c. unfold cloth_sigma.
  destruct (Rle_dec 0 (cloth_cross c)); ring.
Qed.

Lemma cloth_frame_abs : forall c,
  cloth_h2 c <> 0 ->
  Rabs (cloth_cos0 c) <= 1 /\ Rabs (cloth_sin0 c) <= 1.
Proof.
  intros c Hh.
  assert (Hs := cloth_frame_sumsq c Hh).
  assert (one : forall x y, x * x + y * y = 1 -> -1 <= x <= 1).
  { intros x y H. nra. }
  split; apply Rabs_le.
  - apply (one (cloth_cos0 c) (cloth_sin0 c) Hs).
  - apply (one (cloth_sin0 c) (cloth_cos0 c)). rewrite Rplus_comm. exact Hs.
Qed.

Section ClothoidSpeed.
Variable c : ClothoidEgg.
Hypothesis Hwf : cloth_wf c.

Let d : R := cloth_ed c - cloth_sd c.
Let rad : R := Rmax (Rabs (cloth_sd c)) (Rabs (cloth_ed c)).
Let Kphi : R := cloth_phi_K c rad.
Let Lv : R := 2 * d * d * Kphi.
Let nvx (t : R) : R := d * cloth_vx c (cloth_s c t).
Let nvy (t : R) : R := d * cloth_vy c (cloth_s c t).
Let ngx (t : R) : R := px (cloth_eval c t).
Let ngy (t : R) : R := py (cloth_eval c t).

Lemma cloth_len_A : 0 < cloth_A c.
Proof. destruct Hwf as [HA _]. exact HA. Qed.

Lemma cloth_len_h2 : cloth_h2 c <> 0.
Proof. destruct Hwf as [_ [Hh _]]. exact Hh. Qed.

Lemma cloth_len_rad_nn : 0 <= rad.
Proof.
  unfold rad. apply Rle_trans with (Rabs (cloth_sd c));
    [apply Rabs_pos | apply Rmax_l].
Qed.

Lemma cloth_len_Lv_nn : 0 <= Lv.
Proof.
  unfold Lv.
  replace (2 * d * d * Kphi) with (2 * (d * d) * Kphi) by ring.
  apply Rmult_le_pos; [apply Rmult_le_pos; [lra | apply Rle_0_sqr]|].
  unfold Kphi. apply cloth_phi_K_nonneg.
Qed.

Lemma cloth_len_s_in_rad : forall t, 0 <= t <= 1 -> - rad <= cloth_s c t <= rad.
Proof.
  intros t [Ht0 Ht1].
  unfold cloth_s.
  assert (Es : cloth_sd c + t * (cloth_ed c - cloth_sd c)
               = (1 - t) * cloth_sd c + t * cloth_ed c) by ring.
  rewrite Es.
  set (s := (1 - t) * cloth_sd c + t * cloth_ed c).
  assert (H1t : 0 <= 1 - t) by lra.
  assert (Hs : Rabs s <= rad).
  { unfold s. eapply Rle_trans; [apply Rabs_triang |].
    rewrite !Rabs_mult.
    rewrite (Rabs_pos_eq (1 - t) H1t), (Rabs_pos_eq t Ht0).
    apply Rle_trans with ((1 - t) * rad + t * rad).
    - apply Rplus_le_compat.
      + apply Rmult_le_compat_l; [exact H1t | unfold rad; apply Rmax_l].
      + apply Rmult_le_compat_l; [exact Ht0 | unfold rad; apply Rmax_r].
    - right. ring. }
  split.
  - apply Rle_trans with (- Rabs s); [| apply Ropp_le_cancel; rewrite Ropp_involutive;
      rewrite <- (Rabs_Ropp s); apply Rle_abs].
    apply Ropp_le_contravar. exact Hs.
  - apply Rle_trans with (Rabs s); [apply Rle_abs | exact Hs].
Qed.

Lemma cloth_len_psi_lip : forall x y,
  - rad <= x <= rad -> - rad <= y <= rad ->
  Rabs (cloth_psi c x - cloth_psi c y) <= Kphi * Rabs (x - y).
Proof.
  intros x y Hx Hy.
  set (AA := cloth_A c * cloth_A c).
  assert (HA0 : 0 < cloth_A c) by apply cloth_len_A.
  assert (Hpos : 0 < AA) by (unfold AA; nra).
  assert (HA : cloth_A c <> 0) by lra.
  assert (Hinv : 0 < / (2 * AA)) by (apply Rinv_0_lt_compat; lra).
  unfold cloth_psi, Kphi, cloth_phi_K, Rdiv.
  assert (E :
    (cloth_sigma c * x * x) * / (2 * cloth_A c * cloth_A c) -
    (cloth_sigma c * y * y) * / (2 * cloth_A c * cloth_A c)
    = cloth_sigma c * ((x - y) * (x + y)) * / (2 * AA)).
  { unfold AA. field. exact HA. }
  rewrite E. clear E.
  rewrite !Rabs_mult. rewrite cloth_sigma_abs.
  assert (Habs : Rabs (/ (2 * AA)) = / (2 * AA)).
  { apply Rabs_pos_eq. apply Rlt_le. exact Hinv. }
  rewrite Habs. clear Habs.
  assert (Hxy : Rabs (x + y) <= 2 * rad).
  { eapply Rle_trans; [apply Rabs_triang |].
    assert (Hxabs : Rabs x <= rad) by (apply Rabs_le; exact Hx).
    assert (Hyabs : Rabs y <= rad) by (apply Rabs_le; exact Hy).
    apply Rle_trans with (rad + rad); [apply Rplus_le_compat; assumption |].
    right. ring. }
  rewrite (Rabs_pos_eq rad cloth_len_rad_nn).
  apply Rle_trans with ((1 * (Rabs (x - y) * (2 * rad))) * / (2 * AA)).
  - apply Rmult_le_compat_r; [apply Rlt_le; exact Hinv |].
    apply Rmult_le_compat_l; [lra |].
    apply Rmult_le_compat_l; [apply Rabs_pos | exact Hxy].
  - unfold AA. right. field. exact HA.
Qed.

Lemma cloth_len_comb_lip : forall a0 b0 s1 s2,
  Rabs a0 <= 1 -> Rabs b0 <= 1 ->
  - rad <= s1 <= rad -> - rad <= s2 <= rad ->
  Rabs (a0 * (cos (cloth_psi c s1) - cos (cloth_psi c s2))
      + b0 * (sin (cloth_psi c s1) - sin (cloth_psi c s2)))
    <= 2 * Kphi * Rabs (s1 - s2).
Proof.
  intros a0 b0 s1 s2 Ha Hb Hs1 Hs2.
  eapply Rle_trans; [apply Rabs_triang |].
  rewrite !Rabs_mult.
  assert (Hc : Rabs (cos (cloth_psi c s1) - cos (cloth_psi c s2))
               <= Kphi * Rabs (s1 - s2)).
  { eapply Rle_trans; [apply cos_lip | apply cloth_len_psi_lip; assumption]. }
  assert (Hs : Rabs (sin (cloth_psi c s1) - sin (cloth_psi c s2))
               <= Kphi * Rabs (s1 - s2)).
  { eapply Rle_trans; [apply sin_lip | apply cloth_len_psi_lip; assumption]. }
  apply Rle_trans with
    (1 * (Kphi * Rabs (s1 - s2)) + 1 * (Kphi * Rabs (s1 - s2))).
  - apply Rplus_le_compat; apply Rmult_le_compat; try apply Rabs_pos; assumption.
  - right. ring.
Qed.

Lemma cloth_len_scaled_lip : forall (f : R -> R),
  (forall s1 s2, - rad <= s1 <= rad -> - rad <= s2 <= rad ->
     Rabs (f s1 - f s2) <= 2 * Kphi * Rabs (s1 - s2)) ->
  forall x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
  Rabs (d * f (cloth_s c x) - d * f (cloth_s c y)) <= Lv * Rabs (x - y).
Proof.
  intros f Hf x y Hx Hy.
  replace (d * f (cloth_s c x) - d * f (cloth_s c y))
    with (d * (f (cloth_s c x) - f (cloth_s c y))) by ring.
  rewrite Rabs_mult.
  apply Rle_trans with (Rabs d * (2 * Kphi * Rabs (cloth_s c x - cloth_s c y))).
  - apply Rmult_le_compat_l; [apply Rabs_pos |].
    apply Hf; apply cloth_len_s_in_rad; assumption.
  - assert (Es : cloth_s c x - cloth_s c y = d * (x - y)).
    { unfold cloth_s, d. ring. }
    rewrite Es, Rabs_mult.
    unfold Lv.
    replace (Rabs d * (2 * Kphi * (Rabs d * Rabs (x - y))))
      with (2 * (Rabs d * Rabs d) * Kphi * Rabs (x - y)) by ring.
    replace (Rabs d * Rabs d) with (d * d).
    + right. ring.
    + destruct (Rle_dec 0 d) as [Hd|Hd].
      * rewrite (Rabs_right d (Rle_ge _ _ Hd)). reflexivity.
      * apply Rnot_le_lt in Hd. rewrite (Rabs_left d Hd). ring.
Qed.

Lemma cloth_len_nvx_lip : forall x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
  Rabs (nvx x - nvx y) <= Lv * Rabs (x - y).
Proof.
  intros x y Hx Hy. unfold nvx. apply cloth_len_scaled_lip; [| exact Hx | exact Hy].
  intros s1 s2 Hs1 Hs2.
  replace (cloth_vx c s1 - cloth_vx c s2) with
    (cloth_cos0 c * (cos (cloth_psi c s1) - cos (cloth_psi c s2))
     + (- cloth_sin0 c) * (sin (cloth_psi c s1) - sin (cloth_psi c s2)))
    by (unfold cloth_vx; ring).
  apply cloth_len_comb_lip; try assumption.
  - exact (proj1 (cloth_frame_abs c cloth_len_h2)).
  - rewrite Rabs_Ropp. exact (proj2 (cloth_frame_abs c cloth_len_h2)).
Qed.

Lemma cloth_len_nvy_lip : forall x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
  Rabs (nvy x - nvy y) <= Lv * Rabs (x - y).
Proof.
  intros x y Hx Hy. unfold nvy. apply cloth_len_scaled_lip; [| exact Hx | exact Hy].
  intros s1 s2 Hs1 Hs2.
  replace (cloth_vy c s1 - cloth_vy c s2) with
    (cloth_sin0 c * (cos (cloth_psi c s1) - cos (cloth_psi c s2))
     + cloth_cos0 c * (sin (cloth_psi c s1) - sin (cloth_psi c s2)))
    by (unfold cloth_vy; ring).
  apply cloth_len_comb_lip; try assumption; apply (cloth_frame_abs c cloth_len_h2).
Qed.

Lemma cloth_len_ngx_deriv : forall t, 0 <= t <= 1 ->
  derivable_pt_lim ngx t (nvx t).
Proof. intros t _. unfold ngx, nvx. apply cloth_eval_px_deriv. Qed.

Lemma cloth_len_ngy_deriv : forall t, 0 <= t <= 1 ->
  derivable_pt_lim ngy t (nvy t).
Proof. intros t _. unfold ngy, nvy. apply cloth_eval_py_deriv. Qed.

Lemma cloth_len_speed_const : forall t, speed nvx nvy t = Rabs d.
Proof.
  intro t. unfold speed.
  assert (E : nvx t * nvx t + nvy t * nvy t = d * d).
  { unfold nvx, nvy.
    pose proof (cloth_eval_speed_sq c t cloth_len_h2) as Hq.
    cbv zeta in Hq. unfold d. exact Hq. }
  rewrite E.
  destruct (Rle_dec 0 d) as [Hd|Hd].
  - rewrite (Rabs_right d (Rle_ge _ _ Hd)). apply sqrt_square. exact Hd.
  - apply Rnot_le_lt in Hd. rewrite (Rabs_left d Hd).
    replace (d * d) with ((- d) * (- d)) by ring.
    apply sqrt_square. lra.
Qed.

Lemma cloth_len_speed_lip : forall x y,
  Rmin 0 1 <= x <= Rmax 0 1 -> Rmin 0 1 <= y <= Rmax 0 1 ->
  Rabs (speed nvx nvy x - speed nvx nvy y) <= (Lv + Lv) * Rabs (x - y).
Proof.
  intros x y _ _. rewrite !cloth_len_speed_const.
  rewrite Rminus_diag, Rabs_R0.
  apply Rmult_le_pos; [apply Rplus_le_le_0_compat; exact cloth_len_Lv_nn | apply Rabs_pos].
Qed.

Lemma point_eq_len : forall p q : Point, px p = px q -> py p = py q -> p = q.
Proof. intros [] [] Hx Hy. cbn in Hx, Hy. subst. reflexivity. Qed.

(* WITNESS {"claimId":"0007-clothoid-length","topic":"curves","lemma":"clothoid_length_abs","title":"Host clothoid length on [0,1] is |ed-sd|: unit station speed, t-speed the constant |ed-sd|, identified by lip_speed_is_curve_length","file":"theories/ClothoidLengthAbs.v","witness":"clothoid_length_abs","board":"ADR-0007"} *)
Theorem clothoid_length_abs :
  is_curve_length (cloth_eval c) 0 1 (Rabs d).
Proof.
  set (SF := speedF nvx nvy 0 1 Lv Lv cloth_len_Lv_nn cloth_len_Lv_nn
               cloth_len_nvx_lip cloth_len_nvy_lip).
  destruct (lip_speed_is_curve_length ngx ngy nvx nvy 0 1 Lv Lv
              Rle_0_1 cloth_len_Lv_nn cloth_len_Lv_nn
              cloth_len_nvx_lip cloth_len_nvy_lip
              cloth_len_ngx_deriv cloth_len_ngy_deriv) as [Hint Hlen].
  assert (Hsum : 0 <= Lv + Lv).
  { apply Rplus_le_le_0_compat; exact cloth_len_Lv_nn. }
  assert (Hdiff : SF 1 - SF 0 = Rabs d).
  { unfold SF. rewrite Hint.
    transitivity (int_seg (speed nvx nvy) (Lv + Lv) 0 1 Hsum cloth_len_speed_lip).
    - apply int_seg_pi.
    - transitivity (int_seg (fun _ : R => Rabs d) (Lv + Lv) 0 1 Hsum
                     (const_lip (Rabs d) (Lv + Lv) 0 1 Hsum)).
      + apply int_seg_ext. intros x _. apply cloth_len_speed_const.
      + rewrite (int_seg_const (Rabs d) (Lv + Lv) 0 1 Hsum
                  (const_lip (Rabs d) (Lv + Lv) 0 1 Hsum) Rle_0_1).
        ring. }
  apply is_curve_length_ext with (g1 := gamma ngx ngy).
  - intro t. apply point_eq_len; reflexivity.
  - rewrite <- Hdiff. unfold SF. exact Hlen.
Qed.

End ClothoidSpeed.

Print Assumptions cloth_sigma_sq.
Print Assumptions cloth_frame_abs.
Print Assumptions cloth_len_A.
Print Assumptions cloth_len_h2.
Print Assumptions cloth_len_rad_nn.
Print Assumptions cloth_len_Lv_nn.
Print Assumptions cloth_len_s_in_rad.
Print Assumptions cloth_len_psi_lip.
Print Assumptions cloth_len_comb_lip.
Print Assumptions cloth_len_scaled_lip.
Print Assumptions cloth_len_nvx_lip.
Print Assumptions cloth_len_nvy_lip.
Print Assumptions cloth_len_ngx_deriv.
Print Assumptions cloth_len_ngy_deriv.
Print Assumptions cloth_len_speed_const.
Print Assumptions cloth_len_speed_lip.
Print Assumptions point_eq_len.
Print Assumptions clothoid_length_abs.
