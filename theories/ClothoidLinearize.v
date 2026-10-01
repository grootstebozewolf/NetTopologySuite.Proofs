(* ============================================================================
   NetTopologySuite.Proofs.ClothoidLinearize
   ----------------------------------------------------------------------------
   Uniform arc-length samples of a host clothoid inhabit Linearizes.
   Both Hausdorff directions use the same parameter chord, with
   tol = kappa_max * h^2 / 8, h = |ed-sd|/n, and
   kappa_max = max(|kappa(sd)|, |kappa(ed)|) via cloth_signed_is_sigma.
   n >= 2. Reverse symmetry swaps sd and ed.
   claimId: 0007-clothoid-linearize. witness: clothoid_linearizes.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia List PeanoNat ZArith.
From NTS.Proofs Require Import Distance LipInt SheetHenClothoidCore Atan2
  ClothoidFresnelInc LinearizeContract ArcLength ArcRectifiable SignedCurvature.
Import ListNotations.
Local Open Scope R_scope.
Definition cloth_rev (c : ClothoidEgg) : ClothoidEgg :=
  mk_cloth (cloth_place c) (cloth_A c) (cloth_ed c) (cloth_sd c)
    (cloth_m0 c) (cloth_m1 c).
Definition cloth_rad (c : ClothoidEgg) : R :=
  Rmax (Rabs (cloth_sd c)) (Rabs (cloth_ed c)).
Definition cloth_kappa_max (c : ClothoidEgg) : R :=
  Rmax (Rabs (cloth_signed_curv c (cloth_sd c)))
       (Rabs (cloth_signed_curv c (cloth_ed c))).
Definition cloth_hstep (c : ClothoidEgg) (n : nat) : R :=
  Rabs (cloth_ed c - cloth_sd c) / INR n.
Definition cloth_tol (c : ClothoidEgg) (n : nat) : R :=
  cloth_kappa_max c * cloth_hstep c n * cloth_hstep c n / 8.
Definition cloth_ts (n k : nat) : R := INR k / INR n.
Definition cloth_lin_pts (c : ClothoidEgg) (n : nat) : list Point :=
  map (fun k => cloth_eval c (cloth_ts n k)) (seq 0 (S n)).
Lemma cloth_kappa_max_nn : forall c, 0 <= cloth_kappa_max c.
Proof.
  intro c. unfold cloth_kappa_max.
  apply Rle_trans with (Rabs (cloth_signed_curv c (cloth_sd c)));
    [apply Rabs_pos | apply Rmax_l].
Qed.
Lemma cloth_rad_nn : forall c, 0 <= cloth_rad c.
Proof.
  intro c. unfold cloth_rad.
  apply Rle_trans with (Rabs (cloth_sd c)); [apply Rabs_pos | apply Rmax_l].
Qed.
Lemma Rmax_scale_pos : forall x y k, 0 <= k ->
  Rmax (x * k) (y * k) = Rmax x y * k.
Proof.
  intros x y k Hk.
  destruct (Rle_dec x y) as [Hxy|Hxy].
  - rewrite (Rmax_right x y Hxy).
    rewrite (Rmax_right (x * k) (y * k)); [reflexivity|].
    apply Rmult_le_compat_r; assumption.
  - apply Rnot_le_lt in Hxy. assert (Hyx : y <= x) by lra.
    rewrite (Rmax_left x y Hyx).
    rewrite (Rmax_left (x * k) (y * k)); [reflexivity|].
    apply Rmult_le_compat_r; [exact Hk | exact Hyx].
Qed.
Lemma kappa_abs_station : forall c s, cloth_wf c ->
  Rabs (cloth_signed_curv c s) = Rabs s / (cloth_A c * cloth_A c).
Proof.
  intros c s Hwf.
  assert (HA : 0 < cloth_A c) by (apply rho_A; exact Hwf).
  assert (Hden : 0 < cloth_A c * cloth_A c) by nra.
  rewrite cloth_signed_is_sigma. unfold Rdiv.
  rewrite Rabs_mult, (Rabs_pos_eq (/ (cloth_A c * cloth_A c)))
    by (apply Rlt_le, Rinv_0_lt_compat; exact Hden).
  rewrite Rabs_mult, cloth_sigma_abs, Rmult_1_l. reflexivity.
Qed.
Lemma kappa_max_eq : forall c, cloth_wf c ->
  cloth_kappa_max c = cloth_rad c / (cloth_A c * cloth_A c).
Proof.
  intros c Hwf.
  assert (HA : 0 < cloth_A c) by (apply rho_A; exact Hwf).
  assert (Hden : 0 < cloth_A c * cloth_A c) by nra.
  unfold cloth_kappa_max, cloth_rad, Rdiv.
  rewrite !kappa_abs_station by exact Hwf. unfold Rdiv.
  rewrite Rmax_scale_pos by (apply Rlt_le, Rinv_0_lt_compat; exact Hden).
  reflexivity.
Qed.
Lemma sin_abs_le : forall x, Rabs (sin x) <= Rabs x.
Proof.
  intros x. destruct (Rle_dec 0 x) as [Hx|Hx].
  - rewrite (Rabs_right x) by lra. apply Rabs_sin_le. exact Hx.
  - apply Rnot_le_lt in Hx. rewrite (Rabs_left x Hx).
    rewrite <- (Rabs_Ropp (sin x)), <- sin_neg.
    apply Rabs_sin_le. lra.
Qed.
Lemma dist_diff : forall x1 y1 x2 y2,
  dist (mkPoint x1 y1) (mkPoint x2 y2) =
  dist (mkPoint (x1 - x2) (y1 - y2)) (mkPoint 0 0).
Proof.
  intros. unfold dist, dist_sq. cbn.
  replace (x1 - x2 - 0) with (x1 - x2) by ring.
  replace (y1 - y2 - 0) with (y1 - y2) by ring. reflexivity.
Qed.
Lemma dist0 : forall x y,
  dist (mkPoint x y) (mkPoint 0 0) = sqrt (x * x + y * y).
Proof.
  intros. unfold dist, dist_sq. cbn.
  replace (x - 0) with x by ring. replace (y - 0) with y by ring. reflexivity.
Qed.
Lemma abs_le_dist0 : forall x y, Rabs x <= dist (mkPoint x y) (mkPoint 0 0).
Proof.
  intros x y. rewrite dist0. rewrite <- (sqrt_Rsqr_abs x). unfold Rsqr.
  apply sqrt_le_1_alt. pose proof (Rle_0_sqr y) as Hy. nra.
Qed.
Lemma dist0_scale : forall c x y,
  dist (mkPoint (c * x) (c * y)) (mkPoint 0 0) =
  Rabs c * dist (mkPoint x y) (mkPoint 0 0).
Proof.
  intros c x y. rewrite !dist0.
  replace (c * x * (c * x) + c * y * (c * y))
    with (Rsqr (Rabs c) * (x * x + y * y)).
  - rewrite sqrt_mult.
    + rewrite sqrt_Rsqr_abs, Rabs_Rabsolu. reflexivity.
    + apply Rle_0_sqr.
    + apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  - rewrite <- (Rsqr_abs c). unfold Rsqr. ring.
Qed.
Lemma dist0_triangle : forall x1 y1 x2 y2,
  dist (mkPoint (x1 + x2) (y1 + y2)) (mkPoint 0 0) <=
  dist (mkPoint x1 y1) (mkPoint 0 0) + dist (mkPoint x2 y2) (mkPoint 0 0).
Proof.
  intros x1 y1 x2 y2.
  set (A := mkPoint x1 y1). set (B := mkPoint x2 y2).
  set (S := mkPoint (x1 + x2) (y1 + y2)). set (Z := mkPoint 0 0).
  apply Rle_trans with (dist S A + dist A Z).
  - apply dist_triangle.
  - replace (dist S A) with (dist B Z).
    + rewrite Rplus_comm. apply Rle_refl.
    + unfold dist, dist_sq, S, A, B, Z. cbn. f_equal. ring.
Qed.
Lemma heading_gap : forall a b,
  (cos a - cos b) * (cos a - cos b) + (sin a - sin b) * (sin a - sin b) =
  4 * sin ((a - b) / 2) * sin ((a - b) / 2).
Proof.
  intros a b.
  assert (Hs : (cos a - cos b) * (cos a - cos b) +
               (sin a - sin b) * (sin a - sin b) = 2 - 2 * cos (a - b)).
  { rewrite (cos_minus a b).
    pose proof (sin2_cos2 a) as Ha. pose proof (sin2_cos2 b) as Hb.
    unfold Rsqr in Ha, Hb. nra. }
  rewrite Hs. set (t := (a - b) / 2).
  replace (a - b) with (2 * t) by (unfold t; field).
  rewrite (cos_2a_sin t). ring.
Qed.
Lemma tangent_sep : forall c u v, cloth_h2 c <> 0 ->
  dist (mkPoint (cloth_vx c u) (cloth_vy c u))
       (mkPoint (cloth_vx c v) (cloth_vy c v))
    <= Rabs (cloth_psi c u - cloth_psi c v).
Proof.
  intros c u v Hh.
  rewrite (vx_heading c u Hh), (vy_heading c u Hh),
          (vx_heading c v Hh), (vy_heading c v Hh).
  set (a := cloth_heading c u). set (b := cloth_heading c v).
  assert (Hd : a - b = cloth_psi c u - cloth_psi c v)
    by (unfold a, b, cloth_heading; ring).
  unfold dist, dist_sq. cbn.
  set (t := (a - b) / 2).
  replace ((cos a - cos b) * (cos a - cos b) + (sin a - sin b) * (sin a - sin b))
    with (Rsqr (2 * sin t)).
  - rewrite sqrt_Rsqr_abs. rewrite Rabs_mult, (Rabs_right 2) by lra.
    apply Rle_trans with (2 * Rabs t).
    + apply Rmult_le_compat_l; [lra | apply sin_abs_le].
    + unfold t, Rdiv.
      rewrite Rabs_mult, (Rabs_pos_eq (/ 2))
        by (apply Rlt_le, Rinv_0_lt_compat; lra).
      rewrite Hd. lra.
  - rewrite heading_gap. unfold t, Rsqr. ring.
Qed.
Lemma dpsi_le_kappa : forall c u v, cloth_wf c ->
  Rabs u <= cloth_rad c -> Rabs v <= cloth_rad c ->
  Rabs (cloth_psi c u - cloth_psi c v) <=
    cloth_kappa_max c * Rabs (u - v).
Proof.
  intros c u v Hwf Hu Hv.
  eapply Rle_trans.
  - apply (psi_lip_ball c (cloth_rad c) u v); try assumption.
    + apply rho_A. exact Hwf.
    + apply cloth_rad_nn.
  - rewrite (kappa_max_eq c Hwf). unfold cloth_phi_K.
    rewrite (Rabs_right (cloth_rad c)) by (apply Rle_ge, cloth_rad_nn).
    right. reflexivity.
Qed.
Lemma win_in_rad : forall c a b x,
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  Rmin a b <= x <= Rmax a b -> Rabs x <= cloth_rad c.
Proof.
  intros c a b x Ha Hb Hx.
  eapply Rle_trans; [apply abs_seg; exact Hx|].
  apply Rmax_lub; assumption.
Qed.
Lemma vx_lip_win : forall c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (cloth_vx c x - cloth_vx c y) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hb x y Hx Hy.
  eapply Rle_trans.
  - apply (abs_le_dist0 (cloth_vx c x - cloth_vx c y)
                        (cloth_vy c x - cloth_vy c y)).
  - rewrite <- dist_diff. eapply Rle_trans.
    + apply tangent_sep. apply rho_h2. exact Hwf.
    + apply dpsi_le_kappa; try exact Hwf; apply win_in_rad with (a:=a) (b:=b);
        assumption.
Qed.
Lemma vy_lip_win : forall c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (cloth_vy c x - cloth_vy c y) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hb x y Hx Hy.
  eapply Rle_trans.
  - rewrite Rabs_minus_sym.
    apply (abs_le_dist0 (cloth_vy c y - cloth_vy c x)
                        (cloth_vx c y - cloth_vx c x)).
  - rewrite <- dist_diff.
    replace (dist (mkPoint (cloth_vy c y) (cloth_vx c y))
                  (mkPoint (cloth_vy c x) (cloth_vx c x)))
      with (dist (mkPoint (cloth_vx c x) (cloth_vy c x))
                 (mkPoint (cloth_vx c y) (cloth_vy c y))).
    + eapply Rle_trans.
      * apply tangent_sep. apply rho_h2. exact Hwf.
      * apply dpsi_le_kappa; try exact Hwf; apply win_in_rad with (a:=a) (b:=b);
          assumption.
    + unfold dist, dist_sq. cbn. f_equal. ring.
Qed.
Lemma trig_k_lip : forall (f : R -> R) c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  (forall x y, Rabs (f x - f y) <= Rabs (x - y)) ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (f (cloth_psi c x) - f (cloth_psi c y)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros f c a b Hwf Ha Hb Hlip x y Hx Hy.
  eapply Rle_trans; [apply Hlip|].
  apply dpsi_le_kappa; try exact Hwf; apply win_in_rad with (a:=a) (b:=b);
    assumption.
Qed.
Lemma cos_k_lip : forall c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (cos (cloth_psi c x) - cos (cloth_psi c y)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hb x y Hx Hy.
  apply (trig_k_lip cos c a b Hwf Ha Hb).
  - intros u v. apply cos_lip.
  - exact Hx.
  - exact Hy.
Qed.
Lemma sin_k_lip : forall c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (sin (cloth_psi c x) - sin (cloth_psi c y)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hb x y Hx Hy.
  apply (trig_k_lip sin c a b Hwf Ha Hb).
  - intros u v. apply sin_lip.
  - exact Hx.
  - exact Hy.
Qed.
Lemma frame_abs1 : forall z w, z * z + w * w = 1 -> Rabs z <= 1.
Proof.
  intros z w H.
  rewrite <- (Rabs_right 1) by lra. apply Rsqr_le_abs_0.
  unfold Rsqr. rewrite <- H.
  pose proof (Rle_0_sqr w) as Hw. unfold Rsqr in Hw. nra.
Qed.
Lemma coef_trig_lip : forall coef (f : R -> R) c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  Rabs coef <= 1 ->
  (forall x y, Rabs (f x - f y) <= Rabs (x - y)) ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (coef * f (cloth_psi c x) - coef * f (cloth_psi c y)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros coef f c a b Hwf Ha Hb Hc Hlip x y Hx Hy.
  replace (coef * f (cloth_psi c x) - coef * f (cloth_psi c y))
    with (coef * (f (cloth_psi c x) - f (cloth_psi c y))) by ring.
  rewrite Rabs_mult.
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [apply Rabs_pos|].
    apply (trig_k_lip f c a b Hwf Ha Hb Hlip x y Hx Hy).
  - assert (HK : 0 <= cloth_kappa_max c) by apply cloth_kappa_max_nn.
    apply Rle_trans with (1 * (cloth_kappa_max c * Rabs (x - y))).
    + apply Rmult_le_compat_r.
      * apply Rmult_le_pos; [exact HK | apply Rabs_pos].
      * exact Hc.
    + rewrite Rmult_1_l. apply Rle_refl.
Qed.
Lemma cos0_lip : forall c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (cloth_cos0 c * cos (cloth_psi c x) -
          cloth_cos0 c * cos (cloth_psi c y)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hb x y Hx Hy.
  apply (coef_trig_lip (cloth_cos0 c) cos c a b Hwf Ha Hb).
  - apply frame_abs1 with (w := cloth_sin0 c).
    apply cloth_frame_sumsq. apply rho_h2. exact Hwf.
  - intros u v. apply cos_lip.
  - exact Hx.
  - exact Hy.
Qed.
Lemma nsin0_lip : forall c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs ((- cloth_sin0 c) * sin (cloth_psi c x) -
          (- cloth_sin0 c) * sin (cloth_psi c y)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hb x y Hx Hy.
  apply (coef_trig_lip (- cloth_sin0 c) sin c a b Hwf Ha Hb).
  - rewrite Rabs_Ropp. apply frame_abs1 with (w := cloth_cos0 c).
    pose proof (cloth_frame_sumsq c (rho_h2 c Hwf)) as H. nra.
  - intros u v. apply sin_lip.
  - exact Hx.
  - exact Hy.
Qed.
Lemma vx_sum_lip : forall c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs ((cloth_cos0 c * cos (cloth_psi c x) +
           (- cloth_sin0 c) * sin (cloth_psi c x)) -
          (cloth_cos0 c * cos (cloth_psi c y) +
           (- cloth_sin0 c) * sin (cloth_psi c y))) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hb x y Hx Hy.
  replace ((cloth_cos0 c * cos (cloth_psi c x) +
            (- cloth_sin0 c) * sin (cloth_psi c x)) -
           (cloth_cos0 c * cos (cloth_psi c y) +
            (- cloth_sin0 c) * sin (cloth_psi c y)))
    with (cloth_vx c x - cloth_vx c y) by (unfold cloth_vx; ring).
  apply (vx_lip_win c a b Hwf Ha Hb x y Hx Hy).
Qed.
Lemma vy_sum_lip : forall c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs ((cloth_sin0 c * cos (cloth_psi c x) +
           cloth_cos0 c * sin (cloth_psi c x)) -
          (cloth_sin0 c * cos (cloth_psi c y) +
           cloth_cos0 c * sin (cloth_psi c y))) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hb x y Hx Hy.
  replace ((cloth_sin0 c * cos (cloth_psi c x) +
            cloth_cos0 c * sin (cloth_psi c x)) -
           (cloth_sin0 c * cos (cloth_psi c y) +
            cloth_cos0 c * sin (cloth_psi c y)))
    with (cloth_vy c x - cloth_vy c y) by (unfold cloth_vy; ring).
  apply (vy_lip_win c a b Hwf Ha Hb x y Hx Hy).
Qed.
Lemma sin0_lip : forall c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (cloth_sin0 c * sin (cloth_psi c x) -
          cloth_sin0 c * sin (cloth_psi c y)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hb x y Hx Hy.
  apply (coef_trig_lip (cloth_sin0 c) sin c a b Hwf Ha Hb).
  - apply frame_abs1 with (w := cloth_cos0 c).
    pose proof (cloth_frame_sumsq c (rho_h2 c Hwf)) as H. nra.
  - intros u v. apply sin_lip.
  - exact Hx.
  - exact Hy.
Qed.
Lemma px_delta : forall c a b (Hwf : cloth_wf c)
  (Ha : Rabs a <= cloth_rad c) (Hb : Rabs b <= cloth_rad c),
  a <= b ->
  cloth_Px c b - cloth_Px c a =
  int_seg (cloth_vx c) (cloth_kappa_max c) a b
    (cloth_kappa_max_nn c) (vx_lip_win c a b Hwf Ha Hb).
Proof.
  intros c a b Hwf Ha Hb Hab.
  set (K := cloth_kappa_max c).
  unfold cloth_Px.
  replace (px (aff_loc (cloth_place c)) +
           cloth_cos0 c * cloth_Icos c b - cloth_sin0 c * cloth_Isin c b -
          (px (aff_loc (cloth_place c)) +
           cloth_cos0 c * cloth_Icos c a - cloth_sin0 c * cloth_Isin c a))
    with (cloth_cos0 c * (cloth_Icos c b - cloth_Icos c a) -
          cloth_sin0 c * (cloth_Isin c b - cloth_Isin c a)) by ring.
  rewrite (icos_ordered c a b Hwf Hab).
  rewrite (isin_ordered c a b Hwf Hab).
  rewrite (int_seg_L (fun u => cos (cloth_psi c u)) (rho_L c a b) K a b
             (rho_L_nn c a b) (cloth_kappa_max_nn c)
             (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
             (cos_k_lip c a b Hwf Ha Hb)).
  rewrite (int_seg_L (fun u => sin (cloth_psi c u)) (rho_L c a b) K a b
             (rho_L_nn c a b) (cloth_kappa_max_nn c)
             (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
             (sin_k_lip c a b Hwf Ha Hb)).
  set (Ic := int_seg (fun u => cos (cloth_psi c u)) K a b
               (cloth_kappa_max_nn c) (cos_k_lip c a b Hwf Ha Hb)).
  set (Is_ := int_seg (fun u => sin (cloth_psi c u)) K a b
               (cloth_kappa_max_nn c) (sin_k_lip c a b Hwf Ha Hb)).
  replace (cloth_cos0 c * Ic - cloth_sin0 c * Is_)
    with (cloth_cos0 c * Ic + (- cloth_sin0 c) * Is_) by ring.
  unfold Ic, Is_.
  rewrite <- (int_seg_scal (fun u => cos (cloth_psi c u)) (cloth_cos0 c)
               K K a b (cloth_kappa_max_nn c) (cloth_kappa_max_nn c)
               (cos_k_lip c a b Hwf Ha Hb) (cos0_lip c a b Hwf Ha Hb)).
  rewrite <- (int_seg_scal (fun u => sin (cloth_psi c u)) (- cloth_sin0 c)
               K K a b (cloth_kappa_max_nn c) (cloth_kappa_max_nn c)
               (sin_k_lip c a b Hwf Ha Hb) (nsin0_lip c a b Hwf Ha Hb)).
  rewrite <- (int_seg_plus
               (fun u => cloth_cos0 c * cos (cloth_psi c u))
               (fun u => (- cloth_sin0 c) * sin (cloth_psi c u))
               K K K a b
               (cloth_kappa_max_nn c) (cos0_lip c a b Hwf Ha Hb)
               (cloth_kappa_max_nn c) (nsin0_lip c a b Hwf Ha Hb)
               (cloth_kappa_max_nn c) (vx_sum_lip c a b Hwf Ha Hb)).
  apply int_seg_ext. intros u _. unfold cloth_vx. ring.
Qed.
Lemma sin0_cos_lip : forall c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (cloth_sin0 c * cos (cloth_psi c x) -
          cloth_sin0 c * cos (cloth_psi c y)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hb x y Hx Hy.
  apply (coef_trig_lip (cloth_sin0 c) cos c a b Hwf Ha Hb).
  - apply frame_abs1 with (w := cloth_cos0 c).
    pose proof (cloth_frame_sumsq c (rho_h2 c Hwf)) as H. nra.
  - intros u v. apply cos_lip.
  - exact Hx.
  - exact Hy.
Qed.
Lemma cos0_sin_lip : forall c a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (cloth_cos0 c * sin (cloth_psi c x) -
          cloth_cos0 c * sin (cloth_psi c y)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hb x y Hx Hy.
  apply (coef_trig_lip (cloth_cos0 c) sin c a b Hwf Ha Hb).
  - apply frame_abs1 with (w := cloth_sin0 c).
    apply cloth_frame_sumsq. apply rho_h2. exact Hwf.
  - intros u v. apply sin_lip.
  - exact Hx.
  - exact Hy.
Qed.
Lemma py_delta : forall c a b (Hwf : cloth_wf c)
  (Ha : Rabs a <= cloth_rad c) (Hb : Rabs b <= cloth_rad c),
  a <= b ->
  cloth_Py c b - cloth_Py c a =
  int_seg (cloth_vy c) (cloth_kappa_max c) a b
    (cloth_kappa_max_nn c) (vy_lip_win c a b Hwf Ha Hb).
Proof.
  intros c a b Hwf Ha Hb Hab.
  set (K := cloth_kappa_max c).
  unfold cloth_Py.
  replace (py (aff_loc (cloth_place c)) +
           cloth_sin0 c * cloth_Icos c b + cloth_cos0 c * cloth_Isin c b -
          (py (aff_loc (cloth_place c)) +
           cloth_sin0 c * cloth_Icos c a + cloth_cos0 c * cloth_Isin c a))
    with (cloth_sin0 c * (cloth_Icos c b - cloth_Icos c a) +
          cloth_cos0 c * (cloth_Isin c b - cloth_Isin c a)) by ring.
  rewrite (icos_ordered c a b Hwf Hab), (isin_ordered c a b Hwf Hab).
  rewrite (int_seg_L (fun u => cos (cloth_psi c u)) (rho_L c a b) K a b
             (rho_L_nn c a b) (cloth_kappa_max_nn c)
             (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
             (cos_k_lip c a b Hwf Ha Hb)).
  rewrite (int_seg_L (fun u => sin (cloth_psi c u)) (rho_L c a b) K a b
             (rho_L_nn c a b) (cloth_kappa_max_nn c)
             (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
             (sin_k_lip c a b Hwf Ha Hb)).
  set (Ic := int_seg (fun u => cos (cloth_psi c u)) K a b
               (cloth_kappa_max_nn c) (cos_k_lip c a b Hwf Ha Hb)).
  set (Is_ := int_seg (fun u => sin (cloth_psi c u)) K a b
               (cloth_kappa_max_nn c) (sin_k_lip c a b Hwf Ha Hb)).
  unfold Ic, Is_.
  rewrite <- (int_seg_scal (fun u => cos (cloth_psi c u)) (cloth_sin0 c)
               K K a b (cloth_kappa_max_nn c) (cloth_kappa_max_nn c)
               (cos_k_lip c a b Hwf Ha Hb) (sin0_cos_lip c a b Hwf Ha Hb)).
  rewrite <- (int_seg_scal (fun u => sin (cloth_psi c u)) (cloth_cos0 c)
               K K a b (cloth_kappa_max_nn c) (cloth_kappa_max_nn c)
               (sin_k_lip c a b Hwf Ha Hb) (cos0_sin_lip c a b Hwf Ha Hb)).
  rewrite <- (int_seg_plus
               (fun u => cloth_sin0 c * cos (cloth_psi c u))
               (fun u => cloth_cos0 c * sin (cloth_psi c u))
               K K K a b
               (cloth_kappa_max_nn c) (sin0_cos_lip c a b Hwf Ha Hb)
               (cloth_kappa_max_nn c) (cos0_sin_lip c a b Hwf Ha Hb)
               (cloth_kappa_max_nn c) (vy_sum_lip c a b Hwf Ha Hb)).
  apply int_seg_ext. intros u _. unfold cloth_vy. ring.
Qed.
Lemma vx_shift_lip : forall c s0 a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs ((cloth_vx c x - cloth_vx c s0) - (cloth_vx c y - cloth_vx c s0)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c s0 a b Hwf Ha Hb x y Hx Hy.
  replace ((cloth_vx c x - cloth_vx c s0) - (cloth_vx c y - cloth_vx c s0))
    with (cloth_vx c x - cloth_vx c y) by ring.
  apply (vx_lip_win c a b Hwf Ha Hb x y Hx Hy).
Qed.
Lemma vy_shift_lip : forall c s0 a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs ((cloth_vy c x - cloth_vy c s0) - (cloth_vy c y - cloth_vy c s0)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c s0 a b Hwf Ha Hb x y Hx Hy.
  replace ((cloth_vy c x - cloth_vy c s0) - (cloth_vy c y - cloth_vy c s0))
    with (cloth_vy c x - cloth_vy c y) by ring.
  apply (vy_lip_win c a b Hwf Ha Hb x y Hx Hy).
Qed.
Lemma k_ramp_lip : forall K p a b, 0 <= K ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (K * (p - x) - K * (p - y)) <= K * Rabs (x - y).
Proof.
  intros K p a b HK x y _ _.
  replace (K * (p - x) - K * (p - y)) with (K * (y - x)) by ring.
  rewrite Rabs_mult. rewrite (Rabs_right K) by lra.
  rewrite Rabs_minus_sym. apply Rle_refl.
Qed.
Lemma int_k_ramp : forall K p a b (HK : 0 <= K), a <= b ->
  int_seg (fun u => K * (p - u)) K a b HK (k_ramp_lip K p a b HK) =
  K * ((b - a) * (p - a) - (b - a) * (b - a) / 2).
Proof.
  intros K p a b HK Hab.
  rewrite (int_seg_scal (fun u => p - u) K K 1 a b HK Rle_0_1
             (ramp_lip p a b) (k_ramp_lip K p a b HK)).
  rewrite (int_ramp p a b Hab). ring.
Qed.
Lemma k_fwd_lip : forall K s0 a b, 0 <= K ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (K * (x - s0) - K * (y - s0)) <= K * Rabs (x - y).
Proof.
  intros K s0 a b HK x y _ _.
  replace (K * (x - s0) - K * (y - s0)) with (K * (x - y)) by ring.
  rewrite Rabs_mult. rewrite (Rabs_right K) by lra. apply Rle_refl.
Qed.
Lemma int_k_fwd : forall K s0 b (HK : 0 <= K), s0 <= b ->
  int_seg (fun u => K * (u - s0)) K s0 b HK (k_fwd_lip K s0 s0 b HK) =
    K * (b - s0) * (b - s0) / 2.
Proof.
  intros K s0 b HK Hsb.
  rewrite (int_seg_scal (fun u => u - s0) K K 1 s0 b HK Rle_0_1
             (fwd_lip s0 b) (k_fwd_lip K s0 s0 b HK)).
  rewrite (int_forward s0 b Hsb). field.
Qed.
Lemma unit_dot_le : forall ux uy dx dy,
  ux * ux + uy * uy = 1 ->
  Rabs (ux * dx + uy * dy) <= dist (mkPoint dx dy) (mkPoint 0 0).
Proof.
  intros ux uy dx dy Hu.
  rewrite dist0. rewrite <- (sqrt_Rsqr_abs (ux * dx + uy * dy)). unfold Rsqr.
  apply sqrt_le_1_alt.
  pose proof (cauchy_schwarz_2d ux uy dx dy) as Hcs.
  replace (ux * ux + uy * uy) with 1 in Hcs by (symmetry; exact Hu).
  rewrite Rmult_1_l in Hcs. exact Hcs.
Qed.
Lemma shift_dot_lip : forall c ux uy s0 a b, cloth_wf c ->
  ux * ux + uy * uy = 1 ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs ((ux * (cloth_vx c x - cloth_vx c s0) +
           uy * (cloth_vy c x - cloth_vy c s0)) -
          (ux * (cloth_vx c y - cloth_vx c s0) +
           uy * (cloth_vy c y - cloth_vy c s0))) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c ux uy s0 a b Hwf Hunit Ha Hb x y Hx Hy.
  replace ((ux * (cloth_vx c x - cloth_vx c s0) +
            uy * (cloth_vy c x - cloth_vy c s0)) -
           (ux * (cloth_vx c y - cloth_vx c s0) +
            uy * (cloth_vy c y - cloth_vy c s0)))
    with (ux * (cloth_vx c x - cloth_vx c y) +
          uy * (cloth_vy c x - cloth_vy c y)) by ring.
  eapply Rle_trans; [apply unit_dot_le; exact Hunit|].
  rewrite <- dist_diff. eapply Rle_trans.
  - apply tangent_sep. apply rho_h2. exact Hwf.
  - apply dpsi_le_kappa; try exact Hwf.
    + apply (win_in_rad c a b x Ha Hb Hx).
    + apply (win_in_rad c a b y Ha Hb Hy).
Qed.
Lemma coef_vx_shift : forall c coef s0 a b, cloth_wf c ->
  Rabs coef <= 1 ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (coef * (cloth_vx c x - cloth_vx c s0) -
          coef * (cloth_vx c y - cloth_vx c s0)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c coef s0 a b Hwf Hc Ha Hb x y Hx Hy.
  replace (coef * (cloth_vx c x - cloth_vx c s0) -
           coef * (cloth_vx c y - cloth_vx c s0))
    with (coef * (cloth_vx c x - cloth_vx c y)) by ring.
  rewrite Rabs_mult. eapply Rle_trans.
  - apply Rmult_le_compat_l; [apply Rabs_pos|].
    apply (vx_lip_win c a b Hwf Ha Hb x y Hx Hy).
  - assert (HK : 0 <= cloth_kappa_max c) by apply cloth_kappa_max_nn.
    apply Rle_trans with (1 * (cloth_kappa_max c * Rabs (x - y))).
    + apply Rmult_le_compat_r; [apply Rmult_le_pos; [exact HK| apply Rabs_pos]| exact Hc].
    + rewrite Rmult_1_l. apply Rle_refl.
Qed.
Lemma coef_vy_shift : forall c coef s0 a b, cloth_wf c ->
  Rabs coef <= 1 ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (coef * (cloth_vy c x - cloth_vy c s0) -
          coef * (cloth_vy c y - cloth_vy c s0)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c coef s0 a b Hwf Hc Ha Hb x y Hx Hy.
  replace (coef * (cloth_vy c x - cloth_vy c s0) -
           coef * (cloth_vy c y - cloth_vy c s0))
    with (coef * (cloth_vy c x - cloth_vy c y)) by ring.
  rewrite Rabs_mult. eapply Rle_trans.
  - apply Rmult_le_compat_l; [apply Rabs_pos|].
    apply (vy_lip_win c a b Hwf Ha Hb x y Hx Hy).
  - assert (HK : 0 <= cloth_kappa_max c) by apply cloth_kappa_max_nn.
    apply Rle_trans with (1 * (cloth_kappa_max c * Rabs (x - y))).
    + apply Rmult_le_compat_r; [apply Rmult_le_pos; [exact HK| apply Rabs_pos]| exact Hc].
    + rewrite Rmult_1_l. apply Rle_refl.
Qed.
Lemma int_mono : forall g h Lg Lh a b HLg Hlipg HLh Hlih,
  a <= b ->
  (forall x, a <= x <= b -> g x <= h x) ->
  int_seg g Lg a b HLg Hlipg <= int_seg h Lh a b HLh Hlih.
Proof.
  intros g h Lg Lh a b HLg Hlipg HLh Hlih Hab Hle.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hok|Hbad]; [|exfalso; apply Hbad; exact Hab].
  apply lint_mono. intros x Hx. apply Hle. exact Hx.
Qed.
Lemma back_norm : forall c a s (Hwf : cloth_wf c)
  (Ha : Rabs a <= cloth_rad c) (Hs : Rabs s <= cloth_rad c),
  a <= s ->
  dist (mkPoint
          (int_seg (fun u => cloth_vx c u - cloth_vx c s) (cloth_kappa_max c)
             a s (cloth_kappa_max_nn c) (vx_shift_lip c s a s Hwf Ha Hs))
          (int_seg (fun u => cloth_vy c u - cloth_vy c s) (cloth_kappa_max c)
             a s (cloth_kappa_max_nn c) (vy_shift_lip c s a s Hwf Ha Hs)))
       (mkPoint 0 0) <=
  cloth_kappa_max c * (s - a) * (s - a) / 2.
Proof.
  intros c a s Hwf Ha Hs Has.
  set (K := cloth_kappa_max c).
  set (Ix := int_seg (fun u => cloth_vx c u - cloth_vx c s) K a s
               (cloth_kappa_max_nn c) (vx_shift_lip c s a s Hwf Ha Hs)).
  set (Iy := int_seg (fun u => cloth_vy c u - cloth_vy c s) K a s
               (cloth_kappa_max_nn c) (vy_shift_lip c s a s Hwf Ha Hs)).
  rewrite dist0. set (r := sqrt (Ix * Ix + Iy * Iy)).
  destruct (Req_EM_T r 0) as [->|Hr].
  - unfold Rdiv. apply Rmult_le_pos.
    + apply Rmult_le_pos; [apply Rmult_le_pos; [apply cloth_kappa_max_nn|]|]; lra.
    + apply Rlt_le, Rinv_0_lt_compat. lra.
  - assert (Hsq : r * r = Ix * Ix + Iy * Iy).
    { unfold r. rewrite sqrt_sqrt; [reflexivity|].
      apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
    set (ux := Ix / r). set (uy := Iy / r).
    assert (Hunit : ux * ux + uy * uy = 1).
    { unfold ux, uy.
      replace (Ix / r * (Ix / r) + Iy / r * (Iy / r))
        with ((Ix * Ix + Iy * Iy) / (r * r)) by (field; exact Hr).
      rewrite <- Hsq. field. exact Hr. }
    assert (Hux : Rabs ux <= 1) by (apply frame_abs1 with (w := uy); exact Hunit).
    assert (Huy : Rabs uy <= 1) by (apply frame_abs1 with (w := ux); nra).
    assert (Hdot : ux * Ix + uy * Iy = r).
    { unfold ux, uy.
      replace (Ix / r * Ix + Iy / r * Iy) with ((Ix * Ix + Iy * Iy) / r)
        by (field; exact Hr).
      rewrite <- Hsq. field. exact Hr. }
    assert (Elin : ux * Ix + uy * Iy =
      int_seg (fun u => ux * (cloth_vx c u - cloth_vx c s) +
                        uy * (cloth_vy c u - cloth_vy c s))
        K a s (cloth_kappa_max_nn c)
        (shift_dot_lip c ux uy s a s Hwf Hunit Ha Hs)).
    { unfold Ix, Iy.
      rewrite <- (int_seg_scal (fun u => cloth_vx c u - cloth_vx c s) ux
                   K K a s (cloth_kappa_max_nn c) (cloth_kappa_max_nn c)
                   (vx_shift_lip c s a s Hwf Ha Hs)
                   (coef_vx_shift c ux s a s Hwf Hux Ha Hs)).
      rewrite <- (int_seg_scal (fun u => cloth_vy c u - cloth_vy c s) uy
                   K K a s (cloth_kappa_max_nn c) (cloth_kappa_max_nn c)
                   (vy_shift_lip c s a s Hwf Ha Hs)
                   (coef_vy_shift c uy s a s Hwf Huy Ha Hs)).
      rewrite <- (int_seg_plus
                   (fun u => ux * (cloth_vx c u - cloth_vx c s))
                   (fun u => uy * (cloth_vy c u - cloth_vy c s))
                   K K K a s
                   (cloth_kappa_max_nn c)
                   (coef_vx_shift c ux s a s Hwf Hux Ha Hs)
                   (cloth_kappa_max_nn c)
                   (coef_vy_shift c uy s a s Hwf Huy Ha Hs)
                   (cloth_kappa_max_nn c)
                   (shift_dot_lip c ux uy s a s Hwf Hunit Ha Hs)).
      reflexivity. }
    rewrite <- Hdot, Elin.
    eapply Rle_trans.
    + apply int_mono with
        (h := fun u => K * (s - u))
        (Lh := K)
        (HLh := cloth_kappa_max_nn c)
        (Hlih := k_ramp_lip K s a s (cloth_kappa_max_nn c)).
      * exact Has.
      * intros u Hu.
        apply Rle_trans with (K * Rabs (u - s)).
        -- apply Rle_trans with
             (Rabs (ux * (cloth_vx c u - cloth_vx c s) +
                    uy * (cloth_vy c u - cloth_vy c s))).
           ++ apply Rle_abs.
           ++ eapply Rle_trans; [apply unit_dot_le; exact Hunit|].
              rewrite <- dist_diff. eapply Rle_trans.
              ** apply tangent_sep. apply rho_h2. exact Hwf.
              ** apply dpsi_le_kappa; try exact Hwf.
                 --- apply (win_in_rad c a s u Ha Hs).
                     rewrite (Rmin_left a s), (Rmax_right a s) by lra. exact Hu.
                 --- apply (win_in_rad c a s s Ha Hs).
                     rewrite (Rmin_left a s), (Rmax_right a s) by lra. lra.
        -- rewrite Rabs_minus_sym, (Rabs_right (s - u)) by lra.
           unfold K. apply Rle_refl.
    + rewrite (int_k_ramp K s a s (cloth_kappa_max_nn c) Has).
      unfold K.
      replace (cloth_kappa_max c *
               ((s - a) * (s - a) - (s - a) * (s - a) / 2))
        with (cloth_kappa_max c * (s - a) * (s - a) / 2) by field.
      apply Rle_refl.
Qed.
Lemma fwd_norm : forall c s b (Hwf : cloth_wf c)
  (Hs : Rabs s <= cloth_rad c) (Hb : Rabs b <= cloth_rad c),
  s <= b ->
  dist (mkPoint
          (int_seg (fun u => cloth_vx c u - cloth_vx c s) (cloth_kappa_max c)
             s b (cloth_kappa_max_nn c) (vx_shift_lip c s s b Hwf Hs Hb))
          (int_seg (fun u => cloth_vy c u - cloth_vy c s) (cloth_kappa_max c)
             s b (cloth_kappa_max_nn c) (vy_shift_lip c s s b Hwf Hs Hb)))
       (mkPoint 0 0) <=
  cloth_kappa_max c * (b - s) * (b - s) / 2.
Proof.
  intros c s b Hwf Hs Hb Hsb.
  set (K := cloth_kappa_max c).
  set (Ix := int_seg (fun u => cloth_vx c u - cloth_vx c s) K s b
               (cloth_kappa_max_nn c) (vx_shift_lip c s s b Hwf Hs Hb)).
  set (Iy := int_seg (fun u => cloth_vy c u - cloth_vy c s) K s b
               (cloth_kappa_max_nn c) (vy_shift_lip c s s b Hwf Hs Hb)).
  rewrite dist0. set (r := sqrt (Ix * Ix + Iy * Iy)).
  destruct (Req_EM_T r 0) as [->|Hr].
  - unfold Rdiv. apply Rmult_le_pos.
    + apply Rmult_le_pos; [apply Rmult_le_pos; [apply cloth_kappa_max_nn|]|]; lra.
    + apply Rlt_le, Rinv_0_lt_compat. lra.
  - assert (Hsq : r * r = Ix * Ix + Iy * Iy).
    { unfold r. rewrite sqrt_sqrt; [reflexivity|].
      apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
    set (ux := Ix / r). set (uy := Iy / r).
    assert (Hunit : ux * ux + uy * uy = 1).
    { unfold ux, uy.
      replace (Ix / r * (Ix / r) + Iy / r * (Iy / r))
        with ((Ix * Ix + Iy * Iy) / (r * r)) by (field; exact Hr).
      rewrite <- Hsq. field. exact Hr. }
    assert (Hux : Rabs ux <= 1) by (apply frame_abs1 with (w := uy); exact Hunit).
    assert (Huy : Rabs uy <= 1) by (apply frame_abs1 with (w := ux); nra).
    assert (Hdot : ux * Ix + uy * Iy = r).
    { unfold ux, uy.
      replace (Ix / r * Ix + Iy / r * Iy) with ((Ix * Ix + Iy * Iy) / r)
        by (field; exact Hr).
      rewrite <- Hsq. field. exact Hr. }
    assert (Elin : ux * Ix + uy * Iy =
      int_seg (fun u => ux * (cloth_vx c u - cloth_vx c s) +
                        uy * (cloth_vy c u - cloth_vy c s))
        K s b (cloth_kappa_max_nn c)
        (shift_dot_lip c ux uy s s b Hwf Hunit Hs Hb)).
    { unfold Ix, Iy.
      rewrite <- (int_seg_scal (fun u => cloth_vx c u - cloth_vx c s) ux
                   K K s b (cloth_kappa_max_nn c) (cloth_kappa_max_nn c)
                   (vx_shift_lip c s s b Hwf Hs Hb)
                   (coef_vx_shift c ux s s b Hwf Hux Hs Hb)).
      rewrite <- (int_seg_scal (fun u => cloth_vy c u - cloth_vy c s) uy
                   K K s b (cloth_kappa_max_nn c) (cloth_kappa_max_nn c)
                   (vy_shift_lip c s s b Hwf Hs Hb)
                   (coef_vy_shift c uy s s b Hwf Huy Hs Hb)).
      rewrite <- (int_seg_plus
                   (fun u => ux * (cloth_vx c u - cloth_vx c s))
                   (fun u => uy * (cloth_vy c u - cloth_vy c s))
                   K K K s b
                   (cloth_kappa_max_nn c)
                   (coef_vx_shift c ux s s b Hwf Hux Hs Hb)
                   (cloth_kappa_max_nn c)
                   (coef_vy_shift c uy s s b Hwf Huy Hs Hb)
                   (cloth_kappa_max_nn c)
                   (shift_dot_lip c ux uy s s b Hwf Hunit Hs Hb)).
      reflexivity. }
    rewrite <- Hdot, Elin.
    eapply Rle_trans.
    + apply int_mono with
        (h := fun u => K * (u - s))
        (Lh := K)
        (HLh := cloth_kappa_max_nn c)
        (Hlih := k_fwd_lip K s s b (cloth_kappa_max_nn c)).
      * exact Hsb.
      * intros u Hu.
        apply Rle_trans with (K * Rabs (u - s)).
        -- apply Rle_trans with
             (Rabs (ux * (cloth_vx c u - cloth_vx c s) +
                    uy * (cloth_vy c u - cloth_vy c s))).
           ++ apply Rle_abs.
           ++ eapply Rle_trans; [apply unit_dot_le; exact Hunit|].
              rewrite <- dist_diff. eapply Rle_trans.
              ** apply tangent_sep. apply rho_h2. exact Hwf.
              ** apply dpsi_le_kappa; try exact Hwf.
                 --- apply (win_in_rad c s b u Hs Hb).
                     rewrite (Rmin_left s b), (Rmax_right s b) by lra. exact Hu.
                 --- apply (win_in_rad c s b s Hs Hb).
                     rewrite (Rmin_left s b), (Rmax_right s b) by lra. lra.
        -- rewrite (Rabs_right (u - s)) by lra. unfold K. apply Rle_refl.
    + rewrite (int_k_fwd K s b (cloth_kappa_max_nn c) Hsb).
      unfold K. apply Rle_refl.
Qed.
Lemma constK_lip : forall (c0 K a b : R), 0 <= K ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs ((fun _ : R => c0) x - (fun _ : R => c0) y) <= K * Rabs (x - y).
Proof.
  intros c0 K a b HK x y _ _. cbn.
  rewrite Rminus_diag, Rabs_R0.
  apply Rmult_le_pos; [exact HK | apply Rabs_pos].
Qed.
Lemma vx_re_lip : forall c s0 a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (((cloth_vx c x - cloth_vx c s0) + cloth_vx c s0) -
          ((cloth_vx c y - cloth_vx c s0) + cloth_vx c s0)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c s0 a b Hwf Ha Hb x y Hx Hy.
  replace (((cloth_vx c x - cloth_vx c s0) + cloth_vx c s0) -
           ((cloth_vx c y - cloth_vx c s0) + cloth_vx c s0))
    with (cloth_vx c x - cloth_vx c y) by ring.
  apply (vx_lip_win c a b Hwf Ha Hb x y Hx Hy).
Qed.
Lemma vy_re_lip : forall c s0 a b, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (((cloth_vy c x - cloth_vy c s0) + cloth_vy c s0) -
          ((cloth_vy c y - cloth_vy c s0) + cloth_vy c s0)) <=
      cloth_kappa_max c * Rabs (x - y).
Proof.
  intros c s0 a b Hwf Ha Hb x y Hx Hy.
  replace (((cloth_vy c x - cloth_vy c s0) + cloth_vy c s0) -
           ((cloth_vy c y - cloth_vy c s0) + cloth_vy c s0))
    with (cloth_vy c x - cloth_vy c y) by ring.
  apply (vy_lip_win c a b Hwf Ha Hb x y Hx Hy).
Qed.
Lemma int_const_val : forall (c0 L a b : R) HL Hlip, a <= b ->
  int_seg (fun _ : R => c0) L a b HL Hlip = (b - a) * c0.
Proof.
  intros c0 L a b HL Hlip Hab.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hok|Hbad]; [|exfalso; apply Hbad; exact Hab].
  apply lint_const.
Qed.
Lemma int_vx_center : forall c a s (Hwf : cloth_wf c)
  (Ha : Rabs a <= cloth_rad c) (Hs : Rabs s <= cloth_rad c),
  a <= s ->
  int_seg (cloth_vx c) (cloth_kappa_max c) a s (cloth_kappa_max_nn c)
    (vx_lip_win c a s Hwf Ha Hs) =
  int_seg (fun u => cloth_vx c u - cloth_vx c s) (cloth_kappa_max c) a s
    (cloth_kappa_max_nn c) (vx_shift_lip c s a s Hwf Ha Hs) +
  (s - a) * cloth_vx c s.
Proof.
  intros c a s Hwf Ha Hs Has.
  rewrite (int_seg_ext (cloth_vx c)
             (fun u => (cloth_vx c u - cloth_vx c s) + cloth_vx c s)
             (cloth_kappa_max c) a s (cloth_kappa_max_nn c)
             (vx_lip_win c a s Hwf Ha Hs) (vx_re_lip c s a s Hwf Ha Hs))
    by (intros u _; ring).
  rewrite (int_seg_plus
             (fun u => cloth_vx c u - cloth_vx c s) (fun _ => cloth_vx c s)
             (cloth_kappa_max c) (cloth_kappa_max c) (cloth_kappa_max c) a s
             (cloth_kappa_max_nn c) (vx_shift_lip c s a s Hwf Ha Hs)
             (cloth_kappa_max_nn c)
             (constK_lip (cloth_vx c s) (cloth_kappa_max c) a s (cloth_kappa_max_nn c))
             (cloth_kappa_max_nn c) (vx_re_lip c s a s Hwf Ha Hs)).
  rewrite (int_const_val (cloth_vx c s) (cloth_kappa_max c) a s
             (cloth_kappa_max_nn c)
             (constK_lip (cloth_vx c s) (cloth_kappa_max c) a s (cloth_kappa_max_nn c))
             Has).
  ring.
Qed.
Lemma int_vy_center : forall c a s (Hwf : cloth_wf c)
  (Ha : Rabs a <= cloth_rad c) (Hs : Rabs s <= cloth_rad c),
  a <= s ->
  int_seg (cloth_vy c) (cloth_kappa_max c) a s (cloth_kappa_max_nn c)
    (vy_lip_win c a s Hwf Ha Hs) =
  int_seg (fun u => cloth_vy c u - cloth_vy c s) (cloth_kappa_max c) a s
    (cloth_kappa_max_nn c) (vy_shift_lip c s a s Hwf Ha Hs) +
  (s - a) * cloth_vy c s.
Proof.
  intros c a s Hwf Ha Hs Has.
  rewrite (int_seg_ext (cloth_vy c)
             (fun u => (cloth_vy c u - cloth_vy c s) + cloth_vy c s)
             (cloth_kappa_max c) a s (cloth_kappa_max_nn c)
             (vy_lip_win c a s Hwf Ha Hs) (vy_re_lip c s a s Hwf Ha Hs))
    by (intros u _; ring).
  rewrite (int_seg_plus
             (fun u => cloth_vy c u - cloth_vy c s) (fun _ => cloth_vy c s)
             (cloth_kappa_max c) (cloth_kappa_max c) (cloth_kappa_max c) a s
             (cloth_kappa_max_nn c) (vy_shift_lip c s a s Hwf Ha Hs)
             (cloth_kappa_max_nn c)
             (constK_lip (cloth_vy c s) (cloth_kappa_max c) a s (cloth_kappa_max_nn c))
             (cloth_kappa_max_nn c) (vy_re_lip c s a s Hwf Ha Hs)).
  rewrite (int_const_val (cloth_vy c s) (cloth_kappa_max c) a s
             (cloth_kappa_max_nn c)
             (constK_lip (cloth_vy c s) (cloth_kappa_max c) a s (cloth_kappa_max_nn c))
             Has).
  ring.
Qed.
Lemma int_vx_left : forall c a b (Hwf : cloth_wf c)
  (Ha : Rabs a <= cloth_rad c) (Hb : Rabs b <= cloth_rad c),
  a <= b ->
  int_seg (cloth_vx c) (cloth_kappa_max c) a b (cloth_kappa_max_nn c)
    (vx_lip_win c a b Hwf Ha Hb) =
  int_seg (fun u => cloth_vx c u - cloth_vx c a) (cloth_kappa_max c) a b
    (cloth_kappa_max_nn c) (vx_shift_lip c a a b Hwf Ha Hb) +
  (b - a) * cloth_vx c a.
Proof.
  intros c a b Hwf Ha Hb Hab.
  rewrite (int_seg_ext (cloth_vx c)
             (fun u => (cloth_vx c u - cloth_vx c a) + cloth_vx c a)
             (cloth_kappa_max c) a b (cloth_kappa_max_nn c)
             (vx_lip_win c a b Hwf Ha Hb) (vx_re_lip c a a b Hwf Ha Hb))
    by (intros u _; ring).
  rewrite (int_seg_plus
             (fun u => cloth_vx c u - cloth_vx c a) (fun _ => cloth_vx c a)
             (cloth_kappa_max c) (cloth_kappa_max c) (cloth_kappa_max c) a b
             (cloth_kappa_max_nn c) (vx_shift_lip c a a b Hwf Ha Hb)
             (cloth_kappa_max_nn c)
             (constK_lip (cloth_vx c a) (cloth_kappa_max c) a b (cloth_kappa_max_nn c))
             (cloth_kappa_max_nn c) (vx_re_lip c a a b Hwf Ha Hb)).
  rewrite (int_const_val (cloth_vx c a) (cloth_kappa_max c) a b
             (cloth_kappa_max_nn c)
             (constK_lip (cloth_vx c a) (cloth_kappa_max c) a b (cloth_kappa_max_nn c))
             Hab).
  ring.
Qed.
Lemma int_vy_left : forall c a b (Hwf : cloth_wf c)
  (Ha : Rabs a <= cloth_rad c) (Hb : Rabs b <= cloth_rad c),
  a <= b ->
  int_seg (cloth_vy c) (cloth_kappa_max c) a b (cloth_kappa_max_nn c)
    (vy_lip_win c a b Hwf Ha Hb) =
  int_seg (fun u => cloth_vy c u - cloth_vy c a) (cloth_kappa_max c) a b
    (cloth_kappa_max_nn c) (vy_shift_lip c a a b Hwf Ha Hb) +
  (b - a) * cloth_vy c a.
Proof.
  intros c a b Hwf Ha Hb Hab.
  rewrite (int_seg_ext (cloth_vy c)
             (fun u => (cloth_vy c u - cloth_vy c a) + cloth_vy c a)
             (cloth_kappa_max c) a b (cloth_kappa_max_nn c)
             (vy_lip_win c a b Hwf Ha Hb) (vy_re_lip c a a b Hwf Ha Hb))
    by (intros u _; ring).
  rewrite (int_seg_plus
             (fun u => cloth_vy c u - cloth_vy c a) (fun _ => cloth_vy c a)
             (cloth_kappa_max c) (cloth_kappa_max c) (cloth_kappa_max c) a b
             (cloth_kappa_max_nn c) (vy_shift_lip c a a b Hwf Ha Hb)
             (cloth_kappa_max_nn c)
             (constK_lip (cloth_vy c a) (cloth_kappa_max c) a b (cloth_kappa_max_nn c))
             (cloth_kappa_max_nn c) (vy_re_lip c a a b Hwf Ha Hb)).
  rewrite (int_const_val (cloth_vy c a) (cloth_kappa_max c) a b
             (cloth_kappa_max_nn c)
             (constK_lip (cloth_vy c a) (cloth_kappa_max c) a b (cloth_kappa_max_nn c))
             Hab).
  ring.
Qed.
Lemma chord_coord : forall Ps Pa Pb Ix Jx L h V,
  Ps - Pa = Ix + L * h * V ->
  Pb - Ps = Jx + (1 - L) * h * V ->
  Ps - ((1 - L) * Pa + L * Pb) = (1 - L) * Ix - L * Jx.
Proof.
  intros Ps Pa Pb Ix Jx L h V Hps Hpb.
  replace Pb with (Ps + (Pb - Ps)) by ring.
  rewrite Hpb.
  replace Ps with (Pa + (Ps - Pa)) by ring.
  rewrite Hps. ring.
Qed.
Lemma sag_le : forall K h L, 0 <= K -> 0 <= h -> 0 <= L <= 1 ->
  (1 - L) * (K * (L * h) * (L * h) / 2) +
  L * (K * ((1 - L) * h) * ((1 - L) * h) / 2) <= K * h * h / 8.
Proof.
  intros K h L HK Hh HL.
  assert (E4 : L * (1 - L) = / 4 - (L - / 2) ^ 2) by field.
  assert (Hq : L * (1 - L) <= / 4).
  { rewrite E4. apply Rle_trans with (/ 4 - 0).
    - apply Rplus_le_compat_l. apply Ropp_le_contravar. apply pow2_ge_0.
    - unfold Rminus. rewrite Ropp_0, Rplus_0_r. apply Rle_refl. }
  replace ((1 - L) * (K * (L * h) * (L * h) / 2) +
           L * (K * ((1 - L) * h) * ((1 - L) * h) / 2))
    with (K * h * h * (L * (1 - L)) / 2) by field.
  replace (K * h * h / 8) with ((K * h * h / 2) * / 4) by field.
  replace (K * h * h * (L * (1 - L)) / 2)
    with ((K * h * h / 2) * (L * (1 - L))) by field.
  apply Rmult_le_compat_l; [|exact Hq].
  unfold Rdiv. apply Rmult_le_pos.
  - apply Rmult_le_pos; [apply Rmult_le_pos; assumption|assumption].
  - apply Rlt_le, Rinv_0_lt_compat. lra.
Qed.
Lemma chord_near : forall c a b s, cloth_wf c ->
  Rabs a <= cloth_rad c -> Rabs b <= cloth_rad c -> a <= s <= b ->
  dist (cloth_P c s)
       (seg_at (cloth_P c a) (cloth_P c b) ((s - a) / (b - a))) <=
  cloth_kappa_max c * (b - a) * (b - a) / 8.
Proof.
  intros c a b s Hwf Ha Hb Hsrg.
  assert (Hab : a <= b) by lra.
  assert (Hs : Rabs s <= cloth_rad c).
  { apply (win_in_rad c a b s Ha Hb).
    rewrite (Rmin_left a b), (Rmax_right a b) by exact Hab. lra. }
  set (h := b - a). set (lam := (s - a) / h).
  set (K := cloth_kappa_max c).
  destruct (Req_EM_T h 0) as [Hz|Hnz].
  - assert (Ea : s = a) by (unfold h in Hz; lra).
    assert (Eb : b = a) by (unfold h in Hz; lra). subst s b.
    assert (Hp : cloth_P c a = seg_at (cloth_P c a) (cloth_P c a) lam).
    { unfold seg_at. apply (f_equal2 mkPoint); cbn; ring. }
    rewrite <- Hp. unfold dist, dist_sq. cbn.
    rewrite !Rminus_diag, !Rmult_0_l, Rplus_0_l, sqrt_0.
    rewrite !Hz. unfold K, Rdiv.
    rewrite (Rmult_0_r (cloth_kappa_max c)).
    rewrite (Rmult_0_l 0). rewrite (Rmult_0_l (/ 8)). apply Rle_refl.
  - assert (Hpos : 0 < h) by (unfold h in *; lra).
    assert (Hlam : 0 <= lam <= 1).
    { unfold lam. split.
      - apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; exact Hpos].
      - unfold lam. apply Rmult_le_reg_r with h; [exact Hpos|].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
        rewrite Rmult_1_r, Rmult_1_l. unfold h. lra. }
    set (Ix := int_seg (fun u => cloth_vx c u - cloth_vx c s) K a s
                 (cloth_kappa_max_nn c) (vx_shift_lip c s a s Hwf Ha Hs)).
    set (Iy := int_seg (fun u => cloth_vy c u - cloth_vy c s) K a s
                 (cloth_kappa_max_nn c) (vy_shift_lip c s a s Hwf Ha Hs)).
    set (Jx := int_seg (fun u => cloth_vx c u - cloth_vx c s) K s b
                 (cloth_kappa_max_nn c) (vx_shift_lip c s s b Hwf Hs Hb)).
    set (Jy := int_seg (fun u => cloth_vy c u - cloth_vy c s) K s b
                 (cloth_kappa_max_nn c) (vy_shift_lip c s s b Hwf Hs Hb)).
    assert (Hax : cloth_Px c s - cloth_Px c a = Ix + (s - a) * cloth_vx c s).
    { rewrite (px_delta c a s Hwf Ha Hs) by lra.
      rewrite (int_vx_center c a s Hwf Ha Hs) by lra. unfold Ix. reflexivity. }
    assert (Hsx : cloth_Px c b - cloth_Px c s = Jx + (b - s) * cloth_vx c s).
    { rewrite (px_delta c s b Hwf Hs Hb) by lra.
      rewrite (int_vx_left c s b Hwf Hs Hb) by lra. unfold Jx. reflexivity. }
    assert (Hay : cloth_Py c s - cloth_Py c a = Iy + (s - a) * cloth_vy c s).
    { rewrite (py_delta c a s Hwf Ha Hs) by lra.
      rewrite (int_vy_center c a s Hwf Ha Hs) by lra. unfold Iy. reflexivity. }
    assert (Hsy : cloth_Py c b - cloth_Py c s = Jy + (b - s) * cloth_vy c s).
    { rewrite (py_delta c s b Hwf Hs Hb) by lra.
      rewrite (int_vy_left c s b Hwf Hs Hb) by lra. unfold Jy. reflexivity. }
    assert (Esa : s - a = lam * h).
    { unfold lam, Rdiv. rewrite Rmult_assoc, Rinv_l by exact Hnz.
      rewrite Rmult_1_r. reflexivity. }
    assert (Ebs : b - s = (1 - lam) * h).
    { replace ((1 - lam) * h) with (h - lam * h) by ring.
      rewrite <- Esa. unfold h. ring. }
    assert (Hax' : cloth_Px c s - cloth_Px c a =
                   Ix + lam * h * cloth_vx c s).
    { rewrite Hax, Esa. reflexivity. }
    assert (Hsx' : cloth_Px c b - cloth_Px c s =
                   Jx + (1 - lam) * h * cloth_vx c s).
    { rewrite Hsx, Ebs. reflexivity. }
    assert (Hay' : cloth_Py c s - cloth_Py c a =
                   Iy + lam * h * cloth_vy c s).
    { rewrite Hay, Esa. reflexivity. }
    assert (Hsy' : cloth_Py c b - cloth_Py c s =
                   Jy + (1 - lam) * h * cloth_vy c s).
    { rewrite Hsy, Ebs. reflexivity. }
    assert (Ex : px (cloth_P c s) -
            px (seg_at (cloth_P c a) (cloth_P c b) lam) =
            (1 - lam) * Ix - lam * Jx).
    { unfold cloth_P, seg_at. cbn.
      apply (chord_coord (cloth_Px c s) (cloth_Px c a) (cloth_Px c b)
              Ix Jx lam h (cloth_vx c s) Hax' Hsx'). }
    assert (Ey : py (cloth_P c s) -
            py (seg_at (cloth_P c a) (cloth_P c b) lam) =
            (1 - lam) * Iy - lam * Jy).
    { unfold cloth_P, seg_at. cbn.
      apply (chord_coord (cloth_Py c s) (cloth_Py c a) (cloth_Py c b)
              Iy Jy lam h (cloth_vy c s) Hay' Hsy'). }
    assert (D :
      dist (cloth_P c s) (seg_at (cloth_P c a) (cloth_P c b) lam) =
      dist (mkPoint ((1 - lam) * Ix - lam * Jx)
                    ((1 - lam) * Iy - lam * Jy)) (mkPoint 0 0)).
    { unfold cloth_P, seg_at. cbn.
      rewrite dist_diff.
      apply (f_equal2 dist); [|reflexivity].
      apply (f_equal2 mkPoint); cbn.
      - exact Ex.
      - exact Ey. }
    rewrite D. eapply Rle_trans.
      * replace ((1 - lam) * Ix - lam * Jx)
          with ((1 - lam) * Ix + (- lam) * Jx) by ring.
        replace ((1 - lam) * Iy - lam * Jy)
          with ((1 - lam) * Iy + (- lam) * Jy) by ring.
        apply dist0_triangle.
      * rewrite !dist0_scale.
        rewrite (Rabs_right (1 - lam)) by lra.
        rewrite Rabs_Ropp, (Rabs_right lam) by lra.
        unfold Ix, Iy, Jx, Jy.
        eapply Rle_trans.
        -- apply Rplus_le_compat.
           ++ apply Rmult_le_compat_l; [lra|].
              apply (back_norm c a s Hwf Ha Hs). lra.
           ++ apply Rmult_le_compat_l; [lra|].
              apply (fwd_norm c s b Hwf Hs Hb). lra.
        -- rewrite Esa, Ebs. unfold h, K. apply sag_le.
           ++ apply cloth_kappa_max_nn.
           ++ lra.
           ++ exact Hlam.
Qed.

Print Assumptions cloth_kappa_max_nn.
Print Assumptions cloth_rad_nn.
Print Assumptions Rmax_scale_pos.
Print Assumptions kappa_abs_station.
Print Assumptions kappa_max_eq.
Print Assumptions sin_abs_le.
Print Assumptions dist_diff.
Print Assumptions dist0.
Print Assumptions abs_le_dist0.
Print Assumptions dist0_scale.
Print Assumptions dist0_triangle.
Print Assumptions heading_gap.
Print Assumptions tangent_sep.
Print Assumptions dpsi_le_kappa.
Print Assumptions win_in_rad.
Print Assumptions vx_lip_win.
Print Assumptions vy_lip_win.
Print Assumptions trig_k_lip.
Print Assumptions cos_k_lip.
Print Assumptions sin_k_lip.
Print Assumptions frame_abs1.
Print Assumptions coef_trig_lip.
Print Assumptions cos0_lip.
Print Assumptions nsin0_lip.
Print Assumptions vx_sum_lip.
Print Assumptions vy_sum_lip.
Print Assumptions sin0_lip.
Print Assumptions px_delta.
Print Assumptions sin0_cos_lip.
Print Assumptions cos0_sin_lip.
Print Assumptions py_delta.
Print Assumptions vx_shift_lip.
Print Assumptions vy_shift_lip.
Print Assumptions k_ramp_lip.
Print Assumptions int_k_ramp.
Print Assumptions k_fwd_lip.
Print Assumptions int_k_fwd.
Print Assumptions unit_dot_le.
Print Assumptions shift_dot_lip.
Print Assumptions coef_vx_shift.
Print Assumptions coef_vy_shift.
Print Assumptions int_mono.
Print Assumptions back_norm.
Print Assumptions fwd_norm.
Print Assumptions constK_lip.
Print Assumptions vx_re_lip.
Print Assumptions vy_re_lip.
Print Assumptions int_const_val.
Print Assumptions int_vx_center.
Print Assumptions int_vy_center.
Print Assumptions int_vx_left.
Print Assumptions int_vy_left.
Print Assumptions chord_coord.
Print Assumptions sag_le.
Print Assumptions chord_near.
