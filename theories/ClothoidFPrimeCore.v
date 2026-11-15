(* ============================================================================
   NetTopologySuite.Proofs.ClothoidFPrimeCore
   ----------------------------------------------------------------------------
   Sign of the chord-length derivative of a clothoid on the full branch.

   Unit parameter x in [0, 1], heading u(x) = p x + D x^2 / 2 (p = L k0,
   D = L (k1 - k0)), and the four moments
     P = ∫ cos u,  Q = ∫ sin u,  R = ∫ u cos u,  T = ∫ u sin u.
   Half the derivative of the squared chord in the length parameter is
     N = P (P - T) + Q (Q + R).
   Theorem clothoid_fprime_core_pos:  |p| + |D| / 2 < PI  ->  0 < N.

   Proof.  Write W = p + D / 2 (total turning) and centre the parameter:
     u(x) = W / 2 + b(x) + e(x),  b = W (x - 1/2),  e = D x (x - 1) / 2,
   b odd and e even about 1/2.  With
     A = ∫ cos b cos e,  B = ∫ cos b sin e,
     Ae = ∫ e cos b cos e,  Be = ∫ e cos b sin e,
   two integrations by parts (primitives (x - 1/2) cos u, (x - 1/2) sin u)
   and the vanishing of the odd integrals give the identity
     N = cos (W / 2) * A + (A * Be - B * Ae).
   On the branch |W| < PI and |D| < 2 PI, so |b| < PI / 2 and
   |e| <= |D| / 8 < PI / 4 on [0, 1]: cos b > 0, cos e > 0, A > 0,
   |B| <= A.  For the second term put theta = ∫ e cos b / ∫ cos b and
   n(y) = A sin y - B cos y.  Since ∫ cos b * n(e) = 0,
     A * Be - B * Ae = ∫ cos b * (e - theta) * (n(e) - n(theta)),
   and n is nondecreasing on [-PI/4, PI/4], so the integrand is >= 0.
   The circle (D = 0) gives N = cos (W / 2) * sin (W / 2) / (W / 2), which
   vanishes at |W| = PI: the bound is sharp.

   "Every tangent has a positive component along the chord" is not enough
   on its own (a two-point heading distribution at +-beta, beta > 0.87,
   makes the same integral negative).  The proof uses that the heading is
   quadratic.  Stdlib atan prints Classical_Prop.classic, so the chord
   direction is not taken as an angle; theta is a weighted mean instead.

   claimId: none.  Discharges ClothoidResidual.ClothoidFPrimePos.
   No Admitted / Axiom / Parameter.  No MVT, Rolle, RiemannInt, Coquelicot.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude Code
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import LipInt LipIntUnit.
Local Open Scope R_scope.

(* ---- trigonometric facts -------------------------------------------------- *)

Lemma cos_abs_ge :
  forall x y, Rabs x <= y -> y <= PI -> cos y <= cos x.
Proof.
  intros x y Hxy Hy.
  assert (Hc : cos x = cos (Rabs x)).
  { unfold Rabs. destruct (Rcase_abs x); [rewrite cos_neg|]; reflexivity. }
  rewrite Hc. pose proof (Rabs_pos x).
  apply cos_decr_1; lra.
Qed.

Lemma sin_le_cos_quarter :
  forall x, Rabs x <= PI / 4 -> - cos x <= sin x <= cos x.
Proof.
  intros x Hx.
  assert (Hx' : - (PI / 4) <= x <= PI / 4) by (split_Rabs; lra).
  pose proof PI_RGT_0 as Hpi.
  assert (H2 : 0 <= cos (2 * x)) by (apply cos_ge_0; lra).
  assert (H1 : 0 < cos x) by (apply cos_gt_0; lra).
  rewrite cos_2a in H2. split; nra.
Qed.

Lemma id_sin_nonneg :
  forall d, Rabs d <= PI -> 0 <= d * sin d.
Proof.
  intros d Hd.
  assert (Hd' : - PI <= d <= PI) by (split_Rabs; lra).
  destruct (Rle_dec 0 d) as [Hp|Hn].
  - apply Rmult_le_pos; [exact Hp | apply sin_ge_0; lra].
  - assert (Hs : 0 <= sin (- d)) by (apply sin_ge_0; lra).
    rewrite sin_neg in Hs. nra.
Qed.

(* ---- derivatives of the two primitives ----------------------------------- *)

Lemma deriv_quad_heading :
  forall p D x,
    derivable_pt_lim (fun x => p * x + D * x * x / 2) x (p + D * x).
Proof.
  intros p D x eps Heps.
  assert (Hd : 0 < eps / (Rabs D + 1)).
  { apply Rdiv_lt_0_compat; [exact Heps | pose proof (Rabs_pos D); lra]. }
  exists (mkposreal _ Hd). intros h Hh0 Hh. simpl in Hh.
  replace ((p * (x + h) + D * (x + h) * (x + h) / 2 - (p * x + D * x * x / 2)) / h
           - (p + D * x)) with (D * h / 2) by (field; exact Hh0).
  unfold Rdiv at 1. rewrite !Rabs_mult.
  rewrite (Rabs_pos_eq (/ 2)) by lra.
  pose proof (Rabs_pos D) as HD. pose proof (Rabs_pos h) as Hhp.
  assert (Hm : Rabs D * Rabs h <= Rabs D * (eps / (Rabs D + 1))).
  { apply Rmult_le_compat_l; lra. }
  assert (He : Rabs D * (eps / (Rabs D + 1)) <= eps).
  { unfold Rdiv. rewrite (Rmult_comm eps), <- Rmult_assoc.
    assert (Hq : Rabs D * / (Rabs D + 1) <= 1).
    { apply Rmult_le_reg_r with (Rabs D + 1); [lra|].
      rewrite Rmult_assoc, Rinv_l by lra. lra. }
    nra. }
  lra.
Qed.

Lemma deriv_half_cos :
  forall (v : R -> R) x dv,
    derivable_pt_lim v x dv ->
    derivable_pt_lim (fun x => (x - / 2) * cos (v x)) x
      (cos (v x) - (x - / 2) * dv * sin (v x)).
Proof.
  intros v x dv Hv.
  replace (cos (v x) - (x - / 2) * dv * sin (v x))
    with ((1 - 0) * cos (v x) + (x - / 2) * (- sin (v x) * dv)) by ring.
  apply (derivable_pt_lim_mult (fun x => x - / 2) (fun x => cos (v x))).
  - apply (derivable_pt_lim_minus (fun x => x) (fun _ => / 2)).
    + apply derivable_pt_lim_id.
    + apply derivable_pt_lim_const.
  - apply (derivable_pt_lim_comp v cos x dv (- sin (v x)) Hv).
    apply derivable_pt_lim_cos.
Qed.

Lemma deriv_half_sin :
  forall (v : R -> R) x dv,
    derivable_pt_lim v x dv ->
    derivable_pt_lim (fun x => (x - / 2) * sin (v x)) x
      (sin (v x) + (x - / 2) * dv * cos (v x)).
Proof.
  intros v x dv Hv.
  replace (sin (v x) + (x - / 2) * dv * cos (v x))
    with ((1 - 0) * sin (v x) + (x - / 2) * (cos (v x) * dv)) by ring.
  apply (derivable_pt_lim_mult (fun x => x - / 2) (fun x => sin (v x))).
  - apply (derivable_pt_lim_minus (fun x => x) (fun _ => / 2)).
    + apply derivable_pt_lim_id.
    + apply derivable_pt_lim_const.
  - apply (derivable_pt_lim_comp v sin x dv (cos (v x)) Hv).
    apply derivable_pt_lim_sin.
Qed.

(* ---- the centred frame ---------------------------------------------------- *)

Definition cf_W (p D : R) : R := p + D / 2.
Definition cf_u (p D x : R) : R := p * x + D * x * x / 2.
Definition cf_e (D x : R) : R := D * x * (x - 1) / 2.
Definition cf_b (p D x : R) : R := cf_W p D * (x - / 2).

Definition cf_cc (p D x : R) : R := cos (cf_b p D x) * cos (cf_e D x).
Definition cf_cs (p D x : R) : R := cos (cf_b p D x) * sin (cf_e D x).
Definition cf_ss (p D x : R) : R := sin (cf_b p D x) * sin (cf_e D x).
Definition cf_sc (p D x : R) : R := sin (cf_b p D x) * cos (cf_e D x).

Ltac cf_unfold :=
  unfold cf_cc, cf_cs, cf_ss, cf_sc, cf_b, cf_e, cf_u, cf_W.

Ltac cf_ulip := cf_unfold; ulip.

Lemma cf_phase :
  forall p D x, cf_u p D x = cf_W p D / 2 + (cf_b p D x + cf_e D x).
Proof. intros. cf_unfold. field. Qed.

Lemma cf_cos_split :
  forall p D x,
    cos (cf_u p D x)
    = cos (cf_W p D / 2) * cf_cc p D x + - sin (cf_W p D / 2) * cf_cs p D x
      + - cos (cf_W p D / 2) * cf_ss p D x + - sin (cf_W p D / 2) * cf_sc p D x.
Proof.
  intros. rewrite cf_phase, cos_plus, cos_plus, sin_plus.
  unfold cf_cc, cf_cs, cf_ss, cf_sc. ring.
Qed.

Lemma cf_sin_split :
  forall p D x,
    sin (cf_u p D x)
    = sin (cf_W p D / 2) * cf_cc p D x + cos (cf_W p D / 2) * cf_cs p D x
      + - sin (cf_W p D / 2) * cf_ss p D x + cos (cf_W p D / 2) * cf_sc p D x.
Proof.
  intros. rewrite cf_phase, sin_plus, cos_plus, sin_plus.
  unfold cf_cc, cf_cs, cf_ss, cf_sc. ring.
Qed.

Lemma cf_e_refl : forall D x, cf_e D (1 - x) = cf_e D x.
Proof. intros. unfold cf_e. field. Qed.

Lemma cf_b_refl : forall p D x, cf_b p D (1 - x) = - cf_b p D x.
Proof. intros. unfold cf_b. field. Qed.

Lemma cf_ss_refl : forall p D x, cf_ss p D (1 - x) = - cf_ss p D x.
Proof. intros. unfold cf_ss. rewrite cf_e_refl, cf_b_refl, sin_neg. ring. Qed.

Lemma cf_sc_refl : forall p D x, cf_sc p D (1 - x) = - cf_sc p D x.
Proof. intros. unfold cf_sc. rewrite cf_e_refl, cf_b_refl, sin_neg. ring. Qed.

Section Core.
Variables p D : R.

Let W := cf_W p D.
Let ca := cos (W / 2).
Let sa := sin (W / 2).
Let kq := W / 2 - D / 4.

Lemma cf_cc_lip : ULip (cf_cc p D).
Proof. unfold cf_cc. cf_ulip. Qed.
Lemma cf_cs_lip : ULip (cf_cs p D).
Proof. unfold cf_cs. cf_ulip. Qed.
Lemma cf_ss_lip : ULip (cf_ss p D).
Proof. unfold cf_ss. cf_ulip. Qed.
Lemma cf_sc_lip : ULip (cf_sc p D).
Proof. unfold cf_sc. cf_ulip. Qed.
Lemma cf_ecc_lip : ULip (fun x => cf_e D x * cf_cc p D x).
Proof. cf_ulip. Qed.
Lemma cf_ecs_lip : ULip (fun x => cf_e D x * cf_cs p D x).
Proof. cf_ulip. Qed.
Lemma cf_ess_lip : ULip (fun x => cf_e D x * cf_ss p D x).
Proof. cf_ulip. Qed.
Lemma cf_esc_lip : ULip (fun x => cf_e D x * cf_sc p D x).
Proof. cf_ulip. Qed.
Lemma cf_cosu_lip : ULip (fun x => cos (cf_u p D x)).
Proof. cf_ulip. Qed.
Lemma cf_sinu_lip : ULip (fun x => sin (cf_u p D x)).
Proof. cf_ulip. Qed.
Lemma cf_ucosu_lip : ULip (fun x => cf_u p D x * cos (cf_u p D x)).
Proof. cf_ulip. Qed.
Lemma cf_usinu_lip : ULip (fun x => cf_u p D x * sin (cf_u p D x)).
Proof. cf_ulip. Qed.
Lemma cf_ecosu_lip : ULip (fun x => cf_e D x * cos (cf_u p D x)).
Proof. cf_ulip. Qed.
Lemma cf_esinu_lip : ULip (fun x => cf_e D x * sin (cf_u p D x)).
Proof. cf_ulip. Qed.
Lemma cf_cosb_lip : ULip (fun x => cos (cf_b p D x)).
Proof. cf_ulip. Qed.
Lemma cf_ecosb_lip : ULip (fun x => cos (cf_b p D x) * cf_e D x).
Proof. cf_ulip. Qed.

Let A := uint (cf_cc p D) cf_cc_lip.
Let B := uint (cf_cs p D) cf_cs_lip.
Let Ae := uint (fun x => cf_e D x * cf_cc p D x) cf_ecc_lip.
Let Be := uint (fun x => cf_e D x * cf_cs p D x) cf_ecs_lip.
Let P := uint (fun x => cos (cf_u p D x)) cf_cosu_lip.
Let Q := uint (fun x => sin (cf_u p D x)) cf_sinu_lip.
Let Rm := uint (fun x => cf_u p D x * cos (cf_u p D x)) cf_ucosu_lip.
Let Tm := uint (fun x => cf_u p D x * sin (cf_u p D x)) cf_usinu_lip.
Let Pe := uint (fun x => cf_e D x * cos (cf_u p D x)) cf_ecosu_lip.
Let Qe := uint (fun x => cf_e D x * sin (cf_u p D x)) cf_esinu_lip.
Let C0 := uint (fun x => cos (cf_b p D x)) cf_cosb_lip.
Let E1 := uint (fun x => cos (cf_b p D x) * cf_e D x) cf_ecosb_lip.

Lemma cf_ss_zero : uint (cf_ss p D) cf_ss_lip = 0.
Proof. apply uint_odd. intros x _. apply cf_ss_refl. Qed.

Lemma cf_sc_zero : uint (cf_sc p D) cf_sc_lip = 0.
Proof. apply uint_odd. intros x _. apply cf_sc_refl. Qed.

Lemma cf_ess_zero : uint (fun x => cf_e D x * cf_ss p D x) cf_ess_lip = 0.
Proof. apply uint_odd. intros x _. rewrite cf_e_refl, cf_ss_refl. ring. Qed.

Lemma cf_esc_zero : uint (fun x => cf_e D x * cf_sc p D x) cf_esc_lip = 0.
Proof. apply uint_odd. intros x _. rewrite cf_e_refl, cf_sc_refl. ring. Qed.

Lemma cf_P_split : P = ca * A - sa * B.
Proof.
  unfold P.
  rewrite (uint_lincomb
             (ut ca (cf_cc p D) cf_cc_lip :: ut (- sa) (cf_cs p D) cf_cs_lip
              :: ut (- ca) (cf_ss p D) cf_ss_lip
              :: ut (- sa) (cf_sc p D) cf_sc_lip :: nil)).
  - cbn [lc_int ut]. rewrite cf_ss_zero, cf_sc_zero. fold A B. ring.
  - intros x _. cbn [lc_fun ut]. rewrite cf_cos_split. fold W ca sa. ring.
Qed.

Lemma cf_Q_split : Q = sa * A + ca * B.
Proof.
  unfold Q.
  rewrite (uint_lincomb
             (ut sa (cf_cc p D) cf_cc_lip :: ut ca (cf_cs p D) cf_cs_lip
              :: ut (- sa) (cf_ss p D) cf_ss_lip
              :: ut ca (cf_sc p D) cf_sc_lip :: nil)).
  - cbn [lc_int ut]. rewrite cf_ss_zero, cf_sc_zero. fold A B. ring.
  - intros x _. cbn [lc_fun ut]. rewrite cf_sin_split. fold W ca sa. ring.
Qed.

Lemma cf_Pe_split : Pe = ca * Ae - sa * Be.
Proof.
  unfold Pe.
  rewrite (uint_lincomb
             (ut ca _ cf_ecc_lip :: ut (- sa) _ cf_ecs_lip
              :: ut (- ca) _ cf_ess_lip :: ut (- sa) _ cf_esc_lip :: nil)).
  - cbn [lc_int ut]. rewrite cf_ess_zero, cf_esc_zero. fold Ae Be. ring.
  - intros x _. cbn [lc_fun ut]. rewrite cf_cos_split. fold W ca sa. ring.
Qed.

Lemma cf_Qe_split : Qe = sa * Ae + ca * Be.
Proof.
  unfold Qe.
  rewrite (uint_lincomb
             (ut sa _ cf_ecc_lip :: ut ca _ cf_ecs_lip
              :: ut (- sa) _ cf_ess_lip :: ut ca _ cf_esc_lip :: nil)).
  - cbn [lc_int ut]. rewrite cf_ess_zero, cf_esc_zero. fold Ae Be. ring.
  - intros x _. cbn [lc_fun ut]. rewrite cf_sin_split. fold W ca sa. ring.
Qed.

(* Integration by parts, twice. *)

Lemma cf_parts_cos : P - Tm - Qe + kq * Q = (cos W + 1) / 2.
Proof.
  assert (Hl : ULip (fun x => cos (cf_u p D x)
                              - (x - / 2) * (p + D * x) * sin (cf_u p D x)))
    by cf_ulip.
  transitivity (uint _ Hl).
  - rewrite (uint_lincomb
               (ut 1 _ cf_cosu_lip :: ut (- 1) _ cf_usinu_lip
                :: ut (- 1) _ cf_esinu_lip :: ut kq _ cf_sinu_lip :: nil)).
    + cbn [lc_int ut]. fold P Q Tm Qe. ring.
    + intros x _. cbn [lc_fun ut]. unfold kq, W. cf_unfold. field.
  - rewrite (uint_ftc _ Hl (fun x => (x - / 2) * cos (cf_u p D x))).
    + replace (cf_u p D 1) with W by (unfold W; cf_unfold; field).
      replace (cf_u p D 0) with 0 by (cf_unfold; field).
      rewrite cos_0. field.
    + intros x _. apply (deriv_half_cos (cf_u p D) x (p + D * x)).
      apply deriv_quad_heading.
Qed.

Lemma cf_parts_sin : Q + Rm + Pe - kq * P = sin W / 2.
Proof.
  assert (Hl : ULip (fun x => sin (cf_u p D x)
                              + (x - / 2) * (p + D * x) * cos (cf_u p D x)))
    by cf_ulip.
  transitivity (uint _ Hl).
  - rewrite (uint_lincomb
               (ut 1 _ cf_sinu_lip :: ut 1 _ cf_ucosu_lip
                :: ut 1 _ cf_ecosu_lip :: ut (- kq) _ cf_cosu_lip :: nil)).
    + cbn [lc_int ut]. fold P Q Rm Pe. ring.
    + intros x _. cbn [lc_fun ut]. unfold kq, W. cf_unfold. field.
  - rewrite (uint_ftc _ Hl (fun x => (x - / 2) * sin (cf_u p D x))).
    + replace (cf_u p D 1) with W by (unfold W; cf_unfold; field).
      replace (cf_u p D 0) with 0 by (cf_unfold; field).
      rewrite sin_0. field.
    + intros x _. apply (deriv_half_sin (cf_u p D) x (p + D * x)).
      apply deriv_quad_heading.
Qed.

Lemma cf_identity :
  P * (P - Tm) + Q * (Q + Rm) = ca * A + (A * Be - B * Ae).
Proof.
  pose proof cf_parts_cos as H1. pose proof cf_parts_sin as H2.
  assert (HcW : cos W = 2 * ca * ca - 1).
  { replace W with (2 * (W / 2)) at 1 by field. apply cos_2a_cos. }
  assert (HsW : sin W = 2 * sa * ca).
  { replace W with (2 * (W / 2)) at 1 by field. apply sin_2a. }
  assert (Hcs : ca * ca + sa * sa = 1).
  { pose proof (sin2_cos2 (W / 2)) as H. unfold Rsqr in H. fold ca sa in H. lra. }
  rewrite HcW in H1. rewrite HsW in H2.
  assert (HTm : P - Tm = ca * ca + Qe - kq * Q) by lra.
  assert (HRm : Q + Rm = sa * ca - Pe + kq * P) by lra.
  rewrite HTm, HRm, cf_P_split, cf_Q_split, cf_Pe_split, cf_Qe_split.
  replace (ca * A + (A * Be - B * Ae))
    with ((ca * ca + sa * sa) * (ca * A + (A * Be - B * Ae)))
    by (rewrite Hcs; ring).
  ring.
Qed.

(* Positivity on the branch. *)

Hypothesis Hbr : Rabs p + Rabs D / 2 < PI.

Lemma cf_W_lt : Rabs W < PI.
Proof. unfold W, cf_W. split_Rabs; lra. Qed.

Lemma cf_b_bound :
  forall x, 0 <= x <= 1 -> Rabs (cf_b p D x) <= Rabs W / 2.
Proof.
  intros x Hx. unfold cf_b. fold W. rewrite Rabs_mult.
  assert (Hh : Rabs (x - / 2) <= / 2) by (split_Rabs; lra).
  pose proof (Rabs_pos W). nra.
Qed.

Lemma cf_e_bound :
  forall x, 0 <= x <= 1 -> Rabs (cf_e D x) <= Rabs D / 8.
Proof.
  intros x Hx. unfold cf_e.
  assert (Hq : 0 <= x * (1 - x) <= / 4).
  { pose proof (Rle_0_sqr (x - / 2)) as Hs. unfold Rsqr in Hs. split; nra. }
  replace (D * x * (x - 1) / 2) with (- (D * (x * (1 - x) / 2))) by field.
  rewrite Rabs_Ropp, Rabs_mult.
  rewrite (Rabs_pos_eq (x * (1 - x) / 2)) by lra.
  pose proof (Rabs_pos D). nra.
Qed.

Lemma cf_cosb_ge :
  forall x, 0 <= x <= 1 -> cos (Rabs W / 2) <= cos (cf_b p D x).
Proof.
  intros x Hx. pose proof cf_W_lt. pose proof (Rabs_pos W).
  apply cos_abs_ge; [apply cf_b_bound; exact Hx | lra].
Qed.

Lemma cf_cosW_pos : 0 < cos (Rabs W / 2).
Proof.
  pose proof cf_W_lt. pose proof (Rabs_pos W). apply cos_gt_0; lra.
Qed.

Lemma cf_e_quarter :
  forall x, 0 <= x <= 1 -> Rabs (cf_e D x) <= PI / 4.
Proof.
  intros x Hx. pose proof (cf_e_bound x Hx). pose proof (Rabs_pos p). lra.
Qed.

Lemma cf_ca_pos : 0 < ca.
Proof.
  unfold ca. pose proof cf_W_lt as H.
  apply cos_gt_0; split_Rabs; lra.
Qed.

Lemma cf_cose_ge :
  forall x, 0 <= x <= 1 -> cos (PI / 4) <= cos (cf_e D x).
Proof.
  intros x Hx. pose proof PI_RGT_0.
  apply cos_abs_ge; [apply cf_e_quarter; exact Hx | lra].
Qed.

Lemma cf_cos_quarter_pos : 0 < cos (PI / 4).
Proof. pose proof PI_RGT_0. apply cos_gt_0; lra. Qed.

Lemma cf_A_pos : 0 < A.
Proof.
  pose proof cf_cosW_pos as H1. pose proof cf_cos_quarter_pos as H2.
  apply Rlt_le_trans with (cos (Rabs W / 2) * cos (PI / 4)).
  - apply Rmult_lt_0_compat; assumption.
  - unfold A. apply uint_ge_const. intros x Hx. unfold cf_cc.
    pose proof (cf_cosb_ge x Hx). pose proof (cf_cose_ge x Hx).
    apply Rmult_le_compat; lra.
Qed.

Lemma cf_B_le_A : - A <= B <= A.
Proof.
  assert (Hpt : forall x, 0 <= x <= 1 ->
            - cf_cc p D x <= cf_cs p D x <= cf_cc p D x).
  { intros x Hx. unfold cf_cc, cf_cs.
    pose proof (cf_cosb_ge x Hx). pose proof cf_cosW_pos.
    pose proof (sin_le_cos_quarter _ (cf_e_quarter x Hx)). split; nra. }
  split.
  - assert (Hl : ULip (fun x => -1 * cf_cc p D x)) by cf_ulip.
    replace (- A) with (-1 * A) by ring. unfold A.
    rewrite <- (uint_scal (-1) (cf_cc p D) cf_cc_lip Hl).
    unfold B. apply uint_le. intros x Hx. pose proof (Hpt x Hx). lra.
  - unfold A, B. apply uint_le. intros x Hx. apply (Hpt x Hx).
Qed.

Lemma cf_C0_pos : 0 < C0.
Proof.
  apply Rlt_le_trans with (cos (Rabs W / 2)); [apply cf_cosW_pos|].
  unfold C0. apply uint_ge_const. exact cf_cosb_ge.
Qed.

Let th := E1 / C0.

Lemma cf_th_bound : Rabs th <= PI / 4.
Proof.
  pose proof cf_C0_pos as HC.
  assert (Hl : ULip (fun x => PI / 4 * cos (cf_b p D x))) by cf_ulip.
  assert (Hl' : ULip (fun x => - (PI / 4) * cos (cf_b p D x))) by cf_ulip.
  assert (Hpt : forall x, 0 <= x <= 1 ->
            - (PI / 4) * cos (cf_b p D x) <= cos (cf_b p D x) * cf_e D x
            <= PI / 4 * cos (cf_b p D x)).
  { intros x Hx. pose proof (cf_cosb_ge x Hx). pose proof cf_cosW_pos.
    pose proof (cf_e_quarter x Hx) as He.
    assert (He' : - (PI / 4) <= cf_e D x <= PI / 4) by (split_Rabs; lra).
    split; nra. }
  assert (Hup : E1 <= PI / 4 * C0).
  { unfold C0. rewrite <- (uint_scal (PI / 4) _ cf_cosb_lip Hl).
    unfold E1. apply uint_le. intros x Hx. apply (Hpt x Hx). }
  assert (Hlo : - (PI / 4) * C0 <= E1).
  { unfold C0. rewrite <- (uint_scal (- (PI / 4)) _ cf_cosb_lip Hl').
    unfold E1. apply uint_le. intros x Hx. apply (Hpt x Hx). }
  assert (Hth : th * C0 = E1) by (unfold th; field; lra).
  apply Rabs_le. split.
  - apply Rmult_le_reg_r with C0; [exact HC | lra].
  - apply Rmult_le_reg_r with C0; [exact HC | lra].
Qed.

Let nf (y : R) : R := A * sin y - B * cos y.

Lemma cf_nf_mono :
  forall x y, Rabs x <= PI / 4 -> Rabs y <= PI / 4 ->
    0 <= (x - y) * (nf x - nf y).
Proof.
  intros x y Hx Hy. unfold nf.
  replace (A * sin x - B * cos x - (A * sin y - B * cos y))
    with (A * (sin x - sin y) - B * (cos x - cos y)) by ring.
  rewrite form4, form2.
  set (d := (x - y) / 2). set (s := (x + y) / 2).
  pose proof PI_RGT_0 as Hpi.
  assert (Hd : Rabs d <= PI) by (unfold d; split_Rabs; lra).
  assert (Hs : Rabs s <= PI / 4) by (unfold s; split_Rabs; lra).
  pose proof (id_sin_nonneg d Hd) as Hds.
  pose proof (sin_le_cos_quarter s Hs) as [Hs1 Hs2].
  pose proof cf_B_le_A as [HB1 HB2].
  assert (Hk : 0 <= A * cos s + B * sin s).
  { assert (0 <= (A - B) * (cos s - sin s)) by (apply Rmult_le_pos; lra).
    assert (0 <= (A + B) * (cos s + sin s)) by (apply Rmult_le_pos; lra).
    lra. }
  replace (x - y) with (2 * d) by (unfold d; field).
  replace (2 * d * (A * (2 * cos s * sin d) - B * (-2 * sin d * sin s)))
    with (4 * ((d * sin d) * (A * cos s + B * sin s))) by ring.
  apply Rmult_le_pos; [lra | apply Rmult_le_pos; assumption].
Qed.

Lemma cf_cross_nonneg : 0 <= A * Be - B * Ae.
Proof.
  assert (Hl : ULip (fun x => cos (cf_b p D x)
                     * ((cf_e D x - th) * (nf (cf_e D x) - nf th))))
    by (unfold nf; cf_ulip).
  assert (Hth : th * C0 = E1).
  { unfold th. field. pose proof cf_C0_pos. lra. }
  assert (Heq : uint _ Hl = A * Be - B * Ae).
  { rewrite (uint_lincomb
               (ut A _ cf_ecs_lip :: ut (- B) _ cf_ecc_lip
                :: ut (- th * A) _ cf_cs_lip :: ut (th * B) _ cf_cc_lip
                :: ut (- nf th) _ cf_ecosb_lip
                :: ut (th * nf th) _ cf_cosb_lip :: nil)).
    - cbn [lc_int ut]. fold A B Ae Be C0 E1. rewrite <- Hth. ring.
    - intros x _. cbn [lc_fun ut]. unfold nf, cf_cc, cf_cs. ring. }
  rewrite <- Heq. apply uint_ge_const. intros x Hx.
  apply Rmult_le_pos.
  - pose proof (cf_cosb_ge x Hx). pose proof cf_cosW_pos. lra.
  - apply cf_nf_mono; [apply cf_e_quarter; exact Hx | apply cf_th_bound].
Qed.

Lemma cf_core_pos : 0 < P * (P - Tm) + Q * (Q + Rm).
Proof.
  rewrite cf_identity.
  pose proof cf_ca_pos. pose proof cf_A_pos. pose proof cf_cross_nonneg.
  assert (0 < ca * A) by (apply Rmult_lt_0_compat; assumption). lra.
Qed.

End Core.

Theorem clothoid_fprime_core_pos :
  forall p D
    (HP : ULip (fun x => cos (cf_u p D x)))
    (HQ : ULip (fun x => sin (cf_u p D x)))
    (HR : ULip (fun x => cf_u p D x * cos (cf_u p D x)))
    (HT : ULip (fun x => cf_u p D x * sin (cf_u p D x))),
    Rabs p + Rabs D / 2 < PI ->
    0 < uint _ HP * (uint _ HP - uint _ HT) + uint _ HQ * (uint _ HQ + uint _ HR).
Proof.
  intros p D HP HQ HR HT Hbr.
  pose proof (cf_core_pos p D Hbr) as H.
  rewrite (uint_ext _ _ HP (cf_cosu_lip p D)) by (intros; reflexivity).
  rewrite (uint_ext _ _ HQ (cf_sinu_lip p D)) by (intros; reflexivity).
  rewrite (uint_ext _ _ HR (cf_ucosu_lip p D)) by (intros; reflexivity).
  rewrite (uint_ext _ _ HT (cf_usinu_lip p D)) by (intros; reflexivity).
  exact H.
Qed.

Print Assumptions clothoid_fprime_core_pos.
