(* ============================================================================
   NetTopologySuite.Proofs.ClothoidResidual
   ----------------------------------------------------------------------------
   Chord-length residual of a clothoid, on the Stdlib dyadic integral.

   The unit moments (the formulas already stated for this file) are
     P(L) = ∫_0^1 cos(L * psi(tau)) dtau,
     Q(L) = ∫_0^1 sin(L * psi(tau)) dtau,
     psi(tau) = k0 * tau + (k1 - k0) * tau^2 / 2,
   and f(L) = L^2 * (P^2 + Q^2) - d^2,
   f'(L) = 2 L (P^2 + Q^2) + 2 L^2 (Q R - P T),
   with R = ∫ psi cos, T = ∫ psi sin.  The heading along arc length is
     theta(s; L) = k0 * s + (k1 - k0) * s^2 / (2 L)  (L ≠ 0),
   and theta(L * tau; L) = L * psi(tau), so the integrands of P and Q
   are the rescaled integrands cos(theta(L*tau; L)) and sin.  The spatial
   moments are L * P and L * Q.

   H_deriv is the Leibniz rule on that fixed domain [0, 1].  The uniform
   modulus is K = clothoid_kappa^2: |psi| <= clothoid_kappa on [0, 1], and
   LipIntLeibniz.cos_quot_modulus / sin_quot_modulus give an error
   <= psi(tau)^2 * |k| <= K * |k|.

   H_fprime_pos is proved on the half-branch |clothoid_kappa * L| <= 1/2
   (clothoid_L_unique_half_branch).  |kappa * L| is the total turning.
   The full branch |kappa * L| <= PI stays clothoid_L_unique_on_branch,
   with the single premise ClothoidFPrimePos (H_deriv and H_mvt are gone).
   A circular arc has f' = 0 at the endpoint, so the closed bound is not
   strict.  The cos lower bound cannot reach PI.  The intended discharge
   of the open gap is geometric: while the total turning is below PI,
   every tangent has a positive component along the chord, and that
   chord direction is an atan3/atan2 angle already in the corpus.
   f'' and the Kantorovich check are not this file.

   claimId: the residual headline keeps its existing (unnamed) claim.
   No Admitted / Axiom / Parameter.  No MVT, Rolle, RiemannInt, Coquelicot.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import Real RealMonotone Azimuth.
From NTS.Proofs Require Import LipInt LipIntLeibniz.
Local Open Scope R_scope.

Definition clothoid_psi (k0 k1 tau : R) : R :=
  k0 * tau + (k1 - k0) * tau * tau / 2.

Definition clothoid_theta (k0 k1 L s : R) : R :=
  k0 * s + (k1 - k0) * s * s / (2 * L).

Definition clothoid_kappa (k0 k1 : R) : R :=
  Rabs k0 + Rabs (k1 - k0) / 2.

Definition lip_psi (k0 k1 : R) : R := Rabs k0 + Rabs (k1 - k0).

Definition lip_g (k0 k1 L : R) : R := Rabs L * lip_psi k0 k1.

Definition lip_h (k0 k1 L : R) : R :=
  (clothoid_kappa k0 k1 * Rabs L + 1) * lip_psi k0 k1.

Definition g_cos (k0 k1 tau L : R) : R :=
  cos (L * clothoid_psi k0 k1 tau).

Definition g_sin (k0 k1 tau L : R) : R :=
  sin (L * clothoid_psi k0 k1 tau).

Definition unit_cos (k0 k1 tau L : R) : R :=
  clothoid_psi k0 k1 tau * cos (L * clothoid_psi k0 k1 tau).

Definition unit_sin (k0 k1 tau L : R) : R :=
  clothoid_psi k0 k1 tau * sin (L * clothoid_psi k0 k1 tau).

Definition h_cos (k0 k1 tau L : R) : R := - unit_sin k0 k1 tau L.

Definition h_sin (k0 k1 tau L : R) : R := unit_cos k0 k1 tau L.

Lemma theta_on_unit :
  forall k0 k1 L tau,
    L <> 0 ->
    clothoid_theta k0 k1 L (L * tau) = L * clothoid_psi k0 k1 tau.
Proof.
  intros. unfold clothoid_theta, clothoid_psi. field. assumption.
Qed.

Lemma abs_sin_le_1 : forall u, Rabs (sin u) <= 1.
Proof.
  intro u. pose proof (SIN_bound u) as Hb.
  destruct (Rle_lt_dec 0 (sin u)) as [Hp|Hn].
  - rewrite Rabs_pos_eq by exact Hp. lra.
  - rewrite Rabs_left by exact Hn. lra.
Qed.

Lemma abs_cos_le_1 : forall u, Rabs (cos u) <= 1.
Proof.
  intro u. pose proof (COS_bound u) as Hb.
  destruct (Rle_lt_dec 0 (cos u)) as [Hp|Hn].
  - rewrite Rabs_pos_eq by exact Hp. lra.
  - rewrite Rabs_left by exact Hn. lra.
Qed.

Lemma psi_abs_le :
  forall k0 k1 tau,
    0 <= tau <= 1 ->
    Rabs (clothoid_psi k0 k1 tau) <= clothoid_kappa k0 k1.
Proof.
  intros k0 k1 tau Ht. unfold clothoid_psi, clothoid_kappa.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat.
  - rewrite Rabs_mult. rewrite (Rabs_pos_eq tau) by lra.
    apply Rle_trans with (Rabs k0 * 1).
    + apply Rmult_le_compat_l; [apply Rabs_pos | lra].
    + right. ring.
  - unfold Rdiv. rewrite Rabs_mult.
    rewrite (Rabs_right (/ 2)); [| apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; lra].
    rewrite Rabs_mult. rewrite (Rabs_pos_eq tau) by lra.
    rewrite Rabs_mult. rewrite (Rabs_pos_eq tau) by lra.
    apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; lra|].
    apply Rle_trans with ((Rabs (k1 - k0) * tau) * 1).
    + apply Rmult_le_compat_l; [apply Rmult_le_pos; [apply Rabs_pos | lra] | lra].
    + apply Rle_trans with (Rabs (k1 - k0) * 1).
      * replace ((Rabs (k1 - k0) * tau) * 1) with (Rabs (k1 - k0) * tau) by ring.
        apply Rmult_le_compat_l; [apply Rabs_pos | lra].
      * right. ring.
Qed.

Lemma psi_diff_factor :
  forall k0 k1 x y,
    clothoid_psi k0 k1 x - clothoid_psi k0 k1 y =
    (x - y) * (k0 + (k1 - k0) * (x + y) / 2).
Proof.
  intros. unfold clothoid_psi. field.
Qed.

Lemma psi_lip_on_unit :
  forall k0 k1 x y,
    0 <= x <= 1 -> 0 <= y <= 1 ->
    Rabs (clothoid_psi k0 k1 x - clothoid_psi k0 k1 y)
      <= lip_psi k0 k1 * Rabs (x - y).
Proof.
  intros k0 k1 x y Hx Hy.
  rewrite psi_diff_factor, Rabs_mult.
  rewrite (Rmult_comm (lip_psi k0 k1) (Rabs (x - y))).
  apply Rmult_le_compat_l; [apply Rabs_pos|].
  eapply Rle_trans; [apply Rabs_triang|].
  unfold lip_psi. apply Rplus_le_compat.
  - apply Rle_refl.
  - unfold Rdiv. rewrite Rabs_mult.
    rewrite (Rabs_right (/ 2)); [| apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; lra].
    rewrite Rabs_mult.
    assert (Hxy : Rabs (x + y) <= 2).
    { rewrite Rabs_pos_eq by lra. lra. }
    apply Rle_trans with (Rabs (k1 - k0) * 2 * / 2).
    + apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; lra|].
      apply Rmult_le_compat_l; [apply Rabs_pos | exact Hxy].
    + right. field.
Qed.

Lemma prod_diff_abs :
  forall a b c d,
    Rabs (a * b - c * d) <= Rabs a * Rabs (b - d) + Rabs d * Rabs (a - c).
Proof.
  intros a b c d.
  replace (a * b - c * d) with (a * (b - d) + d * (a - c)) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_mult, Rabs_mult. apply Rle_refl.
Qed.

Lemma trig_prod_lip :
  forall (F : R -> R) k0 k1 L x y,
    (forall u v, Rabs (F u - F v) <= Rabs (u - v)) ->
    (forall u, Rabs (F u) <= 1) ->
    0 <= x <= 1 -> 0 <= y <= 1 ->
    Rabs (clothoid_psi k0 k1 x * F (L * clothoid_psi k0 k1 x)
          - clothoid_psi k0 k1 y * F (L * clothoid_psi k0 k1 y))
      <= lip_h k0 k1 L * Rabs (x - y).
Proof.
  intros F k0 k1 L x y HFlip HFbd Hx Hy.
  set (px := clothoid_psi k0 k1 x). set (py := clothoid_psi k0 k1 y).
  eapply Rle_trans; [apply (prod_diff_abs px (F (L * px)) py (F (L * py)))|].
  assert (Hdpsi : Rabs (px - py) <= lip_psi k0 k1 * Rabs (x - y)).
  { unfold px, py. apply psi_lip_on_unit; assumption. }
  assert (Hpx : Rabs px <= clothoid_kappa k0 k1).
  { unfold px. apply psi_abs_le. exact Hx. }
  assert (HdF : Rabs (F (L * px) - F (L * py)) <= Rabs L * Rabs (px - py)).
  { eapply Rle_trans; [apply HFlip|].
    replace (L * px - L * py) with (L * (px - py)) by ring.
    rewrite Rabs_mult. apply Rle_refl. }
  assert (H1 : Rabs px * Rabs (F (L * px) - F (L * py))
               <= clothoid_kappa k0 k1 * Rabs L * Rabs (px - py)).
  { apply Rle_trans with (clothoid_kappa k0 k1 * (Rabs L * Rabs (px - py))).
    - apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hpx | exact HdF].
    - right. ring. }
  assert (H2 : Rabs (F (L * py)) * Rabs (px - py) <= 1 * Rabs (px - py)).
  { apply Rmult_le_compat_r; [apply Rabs_pos |]. apply HFbd. }
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact H1 | exact H2].
  - replace (clothoid_kappa k0 k1 * Rabs L * Rabs (px - py) + 1 * Rabs (px - py))
      with ((clothoid_kappa k0 k1 * Rabs L + 1) * Rabs (px - py)) by ring.
    unfold lip_h. rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    + apply Rplus_le_le_0_compat; [| lra].
      apply Rmult_le_pos; [| apply Rabs_pos].
      apply Rle_trans with (Rabs px); [apply Rabs_pos | exact Hpx].
    + exact Hdpsi.
Qed.

Lemma lip_g_nn : forall k0 k1 L, 0 <= lip_g k0 k1 L.
Proof.
  intros. unfold lip_g, lip_psi.
  apply Rmult_le_pos; [apply Rabs_pos|].
  apply Rplus_le_le_0_compat; apply Rabs_pos.
Qed.

Lemma lip_h_nn : forall k0 k1 L, 0 <= lip_h k0 k1 L.
Proof.
  intros. unfold lip_h, lip_psi, clothoid_kappa.
  apply Rmult_le_pos.
  - apply Rplus_le_le_0_compat; [| lra].
    apply Rmult_le_pos.
    + apply Rplus_le_le_0_compat; [apply Rabs_pos|].
      apply Rmult_le_pos; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra].
    + apply Rabs_pos.
  - apply Rplus_le_le_0_compat; apply Rabs_pos.
Qed.

Lemma lip_g_ok :
  forall k0 k1 L x y,
    0 <= x <= 1 -> 0 <= y <= 1 ->
    Rabs (g_cos k0 k1 x L - g_cos k0 k1 y L)
      <= lip_g k0 k1 L * Rabs (x - y).
Proof.
  intros k0 k1 L x y Hx Hy. unfold g_cos.
  eapply Rle_trans; [apply cos_lip|].
  replace (L * clothoid_psi k0 k1 x - L * clothoid_psi k0 k1 y)
    with (L * (clothoid_psi k0 k1 x - clothoid_psi k0 k1 y)) by ring.
  rewrite Rabs_mult. unfold lip_g. rewrite Rmult_assoc.
  apply Rmult_le_compat_l; [apply Rabs_pos|].
  apply psi_lip_on_unit; assumption.
Qed.

Lemma lip_gsin_ok :
  forall k0 k1 L x y,
    0 <= x <= 1 -> 0 <= y <= 1 ->
    Rabs (g_sin k0 k1 x L - g_sin k0 k1 y L)
      <= lip_g k0 k1 L * Rabs (x - y).
Proof.
  intros k0 k1 L x y Hx Hy. unfold g_sin.
  eapply Rle_trans; [apply sin_lip|].
  replace (L * clothoid_psi k0 k1 x - L * clothoid_psi k0 k1 y)
    with (L * (clothoid_psi k0 k1 x - clothoid_psi k0 k1 y)) by ring.
  rewrite Rabs_mult. unfold lip_g. rewrite Rmult_assoc.
  apply Rmult_le_compat_l; [apply Rabs_pos|].
  apply psi_lip_on_unit; assumption.
Qed.

Lemma lip_unit_cos_ok :
  forall k0 k1 L x y,
    0 <= x <= 1 -> 0 <= y <= 1 ->
    Rabs (unit_cos k0 k1 x L - unit_cos k0 k1 y L)
      <= lip_h k0 k1 L * Rabs (x - y).
Proof.
  intros. unfold unit_cos.
  apply trig_prod_lip; [apply cos_lip | apply abs_cos_le_1 | assumption | assumption].
Qed.

Lemma lip_unit_sin_ok :
  forall k0 k1 L x y,
    0 <= x <= 1 -> 0 <= y <= 1 ->
    Rabs (unit_sin k0 k1 x L - unit_sin k0 k1 y L)
      <= lip_h k0 k1 L * Rabs (x - y).
Proof.
  intros. unfold unit_sin.
  apply trig_prod_lip; [apply sin_lip | apply abs_sin_le_1 | assumption | assumption].
Qed.

Lemma lip_h_cos_ok :
  forall k0 k1 L x y,
    0 <= x <= 1 -> 0 <= y <= 1 ->
    Rabs (h_cos k0 k1 x L - h_cos k0 k1 y L)
      <= lip_h k0 k1 L * Rabs (x - y).
Proof.
  intros k0 k1 L x y Hx Hy. unfold h_cos.
  replace (- unit_sin k0 k1 x L - - unit_sin k0 k1 y L)
    with (- (unit_sin k0 k1 x L - unit_sin k0 k1 y L)) by ring.
  rewrite Rabs_Ropp. apply lip_unit_sin_ok; assumption.
Qed.

Lemma lip_h_sin_ok :
  forall k0 k1 L x y,
    0 <= x <= 1 -> 0 <= y <= 1 ->
    Rabs (h_sin k0 k1 x L - h_sin k0 k1 y L)
      <= lip_h k0 k1 L * Rabs (x - y).
Proof.
  intros. unfold h_sin. apply lip_unit_cos_ok; assumption.
Qed.

Definition clothoid_P (k0 k1 : R) : R -> R :=
  pint (g_cos k0 k1) (lip_g k0 k1) (lip_g_nn k0 k1) (lip_g_ok k0 k1).

Definition clothoid_Q (k0 k1 : R) : R -> R :=
  pint (g_sin k0 k1) (lip_g k0 k1) (lip_g_nn k0 k1) (lip_gsin_ok k0 k1).

Definition clothoid_R (k0 k1 : R) : R -> R :=
  pint (unit_cos k0 k1) (lip_h k0 k1) (lip_h_nn k0 k1) (lip_unit_cos_ok k0 k1).

Definition clothoid_T (k0 k1 : R) : R -> R :=
  pint (unit_sin k0 k1) (lip_h k0 k1) (lip_h_nn k0 k1) (lip_unit_sin_ok k0 k1).

Definition clothoid_Pp (k0 k1 : R) : R -> R :=
  pint (h_cos k0 k1) (lip_h k0 k1) (lip_h_nn k0 k1) (lip_h_cos_ok k0 k1).

Definition clothoid_Qp (k0 k1 : R) : R -> R :=
  pint (h_sin k0 k1) (lip_h k0 k1) (lip_h_nn k0 k1) (lip_h_sin_ok k0 k1).

Definition clothoid_S (k0 k1 L : R) : R :=
  clothoid_P k0 k1 L * clothoid_P k0 k1 L +
  clothoid_Q k0 k1 L * clothoid_Q k0 k1 L.

Definition clothoid_f (k0 k1 d L : R) : R :=
  L * L * clothoid_S k0 k1 L - d * d.

Definition clothoid_f' (k0 k1 L : R) : R :=
  2 * L * clothoid_S k0 k1 L +
  2 * L * L * (clothoid_Q k0 k1 L * clothoid_R k0 k1 L -
               clothoid_P k0 k1 L * clothoid_T k0 k1 L).

Lemma sqr_le_abs :
  forall a b, Rabs a <= b -> a * a <= b * b.
Proof.
  intros a b Hab.
  assert (Hb : 0 <= b).
  { apply Rle_trans with (Rabs a); [apply Rabs_pos | exact Hab]. }
  apply Rle_trans with (Rabs a * Rabs a).
  - right. rewrite <- Rabs_mult. rewrite (Rabs_right (a * a)); [reflexivity|].
    apply Rle_ge, Rle_0_sqr.
  - apply Rmult_le_compat; try apply Rabs_pos; assumption.
Qed.

Lemma gcos_modulus :
  forall k0 k1 tau L k,
    0 <= tau <= 1 -> k <> 0 ->
    Rabs ((g_cos k0 k1 tau (L + k) - g_cos k0 k1 tau L) / k
          - h_cos k0 k1 tau L)
      <= (clothoid_kappa k0 k1 * clothoid_kappa k0 k1) * Rabs k.
Proof.
  intros k0 k1 tau L k Ht Hk.
  unfold g_cos, h_cos, unit_sin.
  replace ((L + k) * clothoid_psi k0 k1 tau)
    with (clothoid_psi k0 k1 tau * (L + k)) by ring.
  replace (L * clothoid_psi k0 k1 tau)
    with (clothoid_psi k0 k1 tau * L) by ring.
  replace (- (clothoid_psi k0 k1 tau * sin (clothoid_psi k0 k1 tau * L)))
    with (- clothoid_psi k0 k1 tau * sin (clothoid_psi k0 k1 tau * L)) by ring.
  eapply Rle_trans.
  - apply cos_quot_modulus. exact Hk.
  - apply Rmult_le_compat_r; [apply Rabs_pos|].
    apply sqr_le_abs. apply psi_abs_le. exact Ht.
Qed.

Lemma gsin_modulus :
  forall k0 k1 tau L k,
    0 <= tau <= 1 -> k <> 0 ->
    Rabs ((g_sin k0 k1 tau (L + k) - g_sin k0 k1 tau L) / k
          - h_sin k0 k1 tau L)
      <= (clothoid_kappa k0 k1 * clothoid_kappa k0 k1) * Rabs k.
Proof.
  intros k0 k1 tau L k Ht Hk.
  unfold g_sin, h_sin, unit_cos.
  replace ((L + k) * clothoid_psi k0 k1 tau)
    with (clothoid_psi k0 k1 tau * (L + k)) by ring.
  replace (L * clothoid_psi k0 k1 tau)
    with (clothoid_psi k0 k1 tau * L) by ring.
  eapply Rle_trans.
  - apply sin_quot_modulus. exact Hk.
  - apply Rmult_le_compat_r; [apply Rabs_pos|].
    apply sqr_le_abs. apply psi_abs_le. exact Ht.
Qed.

Lemma clothoid_P_deriv :
  forall k0 k1 L,
    derivable_pt_lim (clothoid_P k0 k1) L (clothoid_Pp k0 k1 L).
Proof.
  intros k0 k1 L.
  apply (lint_leibniz (g_cos k0 k1) (h_cos k0 k1)
           (lip_g k0 k1) (lip_h k0 k1)
           (lip_g_nn k0 k1) (lip_g_ok k0 k1)
           (lip_h_nn k0 k1) (lip_h_cos_ok k0 k1)
           L (clothoid_kappa k0 k1 * clothoid_kappa k0 k1) 1).
  - lra.
  - apply Rle_0_sqr.
  - intros tau k Ht Hk _. apply gcos_modulus; assumption.
Qed.

Lemma clothoid_Q_deriv :
  forall k0 k1 L,
    derivable_pt_lim (clothoid_Q k0 k1) L (clothoid_Qp k0 k1 L).
Proof.
  intros k0 k1 L.
  apply (lint_leibniz (g_sin k0 k1) (h_sin k0 k1)
           (lip_g k0 k1) (lip_h k0 k1)
           (lip_g_nn k0 k1) (lip_gsin_ok k0 k1)
           (lip_h_nn k0 k1) (lip_h_sin_ok k0 k1)
           L (clothoid_kappa k0 k1 * clothoid_kappa k0 k1) 1).
  - lra.
  - apply Rle_0_sqr.
  - intros tau k Ht Hk _. apply gsin_modulus; assumption.
Qed.

Lemma Pp_eq_neg_T :
  forall k0 k1 L, clothoid_Pp k0 k1 L = - clothoid_T k0 k1 L.
Proof.
  intros k0 k1 L.
  unfold clothoid_Pp, clothoid_T, h_cos.
  rewrite pint_ext, pint_ext.
  apply (lint_opp (fun tau => unit_sin k0 k1 tau L) 0 1 (lip_h k0 k1 L)
           (lip_h_nn k0 k1 L)
           (fun x y Hx Hy => lip_unit_sin_ok k0 k1 L x y Hx Hy)
           (fun x y Hx Hy => lip_h_cos_ok k0 k1 L x y Hx Hy)
           0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1)
           (Rle_refl 0) Rle_0_1 (Rle_refl 1)).
Qed.

Lemma Qp_eq_R :
  forall k0 k1 L, clothoid_Qp k0 k1 L = clothoid_R k0 k1 L.
Proof.
  intros k0 k1 L.
  unfold clothoid_Qp, clothoid_R, h_sin.
  rewrite pint_ext, pint_ext.
  apply lint_ext. intros t Ht. reflexivity.
Qed.

Lemma zero_lip_const :
  forall (c x y : R),
    Rabs (c - c) <= 0 * Rabs (x - y).
Proof.
  intros. replace (c - c) with 0 by ring.
  rewrite Rabs_R0, Rmult_0_l. apply Rle_refl.
Qed.

Lemma lip_theta_cos :
  forall k0 k1 L (HL : L <> 0) x y,
    0 <= x <= 1 -> 0 <= y <= 1 ->
    Rabs (cos (clothoid_theta k0 k1 L (L * x))
          - cos (clothoid_theta k0 k1 L (L * y)))
      <= lip_g k0 k1 L * Rabs (x - y).
Proof.
  intros k0 k1 L HL x y Hx Hy.
  rewrite (theta_on_unit k0 k1 L x HL), (theta_on_unit k0 k1 L y HL).
  apply lip_g_ok; assumption.
Qed.

Lemma lip_theta_sin :
  forall k0 k1 L (HL : L <> 0) x y,
    0 <= x <= 1 -> 0 <= y <= 1 ->
    Rabs (sin (clothoid_theta k0 k1 L (L * x))
          - sin (clothoid_theta k0 k1 L (L * y)))
      <= lip_g k0 k1 L * Rabs (x - y).
Proof.
  intros k0 k1 L HL x y Hx Hy.
  rewrite (theta_on_unit k0 k1 L x HL), (theta_on_unit k0 k1 L y HL).
  apply lip_gsin_ok; assumption.
Qed.

Lemma clothoid_P_rescaled :
  forall k0 k1 L (HL : L <> 0),
    clothoid_P k0 k1 L =
    lint (fun tau => cos (clothoid_theta k0 k1 L (L * tau)))
      0 1 (lip_g k0 k1 L) (lip_g_nn k0 k1 L)
      (fun x y Hx Hy => lip_theta_cos k0 k1 L HL x y Hx Hy)
      0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1).
Proof.
  intros k0 k1 L HL.
  unfold clothoid_P. rewrite pint_ext.
  apply lint_ext. intros tau Htau.
  unfold g_cos. apply f_equal. symmetry. apply theta_on_unit. exact HL.
Qed.

Lemma clothoid_Q_rescaled :
  forall k0 k1 L (HL : L <> 0),
    clothoid_Q k0 k1 L =
    lint (fun tau => sin (clothoid_theta k0 k1 L (L * tau)))
      0 1 (lip_g k0 k1 L) (lip_g_nn k0 k1 L)
      (fun x y Hx Hy => lip_theta_sin k0 k1 L HL x y Hx Hy)
      0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1).
Proof.
  intros k0 k1 L HL.
  unfold clothoid_Q. rewrite pint_ext.
  apply lint_ext. intros tau Htau.
  unfold g_sin. apply f_equal. symmetry. apply theta_on_unit. exact HL.
Qed.

Lemma clothoid_spatial_P :
  forall k0 k1 L (HL : L <> 0),
    L * clothoid_P k0 k1 L =
    L * lint (fun tau => cos (clothoid_theta k0 k1 L (L * tau)))
          0 1 (lip_g k0 k1 L) (lip_g_nn k0 k1 L)
          (fun x y Hx Hy => lip_theta_cos k0 k1 L HL x y Hx Hy)
          0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1).
Proof.
  intros. apply f_equal. apply clothoid_P_rescaled.
Qed.

Lemma clothoid_spatial_Q :
  forall k0 k1 L (HL : L <> 0),
    L * clothoid_Q k0 k1 L =
    L * lint (fun tau => sin (clothoid_theta k0 k1 L (L * tau)))
          0 1 (lip_g k0 k1 L) (lip_g_nn k0 k1 L)
          (fun x y Hx Hy => lip_theta_sin k0 k1 L HL x y Hx Hy)
          0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1).
Proof.
  intros. apply f_equal. apply clothoid_Q_rescaled.
Qed.

Lemma clothoid_f_deriv :
  forall k0 k1 d L,
    derivable_pt_lim (clothoid_f k0 k1 d) L (clothoid_f' k0 k1 L).
Proof.
  intros k0 k1 d L.
  set (P := clothoid_P k0 k1).
  set (Q := clothoid_Q k0 k1).
  set (Pp := clothoid_Pp k0 k1).
  set (Qp := clothoid_Qp k0 k1).
  assert (HP : derivable_pt_lim P L (Pp L)) by apply clothoid_P_deriv.
  assert (HQ : derivable_pt_lim Q L (Qp L)) by apply clothoid_Q_deriv.
  assert (HPsq : derivable_pt_lim (fun z => P z * P z) L
                   (Pp L * P L + P L * Pp L)).
  { apply derivable_pt_lim_mult; exact HP. }
  assert (HQsq : derivable_pt_lim (fun z => Q z * Q z) L
                   (Qp L * Q L + Q L * Qp L)).
  { apply derivable_pt_lim_mult; exact HQ. }
  assert (HS : derivable_pt_lim (fun z => P z * P z + Q z * Q z) L
                 ((Pp L * P L + P L * Pp L) + (Qp L * Q L + Q L * Qp L))).
  { apply derivable_pt_lim_plus; assumption. }
  assert (Hll : derivable_pt_lim (fun z => z * z) L (1 * L + L * 1)).
  { apply derivable_pt_lim_mult; apply derivable_pt_lim_id. }
  assert (Hprod : derivable_pt_lim
           (fun z => (z * z) * (P z * P z + Q z * Q z)) L
           ((1 * L + L * 1) * (P L * P L + Q L * Q L)
            + (L * L) * ((Pp L * P L + P L * Pp L)
                         + (Qp L * Q L + Q L * Qp L)))).
  { apply (derivable_pt_lim_mult (fun z => z * z)
           (fun z => P z * P z + Q z * Q z)
           L (1 * L + L * 1)
           ((Pp L * P L + P L * Pp L) + (Qp L * Q L + Q L * Qp L))).
    - exact Hll.
    - exact HS. }
  assert (Hraw : derivable_pt_lim
           (fun z => (z * z) * (P z * P z + Q z * Q z) - d * d) L
           (((1 * L + L * 1) * (P L * P L + Q L * Q L)
             + (L * L) * ((Pp L * P L + P L * Pp L)
                          + (Qp L * Q L + Q L * Qp L))) - 0)).
  { apply derivable_pt_lim_minus; [exact Hprod | apply derivable_pt_lim_const]. }
  assert (Hext : derivable_pt_lim (clothoid_f k0 k1 d) L
           (((1 * L + L * 1) * (P L * P L + Q L * Q L)
             + (L * L) * ((Pp L * P L + P L * Pp L)
                          + (Qp L * Q L + Q L * Qp L))) - 0)).
  { eapply derivable_pt_lim_ext; [| exact Hraw].
    intros z. unfold clothoid_f, clothoid_S, P, Q. reflexivity. }
  unfold Pp, Qp in Hext.
  rewrite (Pp_eq_neg_T k0 k1 L) in Hext.
  rewrite (Qp_eq_R k0 k1 L) in Hext.
  replace (clothoid_f' k0 k1 L)
    with (((1 * L + L * 1) * (P L * P L + Q L * Q L)
           + (L * L) * (((- clothoid_T k0 k1 L) * P L
                         + P L * (- clothoid_T k0 k1 L))
                        + (clothoid_R k0 k1 L * Q L
                           + Q L * clothoid_R k0 k1 L))) - 0).
  - exact Hext.
  - unfold clothoid_f', clothoid_S, P, Q. ring.
Qed.

Lemma pint_abs_bound :
  forall g lipg Hn Hlip L M,
    (forall tau, 0 <= tau <= 1 -> Rabs (g tau L) <= M) ->
    Rabs (pint g lipg Hn Hlip L) <= M.
Proof.
  intros g lipg Hn Hlip L M HM.
  rewrite pint_ext.
  eapply Rle_trans; [apply lint_abs_le; exact HM |].
  right. ring.
Qed.

Lemma cos_lower_sqr : forall t, 1 - t * t / 2 <= cos t.
Proof.
  intro t.
  replace t with (2 * (t / 2)) at 3 by field.
  rewrite cos_2a.
  assert (Ec : cos (t / 2) * cos (t / 2) = 1 - sin (t / 2) * sin (t / 2)).
  { pose proof (cos2 (t / 2)) as Hc.
    unfold Rsqr in Hc. rewrite Hc. ring. }
  rewrite Ec.
  assert (Hs : sin (t / 2) * sin (t / 2) <= (t / 2) * (t / 2)).
  { apply Rle_trans with (Rabs (t / 2) * Rabs (t / 2)).
    - apply sqr_le_abs. apply abs_sin_le.
    - right. rewrite <- Rabs_mult.
      rewrite (Rabs_right ((t / 2) * (t / 2))); [reflexivity|].
      apply Rle_ge, Rle_0_sqr. }
  apply Rle_trans with (1 - 2 * ((t / 2) * (t / 2))).
  - right. field.
  - replace ((1 - sin (t / 2) * sin (t / 2)) - sin (t / 2) * sin (t / 2))
      with (1 - 2 * (sin (t / 2) * sin (t / 2))) by ring.
    apply Rplus_le_compat_l. apply Ropp_le_contravar.
    apply Rmult_le_compat_l; [lra | exact Hs].
Qed.

Lemma half_branch_inward :
  forall k0 k1 c L2,
    0 <= c -> c <= L2 ->
    Rabs (clothoid_kappa k0 k1 * L2) <= 1 / 2 ->
    Rabs (clothoid_kappa k0 k1 * c) <= 1 / 2.
Proof.
  intros k0 k1 c L2 Hc0 HcL2 Hb.
  rewrite Rabs_mult in *.
  rewrite (Rabs_pos_eq c) by exact Hc0.
  rewrite (Rabs_pos_eq L2) in Hb by lra.
  apply Rle_trans with (Rabs (clothoid_kappa k0 k1) * L2); [| exact Hb].
  apply Rmult_le_compat_l; [apply Rabs_pos | exact HcL2].
Qed.

Lemma const_le_cos_lip :
  forall (c L k0 k1 x y : R),
    0 <= x <= 1 -> 0 <= y <= 1 ->
    Rabs (c - c) <= 0 * Rabs (x - y).
Proof.
  intros. apply zero_lip_const.
Qed.

Lemma clothoid_fprime_pos :
  forall k0 k1 L,
    0 < L ->
    Rabs (clothoid_kappa k0 k1 * L) <= 1 / 2 ->
    0 < clothoid_f' k0 k1 L.
Proof.
  intros k0 k1 L HL Hb.
  set (kap := clothoid_kappa k0 k1).
  assert (Hkap : 0 <= kap).
  { unfold kap, clothoid_kappa.
    apply Rplus_le_le_0_compat; [apply Rabs_pos|].
    apply Rmult_le_pos; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra]. }
  set (e := kap * L).
  assert (He : 0 <= e <= 1 / 2).
  { unfold e. split.
    - apply Rmult_le_pos; [exact Hkap | lra].
    - replace (kap * L) with (Rabs (kap * L)).
      + exact Hb.
      + rewrite Rabs_pos_eq; [reflexivity|].
        apply Rmult_le_pos; [exact Hkap | lra]. }
  assert (Hth : forall tau, 0 <= tau <= 1 ->
            Rabs (L * clothoid_psi k0 k1 tau) <= e).
  { intros tau Ht. rewrite Rabs_mult. rewrite (Rabs_pos_eq L) by lra.
    unfold e. rewrite (Rmult_comm kap L).
    apply Rmult_le_compat_l; [lra|].
    unfold kap. apply psi_abs_le. exact Ht. }
  assert (Hcos_lo : forall tau, 0 <= tau <= 1 ->
            1 - e * e / 2 <= g_cos k0 k1 tau L).
  { intros tau Ht. unfold g_cos.
    apply Rle_trans with
      (1 - (L * clothoid_psi k0 k1 tau) * (L * clothoid_psi k0 k1 tau) / 2).
    - apply Rplus_le_compat_l. apply Ropp_le_contravar. unfold Rdiv.
      apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra|].
      apply sqr_le_abs. apply Hth. exact Ht.
    - apply cos_lower_sqr. }
  assert (HP : 1 - e * e / 2 <= clothoid_P k0 k1 L).
  { unfold clothoid_P. rewrite pint_ext.
    assert (Hc :
      lint (fun _ : R => 1 - e * e / 2) 0 1 0 (Rle_refl 0)
        (fun x y _ _ => zero_lip_const (1 - e * e / 2) x y)
        0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1)
      <= lint (fun t => g_cos k0 k1 t L) 0 1 (lip_g k0 k1 L) (lip_g_nn k0 k1 L)
           (fun x y Hx Hy => lip_g_ok k0 k1 L x y Hx Hy)
           0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1)).
    { apply lint_le. intros t Ht. apply Hcos_lo. exact Ht. }
    rewrite lint_const in Hc.
    replace ((1 - 0) * (1 - e * e / 2)) with (1 - e * e / 2) in Hc by ring.
    exact Hc. }
  assert (HP78 : 7 / 8 <= clothoid_P k0 k1 L).
  { apply Rle_trans with (1 - e * e / 2); [| exact HP].
    assert (e * e <= 1 / 4) by nra.
    nra. }
  assert (HPsq : 49 / 64 <= clothoid_P k0 k1 L * clothoid_P k0 k1 L).
  { apply Rle_trans with ((7 / 8) * (7 / 8)).
    - nra.
    - apply Rmult_le_compat; try lra; exact HP78. }
  assert (HQ : Rabs (clothoid_Q k0 k1 L) <= e).
  { apply pint_abs_bound. intros tau Ht. unfold g_sin.
    eapply Rle_trans; [apply abs_sin_le | apply Hth; exact Ht]. }
  assert (HR : Rabs (clothoid_R k0 k1 L) <= kap).
  { apply pint_abs_bound. intros tau Ht. unfold unit_cos.
    rewrite Rabs_mult.
    eapply Rle_trans.
    - apply Rmult_le_compat_l; [apply Rabs_pos|]. apply abs_cos_le_1.
    - rewrite Rmult_1_r. unfold kap. apply psi_abs_le. exact Ht. }
  assert (HT : Rabs (clothoid_T k0 k1 L) <= kap).
  { apply pint_abs_bound. intros tau Ht. unfold unit_sin.
    rewrite Rabs_mult.
    eapply Rle_trans.
    - apply Rmult_le_compat_l; [apply Rabs_pos|]. apply abs_sin_le_1.
    - rewrite Rmult_1_r. unfold kap. apply psi_abs_le. exact Ht. }
  assert (HPabs : Rabs (clothoid_P k0 k1 L) <= 1).
  { apply pint_abs_bound. intros tau Ht. unfold g_cos. apply abs_cos_le_1. }
  set (cross := clothoid_Q k0 k1 L * clothoid_R k0 k1 L
                - clothoid_P k0 k1 L * clothoid_T k0 k1 L).
  assert (Hcross : Rabs (L * cross) <= e * e + e).
  { rewrite Rabs_mult. rewrite (Rabs_pos_eq L) by lra.
    eapply Rle_trans.
    - apply Rmult_le_compat_l; [lra|].
      eapply Rle_trans; [apply Rabs_triang|].
      rewrite Rabs_Ropp, Rabs_mult, Rabs_mult.
      apply Rplus_le_compat.
      + apply Rmult_le_compat; try apply Rabs_pos; [apply HQ | apply HR].
      + apply Rmult_le_compat; try apply Rabs_pos; [apply HPabs | apply HT].
    - unfold e. nra. }
  assert (Hsum : 1 / 64 <= clothoid_S k0 k1 L + L * cross).
  { unfold clothoid_S.
    set (p2 := clothoid_P k0 k1 L * clothoid_P k0 k1 L).
    set (q2 := clothoid_Q k0 k1 L * clothoid_Q k0 k1 L).
    set (lc := L * cross).
    set (ac := Rabs lc).
    assert (Hq2 : 0 <= q2) by apply Rle_0_sqr.
    assert (Hlow : - ac <= lc).
    { unfold ac. destruct (Rle_lt_dec 0 lc) as [Hp|Hn].
      - apply Rle_trans with 0; [| exact Hp].
        rewrite <- Ropp_0. apply Ropp_le_contravar. apply Rabs_pos.
      - rewrite (Rabs_left lc Hn). lra. }
    assert (Hdrop : p2 - ac <= p2 + q2 + lc) by lra.
    apply Rle_trans with (p2 - ac).
    - assert (Hgap : 49 / 64 - (e * e + e) <= p2 - ac).
      { apply Rplus_le_compat; [exact HPsq | apply Ropp_le_contravar; exact Hcross]. }
      assert (H64 : 1 / 64 <= 49 / 64 - (e * e + e)) by nra.
      lra.
    - exact Hdrop. }
  assert (Hf' : clothoid_f' k0 k1 L =
                 2 * L * (clothoid_S k0 k1 L + L * cross)).
  { unfold clothoid_f', cross. ring. }
  rewrite Hf'.
  apply Rmult_lt_0_compat; [lra|].
  apply Rlt_le_trans with (1 / 64); [lra | exact Hsum].
Qed.

(* Open gap 0 < |κ L| < π.  |κ L| is the total turning on [0, L].
   A circular arc has derivative 0 at |κ L| = π, so the closed bound is
   not this statement.  cos t ≥ 1 − t²/2 cannot reach π.  Intended
   discharge: while the total turning is below π, every tangent has a
   positive component along the chord direction, so the derivative of
   chord length in L is positive.  That direction is atan3/atan2.
   Uninhabited.  Not an axiom. *)
Definition ClothoidFPrimePos : Prop :=
  forall k0 k1 L,
    0 < L ->
    Rabs (clothoid_kappa k0 k1 * L) < PI ->
    0 < clothoid_f' k0 k1 L.

Lemma const_lip_nn :
  forall (c Lg x y : R),
    0 <= Lg ->
    Rabs (c - c) <= Lg * Rabs (x - y).
Proof.
  intros c Lg x y HL.
  replace (c - c) with 0 by ring. rewrite Rabs_R0.
  apply Rmult_le_pos; [exact HL | apply Rabs_pos].
Qed.

Lemma clothoid_moments_flat :
  forall L,
    clothoid_P 0 0 L = 1 /\
    clothoid_Q 0 0 L = 0 /\
    clothoid_R 0 0 L = 0 /\
    clothoid_T 0 0 L = 0.
Proof.
  intro L. repeat split.
  - unfold clothoid_P. rewrite pint_ext.
    assert (Heq :
      lint (fun t => g_cos 0 0 t L) 0 1 (lip_g 0 0 L) (lip_g_nn 0 0 L)
        (fun x y Hx Hy => lip_g_ok 0 0 L x y Hx Hy)
        0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1)
      = lint (fun _ : R => 1) 0 1 (lip_g 0 0 L) (lip_g_nn 0 0 L)
          (fun x y _ _ => const_lip_nn 1 (lip_g 0 0 L) x y (lip_g_nn 0 0 L))
          0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1)).
    { apply lint_ext. intros t _. unfold g_cos, clothoid_psi.
      replace (L * (0 * t + (0 - 0) * t * t / 2)) with 0 by field.
      apply cos_0. }
    rewrite Heq, lint_const. ring.
  - unfold clothoid_Q. rewrite pint_ext.
    assert (Heq :
      lint (fun t => g_sin 0 0 t L) 0 1 (lip_g 0 0 L) (lip_g_nn 0 0 L)
        (fun x y Hx Hy => lip_gsin_ok 0 0 L x y Hx Hy)
        0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1)
      = lint (fun _ : R => 0) 0 1 (lip_g 0 0 L) (lip_g_nn 0 0 L)
          (fun x y _ _ => const_lip_nn 0 (lip_g 0 0 L) x y (lip_g_nn 0 0 L))
          0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1)).
    { apply lint_ext. intros t _. unfold g_sin, clothoid_psi.
      replace (L * (0 * t + (0 - 0) * t * t / 2)) with 0 by field.
      apply sin_0. }
    rewrite Heq, lint_const. ring.
  - unfold clothoid_R. rewrite pint_ext.
    assert (Heq :
      lint (fun t => unit_cos 0 0 t L) 0 1 (lip_h 0 0 L) (lip_h_nn 0 0 L)
        (fun x y Hx Hy => lip_unit_cos_ok 0 0 L x y Hx Hy)
        0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1)
      = lint (fun _ : R => 0) 0 1 (lip_h 0 0 L) (lip_h_nn 0 0 L)
          (fun x y _ _ => const_lip_nn 0 (lip_h 0 0 L) x y (lip_h_nn 0 0 L))
          0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1)).
    { apply lint_ext. intros t _. unfold unit_cos, clothoid_psi.
      replace (0 * t + (0 - 0) * t * t / 2) with 0 by field. ring. }
    rewrite Heq, lint_const. ring.
  - unfold clothoid_T. rewrite pint_ext.
    assert (Heq :
      lint (fun t => unit_sin 0 0 t L) 0 1 (lip_h 0 0 L) (lip_h_nn 0 0 L)
        (fun x y Hx Hy => lip_unit_sin_ok 0 0 L x y Hx Hy)
        0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1)
      = lint (fun _ : R => 0) 0 1 (lip_h 0 0 L) (lip_h_nn 0 0 L)
          (fun x y _ _ => const_lip_nn 0 (lip_h 0 0 L) x y (lip_h_nn 0 0 L))
          0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1)).
    { apply lint_ext. intros t _. unfold unit_sin, clothoid_psi.
      replace (0 * t + (0 - 0) * t * t / 2) with 0 by field. ring. }
    rewrite Heq, lint_const. ring.
Qed.

Lemma clothoid_f_flat :
  forall d L, clothoid_f 0 0 d L = L * L - d * d.
Proof.
  intros d L. unfold clothoid_f, clothoid_S.
  destruct (clothoid_moments_flat L) as [HP [HQ _]].
  rewrite HP, HQ. ring.
Qed.

Lemma clothoid_fprime_flat :
  forall L, clothoid_f' 0 0 L = 2 * L.
Proof.
  intros L. unfold clothoid_f'.
  destruct (clothoid_moments_flat L) as [HP [HQ [HR HT]]].
  unfold clothoid_S. rewrite HP, HQ, HR, HT. ring.
Qed.

Lemma clothoid_kappa_nn :
  forall k0 k1, 0 <= clothoid_kappa k0 k1.
Proof.
  intros k0 k1. unfold clothoid_kappa.
  apply Rplus_le_le_0_compat; [apply Rabs_pos|].
  apply Rmult_le_pos; [apply Rabs_pos|].
  apply Rlt_le. apply Rinv_0_lt_compat. lra.
Qed.

Lemma clothoid_f_seg_continuous :
  forall k0 k1 d a b, seg_continuous (clothoid_f k0 k1 d) a b.
Proof.
  intros k0 k1 d a b t _ eps Heps.
  assert (Hd : derivable_pt (clothoid_f k0 k1 d) t).
  { exists (clothoid_f' k0 k1 t). apply clothoid_f_deriv. }
  pose proof (derivable_continuous_pt _ t Hd) as Hc.
  unfold continuity_pt, continue_in, limit1_in, limit_in in Hc.
  destruct (Hc eps Heps) as [delta [Hdelta Hball]].
  exists delta. split; [exact Hdelta|].
  intros h Hh _.
  destruct (Req_dec h 0) as [Hz|Hnz].
  - subst h. replace (t + 0) with t by ring. rewrite Rminus_diag_eq by reflexivity.
    rewrite Rabs_R0. exact Heps.
  - apply Hball. split.
    + split; [exact I|].
      intro Heq. apply Hnz. symmetry in Heq.
      apply (Rplus_eq_reg_l t). rewrite Rplus_0_r. exact Heq.
    + unfold dist. simpl. unfold Rdist.
      replace (t + h - t) with h by ring. exact Hh.
Qed.

Lemma open_branch_fprime :
  forall k0 k1 L2 t,
    ClothoidFPrimePos ->
    0 < t -> t < L2 ->
    Rabs (clothoid_kappa k0 k1 * L2) <= PI ->
    0 < clothoid_f' k0 k1 t.
Proof.
  intros k0 k1 L2 t Hgap Ht HtL Hb.
  apply Hgap; [exact Ht|].
  set (k := clothoid_kappa k0 k1).
  assert (Hk : 0 <= k) by (unfold k; apply clothoid_kappa_nn).
  assert (Habs_t : Rabs (k * t) = k * t).
  { apply Rabs_right. apply Rle_ge. apply Rmult_le_pos; [exact Hk|lra]. }
  assert (Habs_L : Rabs (k * L2) = k * L2).
  { apply Rabs_right. apply Rle_ge. apply Rmult_le_pos; [exact Hk|lra]. }
  rewrite Habs_t.
  destruct (Req_dec k 0) as [Hz|Hnz].
  - rewrite Hz, Rmult_0_l. apply PI_RGT_0.
  - assert (Hkpos : 0 < k).
    { apply Rnot_le_lt. intro Hle. apply Hnz. apply Rle_antisym; assumption. }
    apply Rlt_le_trans with (k * L2).
    + apply Rmult_lt_compat_l; assumption.
    + rewrite <- Habs_L. exact Hb.
Qed.

Theorem clothoid_residual_strictly_increasing_on_branch :
  forall k0 k1 d L1 L2,
    ClothoidFPrimePos ->
    0 < L1 -> L1 < L2 ->
    Rabs (clothoid_kappa k0 k1 * L2) <= PI ->
    clothoid_f k0 k1 d L1 < clothoid_f k0 k1 d L2.
Proof.
  intros k0 k1 d L1 L2 Hgap HL1 HL12 Hb.
  apply (deriv_pos_strict_incr_open
           (clothoid_f k0 k1 d) (clothoid_f' k0 k1) L1 L2 L1 L2).
  - exact HL12.
  - intros t _. apply clothoid_f_deriv.
  - intros t Ht. apply (open_branch_fprime k0 k1 L2 t); [exact Hgap|lra|lra|exact Hb].
  - apply clothoid_f_seg_continuous.
  - lra.
  - exact HL12.
  - lra.
Qed.

Theorem clothoid_residual_strictly_increasing :
  forall k0 k1 d L1 L2,
    0 < L1 -> L1 < L2 ->
    Rabs (clothoid_kappa k0 k1 * L2) <= 1 / 2 ->
    clothoid_f k0 k1 d L1 < clothoid_f k0 k1 d L2.
Proof.
  intros k0 k1 d L1 L2 HL1 HL12 Hb.
  apply deriv_pos_strict_incr with (f' := clothoid_f' k0 k1) (a := L1) (b := L2).
  - intros t Ht. apply clothoid_f_deriv.
  - intros t Ht. apply clothoid_fprime_pos; [lra|].
    apply (half_branch_inward k0 k1 t L2); [lra | lra | exact Hb].
  - lra.
  - exact HL12.
  - lra.
Qed.

Corollary clothoid_residual_unique_root :
  forall k0 k1 d L1 L2,
    ClothoidFPrimePos ->
    0 < L1 -> 0 < L2 ->
    Rabs (clothoid_kappa k0 k1 * L1) <= PI ->
    Rabs (clothoid_kappa k0 k1 * L2) <= PI ->
    clothoid_f k0 k1 d L1 = 0 ->
    clothoid_f k0 k1 d L2 = 0 ->
    L1 = L2.
Proof.
  intros k0 k1 d L1 L2 Hgap HL1 HL2 Hb1 Hb2 Hf1 Hf2.
  destruct (Rtotal_order L1 L2) as [Hlt | [Heq | Hgt]].
  - pose proof (clothoid_residual_strictly_increasing_on_branch
                  k0 k1 d L1 L2 Hgap HL1 Hlt Hb2). lra.
  - exact Heq.
  - pose proof (clothoid_residual_strictly_increasing_on_branch
                  k0 k1 d L2 L1 Hgap HL2 Hgt Hb1). lra.
Qed.

Corollary clothoid_residual_unique_root_half :
  forall k0 k1 d L1 L2,
    0 < L1 -> 0 < L2 ->
    Rabs (clothoid_kappa k0 k1 * L1) <= 1 / 2 ->
    Rabs (clothoid_kappa k0 k1 * L2) <= 1 / 2 ->
    clothoid_f k0 k1 d L1 = 0 ->
    clothoid_f k0 k1 d L2 = 0 ->
    L1 = L2.
Proof.
  intros k0 k1 d L1 L2 HL1 HL2 Hb1 Hb2 Hf1 Hf2.
  destruct (Rtotal_order L1 L2) as [Hlt | [Heq | Hgt]].
  - pose proof (clothoid_residual_strictly_increasing k0 k1 d L1 L2 HL1 Hlt Hb2). lra.
  - exact Heq.
  - pose proof (clothoid_residual_strictly_increasing k0 k1 d L2 L1 HL2 Hgt Hb1). lra.
Qed.

Print Assumptions theta_on_unit.
Print Assumptions abs_sin_le_1.
Print Assumptions abs_cos_le_1.
Print Assumptions psi_abs_le.
Print Assumptions psi_diff_factor.
Print Assumptions psi_lip_on_unit.
Print Assumptions prod_diff_abs.
Print Assumptions trig_prod_lip.
Print Assumptions lip_g_nn.
Print Assumptions lip_h_nn.
Print Assumptions lip_g_ok.
Print Assumptions lip_gsin_ok.
Print Assumptions lip_unit_cos_ok.
Print Assumptions lip_unit_sin_ok.
Print Assumptions lip_h_cos_ok.
Print Assumptions lip_h_sin_ok.
Print Assumptions sqr_le_abs.
Print Assumptions gcos_modulus.
Print Assumptions gsin_modulus.
Print Assumptions clothoid_P_deriv.
Print Assumptions clothoid_Q_deriv.
Print Assumptions Pp_eq_neg_T.
Print Assumptions Qp_eq_R.
Print Assumptions zero_lip_const.
Print Assumptions const_lip_nn.
Print Assumptions lip_theta_cos.
Print Assumptions lip_theta_sin.
Print Assumptions clothoid_P_rescaled.
Print Assumptions clothoid_Q_rescaled.
Print Assumptions clothoid_spatial_P.
Print Assumptions clothoid_spatial_Q.
Print Assumptions clothoid_f_deriv.
Print Assumptions pint_abs_bound.
Print Assumptions cos_lower_sqr.
Print Assumptions half_branch_inward.
Print Assumptions const_le_cos_lip.
Print Assumptions clothoid_fprime_pos.
Print Assumptions clothoid_moments_flat.
Print Assumptions clothoid_f_flat.
Print Assumptions clothoid_fprime_flat.
Print Assumptions clothoid_kappa_nn.
Print Assumptions clothoid_f_seg_continuous.
Print Assumptions open_branch_fprime.
Print Assumptions clothoid_residual_strictly_increasing_on_branch.
Print Assumptions clothoid_residual_strictly_increasing.
Print Assumptions clothoid_residual_unique_root.
Print Assumptions clothoid_residual_unique_root_half.

