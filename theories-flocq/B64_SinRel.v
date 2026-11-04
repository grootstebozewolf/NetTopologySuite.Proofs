(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_SinRel
   ----------------------------------------------------------------------------
   T3 prerequisite, rung 1: a RELATIVE error bound for the k = 0 branch of the
   binary64 sine (r = x, core(r) = fl(r * P(fl(r r)))), in the form
   r * P(r^2) that keeps every error term proportional to |r|.

     sp_trunc_rel      |r P_exact(r^2) - sin r| <= |r| / 2^59      (|r| <= 8/5)
     tiny_abs_to_rel   2^-1022 <= |x|  ->  2^-1075 <= u |x|
     sn_core_rel       fin r, 2^-1022 <= |r| <= 8/5 ->
                       |B2R (sn_core r) - sin r| <= 10 u |r|       (u = 2^-53)
     b64_sin_rel       (input-relative) the k = 0 branch of b64_sin, signed inputs,
                       2^-1022 <= |x| <= 1609/1024: same 10 u |x| bound

   Why a floor.  Every absolute budget line in B64_AbsErr carries the
   underflow term e0 = 2^-1075 = u * 2^-1022, so it is absorbed into the
   relative budget exactly when |x| >= 2^-1022 (tiny_abs_to_rel).  Below the
   floor the relative statement is NOT claimed here.

   Budget (units of u |r|):  final multiplication ~ 2.75 (7/4 from its relative
   rounding + 1 from the absorbed underflow term), Horner 4, argument rounding
   through the Lipschitz bound 11/32 (64/25 + tiny) ~ 0.9, coefficients ~ 0.34,
   truncation 2^-6.  Total ~ 8.01, stated as 10.  The bound is input-relative
   (denominator |r|), not |sin r|.
   claimId: t3-b64-sin-rel.  Evaluation only; extraction / oracle mode / C#
   port are NOT part of this module.  No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly B64_Sin.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  The tiny underflow term is a relative term above the normal floor.     *)
(* -------------------------------------------------------------------------- *)

Lemma tiny_abs_to_rel : forall x, bpow radix2 (-1022) <= Rabs x ->
  b64ae_e0 <= b64ae_u * Rabs x.
Proof.
  intros x H. unfold b64ae_e0, b64ae_u.
  replace (bpow radix2 (-1075)) with (bpow radix2 (-53) * bpow radix2 (-1022)).
  - apply Rmult_le_compat_l; [apply Rlt_le, bpow_gt_0 | exact H].
  - rewrite <- bpow_plus. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Relative truncation.                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma sp_trunc_rel : forall r, Rabs r <= 8 / 5 ->
  Rabs (r * hz_horner_R sp_exact (r * r) - sin r) <= Rabs r / 576460752303423488.
Proof.
  assert (Hpos : forall a, 0 <= a <= 8 / 5 ->
            Rabs (a * hz_horner_R sp_exact (a * a) - sin a) <= a / 576460752303423488).
  { intros a Ha.
    assert (Hpi : 8 / 5 <= PI)
      by (pose proof sp_pi_bounds as [H _]; unfold sp_pi_lo in H; lra).
    destruct (sin_bound a 5 ltac:(lra) ltac:(lra)) as [H1 H2].
    change (2 * 5 + 1)%nat with 11%nat in H1. change (2 * (5 + 1))%nat with 12%nat in H2.
    rewrite sp_sin_approx_11 in H1. rewrite sp_sin_approx_12 in H2.
    assert (P22 : 0 <= a ^ 22) by (apply pow_le; lra).
    assert (M22 : a ^ 22 <= (8 / 5) ^ 22) by (apply pow_incr; lra).
    replace ((8 / 5) ^ 22) with (73786976294838206464 / 2384185791015625) in M22
      by (cbn [pow]; field).
    assert (E23 : a ^ 23 = a * a ^ 22) by ring.
    assert (B23 : a ^ 23 / 25852016738884976640000 <= a / 576460752303423488).
    { rewrite E23.
      assert (a * a ^ 22 <= a * (73786976294838206464 / 2384185791015625))
        by (apply Rmult_le_compat_l; lra).
      lra. }
    assert (A25 : a ^ 25 / 15511210043330985984000000 <= a ^ 23 / 25852016738884976640000).
    { replace (a ^ 25) with (a ^ 23 * (a * a)) by ring.
      assert (P23 : 0 <= a ^ 23) by (apply pow_le; lra).
      assert (a * a <= 64 / 25) by nra.
      assert (a ^ 23 * (a * a) <= a ^ 23 * (64 / 25)) by (apply Rmult_le_compat_l; lra).
      lra. }
    assert (0 <= a ^ 25 / 15511210043330985984000000)
      by (apply Rmult_le_pos; [apply pow_le; lra | lra]).
    apply Rabs_le. split; lra. }
  intros r Hr.
  destruct (Rle_lt_dec 0 r) as [H0|H0].
  - rewrite (Rabs_right r) by lra. apply Hpos. apply Rabs_le_inv in Hr. lra.
  - replace (r * hz_horner_R sp_exact (r * r) - sin r)
      with (- ((- r) * hz_horner_R sp_exact ((- r) * (- r)) - sin (- r)))
      by (rewrite sp_poly_odd, sin_neg; ring).
    rewrite Rabs_Ropp. rewrite (Rabs_left r) by lra. apply Hpos.
    apply Rabs_le_inv in Hr. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The relative core budget as pure real algebra.                         *)
(* -------------------------------------------------------------------------- *)

Lemma sn_core_rel_alg : forall (x zr pr sr Pz Pxx Exx e : R),
  0 < e <= / 9007199254740992 / 9007199254740992 ->
  e <= / 9007199254740992 * Rabs x -> Rabs x <= 8 / 5 ->
  Rabs (sr - x * pr) <= / 9007199254740992 * Rabs (x * pr) + e ->
  Rabs pr <= 7 / 4 + / 2251799813685248 ->
  Rabs (pr - Pz) <= / 2251799813685248 ->
  Rabs (Pz - Pxx) <= 11 / 32 * Rabs (zr - x * x) ->
  Rabs (zr - x * x) <= / 9007199254740992 * (64 / 25) + e ->
  Rabs (Pxx - Exx) <= (11182133 / 302231454903657293676544) ->
  Rabs (x * Exx - sin x) <= Rabs x / 576460752303423488 ->
  Rabs (sr - sin x) <= 10 * (/ 9007199254740992 * Rabs x).
Proof.
  intros x zr pr sr Pz Pxx Exx e He Hfl Hx L1 Hpr Ep Lip Ez L4c L5.
  set (a := Rabs x) in *.
  assert (Ha : 0 <= a) by (apply Rabs_pos).
  assert (M1 : Rabs (x * pr) <= a * (7 / 4 + / 2251799813685248)).
  { rewrite Rabs_mult. apply Rmult_le_compat_l; assumption. }
  assert (T1 : Rabs (sr - x * pr)
               <= / 9007199254740992 * (a * (7 / 4 + / 2251799813685248))
                  + / 9007199254740992 * a).
  { assert (/ 9007199254740992 * Rabs (x * pr)
            <= / 9007199254740992 * (a * (7 / 4 + / 2251799813685248)))
      by (apply Rmult_le_compat_l; [lra | exact M1]).
    lra. }
  assert (T2 : Rabs (x * (pr - Pz)) <= a * / 2251799813685248).
  { rewrite Rabs_mult. apply Rmult_le_compat_l; assumption. }
  assert (Ez' : Rabs (zr - x * x)
                <= / 9007199254740992 * (64 / 25) + / 9007199254740992 / 9007199254740992)
    by lra.
  assert (T3 : Rabs (x * (Pz - Pxx))
               <= a * (11 / 32 * (/ 9007199254740992 * (64 / 25)
                                  + / 9007199254740992 / 9007199254740992))).
  { rewrite Rabs_mult. apply Rmult_le_compat_l; [exact Ha|].
    eapply Rle_trans; [exact Lip|]. apply Rmult_le_compat_l; [lra | exact Ez']. }
  assert (T4 : Rabs (x * (Pxx - Exx)) <= a * (11182133 / 302231454903657293676544)).
  { rewrite Rabs_mult. apply Rmult_le_compat_l; assumption. }
  replace (sr - sin x)
    with ((sr - x * pr) + x * (pr - Pz) + x * (Pz - Pxx)
          + x * (Pxx - Exx) + (x * Exx - sin x)) by ring.
  pose proof (Rabs_triang ((sr - x * pr) + x * (pr - Pz) + x * (Pz - Pxx)
                            + x * (Pxx - Exx)) (x * Exx - sin x)) as R1.
  pose proof (Rabs_triang ((sr - x * pr) + x * (pr - Pz) + x * (Pz - Pxx))
                          (x * (Pxx - Exx))) as R2.
  pose proof (Rabs_triang ((sr - x * pr) + x * (pr - Pz)) (x * (Pz - Pxx))) as R3.
  pose proof (Rabs_triang (sr - x * pr) (x * (pr - Pz))) as R4.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The core and the k = 0 branch of b64_sin.                              *)
(* -------------------------------------------------------------------------- *)

Lemma sn_core_rel : forall r, fin r = true ->
  bpow radix2 (-1022) <= Rabs (B2R r) -> Rabs (B2R r) <= 8 / 5 ->
  fin (sn_core r) = true /\
  Rabs (B2R (sn_core r) - sin (B2R r)) <= 10 * (b64ae_u * Rabs (B2R r)).
Proof.
  intros r Fr Hfl Hr. unfold sn_core.
  pose proof sp_e0_bounds as [He0 He1].
  pose proof sp_u_val as Uv.
  pose proof (tiny_abs_to_rel _ Hfl) as Tiny.
  destruct (sn_z_facts r Fr Hr) as [Fz [Ez Hz]].
  destruct (sn_p_facts _ Fz Hz) as [Fp [Ep Hp]].
  assert (Hb : 4 <= bpow radix2 1000) by exact sp_bpow1000.
  assert (Bs : Rabs (B2R r * B2R (b64_horner sp_coeffs (b64_mult r r)))
               <= 8 / 5 * (7 / 4 + / 2251799813685248))
    by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err r _ Fr Fp ltac:(lra)) as [Fs Es].
  assert (Hxx : Rabs (B2R r * B2R r) <= 41 / 16).
  { assert (Rabs (B2R r * B2R r) <= 8 / 5 * (8 / 5)) by (apply b64ae_abs_mult_le; assumption).
    lra. }
  split; [exact Fs|].
  rewrite Uv in Tiny |- *.
  rewrite Uv in Es.
  exact (sn_core_rel_alg (B2R r) (B2R (b64_mult r r))
           (B2R (b64_horner sp_coeffs (b64_mult r r)))
           (B2R (b64_mult r (b64_horner sp_coeffs (b64_mult r r))))
           (hz_horner_R (map B2R sp_coeffs) (B2R (b64_mult r r)))
           (hz_horner_R (map B2R sp_coeffs) (B2R r * B2R r))
           (hz_horner_R sp_exact (B2R r * B2R r)) b64ae_e0
           (conj He0 He1) Tiny Hr Es Hp Ep (sn_P_lip _ _ Hz Hxx) Ez
           (sp_coef_err _ Hxx) (sp_trunc_rel _ Hr)).
Qed.

Lemma sr_le_true : forall a b, fin a = true -> fin b = true ->
  B2R a <= B2R b -> b64_le a b = true.
Proof.
  intros a b Fa Fb H. destruct (b64_le a b) eqn:E; [reflexivity|].
  apply b64ae_le_false in E; [|exact Fa|exact Fb]. lra.
Qed.

(* WITNESS-free: this module's claim row is registered in verified-claims.md. *)
Theorem b64_sin_rel : forall x, fin x = true ->
  bpow radix2 (-1022) <= Rabs (B2R x) -> Rabs (B2R x) <= 1609 / 1024 ->
  fin (b64_sin x) = true /\
  Rabs (B2R (b64_sin x) - sin (B2R x)) <= 10 * (b64ae_u * Rabs (B2R x)).
Proof.
  intros x Fx Hfl Hhi.
  destruct sn_T1_R as [ET1 FT1].
  pose proof (Rabs_le_inv _ _ Hhi) as [Hlo' Hhi'].
  unfold b64_sin.
  destruct (b64_le hz_zero x) eqn:Z0.
  - apply b64ae_le_true in Z0; [|reflexivity|exact Fx].
    replace (B2R hz_zero) with 0 in Z0 by reflexivity.
    unfold sn_pos.
    assert (L1 : b64_le x sn_T1 = true).
    { apply sr_le_true; [exact Fx | exact FT1 | rewrite ET1; lra]. }
    rewrite L1.
    apply sn_core_rel; [exact Fx | exact Hfl | lra].
  - apply b64ae_le_false in Z0; [|reflexivity|exact Fx].
    replace (B2R hz_zero) with 0 in Z0 by reflexivity.
    destruct (sn_neg_ok x Fx) as [Fy Ey].
    assert (Hy : bpow radix2 (-1022) <= Rabs (B2R (sn_neg x))).
    { rewrite Ey, Rabs_Ropp. exact Hfl. }
    unfold sn_pos.
    assert (L1 : b64_le (sn_neg x) sn_T1 = true).
    { apply sr_le_true; [exact Fy | exact FT1 | rewrite Ey, ET1; lra]. }
    rewrite L1.
    destruct (sn_core_rel (sn_neg x) Fy Hy
                ltac:(rewrite Ey, Rabs_Ropp; lra)) as [Fc Ec].
    destruct (sn_neg_ok _ Fc) as [Fn En].
    split; [exact Fn|]. rewrite En.
    rewrite Ey, Rabs_Ropp in Ec. rewrite sin_neg in Ec.
    replace (- B2R (sn_core (sn_neg x)) - sin (B2R x))
      with (- (B2R (sn_core (sn_neg x)) - - sin (B2R x))) by ring.
    rewrite Rabs_Ropp. exact Ec.
Qed.

Print Assumptions tiny_abs_to_rel.
Print Assumptions sp_trunc_rel.
Print Assumptions sn_core_rel.
Print Assumptions b64_sin_rel.
