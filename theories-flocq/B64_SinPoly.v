(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_SinPoly
   ----------------------------------------------------------------------------
   S1 instance: the degree-15 reduced-sine polynomial on the B64_Horner
   kernel.  sin r ~ r * P(r^2),  P(z) = sum_{k=0..7} (-1)^k z^k / (2k+1)!,
   evaluated in z = r^2 with |r| <= 13/16 (encloses the reduced range
   |r| <= pi/4 with room for the reduction error), so |z| <= 43/64.

   Coefficients `sp_c0 .. sp_c7` are the round-to-nearest binary64 values of
   (-1)^k / (2k+1)!, written as exact (sign, 53-bit mantissa, exponent)
   literals.  This file proves only the EVALUATION budget line:
     |B2R (b64_horner sp_coeffs z) - P_b64coeff (B2R z)| <= 2^-52
   (`b64_sinpoly_eval_err`; the exact recursive bound is about 1.54 u, and
   2^-52 = 2u rounds it outward).  The other budget lines of the sin
   evaluator are separate S2 claims: coefficient representation (sp_c_k vs
   (-1)^k/(2k+1)!), truncation (Stdlib sin_bound), the rounding of
   z = fl(r*r) and of the final r * P, and argument reduction.
   claimId: s1-b64-horner.  witness: b64_sinpoly_eval_err.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* (-1)^k / (2k+1)!, rounded to nearest binary64. *)
Definition sp_c0 : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition sp_c1 : binary64 :=
  Binary.B754_finite prec emax true 6004799503160661 (-55) eq_refl.
Definition sp_c2 : binary64 :=
  Binary.B754_finite prec emax false 4803839602528529 (-59) eq_refl.
Definition sp_c3 : binary64 :=
  Binary.B754_finite prec emax true 7320136537186330 (-65) eq_refl.
Definition sp_c4 : binary64 :=
  Binary.B754_finite prec emax false 6506788033054516 (-71) eq_refl.
Definition sp_c5 : binary64 :=
  Binary.B754_finite prec emax true 7571535165736164 (-78) eq_refl.
Definition sp_c6 : binary64 :=
  Binary.B754_finite prec emax false 6212541674450185 (-85) eq_refl.
Definition sp_c7 : binary64 :=
  Binary.B754_finite prec emax true 7573384136472607 (-93) eq_refl.

Definition sp_coeffs : list binary64 :=
  [sp_c0; sp_c1; sp_c2; sp_c3; sp_c4; sp_c5; sp_c6; sp_c7].

(* Dyadic magnitude bounds |sp_c_k| <= sp_m_k. *)
Definition sp_ms : list R :=
  [1; / 4; / 64; / 4096; / 262144; / 33554432; / 4294967296; / 1099511627776].

Definition sp_Z : R := 43 / 64.

Lemma sp_coeffs_ok : hz_coeffs_ok sp_coeffs sp_ms.
Proof.
  unfold hz_coeffs_ok, sp_coeffs, sp_ms.
  repeat (apply Forall2_cons;
          [split; [reflexivity|]; cbn; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma sp_u_val : b64ae_u = / 9007199254740992.
Proof. unfold b64ae_u. cbn. reflexivity. Qed.

Lemma sp_e0_bounds : 0 < b64ae_e0 <= / 9007199254740992 / 9007199254740992.
Proof.
  unfold b64ae_e0. split; [apply bpow_gt_0|].
  apply Rle_trans with (bpow radix2 (-106)); [apply bpow_le; lia|].
  cbn. lra.
Qed.

Lemma sp_bpow1000 : 4 <= bpow radix2 1000.
Proof.
  apply Rle_trans with (bpow radix2 2); [cbn; lra|]. apply bpow_le. lia.
Qed.

Lemma sp_safe : hz_safe sp_ms sp_Z.
Proof.
  pose proof sp_e0_bounds as [He0 He1]. pose proof sp_bpow1000 as Hb.
  unfold sp_ms, sp_Z. cbn [hz_safe hz_M hz_E]. rewrite sp_u_val.
  set (e := b64ae_e0) in *.
  repeat split; lra.
Qed.

(* Suffixes S_k = [m_k; ...; m_7] of sp_ms, with exact hz_M values and
   dyadic (multiples of 2^-80) hz_E bounds, checked one level at a time. *)
Definition sp_S7 : list R := [/ 1099511627776].
Definition sp_S6 : list R := / 4294967296 :: sp_S7.
Definition sp_S5 : list R := / 33554432 :: sp_S6.
Definition sp_S4 : list R := / 262144 :: sp_S5.
Definition sp_S3 : list R := / 4096 :: sp_S4.
Definition sp_S2 : list R := / 64 :: sp_S3.
Definition sp_S1 : list R := / 4 :: sp_S2.
Definition sp_S0 : list R := 1 :: sp_S1.
Lemma sp_ms_S0 : sp_ms = sp_S0.
Proof. reflexivity. Qed.

Lemma sp_S7_nonneg : Forall (fun m => 0 <= m) sp_S7.
Proof. unfold sp_S7. repeat constructor; lra. Qed.
Lemma sp_S6_nonneg : Forall (fun m => 0 <= m) sp_S6.
Proof. unfold sp_S6, sp_S7. repeat constructor; lra. Qed.
Lemma sp_S5_nonneg : Forall (fun m => 0 <= m) sp_S5.
Proof. unfold sp_S5, sp_S6, sp_S7. repeat constructor; lra. Qed.
Lemma sp_S4_nonneg : Forall (fun m => 0 <= m) sp_S4.
Proof. unfold sp_S4, sp_S5, sp_S6, sp_S7. repeat constructor; lra. Qed.
Lemma sp_S3_nonneg : Forall (fun m => 0 <= m) sp_S3.
Proof. unfold sp_S3, sp_S4, sp_S5, sp_S6, sp_S7. repeat constructor; lra. Qed.
Lemma sp_S2_nonneg : Forall (fun m => 0 <= m) sp_S2.
Proof. unfold sp_S2, sp_S3, sp_S4, sp_S5, sp_S6, sp_S7. repeat constructor; lra. Qed.
Lemma sp_S1_nonneg : Forall (fun m => 0 <= m) sp_S1.
Proof. unfold sp_S1, sp_S2, sp_S3, sp_S4, sp_S5, sp_S6, sp_S7. repeat constructor; lra. Qed.
Lemma sp_S0_nonneg : Forall (fun m => 0 <= m) sp_S0.
Proof. unfold sp_S0, sp_S1, sp_S2, sp_S3, sp_S4, sp_S5, sp_S6, sp_S7. repeat constructor; lra. Qed.

Lemma sp_M7 : hz_M sp_S7 sp_Z <= (1 / 1099511627776).
Proof. unfold sp_S7, sp_Z. cbn [hz_M]. lra. Qed.
Lemma sp_M6 : hz_M sp_S6 sp_Z <= (16427 / 70368744177664).
Proof. unfold sp_S6, sp_S7, sp_Z. cbn [hz_M]. lra. Qed.
Lemma sp_M5 : hz_M sp_S5 sp_Z <= (134924089 / 4503599627370496).
Proof. unfold sp_S5, sp_S6, sp_S7, sp_Z. cbn [hz_M]. lra. Qed.
Lemma sp_M4 : hz_M sp_S4 sp_Z <= (1105313363603 / 288230376151711744).
Proof. unfold sp_S4, sp_S5, sp_S6, sp_S7, sp_Z. cbn [hz_M]. lra. Qed.
Lemma sp_M3 : hz_M sp_S3 sp_Z <= (4551128102005425 / 18446744073709551616).
Proof. unfold sp_S3, sp_S4, sp_S5, sp_S6, sp_S7, sp_Z. cbn [hz_M]. lra. Qed.
Lemma sp_M2 : hz_M sp_S2 sp_Z <= (18642442582095784891 / 1180591620717411303424).
Proof. unfold sp_S2, sp_S3, sp_S4, sp_S5, sp_S6, sp_S7, sp_Z. cbn [hz_M]. lra. Qed.
Lemma sp_M1 : hz_M sp_S1 sp_Z <= (19691090962508699605097 / 75557863725914323419136).
Proof. unfold sp_S1, sp_S2, sp_S3, sp_S4, sp_S5, sp_S6, sp_S7, sp_Z. cbn [hz_M]. lra. Qed.
Lemma sp_M0 : hz_M sp_S0 sp_Z <= (5682420189846390781843875 / 4835703278458516698824704).
Proof. unfold sp_S0, sp_S1, sp_S2, sp_S3, sp_S4, sp_S5, sp_S6, sp_S7, sp_Z. cbn [hz_M]. lra. Qed.

Lemma sp_E7 : hz_E sp_S7 sp_Z <= 0.
Proof. unfold sp_S7. cbn. lra. Qed.
Lemma sp_E6 : hz_E sp_S6 sp_Z <= (1 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S6 with (/ 4294967296 :: / 1099511627776 :: []).
    apply (hz_E_cons_le (/ 4294967296) _ _ sp_Z (1 / 1099511627776) 0);
      [unfold sp_Z; lra
      |apply hz_M_nonneg; [exact sp_S7_nonneg | unfold sp_Z; lra]
      |apply hz_E_nonneg; [exact sp_S7_nonneg | unfold sp_Z; lra]
      |exact sp_M7 | exact sp_E7].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E5 : hz_E sp_S5 sp_Z <= (5 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S5 with (/ 33554432 :: / 4294967296 :: sp_S7).
    apply (hz_E_cons_le (/ 33554432) _ _ sp_Z (16427 / 70368744177664) (1 / 1208925819614629174706176));
      [unfold sp_Z; lra
      |apply hz_M_nonneg; [exact sp_S6_nonneg | unfold sp_Z; lra]
      |apply hz_E_nonneg; [exact sp_S6_nonneg | unfold sp_Z; lra]
      |exact sp_M6 | exact sp_E6].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E4 : hz_E sp_S4 sp_Z <= (521 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S4 with (/ 262144 :: / 33554432 :: sp_S6).
    apply (hz_E_cons_le (/ 262144) _ _ sp_Z (134924089 / 4503599627370496) (5 / 1208925819614629174706176));
      [unfold sp_Z; lra
      |apply hz_M_nonneg; [exact sp_S5_nonneg | unfold sp_Z; lra]
      |apply hz_E_nonneg; [exact sp_S5_nonneg | unfold sp_Z; lra]
      |exact sp_M5 | exact sp_E5].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E3 : hz_E sp_S3 sp_Z <= (16905 / 604462909807314587353088).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S3 with (/ 4096 :: / 262144 :: sp_S5).
    apply (hz_E_cons_le (/ 4096) _ _ sp_Z (1105313363603 / 288230376151711744) (521 / 1208925819614629174706176));
      [unfold sp_Z; lra
      |apply hz_M_nonneg; [exact sp_S4_nonneg | unfold sp_Z; lra]
      |apply hz_E_nonneg; [exact sp_S4_nonneg | unfold sp_Z; lra]
      |exact sp_M4 | exact sp_E4].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E2 : hz_E sp_S2 sp_Z <= (2164365 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S2 with (/ 64 :: / 4096 :: sp_S4).
    apply (hz_E_cons_le (/ 64) _ _ sp_Z (4551128102005425 / 18446744073709551616) (16905 / 604462909807314587353088));
      [unfold sp_Z; lra
      |apply hz_M_nonneg; [exact sp_S3_nonneg | unfold sp_Z; lra]
      |apply hz_E_nonneg; [exact sp_S3_nonneg | unfold sp_Z; lra]
      |exact sp_M3 | exact sp_E3].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E1 : hz_E sp_S1 sp_Z <= (37856559 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S1 with (/ 4 :: / 64 :: sp_S3).
    apply (hz_E_cons_le (/ 4) _ _ sp_Z (18642442582095784891 / 1180591620717411303424) (2164365 / 1208925819614629174706176));
      [unfold sp_Z; lra
      |apply hz_M_nonneg; [exact sp_S2_nonneg | unfold sp_Z; lra]
      |apply hz_E_nonneg; [exact sp_S2_nonneg | unfold sp_Z; lra]
      |exact sp_M2 | exact sp_E2].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E0 : hz_E sp_S0 sp_Z <= (206654835 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S0 with (1 :: / 4 :: sp_S2).
    apply (hz_E_cons_le 1 _ _ sp_Z (19691090962508699605097 / 75557863725914323419136) (37856559 / 1208925819614629174706176));
      [unfold sp_Z; lra
      |apply hz_M_nonneg; [exact sp_S1_nonneg | unfold sp_Z; lra]
      |apply hz_E_nonneg; [exact sp_S1_nonneg | unfold sp_Z; lra]
      |exact sp_M1 | exact sp_E1].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.

Lemma sp_E_bound : hz_E sp_ms sp_Z <= bpow radix2 (-52).
Proof.
  rewrite sp_ms_S0. eapply Rle_trans; [exact sp_E0|].
  replace (bpow radix2 (-52)) with (/ 4503599627370496) by (cbn; reflexivity).
  lra.
Qed.

(* WITNESS {"claimId":"s1-b64-horner","topic":"numerics","lemma":"b64_sinpoly_eval_err","title":"The binary64 Horner evaluation of the degree-15 reduced-sine polynomial (binary64 coefficients of (-1)^k/(2k+1)!, z = r^2 with |z| <= 43/64) is finite and within 2^-52 of the same coefficients evaluated exactly at the same z","file":"theories-flocq/B64_SinPoly.v","witness":"b64_sinpoly_eval_err","board":"ADR-0006"} *)
Theorem b64_sinpoly_eval_err : forall z : binary64,
  fin z = true -> Rabs (B2R z) <= 43 / 64 ->
  fin (b64_horner sp_coeffs z) = true /\
  Rabs (B2R (b64_horner sp_coeffs z) - hz_horner_R (map B2R sp_coeffs) (B2R z))
    <= bpow radix2 (-52).
Proof.
  intros z Fz Hz.
  destruct (b64_horner_err sp_coeffs sp_ms z sp_Z sp_coeffs_ok Fz Hz
              ltac:(unfold sp_Z; lra) sp_safe) as [F E].
  split; [exact F|]. eapply Rle_trans; [exact E | exact sp_E_bound].
Qed.

Print Assumptions sp_coeffs_ok.
Print Assumptions sp_safe.
Print Assumptions sp_E_bound.
Print Assumptions b64_sinpoly_eval_err.
