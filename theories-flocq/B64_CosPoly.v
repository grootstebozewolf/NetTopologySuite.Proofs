(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CosPoly
   ----------------------------------------------------------------------------
   S4 polynomial facts: the degree-22 cosine polynomial on the B64_Horner
   kernel, by reuse of the S1/S2 sine machinery.  cos r ~ Q(r^2),
   Q(z) = sum_{k=0..11} (-1)^k z^k / (2k)!, for |r| <= 8/5 (the same reduced
   range as B64_SinPoly), so |z| <= 41/16.

   cq_c0 .. cq_c11 are the round-to-nearest binary64 values of (-1)^k/(2k)!.
   Budget lines proved here, each a separate theorem:
     b64_cospoly_eval_err   binary64 Horner vs the same coefficients exact,
                            <= 2^-50 (exact recursive bound ~7.14 u)
     cq_coef_err            binary64 coefficients vs (-1)^k/(2k)!
     cq_trunc               Q(r^2) vs cos r: <= (8/5)^24 / 23!
     cq_M_bound, cq_L_bound magnitude <= 11/4, Lipschitz <= 7/8
   The truncation line is NOT Stdlib cos_bound (that needs |r| <= pi/2, and
   the reduced range is slightly wider): d/dr (Q(r^2) - cos r) = sin r -
   r P(r^2), which B64_SinPoly.sp_trunc bounds by (8/5)^23/23!, and
   RealMonotone.deriv_nonneg_incr turns the derivative bound into the value
   bound (no classical MVT).  B64_Horner.hz_horner_R_deriv supplies Q'.
   claimId: s4-b64-cos.  witness: b64_cospoly_eval_err.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import RealMonotone.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* (-1)^k / (2k)!, rounded to nearest binary64. *)
Definition cq_c0 : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition cq_c1 : binary64 :=
  Binary.B754_finite prec emax true 4503599627370496 (-53) eq_refl.
Definition cq_c2 : binary64 :=
  Binary.B754_finite prec emax false 6004799503160661 (-57) eq_refl.
Definition cq_c3 : binary64 :=
  Binary.B754_finite prec emax true 6405119470038039 (-62) eq_refl.
Definition cq_c4 : binary64 :=
  Binary.B754_finite prec emax false 7320136537186330 (-68) eq_refl.
Definition cq_c5 : binary64 :=
  Binary.B754_finite prec emax true 5205430426443612 (-74) eq_refl.
Definition cq_c6 : binary64 :=
  Binary.B754_finite prec emax false 5047690110490776 (-81) eq_refl.
Definition cq_c7 : binary64 :=
  Binary.B754_finite prec emax true 7100047627943069 (-89) eq_refl.
Definition cq_c8 : binary64 :=
  Binary.B754_finite prec emax false 7573384136472607 (-97) eq_refl.
Definition cq_c9 : binary64 :=
  Binary.B754_finite prec emax true 6335903068421527 (-105) eq_refl.
Definition cq_c10 : binary64 :=
  Binary.B754_finite prec emax false 8536795713241637 (-114) eq_refl.
Definition cq_c11 : binary64 :=
  Binary.B754_finite prec emax true 4730345676601427 (-122) eq_refl.

Definition cq_coeffs : list binary64 :=
  [cq_c0; cq_c1; cq_c2; cq_c3; cq_c4; cq_c5; cq_c6; cq_c7; cq_c8; cq_c9; cq_c10; cq_c11].

(* Dyadic magnitude bounds |cq_c_k| <= cq_m_k, as suffixes S_k = [m_k; ...]. *)
Definition cq_S11 : list R := [/ 590295810358705651712].
Definition cq_S10 : list R := / 2305843009213693952 :: cq_S11.
Definition cq_S9 : list R := / 4503599627370496 :: cq_S10.
Definition cq_S8 : list R := / 17592186044416 :: cq_S9.
Definition cq_S7 : list R := / 68719476736 :: cq_S8.
Definition cq_S6 : list R := / 268435456 :: cq_S7.
Definition cq_S5 : list R := / 2097152 :: cq_S6.
Definition cq_S4 : list R := / 32768 :: cq_S5.
Definition cq_S3 : list R := / 512 :: cq_S4.
Definition cq_S2 : list R := / 16 :: cq_S3.
Definition cq_S1 : list R := / 2 :: cq_S2.
Definition cq_S0 : list R := 1 :: cq_S1.
Definition cq_ms : list R := cq_S0.

Lemma cq_coeffs_ok : hz_coeffs_ok cq_coeffs cq_ms.
Proof.
  unfold hz_coeffs_ok, cq_coeffs, cq_ms, cq_S0, cq_S1, cq_S2, cq_S3, cq_S4, cq_S5, cq_S6, cq_S7, cq_S8, cq_S9, cq_S10, cq_S11.
  repeat (apply Forall2_cons;
          [split; [reflexivity|]; cbn; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma cq_coeffs_ok_R : Forall2 (fun c m => Rabs c <= m) (map B2R cq_coeffs) cq_ms.
Proof.
  generalize cq_coeffs_ok. unfold hz_coeffs_ok.
  generalize cq_coeffs cq_ms. intros cs ms H.
  induction H as [|c m cs ms [_ Hm] _ IH]; cbn; constructor; assumption.
Qed.

Lemma cq_bpow1000 : 16 <= bpow radix2 1000.
Proof.
  apply Rle_trans with (bpow radix2 4); [cbn; lra|]. apply bpow_le. lia.
Qed.

Lemma cq_S11_nonneg : Forall (fun m => 0 <= m) cq_S11.
Proof. unfold cq_S11. repeat constructor; lra. Qed.
Lemma cq_S10_nonneg : Forall (fun m => 0 <= m) cq_S10.
Proof. unfold cq_S10, cq_S11. repeat constructor; lra. Qed.
Lemma cq_S9_nonneg : Forall (fun m => 0 <= m) cq_S9.
Proof. unfold cq_S9, cq_S10, cq_S11. repeat constructor; lra. Qed.
Lemma cq_S8_nonneg : Forall (fun m => 0 <= m) cq_S8.
Proof. unfold cq_S8, cq_S9, cq_S10, cq_S11. repeat constructor; lra. Qed.
Lemma cq_S7_nonneg : Forall (fun m => 0 <= m) cq_S7.
Proof. unfold cq_S7, cq_S8, cq_S9, cq_S10, cq_S11. repeat constructor; lra. Qed.
Lemma cq_S6_nonneg : Forall (fun m => 0 <= m) cq_S6.
Proof. unfold cq_S6, cq_S7, cq_S8, cq_S9, cq_S10, cq_S11. repeat constructor; lra. Qed.
Lemma cq_S5_nonneg : Forall (fun m => 0 <= m) cq_S5.
Proof. unfold cq_S5, cq_S6, cq_S7, cq_S8, cq_S9, cq_S10, cq_S11. repeat constructor; lra. Qed.
Lemma cq_S4_nonneg : Forall (fun m => 0 <= m) cq_S4.
Proof. unfold cq_S4, cq_S5, cq_S6, cq_S7, cq_S8, cq_S9, cq_S10, cq_S11. repeat constructor; lra. Qed.
Lemma cq_S3_nonneg : Forall (fun m => 0 <= m) cq_S3.
Proof. unfold cq_S3, cq_S4, cq_S5, cq_S6, cq_S7, cq_S8, cq_S9, cq_S10, cq_S11. repeat constructor; lra. Qed.
Lemma cq_S2_nonneg : Forall (fun m => 0 <= m) cq_S2.
Proof. unfold cq_S2, cq_S3, cq_S4, cq_S5, cq_S6, cq_S7, cq_S8, cq_S9, cq_S10, cq_S11. repeat constructor; lra. Qed.
Lemma cq_S1_nonneg : Forall (fun m => 0 <= m) cq_S1.
Proof. unfold cq_S1, cq_S2, cq_S3, cq_S4, cq_S5, cq_S6, cq_S7, cq_S8, cq_S9, cq_S10, cq_S11. repeat constructor; lra. Qed.
Lemma cq_S0_nonneg : Forall (fun m => 0 <= m) cq_S0.
Proof. unfold cq_S0, cq_S1, cq_S2, cq_S3, cq_S4, cq_S5, cq_S6, cq_S7, cq_S8, cq_S9, cq_S10, cq_S11. repeat constructor; lra. Qed.

Lemma cq_M11 : hz_M cq_S11 sp_Z <= (1 / 590295810358705651712).
Proof. unfold cq_S11, sp_Z. cbn [hz_M]. lra. Qed.
Lemma cq_M10 : hz_M cq_S10 sp_Z <= (4137 / 9444732965739290427392).
Proof.
  change (hz_M cq_S10 sp_Z) with (hz_M cq_S11 sp_Z * sp_Z + / 2305843009213693952).
  assert (H := cq_M11). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S11 sp_Z * sp_Z <= (1 / 590295810358705651712) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_M9 : hz_M cq_S9 sp_Z <= (33724049 / 151115727451828646838272).
Proof.
  change (hz_M cq_S9 sp_Z) with (hz_M cq_S10 sp_Z * sp_Z + / 4503599627370496).
  assert (H := cq_M10). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S10 sp_Z * sp_Z <= (4137 / 9444732965739290427392) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_M8 : hz_M cq_S8 sp_Z <= (138821639481 / 2417851639229258349412352).
Proof.
  change (hz_M cq_S8 sp_Z) with (hz_M cq_S9 sp_Z * sp_Z + / 17592186044416).
  assert (H := cq_M9). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S9 sp_Z * sp_Z <= (33724049 / 151115727451828646838272) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_M7 : hz_M cq_S7 sp_Z <= (568641640640033 / 38685626227668133590597632).
Proof.
  change (hz_M cq_S7 sp_Z) with (hz_M cq_S8 sp_Z * sp_Z + / 68719476736).
  assert (H := cq_M8). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S8 sp_Z * sp_Z <= (138821639481 / 2417851639229258349412352) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_M6 : hz_M cq_S6 sp_Z <= (2329157316479935305 / 618970019642690137449562112).
Proof.
  change (hz_M cq_S6 sp_Z) with (hz_M cq_S7 sp_Z * sp_Z + / 268435456).
  assert (H := cq_M7). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S7 sp_Z * sp_Z <= (568641640640033 / 38685626227668133590597632) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_M5 : hz_M cq_S5 sp_Z <= (4817861932845322561201 / 9903520314283042199192993792).
Proof.
  change (hz_M cq_S5 sp_Z) with (hz_M cq_S6 sp_Z * sp_Z + / 2097152).
  assert (H := cq_M6). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S6 sp_Z * sp_Z <= (2329157316479935305 / 618970019642690137449562112) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_M4 : hz_M cq_S4 sp_Z <= (5033235617705174923833945 / 158456325028528675187087900672).
Proof.
  change (hz_M cq_S4 sp_Z) with (hz_M cq_S5 sp_Z * sp_Z + / 32768).
  assert (H := cq_M5). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S5 sp_Z * sp_Z <= (4817861932845322561201 / 9903520314283042199192993792) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_M3 : hz_M cq_S3 sp_Z <= (5158122817467433271473688641 / 2535301200456458802993406410752).
Proof.
  change (hz_M cq_S3 sp_Z) with (hz_M cq_S4 sp_Z * sp_Z + / 512).
  assert (H := cq_M4). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S4 sp_Z * sp_Z <= (5033235617705174923833945 / 158456325028528675187087900672) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_M2 : hz_M cq_S2 sp_Z <= (2746784235972623567123827645033 / 40564819207303340847894502572032).
Proof.
  change (hz_M cq_S2 sp_Z) with (hz_M cq_S3 sp_Z * sp_Z + / 16).
  assert (H := cq_M3). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S3 sp_Z * sp_Z <= (5158122817467433271473688641 / 2535301200456458802993406410752) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_M1 : hz_M cq_S1 sp_Z <= (437136707333304293035232954022609 / 649037107316853453566312041152512).
Proof.
  change (hz_M cq_S1 sp_Z) with (hz_M cq_S2 sp_Z * sp_Z + / 2).
  assert (H := cq_M2). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S2 sp_Z * sp_Z <= (2746784235972623567123827645033 / 40564819207303340847894502572032) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_M0 : hz_M cq_S0 sp_Z <= (28307198717735131271505543773367161 / 10384593717069655257060992658440192).
Proof.
  change (hz_M cq_S0 sp_Z) with (hz_M cq_S1 sp_Z * sp_Z + 1).
  assert (H := cq_M1). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S1 sp_Z * sp_Z <= (437136707333304293035232954022609 / 649037107316853453566312041152512) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.

Lemma cq_L11 : hz_L cq_S11 sp_Z <= 0.
Proof. unfold cq_S11. cbn. lra. Qed.
Lemma cq_L10 : hz_L cq_S10 sp_Z <= (1 / 590295810358705651712).
Proof.
  change (hz_L cq_S10 sp_Z) with (hz_L cq_S11 sp_Z * sp_Z + hz_M cq_S11 sp_Z).
  assert (H := cq_L11). assert (H2 := cq_M11). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S11 sp_Z * sp_Z <= 0 * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_L9 : hz_L cq_S9 sp_Z <= (2089 / 4722366482869645213696).
Proof.
  change (hz_L cq_S9 sp_Z) with (hz_L cq_S10 sp_Z * sp_Z + hz_M cq_S10 sp_Z).
  assert (H := cq_L10). assert (H2 := cq_M10). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S10 sp_Z * sp_Z <= (1 / 590295810358705651712) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_L8 : hz_L cq_S8 sp_Z <= (33895347 / 151115727451828646838272).
Proof.
  change (hz_L cq_S8 sp_Z) with (hz_L cq_S9 sp_Z * sp_Z + hz_M cq_S9 sp_Z).
  assert (H := cq_L9). assert (H2 := cq_M9). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S9 sp_Z * sp_Z <= (2089 / 4722366482869645213696) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_L7 : hz_L cq_S7 sp_Z <= (35052837177 / 604462909807314587353088).
Proof.
  change (hz_L cq_S7 sp_Z) with (hz_L cq_S8 sp_Z * sp_Z + hz_M cq_S8 sp_Z).
  assert (H := cq_L8). assert (H2 := cq_M8). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S8 sp_Z * sp_Z <= (33895347 / 151115727451828646838272) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_L6 : hz_L cq_S6 sp_Z <= (574390305937061 / 38685626227668133590597632).
Proof.
  change (hz_L cq_S6 sp_Z) with (hz_L cq_S7 sp_Z * sp_Z + hz_M cq_S7 sp_Z).
  assert (H := cq_L7). assert (H2 := cq_M7). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S7 sp_Z * sp_Z <= (35052837177 / 604462909807314587353088) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_L5 : hz_L cq_S5 sp_Z <= (1176353659511677403 / 309485009821345068724781056).
Proof.
  change (hz_L cq_S5 sp_Z) with (hz_L cq_S6 sp_Z * sp_Z + hz_M cq_S6 sp_Z).
  assert (H := cq_L6). assert (H2 := cq_M6). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S6 sp_Z * sp_Z <= (574390305937061 / 38685626227668133590597632) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_L4 : hz_L cq_S4 sp_Z <= (4914322932925280108247 / 9903520314283042199192993792).
Proof.
  change (hz_L cq_S4 sp_Z) with (hz_L cq_S5 sp_Z * sp_Z + hz_M cq_S5 sp_Z).
  assert (H := cq_L5). assert (H2 := cq_M5). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S5 sp_Z * sp_Z <= (1176353659511677403 / 309485009821345068724781056) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_L3 : hz_L cq_S3 sp_Z <= (654340357244388926034009 / 19807040628566084398385987584).
Proof.
  change (hz_L cq_S3 sp_Z) with (hz_L cq_S4 sp_Z * sp_Z + hz_M cq_S4 sp_Z).
  assert (H := cq_L4). assert (H2 := cq_M4). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S4 sp_Z * sp_Z <= (4914322932925280108247 / 9903520314283042199192993792) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_L2 : hz_L cq_S2 sp_Z <= (5372746454643592839212843593 / 2535301200456458802993406410752).
Proof.
  change (hz_L cq_S2 sp_Z) with (hz_L cq_S3 sp_Z * sp_Z + hz_M cq_S3 sp_Z).
  assert (H := cq_L3). assert (H2 := cq_M3). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S3 sp_Z * sp_Z <= (654340357244388926034009 / 19807040628566084398385987584) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_L1 : hz_L cq_S1 sp_Z <= (1483533420306505436765777116173 / 20282409603651670423947251286016).
Proof.
  change (hz_L cq_S1 sp_Z) with (hz_L cq_S2 sp_Z * sp_Z + hz_M cq_S2 sp_Z).
  assert (H := cq_L2). assert (H2 := cq_M2). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S2 sp_Z * sp_Z <= (5372746454643592839212843593 / 2535301200456458802993406410752) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_L0 : hz_L cq_S0 sp_Z <= (558786447798437738850026677548795 / 649037107316853453566312041152512).
Proof.
  change (hz_L cq_S0 sp_Z) with (hz_L cq_S1 sp_Z * sp_Z + hz_M cq_S1 sp_Z).
  assert (H := cq_L1). assert (H2 := cq_M1). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S1 sp_Z * sp_Z <= (1483533420306505436765777116173 / 20282409603651670423947251286016) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.

Lemma cq_E11 : hz_E cq_S11 sp_Z <= 0.
Proof. unfold cq_S11. cbn. lra. Qed.
Lemma cq_E10 : hz_E cq_S10 sp_Z <= (1 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S10 with ((/ 2305843009213693952) :: (/ 590295810358705651712) :: []).
    apply (hz_E_cons_le (/ 2305843009213693952) _ _ sp_Z (1 / 590295810358705651712) 0);
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S11_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S11_nonneg | exact sp_Z_nonneg]
      |exact cq_M11 | exact cq_E11].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma cq_E9 : hz_E cq_S9 sp_Z <= (3 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S9 with ((/ 4503599627370496) :: (/ 2305843009213693952) :: cq_S11).
    apply (hz_E_cons_le (/ 4503599627370496) _ _ sp_Z (4137 / 9444732965739290427392) (1 / 1208925819614629174706176));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S10_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S10_nonneg | exact sp_Z_nonneg]
      |exact cq_M10 | exact cq_E10].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma cq_E8 : hz_E cq_S8 sp_Z <= (1 / 151115727451828646838272).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S8 with ((/ 17592186044416) :: (/ 4503599627370496) :: cq_S10).
    apply (hz_E_cons_le (/ 17592186044416) _ _ sp_Z (33724049 / 151115727451828646838272) (3 / 1208925819614629174706176));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S9_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S9_nonneg | exact sp_Z_nonneg]
      |exact cq_M9 | exact cq_E9].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma cq_E7 : hz_E cq_S7 sp_Z <= (21 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S7 with ((/ 68719476736) :: (/ 17592186044416) :: cq_S9).
    apply (hz_E_cons_le (/ 68719476736) _ _ sp_Z (138821639481 / 2417851639229258349412352) (1 / 151115727451828646838272));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S8_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S8_nonneg | exact sp_Z_nonneg]
      |exact cq_M8 | exact cq_E8].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma cq_E6 : hz_E cq_S6 sp_Z <= (55 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S6 with ((/ 268435456) :: (/ 68719476736) :: cq_S8).
    apply (hz_E_cons_le (/ 268435456) _ _ sp_Z (568641640640033 / 38685626227668133590597632) (21 / 1208925819614629174706176));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S7_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S7_nonneg | exact sp_Z_nonneg]
      |exact cq_M7 | exact cq_E7].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma cq_E5 : hz_E cq_S5 sp_Z <= (13 / 75557863725914323419136).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S5 with ((/ 2097152) :: (/ 268435456) :: cq_S7).
    apply (hz_E_cons_le (/ 2097152) _ _ sp_Z (2329157316479935305 / 618970019642690137449562112) (55 / 1208925819614629174706176));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S6_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S6_nonneg | exact sp_Z_nonneg]
      |exact cq_M6 | exact cq_E6].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma cq_E4 : hz_E cq_S4 sp_Z <= (1241 / 302231454903657293676544).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S4 with ((/ 32768) :: (/ 2097152) :: cq_S6).
    apply (hz_E_cons_le (/ 32768) _ _ sp_Z (4817861932845322561201 / 9903520314283042199192993792) (13 / 75557863725914323419136));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S5_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S5_nonneg | exact sp_Z_nonneg]
      |exact cq_M5 | exact cq_E5].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma cq_E3 : hz_E cq_S3 sp_Z <= (148357 / 604462909807314587353088).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S3 with ((/ 512) :: (/ 32768) :: cq_S5).
    apply (hz_E_cons_le (/ 512) _ _ sp_Z (5033235617705174923833945 / 158456325028528675187087900672) (1241 / 302231454903657293676544));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S4_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S4_nonneg | exact sp_Z_nonneg]
      |exact cq_M4 | exact cq_E4].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma cq_E2 : hz_E cq_S2 sp_Z <= (10548415 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S2 with ((/ 16) :: (/ 512) :: cq_S4).
    apply (hz_E_cons_le (/ 16) _ _ sp_Z (5158122817467433271473688641 / 2535301200456458802993406410752) (148357 / 604462909807314587353088));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S3_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S3_nonneg | exact sp_Z_nonneg]
      |exact cq_M3 | exact cq_E3].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma cq_E1 : hz_E cq_S1 sp_Z <= (140716955 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S1 with ((/ 2) :: (/ 16) :: cq_S3).
    apply (hz_E_cons_le (/ 2) _ _ sp_Z (2746784235972623567123827645033 / 40564819207303340847894502572032) (10548415 / 1208925819614629174706176));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S2_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S2_nonneg | exact sp_Z_nonneg]
      |exact cq_M2 | exact cq_E2].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma cq_E0 : hz_E cq_S0 sp_Z <= (479046703 / 604462909807314587353088).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S0 with ((1) :: (/ 2) :: cq_S2).
    apply (hz_E_cons_le (1) _ _ sp_Z (437136707333304293035232954022609 / 649037107316853453566312041152512) (140716955 / 1208925819614629174706176));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S1_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S1_nonneg | exact sp_Z_nonneg]
      |exact cq_M1 | exact cq_E1].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.

Lemma cq_safe11 : hz_safe cq_S11 sp_Z.
Proof. exact I. Qed.
Lemma cq_safe10 : hz_safe cq_S10 sp_Z.
Proof.
  change (hz_safe cq_S10 sp_Z) with
    (hz_safe cq_S11 sp_Z /\
     (hz_M cq_S11 sp_Z + hz_E cq_S11 sp_Z) * sp_Z * 2 + / 2305843009213693952 + 1
       <= bpow radix2 1000).
  split; [exact cq_safe11|].
  assert (H1 := cq_M11). assert (H2 := cq_E11). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S11 sp_Z + hz_E cq_S11 sp_Z) * sp_Z * 2
          <= ((1 / 590295810358705651712) + 0) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_safe9 : hz_safe cq_S9 sp_Z.
Proof.
  change (hz_safe cq_S9 sp_Z) with
    (hz_safe cq_S10 sp_Z /\
     (hz_M cq_S10 sp_Z + hz_E cq_S10 sp_Z) * sp_Z * 2 + / 4503599627370496 + 1
       <= bpow radix2 1000).
  split; [exact cq_safe10|].
  assert (H1 := cq_M10). assert (H2 := cq_E10). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S10 sp_Z + hz_E cq_S10 sp_Z) * sp_Z * 2
          <= ((4137 / 9444732965739290427392) + (1 / 1208925819614629174706176)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_safe8 : hz_safe cq_S8 sp_Z.
Proof.
  change (hz_safe cq_S8 sp_Z) with
    (hz_safe cq_S9 sp_Z /\
     (hz_M cq_S9 sp_Z + hz_E cq_S9 sp_Z) * sp_Z * 2 + / 17592186044416 + 1
       <= bpow radix2 1000).
  split; [exact cq_safe9|].
  assert (H1 := cq_M9). assert (H2 := cq_E9). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S9 sp_Z + hz_E cq_S9 sp_Z) * sp_Z * 2
          <= ((33724049 / 151115727451828646838272) + (3 / 1208925819614629174706176)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_safe7 : hz_safe cq_S7 sp_Z.
Proof.
  change (hz_safe cq_S7 sp_Z) with
    (hz_safe cq_S8 sp_Z /\
     (hz_M cq_S8 sp_Z + hz_E cq_S8 sp_Z) * sp_Z * 2 + / 68719476736 + 1
       <= bpow radix2 1000).
  split; [exact cq_safe8|].
  assert (H1 := cq_M8). assert (H2 := cq_E8). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S8 sp_Z + hz_E cq_S8 sp_Z) * sp_Z * 2
          <= ((138821639481 / 2417851639229258349412352) + (1 / 151115727451828646838272)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_safe6 : hz_safe cq_S6 sp_Z.
Proof.
  change (hz_safe cq_S6 sp_Z) with
    (hz_safe cq_S7 sp_Z /\
     (hz_M cq_S7 sp_Z + hz_E cq_S7 sp_Z) * sp_Z * 2 + / 268435456 + 1
       <= bpow radix2 1000).
  split; [exact cq_safe7|].
  assert (H1 := cq_M7). assert (H2 := cq_E7). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S7 sp_Z + hz_E cq_S7 sp_Z) * sp_Z * 2
          <= ((568641640640033 / 38685626227668133590597632) + (21 / 1208925819614629174706176)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_safe5 : hz_safe cq_S5 sp_Z.
Proof.
  change (hz_safe cq_S5 sp_Z) with
    (hz_safe cq_S6 sp_Z /\
     (hz_M cq_S6 sp_Z + hz_E cq_S6 sp_Z) * sp_Z * 2 + / 2097152 + 1
       <= bpow radix2 1000).
  split; [exact cq_safe6|].
  assert (H1 := cq_M6). assert (H2 := cq_E6). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S6 sp_Z + hz_E cq_S6 sp_Z) * sp_Z * 2
          <= ((2329157316479935305 / 618970019642690137449562112) + (55 / 1208925819614629174706176)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_safe4 : hz_safe cq_S4 sp_Z.
Proof.
  change (hz_safe cq_S4 sp_Z) with
    (hz_safe cq_S5 sp_Z /\
     (hz_M cq_S5 sp_Z + hz_E cq_S5 sp_Z) * sp_Z * 2 + / 32768 + 1
       <= bpow radix2 1000).
  split; [exact cq_safe5|].
  assert (H1 := cq_M5). assert (H2 := cq_E5). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S5 sp_Z + hz_E cq_S5 sp_Z) * sp_Z * 2
          <= ((4817861932845322561201 / 9903520314283042199192993792) + (13 / 75557863725914323419136)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_safe3 : hz_safe cq_S3 sp_Z.
Proof.
  change (hz_safe cq_S3 sp_Z) with
    (hz_safe cq_S4 sp_Z /\
     (hz_M cq_S4 sp_Z + hz_E cq_S4 sp_Z) * sp_Z * 2 + / 512 + 1
       <= bpow radix2 1000).
  split; [exact cq_safe4|].
  assert (H1 := cq_M4). assert (H2 := cq_E4). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S4 sp_Z + hz_E cq_S4 sp_Z) * sp_Z * 2
          <= ((5033235617705174923833945 / 158456325028528675187087900672) + (1241 / 302231454903657293676544)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_safe2 : hz_safe cq_S2 sp_Z.
Proof.
  change (hz_safe cq_S2 sp_Z) with
    (hz_safe cq_S3 sp_Z /\
     (hz_M cq_S3 sp_Z + hz_E cq_S3 sp_Z) * sp_Z * 2 + / 16 + 1
       <= bpow radix2 1000).
  split; [exact cq_safe3|].
  assert (H1 := cq_M3). assert (H2 := cq_E3). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S3 sp_Z + hz_E cq_S3 sp_Z) * sp_Z * 2
          <= ((5158122817467433271473688641 / 2535301200456458802993406410752) + (148357 / 604462909807314587353088)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_safe1 : hz_safe cq_S1 sp_Z.
Proof.
  change (hz_safe cq_S1 sp_Z) with
    (hz_safe cq_S2 sp_Z /\
     (hz_M cq_S2 sp_Z + hz_E cq_S2 sp_Z) * sp_Z * 2 + / 2 + 1
       <= bpow radix2 1000).
  split; [exact cq_safe2|].
  assert (H1 := cq_M2). assert (H2 := cq_E2). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S2 sp_Z + hz_E cq_S2 sp_Z) * sp_Z * 2
          <= ((2746784235972623567123827645033 / 40564819207303340847894502572032) + (10548415 / 1208925819614629174706176)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma cq_safe0 : hz_safe cq_S0 sp_Z.
Proof.
  change (hz_safe cq_S0 sp_Z) with
    (hz_safe cq_S1 sp_Z /\
     (hz_M cq_S1 sp_Z + hz_E cq_S1 sp_Z) * sp_Z * 2 + 1 + 1
       <= bpow radix2 1000).
  split; [exact cq_safe1|].
  assert (H1 := cq_M1). assert (H2 := cq_E1). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S1 sp_Z + hz_E cq_S1 sp_Z) * sp_Z * 2
          <= ((437136707333304293035232954022609 / 649037107316853453566312041152512) + (140716955 / 1208925819614629174706176)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.

Lemma cq_M_bound : hz_M cq_ms sp_Z <= (11 / 4).
Proof. unfold cq_ms. eapply Rle_trans; [exact cq_M0|]. lra. Qed.

Lemma cq_L_bound : hz_L cq_ms sp_Z <= (7 / 8).
Proof. unfold cq_ms. eapply Rle_trans; [exact cq_L0|]. lra. Qed.

Lemma cq_E_bound : hz_E cq_ms sp_Z <= bpow radix2 (-50).
Proof.
  unfold cq_ms. eapply Rle_trans; [exact cq_E0|].
  replace (bpow radix2 (-50)) with (/ 1125899906842624) by (cbn; reflexivity).
  lra.
Qed.

(* WITNESS {"claimId":"s4-b64-cos","topic":"numerics","lemma":"b64_cospoly_eval_err","title":"The binary64 Horner evaluation of the degree-22 cosine polynomial (binary64 coefficients of (-1)^k/(2k)!, z with |z| <= 41/16) is finite and within 2^-50 of the same coefficients evaluated exactly at the same z","file":"theories-flocq/B64_CosPoly.v","witness":"b64_cospoly_eval_err","board":"ADR-0006"} *)
Theorem b64_cospoly_eval_err : forall z : binary64,
  fin z = true -> Rabs (B2R z) <= 41 / 16 ->
  fin (b64_horner cq_coeffs z) = true /\
  Rabs (B2R (b64_horner cq_coeffs z) - hz_horner_R (map B2R cq_coeffs) (B2R z))
    <= bpow radix2 (-50).
Proof.
  intros z Fz Hz.
  destruct (b64_horner_err cq_coeffs cq_ms z sp_Z cq_coeffs_ok Fz Hz
              sp_Z_nonneg cq_safe0) as [F E].
  split; [exact F|]. eapply Rle_trans; [exact E | exact cq_E_bound].
Qed.

(* The mathematical coefficients (-1)^k / (2k)!. *)
Definition cq_exact : list R :=
  [1; - / 2; / 24; - / 720; / 40320; - / 3628800; / 479001600; - / 87178291200; / 20922789888000; - / 6402373705728000; / 2432902008176640000; - / 1124000727777607680000].

Definition cq_delta : list R :=
  [B2R cq_c0 - (1);
   B2R cq_c1 - (- / 2);
   B2R cq_c2 - (/ 24);
   B2R cq_c3 - (- / 720);
   B2R cq_c4 - (/ 40320);
   B2R cq_c5 - (- / 3628800);
   B2R cq_c6 - (/ 479001600);
   B2R cq_c7 - (- / 87178291200);
   B2R cq_c8 - (/ 20922789888000);
   B2R cq_c9 - (- / 6402373705728000);
   B2R cq_c10 - (/ 2432902008176640000);
   B2R cq_c11 - (- / 1124000727777607680000)].

Lemma cq_delta_eq : forall x,
  hz_horner_R (map B2R cq_coeffs) x - hz_horner_R cq_exact x = hz_horner_R cq_delta x.
Proof. intro x. unfold cq_coeffs, cq_exact, cq_delta. cbn [map hz_horner_R]. ring. Qed.

Definition cq_ds : list R :=
  [0; 0; / 288230376151711744; / 18446744073709551616; / 37778931862957161709568; / 37778931862957161709568; / 4835703278458516698824704; / 2475880078570760549798248448; / 1267650600228229401496703205376; / 81129638414606681695789005144064; / 664613997892457936451903530140172288; / 10633823966279326983230456482242756608].

Lemma cq_delta_ok : Forall2 (fun c m => Rabs c <= m) cq_delta cq_ds.
Proof.
  unfold cq_delta, cq_ds, cq_c0, cq_c1, cq_c2, cq_c3, cq_c4, cq_c5, cq_c6, cq_c7, cq_c8, cq_c9, cq_c10, cq_c11.
  repeat (apply Forall2_cons; [cbn [Binary.B2R]; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma cq_ds_M : hz_M cq_ds sp_Z <= (28649227 / 1208925819614629174706176).
Proof. unfold cq_ds, sp_Z. cbn [hz_M]. lra. Qed.

(* Coefficient representation line. *)
Lemma cq_coef_err : forall x, Rabs x <= 41 / 16 ->
  Rabs (hz_horner_R (map B2R cq_coeffs) x - hz_horner_R cq_exact x) <= (28649227 / 1208925819614629174706176).
Proof.
  intros x Hx. rewrite cq_delta_eq.
  eapply Rle_trans; [apply (hz_horner_R_bound_R _ cq_ds x sp_Z cq_delta_ok); exact Hx|].
  exact cq_ds_M.
Qed.

(* -------------------------------------------------------------------------- *)
(* Truncation through the derivative: (Q(r^2) - cos r)' = sin r - r P(r^2).  *)
(* -------------------------------------------------------------------------- *)

Lemma cq_dR_eq : forall t,
  hz_horner_dR cq_exact (t * t) * (1 * t + t * 1) = - (t * hz_horner_R sp_exact (t * t)).
Proof. intro t. unfold cq_exact, sp_exact. cbn [hz_horner_R hz_horner_dR]. field. Qed.

Definition cq_F (a : R) : R := hz_horner_R cq_exact (a * a) - cos a.

Lemma cq_F_deriv : forall t,
  derivable_pt_lim cq_F t (sin t - t * hz_horner_R sp_exact (t * t)).
Proof.
  intro t.
  assert (Hsq : derivable_pt_lim (fun a => a * a) t (1 * t + t * 1)).
  { eapply derivable_pt_lim_ext;
      [| exact (derivable_pt_lim_mult id id t 1 1 (derivable_pt_lim_id t) (derivable_pt_lim_id t))].
    intro z. unfold mult_fct, id. reflexivity. }
  assert (Hc := derivable_pt_lim_comp (fun a => a * a) (fun y => hz_horner_R cq_exact y)
                  t _ _ Hsq (hz_horner_R_deriv cq_exact (t * t))).
  assert (Hm := derivable_pt_lim_minus _ cos t _ _ Hc (derivable_pt_lim_cos t)).
  replace (sin t - t * hz_horner_R sp_exact (t * t))
    with (hz_horner_dR cq_exact (t * t) * (1 * t + t * 1) - - sin t)
    by (rewrite cq_dR_eq; ring).
  eapply derivable_pt_lim_ext; [| exact Hm].
  intro z. unfold minus_fct, comp, cq_F. reflexivity.
Qed.

Lemma cq_lin_deriv : forall K t, derivable_pt_lim (fun y => K * y) t K.
Proof.
  intros K t.
  assert (H : derivable_pt_lim (fun y => K * y) t (K * 1)).
  { eapply derivable_pt_lim_ext;
      [| exact (derivable_pt_lim_scal id K t 1 (derivable_pt_lim_id t))].
    intro z. unfold mult_real_fct, id. reflexivity. }
  rewrite Rmult_1_r in H. exact H.
Qed.

Lemma cq_F0 : cq_F 0 = 0.
Proof. unfold cq_F. rewrite cos_0. unfold cq_exact. cbn [hz_horner_R]. ring. Qed.

Lemma cq_F_even : forall a, cq_F (- a) = cq_F a.
Proof. intro a. unfold cq_F. rewrite cos_neg. replace (- a * - a) with (a * a) by ring. reflexivity. Qed.

(* Truncation line. *)
Lemma cq_trunc : forall r, Rabs r <= 8 / 5 ->
  Rabs (hz_horner_R cq_exact (r * r) - cos r) <= (8 / 5) ^ 24 / 25852016738884976640000.
Proof.
  set (K := (8 / 5) ^ 23 / 25852016738884976640000).
  assert (HK0 : 0 <= K) by (unfold K; apply Rmult_le_pos; [apply pow_le; lra | lra]).
  assert (HK : forall t, 0 <= t <= 8 / 5 ->
             Rabs (sin t - t * hz_horner_R sp_exact (t * t)) <= K).
  { intros t Ht. rewrite <- Rabs_Ropp.
    replace (- (sin t - t * hz_horner_R sp_exact (t * t)))
      with (t * hz_horner_R sp_exact (t * t) - sin t) by ring.
    apply sp_trunc. rewrite Rabs_pos_eq; lra. }
  assert (Hpos : forall a, 0 <= a <= 8 / 5 -> Rabs (cq_F a) <= 8 / 5 * K).
  { intros a Ha.
    assert (Lo : cq_F 0 + K * 0 <= cq_F a + K * a).
    { apply (deriv_nonneg_incr (fun y => cq_F y + K * y)
               (fun y => (sin y - y * hz_horner_R sp_exact (y * y)) + K) 0 (8 / 5) 0 a).
      - intros t Ht. apply derivable_pt_lim_plus with (f1 := cq_F) (f2 := fun y => K * y);
          [apply cq_F_deriv | apply cq_lin_deriv].
      - intros t Ht. specialize (HK t Ht). apply Rabs_le_inv in HK. lra.
      - lra. - lra. - lra. }
    assert (Hi : K * 0 - cq_F 0 <= K * a - cq_F a).
    { apply (deriv_nonneg_incr (fun y => K * y - cq_F y)
               (fun y => K - (sin y - y * hz_horner_R sp_exact (y * y))) 0 (8 / 5) 0 a).
      - intros t Ht. apply derivable_pt_lim_minus with (f1 := fun y => K * y) (f2 := cq_F);
          [apply cq_lin_deriv | apply cq_F_deriv].
      - intros t Ht. specialize (HK t Ht). apply Rabs_le_inv in HK. lra.
      - lra. - lra. - lra. }
    rewrite cq_F0 in Lo, Hi.
    assert (K * a <= K * (8 / 5)) by (apply Rmult_le_compat_l; lra).
    apply Rabs_le. split; lra. }
  intros r Hr.
  replace ((8 / 5) ^ 24 / 25852016738884976640000) with (8 / 5 * K) by (unfold K; cbn [pow]; field).
  fold (cq_F r).
  destruct (Rle_lt_dec 0 r) as [H0|H0].
  - apply Hpos. apply Rabs_le_inv in Hr. lra.
  - rewrite <- cq_F_even. apply Hpos. apply Rabs_le_inv in Hr. lra.
Qed.

Print Assumptions cq_coeffs_ok.
Print Assumptions b64_cospoly_eval_err.
Print Assumptions cq_coef_err.
Print Assumptions cq_trunc.
Print Assumptions cq_M_bound.
Print Assumptions cq_L_bound.
