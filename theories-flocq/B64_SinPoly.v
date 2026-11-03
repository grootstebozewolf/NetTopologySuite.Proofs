(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_SinPoly
   ----------------------------------------------------------------------------
   S1 instance and S2 polynomial facts: the degree-21 sine polynomial on the
   B64_Horner kernel.  sin r ~ r * P(r^2),  P(z) = sum_{k=0..10}
   (-1)^k z^k / (2k+1)!, for |r| <= 8/5 (encloses the mod-pi reduced range
   |r| <= pi/2 + slack used by B64_Sin.v), so |z| <= 41/16.

   sp_c0 .. sp_c10 are the round-to-nearest binary64 values of
   (-1)^k / (2k+1)!, as exact (sign, 53-bit mantissa, exponent) literals.
   Budget lines proved here, each a separate theorem:
     b64_sinpoly_eval_err   binary64 Horner vs the same coefficients exact,
                            <= 2^-51 (exact recursive bound ~3.47 u)
     sp_coef_err            binary64 coefficients vs (-1)^k/(2k+1)!
     sp_trunc               r P(r^2) vs sin r: <= (8/5)^23 / 23!  (sin_bound)
     sp_M_bound, sp_L_bound magnitude <= 7/4 and Lipschitz <= 11/32 of the
                            binary64-coefficient polynomial on |z| <= 41/16
     sp_pi_bounds           a rational enclosure of PI (Machin 2-3-7, N = 10)
   Every bound chain is checked one Horner level at a time
   (B64_Horner.hz_E_cons_le), the constants are generated exactly.
   claimId: s1-b64-horner.  witness: b64_sinpoly_eval_err.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List Machin.
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
Definition sp_c8 : binary64 :=
  Binary.B754_finite prec emax false 7127890951974218 (-101) eq_refl.
Definition sp_c9 : binary64 :=
  Binary.B754_finite prec emax true 5335497320776023 (-109) eq_refl.
Definition sp_c10 : binary64 :=
  Binary.B754_finite prec emax false 6504225305326962 (-118) eq_refl.

Definition sp_coeffs : list binary64 :=
  [sp_c0; sp_c1; sp_c2; sp_c3; sp_c4; sp_c5; sp_c6; sp_c7; sp_c8; sp_c9; sp_c10].

(* Dyadic magnitude bounds |sp_c_k| <= sp_m_k, as suffixes S_k = [m_k; ...]. *)
Definition sp_S10 : list R := [/ 36893488147419103232].
Definition sp_S9 : list R := / 72057594037927936 :: sp_S10.
Definition sp_S8 : list R := / 281474976710656 :: sp_S9.
Definition sp_S7 : list R := / 1099511627776 :: sp_S8.
Definition sp_S6 : list R := / 4294967296 :: sp_S7.
Definition sp_S5 : list R := / 33554432 :: sp_S6.
Definition sp_S4 : list R := / 262144 :: sp_S5.
Definition sp_S3 : list R := / 4096 :: sp_S4.
Definition sp_S2 : list R := / 64 :: sp_S3.
Definition sp_S1 : list R := / 4 :: sp_S2.
Definition sp_S0 : list R := 1 :: sp_S1.
Definition sp_ms : list R := sp_S0.
Definition sp_Z : R := 41 / 16.

Lemma sp_coeffs_ok : hz_coeffs_ok sp_coeffs sp_ms.
Proof.
  unfold hz_coeffs_ok, sp_coeffs, sp_ms, sp_S0, sp_S1, sp_S2, sp_S3, sp_S4, sp_S5, sp_S6, sp_S7, sp_S8, sp_S9, sp_S10.
  repeat (apply Forall2_cons;
          [split; [reflexivity|]; cbn; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma sp_coeffs_ok_R : Forall2 (fun c m => Rabs c <= m) (map B2R sp_coeffs) sp_ms.
Proof.
  generalize sp_coeffs_ok. unfold hz_coeffs_ok.
  generalize sp_coeffs sp_ms. intros cs ms H.
  induction H as [|c m cs ms [_ Hm] _ IH]; cbn; constructor; assumption.
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

Lemma sp_Z_nonneg : 0 <= sp_Z.
Proof. unfold sp_Z. lra. Qed.

Lemma sp_S10_nonneg : Forall (fun m => 0 <= m) sp_S10.
Proof. unfold sp_S10. repeat constructor; lra. Qed.
Lemma sp_S9_nonneg : Forall (fun m => 0 <= m) sp_S9.
Proof. unfold sp_S9, sp_S10. repeat constructor; lra. Qed.
Lemma sp_S8_nonneg : Forall (fun m => 0 <= m) sp_S8.
Proof. unfold sp_S8, sp_S9, sp_S10. repeat constructor; lra. Qed.
Lemma sp_S7_nonneg : Forall (fun m => 0 <= m) sp_S7.
Proof. unfold sp_S7, sp_S8, sp_S9, sp_S10. repeat constructor; lra. Qed.
Lemma sp_S6_nonneg : Forall (fun m => 0 <= m) sp_S6.
Proof. unfold sp_S6, sp_S7, sp_S8, sp_S9, sp_S10. repeat constructor; lra. Qed.
Lemma sp_S5_nonneg : Forall (fun m => 0 <= m) sp_S5.
Proof. unfold sp_S5, sp_S6, sp_S7, sp_S8, sp_S9, sp_S10. repeat constructor; lra. Qed.
Lemma sp_S4_nonneg : Forall (fun m => 0 <= m) sp_S4.
Proof. unfold sp_S4, sp_S5, sp_S6, sp_S7, sp_S8, sp_S9, sp_S10. repeat constructor; lra. Qed.
Lemma sp_S3_nonneg : Forall (fun m => 0 <= m) sp_S3.
Proof. unfold sp_S3, sp_S4, sp_S5, sp_S6, sp_S7, sp_S8, sp_S9, sp_S10. repeat constructor; lra. Qed.
Lemma sp_S2_nonneg : Forall (fun m => 0 <= m) sp_S2.
Proof. unfold sp_S2, sp_S3, sp_S4, sp_S5, sp_S6, sp_S7, sp_S8, sp_S9, sp_S10. repeat constructor; lra. Qed.
Lemma sp_S1_nonneg : Forall (fun m => 0 <= m) sp_S1.
Proof. unfold sp_S1, sp_S2, sp_S3, sp_S4, sp_S5, sp_S6, sp_S7, sp_S8, sp_S9, sp_S10. repeat constructor; lra. Qed.
Lemma sp_S0_nonneg : Forall (fun m => 0 <= m) sp_S0.
Proof. unfold sp_S0, sp_S1, sp_S2, sp_S3, sp_S4, sp_S5, sp_S6, sp_S7, sp_S8, sp_S9, sp_S10. repeat constructor; lra. Qed.

Lemma sp_M10 : hz_M sp_S10 sp_Z <= (1 / 36893488147419103232).
Proof. unfold sp_S10, sp_Z. cbn [hz_M]. lra. Qed.
Lemma sp_M9 : hz_M sp_S9 sp_Z <= (8233 / 590295810358705651712).
Proof.
  change (hz_M sp_S9 sp_Z) with (hz_M sp_S10 sp_Z * sp_Z + / 72057594037927936).
  assert (H := sp_M10). assert (HZ := sp_Z_nonneg).
  assert (hz_M sp_S10 sp_Z * sp_Z <= (1 / 36893488147419103232) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_M8 : hz_M sp_S8 sp_Z <= (33891985 / 9444732965739290427392).
Proof.
  change (hz_M sp_S8 sp_Z) with (hz_M sp_S9 sp_Z * sp_Z + / 281474976710656).
  assert (H := sp_M9). assert (HZ := sp_Z_nonneg).
  assert (hz_M sp_S9 sp_Z * sp_Z <= (8233 / 590295810358705651712) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_M7 : hz_M sp_S7 sp_Z <= (138828524857 / 151115727451828646838272).
Proof.
  change (hz_M sp_S7 sp_Z) with (hz_M sp_S8 sp_Z * sp_Z + / 1099511627776).
  assert (H := sp_M8). assert (HZ := sp_Z_nonneg).
  assert (hz_M sp_S8 sp_Z * sp_Z <= (33891985 / 9444732965739290427392) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_M6 : hz_M sp_S6 sp_Z <= (568641922940449 / 2417851639229258349412352).
Proof.
  change (hz_M sp_S6 sp_Z) with (hz_M sp_S7 sp_Z * sp_Z + / 4294967296).
  assert (H := sp_M7). assert (HZ := sp_Z_nonneg).
  assert (hz_M sp_S7 sp_Z * sp_Z <= (138828524857 / 151115727451828646838272) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_M5 : hz_M sp_S5 sp_Z <= (1176235823447405385 / 38685626227668133590597632).
Proof.
  change (hz_M sp_S5 sp_Z) with (hz_M sp_S6 sp_Z * sp_Z + / 33554432).
  assert (H := sp_M6). assert (HZ := sp_Z_nonneg).
  assert (hz_M sp_S6 sp_Z * sp_Z <= (568641922940449 / 2417851639229258349412352) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_M4 : hz_M sp_S4 sp_Z <= (2409408910196166227633 / 618970019642690137449562112).
Proof.
  change (hz_M sp_S4 sp_Z) with (hz_M sp_S5 sp_Z * sp_Z + / 262144).
  assert (H := sp_M5). assert (HZ := sp_Z_nonneg).
  assert (hz_M sp_S5 sp_Z * sp_Z <= (1176235823447405385 / 38685626227668133590597632) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_M3 : hz_M sp_S3 sp_Z <= (2516637404547301164745305 / 9903520314283042199192993792).
Proof.
  change (hz_M sp_S3 sp_Z) with (hz_M sp_S4 sp_Z * sp_Z + / 4096).
  assert (H := sp_M4). assert (HZ := sp_Z_nonneg).
  assert (hz_M sp_S4 sp_Z * sp_Z <= (2409408910196166227633 / 618970019642690137449562112) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_M2 : hz_M sp_S2 sp_Z <= (2579062212157199897552805953 / 158456325028528675187087900672).
Proof.
  change (hz_M sp_S2 sp_Z) with (hz_M sp_S3 sp_Z * sp_Z + / 64).
  assert (H := sp_M3). assert (HZ := sp_Z_nonneg).
  assert (hz_M sp_S3 sp_Z * sp_Z <= (2516637404547301164745305 / 9903520314283042199192993792) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_M1 : hz_M sp_S1 sp_Z <= (739566850812559896548016646761 / 2535301200456458802993406410752).
Proof.
  change (hz_M sp_S1 sp_Z) with (hz_M sp_S2 sp_Z * sp_Z + / 4).
  assert (H := sp_M2). assert (HZ := sp_Z_nonneg).
  assert (hz_M sp_S2 sp_Z * sp_Z <= (2579062212157199897552805953 / 158456325028528675187087900672) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_M0 : hz_M sp_S0 sp_Z <= (70887060090618296606363185089233 / 40564819207303340847894502572032).
Proof.
  change (hz_M sp_S0 sp_Z) with (hz_M sp_S1 sp_Z * sp_Z + 1).
  assert (H := sp_M1). assert (HZ := sp_Z_nonneg).
  assert (hz_M sp_S1 sp_Z * sp_Z <= (739566850812559896548016646761 / 2535301200456458802993406410752) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.

Lemma sp_L10 : hz_L sp_S10 sp_Z <= 0.
Proof. unfold sp_S10. cbn. lra. Qed.
Lemma sp_L9 : hz_L sp_S9 sp_Z <= (1 / 36893488147419103232).
Proof.
  change (hz_L sp_S9 sp_Z) with (hz_L sp_S10 sp_Z * sp_Z + hz_M sp_S10 sp_Z).
  assert (H := sp_L10). assert (H2 := sp_M10). assert (HZ := sp_Z_nonneg).
  assert (hz_L sp_S10 sp_Z * sp_Z <= 0 * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_L8 : hz_L sp_S8 sp_Z <= (4137 / 295147905179352825856).
Proof.
  change (hz_L sp_S8 sp_Z) with (hz_L sp_S9 sp_Z * sp_Z + hz_M sp_S9 sp_Z).
  assert (H := sp_L9). assert (H2 := sp_M9). assert (HZ := sp_Z_nonneg).
  assert (hz_L sp_S9 sp_Z * sp_Z <= (1 / 36893488147419103232) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_L7 : hz_L sp_S7 sp_Z <= (34231219 / 9444732965739290427392).
Proof.
  change (hz_L sp_S7 sp_Z) with (hz_L sp_S8 sp_Z * sp_Z + hz_M sp_S8 sp_Z).
  assert (H := sp_L8). assert (H2 := sp_M8). assert (HZ := sp_Z_nonneg).
  assert (hz_L sp_S8 sp_Z * sp_Z <= (4137 / 295147905179352825856) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_L6 : hz_L sp_S6 sp_Z <= (35058001209 / 37778931862957161709568).
Proof.
  change (hz_L sp_S6 sp_Z) with (hz_L sp_S7 sp_Z * sp_Z + hz_M sp_S7 sp_Z).
  assert (H := sp_L7). assert (H2 := sp_M7). assert (HZ := sp_Z_nonneg).
  assert (hz_L sp_S7 sp_Z * sp_Z <= (34231219 / 9444732965739290427392) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_L5 : hz_L sp_S5 sp_Z <= (574391435138725 / 2417851639229258349412352).
Proof.
  change (hz_L sp_S5 sp_Z) with (hz_L sp_S6 sp_Z * sp_Z + hz_M sp_S6 sp_Z).
  assert (H := sp_L6). assert (H2 := sp_M6). assert (HZ := sp_Z_nonneg).
  assert (hz_L sp_S6 sp_Z * sp_Z <= (35058001209 / 37778931862957161709568) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_L4 : hz_L sp_S4 sp_Z <= (599892936144046555 / 19342813113834066795298816).
Proof.
  change (hz_L sp_S4 sp_Z) with (hz_L sp_S5 sp_Z * sp_Z + hz_M sp_S5 sp_Z).
  assert (H := sp_L5). assert (H2 := sp_M5). assert (HZ := sp_Z_nonneg).
  assert (hz_L sp_S5 sp_Z * sp_Z <= (574391435138725 / 2417851639229258349412352) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_L3 : hz_L sp_S3 sp_Z <= (2458600130959978045143 / 618970019642690137449562112).
Proof.
  change (hz_L sp_S3 sp_Z) with (hz_L sp_S4 sp_Z * sp_Z + hz_M sp_S4 sp_Z).
  assert (H := sp_L4). assert (H2 := sp_M4). assert (HZ := sp_Z_nonneg).
  assert (hz_L sp_S4 sp_Z * sp_Z <= (599892936144046555 / 19342813113834066795298816) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_L2 : hz_L sp_S2 sp_Z <= (327180001239582533074521 / 1237940039285380274899124224).
Proof.
  change (hz_L sp_S2 sp_Z) with (hz_L sp_S3 sp_Z * sp_Z + hz_M sp_S3 sp_Z).
  assert (H := sp_L3). assert (H2 := sp_M3). assert (HZ := sp_Z_nonneg).
  assert (hz_L sp_S3 sp_Z * sp_Z <= (2458600130959978045143 / 618970019642690137449562112) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_L1 : hz_L sp_S1 sp_Z <= (2686377252563782968401248841 / 158456325028528675187087900672).
Proof.
  change (hz_L sp_S1 sp_Z) with (hz_L sp_S2 sp_Z * sp_Z + hz_M sp_S2 sp_Z).
  assert (H := sp_L2). assert (H2 := sp_M2). assert (HZ := sp_Z_nonneg).
  assert (hz_L sp_S2 sp_Z * sp_Z <= (327180001239582533074521 / 1237940039285380274899124224) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_L0 : hz_L sp_S0 sp_Z <= (424854159083837499126233924621 / 1267650600228229401496703205376).
Proof.
  change (hz_L sp_S0 sp_Z) with (hz_L sp_S1 sp_Z * sp_Z + hz_M sp_S1 sp_Z).
  assert (H := sp_L1). assert (H2 := sp_M1). assert (HZ := sp_Z_nonneg).
  assert (hz_L sp_S1 sp_Z * sp_Z <= (2686377252563782968401248841 / 158456325028528675187087900672) * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.

Lemma sp_E10 : hz_E sp_S10 sp_Z <= 0.
Proof. unfold sp_S10. cbn. lra. Qed.
Lemma sp_E9 : hz_E sp_S9 sp_Z <= (1 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S9 with ((/ 72057594037927936) :: (/ 36893488147419103232) :: []).
    apply (hz_E_cons_le (/ 72057594037927936) _ _ sp_Z (1 / 36893488147419103232) 0);
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact sp_S10_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact sp_S10_nonneg | exact sp_Z_nonneg]
      |exact sp_M10 | exact sp_E10].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E8 : hz_E sp_S8 sp_Z <= (3 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S8 with ((/ 281474976710656) :: (/ 72057594037927936) :: sp_S10).
    apply (hz_E_cons_le (/ 281474976710656) _ _ sp_Z (8233 / 590295810358705651712) (1 / 1208925819614629174706176));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact sp_S9_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact sp_S9_nonneg | exact sp_Z_nonneg]
      |exact sp_M9 | exact sp_E9].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E7 : hz_E sp_S7 sp_Z <= (1 / 151115727451828646838272).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S7 with ((/ 1099511627776) :: (/ 281474976710656) :: sp_S9).
    apply (hz_E_cons_le (/ 1099511627776) _ _ sp_Z (33891985 / 9444732965739290427392) (3 / 1208925819614629174706176));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact sp_S8_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact sp_S8_nonneg | exact sp_Z_nonneg]
      |exact sp_M8 | exact sp_E8].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E6 : hz_E sp_S6 sp_Z <= (21 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S6 with ((/ 4294967296) :: (/ 1099511627776) :: sp_S8).
    apply (hz_E_cons_le (/ 4294967296) _ _ sp_Z (138828524857 / 151115727451828646838272) (1 / 151115727451828646838272));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact sp_S7_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact sp_S7_nonneg | exact sp_Z_nonneg]
      |exact sp_M7 | exact sp_E7].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E5 : hz_E sp_S5 sp_Z <= (29 / 604462909807314587353088).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S5 with ((/ 33554432) :: (/ 4294967296) :: sp_S7).
    apply (hz_E_cons_le (/ 33554432) _ _ sp_Z (568641922940449 / 2417851639229258349412352) (21 / 1208925819614629174706176));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact sp_S6_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact sp_S6_nonneg | exact sp_Z_nonneg]
      |exact sp_M6 | exact sp_E6].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E4 : hz_E sp_S4 sp_Z <= (341 / 604462909807314587353088).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S4 with ((/ 262144) :: (/ 33554432) :: sp_S6).
    apply (hz_E_cons_le (/ 262144) _ _ sp_Z (1176235823447405385 / 38685626227668133590597632) (29 / 604462909807314587353088));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact sp_S5_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact sp_S5_nonneg | exact sp_Z_nonneg]
      |exact sp_M5 | exact sp_E5].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E3 : hz_E sp_S3 sp_Z <= (18597 / 604462909807314587353088).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S3 with ((/ 4096) :: (/ 262144) :: sp_S5).
    apply (hz_E_cons_le (/ 4096) _ _ sp_Z (2409408910196166227633 / 618970019642690137449562112) (341 / 604462909807314587353088));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact sp_S4_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact sp_S4_nonneg | exact sp_Z_nonneg]
      |exact sp_M4 | exact sp_E4].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E2 : hz_E sp_S2 sp_Z <= (2367259 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S2 with ((/ 64) :: (/ 4096) :: sp_S4).
    apply (hz_E_cons_le (/ 64) _ _ sp_Z (2516637404547301164745305 / 9903520314283042199192993792) (18597 / 604462909807314587353088));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact sp_S3_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact sp_S3_nonneg | exact sp_Z_nonneg]
      |exact sp_M3 | exact sp_E3].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E1 : hz_E sp_S1 sp_Z <= (12704089 / 302231454903657293676544).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S1 with ((/ 4) :: (/ 64) :: sp_S3).
    apply (hz_E_cons_le (/ 4) _ _ sp_Z (2579062212157199897552805953 / 158456325028528675187087900672) (2367259 / 1208925819614629174706176));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact sp_S2_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact sp_S2_nonneg | exact sp_Z_nonneg]
      |exact sp_M2 | exact sp_E2].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma sp_E0 : hz_E sp_S0 sp_Z <= (465090399 / 1208925819614629174706176).
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S0 with ((1) :: (/ 4) :: sp_S2).
    apply (hz_E_cons_le (1) _ _ sp_Z (739566850812559896548016646761 / 2535301200456458802993406410752) (12704089 / 302231454903657293676544));
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact sp_S1_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact sp_S1_nonneg | exact sp_Z_nonneg]
      |exact sp_M1 | exact sp_E1].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.

Lemma sp_safe10 : hz_safe sp_S10 sp_Z.
Proof. exact I. Qed.
Lemma sp_safe9 : hz_safe sp_S9 sp_Z.
Proof.
  change (hz_safe sp_S9 sp_Z) with
    (hz_safe sp_S10 sp_Z /\
     (hz_M sp_S10 sp_Z + hz_E sp_S10 sp_Z) * sp_Z * 2 + / 72057594037927936 + 1
       <= bpow radix2 1000).
  split; [exact sp_safe10|].
  assert (H1 := sp_M10). assert (H2 := sp_E10). assert (HZ := sp_Z_nonneg).
  assert (Hb := sp_bpow1000).
  assert ((hz_M sp_S10 sp_Z + hz_E sp_S10 sp_Z) * sp_Z * 2
          <= ((1 / 36893488147419103232) + 0) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_safe8 : hz_safe sp_S8 sp_Z.
Proof.
  change (hz_safe sp_S8 sp_Z) with
    (hz_safe sp_S9 sp_Z /\
     (hz_M sp_S9 sp_Z + hz_E sp_S9 sp_Z) * sp_Z * 2 + / 281474976710656 + 1
       <= bpow radix2 1000).
  split; [exact sp_safe9|].
  assert (H1 := sp_M9). assert (H2 := sp_E9). assert (HZ := sp_Z_nonneg).
  assert (Hb := sp_bpow1000).
  assert ((hz_M sp_S9 sp_Z + hz_E sp_S9 sp_Z) * sp_Z * 2
          <= ((8233 / 590295810358705651712) + (1 / 1208925819614629174706176)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_safe7 : hz_safe sp_S7 sp_Z.
Proof.
  change (hz_safe sp_S7 sp_Z) with
    (hz_safe sp_S8 sp_Z /\
     (hz_M sp_S8 sp_Z + hz_E sp_S8 sp_Z) * sp_Z * 2 + / 1099511627776 + 1
       <= bpow radix2 1000).
  split; [exact sp_safe8|].
  assert (H1 := sp_M8). assert (H2 := sp_E8). assert (HZ := sp_Z_nonneg).
  assert (Hb := sp_bpow1000).
  assert ((hz_M sp_S8 sp_Z + hz_E sp_S8 sp_Z) * sp_Z * 2
          <= ((33891985 / 9444732965739290427392) + (3 / 1208925819614629174706176)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_safe6 : hz_safe sp_S6 sp_Z.
Proof.
  change (hz_safe sp_S6 sp_Z) with
    (hz_safe sp_S7 sp_Z /\
     (hz_M sp_S7 sp_Z + hz_E sp_S7 sp_Z) * sp_Z * 2 + / 4294967296 + 1
       <= bpow radix2 1000).
  split; [exact sp_safe7|].
  assert (H1 := sp_M7). assert (H2 := sp_E7). assert (HZ := sp_Z_nonneg).
  assert (Hb := sp_bpow1000).
  assert ((hz_M sp_S7 sp_Z + hz_E sp_S7 sp_Z) * sp_Z * 2
          <= ((138828524857 / 151115727451828646838272) + (1 / 151115727451828646838272)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_safe5 : hz_safe sp_S5 sp_Z.
Proof.
  change (hz_safe sp_S5 sp_Z) with
    (hz_safe sp_S6 sp_Z /\
     (hz_M sp_S6 sp_Z + hz_E sp_S6 sp_Z) * sp_Z * 2 + / 33554432 + 1
       <= bpow radix2 1000).
  split; [exact sp_safe6|].
  assert (H1 := sp_M6). assert (H2 := sp_E6). assert (HZ := sp_Z_nonneg).
  assert (Hb := sp_bpow1000).
  assert ((hz_M sp_S6 sp_Z + hz_E sp_S6 sp_Z) * sp_Z * 2
          <= ((568641922940449 / 2417851639229258349412352) + (21 / 1208925819614629174706176)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_safe4 : hz_safe sp_S4 sp_Z.
Proof.
  change (hz_safe sp_S4 sp_Z) with
    (hz_safe sp_S5 sp_Z /\
     (hz_M sp_S5 sp_Z + hz_E sp_S5 sp_Z) * sp_Z * 2 + / 262144 + 1
       <= bpow radix2 1000).
  split; [exact sp_safe5|].
  assert (H1 := sp_M5). assert (H2 := sp_E5). assert (HZ := sp_Z_nonneg).
  assert (Hb := sp_bpow1000).
  assert ((hz_M sp_S5 sp_Z + hz_E sp_S5 sp_Z) * sp_Z * 2
          <= ((1176235823447405385 / 38685626227668133590597632) + (29 / 604462909807314587353088)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_safe3 : hz_safe sp_S3 sp_Z.
Proof.
  change (hz_safe sp_S3 sp_Z) with
    (hz_safe sp_S4 sp_Z /\
     (hz_M sp_S4 sp_Z + hz_E sp_S4 sp_Z) * sp_Z * 2 + / 4096 + 1
       <= bpow radix2 1000).
  split; [exact sp_safe4|].
  assert (H1 := sp_M4). assert (H2 := sp_E4). assert (HZ := sp_Z_nonneg).
  assert (Hb := sp_bpow1000).
  assert ((hz_M sp_S4 sp_Z + hz_E sp_S4 sp_Z) * sp_Z * 2
          <= ((2409408910196166227633 / 618970019642690137449562112) + (341 / 604462909807314587353088)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_safe2 : hz_safe sp_S2 sp_Z.
Proof.
  change (hz_safe sp_S2 sp_Z) with
    (hz_safe sp_S3 sp_Z /\
     (hz_M sp_S3 sp_Z + hz_E sp_S3 sp_Z) * sp_Z * 2 + / 64 + 1
       <= bpow radix2 1000).
  split; [exact sp_safe3|].
  assert (H1 := sp_M3). assert (H2 := sp_E3). assert (HZ := sp_Z_nonneg).
  assert (Hb := sp_bpow1000).
  assert ((hz_M sp_S3 sp_Z + hz_E sp_S3 sp_Z) * sp_Z * 2
          <= ((2516637404547301164745305 / 9903520314283042199192993792) + (18597 / 604462909807314587353088)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_safe1 : hz_safe sp_S1 sp_Z.
Proof.
  change (hz_safe sp_S1 sp_Z) with
    (hz_safe sp_S2 sp_Z /\
     (hz_M sp_S2 sp_Z + hz_E sp_S2 sp_Z) * sp_Z * 2 + / 4 + 1
       <= bpow radix2 1000).
  split; [exact sp_safe2|].
  assert (H1 := sp_M2). assert (H2 := sp_E2). assert (HZ := sp_Z_nonneg).
  assert (Hb := sp_bpow1000).
  assert ((hz_M sp_S2 sp_Z + hz_E sp_S2 sp_Z) * sp_Z * 2
          <= ((2579062212157199897552805953 / 158456325028528675187087900672) + (2367259 / 1208925819614629174706176)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.
Lemma sp_safe0 : hz_safe sp_S0 sp_Z.
Proof.
  change (hz_safe sp_S0 sp_Z) with
    (hz_safe sp_S1 sp_Z /\
     (hz_M sp_S1 sp_Z + hz_E sp_S1 sp_Z) * sp_Z * 2 + 1 + 1
       <= bpow radix2 1000).
  split; [exact sp_safe1|].
  assert (H1 := sp_M1). assert (H2 := sp_E1). assert (HZ := sp_Z_nonneg).
  assert (Hb := sp_bpow1000).
  assert ((hz_M sp_S1 sp_Z + hz_E sp_S1 sp_Z) * sp_Z * 2
          <= ((739566850812559896548016646761 / 2535301200456458802993406410752) + (12704089 / 302231454903657293676544)) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.

Lemma sp_M_bound : hz_M sp_ms sp_Z <= 7 / 4.
Proof. unfold sp_ms. eapply Rle_trans; [exact sp_M0|]. lra. Qed.

Lemma sp_L_bound : hz_L sp_ms sp_Z <= 11 / 32.
Proof. unfold sp_ms. eapply Rle_trans; [exact sp_L0|]. lra. Qed.

Lemma sp_E_bound : hz_E sp_ms sp_Z <= bpow radix2 (-51).
Proof.
  unfold sp_ms. eapply Rle_trans; [exact sp_E0|].
  replace (bpow radix2 (-51)) with (/ 2251799813685248) by (cbn; reflexivity).
  lra.
Qed.

(* WITNESS {"claimId":"s1-b64-horner","topic":"numerics","lemma":"b64_sinpoly_eval_err","title":"The binary64 Horner evaluation of the degree-21 sine polynomial (binary64 coefficients of (-1)^k/(2k+1)!, z with |z| <= 41/16) is finite and within 2^-51 of the same coefficients evaluated exactly at the same z","file":"theories-flocq/B64_SinPoly.v","witness":"b64_sinpoly_eval_err","board":"ADR-0006"} *)
Theorem b64_sinpoly_eval_err : forall z : binary64,
  fin z = true -> Rabs (B2R z) <= 41 / 16 ->
  fin (b64_horner sp_coeffs z) = true /\
  Rabs (B2R (b64_horner sp_coeffs z) - hz_horner_R (map B2R sp_coeffs) (B2R z))
    <= bpow radix2 (-51).
Proof.
  intros z Fz Hz.
  destruct (b64_horner_err sp_coeffs sp_ms z sp_Z sp_coeffs_ok Fz Hz
              sp_Z_nonneg sp_safe0) as [F E].
  split; [exact F|]. eapply Rle_trans; [exact E | exact sp_E_bound].
Qed.

(* The mathematical coefficients (-1)^k / (2k+1)!. *)
Definition sp_exact : list R :=
  [1; - / 6; / 120; - / 5040; / 362880; - / 39916800; / 6227020800; - / 1307674368000; / 355687428096000; - / 121645100408832000; / 51090942171709440000].

Definition sp_delta : list R :=
  [B2R sp_c0 - (1);
   B2R sp_c1 - (- / 6);
   B2R sp_c2 - (/ 120);
   B2R sp_c3 - (- / 5040);
   B2R sp_c4 - (/ 362880);
   B2R sp_c5 - (- / 39916800);
   B2R sp_c6 - (/ 6227020800);
   B2R sp_c7 - (- / 1307674368000);
   B2R sp_c8 - (/ 355687428096000);
   B2R sp_c9 - (- / 121645100408832000);
   B2R sp_c10 - (/ 51090942171709440000)].

Lemma sp_delta_eq : forall x,
  hz_horner_R (map B2R sp_coeffs) x - hz_horner_R sp_exact x = hz_horner_R sp_delta x.
Proof. intro x. unfold sp_coeffs, sp_exact, sp_delta. cbn [map hz_horner_R]. ring. Qed.

Definition sp_ds : list R :=
  [0; / 72057594037927936; / 4611686018427387904; / 4722366482869645213696; / 4722366482869645213696; / 604462909807314587353088; / 77371252455336267181195264; / 79228162514264337593543950336; / 5070602400912917605986812821504; / 2596148429267413814265248164610048; / 664613997892457936451903530140172288].

Lemma sp_delta_ok : Forall2 (fun c m => Rabs c <= m) sp_delta sp_ds.
Proof.
  unfold sp_delta, sp_ds, sp_c0, sp_c1, sp_c2, sp_c3, sp_c4, sp_c5, sp_c6, sp_c7, sp_c8, sp_c9, sp_c10.
  repeat (apply Forall2_cons; [cbn [Binary.B2R]; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma sp_ds_M : hz_M sp_ds sp_Z <= (11182133 / 302231454903657293676544).
Proof. unfold sp_ds, sp_Z. cbn [hz_M]. lra. Qed.

(* Coefficient representation line. *)
Lemma sp_coef_err : forall x, Rabs x <= 41 / 16 ->
  Rabs (hz_horner_R (map B2R sp_coeffs) x - hz_horner_R sp_exact x) <= (11182133 / 302231454903657293676544).
Proof.
  intros x Hx. rewrite sp_delta_eq.
  eapply Rle_trans; [apply (hz_horner_R_bound_R _ sp_ds x sp_Z sp_delta_ok); exact Hx|].
  exact sp_ds_M.
Qed.

(* A rational enclosure of PI: Machin 2-3-7 alternating series, N = 10. *)
Definition sp_pi_lo : R := (206324479159212898448458737198403541543452221524575397105132418900897592 / 65675121478098948134211473850539027996520477148407130764892740641180475).
Definition sp_pi_hi : R := (10880371204936608049807306858043012643607007771833878115320469157284 / 3463329719880765075895769332412541686258528563434431828555225472825).

Lemma sp_pi_bounds : sp_pi_lo <= PI <= sp_pi_hi.
Proof.
  destruct (PI_2_3_7_ineq 10) as [Hlo Hhi].
  cbn [sum_f_R0 Nat.mul Nat.add] in Hlo, Hhi.
  unfold tg_alt, PI_2_3_7_tg, Ratan_seq in Hlo, Hhi.
  cbn [Nat.mul Nat.add] in Hlo, Hhi.
  repeat match type of Hlo with context [INR ?n] => rewrite (INR_IZR_INZ n) in Hlo end.
  repeat match type of Hhi with context [INR ?n] => rewrite (INR_IZR_INZ n) in Hhi end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ pow] in Hlo, Hhi.
  match type of Hlo with ?S <= _ => replace S with (51581119789803224612114684299600885385863055381143849276283104725224398 / 65675121478098948134211473850539027996520477148407130764892740641180475) in Hlo by field end.
  match type of Hhi with _ <= ?S => replace S with (2720092801234152012451826714510753160901751942958469528830117289321 / 3463329719880765075895769332412541686258528563434431828555225472825) in Hhi by field end.
  unfold sp_pi_lo, sp_pi_hi. split; lra.
Qed.

Lemma sp_INR_fact_S : forall n, INR (fact (S n)) = INR (S n) * INR (fact n).
Proof. intro n. rewrite fact_simpl, mult_INR. reflexivity. Qed.

Lemma sp_INR_fact_0 : INR (fact 0) = 1.
Proof. reflexivity. Qed.

(* r P(r^2) with the exact coefficients is sin_approx up to one / two terms. *)
Lemma sp_sin_approx_11 : forall a,
  sin_approx a 11 = a * hz_horner_R sp_exact (a * a) - a ^ 23 / 25852016738884976640000.
Proof.
  intro a. unfold sin_approx, sin_term. cbn [sum_f_R0 Nat.mul Nat.add].
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (sp_INR_fact_S n) end.
  rewrite ?sp_INR_fact_0.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. unfold sp_exact. cbn [hz_horner_R].
  field.
Qed.

Lemma sp_sin_approx_12 : forall a,
  sin_approx a 12 = a * hz_horner_R sp_exact (a * a) - a ^ 23 / 25852016738884976640000 + a ^ 25 / 15511210043330985984000000.
Proof.
  intro a. unfold sin_approx, sin_term. cbn [sum_f_R0 Nat.mul Nat.add].
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (sp_INR_fact_S n) end.
  rewrite ?sp_INR_fact_0.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. unfold sp_exact. cbn [hz_horner_R].
  field.
Qed.

Lemma sp_poly_odd : forall a,
  (- a) * hz_horner_R sp_exact ((- a) * (- a)) = - (a * hz_horner_R sp_exact (a * a)).
Proof. intro a. replace ((- a) * (- a)) with (a * a) by ring. ring. Qed.

(* Truncation line. *)
Lemma sp_trunc : forall r, Rabs r <= 8 / 5 ->
  Rabs (r * hz_horner_R sp_exact (r * r) - sin r) <= (8 / 5) ^ 23 / 25852016738884976640000.
Proof.
  assert (Hpos : forall a, 0 <= a <= 8 / 5 ->
            Rabs (a * hz_horner_R sp_exact (a * a) - sin a) <= (8 / 5) ^ 23 / 25852016738884976640000).
  { intros a Ha.
    assert (Hpi : 8 / 5 <= PI)
      by (pose proof sp_pi_bounds as [H _]; unfold sp_pi_lo in H; lra).
    destruct (sin_bound a 5 ltac:(lra) ltac:(lra)) as [H1 H2].
    change (2 * 5 + 1)%nat with 11%nat in H1. change (2 * (5 + 1))%nat with 12%nat in H2.
    rewrite sp_sin_approx_11 in H1. rewrite sp_sin_approx_12 in H2.
    assert (P23 : 0 <= a ^ 23) by (apply pow_le; lra).
    assert (M23 : a ^ 23 <= (8 / 5) ^ 23) by (apply pow_incr; lra).
    assert (A25 : a ^ 25 / 15511210043330985984000000 <= a ^ 23 / 25852016738884976640000).
    { replace (a ^ 25) with (a ^ 23 * (a * a)) by ring.
      assert (a * a <= 64 / 25) by nra.
      apply Rmult_le_reg_r with (15511210043330985984000000); [lra|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
      assert (a ^ 23 * (a * a) <= a ^ 23 * (64 / 25)) by (apply Rmult_le_compat_l; lra).
      lra. }
    assert (0 <= a ^ 25 / 15511210043330985984000000)
      by (apply Rmult_le_pos; [apply pow_le; lra | lra]).
    apply Rabs_le. split; lra. }
  intros r Hr.
  destruct (Rle_lt_dec 0 r) as [H0|H0].
  - apply Hpos. apply Rabs_le_inv in Hr. lra.
  - replace (r * hz_horner_R sp_exact (r * r) - sin r)
      with (- ((- r) * hz_horner_R sp_exact ((- r) * (- r)) - sin (- r)))
      by (rewrite sp_poly_odd, sin_neg; ring).
    rewrite Rabs_Ropp. apply Hpos. apply Rabs_le_inv in Hr. lra.
Qed.

Print Assumptions sp_coeffs_ok.
Print Assumptions b64_sinpoly_eval_err.
Print Assumptions sp_coef_err.
Print Assumptions sp_pi_bounds.
Print Assumptions sp_trunc.
Print Assumptions sp_M_bound.
Print Assumptions sp_L_bound.
