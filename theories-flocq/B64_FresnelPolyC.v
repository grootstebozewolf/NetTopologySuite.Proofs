(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_FresnelPolyC
   ----------------------------------------------------------------------------
   S7 polynomial facts for the canonical Fresnel integrals (C half; the S
   half is B64_FresnelPolyS, the umbrella B64_FresnelPoly re-exports both)
     C(x) = int_0^x cos(t^2) dt = x   P(x^4),  P(z) = sum_{k<=19} (-1)^k z^k / ((2k)!   (4k+1))
     S(x) = int_0^x sin(t^2) dt = x^3 Q(x^4),  Q(z) = sum_{k<=18} (-1)^k z^k / ((2k+1)! (4k+3))
   on the B64_Horner kernel, for |z| <= 40 (the intake |x| <= 5/2 gives
   x^4 <= 625/16, plus the rounding of z).  X_F = 5/2 is the tangent-rotation
   cap |psi| = x^2 <= 25/4 rad from the inflection point (B64_Fresnel.v
   header; lemma B64_ClothoidMap.xf_psi_bound states the equivalence).
   Budget lines, each a theorem: frc_eval_err / frs_eval_err (binary64
   Horner vs the same coefficients exact), frc_coef_err / frs_coef_err,
   frc_M/L_bound, frs_M/L_bound, and frc_fz_eq / frs_fz_eq: the exact
   polynomials ARE FresnelSeries.fz_C 19 1 / fz_S 18 1, whose truncation is
   FresnelSeries.fz_C_rem / fz_S_rem.  The e0 term is bounded by 2^-1000
   (not 2^-106): z^k amplifies it by 40^19.
   claimId: s7-b64-fresnel.  witness: b64_fresnel_C_err (B64_Fresnel.v).
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List Factorial.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import FresnelSeries.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

Definition fr_Z : R := 40.

Lemma fr_Z_nonneg : 0 <= fr_Z.
Proof. unfold fr_Z. lra. Qed.

Lemma fr_e0_bounds : 0 < b64ae_e0 <= / 10715086071862673209484250490600018105614048117055336074437503883703510511249361224931983788156958581275946729175531468251871452856923140435984577574698574803934567774824230985421074605062371141877954182153046474983581941267398767559165543946077062914571196477686542167660429831652624386837205668069376.
Proof.
  unfold b64ae_e0. split; [apply bpow_gt_0|].
  apply Rle_trans with (bpow radix2 (-1000)); [apply bpow_le; lia|].
  cbn. lra.
Qed.

Lemma fr_bpow1000 : 4096 <= bpow radix2 1000.
Proof.
  apply Rle_trans with (bpow radix2 12); [cbn; lra|]. apply bpow_le. lia.
Qed.

(* Fresnel C: (-1)^k / ((2k)! (4k+1)), rounded to nearest binary64. *)
Definition frc_c0 : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition frc_c1 : binary64 :=
  Binary.B754_finite prec emax true 7205759403792794 (-56) eq_refl.
Definition frc_c2 : binary64 :=
  Binary.B754_finite prec emax false 5337599558365032 (-60) eq_refl.
Definition frc_c3 : binary64 :=
  Binary.B754_finite prec emax true 7883223963123740 (-66) eq_refl.
Definition frc_c4 : binary64 :=
  Binary.B754_finite prec emax false 6889540270293016 (-72) eq_refl.
Definition frc_c5 : binary64 :=
  Binary.B754_finite prec emax true 7932084459342648 (-79) eq_refl.
Definition frc_c6 : binary64 :=
  Binary.B754_finite prec emax false 6461043341428193 (-86) eq_refl.
Definition frc_c7 : binary64 :=
  Binary.B754_finite prec emax true 7834535313592352 (-94) eq_refl.
Definition frc_c8 : binary64 :=
  Binary.B754_finite prec emax false 7343887647488589 (-102) eq_refl.
Definition frc_c9 : binary64 :=
  Binary.B754_finite prec emax true 5479699951067267 (-110) eq_refl.
Definition frc_c10 : binary64 :=
  Binary.B754_finite prec emax false 6662864946920302 (-119) eq_refl.
Definition frc_c11 : binary64 :=
  Binary.B754_finite prec emax true 6727602740055362 (-128) eq_refl.
Definition frc_c12 : binary64 :=
  Binary.B754_finite prec emax false 5730699760827993 (-137) eq_refl.
Definition frc_c13 : binary64 :=
  Binary.B754_finite prec emax true 8346693503608283 (-147) eq_refl.
Definition frc_c14 : binary64 :=
  Binary.B754_finite prec emax false 5256100318247340 (-156) eq_refl.
Definition frc_c15 : binary64 :=
  Binary.B754_finite prec emax true 5780818982013581 (-166) eq_refl.
Definition frc_c16 : binary64 :=
  Binary.B754_finite prec emax false 5600078735925811 (-176) eq_refl.
Definition frc_c17 : binary64 :=
  Binary.B754_finite prec emax true 4814658615092382 (-186) eq_refl.
Definition frc_c18 : binary64 :=
  Binary.B754_finite prec emax false 7396923659664434 (-197) eq_refl.
Definition frc_c19 : binary64 :=
  Binary.B754_finite prec emax true 5107376895006889 (-207) eq_refl.

Definition frc_coeffs : list binary64 :=
  [frc_c0; frc_c1; frc_c2; frc_c3; frc_c4; frc_c5; frc_c6; frc_c7; frc_c8; frc_c9; frc_c10; frc_c11; frc_c12; frc_c13; frc_c14; frc_c15; frc_c16; frc_c17; frc_c18; frc_c19].

Definition frc_S19 : list R := [/ 22835963083295358096932575511191922182123945984].
Definition frc_S18 : list R := / 22300745198530623141535718272648361505980416 :: frc_S19.
Definition frc_S17 : list R := / 10889035741470030830827987437816582766592 :: frc_S18.
Definition frc_S16 : list R := / 10633823966279326983230456482242756608 :: frc_S17.
Definition frc_S15 : list R := / 10384593717069655257060992658440192 :: frc_S16.
Definition frc_S14 : list R := / 10141204801825835211973625643008 :: frc_S15.
Definition frc_S13 : list R := / 19807040628566084398385987584 :: frc_S14.
Definition frc_S12 : list R := / 19342813113834066795298816 :: frc_S13.
Definition frc_S11 : list R := / 37778931862957161709568 :: frc_S12.
Definition frc_S10 : list R := / 73786976294838206464 :: frc_S11.
Definition frc_S9 : list R := / 144115188075855872 :: frc_S10.
Definition frc_S8 : list R := / 562949953421312 :: frc_S9.
Definition frc_S7 : list R := / 2199023255552 :: frc_S8.
Definition frc_S6 : list R := / 8589934592 :: frc_S7.
Definition frc_S5 : list R := / 67108864 :: frc_S6.
Definition frc_S4 : list R := / 524288 :: frc_S5.
Definition frc_S3 : list R := / 8192 :: frc_S4.
Definition frc_S2 : list R := / 128 :: frc_S3.
Definition frc_S1 : list R := / 8 :: frc_S2.
Definition frc_S0 : list R := 1 :: frc_S1.
Definition frc_ms : list R := frc_S0.

Lemma frc_coeffs_ok : hz_coeffs_ok frc_coeffs frc_ms.
Proof.
  unfold hz_coeffs_ok, frc_coeffs, frc_ms, frc_S0, frc_S1, frc_S2, frc_S3, frc_S4, frc_S5, frc_S6, frc_S7, frc_S8, frc_S9, frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19.
  repeat (apply Forall2_cons;
          [split; [reflexivity|]; cbn; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma frc_coeffs_ok_R : Forall2 (fun c m => Rabs c <= m) (map B2R frc_coeffs) frc_ms.
Proof.
  generalize frc_coeffs_ok. unfold hz_coeffs_ok.
  generalize frc_coeffs frc_ms. intros cs ms H.
  induction H as [|c m cs ms [_ Hm] _ IH]; cbn; constructor; assumption.
Qed.

Lemma frc_S19_nonneg : Forall (fun m => 0 <= m) frc_S19.
Proof. unfold frc_S19. repeat constructor; lra. Qed.
Lemma frc_S18_nonneg : Forall (fun m => 0 <= m) frc_S18.
Proof. unfold frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S17_nonneg : Forall (fun m => 0 <= m) frc_S17.
Proof. unfold frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S16_nonneg : Forall (fun m => 0 <= m) frc_S16.
Proof. unfold frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S15_nonneg : Forall (fun m => 0 <= m) frc_S15.
Proof. unfold frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S14_nonneg : Forall (fun m => 0 <= m) frc_S14.
Proof. unfold frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S13_nonneg : Forall (fun m => 0 <= m) frc_S13.
Proof. unfold frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S12_nonneg : Forall (fun m => 0 <= m) frc_S12.
Proof. unfold frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S11_nonneg : Forall (fun m => 0 <= m) frc_S11.
Proof. unfold frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S10_nonneg : Forall (fun m => 0 <= m) frc_S10.
Proof. unfold frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S9_nonneg : Forall (fun m => 0 <= m) frc_S9.
Proof. unfold frc_S9, frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S8_nonneg : Forall (fun m => 0 <= m) frc_S8.
Proof. unfold frc_S8, frc_S9, frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S7_nonneg : Forall (fun m => 0 <= m) frc_S7.
Proof. unfold frc_S7, frc_S8, frc_S9, frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S6_nonneg : Forall (fun m => 0 <= m) frc_S6.
Proof. unfold frc_S6, frc_S7, frc_S8, frc_S9, frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S5_nonneg : Forall (fun m => 0 <= m) frc_S5.
Proof. unfold frc_S5, frc_S6, frc_S7, frc_S8, frc_S9, frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S4_nonneg : Forall (fun m => 0 <= m) frc_S4.
Proof. unfold frc_S4, frc_S5, frc_S6, frc_S7, frc_S8, frc_S9, frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S3_nonneg : Forall (fun m => 0 <= m) frc_S3.
Proof. unfold frc_S3, frc_S4, frc_S5, frc_S6, frc_S7, frc_S8, frc_S9, frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S2_nonneg : Forall (fun m => 0 <= m) frc_S2.
Proof. unfold frc_S2, frc_S3, frc_S4, frc_S5, frc_S6, frc_S7, frc_S8, frc_S9, frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S1_nonneg : Forall (fun m => 0 <= m) frc_S1.
Proof. unfold frc_S1, frc_S2, frc_S3, frc_S4, frc_S5, frc_S6, frc_S7, frc_S8, frc_S9, frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_S0_nonneg : Forall (fun m => 0 <= m) frc_S0.
Proof. unfold frc_S0, frc_S1, frc_S2, frc_S3, frc_S4, frc_S5, frc_S6, frc_S7, frc_S8, frc_S9, frc_S10, frc_S11, frc_S12, frc_S13, frc_S14, frc_S15, frc_S16, frc_S17, frc_S18, frc_S19. repeat constructor; lra. Qed.
Lemma frc_M19 : hz_M frc_S19 fr_Z <= (1 / 22835963083295358096932575511191922182123945984).
Proof. unfold frc_S19, fr_Z. cbn [hz_M]. lra. Qed.
Lemma frc_M18 : hz_M frc_S18 fr_Z <= (133 / 2854495385411919762116571938898990272765493248).
Proof.
  change (hz_M frc_S18 fr_Z) with (hz_M frc_S19 fr_Z * fr_Z + / 22300745198530623141535718272648361505980416).
  assert (H := frc_M19). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S19 fr_Z * fr_Z <= (1 / 22835963083295358096932575511191922182123945984) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M17 : hz_M frc_S17 fr_Z <= (33433 / 356811923176489970264571492362373784095686656).
Proof.
  change (hz_M frc_S17 fr_Z) with (hz_M frc_S18 fr_Z * fr_Z + / 10889035741470030830827987437816582766592).
  assert (H := frc_M18). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S18 fr_Z * fr_Z <= (133 / 2854495385411919762116571938898990272765493248) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M16 : hz_M frc_S16 fr_Z <= (4361469 / 44601490397061246283071436545296723011960832).
Proof.
  change (hz_M frc_S16 fr_Z) with (hz_M frc_S17 fr_Z * fr_Z + / 10633823966279326983230456482242756608).
  assert (H := frc_M17). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S17 fr_Z * fr_Z <= (33433 / 356811923176489970264571492362373784095686656) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M15 : hz_M frc_S15 fr_Z <= (558678257 / 5575186299632655785383929568162090376495104).
Proof.
  change (hz_M frc_S15 fr_Z) with (hz_M frc_S16 fr_Z * fr_Z + / 10384593717069655257060992658440192).
  assert (H := frc_M16). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S16 fr_Z * fr_Z <= (4361469 / 44601490397061246283071436545296723011960832) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M14 : hz_M frc_S14 fr_Z <= (71512868021 / 696898287454081973172991196020261297061888).
Proof.
  change (hz_M frc_S14 fr_Z) with (hz_M frc_S15 fr_Z * fr_Z + / 10141204801825835211973625643008).
  assert (H := frc_M15). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S15 fr_Z * fr_Z <= (558678257 / 5575186299632655785383929568162090376495104) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M13 : hz_M frc_S13 fr_Z <= (4755610851209 / 87112285931760246646623899502532662132736).
Proof.
  change (hz_M frc_S13 fr_Z) with (hz_M frc_S14 fr_Z * fr_Z + / 19807040628566084398385987584).
  assert (H := frc_M14). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S14 fr_Z * fr_Z <= (71512868021 / 696898287454081973172991196020261297061888) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M12 : hz_M frc_S12 fr_Z <= (586728007677357 / 10889035741470030830827987437816582766592).
Proof.
  change (hz_M frc_S12 fr_Z) with (hz_M frc_S13 fr_Z * fr_Z + / 19342813113834066795298816).
  assert (H := frc_M13). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S13 fr_Z * fr_Z <= (4755610851209 / 87112285931760246646623899502532662132736) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M11 : hz_M frc_S11 fr_Z <= (38962437057350753 / 1361129467683753853853498429727072845824).
Proof.
  change (hz_M frc_S11 fr_Z) with (hz_M frc_S12 fr_Z * fr_Z + / 37778931862957161709568).
  assert (H := frc_M12). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S12 fr_Z * fr_Z <= (586728007677357 / 10889035741470030830827987437816582766592) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M10 : hz_M frc_S10 fr_Z <= (2500655194500447717 / 170141183460469231731687303715884105728).
Proof.
  change (hz_M frc_S10 fr_Z) with (hz_M frc_S11 fr_Z * fr_Z + / 73786976294838206464).
  assert (H := frc_M11). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S11 fr_Z * fr_Z <= (38962437057350753 / 1361129467683753853853498429727072845824) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M9 : hz_M frc_S9 fr_Z <= (160077228562178651513 / 21267647932558653966460912964485513216).
Proof.
  change (hz_M frc_S9 fr_Z) with (hz_M frc_S10 fr_Z * fr_Z + / 144115188075855872).
  assert (H := frc_M10). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S10 fr_Z * fr_Z <= (2500655194500447717 / 170141183460469231731687303715884105728) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M8 : hz_M frc_S8 fr_Z <= (5522752625680538471261 / 2658455991569831745807614120560689152).
Proof.
  change (hz_M frc_S8 fr_Z) with (hz_M frc_S9 fr_Z * fr_Z + / 562949953421312).
  assert (H := frc_M9). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S9 fr_Z * fr_Z <= (160077228562178651513 / 21267647932558653966460912964485513216) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M7 : hz_M frc_S7 fr_Z <= (178729490580231339194577 / 332306998946228968225951765070086144).
Proof.
  change (hz_M frc_S7 fr_Z) with (hz_M frc_S8 fr_Z * fr_Z + / 2199023255552).
  assert (H := frc_M8). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S8 fr_Z * fr_Z <= (5522752625680538471261 / 2658455991569831745807614120560689152) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M6 : hz_M frc_S6 fr_Z <= (5729350731359673394797589 / 41538374868278621028243970633760768).
Proof.
  change (hz_M frc_S6 fr_Z) with (hz_M frc_S7 fr_Z * fr_Z + / 8589934592).
  assert (H := frc_M7). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S7 fr_Z * fr_Z <= (178729490580231339194577 / 332306998946228968225951765070086144) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M5 : hz_M frc_S5 fr_Z <= (106018006112134634155183209 / 5192296858534827628530496329220096).
Proof.
  change (hz_M frc_S5 fr_Z) with (hz_M frc_S6 fr_Z * fr_Z + / 67108864).
  assert (H := frc_M6). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S6 fr_Z * fr_Z <= (5729350731359673394797589 / 41538374868278621028243970633760768) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M4 : hz_M frc_S4 fr_Z <= (1768030069846053445675040269 / 649037107316853453566312041152512).
Proof.
  change (hz_M frc_S4 fr_Z) with (hz_M frc_S5 fr_Z * fr_Z + / 524288).
  assert (H := frc_M5). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S5 fr_Z * fr_Z <= (106018006112134634155183209 / 5192296858534827628530496329220096) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M3 : hz_M frc_S3 fr_Z <= (18743670663513309427568195137 / 81129638414606681695789005144064).
Proof.
  change (hz_M frc_S3 fr_Z) with (hz_M frc_S4 fr_Z * fr_Z + / 8192).
  assert (H := frc_M4). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S4 fr_Z * fr_Z <= (1768030069846053445675040269 / 649037107316853453566312041152512) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M2 : hz_M frc_S2 fr_Z <= (172946515831830884731384926021 / 10141204801825835211973625643008).
Proof.
  change (hz_M frc_S2 fr_Z) with (hz_M frc_S3 fr_Z * fr_Z + / 128).
  assert (H := frc_M3). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S3 fr_Z * fr_Z <= (18743670663513309427568195137 / 81129638414606681695789005144064) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M1 : hz_M frc_S1 fr_Z <= (1023188904187683098844012530777 / 1267650600228229401496703205376).
Proof.
  change (hz_M frc_S1 fr_Z) with (hz_M frc_S2 fr_Z * fr_Z + / 8).
  assert (H := frc_M2). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S2 fr_Z * fr_Z <= (172946515831830884731384926021 / 10141204801825835211973625643008) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_M0 : hz_M frc_S0 fr_Z <= (5274400845966944169407150554557 / 158456325028528675187087900672).
Proof.
  change (hz_M frc_S0 fr_Z) with (hz_M frc_S1 fr_Z * fr_Z + 1).
  assert (H := frc_M1). assert (HZ := fr_Z_nonneg).
  assert (hz_M frc_S1 fr_Z * fr_Z <= (1023188904187683098844012530777 / 1267650600228229401496703205376) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L19 : hz_L frc_S19 fr_Z <= 0.
Proof. unfold frc_S19. cbn. lra. Qed.
Lemma frc_L18 : hz_L frc_S18 fr_Z <= (1 / 22835963083295358096932575511191922182123945984).
Proof.
  change (hz_L frc_S18 fr_Z) with (hz_L frc_S19 fr_Z * fr_Z + hz_M frc_S19 fr_Z).
  assert (H := frc_L19). assert (H2 := frc_M19). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S19 fr_Z * fr_Z <= 0 * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L17 : hz_L frc_S17 fr_Z <= (69 / 1427247692705959881058285969449495136382746624).
Proof.
  change (hz_L frc_S17 fr_Z) with (hz_L frc_S18 fr_Z * fr_Z + hz_M frc_S18 fr_Z).
  assert (H := frc_L18). assert (H2 := frc_M18). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S18 fr_Z * fr_Z <= (1 / 22835963083295358096932575511191922182123945984) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L16 : hz_L frc_S16 fr_Z <= (34123 / 356811923176489970264571492362373784095686656).
Proof.
  change (hz_L frc_S16 fr_Z) with (hz_L frc_S17 fr_Z * fr_Z + hz_M frc_S17 fr_Z).
  assert (H := frc_L17). assert (H2 := frc_M17). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S17 fr_Z * fr_Z <= (69 / 1427247692705959881058285969449495136382746624) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L15 : hz_L frc_S15 fr_Z <= (1133021 / 11150372599265311570767859136324180752990208).
Proof.
  change (hz_L frc_S15 fr_Z) with (hz_L frc_S16 fr_Z * fr_Z + hz_M frc_S16 fr_Z).
  assert (H := frc_L16). assert (H2 := frc_M16). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S16 fr_Z * fr_Z <= (34123 / 356811923176489970264571492362373784095686656) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L14 : hz_L frc_S14 fr_Z <= (581338677 / 5575186299632655785383929568162090376495104).
Proof.
  change (hz_L frc_S14 fr_Z) with (hz_L frc_S15 fr_Z * fr_Z + hz_M frc_S15 fr_Z).
  assert (H := frc_L15). assert (H2 := frc_M15). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S15 fr_Z * fr_Z <= (1133021 / 11150372599265311570767859136324180752990208) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L13 : hz_L frc_S13 fr_Z <= (37209780703 / 348449143727040986586495598010130648530944).
Proof.
  change (hz_L frc_S13 fr_Z) with (hz_L frc_S14 fr_Z * fr_Z + hz_M frc_S14 fr_Z).
  assert (H := frc_L14). assert (H2 := frc_M14). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S14 fr_Z * fr_Z <= (581338677 / 5575186299632655785383929568162090376495104) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L12 : hz_L frc_S12 fr_Z <= (5127708658239 / 87112285931760246646623899502532662132736).
Proof.
  change (hz_L frc_S12 fr_Z) with (hz_L frc_S13 fr_Z * fr_Z + hz_M frc_S13 fr_Z).
  assert (H := frc_L13). assert (H2 := frc_M13). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S13 fr_Z * fr_Z <= (37209780703 / 348449143727040986586495598010130648530944) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L11 : hz_L frc_S11 fr_Z <= (76545818871069 / 1361129467683753853853498429727072845824).
Proof.
  change (hz_L frc_S11 fr_Z) with (hz_L frc_S12 fr_Z * fr_Z + hz_M frc_S12 fr_Z).
  assert (H := frc_L12). assert (H2 := frc_M12). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S12 fr_Z * fr_Z <= (5127708658239 / 87112285931760246646623899502532662132736) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L10 : hz_L frc_S10 fr_Z <= (42024269812193513 / 1361129467683753853853498429727072845824).
Proof.
  change (hz_L frc_S10 fr_Z) with (hz_L frc_S11 fr_Z * fr_Z + hz_M frc_S11 fr_Z).
  assert (H := frc_L11). assert (H2 := frc_M11). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S11 fr_Z * fr_Z <= (76545818871069 / 1361129467683753853853498429727072845824) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L9 : hz_L frc_S9 fr_Z <= (1355388271780707641 / 85070591730234615865843651857942052864).
Proof.
  change (hz_L frc_S9 fr_Z) with (hz_L frc_S10 fr_Z * fr_Z + hz_M frc_S10 fr_Z).
  assert (H := frc_L10). assert (H2 := frc_M10). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S10 fr_Z * fr_Z <= (42024269812193513 / 1361129467683753853853498429727072845824) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L8 : hz_L frc_S8 fr_Z <= (173631111279985727923 / 21267647932558653966460912964485513216).
Proof.
  change (hz_L frc_S8 fr_Z) with (hz_L frc_S9 fr_Z * fr_Z + hz_M frc_S9 fr_Z).
  assert (H := frc_L9). assert (H2 := frc_M9). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S9 fr_Z * fr_Z <= (1355388271780707641 / 85070591730234615865843651857942052864) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L7 : hz_L frc_S7 fr_Z <= (1597727045520116777719 / 664613997892457936451903530140172288).
Proof.
  change (hz_L frc_S7 fr_Z) with (hz_L frc_S8 fr_Z * fr_Z + hz_M frc_S8 fr_Z).
  assert (H := frc_L8). assert (H2 := frc_M8). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S8 fr_Z * fr_Z <= (173631111279985727923 / 21267647932558653966460912964485513216) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L6 : hz_L frc_S6 fr_Z <= (210684031490633674748957 / 332306998946228968225951765070086144).
Proof.
  change (hz_L frc_S6 fr_Z) with (hz_L frc_S7 fr_Z * fr_Z + hz_M frc_S7 fr_Z).
  assert (H := frc_L7). assert (H2 := frc_M7). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S7 fr_Z * fr_Z <= (1597727045520116777719 / 664613997892457936451903530140172288) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L5 : hz_L frc_S5 fr_Z <= (3391385444406420884271187 / 20769187434139310514121985316880384).
Proof.
  change (hz_L frc_S5 fr_Z) with (hz_L frc_S6 fr_Z * fr_Z + hz_M frc_S6 fr_Z).
  assert (H := frc_L6). assert (H2 := frc_M6). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S6 fr_Z * fr_Z <= (210684031490633674748957 / 332306998946228968225951765070086144) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L4 : hz_L frc_S4 fr_Z <= (139931860556198842997895079 / 5192296858534827628530496329220096).
Proof.
  change (hz_L frc_S4 fr_Z) with (hz_L frc_S5 fr_Z * fr_Z + hz_M frc_S5 fr_Z).
  assert (H := frc_L5). assert (H2 := frc_M5). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S5 fr_Z * fr_Z <= (3391385444406420884271187 / 20769187434139310514121985316880384) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L3 : hz_L frc_S3 fr_Z <= (154230585789190478791532229 / 40564819207303340847894502572032).
Proof.
  change (hz_L frc_S3 fr_Z) with (hz_L frc_S4 fr_Z * fr_Z + hz_M frc_S4 fr_Z).
  assert (H := frc_L4). assert (H2 := frc_M4). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S4 fr_Z * fr_Z <= (139931860556198842997895079 / 5192296858534827628530496329220096) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L2 : hz_L frc_S2 fr_Z <= (31082117526648547730890773457 / 81129638414606681695789005144064).
Proof.
  change (hz_L frc_S2 fr_Z) with (hz_L frc_S3 fr_Z * fr_Z + hz_M frc_S3 fr_Z).
  assert (H := frc_L3). assert (H2 := frc_M3). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S3 fr_Z * fr_Z <= (154230585789190478791532229 / 40564819207303340847894502572032) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L1 : hz_L frc_S1 fr_Z <= (164178551732536811692919396653 / 5070602400912917605986812821504).
Proof.
  change (hz_L frc_S1 fr_Z) with (hz_L frc_S2 fr_Z * fr_Z + hz_M frc_S2 fr_Z).
  assert (H := frc_L2). assert (H2 := frc_M2). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S2 fr_Z * fr_Z <= (31082117526648547730890773457 / 81129638414606681695789005144064) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_L0 : hz_L frc_S0 fr_Z <= (2664974421513051215773206497307 / 1267650600228229401496703205376).
Proof.
  change (hz_L frc_S0 fr_Z) with (hz_L frc_S1 fr_Z * fr_Z + hz_M frc_S1 fr_Z).
  assert (H := frc_L1). assert (H2 := frc_M1). assert (HZ := fr_Z_nonneg).
  assert (hz_L frc_S1 fr_Z * fr_Z <= (164178551732536811692919396653 / 5070602400912917605986812821504) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_E19 : hz_E frc_S19 fr_Z <= 0.
Proof. unfold frc_S19. cbn. lra. Qed.
Lemma frc_E18 : hz_E frc_S18 fr_Z <= (9943947977234055209 / 1852673427797059126777135760139006525652319754650249024631321344126610074238976).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S18 with ((/ 22300745198530623141535718272648361505980416) :: (/ 22835963083295358096932575511191922182123945984) :: []).
    apply (hz_E_cons_le (/ 22300745198530623141535718272648361505980416) _ _ fr_Z (1 / 22835963083295358096932575511191922182123945984) 0);
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S19_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S19_nonneg | exact fr_Z_nonneg]
      |exact frc_M19 | exact frc_E19].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E17 : hz_E frc_S17 fr_Z <= (9791951489810300993 / 904625697166532776746648320380374280103671755200316906558262375061821325312).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S17 with ((/ 10889035741470030830827987437816582766592) :: (/ 22300745198530623141535718272648361505980416) :: frc_S19).
    apply (hz_E_cons_le (/ 10889035741470030830827987437816582766592) _ _ fr_Z (133 / 2854495385411919762116571938898990272765493248) (9943947977234055209 / 1852673427797059126777135760139006525652319754650249024631321344126610074238976));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S18_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S18_nonneg | exact fr_Z_nonneg]
      |exact frc_M18 | exact frc_E18].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E16 : hz_E frc_S16 fr_Z <= (10341069586954190977 / 883423532389192164791648750371459257913741948437809479060803100646309888).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S16 with ((/ 10633823966279326983230456482242756608) :: (/ 10889035741470030830827987437816582766592) :: frc_S18).
    apply (hz_E_cons_le (/ 10633823966279326983230456482242756608) _ _ fr_Z (33433 / 356811923176489970264571492362373784095686656) (9791951489810300993 / 904625697166532776746648320380374280103671755200316906558262375061821325312));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S17_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S17_nonneg | exact fr_Z_nonneg]
      |exact frc_M17 | exact frc_E17].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E15 : hz_E frc_S15 fr_Z <= (10376614736295886985 / 862718293348820473429344482784628181556388621521298319395315527974912).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S15 with ((/ 10384593717069655257060992658440192) :: (/ 10633823966279326983230456482242756608) :: frc_S17).
    apply (hz_E_cons_le (/ 10384593717069655257060992658440192) _ _ fr_Z (4361469 / 44601490397061246283071436545296723011960832) (10341069586954190977 / 883423532389192164791648750371459257913741948437809479060803100646309888));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S16_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S16_nonneg | exact fr_Z_nonneg]
      |exact frc_M16 | exact frc_E16].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E14 : hz_E frc_S14 fr_Z <= (10378553813366734985 / 842498333348457493583344221469363458551160763204392890034487820288).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S14 with ((/ 10141204801825835211973625643008) :: (/ 10384593717069655257060992658440192) :: frc_S16).
    apply (hz_E_cons_le (/ 10141204801825835211973625643008) _ _ fr_Z (558678257 / 5575186299632655785383929568162090376495104) (10376614736295886985 / 862718293348820473429344482784628181556388621521298319395315527974912));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S15_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S15_nonneg | exact fr_Z_nonneg]
      |exact frc_M15 | exact frc_E15].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E13 : hz_E frc_S13 fr_Z <= (5766965047741907081 / 822752278660603021077484591278675252491367932816789931674304512).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S13 with ((/ 19807040628566084398385987584) :: (/ 10141204801825835211973625643008) :: frc_S15).
    apply (hz_E_cons_le (/ 19807040628566084398385987584) _ _ fr_Z (71512868021 / 696898287454081973172991196020261297061888) (10378553813366734985 / 842498333348457493583344221469363458551160763204392890034487820288));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S14_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S14_nonneg | exact fr_Z_nonneg]
      |exact frc_M14 | exact frc_E14].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E12 : hz_E frc_S12 fr_Z <= (5226537731535847501 / 803469022129495137770981046170581301261101496891396417650688).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S12 with ((/ 19342813113834066795298816) :: (/ 19807040628566084398385987584) :: frc_S14).
    apply (hz_E_cons_le (/ 19342813113834066795298816) _ _ fr_Z (4755610851209 / 87112285931760246646623899502532662132736) (5766965047741907081 / 822752278660603021077484591278675252491367932816789931674304512));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S13_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S13_nonneg | exact fr_Z_nonneg]
      |exact frc_M13 | exact frc_E13].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E11 : hz_E frc_S11 fr_Z <= (11542042257061286165 / 3138550867693340381917894711603833208051177722232017256448).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S11 with ((/ 37778931862957161709568) :: (/ 19342813113834066795298816) :: frc_S13).
    apply (hz_E_cons_le (/ 37778931862957161709568) _ _ fr_Z (586728007677357 / 10889035741470030830827987437816582766592) (5226537731535847501 / 803469022129495137770981046170581301261101496891396417650688));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S12_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S12_nonneg | exact fr_Z_nonneg]
      |exact frc_M12 | exact frc_E12].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E10 : hz_E frc_S10 fr_Z <= (11683591570481719197 / 6129982163463555433433388108601236734474956488734408704).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S10 with ((/ 73786976294838206464) :: (/ 37778931862957161709568) :: frc_S12).
    apply (hz_E_cons_le (/ 73786976294838206464) _ _ fr_Z (38962437057350753 / 1361129467683753853853498429727072845824) (11542042257061286165 / 3138550867693340381917894711603833208051177722232017256448));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S11_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S11_nonneg | exact fr_Z_nonneg]
      |exact frc_M11 | exact frc_E11].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E9 : hz_E frc_S9 fr_Z <= (11699062124861440233 / 11972621413014756705924586149611790497021399392059392).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S9 with ((/ 144115188075855872) :: (/ 73786976294838206464) :: frc_S11).
    apply (hz_E_cons_le (/ 144115188075855872) _ _ fr_Z (2500655194500447717 / 170141183460469231731687303715884105728) (11683591570481719197 / 6129982163463555433433388108601236734474956488734408704));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S10_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S10_nonneg | exact fr_Z_nonneg]
      |exact frc_M10 | exact frc_E10].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E8 : hz_E frc_S8 fr_Z <= (3544464716054857053 / 11692013098647223345629478661730264157247460343808).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S8 with ((/ 562949953421312) :: (/ 144115188075855872) :: frc_S10).
    apply (hz_E_cons_le (/ 562949953421312) _ _ fr_Z (160077228562178651513 / 21267647932558653966460912964485513216) (11699062124861440233 / 11972621413014756705924586149611790497021399392059392));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S9_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S9_nonneg | exact fr_Z_nonneg]
      |exact frc_M9 | exact frc_E9].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E7 : hz_E frc_S7 fr_Z <= (14809483178774156427 / 182687704666362864775460604089535377456991567872).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S7 with ((/ 2199023255552) :: (/ 562949953421312) :: frc_S9).
    apply (hz_E_cons_le (/ 2199023255552) _ _ fr_Z (5522752625680538471261 / 2658455991569831745807614120560689152) (3544464716054857053 / 11692013098647223345629478661730264157247460343808));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S8_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S8_nonneg | exact fr_Z_nonneg]
      |exact frc_M8 | exact frc_E8].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E6 : hz_E frc_S6 fr_Z <= (14946348278553026875 / 713623846352979940529142984724747568191373312).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S6 with ((/ 8589934592) :: (/ 2199023255552) :: frc_S8).
    apply (hz_E_cons_le (/ 8589934592) _ _ fr_Z (178729490580231339194577 / 332306998946228968225951765070086144) (14809483178774156427 / 182687704666362864775460604089535377456991567872));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S7_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S7_nonneg | exact fr_Z_nonneg]
      |exact frc_M7 | exact frc_E7].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E5 : hz_E frc_S5 fr_Z <= (10362012088314477193 / 2787593149816327892691964784081045188247552).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S5 with ((/ 67108864) :: (/ 8589934592) :: frc_S7).
    apply (hz_E_cons_le (/ 67108864) _ _ fr_Z (5729350731359673394797589 / 41538374868278621028243970633760768) (14946348278553026875 / 713623846352979940529142984724747568191373312));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S6_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S6_nonneg | exact fr_Z_nonneg]
      |exact frc_M6 | exact frc_E6].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E4 : hz_E frc_S4 fr_Z <= (11799293292343773571 / 21778071482940061661655974875633165533184).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S4 with ((/ 524288) :: (/ 67108864) :: frc_S6).
    apply (hz_E_cons_le (/ 524288) _ _ fr_Z (106018006112134634155183209 / 5192296858534827628530496329220096) (10362012088314477193 / 2787593149816327892691964784081045188247552));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S5_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S5_nonneg | exact fr_Z_nonneg]
      |exact frc_M5 | exact frc_E5].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E3 : hz_E frc_S3 fr_Z <= (10109637954687651245 / 170141183460469231731687303715884105728).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S3 with ((/ 8192) :: (/ 524288) :: frc_S5).
    apply (hz_E_cons_le (/ 8192) _ _ fr_Z (1768030069846053445675040269 / 649037107316853453566312041152512) (11799293292343773571 / 21778071482940061661655974875633165533184));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S4_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S4_nonneg | exact fr_Z_nonneg]
      |exact frc_M4 | exact frc_E4].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E2 : hz_E frc_S2 fr_Z <= (1759936607771365563 / 332306998946228968225951765070086144).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S2 with ((/ 128) :: (/ 8192) :: frc_S4).
    apply (hz_E_cons_le (/ 128) _ _ fr_Z (18743670663513309427568195137 / 81129638414606681695789005144064) (10109637954687651245 / 170141183460469231731687303715884105728));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S3_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S3_nonneg | exact fr_Z_nonneg]
      |exact frc_M3 | exact frc_E3].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E1 : hz_E frc_S1 fr_Z <= (3916975346181443827 / 10384593717069655257060992658440192).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S1 with ((/ 8) :: (/ 128) :: frc_S3).
    apply (hz_E_cons_le (/ 8) _ _ fr_Z (172946515831830884731384926021 / 10141204801825835211973625643008) (1759936607771365563 / 332306998946228968225951765070086144));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S2_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S2_nonneg | exact fr_Z_nonneg]
      |exact frc_M2 | exact frc_E2].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_E0 : hz_E frc_S0 fr_Z <= (1814677549481158795 / 81129638414606681695789005144064).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frc_S0 with ((1) :: (/ 8) :: frc_S2).
    apply (hz_E_cons_le (1) _ _ fr_Z (1023188904187683098844012530777 / 1267650600228229401496703205376) (3916975346181443827 / 10384593717069655257060992658440192));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frc_S1_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frc_S1_nonneg | exact fr_Z_nonneg]
      |exact frc_M1 | exact frc_E1].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frc_safe19 : hz_safe frc_S19 fr_Z.
Proof. exact I. Qed.
Lemma frc_safe18 : hz_safe frc_S18 fr_Z.
Proof.
  change (hz_safe frc_S18 fr_Z) with
    (hz_safe frc_S19 fr_Z /\
     (hz_M frc_S19 fr_Z + hz_E frc_S19 fr_Z) * fr_Z * 2 + / 22300745198530623141535718272648361505980416 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe19|].
  assert (H1 := frc_M19). assert (H2 := frc_E19). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S19 fr_Z + hz_E frc_S19 fr_Z) * fr_Z * 2
          <= ((1 / 22835963083295358096932575511191922182123945984) + 0) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe17 : hz_safe frc_S17 fr_Z.
Proof.
  change (hz_safe frc_S17 fr_Z) with
    (hz_safe frc_S18 fr_Z /\
     (hz_M frc_S18 fr_Z + hz_E frc_S18 fr_Z) * fr_Z * 2 + / 10889035741470030830827987437816582766592 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe18|].
  assert (H1 := frc_M18). assert (H2 := frc_E18). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S18 fr_Z + hz_E frc_S18 fr_Z) * fr_Z * 2
          <= ((133 / 2854495385411919762116571938898990272765493248) + (9943947977234055209 / 1852673427797059126777135760139006525652319754650249024631321344126610074238976)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe16 : hz_safe frc_S16 fr_Z.
Proof.
  change (hz_safe frc_S16 fr_Z) with
    (hz_safe frc_S17 fr_Z /\
     (hz_M frc_S17 fr_Z + hz_E frc_S17 fr_Z) * fr_Z * 2 + / 10633823966279326983230456482242756608 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe17|].
  assert (H1 := frc_M17). assert (H2 := frc_E17). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S17 fr_Z + hz_E frc_S17 fr_Z) * fr_Z * 2
          <= ((33433 / 356811923176489970264571492362373784095686656) + (9791951489810300993 / 904625697166532776746648320380374280103671755200316906558262375061821325312)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe15 : hz_safe frc_S15 fr_Z.
Proof.
  change (hz_safe frc_S15 fr_Z) with
    (hz_safe frc_S16 fr_Z /\
     (hz_M frc_S16 fr_Z + hz_E frc_S16 fr_Z) * fr_Z * 2 + / 10384593717069655257060992658440192 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe16|].
  assert (H1 := frc_M16). assert (H2 := frc_E16). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S16 fr_Z + hz_E frc_S16 fr_Z) * fr_Z * 2
          <= ((4361469 / 44601490397061246283071436545296723011960832) + (10341069586954190977 / 883423532389192164791648750371459257913741948437809479060803100646309888)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe14 : hz_safe frc_S14 fr_Z.
Proof.
  change (hz_safe frc_S14 fr_Z) with
    (hz_safe frc_S15 fr_Z /\
     (hz_M frc_S15 fr_Z + hz_E frc_S15 fr_Z) * fr_Z * 2 + / 10141204801825835211973625643008 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe15|].
  assert (H1 := frc_M15). assert (H2 := frc_E15). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S15 fr_Z + hz_E frc_S15 fr_Z) * fr_Z * 2
          <= ((558678257 / 5575186299632655785383929568162090376495104) + (10376614736295886985 / 862718293348820473429344482784628181556388621521298319395315527974912)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe13 : hz_safe frc_S13 fr_Z.
Proof.
  change (hz_safe frc_S13 fr_Z) with
    (hz_safe frc_S14 fr_Z /\
     (hz_M frc_S14 fr_Z + hz_E frc_S14 fr_Z) * fr_Z * 2 + / 19807040628566084398385987584 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe14|].
  assert (H1 := frc_M14). assert (H2 := frc_E14). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S14 fr_Z + hz_E frc_S14 fr_Z) * fr_Z * 2
          <= ((71512868021 / 696898287454081973172991196020261297061888) + (10378553813366734985 / 842498333348457493583344221469363458551160763204392890034487820288)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe12 : hz_safe frc_S12 fr_Z.
Proof.
  change (hz_safe frc_S12 fr_Z) with
    (hz_safe frc_S13 fr_Z /\
     (hz_M frc_S13 fr_Z + hz_E frc_S13 fr_Z) * fr_Z * 2 + / 19342813113834066795298816 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe13|].
  assert (H1 := frc_M13). assert (H2 := frc_E13). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S13 fr_Z + hz_E frc_S13 fr_Z) * fr_Z * 2
          <= ((4755610851209 / 87112285931760246646623899502532662132736) + (5766965047741907081 / 822752278660603021077484591278675252491367932816789931674304512)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe11 : hz_safe frc_S11 fr_Z.
Proof.
  change (hz_safe frc_S11 fr_Z) with
    (hz_safe frc_S12 fr_Z /\
     (hz_M frc_S12 fr_Z + hz_E frc_S12 fr_Z) * fr_Z * 2 + / 37778931862957161709568 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe12|].
  assert (H1 := frc_M12). assert (H2 := frc_E12). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S12 fr_Z + hz_E frc_S12 fr_Z) * fr_Z * 2
          <= ((586728007677357 / 10889035741470030830827987437816582766592) + (5226537731535847501 / 803469022129495137770981046170581301261101496891396417650688)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe10 : hz_safe frc_S10 fr_Z.
Proof.
  change (hz_safe frc_S10 fr_Z) with
    (hz_safe frc_S11 fr_Z /\
     (hz_M frc_S11 fr_Z + hz_E frc_S11 fr_Z) * fr_Z * 2 + / 73786976294838206464 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe11|].
  assert (H1 := frc_M11). assert (H2 := frc_E11). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S11 fr_Z + hz_E frc_S11 fr_Z) * fr_Z * 2
          <= ((38962437057350753 / 1361129467683753853853498429727072845824) + (11542042257061286165 / 3138550867693340381917894711603833208051177722232017256448)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe9 : hz_safe frc_S9 fr_Z.
Proof.
  change (hz_safe frc_S9 fr_Z) with
    (hz_safe frc_S10 fr_Z /\
     (hz_M frc_S10 fr_Z + hz_E frc_S10 fr_Z) * fr_Z * 2 + / 144115188075855872 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe10|].
  assert (H1 := frc_M10). assert (H2 := frc_E10). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S10 fr_Z + hz_E frc_S10 fr_Z) * fr_Z * 2
          <= ((2500655194500447717 / 170141183460469231731687303715884105728) + (11683591570481719197 / 6129982163463555433433388108601236734474956488734408704)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe8 : hz_safe frc_S8 fr_Z.
Proof.
  change (hz_safe frc_S8 fr_Z) with
    (hz_safe frc_S9 fr_Z /\
     (hz_M frc_S9 fr_Z + hz_E frc_S9 fr_Z) * fr_Z * 2 + / 562949953421312 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe9|].
  assert (H1 := frc_M9). assert (H2 := frc_E9). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S9 fr_Z + hz_E frc_S9 fr_Z) * fr_Z * 2
          <= ((160077228562178651513 / 21267647932558653966460912964485513216) + (11699062124861440233 / 11972621413014756705924586149611790497021399392059392)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe7 : hz_safe frc_S7 fr_Z.
Proof.
  change (hz_safe frc_S7 fr_Z) with
    (hz_safe frc_S8 fr_Z /\
     (hz_M frc_S8 fr_Z + hz_E frc_S8 fr_Z) * fr_Z * 2 + / 2199023255552 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe8|].
  assert (H1 := frc_M8). assert (H2 := frc_E8). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S8 fr_Z + hz_E frc_S8 fr_Z) * fr_Z * 2
          <= ((5522752625680538471261 / 2658455991569831745807614120560689152) + (3544464716054857053 / 11692013098647223345629478661730264157247460343808)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe6 : hz_safe frc_S6 fr_Z.
Proof.
  change (hz_safe frc_S6 fr_Z) with
    (hz_safe frc_S7 fr_Z /\
     (hz_M frc_S7 fr_Z + hz_E frc_S7 fr_Z) * fr_Z * 2 + / 8589934592 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe7|].
  assert (H1 := frc_M7). assert (H2 := frc_E7). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S7 fr_Z + hz_E frc_S7 fr_Z) * fr_Z * 2
          <= ((178729490580231339194577 / 332306998946228968225951765070086144) + (14809483178774156427 / 182687704666362864775460604089535377456991567872)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe5 : hz_safe frc_S5 fr_Z.
Proof.
  change (hz_safe frc_S5 fr_Z) with
    (hz_safe frc_S6 fr_Z /\
     (hz_M frc_S6 fr_Z + hz_E frc_S6 fr_Z) * fr_Z * 2 + / 67108864 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe6|].
  assert (H1 := frc_M6). assert (H2 := frc_E6). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S6 fr_Z + hz_E frc_S6 fr_Z) * fr_Z * 2
          <= ((5729350731359673394797589 / 41538374868278621028243970633760768) + (14946348278553026875 / 713623846352979940529142984724747568191373312)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe4 : hz_safe frc_S4 fr_Z.
Proof.
  change (hz_safe frc_S4 fr_Z) with
    (hz_safe frc_S5 fr_Z /\
     (hz_M frc_S5 fr_Z + hz_E frc_S5 fr_Z) * fr_Z * 2 + / 524288 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe5|].
  assert (H1 := frc_M5). assert (H2 := frc_E5). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S5 fr_Z + hz_E frc_S5 fr_Z) * fr_Z * 2
          <= ((106018006112134634155183209 / 5192296858534827628530496329220096) + (10362012088314477193 / 2787593149816327892691964784081045188247552)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe3 : hz_safe frc_S3 fr_Z.
Proof.
  change (hz_safe frc_S3 fr_Z) with
    (hz_safe frc_S4 fr_Z /\
     (hz_M frc_S4 fr_Z + hz_E frc_S4 fr_Z) * fr_Z * 2 + / 8192 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe4|].
  assert (H1 := frc_M4). assert (H2 := frc_E4). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S4 fr_Z + hz_E frc_S4 fr_Z) * fr_Z * 2
          <= ((1768030069846053445675040269 / 649037107316853453566312041152512) + (11799293292343773571 / 21778071482940061661655974875633165533184)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe2 : hz_safe frc_S2 fr_Z.
Proof.
  change (hz_safe frc_S2 fr_Z) with
    (hz_safe frc_S3 fr_Z /\
     (hz_M frc_S3 fr_Z + hz_E frc_S3 fr_Z) * fr_Z * 2 + / 128 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe3|].
  assert (H1 := frc_M3). assert (H2 := frc_E3). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S3 fr_Z + hz_E frc_S3 fr_Z) * fr_Z * 2
          <= ((18743670663513309427568195137 / 81129638414606681695789005144064) + (10109637954687651245 / 170141183460469231731687303715884105728)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe1 : hz_safe frc_S1 fr_Z.
Proof.
  change (hz_safe frc_S1 fr_Z) with
    (hz_safe frc_S2 fr_Z /\
     (hz_M frc_S2 fr_Z + hz_E frc_S2 fr_Z) * fr_Z * 2 + / 8 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe2|].
  assert (H1 := frc_M2). assert (H2 := frc_E2). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S2 fr_Z + hz_E frc_S2 fr_Z) * fr_Z * 2
          <= ((172946515831830884731384926021 / 10141204801825835211973625643008) + (1759936607771365563 / 332306998946228968225951765070086144)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frc_safe0 : hz_safe frc_S0 fr_Z.
Proof.
  change (hz_safe frc_S0 fr_Z) with
    (hz_safe frc_S1 fr_Z /\
     (hz_M frc_S1 fr_Z + hz_E frc_S1 fr_Z) * fr_Z * 2 + 1 + 1
       <= bpow radix2 1000).
  split; [exact frc_safe1|].
  assert (H1 := frc_M1). assert (H2 := frc_E1). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frc_S1 fr_Z + hz_E frc_S1 fr_Z) * fr_Z * 2
          <= ((1023188904187683098844012530777 / 1267650600228229401496703205376) + (3916975346181443827 / 10384593717069655257060992658440192)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.

Lemma frc_M_bound : hz_M frc_ms fr_Z <= (9594079248867172591 / 288230376151711744).
Proof. unfold frc_ms. eapply Rle_trans; [exact frc_M0|]. lra. Qed.

Lemma frc_L_bound : hz_L frc_ms fr_Z <= (2423780116726494467 / 1152921504606846976).
Proof. unfold frc_ms. eapply Rle_trans; [exact frc_L0|]. lra. Qed.

Theorem frc_eval_err : forall z : binary64,
  fin z = true -> Rabs (B2R z) <= 40 ->
  fin (b64_horner frc_coeffs z) = true /\
  Rabs (B2R (b64_horner frc_coeffs z) - hz_horner_R (map B2R frc_coeffs) (B2R z))
    <= (1814677549481158795 / 81129638414606681695789005144064).
Proof.
  intros z Fz Hz.
  destruct (b64_horner_err frc_coeffs frc_ms z fr_Z frc_coeffs_ok Fz Hz
              fr_Z_nonneg frc_safe0) as [F E].
  split; [exact F|]. eapply Rle_trans; [exact E|]. unfold frc_ms. exact frc_E0.
Qed.

Definition frc_exact : list R :=
  [1; - / 10; / 216; - / 9360; / 685440; - / 76204800; / 11975040000; - / 2528170444800; / 690452066304000; - / 236887827111936000; / 99748982335242240000; - / 50580032749992345600000; / 30401971684928732528640000; - / 21374447439710098685952000000; / 17378635642867690048585728000000; - / 16180424448543654576814817280000000; / 17103504400690079460869170790400000000; - / 20371063133732685718485684065402880000000; / 27155512855662788875163959715010969600000000; - / 40272741544928285605520556255705720422400000000].

Definition frc_delta : list R :=
  [B2R frc_c0 - (1);
   B2R frc_c1 - (- / 10);
   B2R frc_c2 - (/ 216);
   B2R frc_c3 - (- / 9360);
   B2R frc_c4 - (/ 685440);
   B2R frc_c5 - (- / 76204800);
   B2R frc_c6 - (/ 11975040000);
   B2R frc_c7 - (- / 2528170444800);
   B2R frc_c8 - (/ 690452066304000);
   B2R frc_c9 - (- / 236887827111936000);
   B2R frc_c10 - (/ 99748982335242240000);
   B2R frc_c11 - (- / 50580032749992345600000);
   B2R frc_c12 - (/ 30401971684928732528640000);
   B2R frc_c13 - (- / 21374447439710098685952000000);
   B2R frc_c14 - (/ 17378635642867690048585728000000);
   B2R frc_c15 - (- / 16180424448543654576814817280000000);
   B2R frc_c16 - (/ 17103504400690079460869170790400000000);
   B2R frc_c17 - (- / 20371063133732685718485684065402880000000);
   B2R frc_c18 - (/ 27155512855662788875163959715010969600000000);
   B2R frc_c19 - (- / 40272741544928285605520556255705720422400000000)].

Lemma frc_delta_eq : forall x,
  hz_horner_R (map B2R frc_coeffs) x - hz_horner_R frc_exact x = hz_horner_R frc_delta x.
Proof. intro x. unfold frc_coeffs, frc_exact, frc_delta. cbn [map hz_horner_R]. ring. Qed.

Definition frc_ds : list R :=
  [0; / 144115188075855872; / 2305843009213693952; / 9444732965739290427392; / 9444732965739290427392; / 1208925819614629174706176; / 618970019642690137449562112; / 79228162514264337593543950336; / 10141204801825835211973625643008; / 83076749736557242056487941267521536; / 5316911983139663491615228241121378304; / 1361129467683753853853498429727072845824; / 348449143727040986586495598010130648530944; / 356811923176489970264571492362373784095686656; / 1461501637330902918203684832716283019655932542976; / 5986310706507378352962293074805895248510699696029696; / 191561942608236107294793378393788647952342390272950272; / 392318858461667547739736838950479151006397215279002157056; / 1606938044258990275541962092341162602522202993782792835301376; / 411376139330301510538742295639337626245683966408394965837152256].

Lemma frc_delta_ok : Forall2 (fun c m => Rabs c <= m) frc_delta frc_ds.
Proof.
  unfold frc_delta, frc_ds, frc_c0, frc_c1, frc_c2, frc_c3, frc_c4, frc_c5, frc_c6, frc_c7, frc_c8, frc_c9, frc_c10, frc_c11, frc_c12, frc_c13, frc_c14, frc_c15, frc_c16, frc_c17, frc_c18, frc_c19.
  repeat (apply Forall2_cons; [cbn [Binary.B2R]; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma frc_ds_M : hz_M frc_ds fr_Z <= (3487438286539289211 / 2596148429267413814265248164610048).
Proof. unfold frc_ds, fr_Z. cbn [hz_M]. lra. Qed.

Lemma frc_coef_err : forall x, Rabs x <= 40 ->
  Rabs (hz_horner_R (map B2R frc_coeffs) x - hz_horner_R frc_exact x) <= (3487438286539289211 / 2596148429267413814265248164610048).
Proof.
  intros x Hx. rewrite frc_delta_eq.
  eapply Rle_trans; [apply (hz_horner_R_bound_R _ frc_ds x fr_Z frc_delta_ok); unfold fr_Z; exact Hx|].
  exact frc_ds_M.
Qed.

Lemma frc_P_bound : forall y, Rabs y <= 40 ->
  Rabs (hz_horner_R (map B2R frc_coeffs) y) <= (9594079248867172591 / 288230376151711744).
Proof.
  intros y Hy.
  eapply Rle_trans; [apply (hz_horner_R_bound frc_coeffs frc_ms y fr_Z frc_coeffs_ok);
                     unfold fr_Z; exact Hy|].
  exact frc_M_bound.
Qed.

Lemma frc_P_lip : forall y v, Rabs y <= 40 -> Rabs v <= 40 ->
  Rabs (hz_horner_R (map B2R frc_coeffs) y - hz_horner_R (map B2R frc_coeffs) v)
    <= (2423780116726494467 / 1152921504606846976) * Rabs (y - v).
Proof.
  intros y v Hy Hv.
  eapply Rle_trans;
    [apply (hz_horner_R_lip (map B2R frc_coeffs) frc_ms y v fr_Z frc_coeffs_ok_R);
     unfold fr_Z; assumption|].
  apply Rmult_le_compat_r; [apply Rabs_pos | exact frc_L_bound].
Qed.

Lemma fr_INR_fact_S : forall n, INR (fact (S n)) = INR (S n) * INR (fact n).
Proof. intro n. rewrite fact_simpl, mult_INR. reflexivity. Qed.

(* The exact C polynomial is the S6 partial sum fz_C 19 at a = 1. *)
Lemma frc_fz_eq : forall x, fz_C 19 1 x = x * hz_horner_R frc_exact (x * x * (x * x)).
Proof.
  intro x. unfold fz_C, fz_Cterm. cbn [sum_f_R0 Nat.mul Nat.add].
  rewrite !pow1.
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (fr_INR_fact_S n) end.
  replace (INR (fact 0)) with 1 by reflexivity.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. unfold frc_exact. cbn [hz_horner_R].
  field.
Qed.

Print Assumptions frc_eval_err.
Print Assumptions frc_coef_err.
Print Assumptions frc_fz_eq.
