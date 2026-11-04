(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_FresnelPolyS
   ----------------------------------------------------------------------------
   S7 polynomial facts, S half: Q(z) = sum_{k<=18} (-1)^k z^k / ((2k+1)! (4k+3)),
   S(x) = x^3 Q(x^4), on the B64_Horner kernel for |z| <= 40.  Shares fr_Z,
   fr_e0_bounds, fr_bpow1000, fr_INR_fact_S with B64_FresnelPolyC.
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
  B64_AbsErr B64_Horner B64_SinPoly B64_FresnelPolyC.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* Fresnel S: (-1)^k / ((2k+1)! (4k+3)), rounded to nearest binary64. *)
Definition frs_c0 : binary64 :=
  Binary.B754_finite prec emax false 6004799503160661 (-54) eq_refl.
Definition frs_c1 : binary64 :=
  Binary.B754_finite prec emax true 6862628003612184 (-58) eq_refl.
Definition frs_c2 : binary64 :=
  Binary.B754_finite prec emax false 6987403058223315 (-63) eq_refl.
Definition frs_c3 : binary64 :=
  Binary.B754_finite prec emax true 7808145639665419 (-69) eq_refl.
Definition frs_c4 : binary64 :=
  Binary.B754_finite prec emax false 5479400448888013 (-75) eq_refl.
Definition frs_c5 : binary64 :=
  Binary.B754_finite prec emax true 5267154897903418 (-82) eq_refl.
Definition frs_c6 : binary64 :=
  Binary.B754_finite prec emax false 7363012354903924 (-90) eq_refl.
Definition frs_c7 : binary64 :=
  Binary.B754_finite prec emax true 7817686850552369 (-98) eq_refl.
Definition frs_c8 : binary64 :=
  Binary.B754_finite prec emax false 6516928870376428 (-106) eq_refl.
Definition frs_c9 : binary64 :=
  Binary.B754_finite prec emax true 8755687911017064 (-115) eq_refl.
Definition frs_c10 : binary64 :=
  Binary.B754_finite prec emax false 4840353715592157 (-123) eq_refl.
Definition frs_c11 : binary64 :=
  Binary.B754_finite prec emax true 8961838987677818 (-133) eq_refl.
Definition frs_c12 : binary64 :=
  Binary.B754_finite prec emax false 7047637039198661 (-142) eq_refl.
Definition frs_c13 : binary64 :=
  Binary.B754_finite prec emax true 4766327334047020 (-151) eq_refl.
Definition frs_c14 : binary64 :=
  Binary.B754_finite prec emax false 5603230263286469 (-161) eq_refl.
Definition frs_c15 : binary64 :=
  Binary.B754_finite prec emax true 5777859013256790 (-171) eq_refl.
Definition frs_c16 : binary64 :=
  Binary.B754_finite prec emax false 5268278503268063 (-181) eq_refl.
Definition frs_c17 : binary64 :=
  Binary.B754_finite prec emax true 8555948669717488 (-192) eq_refl.
Definition frs_c18 : binary64 :=
  Binary.B754_finite prec emax false 6226743664495898 (-202) eq_refl.

Definition frs_coeffs : list binary64 :=
  [frs_c0; frs_c1; frs_c2; frs_c3; frs_c4; frs_c5; frs_c6; frs_c7; frs_c8; frs_c9; frs_c10; frs_c11; frs_c12; frs_c13; frs_c14; frs_c15; frs_c16; frs_c17; frs_c18].

Definition frs_S18 : list R := [/ 713623846352979940529142984724747568191373312].
Definition frs_S17 : list R := / 696898287454081973172991196020261297061888 :: frs_S18.
Definition frs_S16 : list R := / 340282366920938463463374607431768211456 :: frs_S17.
Definition frs_S15 : list R := / 332306998946228968225951765070086144 :: frs_S16.
Definition frs_S14 : list R := / 324518553658426726783156020576256 :: frs_S15.
Definition frs_S13 : list R := / 316912650057057350374175801344 :: frs_S14.
Definition frs_S12 : list R := / 618970019642690137449562112 :: frs_S13.
Definition frs_S11 : list R := / 1208925819614629174706176 :: frs_S12.
Definition frs_S10 : list R := / 1180591620717411303424 :: frs_S11.
Definition frs_S9 : list R := / 4611686018427387904 :: frs_S10.
Definition frs_S8 : list R := / 9007199254740992 :: frs_S9.
Definition frs_S7 : list R := / 35184372088832 :: frs_S8.
Definition frs_S6 : list R := / 137438953472 :: frs_S7.
Definition frs_S5 : list R := / 536870912 :: frs_S6.
Definition frs_S4 : list R := / 4194304 :: frs_S5.
Definition frs_S3 : list R := / 65536 :: frs_S4.
Definition frs_S2 : list R := / 1024 :: frs_S3.
Definition frs_S1 : list R := / 32 :: frs_S2.
Definition frs_S0 : list R := / 2 :: frs_S1.
Definition frs_ms : list R := frs_S0.

Lemma frs_coeffs_ok : hz_coeffs_ok frs_coeffs frs_ms.
Proof.
  unfold hz_coeffs_ok, frs_coeffs, frs_ms, frs_S0, frs_S1, frs_S2, frs_S3, frs_S4, frs_S5, frs_S6, frs_S7, frs_S8, frs_S9, frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18.
  repeat (apply Forall2_cons;
          [split; [reflexivity|]; cbn; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma frs_coeffs_ok_R : Forall2 (fun c m => Rabs c <= m) (map B2R frs_coeffs) frs_ms.
Proof.
  generalize frs_coeffs_ok. unfold hz_coeffs_ok.
  generalize frs_coeffs frs_ms. intros cs ms H.
  induction H as [|c m cs ms [_ Hm] _ IH]; cbn; constructor; assumption.
Qed.

Lemma frs_S18_nonneg : Forall (fun m => 0 <= m) frs_S18.
Proof. unfold frs_S18. repeat constructor; lra. Qed.
Lemma frs_S17_nonneg : Forall (fun m => 0 <= m) frs_S17.
Proof. unfold frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S16_nonneg : Forall (fun m => 0 <= m) frs_S16.
Proof. unfold frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S15_nonneg : Forall (fun m => 0 <= m) frs_S15.
Proof. unfold frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S14_nonneg : Forall (fun m => 0 <= m) frs_S14.
Proof. unfold frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S13_nonneg : Forall (fun m => 0 <= m) frs_S13.
Proof. unfold frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S12_nonneg : Forall (fun m => 0 <= m) frs_S12.
Proof. unfold frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S11_nonneg : Forall (fun m => 0 <= m) frs_S11.
Proof. unfold frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S10_nonneg : Forall (fun m => 0 <= m) frs_S10.
Proof. unfold frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S9_nonneg : Forall (fun m => 0 <= m) frs_S9.
Proof. unfold frs_S9, frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S8_nonneg : Forall (fun m => 0 <= m) frs_S8.
Proof. unfold frs_S8, frs_S9, frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S7_nonneg : Forall (fun m => 0 <= m) frs_S7.
Proof. unfold frs_S7, frs_S8, frs_S9, frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S6_nonneg : Forall (fun m => 0 <= m) frs_S6.
Proof. unfold frs_S6, frs_S7, frs_S8, frs_S9, frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S5_nonneg : Forall (fun m => 0 <= m) frs_S5.
Proof. unfold frs_S5, frs_S6, frs_S7, frs_S8, frs_S9, frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S4_nonneg : Forall (fun m => 0 <= m) frs_S4.
Proof. unfold frs_S4, frs_S5, frs_S6, frs_S7, frs_S8, frs_S9, frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S3_nonneg : Forall (fun m => 0 <= m) frs_S3.
Proof. unfold frs_S3, frs_S4, frs_S5, frs_S6, frs_S7, frs_S8, frs_S9, frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S2_nonneg : Forall (fun m => 0 <= m) frs_S2.
Proof. unfold frs_S2, frs_S3, frs_S4, frs_S5, frs_S6, frs_S7, frs_S8, frs_S9, frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S1_nonneg : Forall (fun m => 0 <= m) frs_S1.
Proof. unfold frs_S1, frs_S2, frs_S3, frs_S4, frs_S5, frs_S6, frs_S7, frs_S8, frs_S9, frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_S0_nonneg : Forall (fun m => 0 <= m) frs_S0.
Proof. unfold frs_S0, frs_S1, frs_S2, frs_S3, frs_S4, frs_S5, frs_S6, frs_S7, frs_S8, frs_S9, frs_S10, frs_S11, frs_S12, frs_S13, frs_S14, frs_S15, frs_S16, frs_S17, frs_S18. repeat constructor; lra. Qed.
Lemma frs_M18 : hz_M frs_S18 fr_Z <= (1 / 713623846352979940529142984724747568191373312).
Proof. unfold frs_S18, fr_Z. cbn [hz_M]. lra. Qed.
Lemma frs_M17 : hz_M frs_S17 fr_Z <= (133 / 89202980794122492566142873090593446023921664).
Proof.
  change (hz_M frs_S17 fr_Z) with (hz_M frs_S18 fr_Z * fr_Z + / 696898287454081973172991196020261297061888).
  assert (H := frs_M18). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S18 fr_Z * fr_Z <= (1 / 713623846352979940529142984724747568191373312) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M16 : hz_M frs_S16 fr_Z <= (33433 / 11150372599265311570767859136324180752990208).
Proof.
  change (hz_M frs_S16 fr_Z) with (hz_M frs_S17 fr_Z * fr_Z + / 340282366920938463463374607431768211456).
  assert (H := frs_M17). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S17 fr_Z * fr_Z <= (133 / 89202980794122492566142873090593446023921664) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M15 : hz_M frs_S15 fr_Z <= (4361469 / 1393796574908163946345982392040522594123776).
Proof.
  change (hz_M frs_S15 fr_Z) with (hz_M frs_S16 fr_Z * fr_Z + / 332306998946228968225951765070086144).
  assert (H := frs_M16). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S16 fr_Z * fr_Z <= (33433 / 11150372599265311570767859136324180752990208) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M14 : hz_M frs_S14 fr_Z <= (558678257 / 174224571863520493293247799005065324265472).
Proof.
  change (hz_M frs_S14 fr_Z) with (hz_M frs_S15 fr_Z * fr_Z + / 324518553658426726783156020576256).
  assert (H := frs_M15). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S15 fr_Z * fr_Z <= (4361469 / 1393796574908163946345982392040522594123776) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M13 : hz_M frs_S13 fr_Z <= (71512868021 / 21778071482940061661655974875633165533184).
Proof.
  change (hz_M frs_S13 fr_Z) with (hz_M frs_S14 fr_Z * fr_Z + / 316912650057057350374175801344).
  assert (H := frs_M14). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S14 fr_Z * fr_Z <= (558678257 / 174224571863520493293247799005065324265472) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M12 : hz_M frs_S12 fr_Z <= (4755610851209 / 2722258935367507707706996859454145691648).
Proof.
  change (hz_M frs_S12 fr_Z) with (hz_M frs_S13 fr_Z * fr_Z + / 618970019642690137449562112).
  assert (H := frs_M13). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S13 fr_Z * fr_Z <= (71512868021 / 21778071482940061661655974875633165533184) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M11 : hz_M frs_S11 fr_Z <= (305253030966701 / 340282366920938463463374607431768211456).
Proof.
  change (hz_M frs_S11 fr_Z) with (hz_M frs_S12 fr_Z * fr_Z + / 1208925819614629174706176).
  assert (H := frs_M12). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S12 fr_Z * fr_Z <= (4755610851209 / 2722258935367507707706996859454145691648) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M10 : hz_M frs_S10 fr_Z <= (37555062173797473 / 42535295865117307932921825928971026432).
Proof.
  change (hz_M frs_S10 fr_Z) with (hz_M frs_S11 fr_Z * fr_Z + / 1180591620717411303424).
  assert (H := frs_M11). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S11 fr_Z * fr_Z <= (305253030966701 / 340282366920938463463374607431768211456) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M9 : hz_M frs_S9 fr_Z <= (1340696815475834341 / 5316911983139663491615228241121378304).
Proof.
  change (hz_M frs_S9 fr_Z) with (hz_M frs_S10 fr_Z * fr_Z + / 4611686018427387904).
  assert (H := frs_M10). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S10 fr_Z * fr_Z <= (37555062173797473 / 42535295865117307932921825928971026432) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M8 : hz_M frs_S8 fr_Z <= (80490460372217378169 / 664613997892457936451903530140172288).
Proof.
  change (hz_M frs_S8 fr_Z) with (hz_M frs_S9 fr_Z * fr_Z + / 9007199254740992).
  assert (H := frs_M9). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S9 fr_Z * fr_Z <= (1340696815475834341 / 5316911983139663491615228241121378304) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M7 : hz_M frs_S7 fr_Z <= (2763635543295909497693 / 83076749736557242056487941267521536).
Proof.
  change (hz_M frs_S7 fr_Z) with (hz_M frs_S8 fr_Z * fr_Z + / 35184372088832).
  assert (H := frs_M8). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S8 fr_Z * fr_Z <= (80490460372217378169 / 664613997892457936451903530140172288) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M6 : hz_M frs_S6 fr_Z <= (89376041442393870907601 / 10384593717069655257060992658440192).
Proof.
  change (hz_M frs_S6 fr_Z) with (hz_M frs_S7 fr_Z * fr_Z + / 137438953472).
  assert (H := frs_M7). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S7 fr_Z * fr_Z <= (2763635543295909497693 / 83076749736557242056487941267521536) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M5 : hz_M frs_S5 fr_Z <= (2864731846441227703950357 / 1298074214633706907132624082305024).
Proof.
  change (hz_M frs_S5 fr_Z) with (hz_M frs_S6 fr_Z * fr_Z + / 536870912).
  assert (H := frs_M6). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S6 fr_Z * fr_Z <= (89376041442393870907601 / 10384593717069655257060992658440192) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M4 : hz_M frs_S4 fr_Z <= (53009285459874272110349417 / 162259276829213363391578010288128).
Proof.
  change (hz_M frs_S4 fr_Z) with (hz_M frs_S5 fr_Z * fr_Z + / 4194304).
  assert (H := frs_M5). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S5 fr_Z * fr_Z <= (2864731846441227703950357 / 1298074214633706907132624082305024) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M3 : hz_M frs_S3 fr_Z <= (574531437120716429276528141 / 20282409603651670423947251286016).
Proof.
  change (hz_M frs_S3 fr_Z) with (hz_M frs_S4 fr_Z * fr_Z + / 65536).
  assert (H := frs_M4). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S4 fr_Z * fr_Z <= (53009285459874272110349417 / 162259276829213363391578010288128) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M2 : hz_M frs_S2 fr_Z <= (5348537264174342696180889153 / 2535301200456458802993406410752).
Proof.
  change (hz_M frs_S2 fr_Z) with (hz_M frs_S3 fr_Z * fr_Z + / 1024).
  assert (H := frs_M3). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S3 fr_Z * fr_Z <= (574531437120716429276528141 / 20282409603651670423947251286016) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M1 : hz_M frs_S1 fr_Z <= (36646206635154755680097439557 / 316912650057057350374175801344).
Proof.
  change (hz_M frs_S1 fr_Z) with (hz_M frs_S2 fr_Z * fr_Z + / 32).
  assert (H := frs_M2). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S2 fr_Z * fr_Z <= (5348537264174342696180889153 / 2535301200456458802993406410752) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_M0 : hz_M frs_S0 fr_Z <= (203038073804339862798873185369 / 39614081257132168796771975168).
Proof.
  change (hz_M frs_S0 fr_Z) with (hz_M frs_S1 fr_Z * fr_Z + / 2).
  assert (H := frs_M1). assert (HZ := fr_Z_nonneg).
  assert (hz_M frs_S1 fr_Z * fr_Z <= (36646206635154755680097439557 / 316912650057057350374175801344) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L18 : hz_L frs_S18 fr_Z <= 0.
Proof. unfold frs_S18. cbn. lra. Qed.
Lemma frs_L17 : hz_L frs_S17 fr_Z <= (1 / 713623846352979940529142984724747568191373312).
Proof.
  change (hz_L frs_S17 fr_Z) with (hz_L frs_S18 fr_Z * fr_Z + hz_M frs_S18 fr_Z).
  assert (H := frs_L18). assert (H2 := frs_M18). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S18 fr_Z * fr_Z <= 0 * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L16 : hz_L frs_S16 fr_Z <= (69 / 44601490397061246283071436545296723011960832).
Proof.
  change (hz_L frs_S16 fr_Z) with (hz_L frs_S17 fr_Z * fr_Z + hz_M frs_S17 fr_Z).
  assert (H := frs_L17). assert (H2 := frs_M17). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S17 fr_Z * fr_Z <= (1 / 713623846352979940529142984724747568191373312) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L15 : hz_L frs_S15 fr_Z <= (34123 / 11150372599265311570767859136324180752990208).
Proof.
  change (hz_L frs_S15 fr_Z) with (hz_L frs_S16 fr_Z * fr_Z + hz_M frs_S16 fr_Z).
  assert (H := frs_L16). assert (H2 := frs_M16). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S16 fr_Z * fr_Z <= (69 / 44601490397061246283071436545296723011960832) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L14 : hz_L frs_S14 fr_Z <= (1133021 / 348449143727040986586495598010130648530944).
Proof.
  change (hz_L frs_S14 fr_Z) with (hz_L frs_S15 fr_Z * fr_Z + hz_M frs_S15 fr_Z).
  assert (H := frs_L15). assert (H2 := frs_M15). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S15 fr_Z * fr_Z <= (34123 / 11150372599265311570767859136324180752990208) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L13 : hz_L frs_S13 fr_Z <= (581338677 / 174224571863520493293247799005065324265472).
Proof.
  change (hz_L frs_S13 fr_Z) with (hz_L frs_S14 fr_Z * fr_Z + hz_M frs_S14 fr_Z).
  assert (H := frs_L14). assert (H2 := frs_M14). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S14 fr_Z * fr_Z <= (1133021 / 348449143727040986586495598010130648530944) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L12 : hz_L frs_S12 fr_Z <= (37209780703 / 10889035741470030830827987437816582766592).
Proof.
  change (hz_L frs_S12 fr_Z) with (hz_L frs_S13 fr_Z * fr_Z + hz_M frs_S13 fr_Z).
  assert (H := frs_L13). assert (H2 := frs_M13). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S13 fr_Z * fr_Z <= (581338677 / 174224571863520493293247799005065324265472) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L11 : hz_L frs_S11 fr_Z <= (5127708658239 / 2722258935367507707706996859454145691648).
Proof.
  change (hz_L frs_S11 fr_Z) with (hz_L frs_S12 fr_Z * fr_Z + hz_M frs_S12 fr_Z).
  assert (H := frs_L12). assert (H2 := frs_M12). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S12 fr_Z * fr_Z <= (37209780703 / 10889035741470030830827987437816582766592) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L10 : hz_L frs_S10 fr_Z <= (41361446782237 / 42535295865117307932921825928971026432).
Proof.
  change (hz_L frs_S10 fr_Z) with (hz_L frs_S11 fr_Z * fr_Z + hz_M frs_S11 fr_Z).
  assert (H := frs_L11). assert (H2 := frs_M11). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S11 fr_Z * fr_Z <= (5127708658239 / 2722258935367507707706996859454145691648) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L9 : hz_L frs_S9 fr_Z <= (39209520045086953 / 42535295865117307932921825928971026432).
Proof.
  change (hz_L frs_S9 fr_Z) with (hz_L frs_S10 fr_Z * fr_Z + hz_M frs_S10 fr_Z).
  assert (H := frs_L10). assert (H2 := frs_M10). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S10 fr_Z * fr_Z <= (41361446782237 / 42535295865117307932921825928971026432) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L8 : hz_L frs_S8 fr_Z <= (768372207850634553 / 2658455991569831745807614120560689152).
Proof.
  change (hz_L frs_S8 fr_Z) with (hz_L frs_S9 fr_Z * fr_Z + hz_M frs_S9 fr_Z).
  assert (H := frs_L9). assert (H2 := frs_M9). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S9 fr_Z * fr_Z <= (39209520045086953 / 42535295865117307932921825928971026432) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L7 : hz_L frs_S7 fr_Z <= (88174182450723723699 / 664613997892457936451903530140172288).
Proof.
  change (hz_L frs_S7 fr_Z) with (hz_L frs_S8 fr_Z * fr_Z + hz_M frs_S8 fr_Z).
  assert (H := frs_L8). assert (H2 := frs_M8). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S8 fr_Z * fr_Z <= (768372207850634553 / 2658455991569831745807614120560689152) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L6 : hz_L frs_S6 fr_Z <= (801126613887382029047 / 20769187434139310514121985316880384).
Proof.
  change (hz_L frs_S6 fr_Z) with (hz_L frs_S7 fr_Z * fr_Z + hz_M frs_S7 fr_Z).
  assert (H := frs_L7). assert (H2 := frs_M7). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S7 fr_Z * fr_Z <= (88174182450723723699 / 664613997892457936451903530140172288) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L5 : hz_L frs_S5 fr_Z <= (105398573720141511488541 / 10384593717069655257060992658440192).
Proof.
  change (hz_L frs_S5 fr_Z) with (hz_L frs_S6 fr_Z * fr_Z + hz_M frs_S6 fr_Z).
  assert (H := frs_L6). assert (H2 := frs_M6). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S6 fr_Z * fr_Z <= (801126613887382029047 / 20769187434139310514121985316880384) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L4 : hz_L frs_S4 fr_Z <= (1695862357520967630696531 / 649037107316853453566312041152512).
Proof.
  change (hz_L frs_S4 fr_Z) with (hz_L frs_S5 fr_Z * fr_Z + hz_M frs_S5 fr_Z).
  assert (H := frs_L5). assert (H2 := frs_M5). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S5 fr_Z * fr_Z <= (105398573720141511488541 / 10384593717069655257060992658440192) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L3 : hz_L frs_S3 fr_Z <= (69967909035083948417314727 / 162259276829213363391578010288128).
Proof.
  change (hz_L frs_S3 fr_Z) with (hz_L frs_S4 fr_Z * fr_Z + hz_M frs_S4 fr_Z).
  assert (H := frs_L4). assert (H2 := frs_M4). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S4 fr_Z * fr_Z <= (1695862357520967630696531 / 649037107316853453566312041152512) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L2 : hz_L frs_S2 fr_Z <= (57773186393508510710193861 / 1267650600228229401496703205376).
Proof.
  change (hz_L frs_S2 fr_Z) with (hz_L frs_S3 fr_Z * fr_Z + hz_M frs_S3 fr_Z).
  assert (H := frs_L3). assert (H2 := frs_M3). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S3 fr_Z * fr_Z <= (69967909035083948417314727 / 162259276829213363391578010288128) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L1 : hz_L frs_S1 fr_Z <= (9970392175655023552996398033 / 2535301200456458802993406410752).
Proof.
  change (hz_L frs_S1 fr_Z) with (hz_L frs_S2 fr_Z * fr_Z + hz_M frs_S2 fr_Z).
  assert (H := frs_L2). assert (H2 := frs_M2). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S2 fr_Z * fr_Z <= (57773186393508510710193861 / 1267650600228229401496703205376) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_L0 : hz_L frs_S0 fr_Z <= (43249083756714936722539714861 / 158456325028528675187087900672).
Proof.
  change (hz_L frs_S0 fr_Z) with (hz_L frs_S1 fr_Z * fr_Z + hz_M frs_S1 fr_Z).
  assert (H := frs_L1). assert (H2 := frs_M1). assert (HZ := fr_Z_nonneg).
  assert (hz_L frs_S1 fr_Z * fr_Z <= (9970392175655023552996398033 / 2535301200456458802993406410752) * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_E18 : hz_E frs_S18 fr_Z <= 0.
Proof. unfold frs_S18. cbn. lra. Qed.
Lemma frs_E17 : hz_E frs_S17 fr_Z <= (9943947977234055209 / 57896044618658097711785492504343953926634992332820282019728792003956564819968).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S17 with ((/ 696898287454081973172991196020261297061888) :: (/ 713623846352979940529142984724747568191373312) :: []).
    apply (hz_E_cons_le (/ 696898287454081973172991196020261297061888) _ _ fr_Z (1 / 713623846352979940529142984724747568191373312) 0);
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S18_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S18_nonneg | exact fr_Z_nonneg]
      |exact frs_M18 | exact frs_E18].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E16 : hz_E frs_S16 fr_Z <= (9791951489810300993 / 28269553036454149273332760011886696253239742350009903329945699220681916416).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S16 with ((/ 340282366920938463463374607431768211456) :: (/ 696898287454081973172991196020261297061888) :: frs_S18).
    apply (hz_E_cons_le (/ 340282366920938463463374607431768211456) _ _ fr_Z (133 / 89202980794122492566142873090593446023921664) (9943947977234055209 / 57896044618658097711785492504343953926634992332820282019728792003956564819968));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S17_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S17_nonneg | exact fr_Z_nonneg]
      |exact frs_M17 | exact frs_E17].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E15 : hz_E frs_S15 fr_Z <= (10341069586954190977 / 27606985387162255149739023449108101809804435888681546220650096895197184).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S15 with ((/ 332306998946228968225951765070086144) :: (/ 340282366920938463463374607431768211456) :: frs_S17).
    apply (hz_E_cons_le (/ 332306998946228968225951765070086144) _ _ fr_Z (33433 / 11150372599265311570767859136324180752990208) (9791951489810300993 / 28269553036454149273332760011886696253239742350009903329945699220681916416));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S16_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S16_nonneg | exact fr_Z_nonneg]
      |exact frs_M16 | exact frs_E16].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E14 : hz_E frs_S14 fr_Z <= (10376614736295886985 / 26959946667150639794667015087019630673637144422540572481103610249216).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S14 with ((/ 324518553658426726783156020576256) :: (/ 332306998946228968225951765070086144) :: frs_S16).
    apply (hz_E_cons_le (/ 324518553658426726783156020576256) _ _ fr_Z (4361469 / 1393796574908163946345982392040522594123776) (10341069586954190977 / 27606985387162255149739023449108101809804435888681546220650096895197184));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S15_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S15_nonneg | exact fr_Z_nonneg]
      |exact frs_M15 | exact frs_E15].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E13 : hz_E frs_S13 fr_Z <= (10378553813366734985 / 26328072917139296674479506920917608079723773850137277813577744384).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S13 with ((/ 316912650057057350374175801344) :: (/ 324518553658426726783156020576256) :: frs_S15).
    apply (hz_E_cons_le (/ 316912650057057350374175801344) _ _ fr_Z (558678257 / 174224571863520493293247799005065324265472) (10376614736295886985 / 26959946667150639794667015087019630673637144422540572481103610249216));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S14_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S14_nonneg | exact fr_Z_nonneg]
      |exact frs_M14 | exact frs_E14].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E12 : hz_E frs_S12 fr_Z <= (5766965047741907081 / 25711008708143844408671393477458601640355247900524685364822016).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S12 with ((/ 618970019642690137449562112) :: (/ 316912650057057350374175801344) :: frs_S14).
    apply (hz_E_cons_le (/ 618970019642690137449562112) _ _ fr_Z (71512868021 / 21778071482940061661655974875633165533184) (10378553813366734985 / 26328072917139296674479506920917608079723773850137277813577744384));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S13_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S13_nonneg | exact fr_Z_nonneg]
      |exact frs_M13 | exact frs_E13].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E11 : hz_E frs_S11 fr_Z <= (2920694722322153549 / 25108406941546723055343157692830665664409421777856138051584).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S11 with ((/ 1208925819614629174706176) :: (/ 618970019642690137449562112) :: frs_S13).
    apply (hz_E_cons_le (/ 1208925819614629174706176) _ _ fr_Z (4755610851209 / 2722258935367507707706996859454145691648) (5766965047741907081 / 25711008708143844408671393477458601640355247900524685364822016));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S12_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S12_nonneg | exact fr_Z_nonneg]
      |exact frs_M12 | exact frs_E12].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E10 : hz_E frs_S10 fr_Z <= (10461178346492367005 / 98079714615416886934934209737619787751599303819750539264).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S10 with ((/ 1180591620717411303424) :: (/ 1208925819614629174706176) :: frs_S12).
    apply (hz_E_cons_le (/ 1180591620717411303424) _ _ fr_Z (305253030966701 / 340282366920938463463374607431768211456) (2920694722322153549 / 25108406941546723055343157692830665664409421777856138051584));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S11_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S11_nonneg | exact fr_Z_nonneg]
      |exact frs_M11 | exact frs_E11].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E9 : hz_E frs_S9 fr_Z <= (13862336127398006523 / 383123885216472214589586756787577295904684780545900544).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S9 with ((/ 4611686018427387904) :: (/ 1180591620717411303424) :: frs_S11).
    apply (hz_E_cons_le (/ 4611686018427387904) _ _ fr_Z (37555062173797473 / 42535295865117307932921825928971026432) (10461178346492367005 / 98079714615416886934934209737619787751599303819750539264));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S10_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S10_nonneg | exact fr_Z_nonneg]
      |exact frs_M10 | exact frs_E10].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E8 : hz_E frs_S8 fr_Z <= (1497779758269067291 / 93536104789177786765035829293842113257979682750464).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S8 with ((/ 9007199254740992) :: (/ 4611686018427387904) :: frs_S10).
    apply (hz_E_cons_le (/ 9007199254740992) _ _ fr_Z (1340696815475834341 / 5316911983139663491615228241121378304) (13862336127398006523 / 383123885216472214589586756787577295904684780545900544));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S9_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S9_nonneg | exact fr_Z_nonneg]
      |exact frs_M9 | exact frs_E9].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E7 : hz_E frs_S7 fr_Z <= (14239755342980851847 / 2923003274661805836407369665432566039311865085952).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S7 with ((/ 35184372088832) :: (/ 9007199254740992) :: frs_S9).
    apply (hz_E_cons_le (/ 35184372088832) _ _ fr_Z (80490460372217378169 / 664613997892457936451903530140172288) (1497779758269067291 / 93536104789177786765035829293842113257979682750464));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S8_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S8_nonneg | exact fr_Z_nonneg]
      |exact frs_M8 | exact frs_E8].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E6 : hz_E frs_S6 fr_Z <= (7410956176628962057 / 5708990770823839524233143877797980545530986496).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S6 with ((/ 137438953472) :: (/ 35184372088832) :: frs_S8).
    apply (hz_E_cons_le (/ 137438953472) _ _ fr_Z (2763635543295909497693 / 83076749736557242056487941267521536) (14239755342980851847 / 2923003274661805836407369665432566039311865085952));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S7_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S7_nonneg | exact fr_Z_nonneg]
      |exact frs_M7 | exact frs_E7].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E5 : hz_E frs_S5 fr_Z <= (7474360625539096479 / 22300745198530623141535718272648361505980416).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S5 with ((/ 536870912) :: (/ 137438953472) :: frs_S7).
    apply (hz_E_cons_le (/ 536870912) _ _ fr_Z (89376041442393870907601 / 10384593717069655257060992658440192) (7410956176628962057 / 5708990770823839524233143877797980545530986496));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S6_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S6_nonneg | exact fr_Z_nonneg]
      |exact frs_M6 | exact frs_E6].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E4 : hz_E frs_S4 fr_Z <= (2590612548896480371 / 43556142965880123323311949751266331066368).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S4 with ((/ 4194304) :: (/ 536870912) :: frs_S6).
    apply (hz_E_cons_le (/ 4194304) _ _ fr_Z (2864731846441227703950357 / 1298074214633706907132624082305024) (7474360625539096479 / 22300745198530623141535718272648361505980416));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S5_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S5_nonneg | exact fr_Z_nonneg]
      |exact frs_M5 | exact frs_E5].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E3 : hz_E frs_S3 fr_Z <= (4746804116187825963 / 680564733841876926926749214863536422912).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S3 with ((/ 65536) :: (/ 4194304) :: frs_S5).
    apply (hz_E_cons_le (/ 65536) _ _ fr_Z (53009285459874272110349417 / 162259276829213363391578010288128) (2590612548896480371 / 43556142965880123323311949751266331066368));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S4_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S4_nonneg | exact fr_Z_nonneg]
      |exact frs_M4 | exact frs_E4].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E2 : hz_E frs_S2 fr_Z <= (6795044563308221659 / 10633823966279326983230456482242756608).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S2 with ((/ 1024) :: (/ 65536) :: frs_S4).
    apply (hz_E_cons_le (/ 1024) _ _ fr_Z (574531437120716429276528141 / 20282409603651670423947251286016) (4746804116187825963 / 680564733841876926926749214863536422912));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S3_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S3_nonneg | exact fr_Z_nonneg]
      |exact frs_M3 | exact frs_E3].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E1 : hz_E frs_S1 fr_Z <= (15873244077864222033 / 332306998946228968225951765070086144).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S1 with ((/ 32) :: (/ 1024) :: frs_S3).
    apply (hz_E_cons_le (/ 32) _ _ fr_Z (5348537264174342696180889153 / 2535301200456458802993406410752) (6795044563308221659 / 10633823966279326983230456482242756608));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S2_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S2_nonneg | exact fr_Z_nonneg]
      |exact frs_M2 | exact frs_E2].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_E0 : hz_E frs_S0 fr_Z <= (7770866424388360789 / 2596148429267413814265248164610048).
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change frs_S0 with ((/ 2) :: (/ 32) :: frs_S2).
    apply (hz_E_cons_le (/ 2) _ _ fr_Z (36646206635154755680097439557 / 316912650057057350374175801344) (15873244077864222033 / 332306998946228968225951765070086144));
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact frs_S1_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact frs_S1_nonneg | exact fr_Z_nonneg]
      |exact frs_M1 | exact frs_E1].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.
Lemma frs_safe18 : hz_safe frs_S18 fr_Z.
Proof. exact I. Qed.
Lemma frs_safe17 : hz_safe frs_S17 fr_Z.
Proof.
  change (hz_safe frs_S17 fr_Z) with
    (hz_safe frs_S18 fr_Z /\
     (hz_M frs_S18 fr_Z + hz_E frs_S18 fr_Z) * fr_Z * 2 + / 696898287454081973172991196020261297061888 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe18|].
  assert (H1 := frs_M18). assert (H2 := frs_E18). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S18 fr_Z + hz_E frs_S18 fr_Z) * fr_Z * 2
          <= ((1 / 713623846352979940529142984724747568191373312) + 0) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe16 : hz_safe frs_S16 fr_Z.
Proof.
  change (hz_safe frs_S16 fr_Z) with
    (hz_safe frs_S17 fr_Z /\
     (hz_M frs_S17 fr_Z + hz_E frs_S17 fr_Z) * fr_Z * 2 + / 340282366920938463463374607431768211456 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe17|].
  assert (H1 := frs_M17). assert (H2 := frs_E17). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S17 fr_Z + hz_E frs_S17 fr_Z) * fr_Z * 2
          <= ((133 / 89202980794122492566142873090593446023921664) + (9943947977234055209 / 57896044618658097711785492504343953926634992332820282019728792003956564819968)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe15 : hz_safe frs_S15 fr_Z.
Proof.
  change (hz_safe frs_S15 fr_Z) with
    (hz_safe frs_S16 fr_Z /\
     (hz_M frs_S16 fr_Z + hz_E frs_S16 fr_Z) * fr_Z * 2 + / 332306998946228968225951765070086144 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe16|].
  assert (H1 := frs_M16). assert (H2 := frs_E16). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S16 fr_Z + hz_E frs_S16 fr_Z) * fr_Z * 2
          <= ((33433 / 11150372599265311570767859136324180752990208) + (9791951489810300993 / 28269553036454149273332760011886696253239742350009903329945699220681916416)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe14 : hz_safe frs_S14 fr_Z.
Proof.
  change (hz_safe frs_S14 fr_Z) with
    (hz_safe frs_S15 fr_Z /\
     (hz_M frs_S15 fr_Z + hz_E frs_S15 fr_Z) * fr_Z * 2 + / 324518553658426726783156020576256 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe15|].
  assert (H1 := frs_M15). assert (H2 := frs_E15). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S15 fr_Z + hz_E frs_S15 fr_Z) * fr_Z * 2
          <= ((4361469 / 1393796574908163946345982392040522594123776) + (10341069586954190977 / 27606985387162255149739023449108101809804435888681546220650096895197184)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe13 : hz_safe frs_S13 fr_Z.
Proof.
  change (hz_safe frs_S13 fr_Z) with
    (hz_safe frs_S14 fr_Z /\
     (hz_M frs_S14 fr_Z + hz_E frs_S14 fr_Z) * fr_Z * 2 + / 316912650057057350374175801344 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe14|].
  assert (H1 := frs_M14). assert (H2 := frs_E14). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S14 fr_Z + hz_E frs_S14 fr_Z) * fr_Z * 2
          <= ((558678257 / 174224571863520493293247799005065324265472) + (10376614736295886985 / 26959946667150639794667015087019630673637144422540572481103610249216)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe12 : hz_safe frs_S12 fr_Z.
Proof.
  change (hz_safe frs_S12 fr_Z) with
    (hz_safe frs_S13 fr_Z /\
     (hz_M frs_S13 fr_Z + hz_E frs_S13 fr_Z) * fr_Z * 2 + / 618970019642690137449562112 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe13|].
  assert (H1 := frs_M13). assert (H2 := frs_E13). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S13 fr_Z + hz_E frs_S13 fr_Z) * fr_Z * 2
          <= ((71512868021 / 21778071482940061661655974875633165533184) + (10378553813366734985 / 26328072917139296674479506920917608079723773850137277813577744384)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe11 : hz_safe frs_S11 fr_Z.
Proof.
  change (hz_safe frs_S11 fr_Z) with
    (hz_safe frs_S12 fr_Z /\
     (hz_M frs_S12 fr_Z + hz_E frs_S12 fr_Z) * fr_Z * 2 + / 1208925819614629174706176 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe12|].
  assert (H1 := frs_M12). assert (H2 := frs_E12). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S12 fr_Z + hz_E frs_S12 fr_Z) * fr_Z * 2
          <= ((4755610851209 / 2722258935367507707706996859454145691648) + (5766965047741907081 / 25711008708143844408671393477458601640355247900524685364822016)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe10 : hz_safe frs_S10 fr_Z.
Proof.
  change (hz_safe frs_S10 fr_Z) with
    (hz_safe frs_S11 fr_Z /\
     (hz_M frs_S11 fr_Z + hz_E frs_S11 fr_Z) * fr_Z * 2 + / 1180591620717411303424 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe11|].
  assert (H1 := frs_M11). assert (H2 := frs_E11). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S11 fr_Z + hz_E frs_S11 fr_Z) * fr_Z * 2
          <= ((305253030966701 / 340282366920938463463374607431768211456) + (2920694722322153549 / 25108406941546723055343157692830665664409421777856138051584)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe9 : hz_safe frs_S9 fr_Z.
Proof.
  change (hz_safe frs_S9 fr_Z) with
    (hz_safe frs_S10 fr_Z /\
     (hz_M frs_S10 fr_Z + hz_E frs_S10 fr_Z) * fr_Z * 2 + / 4611686018427387904 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe10|].
  assert (H1 := frs_M10). assert (H2 := frs_E10). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S10 fr_Z + hz_E frs_S10 fr_Z) * fr_Z * 2
          <= ((37555062173797473 / 42535295865117307932921825928971026432) + (10461178346492367005 / 98079714615416886934934209737619787751599303819750539264)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe8 : hz_safe frs_S8 fr_Z.
Proof.
  change (hz_safe frs_S8 fr_Z) with
    (hz_safe frs_S9 fr_Z /\
     (hz_M frs_S9 fr_Z + hz_E frs_S9 fr_Z) * fr_Z * 2 + / 9007199254740992 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe9|].
  assert (H1 := frs_M9). assert (H2 := frs_E9). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S9 fr_Z + hz_E frs_S9 fr_Z) * fr_Z * 2
          <= ((1340696815475834341 / 5316911983139663491615228241121378304) + (13862336127398006523 / 383123885216472214589586756787577295904684780545900544)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe7 : hz_safe frs_S7 fr_Z.
Proof.
  change (hz_safe frs_S7 fr_Z) with
    (hz_safe frs_S8 fr_Z /\
     (hz_M frs_S8 fr_Z + hz_E frs_S8 fr_Z) * fr_Z * 2 + / 35184372088832 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe8|].
  assert (H1 := frs_M8). assert (H2 := frs_E8). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S8 fr_Z + hz_E frs_S8 fr_Z) * fr_Z * 2
          <= ((80490460372217378169 / 664613997892457936451903530140172288) + (1497779758269067291 / 93536104789177786765035829293842113257979682750464)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe6 : hz_safe frs_S6 fr_Z.
Proof.
  change (hz_safe frs_S6 fr_Z) with
    (hz_safe frs_S7 fr_Z /\
     (hz_M frs_S7 fr_Z + hz_E frs_S7 fr_Z) * fr_Z * 2 + / 137438953472 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe7|].
  assert (H1 := frs_M7). assert (H2 := frs_E7). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S7 fr_Z + hz_E frs_S7 fr_Z) * fr_Z * 2
          <= ((2763635543295909497693 / 83076749736557242056487941267521536) + (14239755342980851847 / 2923003274661805836407369665432566039311865085952)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe5 : hz_safe frs_S5 fr_Z.
Proof.
  change (hz_safe frs_S5 fr_Z) with
    (hz_safe frs_S6 fr_Z /\
     (hz_M frs_S6 fr_Z + hz_E frs_S6 fr_Z) * fr_Z * 2 + / 536870912 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe6|].
  assert (H1 := frs_M6). assert (H2 := frs_E6). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S6 fr_Z + hz_E frs_S6 fr_Z) * fr_Z * 2
          <= ((89376041442393870907601 / 10384593717069655257060992658440192) + (7410956176628962057 / 5708990770823839524233143877797980545530986496)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe4 : hz_safe frs_S4 fr_Z.
Proof.
  change (hz_safe frs_S4 fr_Z) with
    (hz_safe frs_S5 fr_Z /\
     (hz_M frs_S5 fr_Z + hz_E frs_S5 fr_Z) * fr_Z * 2 + / 4194304 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe5|].
  assert (H1 := frs_M5). assert (H2 := frs_E5). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S5 fr_Z + hz_E frs_S5 fr_Z) * fr_Z * 2
          <= ((2864731846441227703950357 / 1298074214633706907132624082305024) + (7474360625539096479 / 22300745198530623141535718272648361505980416)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe3 : hz_safe frs_S3 fr_Z.
Proof.
  change (hz_safe frs_S3 fr_Z) with
    (hz_safe frs_S4 fr_Z /\
     (hz_M frs_S4 fr_Z + hz_E frs_S4 fr_Z) * fr_Z * 2 + / 65536 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe4|].
  assert (H1 := frs_M4). assert (H2 := frs_E4). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S4 fr_Z + hz_E frs_S4 fr_Z) * fr_Z * 2
          <= ((53009285459874272110349417 / 162259276829213363391578010288128) + (2590612548896480371 / 43556142965880123323311949751266331066368)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe2 : hz_safe frs_S2 fr_Z.
Proof.
  change (hz_safe frs_S2 fr_Z) with
    (hz_safe frs_S3 fr_Z /\
     (hz_M frs_S3 fr_Z + hz_E frs_S3 fr_Z) * fr_Z * 2 + / 1024 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe3|].
  assert (H1 := frs_M3). assert (H2 := frs_E3). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S3 fr_Z + hz_E frs_S3 fr_Z) * fr_Z * 2
          <= ((574531437120716429276528141 / 20282409603651670423947251286016) + (4746804116187825963 / 680564733841876926926749214863536422912)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe1 : hz_safe frs_S1 fr_Z.
Proof.
  change (hz_safe frs_S1 fr_Z) with
    (hz_safe frs_S2 fr_Z /\
     (hz_M frs_S2 fr_Z + hz_E frs_S2 fr_Z) * fr_Z * 2 + / 32 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe2|].
  assert (H1 := frs_M2). assert (H2 := frs_E2). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S2 fr_Z + hz_E frs_S2 fr_Z) * fr_Z * 2
          <= ((5348537264174342696180889153 / 2535301200456458802993406410752) + (6795044563308221659 / 10633823966279326983230456482242756608)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.
Lemma frs_safe0 : hz_safe frs_S0 fr_Z.
Proof.
  change (hz_safe frs_S0 fr_Z) with
    (hz_safe frs_S1 fr_Z /\
     (hz_M frs_S1 fr_Z + hz_E frs_S1 fr_Z) * fr_Z * 2 + / 2 + 1
       <= bpow radix2 1000).
  split; [exact frs_safe1|].
  assert (H1 := frs_M1). assert (H2 := frs_E1). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M frs_S1 fr_Z + hz_E frs_S1 fr_Z) * fr_Z * 2
          <= ((36646206635154755680097439557 / 316912650057057350374175801344) + (15873244077864222033 / 332306998946228968225951765070086144)) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.

Lemma frs_M_bound : hz_M frs_ms fr_Z <= (11818371352526584105 / 2305843009213693952).
Proof. unfold frs_ms. eapply Rle_trans; [exact frs_M0|]. lra. Qed.

Lemma frs_L_bound : hz_L frs_ms fr_Z <= (1258714001064507079 / 4611686018427387904).
Proof. unfold frs_ms. eapply Rle_trans; [exact frs_L0|]. lra. Qed.

Theorem frs_eval_err : forall z : binary64,
  fin z = true -> Rabs (B2R z) <= 40 ->
  fin (b64_horner frs_coeffs z) = true /\
  Rabs (B2R (b64_horner frs_coeffs z) - hz_horner_R (map B2R frs_coeffs) (B2R z))
    <= (7770866424388360789 / 2596148429267413814265248164610048).
Proof.
  intros z Fz Hz.
  destruct (b64_horner_err frs_coeffs frs_ms z fr_Z frs_coeffs_ok Fz Hz
              fr_Z_nonneg frs_safe0) as [F E].
  split; [exact F|]. eapply Rle_trans; [exact E|]. unfold frs_ms. exact frs_E0.
Qed.

Definition frs_exact : list R :=
  [/ 3; - / 42; / 1320; - / 75600; / 6894720; - / 918086400; / 168129561600; - / 40537905408000; / 12449059983360000; - / 4744158915944448000; / 2196910513383505920000; - / 1215044786727593902080000; / 791071712209880285184000000; - / 598887819773009368842240000000; / 521663957630642415318073344000000; - / 518038835213209137516710461440000000; / 581782280460396395199719024885760000000; - / 733653505613416290006332244964147200000000; / 1032281481841975878473698468618567680000000000].

Definition frs_delta : list R :=
  [B2R frs_c0 - (/ 3);
   B2R frs_c1 - (- / 42);
   B2R frs_c2 - (/ 1320);
   B2R frs_c3 - (- / 75600);
   B2R frs_c4 - (/ 6894720);
   B2R frs_c5 - (- / 918086400);
   B2R frs_c6 - (/ 168129561600);
   B2R frs_c7 - (- / 40537905408000);
   B2R frs_c8 - (/ 12449059983360000);
   B2R frs_c9 - (- / 4744158915944448000);
   B2R frs_c10 - (/ 2196910513383505920000);
   B2R frs_c11 - (- / 1215044786727593902080000);
   B2R frs_c12 - (/ 791071712209880285184000000);
   B2R frs_c13 - (- / 598887819773009368842240000000);
   B2R frs_c14 - (/ 521663957630642415318073344000000);
   B2R frs_c15 - (- / 518038835213209137516710461440000000);
   B2R frs_c16 - (/ 581782280460396395199719024885760000000);
   B2R frs_c17 - (- / 733653505613416290006332244964147200000000);
   B2R frs_c18 - (/ 1032281481841975878473698468618567680000000000)].

Lemma frs_delta_eq : forall x,
  hz_horner_R (map B2R frs_coeffs) x - hz_horner_R frs_exact x = hz_horner_R frs_delta x.
Proof. intro x. unfold frs_coeffs, frs_exact, frs_delta. cbn [map hz_horner_R]. ring. Qed.

Definition frs_ds : list R :=
  [/ 36028797018963968; / 576460752303423488; / 1180591620717411303424; / 1180591620717411303424; / 302231454903657293676544; / 19342813113834066795298816; / 2475880078570760549798248448; / 633825300114114700748351602688; / 162259276829213363391578010288128; / 83076749736557242056487941267521536; / 21267647932558653966460912964485513216; / 21778071482940061661655974875633165533184; / 22300745198530623141535718272648361505980416; / 5708990770823839524233143877797980545530986496; / 11692013098647223345629478661730264157247460343808; / 5986310706507378352962293074805895248510699696029696; / 12259964326927110866866776217202473468949912977468817408; / 100433627766186892221372630771322662657637687111424552206336; / 12855504354071922204335696738729300820177623950262342682411008].

Lemma frs_delta_ok : Forall2 (fun c m => Rabs c <= m) frs_delta frs_ds.
Proof.
  unfold frs_delta, frs_ds, frs_c0, frs_c1, frs_c2, frs_c3, frs_c4, frs_c5, frs_c6, frs_c7, frs_c8, frs_c9, frs_c10, frs_c11, frs_c12, frs_c13, frs_c14, frs_c15, frs_c16, frs_c17, frs_c18.
  repeat (apply Forall2_cons; [cbn [Binary.B2R]; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma frs_ds_M : hz_M frs_ds fr_Z <= (1749088281601660145 / 10384593717069655257060992658440192).
Proof. unfold frs_ds, fr_Z. cbn [hz_M]. lra. Qed.

Lemma frs_coef_err : forall x, Rabs x <= 40 ->
  Rabs (hz_horner_R (map B2R frs_coeffs) x - hz_horner_R frs_exact x) <= (1749088281601660145 / 10384593717069655257060992658440192).
Proof.
  intros x Hx. rewrite frs_delta_eq.
  eapply Rle_trans; [apply (hz_horner_R_bound_R _ frs_ds x fr_Z frs_delta_ok); unfold fr_Z; exact Hx|].
  exact frs_ds_M.
Qed.

Lemma frs_P_bound : forall y, Rabs y <= 40 ->
  Rabs (hz_horner_R (map B2R frs_coeffs) y) <= (11818371352526584105 / 2305843009213693952).
Proof.
  intros y Hy.
  eapply Rle_trans; [apply (hz_horner_R_bound frs_coeffs frs_ms y fr_Z frs_coeffs_ok);
                     unfold fr_Z; exact Hy|].
  exact frs_M_bound.
Qed.

Lemma frs_P_lip : forall y v, Rabs y <= 40 -> Rabs v <= 40 ->
  Rabs (hz_horner_R (map B2R frs_coeffs) y - hz_horner_R (map B2R frs_coeffs) v)
    <= (1258714001064507079 / 4611686018427387904) * Rabs (y - v).
Proof.
  intros y v Hy Hv.
  eapply Rle_trans;
    [apply (hz_horner_R_lip (map B2R frs_coeffs) frs_ms y v fr_Z frs_coeffs_ok_R);
     unfold fr_Z; assumption|].
  apply Rmult_le_compat_r; [apply Rabs_pos | exact frs_L_bound].
Qed.

(* The exact S polynomial is the S6 partial sum fz_S 18 at a = 1. *)
Lemma frs_fz_eq : forall x, fz_S 18 1 x = x * (x * x) * hz_horner_R frs_exact (x * x * (x * x)).
Proof.
  intro x. unfold fz_S, fz_Sterm. cbn [sum_f_R0 Nat.mul Nat.add].
  rewrite !pow1.
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (fr_INR_fact_S n) end.
  replace (INR (fact 0)) with 1 by reflexivity.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. unfold frs_exact. cbn [hz_horner_R].
  field.
Qed.

Print Assumptions frs_eval_err.
Print Assumptions frs_coef_err.
Print Assumptions frs_fz_eq.
