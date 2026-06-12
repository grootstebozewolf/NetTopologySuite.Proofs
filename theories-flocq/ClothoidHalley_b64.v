(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ClothoidHalley_b64
   ----------------------------------------------------------------------------
   Route (C) Scope A.4+: bit-exact second derivative assembly and the
   per-iterate Halley polynomial step on binary64.

   Companion: clothoid-halley-coq Clothoid_L.v / Solver.cs (EUPL-1.2).
   Problem order: (k0, k1, L); assembly uses d2, L, P, Q, Rm, T, S2c, S2s.

   Scope A.4  — f''(L) polynomial is integer-exact under clothoid_scalar_int_safe
                (|n| <= 2^12), mirroring ClothoidResidual_b64_exact.v.
   Scope A.5  — Halley denom / step use b64 round-chain (division rounds);
                soundness is conditional on explicit b64_safe overflow premises,
                not integer-exactness.
   Scope A.6  — l_update / fuel iteration skeleton mirroring theories/ClothoidHalley.v
                (convergence guard, denom guard, 0.5L floor, 1.5L fallback).
   Scope A.7  — degenerate straight-chord compose: Halley l_update is a no-op at L = d
                when the converged guard fires (route A + comparison bridge).

   No Admitted, no Axiom, no Parameter.
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.


From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.
From NTS.Proofs.Flocq Require Import InCircle_b64_exact.
From NTS.Proofs.Flocq Require Import ClothoidResidual_b64_exact.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import ClothoidDegenerate_b64.
From NTS.Proofs Require Import ClothoidHalley.
From NTS.Proofs Require Import ClothoidDegenerate.

Local Open Scope R_scope.

Local Notation b64_round := (round radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64)).

Definition clothoid_residual_second_prime_R (L P Q Rm T S2c S2s : R) : R :=
  2 * clothoid_r2_R P Q
  + 8 * L * (Q * Rm - P * T)
  + 2 * L * L * (Rm * Rm + T * T - (P * S2c + Q * S2s)).

Definition b64_clothoid_residual_second_prime
  (L P Q Rm T S2c S2s : binary64) : binary64 :=
  let r2 := b64_clothoid_r2 P Q in
  let term1 := b64_mult (b64Z 2) r2 in
  let qrpt := b64_minus (b64_mult Q Rm) (b64_mult P T) in
  let term2 := b64_mult (b64_mult (b64Z 8) L) qrpt in
  let rt_sq := b64_plus (b64_mult Rm Rm) (b64_mult T T) in
  let pq_s2 := b64_plus (b64_mult P S2c) (b64_mult Q S2s) in
  let inner := b64_minus rt_sq pq_s2 in
  let term3 := b64_mult (b64_mult (b64Z 2) (b64_mult L L)) inner in
  b64_plus (b64_plus term1 term2) term3.

Definition clothoid_halley_assembly_int_safe
  (L P Q Rm T S2c S2s : binary64) : Prop :=
  clothoid_scalar_int_safe L /\
  clothoid_scalar_int_safe P /\
  clothoid_scalar_int_safe Q /\
  clothoid_scalar_int_safe Rm /\
  clothoid_scalar_int_safe T /\
  clothoid_scalar_int_safe S2c /\
  clothoid_scalar_int_safe S2s.

Lemma clothoid_double_r2_bound_2p26 :
  forall nP nQ : Z,
    (Z.abs nP <= 2 ^ 12)%Z -> (Z.abs nQ <= 2 ^ 12)%Z ->
    (Z.abs (2 * (nP * nP + nQ * nQ)) <= 2 ^ 26)%Z.
Proof.
  intros nP nQ HP HQ.
  pose proof (arc_sum_sq_bound_2p25 (nP * nP) (nQ * nQ)
              (clothoid_sq_bound_2p24 nP HP)
              (clothoid_sq_bound_2p24 nQ HQ)) as Hsum.
  lia.
Qed.

Lemma clothoid_eight_L_qrpt_bound_2p40 :
  forall nL nqrpt : Z,
    (Z.abs nL <= 2 ^ 12)%Z -> (Z.abs nqrpt <= 2 ^ 25)%Z ->
    (Z.abs (8 * nL * nqrpt) <= 2 ^ 40)%Z.
Proof.
  intros nL nqrpt HL Hqrpt.
  rewrite Z.abs_mul.
  replace (8 * nL * nqrpt)%Z with (8 * (nL * nqrpt))%Z by ring.
  rewrite Z.abs_mul.
  assert (Hprod : (Z.abs (nL * nqrpt) <= 2 ^ 37)%Z).
  { rewrite Z.abs_mul.
    replace (2 ^ 37)%Z with (2 ^ 12 * 2 ^ 25)%Z by lia.
    apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption. }
  lia.
Qed.

Lemma clothoid_rt_sq_minus_ps2_bound_2p26 :
  forall nRm nT nP nQ nS2c nS2s : Z,
    (Z.abs nRm <= 2 ^ 12)%Z -> (Z.abs nT <= 2 ^ 12)%Z ->
    (Z.abs nP <= 2 ^ 12)%Z -> (Z.abs nQ <= 2 ^ 12)%Z ->
    (Z.abs nS2c <= 2 ^ 12)%Z -> (Z.abs nS2s <= 2 ^ 12)%Z ->
    (Z.abs (nRm * nRm + nT * nT - (nP * nS2c + nQ * nS2s)) <= 2 ^ 26)%Z.
Proof.
  intros nRm nT nP nQ nS2c nS2s HRm HT HP HQ HS2c HS2s.
  pose proof (clothoid_sq_bound_2p24 nRm HRm) as Hrm2.
  pose proof (clothoid_sq_bound_2p24 nT HT) as Ht2.
  pose proof (arc_sum_sq_bound_2p25 (nRm * nRm) (nT * nT) Hrm2 Ht2) as Hrt.
  pose proof (arc_product_bound_2p24 nP nS2c HP HS2c) as Hps2c.
  pose proof (arc_product_bound_2p24 nQ nS2s HQ HS2s) as Hqs2s.
  pose proof (arc_sum_sq_bound_2p25 (nP * nS2c) (nQ * nS2s) Hps2c Hqs2s) as Hpq.
  lia.
Qed.

Lemma clothoid_fpp_term3_bound_2p51 :
  forall nL ninner : Z,
    (Z.abs nL <= 2 ^ 12)%Z -> (Z.abs ninner <= 2 ^ 26)%Z ->
    (Z.abs (2 * (nL * nL) * ninner) <= 2 ^ 51)%Z.
Proof.
  intros nL ninner HL Hinner.
  pose proof (clothoid_sq_bound_2p24 nL HL) as Hll.
  assert (Hprod : (Z.abs ((nL * nL) * ninner) <= 2 ^ 50)%Z).
  { rewrite Z.abs_mul.
    replace (2 ^ 50)%Z with (2 ^ 24 * 2 ^ 26)%Z by lia.
    apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption. }
  replace (2 * (nL * nL) * ninner)%Z with (2 * ((nL * nL) * ninner))%Z by ring.
  rewrite Z.abs_mul.
  lia.
Qed.

Lemma clothoid_fpp_sum12_bound_2p41 :
  forall a b : Z,
    (Z.abs a <= 2 ^ 26)%Z -> (Z.abs b <= 2 ^ 40)%Z ->
    (Z.abs (a + b) <= 2 ^ 41)%Z.
Proof. intros a b Ha Hb. lia. Qed.

Lemma clothoid_fpp_sum_bound_2p52 :
  forall a b : Z,
    (Z.abs a <= 2 ^ 41)%Z -> (Z.abs b <= 2 ^ 51)%Z ->
    (Z.abs (a + b) <= 2 ^ 52)%Z.
Proof. intros a b Ha Hb. lia. Qed.

Lemma clothoid_IZR_sum_minus (a b c d : Z) :
  IZR a + IZR b - (IZR c + IZR d) = IZR (a + b - (c + d)).
Proof.
  rewrite <- plus_IZR.
  rewrite <- plus_IZR.
  rewrite <- minus_IZR.
  reflexivity.
Qed.

Lemma clothoid_residual_second_prime_R_IZR :
  forall nL nP nQ nRm nT nS2c nS2s : Z,
    clothoid_residual_second_prime_R (IZR nL) (IZR nP) (IZR nQ)
      (IZR nRm) (IZR nT) (IZR nS2c) (IZR nS2s)
    = IZR (2 * (nP * nP + nQ * nQ)
           + 8 * nL * (nQ * nRm - nP * nT)
           + 2 * nL * nL * (nRm * nRm + nT * nT - (nP * nS2c + nQ * nS2s))).
Proof.
  intros.
  unfold clothoid_residual_second_prime_R, clothoid_r2_R.
  replace (2 : R) with (IZR 2) by reflexivity.
  replace (8 : R) with (IZR 8) by reflexivity.
  repeat rewrite <- mult_IZR.
  rewrite <- plus_IZR.
  rewrite <- mult_IZR.
  repeat rewrite <- mult_IZR.
  rewrite <- minus_IZR.
  rewrite <- mult_IZR.
  rewrite clothoid_IZR_sum_minus.
  rewrite <- mult_IZR.
  rewrite <- plus_IZR.
  rewrite <- plus_IZR.
  reflexivity.
Qed.

Lemma b64Z_eight_R :
  Binary.B2R prec emax (b64Z 8) = 8
  /\ Binary.is_finite prec emax (b64Z 8) = true.
Proof. apply b64Z_R; lia. Qed.

Lemma clothoid_eight_bound_2p15 :
  forall n : Z, (Z.abs n <= 2 ^ 12)%Z -> (Z.abs (8 * n) <= 2 ^ 15)%Z.
Proof. intros n Hn. lia. Qed.

Lemma le_2p15_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 15)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 15); [lia | exact H]. Qed.

Lemma le_2p40_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 40)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 40); [lia | exact H]. Qed.

Lemma le_2p41_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 41)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 41); [lia | exact H]. Qed.

Theorem b64_clothoid_residual_second_prime_exact :
  forall L P Q Rm T S2c S2s : binary64,
    clothoid_halley_assembly_int_safe L P Q Rm T S2c S2s ->
    Binary.B2R prec emax (b64_clothoid_residual_second_prime L P Q Rm T S2c S2s)
      = clothoid_residual_second_prime_R (Binary.B2R prec emax L)
          (Binary.B2R prec emax P) (Binary.B2R prec emax Q)
          (Binary.B2R prec emax Rm) (Binary.B2R prec emax T)
          (Binary.B2R prec emax S2c) (Binary.B2R prec emax S2s)
    /\ Binary.is_finite prec emax
         (b64_clothoid_residual_second_prime L P Q Rm T S2c S2s) = true.
Proof.
  intros L P Q Rm T S2c S2s Hsafe.
  destruct Hsafe as (HL & HP & HQ & HRm & HT & HS2c & HS2s).
  pose proof (b64_clothoid_r2_exact P Q HP HQ) as [Hr2R Fr2].
  destruct HL as (FL & nL & HLR & HLb).
  destruct HP as (FP & nP & HPR & HPb).
  destruct HQ as (FQ & nQ & HQR & HQb).
  destruct HRm as (FRm & nRm & HRmR & HRmb).
  destruct HT as (FT & nT & HTR & HTb).
  destruct HS2c as (FS2c & nS2c & HS2cR & HS2cb).
  destruct HS2s as (FS2s & nS2s & HS2sR & HS2sb).
  unfold b64_clothoid_residual_second_prime.
  set (nr2 := (nP * nP + nQ * nQ)%Z).
  assert (Hnr2R : Binary.B2R prec emax (b64_clothoid_r2 P Q) = IZR nr2).
  { rewrite Hr2R, HPR, HQR. unfold clothoid_r2_R, nr2.
    rewrite plus_IZR, !mult_IZR. reflexivity. }
  assert (Hnr2b : (Z.abs nr2 <= 2 ^ 25)%Z).
  { subst nr2. apply arc_sum_sq_bound_2p25; apply clothoid_sq_bound_2p24; assumption. }
  destruct b64Z_two_R as [H2R F2].
  destruct b64Z_eight_R as [H8R F8].
  destruct (b64_mult_int_exact (b64Z 2) (b64_clothoid_r2 P Q) 2 nr2 F2 Fr2 H2R Hnr2R
              (le_2p26_le_2pprec _ (clothoid_double_r2_bound_2p26 nP nQ HPb HQb)))
    as [Ht1 Ft1].
  destruct (b64_mult_int_exact Q Rm nQ nRm FQ FRm HQR HRmR
              (le_2p24_le_2pprec _ (arc_product_bound_2p24 nQ nRm HQb HRmb)))
    as [HQRm FQRm].
  destruct (b64_mult_int_exact P T nP nT FP FT HPR HTR
              (le_2p24_le_2pprec _ (arc_product_bound_2p24 nP nT HPb HTb)))
    as [HPT FPT].
  set (nqrpt := (nQ * nRm - nP * nT)%Z).
  pose proof (arc_diff_bound_2p25 (nQ * nRm) (nP * nT)
              (arc_product_bound_2p24 nQ nRm HQb HRmb)
              (arc_product_bound_2p24 nP nT HPb HTb)) as Bqrpt.
  destruct (b64_minus_int_exact (b64_mult Q Rm) (b64_mult P T)
              (nQ * nRm) (nP * nT) FQRm FPT HQRm HPT
              (le_2p25_le_2pprec _ Bqrpt)) as [Hqrpt Fqrpt].
  destruct (b64_mult_int_exact (b64Z 8) L 8 nL F8 FL H8R HLR
              (le_2p15_le_2pprec (8 * nL)%Z (clothoid_eight_bound_2p15 nL HLb))) as [H8L F8L].
  destruct (b64_mult_int_exact (b64_mult (b64Z 8) L) (b64_minus (b64_mult Q Rm) (b64_mult P T))
              (8 * nL) nqrpt F8L Fqrpt H8L Hqrpt
              (le_2p40_le_2pprec _ (clothoid_eight_L_qrpt_bound_2p40 nL nqrpt HLb Bqrpt)))
    as [Ht2 Ft2].
  destruct (b64_mult_int_exact Rm Rm nRm nRm FRm FRm HRmR HRmR
              (le_2p24_le_2pprec _ (clothoid_sq_bound_2p24 nRm HRmb))) as [HRm2 FRm2].
  destruct (b64_mult_int_exact T T nT nT FT FT HTR HTR
              (le_2p24_le_2pprec _ (clothoid_sq_bound_2p24 nT HTb))) as [HT2 FT2].
  pose proof (arc_sum_sq_bound_2p25 (nRm * nRm) (nT * nT)
              (clothoid_sq_bound_2p24 nRm HRmb) (clothoid_sq_bound_2p24 nT HTb)) as Brt.
  destruct (b64_plus_int_exact (b64_mult Rm Rm) (b64_mult T T)
              (nRm * nRm) (nT * nT) FRm2 FT2 HRm2 HT2
              (le_2p25_le_2pprec _ Brt)) as [Hrt_sq Frt_sq].
  destruct (b64_mult_int_exact P S2c nP nS2c FP FS2c HPR HS2cR
              (le_2p24_le_2pprec _ (arc_product_bound_2p24 nP nS2c HPb HS2cb)))
    as [HPS2c FPS2c].
  destruct (b64_mult_int_exact Q S2s nQ nS2s FQ FS2s HQR HS2sR
              (le_2p24_le_2pprec _ (arc_product_bound_2p24 nQ nS2s HQb HS2sb)))
    as [HQS2s FQS2s].
  pose proof (arc_sum_sq_bound_2p25 (nP * nS2c) (nQ * nS2s)
              (arc_product_bound_2p24 nP nS2c HPb HS2cb)
              (arc_product_bound_2p24 nQ nS2s HQb HS2sb)) as Bpq.
  destruct (b64_plus_int_exact (b64_mult P S2c) (b64_mult Q S2s)
              (nP * nS2c) (nQ * nS2s) FPS2c FQS2s HPS2c HQS2s
              (le_2p25_le_2pprec _ Bpq)) as [Hpq_s2 Fpq_s2].
  set (ninner := (nRm * nRm + nT * nT - (nP * nS2c + nQ * nS2s))%Z).
  pose proof (clothoid_rt_sq_minus_ps2_bound_2p26 nRm nT nP nQ nS2c nS2s
              HRmb HTb HPb HQb HS2cb HS2sb) as Binner.
  destruct (b64_minus_int_exact (b64_plus (b64_mult Rm Rm) (b64_mult T T))
              (b64_plus (b64_mult P S2c) (b64_mult Q S2s))
              (nRm * nRm + nT * nT) (nP * nS2c + nQ * nS2s) Frt_sq Fpq_s2 Hrt_sq Hpq_s2
              (le_2p26_le_2pprec _ Binner)) as [Hinner Finner].
  destruct (b64_mult_int_exact L L nL nL FL FL HLR HLR
              (le_2p24_le_2pprec _ (clothoid_sq_bound_2p24 nL HLb))) as [HLL FLL].
  destruct (b64_mult_int_exact (b64Z 2) (b64_mult L L) 2 (nL * nL) F2 FLL H2R HLL
              (le_2p25_le_2pprec _ (clothoid_double_sq_bound_2p25 nL HLb))) as [H2LL F2LL].
  pose proof (clothoid_fpp_term3_bound_2p51 nL ninner HLb Binner) as Bt3.
  destruct (b64_mult_int_exact (b64_mult (b64Z 2) (b64_mult L L))
              (b64_minus (b64_plus (b64_mult Rm Rm) (b64_mult T T))
                        (b64_plus (b64_mult P S2c) (b64_mult Q S2s)))
              (2 * (nL * nL)) ninner F2LL Finner H2LL Hinner
              (le_2p51_le_2pprec _ Bt3)) as [Ht3 Ft3].
  pose proof (clothoid_fpp_sum12_bound_2p41 (2 * nr2) (8 * nL * nqrpt)
              (clothoid_double_r2_bound_2p26 nP nQ HPb HQb)
              (clothoid_eight_L_qrpt_bound_2p40 nL nqrpt HLb Bqrpt)) as Bsum12.
  destruct (b64_plus_int_exact (b64_mult (b64Z 2) (b64_clothoid_r2 P Q))
              (b64_mult (b64_mult (b64Z 8) L)
                        (b64_minus (b64_mult Q Rm) (b64_mult P T)))
              (2 * nr2) (8 * nL * nqrpt) Ft1 Ft2 Ht1 Ht2
              (le_2p41_le_2pprec _ Bsum12)) as [Hsum12 Fsum12].
  pose proof (clothoid_fpp_sum_bound_2p52 (2 * nr2 + 8 * nL * nqrpt)
              (2 * (nL * nL) * ninner) Bsum12 Bt3) as Bsum.
  destruct (b64_plus_int_exact (b64_plus (b64_mult (b64Z 2) (b64_clothoid_r2 P Q))
                                         (b64_mult (b64_mult (b64Z 8) L)
                                                   (b64_minus (b64_mult Q Rm) (b64_mult P T))))
              (b64_mult (b64_mult (b64Z 2) (b64_mult L L))
                        (b64_minus (b64_plus (b64_mult Rm Rm) (b64_mult T T))
                                   (b64_plus (b64_mult P S2c) (b64_mult Q S2s))))
              (2 * nr2 + 8 * nL * nqrpt) (2 * (nL * nL) * ninner) Fsum12 Ft3 Hsum12 Ht3
              (le_2p52_le_2pprec _ Bsum)) as [Hfpp Ffpp].
  split; [ | exact Ffpp ].
  rewrite Hfpp, HLR, HPR, HQR, HRmR, HTR, HS2cR, HS2sR,
          clothoid_residual_second_prime_R_IZR.
  unfold nr2, nqrpt, ninner. f_equal. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Halley polynomial step — round-chain (Scope A.5).                          *)
(* -------------------------------------------------------------------------- *)

Definition b64_clothoid_halley_denom (f fp fpp : binary64) : binary64 :=
  b64_minus (b64_mult (b64_mult (b64Z 2) fp) fp) (b64_mult f fpp).

Definition b64_clothoid_halley_step_num (f fp : binary64) : binary64 :=
  b64_mult (b64_mult (b64Z 2) f) fp.

Definition b64_clothoid_halley_step (f fp fpp : binary64) : binary64 :=
  b64_div (b64_clothoid_halley_step_num f fp) (b64_clothoid_halley_denom f fp fpp).

Definition clothoid_halley_denom_R (f fp fpp : R) : R :=
  2 * fp * fp - f * fpp.

Definition clothoid_halley_step_R (f fp fpp : R) : R :=
  2 * f * fp / clothoid_halley_denom_R f fp fpp.

Theorem b64_clothoid_halley_denom_round :
  forall f fp fpp,
    b64_safe Rmult (b64Z 2) fp ->
    b64_safe Rmult (b64_mult (b64Z 2) fp) fp ->
    b64_safe Rmult f fpp ->
    b64_safe Rminus (b64_mult (b64_mult (b64Z 2) fp) fp) (b64_mult f fpp) ->
    Binary.B2R prec emax (b64_clothoid_halley_denom f fp fpp)
      = b64_round (Binary.B2R prec emax (b64_mult (b64_mult (b64Z 2) fp) fp)
                     - Binary.B2R prec emax (b64_mult f fpp))
    /\ Binary.is_finite prec emax (b64_clothoid_halley_denom f fp fpp) = true.
Proof.
  intros f fp fpp H2fp Hfp2 Hffpp Hden.
  destruct (b64_mult_correct (b64Z 2) fp H2fp) as [H2fpR F2fp].
  destruct (b64_mult_correct (b64_mult (b64Z 2) fp) fp Hfp2) as [Hfp2R Ffp2].
  destruct (b64_mult_correct f fpp Hffpp) as [HffppR Fffpp].
  destruct (b64_minus_correct (b64_mult (b64_mult (b64Z 2) fp) fp) (b64_mult f fpp) Hden)
    as [HdenR Fden].
  split; [exact HdenR | exact Fden].
Qed.

Theorem b64_clothoid_halley_step_round :
  forall f fp fpp,
    b64_safe Rmult (b64Z 2) f ->
    b64_safe Rmult (b64_mult (b64Z 2) f) fp ->
    b64_safe Rmult (b64Z 2) fp ->
    b64_safe Rmult (b64_mult (b64Z 2) fp) fp ->
    b64_safe Rmult f fpp ->
    b64_safe Rminus (b64_mult (b64_mult (b64Z 2) fp) fp) (b64_mult f fpp) ->
    Binary.B2R prec emax (b64_clothoid_halley_denom f fp fpp) <> 0 ->
    Rabs (b64_round (Binary.B2R prec emax (b64_clothoid_halley_step_num f fp)
                        / Binary.B2R prec emax (b64_clothoid_halley_denom f fp fpp)))
           < bpow radix2 emax ->
    Binary.B2R prec emax (b64_clothoid_halley_step f fp fpp)
      = b64_round (Binary.B2R prec emax (b64_clothoid_halley_step_num f fp)
                     / Binary.B2R prec emax (b64_clothoid_halley_denom f fp fpp))
    /\ Binary.is_finite prec emax (b64_clothoid_halley_step f fp fpp) = true.
Proof.
  intros f fp fpp H2f H2ffp H2fp Hfp2 Hffpp Hden Hden_nz Hbnd.
  destruct (b64_mult_correct (b64Z 2) f H2f) as [H2fR F2f].
  destruct (b64_mult_correct (b64_mult (b64Z 2) f) fp H2ffp) as [HnumR Fnum].
  destruct (b64_clothoid_halley_denom_round f fp fpp H2fp Hfp2 Hffpp Hden) as [HdenR Fden].
  destruct (b64_div_correct (b64_clothoid_halley_step_num f fp)
              (b64_clothoid_halley_denom f fp fpp) Fnum Fden Hden_nz Hbnd)
    as [HstepR Fstep].
  split; [exact HstepR | exact Fstep].
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope A.6 — l_update / fuel (Solver.cs safety guards).                     *)
(* -------------------------------------------------------------------------- *)

Definition b64_zero : binary64 := b64Z 0.

Definition b64_max (x y : binary64) : binary64 :=
  if b64_le x y then y else x.

Definition b64_clothoid_tol_scale (d2 : binary64) : binary64 :=
  b64_max d2 b64_one.

Definition b64_clothoid_converged_bool (f d2 tol : binary64) : bool :=
  b64_lt (b64_abs f) (b64_mult tol (b64_clothoid_tol_scale d2)).

Definition b64_clothoid_halley_denom_guard_bool (denom fp : binary64) : bool :=
  if b64_lt b64_zero fp then
    if b64_lt b64_zero (b64_abs denom) then true else false
  else false.

Definition b64_clothoid_halley_l_fallback (L : binary64) : binary64 :=
  b64_plus L (b64_mult b64_half L).

Definition b64_clothoid_halley_l_new (L f fp fpp : binary64) : binary64 :=
  let step := b64_clothoid_halley_step f fp fpp in
  let raw := b64_minus L step in
  if b64_le raw b64_zero then b64_mult b64_half L else raw.

Record b64_clothoid_moments : Type := MkB64ClothoidMoments {
  bcmP : binary64;
  bcmQ : binary64;
  bcmR : binary64;
  bcmT : binary64;
  bcmS2c : binary64;
  bcmS2s : binary64
}.

Definition b64_clothoid_eval_moments (mom : binary64 -> b64_clothoid_moments)
  (L : binary64) : b64_clothoid_moments :=
  mom L.

Definition b64_clothoid_residual_at (d2 : binary64)
  (mom : binary64 -> b64_clothoid_moments) (L : binary64) : binary64 :=
  let m := b64_clothoid_eval_moments mom L in
  b64_clothoid_residual d2 L (bcmP m) (bcmQ m).

Definition b64_clothoid_fp_at (mom : binary64 -> b64_clothoid_moments)
  (L : binary64) : binary64 :=
  let m := b64_clothoid_eval_moments mom L in
  b64_clothoid_residual_prime L (bcmP m) (bcmQ m) (bcmR m) (bcmT m).

Definition b64_clothoid_fpp_at (mom : binary64 -> b64_clothoid_moments)
  (L : binary64) : binary64 :=
  let m := b64_clothoid_eval_moments mom L in
  b64_clothoid_residual_second_prime L (bcmP m) (bcmQ m) (bcmR m) (bcmT m)
    (bcmS2c m) (bcmS2s m).

Definition b64_clothoid_halley_l_update (d2 tol : binary64)
  (mom : binary64 -> b64_clothoid_moments) (L : binary64) : binary64 :=
  let f := b64_clothoid_residual_at d2 mom L in
  let fp := b64_clothoid_fp_at mom L in
  let fpp := b64_clothoid_fpp_at mom L in
  let denom := b64_clothoid_halley_denom f fp fpp in
  if b64_clothoid_converged_bool f d2 tol then L
  else if b64_clothoid_halley_denom_guard_bool denom fp then
         b64_clothoid_halley_l_new L f fp fpp
       else b64_clothoid_halley_l_fallback L.

Fixpoint b64_clothoid_halley_fuel (fuel : nat) (L d2 tol : binary64)
  (mom : binary64 -> b64_clothoid_moments) : binary64 :=
  match fuel with
  | O => L
  | S fuel' =>
      b64_clothoid_halley_fuel fuel'
        (b64_clothoid_halley_l_update d2 tol mom L) d2 tol mom
  end.

Definition b64_clothoid_halley_fuel_iters (fuel : nat) : nat := fuel.

Lemma b64_clothoid_halley_l_update_converged :
  forall d2 tol (mom : binary64 -> b64_clothoid_moments) L,
    b64_clothoid_converged_bool (b64_clothoid_residual_at d2 mom L) d2 tol = true ->
    b64_clothoid_halley_l_update d2 tol mom L = L.
Proof.
  intros d2 tol mom L Hconv.
  unfold b64_clothoid_halley_l_update.
  rewrite Hconv. reflexivity.
Qed.

Lemma b64_clothoid_halley_fuel_zero :
  forall L d2 tol (mom : binary64 -> b64_clothoid_moments),
    b64_clothoid_halley_fuel O L d2 tol mom = L.
Proof. reflexivity. Qed.

Lemma b64_clothoid_halley_fuel_succ :
  forall fuel L d2 tol (mom : binary64 -> b64_clothoid_moments),
    b64_clothoid_halley_fuel (S fuel) L d2 tol mom =
    b64_clothoid_halley_fuel fuel
      (b64_clothoid_halley_l_update d2 tol mom L) d2 tol mom.
Proof. reflexivity. Qed.

Lemma b64_max_B2R :
  forall x y,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax (b64_max x y)
      = Rmax (Binary.B2R prec emax x) (Binary.B2R prec emax y).
Proof.
  intros x y Fx Fy.
  unfold b64_max.
  destruct (b64_le x y) eqn:E.
  - symmetry. apply Rmax_right. apply b64_le_R_of_true; assumption.
  - symmetry. apply Rmax_left.
    destruct (Rle_lt_dec (Binary.B2R prec emax x) (Binary.B2R prec emax y))
      as [Hle | Hlt].
    + apply b64_le_complete in Hle; [ congruence | assumption | assumption ].
    + lra.
Qed.

Lemma b64_abs_finite :
  forall x,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax (b64_abs x) = true.
Proof.
  intros x Fx.
  unfold b64_abs.
  pose proof (@Binary.is_finite_Babs prec emax default_abs_nan_b64 x) as Hfin.
  rewrite Hfin. exact Fx.
Qed.

Lemma b64_clothoid_tol_scale_B2R :
  forall d2,
    Binary.is_finite prec emax d2 = true ->
    Binary.B2R prec emax (b64_clothoid_tol_scale d2)
      = clothoid_tol_scale (Binary.B2R prec emax d2).
Proof.
  intros d2 Fd2.
  unfold b64_clothoid_tol_scale, clothoid_tol_scale.
  destruct B2R_and_finite_b64_one as [H1R F1].
  rewrite (b64_max_B2R d2 b64_one Fd2 F1).
  rewrite H1R. reflexivity.
Qed.

Lemma b64_clothoid_converged_bool_true_of_R :
  forall f d2 tol,
    Binary.is_finite prec emax f = true ->
    Binary.is_finite prec emax d2 = true ->
    Binary.is_finite prec emax tol = true ->
    Binary.is_finite prec emax (b64_mult tol (b64_clothoid_tol_scale d2)) = true ->
    Binary.B2R prec emax (b64_abs f)
      < Binary.B2R prec emax (b64_mult tol (b64_clothoid_tol_scale d2)) ->
    b64_clothoid_converged_bool f d2 tol = true.
Proof.
  intros f d2 tol Ff Fd2 Ftol Fthr Hlt.
  unfold b64_clothoid_converged_bool.
  pose proof (b64_abs_finite f Ff) as Fabs.
  apply b64_lt_complete; [exact Fabs | exact Fthr | exact Hlt].
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope A.7 — degenerate compose (route A + comparison bridge).              *)
(* -------------------------------------------------------------------------- *)

Definition b64_degenerate_moments (_ : binary64) : b64_clothoid_moments :=
  MkB64ClothoidMoments (b64Z 1) (b64Z 0) (b64Z 0) (b64Z 0) (b64Z 0) (b64Z 0).

Lemma b64_degenerate_residual_at_chord_B2R :
  forall d L,
    coord_int_safe d ->
    coord_int_safe L ->
    Binary.B2R prec emax (b64_clothoid_residual_at (b64_mult d d)
      b64_degenerate_moments L)
      = Binary.B2R prec emax (b64_degenerate_residual d L).
Proof.
  intros d L Hd HL.
  destruct (b64_degenerate_residual_exact d L Hd HL) as [Hexact _].
  destruct Hd as (Fd & a & HdR & Ha).
  destruct HL as (FL & b & HLR & Hb).
  unfold b64_clothoid_residual_at, b64_degenerate_moments, b64_clothoid_eval_moments.
  simpl.
  unfold b64_clothoid_residual.
  rewrite b64_clothoid_r2_one_zero.
  destruct (b64_mult_int_exact L L b b FL FL HLR HLR
              (square_int_window b Hb)) as [HLL FLL].
  destruct (b64Z_R 1 ltac:(lia)) as [H1R F1].
  assert (Hbb1 : (Z.abs (b * b * 1) <= 2 ^ prec)%Z).
  { replace (b * b * 1)%Z with (b * b)%Z by ring. apply square_int_window; assumption. }
  destruct (b64_mult_int_exact (b64_mult L L) (b64Z 1) (b * b) 1 FLL F1 HLL H1R
              Hbb1) as [HL1 FLL1].
  assert (HL1bb : Binary.B2R prec emax (b64_mult (b64_mult L L) (b64Z 1)) = IZR (b * b)).
  { rewrite HL1. f_equal. ring. }
  destruct (b64_mult_int_exact d d a a Fd Fd HdR HdR
              (square_int_window a Ha)) as [Hd2R Fd2].
  destruct (b64_minus_int_exact (b64_mult (b64_mult L L) (b64Z 1)) (b64_mult d d)
              (b * b) (a * a) FLL1 Fd2 HL1bb Hd2R
              (square_diff_int_window a b Ha Hb)) as [Hres _].
  rewrite Hres, Hexact, HdR, HLR.
  unfold degenerate_residual.
  rewrite minus_IZR. f_equal; rewrite mult_IZR; reflexivity.
Qed.

Lemma b64_degenerate_residual_at_chord_finite :
  forall d L,
    coord_int_safe d ->
    coord_int_safe L ->
    Binary.is_finite prec emax
      (b64_clothoid_residual_at (b64_mult d d) b64_degenerate_moments L) = true.
Proof.
  intros d L Hd HL.
  destruct Hd as (Fd & a & HdR & Ha).
  destruct HL as (FL & b & HLR & Hb).
  unfold b64_clothoid_residual_at, b64_degenerate_moments, b64_clothoid_eval_moments.
  simpl.
  unfold b64_clothoid_residual.
  rewrite b64_clothoid_r2_one_zero.
  destruct (b64_mult_int_exact L L b b FL FL HLR HLR
              (square_int_window b Hb)) as [HLL FLL].
  destruct (b64Z_R 1 ltac:(lia)) as [H1R F1].
  assert (Hbb1 : (Z.abs (b * b * 1) <= 2 ^ prec)%Z).
  { replace (b * b * 1)%Z with (b * b)%Z by ring. apply square_int_window; assumption. }
  destruct (b64_mult_int_exact (b64_mult L L) (b64Z 1) (b * b) 1 FLL F1 HLL H1R
              Hbb1) as [HL1 FLL1].
  assert (HL1bb : Binary.B2R prec emax (b64_mult (b64_mult L L) (b64Z 1)) = IZR (b * b)).
  { rewrite HL1. f_equal. ring. }
  destruct (b64_mult_int_exact d d a a Fd Fd HdR HdR
              (square_int_window a Ha)) as [Hd2R Fd2].
  destruct (b64_minus_int_exact (b64_mult (b64_mult L L) (b64Z 1)) (b64_mult d d)
              (b * b) (a * a) FLL1 Fd2 HL1bb Hd2R
              (square_diff_int_window a b Ha Hb)) as [_ Fres].
  exact Fres.
Qed.

Lemma b64_abs_B2R_zero :
  forall x,
    Binary.is_finite prec emax x = true ->
    Binary.B2R prec emax x = 0 ->
    Binary.B2R prec emax (b64_abs x) = 0.
Proof.
  intros x Fx HxR.
  unfold b64_abs.
  pose proof (@Binary.B2R_Babs prec emax default_abs_nan_b64 x) as Habs.
  rewrite Habs, HxR, Rabs_R0. reflexivity.
Qed.

Lemma b64_clothoid_converged_bool_true_of_zero_residual :
  forall f d2 tol,
    Binary.is_finite prec emax f = true ->
    Binary.is_finite prec emax (b64_mult tol (b64_clothoid_tol_scale d2)) = true ->
    Binary.B2R prec emax f = 0 ->
    0 < Binary.B2R prec emax (b64_mult tol (b64_clothoid_tol_scale d2)) ->
    b64_clothoid_converged_bool f d2 tol = true.
Proof.
  intros f d2 tol Ff Fthr Hf0 Hthr.
  unfold b64_clothoid_converged_bool.
  pose proof (b64_abs_finite f Ff) as Fabs.
  apply b64_lt_complete; [exact Fabs | exact Fthr |].
  rewrite (b64_abs_B2R_zero f Ff Hf0). lra.
Qed.

Lemma b64_degenerate_residual_zero_at_chord :
  forall d,
    coord_int_safe d ->
    0 < Binary.B2R prec emax d ->
    Binary.B2R prec emax
      (b64_clothoid_residual_at (b64_mult d d) b64_degenerate_moments d) = 0.
Proof.
  intros d Hd Hdpos.
  rewrite b64_degenerate_residual_at_chord_B2R; [ | exact Hd | exact Hd ].
  destruct (b64_degenerate_root_exact d d Hd Hd Hdpos Hdpos) as [_ Hroot].
  apply Hroot. reflexivity.
Qed.

Theorem b64_degenerate_halley_fixed_at_root :
  forall d tol,
    coord_int_safe d ->
    clothoid_scalar_int_safe tol ->
    0 < Binary.B2R prec emax d ->
    0 < Binary.B2R prec emax tol ->
    Binary.is_finite prec emax
      (b64_mult tol (b64_clothoid_tol_scale (b64_mult d d))) = true ->
    0 < Binary.B2R prec emax
      (b64_mult tol (b64_clothoid_tol_scale (b64_mult d d))) ->
    b64_clothoid_halley_l_update (b64_mult d d) tol b64_degenerate_moments d = d.
Proof.
  intros d tol Hd Htol Hdpos Htolpos Fthr Hthrpos.
  set (d2 := b64_mult d d).
  set (f := b64_clothoid_residual_at d2 b64_degenerate_moments d).
  assert (Hf0 : Binary.B2R prec emax f = 0).
  { subst f d2. apply b64_degenerate_residual_zero_at_chord; assumption. }
  assert (Ff : Binary.is_finite prec emax f = true).
  { subst f d2. apply b64_degenerate_residual_at_chord_finite; assumption. }
  assert (Hcb : b64_clothoid_converged_bool f d2 tol = true).
  {
    apply b64_clothoid_converged_bool_true_of_zero_residual with (f := f) (d2 := d2);
      assumption.
  }
  assert (Hcb' : b64_clothoid_converged_bool
      (b64_clothoid_residual_at d2 b64_degenerate_moments d) d2 tol = true).
  { subst f. exact Hcb. }
  apply b64_clothoid_halley_l_update_converged. exact Hcb'.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conditional <=4-iteration interface (corpus witness, b64 fuel model).      *)
(* -------------------------------------------------------------------------- *)

Section ClothoidHalleyB64CorpusBound.

Variable Problem : Type.
Variable iterations_used : Problem -> nat.

Hypothesis H_iterations_le_max :
  forall p : Problem,
    (iterations_used p <= clothoid_halley_max_iter_default)%nat.

Hypothesis H_filtered_corpus_le_four :
  forall p : Problem,
    (iterations_used p <= clothoid_halley_corpus_iter_bound)%nat.

(* Fuel wiring: an extracted solver should witness
   `iterations_used p = b64_clothoid_halley_fuel_iters fuel` for the fuel
   consumed by `b64_clothoid_halley_fuel fuel ...`. *)

Theorem b64_clothoid_halley_filtered_corpus_le_four :
  forall p : Problem,
    (iterations_used p <= clothoid_halley_corpus_iter_bound)%nat.
Proof. intro p. apply H_filtered_corpus_le_four. Qed.

Theorem b64_clothoid_halley_filtered_corpus_le_max :
  forall p : Problem,
    (iterations_used p <= clothoid_halley_max_iter_default)%nat.
Proof. intro p. apply H_iterations_le_max. Qed.

End ClothoidHalleyB64CorpusBound.

Print Assumptions b64_clothoid_residual_second_prime_exact.
Print Assumptions b64_clothoid_halley_denom_round.
Print Assumptions b64_clothoid_halley_step_round.
Print Assumptions b64_degenerate_halley_fixed_at_root.
Print Assumptions b64_clothoid_halley_filtered_corpus_le_four.