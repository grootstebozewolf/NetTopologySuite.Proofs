(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ClothoidResidual_b64_exact
   ----------------------------------------------------------------------------
   Route (C) Scope A: bit-exact polynomial assembly for the clothoid
   chord-length residual and its first derivative.

   Companion: clothoid-halley-coq Clothoid_L.v / Solver.cs (EUPL-1.2).
   Problem order: (k0, k1, L) in oracle vectors; assembly uses d2, L, P, Q, Rm, T.

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

Local Open Scope R_scope.

Definition clothoid_d2_R (P0 P1 : BPoint) : R :=
  (Binary.B2R prec emax (bx P0) - Binary.B2R prec emax (bx P1)) *
  (Binary.B2R prec emax (bx P0) - Binary.B2R prec emax (bx P1)) +
  (Binary.B2R prec emax (by_ P0) - Binary.B2R prec emax (by_ P1)) *
  (Binary.B2R prec emax (by_ P0) - Binary.B2R prec emax (by_ P1)).

Definition clothoid_r2_R (P Q : R) : R := P * P + Q * Q.

Definition clothoid_residual_R (d2 L P Q : R) : R :=
  L * L * clothoid_r2_R P Q - d2.

Definition clothoid_residual_prime_R (L P Q Rm T : R) : R :=
  2 * L * clothoid_r2_R P Q + 2 * L * L * (Q * Rm - P * T).

Definition b64_clothoid_d2 (P0 P1 : BPoint) : binary64 := b64_dist_sq P0 P1.

Definition b64_clothoid_r2 (P Q : binary64) : binary64 :=
  b64_plus (b64_mult P P) (b64_mult Q Q).

Definition b64_clothoid_residual (d2 L P Q : binary64) : binary64 :=
  b64_minus (b64_mult (b64_mult L L) (b64_clothoid_r2 P Q)) d2.

Definition b64_clothoid_residual_prime (L P Q Rm T : binary64) : binary64 :=
  let r2 := b64_clothoid_r2 P Q in
  let term1 := b64_mult (b64_mult (b64Z 2) L) r2 in
  let qrpt := b64_minus (b64_mult Q Rm) (b64_mult P T) in
  let term2 := b64_mult (b64_mult (b64Z 2) (b64_mult L L)) qrpt in
  b64_plus term1 term2.

Definition clothoid_scalar_int_safe (x : binary64) : Prop :=
  Binary.is_finite prec emax x = true /\
  exists n : Z,
    Binary.B2R prec emax x = IZR n /\ (Z.abs n <= 2 ^ 12)%Z.

Definition clothoid_chord_inputs_int_safe (P0 P1 : BPoint) : Prop :=
  arc_coord_int_safe (bx P0) /\ arc_coord_int_safe (by_ P0) /\
  arc_coord_int_safe (bx P1) /\ arc_coord_int_safe (by_ P1).

Definition clothoid_residual_assembly_int_safe
  (d2 L P Q Rm T : binary64) : Prop :=
  clothoid_scalar_int_safe d2 /\
  clothoid_scalar_int_safe L /\
  clothoid_scalar_int_safe P /\
  clothoid_scalar_int_safe Q /\
  clothoid_scalar_int_safe Rm /\
  clothoid_scalar_int_safe T.

Lemma clothoid_sq_bound_2p24 :
  forall n : Z, (Z.abs n <= 2 ^ 12)%Z -> (Z.abs (n * n) <= 2 ^ 24)%Z.
Proof. intros n Hn. apply arc_sq_bound_2p24. exact Hn. Qed.

Lemma clothoid_double_bound_2p13 :
  forall n : Z, (Z.abs n <= 2 ^ 12)%Z -> (Z.abs (2 * n) <= 2 ^ 13)%Z.
Proof. intros n Hn. lia. Qed.

Lemma clothoid_double_sq_bound_2p25 :
  forall n : Z, (Z.abs n <= 2 ^ 12)%Z -> (Z.abs (2 * (n * n)) <= 2 ^ 25)%Z.
Proof.
  intros n Hn.
  pose proof (clothoid_sq_bound_2p24 n Hn) as Hsq.
  lia.
Qed.

Lemma clothoid_product_bound_2p38 :
  forall a b : Z,
    (Z.abs a <= 2 ^ 13)%Z -> (Z.abs b <= 2 ^ 25)%Z ->
    (Z.abs (a * b) <= 2 ^ 38)%Z.
Proof.
  intros a b Ha Hb.
  rewrite Z.abs_mul.
  replace (2 ^ 38)%Z with (2 ^ 13 * 2 ^ 25)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma clothoid_product_bound_2p49 :
  forall a b : Z,
    (Z.abs a <= 2 ^ 24)%Z -> (Z.abs b <= 2 ^ 25)%Z ->
    (Z.abs (a * b) <= 2 ^ 49)%Z.
Proof.
  intros a b Ha Hb.
  rewrite Z.abs_mul.
  replace (2 ^ 49)%Z with (2 ^ 24 * 2 ^ 25)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma clothoid_residual_diff_bound_2p50 :
  forall a b : Z,
    (Z.abs a <= 2 ^ 49)%Z -> (Z.abs b <= 2 ^ 25)%Z ->
    (Z.abs (a - b) <= 2 ^ 50)%Z.
Proof. intros a b Ha Hb. lia. Qed.

Lemma clothoid_residual_diff_bound_2p50_scalar :
  forall a b : Z,
    (Z.abs a <= 2 ^ 49)%Z -> (Z.abs b <= 2 ^ 12)%Z ->
    (Z.abs (a - b) <= 2 ^ 50)%Z.
Proof. intros a b Ha Hb. lia. Qed.

Lemma clothoid_prime_sum_bound_2p51 :
  forall a b : Z,
    (Z.abs a <= 2 ^ 38)%Z -> (Z.abs b <= 2 ^ 50)%Z ->
    (Z.abs (a + b) <= 2 ^ 51)%Z.
Proof. intros a b Ha Hb. lia. Qed.

Lemma le_2p49_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 49)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 49); [lia | exact H]. Qed.

Lemma le_2p13_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 13)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 13); [lia | exact H]. Qed.

Lemma clothoid_residual_prime_R_IZR :
  forall nL nP nQ nRm nT : Z,
    clothoid_residual_prime_R (IZR nL) (IZR nP) (IZR nQ) (IZR nRm) (IZR nT)
    = IZR (2 * nL * (nP * nP + nQ * nQ)
           + 2 * nL * nL * (nQ * nRm - nP * nT)).
Proof.
  intros.
  unfold clothoid_residual_prime_R, clothoid_r2_R.
  replace (2 : R) with (IZR 2) by reflexivity.
  repeat rewrite <- mult_IZR.
  rewrite <- plus_IZR.
  repeat rewrite <- mult_IZR.
  rewrite <- minus_IZR.
  rewrite <- mult_IZR.
  rewrite <- plus_IZR.
  reflexivity.
Qed.

Lemma clothoid_residual_R_IZR :
  forall nd2 nL nP nQ : Z,
    clothoid_residual_R (IZR nd2) (IZR nL) (IZR nP) (IZR nQ)
    = IZR (nL * nL * (nP * nP + nQ * nQ) - nd2).
Proof.
  intros. unfold clothoid_residual_R, clothoid_r2_R.
  repeat rewrite <- mult_IZR.
  rewrite <- plus_IZR.
  repeat rewrite <- mult_IZR.
  rewrite <- minus_IZR.
  reflexivity.
Qed.

Lemma clothoid_scalar_int_safe_b64Z :
  forall n : Z, (Z.abs n <= 2 ^ 12)%Z -> clothoid_scalar_int_safe (b64Z n).
Proof.
  intros n Hn.
  destruct (b64Z_R n ltac:(lia)) as [HR Hf].
  split; [exact Hf | exists n; split; [exact HR | exact Hn]].
Qed.

Lemma b64Z_two_R :
  Binary.B2R prec emax (b64Z 2) = 2
  /\ Binary.is_finite prec emax (b64Z 2) = true.
Proof. apply b64Z_R; lia. Qed.

Theorem b64_clothoid_d2_exact :
  forall P0 P1 : BPoint,
    clothoid_chord_inputs_int_safe P0 P1 ->
    Binary.B2R prec emax (b64_clothoid_d2 P0 P1) = clothoid_d2_R P0 P1
    /\ Binary.is_finite prec emax (b64_clothoid_d2 P0 P1) = true.
Proof.
  intros P0 P1 Hchord.
  destruct Hchord as (Hx0 & Hy0 & Hx1 & Hy1).
  unfold b64_clothoid_d2, clothoid_d2_R, b64_dist_sq.
  destruct Hx0 as (Fx0 & nx0 & Hx0R & Hx0b).
  destruct Hy0 as (Fy0 & ny0 & Hy0R & Hy0b).
  destruct Hx1 as (Fx1 & nx1 & Hx1R & Hx1b).
  destruct Hy1 as (Fy1 & ny1 & Hy1R & Hy1b).
  set (dx := (nx0 - nx1)%Z). set (dy := (ny0 - ny1)%Z).
  pose proof (arc_diff_bound_2p12 nx0 nx1 Hx0b Hx1b) as Bdx.
  pose proof (arc_diff_bound_2p12 ny0 ny1 Hy0b Hy1b) as Bdy.
  destruct (b64_minus_int_exact (bx P0) (bx P1) nx0 nx1 Fx0 Fx1 Hx0R Hx1R
              (le_2p12_le_2pprec dx Bdx)) as [Hdx Fdx].
  destruct (b64_minus_int_exact (by_ P0) (by_ P1) ny0 ny1 Fy0 Fy1 Hy0R Hy1R
              (le_2p12_le_2pprec dy Bdy)) as [Hdy Fdy].
  destruct (b64_mult_int_exact (b64_minus (bx P0) (bx P1))
              (b64_minus (bx P0) (bx P1)) dx dx Fdx Fdx Hdx Hdx
              (le_2p24_le_2pprec (dx * dx)%Z (clothoid_sq_bound_2p24 dx Bdx)))
    as [Hdx2 Fdx2].
  destruct (b64_mult_int_exact (b64_minus (by_ P0) (by_ P1))
              (b64_minus (by_ P0) (by_ P1)) dy dy Fdy Fdy Hdy Hdy
              (le_2p24_le_2pprec (dy * dy)%Z (clothoid_sq_bound_2p24 dy Bdy)))
    as [Hdy2 Fdy2].
  pose proof (arc_sum_sq_bound_2p25 (dx * dx) (dy * dy)
              (clothoid_sq_bound_2p24 dx Bdx)
              (clothoid_sq_bound_2p24 dy Bdy)) as Bsum.
  destruct (b64_plus_int_exact (b64_mult (b64_minus (bx P0) (bx P1))
                                   (b64_minus (bx P0) (bx P1)))
              (b64_mult (b64_minus (by_ P0) (by_ P1))
                        (b64_minus (by_ P0) (by_ P1)))
              (dx * dx) (dy * dy) Fdx2 Fdy2 Hdx2 Hdy2
              (le_2p25_le_2pprec _ Bsum)) as [Hd2 Fd2].
  split; [ | exact Fd2 ].
  rewrite Hd2.
  rewrite Hx0R, Hx1R, Hy0R, Hy1R.
  rewrite plus_IZR, !mult_IZR.
  repeat rewrite <- minus_IZR.
  reflexivity.
Qed.

Theorem b64_clothoid_r2_exact :
  forall P Q : binary64,
    clothoid_scalar_int_safe P ->
    clothoid_scalar_int_safe Q ->
    Binary.B2R prec emax (b64_clothoid_r2 P Q)
      = clothoid_r2_R (Binary.B2R prec emax P) (Binary.B2R prec emax Q)
    /\ Binary.is_finite prec emax (b64_clothoid_r2 P Q) = true.
Proof.
  intros P Q HP HQ.
  destruct HP as (FP & nP & HPR & HPb).
  destruct HQ as (FQ & nQ & HQR & HQb).
  unfold b64_clothoid_r2, clothoid_r2_R.
  destruct (b64_mult_int_exact P P nP nP FP FP HPR HPR
              (le_2p24_le_2pprec (nP * nP)%Z (clothoid_sq_bound_2p24 nP HPb)))
    as [HP2 FP2].
  destruct (b64_mult_int_exact Q Q nQ nQ FQ FQ HQR HQR
              (le_2p24_le_2pprec (nQ * nQ)%Z (clothoid_sq_bound_2p24 nQ HQb)))
    as [HQ2 FQ2].
  pose proof (arc_sum_sq_bound_2p25 (nP * nP) (nQ * nQ)
              (clothoid_sq_bound_2p24 nP HPb)
              (clothoid_sq_bound_2p24 nQ HQb)) as Bsum.
  destruct (b64_plus_int_exact (b64_mult P P) (b64_mult Q Q)
              (nP * nP) (nQ * nQ) FP2 FQ2 HP2 HQ2
              (le_2p25_le_2pprec _ Bsum)) as [Hr2 Fr2].
  split; [ | exact Fr2 ].
  rewrite Hr2, HPR, HQR.
  rewrite plus_IZR, !mult_IZR. ring.
Qed.

Theorem b64_clothoid_residual_exact :
  forall d2 L P Q : binary64,
    clothoid_scalar_int_safe d2 ->
    clothoid_scalar_int_safe L ->
    clothoid_scalar_int_safe P ->
    clothoid_scalar_int_safe Q ->
    Binary.B2R prec emax (b64_clothoid_residual d2 L P Q)
      = clothoid_residual_R (Binary.B2R prec emax d2) (Binary.B2R prec emax L)
          (Binary.B2R prec emax P) (Binary.B2R prec emax Q)
    /\ Binary.is_finite prec emax (b64_clothoid_residual d2 L P Q) = true.
Proof.
  intros d2 L P Q Hd HL HP HQ.
  pose proof (b64_clothoid_r2_exact P Q HP HQ) as [Hr2R Fr2].
  destruct Hd as (Fd & nd2 & Hd2R & Hd2b).
  destruct HL as (FL & nL & HLR & HLb).
  destruct HP as (FP & nP & HPR & HPb).
  destruct HQ as (FQ & nQ & HQR & HQb).
  unfold b64_clothoid_residual.
  set (nr2 := (nP * nP + nQ * nQ)%Z).
  assert (Hnr2R : Binary.B2R prec emax (b64_clothoid_r2 P Q) = IZR nr2).
  { rewrite Hr2R, HPR, HQR. unfold clothoid_r2_R, nr2.
    rewrite plus_IZR, !mult_IZR. reflexivity. }
  assert (Hnr2b : (Z.abs nr2 <= 2 ^ 25)%Z).
  { subst nr2. apply arc_sum_sq_bound_2p25; apply clothoid_sq_bound_2p24; assumption. }
  destruct (b64_mult_int_exact L L nL nL FL FL HLR HLR
              (le_2p24_le_2pprec (nL * nL)%Z (clothoid_sq_bound_2p24 nL HLb)))
    as [HLL FLL].
  pose proof (clothoid_product_bound_2p49 (nL * nL) nr2
              (clothoid_sq_bound_2p24 nL HLb) Hnr2b) as BLr2.
  destruct (b64_mult_int_exact (b64_mult L L) (b64_clothoid_r2 P Q)
              (nL * nL) nr2 FLL Fr2 HLL Hnr2R
              (le_2p49_le_2pprec _ BLr2)) as [HLr2 FLr2].
  pose proof (clothoid_residual_diff_bound_2p50_scalar (nL * nL * nr2) nd2 BLr2 Hd2b) as Bdiff.
  destruct (b64_minus_int_exact (b64_mult (b64_mult L L) (b64_clothoid_r2 P Q))
              d2 (nL * nL * nr2) nd2 FLr2 Fd HLr2 Hd2R
              (le_2p50_le_2pprec _ Bdiff)) as [Hf Ff].
  split; [ | exact Ff ].
  rewrite Hf, Hd2R, HLR, HPR, HQR, clothoid_residual_R_IZR.
  unfold nr2. reflexivity.
Qed.

Theorem b64_clothoid_residual_prime_exact :
  forall L P Q Rm T : binary64,
    clothoid_scalar_int_safe L ->
    clothoid_scalar_int_safe P ->
    clothoid_scalar_int_safe Q ->
    clothoid_scalar_int_safe Rm ->
    clothoid_scalar_int_safe T ->
    Binary.B2R prec emax (b64_clothoid_residual_prime L P Q Rm T)
      = clothoid_residual_prime_R (Binary.B2R prec emax L)
          (Binary.B2R prec emax P) (Binary.B2R prec emax Q)
          (Binary.B2R prec emax Rm) (Binary.B2R prec emax T)
    /\ Binary.is_finite prec emax (b64_clothoid_residual_prime L P Q Rm T) = true.
Proof.
  intros L P Q Rm T HL HP HQ HRm HT.
  pose proof (b64_clothoid_r2_exact P Q HP HQ) as [Hr2R Fr2].
  destruct HL as (FL & nL & HLR & HLb).
  destruct HP as (FP & nP & HPR & HPb).
  destruct HQ as (FQ & nQ & HQR & HQb).
  destruct HRm as (FRm & nRm & HRmR & HRmb).
  destruct HT as (FT & nT & HTR & HTb).
  unfold b64_clothoid_residual_prime.
  set (nr2 := (nP * nP + nQ * nQ)%Z).
  assert (Hnr2R : Binary.B2R prec emax (b64_clothoid_r2 P Q) = IZR nr2).
  { rewrite Hr2R, HPR, HQR. unfold clothoid_r2_R, nr2.
    rewrite plus_IZR, !mult_IZR. reflexivity. }
  assert (Hnr2b : (Z.abs nr2 <= 2 ^ 25)%Z).
  { subst nr2. apply arc_sum_sq_bound_2p25; apply clothoid_sq_bound_2p24; assumption. }
  destruct b64Z_two_R as [H2R F2].
  destruct (b64_mult_int_exact (b64Z 2) L 2 nL F2 FL H2R HLR
              (le_2p13_le_2pprec (2 * nL)%Z (clothoid_double_bound_2p13 nL HLb)))
    as [H2L F2L].
  destruct (b64_mult_int_exact (b64_mult (b64Z 2) L) (b64_clothoid_r2 P Q)
              (2 * nL) nr2 F2L Fr2 H2L Hnr2R
              (le_2p38_le_2pprec _ (clothoid_product_bound_2p38 (2 * nL) nr2
                  (clothoid_double_bound_2p13 nL HLb) Hnr2b)))
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
  destruct (b64_mult_int_exact L L nL nL FL FL HLR HLR
              (le_2p24_le_2pprec _ (clothoid_sq_bound_2p24 nL HLb))) as [HLL FLL].
  destruct (b64_mult_int_exact (b64Z 2) (b64_mult L L) 2 (nL * nL) F2 FLL H2R HLL
              (le_2p25_le_2pprec (2 * (nL * nL)) (clothoid_double_sq_bound_2p25 nL HLb)))
    as [H2LL F2LL].
  pose proof (arc_row4_bound_2p50 (2 * (nL * nL)) nqrpt
              (clothoid_double_sq_bound_2p25 nL HLb) Bqrpt) as Bt2.
  destruct (b64_mult_int_exact (b64_mult (b64Z 2) (b64_mult L L))
              (b64_minus (b64_mult Q Rm) (b64_mult P T))
              (2 * (nL * nL)) nqrpt F2LL Fqrpt H2LL Hqrpt
              (le_2p50_le_2pprec _ Bt2)) as [Ht2 Ft2].
  pose proof (clothoid_prime_sum_bound_2p51 (2 * nL * nr2) (2 * (nL * nL) * nqrpt)
              (clothoid_product_bound_2p38 (2 * nL) nr2
                (clothoid_double_bound_2p13 nL HLb) Hnr2b) Bt2) as Bsum.
  destruct (b64_plus_int_exact (b64_mult (b64_mult (b64Z 2) L) (b64_clothoid_r2 P Q))
              (b64_mult (b64_mult (b64Z 2) (b64_mult L L))
                        (b64_minus (b64_mult Q Rm) (b64_mult P T)))
              (2 * nL * nr2) (2 * (nL * nL) * nqrpt) Ft1 Ft2 Ht1 Ht2
              (le_2p51_le_2pprec _ Bsum)) as [Hfp Ffp].
  split; [ | exact Ffp ].
  rewrite Hfp, HLR, HPR, HQR, HRmR, HTR, clothoid_residual_prime_R_IZR.
  unfold nr2, nqrpt. f_equal. ring.
Qed.

Lemma b64_clothoid_r2_one_zero :
  b64_clothoid_r2 (b64Z 1) (b64Z 0) = b64Z 1.
Proof.
  unfold b64_clothoid_r2.
  destruct (b64Z_R 1 ltac:(lia)) as [H1R F1].
  destruct (b64Z_R 0 ltac:(lia)) as [H0R F0].
  destruct (b64Z_R 1 ltac:(lia)) as [_ F1'].
  destruct (b64_mult_int_exact (b64Z 1) (b64Z 1) 1 1 F1 F1' H1R H1R
              (le_2p24_le_2pprec 1 ltac:(lia))) as [H11 _].
  destruct (b64_mult_int_exact (b64Z 0) (b64Z 0) 0 0 F0 F0 H0R H0R
              (le_2p24_le_2pprec 0 ltac:(lia))) as [H00 _].
  destruct (b64_plus_int_exact (b64_mult (b64Z 1) (b64Z 1)) (b64_mult (b64Z 0) (b64Z 0))
              1 0 F1 F0 H11 H00 (le_2p25_le_2pprec 1 ltac:(lia))) as [H1 Fplus].
  destruct (b64Z_R 1 ltac:(lia)) as [H1Z F1''].
  apply Binary.B2R_Bsign_inj; [exact Fplus | exact F1'' | | ].
  - rewrite H1, H1Z. reflexivity.
  - unfold b64Z. simpl. reflexivity.
Qed.

Theorem b64_clothoid_residual_unit_moments :
  forall d2 L : binary64,
    clothoid_scalar_int_safe d2 ->
    clothoid_scalar_int_safe L ->
    b64_clothoid_residual d2 L (b64Z 1) (b64Z 0)
    = b64_minus (b64_mult (b64_mult L L) (b64Z 1)) d2.
Proof.
  intros d2 L _ _.
  unfold b64_clothoid_residual.
  rewrite b64_clothoid_r2_one_zero. reflexivity.
Qed.

Print Assumptions b64_clothoid_d2_exact.
Print Assumptions b64_clothoid_r2_exact.
Print Assumptions b64_clothoid_residual_exact.
Print Assumptions b64_clothoid_residual_prime_exact.
Print Assumptions b64_clothoid_residual_unit_moments.