(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_SegGRel
   ----------------------------------------------------------------------------
   T3 prerequisite, rung 2: a RELATIVE error bound for the segment denominator
   g(a) = a - sin a, for 2^-338 <= a <= 1, evaluated WITHOUT cancellation as
   a^3 Q(a^2) on the tail of the existing sine polynomial.

   Mathematics.  P(z) = sum (-1)^k z^k / (2k+1)!  (B64_SinPoly), so
   P(z) = 1 + z T(z) with T = the tail polynomial, and
     a - sin a = a - a P(a^2) + (a P(a^2) - sin a) = a^3 Q(a^2) + eps,
   Q = -T, |eps| <= a^3 / 25852016738884976640000 (a <= 1, sg_trunc_cube).

   Real layer (no binary64):
     sg_g_enclosure   0 <= a <= 1 -> 19/120 a^3 <= a - sin a <= a^3/6
     sg_g_poly        |(a - sin a) - a^3 Q(a^2)| <= a^3 / 25852016738884976640000
     sg_Qex_range     0 < a <= 1 -> 79/500 <= Q(a^2) <= 167/1000
   Pipeline (binary64, RNE, extractable, no FMA):
     z = a*a, w = a*z, Tm = Horner(tl sp_coeffs)(z), g^ = -(w*Tm)   (mf_seg_g_poly)
     mf_seg_g_poly_rel   fin a, 2^-338 <= a <= 1 ->
                         |g^ - (a - sin a)| <= 24 u (a - sin a)      (u = 2^-53)
   Budget (units of u a^3): final product + absorbed underflow ~1.17,
   (w - a^3) q ~0.84, Q error (Horner sp_E1 + argument rounding through the
   Lipschitz bound sp_L1 + coefficients, <= u) 1, truncation ~0;  total ~3.02
   u a^3, and a^3 <= (120/19)(a - sin a) gives ~19.1 u g, stated as 24.
   The floor 2^-338 makes a^3 >= 2^-1014 normal, so the underflow term 2^-1075
   is absorbed (B64_SinRel.tiny_abs_to_rel); g itself stops being normal near
   a ~ 2^-340, so this is the intrinsic floor, not an artefact of the method.
   Evaluation only: no extraction, no oracle mode, no port, no consumer switch.
   claimId: t3-seg-g-rel.  No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly B64_Sin B64_SinRel.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  Real layer.                                                            *)
(* -------------------------------------------------------------------------- *)

Definition sg_Qex (x : R) : R := - hz_horner_R (tl sp_exact) x.

Lemma sg_pow2 : forall x n, 0 <= x <= 1 -> x ^ (S (S n)) <= x ^ n.
Proof.
  intros x n [H0 H1]. cbn [pow].
  assert (Hn : 0 <= x ^ n) by (apply pow_le; lra).
  assert (Hxx : x * x <= 1) by nra.
  replace (x * (x * x ^ n)) with ((x * x) * x ^ n) by ring.
  nra.
Qed.

Lemma sg_sin_approx3 : forall a,
  sin_approx a 3 = a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040.
Proof.
  intro a. unfold sin_approx, sin_term. cbn [sum_f_R0 Nat.mul Nat.add].
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (sp_INR_fact_S n) end.
  rewrite ?sp_INR_fact_0.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. field.
Qed.

Lemma sg_sin_approx4 : forall a,
  sin_approx a 4 = a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040 + a ^ 9 / 362880.
Proof.
  intro a. unfold sin_approx, sin_term. cbn [sum_f_R0 Nat.mul Nat.add].
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (sp_INR_fact_S n) end.
  rewrite ?sp_INR_fact_0.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. field.
Qed.

Lemma sg_g_enclosure : forall a, 0 <= a <= 1 ->
  19 / 120 * (a * (a * a)) <= a - sin a /\ a - sin a <= a * (a * a) / 6.
Proof.
  intros a Ha.
  assert (Hpi : 1 <= PI) by (pose proof sp_pi_bounds as [H _]; unfold sp_pi_lo in H; lra).
  destruct (sin_bound a 1 ltac:(lra) ltac:(lra)) as [H1 H2].
  change (2 * 1 + 1)%nat with 3%nat in H1. change (2 * (1 + 1))%nat with 4%nat in H2.
  rewrite sg_sin_approx3 in H1. rewrite sg_sin_approx4 in H2.
  assert (P3 : a ^ 5 <= a ^ 3) by exact (sg_pow2 a 3 Ha).
  assert (P5 : a ^ 7 <= a ^ 5) by exact (sg_pow2 a 5 Ha).
  assert (P7 : a ^ 9 <= a ^ 7) by exact (sg_pow2 a 7 Ha).
  assert (N5 : 0 <= a ^ 5) by (apply pow_le; lra).
  assert (N7 : 0 <= a ^ 7) by (apply pow_le; lra).
  assert (N9 : 0 <= a ^ 9) by (apply pow_le; lra).
  replace (a * (a * a)) with (a ^ 3) by ring.
  split; lra.
Qed.

(* Truncation relative to a^3 (a <= 1): the sp_trunc proof with a^23 <= a^3. *)
Lemma sg_trunc_cube : forall a, 0 <= a <= 1 ->
  Rabs (a * hz_horner_R sp_exact (a * a) - sin a)
    <= a * (a * a) / 25852016738884976640000.
Proof.
  intros a Ha.
  assert (Hpi : 1 <= PI) by (pose proof sp_pi_bounds as [H _]; unfold sp_pi_lo in H; lra).
  destruct (sin_bound a 5 ltac:(lra) ltac:(lra)) as [H1 H2].
  change (2 * 5 + 1)%nat with 11%nat in H1. change (2 * (5 + 1))%nat with 12%nat in H2.
  rewrite sp_sin_approx_11 in H1. rewrite sp_sin_approx_12 in H2.
  assert (P23 : 0 <= a ^ 23) by (apply pow_le; lra).
  assert (C23 : a ^ 23 <= a * (a * a)).
  { replace (a * (a * a)) with (a ^ 3) by ring.
    assert (E : a ^ 23 = a ^ 3 * a ^ 20) by ring.
    assert (B20 : a ^ 20 <= 1).
    { pose proof (pow_incr a 1 20 ltac:(lra)) as H. rewrite pow1 in H. exact H. }
    assert (0 <= a ^ 3) by (apply pow_le; lra).
    nra. }
  assert (A25 : a ^ 25 / 15511210043330985984000000 <= a ^ 23 / 25852016738884976640000).
  { replace (a ^ 25) with (a ^ 23 * (a * a)) by ring.
    assert (a * a <= 1) by nra.
    assert (a ^ 23 * (a * a) <= a ^ 23 * 1) by (apply Rmult_le_compat_l; lra).
    lra. }
  assert (0 <= a ^ 25 / 15511210043330985984000000)
    by (apply Rmult_le_pos; [apply pow_le; lra | lra]).
  apply Rabs_le. split; lra.
Qed.

Lemma sg_g_poly : forall a, 0 <= a <= 1 ->
  Rabs ((a - sin a) - a * (a * a) * sg_Qex (a * a))
    <= a * (a * a) / 25852016738884976640000.
Proof.
  intros a Ha.
  pose proof (sg_trunc_cube a Ha) as T.
  assert (Hsplit : hz_horner_R sp_exact (a * a) = hz_horner_R (tl sp_exact) (a * a) * (a * a) + 1)
    by (unfold sp_exact; cbn [hz_horner_R tl]; ring).
  unfold sg_Qex.
  replace ((a - sin a) - a * (a * a) * - hz_horner_R (tl sp_exact) (a * a))
    with (a * hz_horner_R sp_exact (a * a) - sin a) by (rewrite Hsplit; ring).
  exact T.
Qed.

Lemma sg_Qex_range : forall a, 0 < a <= 1 ->
  79 / 500 <= sg_Qex (a * a) <= 167 / 1000.
Proof.
  intros a Ha.
  pose proof (sg_g_enclosure a ltac:(lra)) as [Gl Gu].
  pose proof (sg_g_poly a ltac:(lra)) as Gp.
  apply Rabs_le_inv in Gp as [Gp1 Gp2].
  assert (HA : 0 < a * (a * a)) by (apply Rmult_lt_0_compat; [lra | apply Rmult_lt_0_compat; lra]).
  set (A := a * (a * a)) in *. set (Q := sg_Qex (a * a)) in *.
  split.
  - apply Rmult_le_reg_l with A; [exact HA|].
    assert (A * (79 / 500) <= A * Q) by nra. lra.
  - apply Rmult_le_reg_l with A; [exact HA|]. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The pure-real budget.                                                  *)
(* -------------------------------------------------------------------------- *)

Lemma sg_alg : forall (a zr wr Tr fr Qx e : R),
  0 < a <= 1 ->
  e <= / 9007199254740992 * (a * (a * a)) ->
  e <= / 9007199254740992 * (a * a) ->
  Rabs (zr - a * a) <= / 9007199254740992 * Rabs (a * a) + e ->
  Rabs (wr - a * zr) <= / 9007199254740992 * Rabs (a * zr) + e ->
  Rabs (fr - wr * Tr) <= / 9007199254740992 * Rabs (wr * Tr) + e ->
  Rabs ((- Tr) - Qx) <= / 9007199254740992 ->
  79 / 500 <= Qx <= 167 / 1000 ->
  Rabs ((a - sin a) - a * (a * a) * Qx) <= a * (a * a) / 25852016738884976640000 ->
  19 / 120 * (a * (a * a)) <= a - sin a ->
  Rabs ((- fr) - (a - sin a)) <= 24 * (/ 9007199254740992 * (a - sin a)).
Proof.
  intros a zr wr Tr fr Qx e Ha He3 He2 Hz Hw Hf HT HQ Hg Hgl.
  set (U := / 9007199254740992) in *.
  assert (HU : 0 < U <= / 1000) by (unfold U; split; lra).
  set (A := a * (a * a)) in *.
  assert (HA : 0 < A) by (unfold A; apply Rmult_lt_0_compat; [lra | apply Rmult_lt_0_compat; lra]).
  assert (HA1 : A <= 1) by (unfold A; nra).
  assert (Haa : 0 <= a * a) by nra.
  rewrite (Rabs_right (a * a)) in Hz by lra.
  assert (Hz2 : Rabs (zr - a * a) <= 2 * U * (a * a)) by lra.
  apply Rabs_le_inv in Hz2 as [Hz2l Hz2u].
  assert (Hzr : 0 <= zr) by nra.
  assert (S3 : Rabs (a * zr - A) <= 2 * U * A).
  { replace (a * zr - A) with (a * (zr - a * a)) by (unfold A; ring).
    rewrite Rabs_mult, (Rabs_right a) by lra.
    assert (a * Rabs (zr - a * a) <= a * (2 * U * (a * a)))
      by (apply Rmult_le_compat_l; [lra | exact (Rabs_le _ _ (conj Hz2l Hz2u))]).
    unfold A. nra. }
  pose proof (Rabs_le_inv _ _ S3) as [S3l S3u].
  assert (Hazr : Rabs (a * zr) <= A * (1 + 2 * U)).
  { rewrite Rabs_right by (apply Rle_ge; nra). lra. }
  assert (Hw' : Rabs (wr - A) <= 5 * U * A).
  { assert (Rabs (wr - A) <= Rabs (wr - a * zr) + Rabs (a * zr - A)).
    { replace (wr - A) with ((wr - a * zr) + (a * zr - A)) by ring. apply Rabs_triang. }
    assert (U * Rabs (a * zr) <= U * (A * (1 + 2 * U))) by (apply Rmult_le_compat_l; lra).
    assert (U * (A * (1 + 2 * U)) <= 2 * U * A) by nra.
    nra. }
  apply Rabs_le_inv in Hw' as [Hw'l Hw'u].
  assert (Hwr : Rabs wr <= A * (1 + 5 * U)) by (apply Rabs_le; split; nra).
  assert (Hq : Rabs (- Tr) <= 168 / 1000).
  { apply Rabs_le_inv in HT as [HTl HTu]. apply Rabs_le. split; lra. }
  rewrite Rabs_Ropp in Hq.
  assert (Hwt : Rabs (wr * Tr) <= A * (17 / 100)).
  { rewrite Rabs_mult.
    assert (Rabs wr * Rabs Tr <= (A * (1 + 5 * U)) * (168 / 1000))
      by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hwr | exact Hq]).
    nra. }
  assert (Hf' : Rabs (fr - wr * Tr) <= U * (A * (17 / 100)) + U * A).
  { assert (U * Rabs (wr * Tr) <= U * (A * (17 / 100))) by (apply Rmult_le_compat_l; lra).
    lra. }
  assert (Hmid : Rabs (wr * (- Tr) - A * Qx) <= (5 * U * A) * (168 / 1000) + A * U).
  { replace (wr * (- Tr) - A * Qx) with ((wr - A) * (- Tr) + A * ((- Tr) - Qx)) by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    assert (X1 : Rabs ((wr - A) * (- Tr)) <= (5 * U * A) * (168 / 1000)).
    { rewrite Rabs_mult, Rabs_Ropp. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | | exact Hq].
      apply Rabs_le; split; lra. }
    assert (X2 : Rabs (A * ((- Tr) - Qx)) <= A * U).
    { rewrite Rabs_mult, (Rabs_right A) by lra. apply Rmult_le_compat_l; lra. }
    lra. }
  replace ((- fr) - (a - sin a))
    with (- (fr - wr * Tr) + (wr * (- Tr) - A * Qx) + (A * Qx - (a - sin a))) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang|].
  rewrite Rabs_Ropp.
  assert (Hg' : Rabs (A * Qx - (a - sin a)) <= A / 25852016738884976640000).
  { rewrite <- Rabs_Ropp. replace (- (A * Qx - (a - sin a))) with ((a - sin a) - A * Qx) by ring.
    exact Hg. }
  assert (Hgpos : A <= 120 / 19 * (a - sin a)) by lra.
  assert (Hfin : U * A <= U * (120 / 19 * (a - sin a))) by (apply Rmult_le_compat_l; lra).
  assert (Hfin2 : A / 25852016738884976640000 <= U * A).
  { unfold U. lra. }
  nra.
Qed.
