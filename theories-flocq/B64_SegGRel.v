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
   (w - a^3) q ~0.67, Q error (Horner sp_E1 + argument rounding through the
   Lipschitz bound sp_L1 + coefficients, <= u) 1, truncation ~0.001; total
   ~2.85, proved as 2.9 u a^3, and a^3 <= (120/19)(a - sin a) gives ~18.3 u g,
   stated as 24 (the extra headroom is deliberate).
   Floor.  The proof needs a^3 >= 2^-1022 so that the underflow term 2^-1075 is
   absorbed (B64_SinRel.tiny_abs_to_rel), i.e. a >= 2^-340.67; and g ~ a^3/6
   leaves the normal range near a ~ 2^-339.8.  2^-338 is a round value about two
   binades more conservative than either; it is a choice, not a proof limit.
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
  Rabs (zr - a * a) <= / 9007199254740992 * Rabs (a * a) + e ->
  Rabs (wr - a * zr) <= / 9007199254740992 * Rabs (a * zr) + e ->
  Rabs (fr - wr * Tr) <= / 9007199254740992 * Rabs (wr * Tr) + e ->
  Rabs ((- Tr) - Qx) <= / 9007199254740992 ->
  79 / 500 <= Qx <= 167 / 1000 ->
  Rabs ((a - sin a) - a * (a * a) * Qx) <= a * (a * a) / 25852016738884976640000 ->
  19 / 120 * (a * (a * a)) <= a - sin a ->
  Rabs ((- fr) - (a - sin a)) <= 24 * (/ 9007199254740992 * (a - sin a)).
Proof.
  intros a zr wr Tr fr Qx e Ha He3 Hz Hw Hf HT HQ Hg Hgl.
  set (U := / 9007199254740992) in *.
  assert (HU : 0 < U <= / 1000) by (unfold U; split; lra).
  set (A := a * (a * a)) in *.
  assert (HA : 0 < A) by (unfold A; apply Rmult_lt_0_compat; [lra | apply Rmult_lt_0_compat; lra]).
  assert (HA1 : A <= 1) by (unfold A; nra).
  assert (Haa : 0 <= a * a) by nra.
  assert (He2 : e <= U * (a * a)).
  { assert (A <= a * a) by (unfold A; nra).
    assert (U * A <= U * (a * a)) by (apply Rmult_le_compat_l; lra). lra. }
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
  assert (Hw' : Rabs (wr - A) <= 401 / 100 * U * A).
  { assert (Rabs (wr - A) <= Rabs (wr - a * zr) + Rabs (a * zr - A)).
    { replace (wr - A) with ((wr - a * zr) + (a * zr - A)) by ring. apply Rabs_triang. }
    assert (U * Rabs (a * zr) <= U * (A * (1 + 2 * U))) by (apply Rmult_le_compat_l; lra).
    assert (U * (A * (1 + 2 * U)) <= 101 / 100 * U * A) by nra.
    nra. }
  apply Rabs_le_inv in Hw' as [Hw'l Hw'u].
  assert (Hwr : Rabs wr <= A * (1 + 401 / 100 * U)) by (apply Rabs_le; split; nra).
  assert (Hq : Rabs (- Tr) <= 168 / 1000).
  { apply Rabs_le_inv in HT as [HTl HTu]. apply Rabs_le. split; lra. }
  rewrite Rabs_Ropp in Hq.
  assert (Hwt : Rabs (wr * Tr) <= A * (17 / 100)).
  { rewrite Rabs_mult.
    assert (Rabs wr * Rabs Tr <= (A * (1 + 401 / 100 * U)) * (168 / 1000))
      by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hwr | exact Hq]).
    nra. }
  assert (Hf' : Rabs (fr - wr * Tr) <= U * (A * (17 / 100)) + U * A).
  { assert (U * Rabs (wr * Tr) <= U * (A * (17 / 100))) by (apply Rmult_le_compat_l; lra).
    lra. }
  assert (Hmid : Rabs (wr * (- Tr) - A * Qx) <= (401 / 100 * U * A) * (168 / 1000) + A * U).
  { replace (wr * (- Tr) - A * Qx) with ((wr - A) * (- Tr) + A * ((- Tr) - Qx)) by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    assert (X1 : Rabs ((wr - A) * (- Tr)) <= (401 / 100 * U * A) * (168 / 1000)).
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
  (* The chain, one closed step at a time:
       |g^ - g| <= 2.9 U A             (sum of the budget lines, ~2.85)
       A <= 120/19 g                   (from 19/120 A <= g)
       2.9 * 120/19 = 18.32 <= 24. *)
  assert (Hfin2 : A / 25852016738884976640000 <= U * A / 1000) by (unfold U; lra).
  assert (Hlin : Rabs (fr - wr * Tr)
                 + Rabs (wr * (- Tr) - A * Qx) + Rabs (A * Qx - (a - sin a))
                 <= U * A * (29 / 10)) by lra.
  assert (Hgpos : A <= 120 / 19 * (a - sin a)) by lra.
  assert (Hg0 : 0 <= a - sin a) by lra.
  assert (HUg : 0 <= U * (a - sin a)) by (apply Rmult_le_pos; lra).
  assert (Hconv : U * A * (29 / 10) <= U * (120 / 19 * (a - sin a)) * (29 / 10)).
  { assert (U * A <= U * (120 / 19 * (a - sin a))) by (apply Rmult_le_compat_l; lra).
    lra. }
  assert (Hrat : U * (120 / 19 * (a - sin a)) * (29 / 10)
                 <= 24 * (U * (a - sin a))).
  { replace (U * (120 / 19 * (a - sin a)) * (29 / 10))
      with ((120 / 19 * (29 / 10)) * (U * (a - sin a))) by ring.
    apply Rmult_le_compat_r; [exact HUg | lra]. }
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The binary64 pipeline.                                                 *)
(* -------------------------------------------------------------------------- *)

Definition sg_T (z : binary64) : binary64 := b64_horner (tl sp_coeffs) z.

Definition mf_seg_g_poly (t : binary64) : binary64 :=
  sn_neg (b64_mult (b64_mult t (b64_mult t t)) (sg_T (b64_mult t t))).

Lemma sg_floor : forall a, bpow radix2 (-338) <= a ->
  bpow radix2 (-1022) <= a * a /\ bpow radix2 (-1022) <= a * (a * a).
Proof.
  intros a H.
  assert (Hb : 0 < bpow radix2 (-338)) by apply bpow_gt_0.
  assert (H2 : bpow radix2 (-338) * bpow radix2 (-338) <= a * a)
    by (apply Rmult_le_compat; lra).
  assert (H3 : bpow radix2 (-338) * (bpow radix2 (-338) * bpow radix2 (-338)) <= a * (a * a)).
  { apply Rmult_le_compat; [lra | nra | exact H | exact H2]. }
  assert (E2 : bpow radix2 (-338) * bpow radix2 (-338) = bpow radix2 (-676))
    by (rewrite <- bpow_plus; reflexivity).
  assert (E3 : bpow radix2 (-338) * (bpow radix2 (-338) * bpow radix2 (-338))
               = bpow radix2 (-1014)) by (rewrite <- !bpow_plus; reflexivity).
  assert (L2 : bpow radix2 (-1022) <= bpow radix2 (-676)) by (apply bpow_le; lia).
  assert (L3 : bpow radix2 (-1022) <= bpow radix2 (-1014)) by (apply bpow_le; lia).
  split; lra.
Qed.

Lemma sg_coeffs_ok : hz_coeffs_ok (tl sp_coeffs) sp_S1.
Proof.
  pose proof sp_coeffs_ok as H. unfold hz_coeffs_ok in *.
  unfold sp_coeffs, sp_ms, sp_S0 in H. inversion H; subst. cbn [tl]. assumption.
Qed.

Lemma sg_coeffs_ok_R :
  Forall2 (fun c m => Rabs c <= m) (map B2R (tl sp_coeffs)) sp_S1.
Proof.
  pose proof sp_coeffs_ok_R as H.
  unfold sp_coeffs, sp_ms, sp_S0 in H. cbn [map] in H. inversion H; subst.
  unfold sp_coeffs. cbn [tl map]. assumption.
Qed.

Lemma sg_delta_ok : Forall2 (fun c m => Rabs c <= m) (tl sp_delta) (tl sp_ds).
Proof.
  pose proof sp_delta_ok as H.
  unfold sp_delta, sp_ds in H. inversion H; subst.
  unfold sp_delta, sp_ds. cbn [tl]. assumption.
Qed.

Lemma sg_delta_eq : forall x,
  hz_horner_R (map B2R (tl sp_coeffs)) x - hz_horner_R (tl sp_exact) x
  = hz_horner_R (tl sp_delta) x.
Proof. intro x. unfold sp_coeffs, sp_exact, sp_delta. cbn [map tl hz_horner_R]. ring. Qed.

Lemma sg_ds_M : hz_M (tl sp_ds) sp_Z <= 11182133 / 302231454903657293676544.
Proof. unfold sp_ds, sp_Z. cbn [tl hz_M]. lra. Qed.

Lemma sg_T_err : forall z, fin z = true -> Rabs (B2R z) <= sp_Z ->
  fin (sg_T z) = true /\
  Rabs (B2R (sg_T z) - hz_horner_R (map B2R (tl sp_coeffs)) (B2R z))
    <= 12704089 / 302231454903657293676544.
Proof.
  intros z Fz Hz.
  destruct (b64_horner_err (tl sp_coeffs) sp_S1 z sp_Z sg_coeffs_ok Fz Hz
              sp_Z_nonneg sp_safe1) as [F E].
  split; [exact F|]. eapply Rle_trans; [exact E | exact sp_E1].
Qed.

Lemma sg_tri3 : forall t h1 h2 e : R,
  (- t) - (- e) = - ((t - h1) + (h1 - h2) + (h2 - e)).
Proof. intros. ring. Qed.

Lemma sg_Q_numeric :
  12704089 / 302231454903657293676544 + / 50 * (2 * / 9007199254740992)
  + 11182133 / 302231454903657293676544 <= / 9007199254740992.
Proof. lra. Qed.

(* WITNESS-free: registered in verified-claims.md (claimId t3-seg-g-rel). *)
Theorem mf_seg_g_poly_rel : forall t, fin t = true ->
  bpow radix2 (-338) <= B2R t -> B2R t <= 1 ->
  fin (mf_seg_g_poly t) = true /\
  Rabs (B2R (mf_seg_g_poly t) - (B2R t - sin (B2R t)))
    <= 24 * (b64ae_u * (B2R t - sin (B2R t))).
Proof.
  intros t Ft Hlo Hhi.
  set (a := B2R t) in *.
  pose proof sp_u_val as Uv. pose proof sp_e0_bounds as [He0 He1].
  assert (Hb : 4 <= bpow radix2 1000) by exact sp_bpow1000.
  assert (Ha : 0 < a) by (pose proof (bpow_gt_0 radix2 (-338)); lra).
  destruct (sg_floor a Hlo) as [Fl2 Fl3].
  assert (Haa : 0 <= a * a) by nra.
  assert (Haa1 : a * a <= 1) by nra.
  assert (Hcube : 0 <= a * (a * a) <= 1) by (split; nra).
  assert (R2 : Rabs (a * a) = a * a) by (apply Rabs_right; lra).
  assert (T3 : b64ae_e0 <= b64ae_u * (a * (a * a))).
  { pose proof (tiny_abs_to_rel (a * (a * a))) as H.
    rewrite (Rabs_right (a * (a * a))) in H by lra. apply H. exact Fl3. }
  (* z = fl(a a) *)
  destruct (b64ae_mult_err t t Ft Ft
              ltac:(change (B2R t) with a; rewrite R2; lra)) as [Fz Ez].
  change (B2R t) with a in Ez. rewrite R2 in Ez.
  set (z := b64_mult t t) in *. set (zr := B2R z) in *.
  assert (T2 : b64ae_e0 <= b64ae_u * (a * a)).
  { assert (Hc : a * (a * a) <= a * a) by nra.
    pose proof b64ae_u_small as [Hu0 _].
    assert (b64ae_u * (a * (a * a)) <= b64ae_u * (a * a))
      by (apply Rmult_le_compat_l; lra).
    lra. }
  assert (Hz2 : Rabs (zr - a * a) <= 2 * b64ae_u * (a * a)) by lra.
  pose proof (Rabs_le_inv _ _ Hz2) as [Hz2l Hz2u].
  assert (Hu1 : b64ae_u <= / 1000) by (rewrite Uv; lra).
  assert (Hzr : Rabs zr <= 41 / 16) by (apply Rabs_le; split; nra).
  (* T = Horner of the tail at zr *)
  destruct (sg_T_err z Fz ltac:(unfold sp_Z; exact Hzr)) as [FT ET'].
  set (Tr := B2R (sg_T z)) in *.
  (* the real tail: Lipschitz and coefficient errors *)
  assert (Hxx : Rabs (a * a) <= sp_Z) by (unfold sp_Z; rewrite R2; lra).
  pose proof (hz_horner_R_lip _ _ zr (a * a) sp_Z sg_coeffs_ok_R
                ltac:(unfold sp_Z; exact Hzr) Hxx) as Lip.
  assert (Lb : hz_L sp_S1 sp_Z <= / 50)
    by (eapply Rle_trans; [exact sp_L1|]; lra).
  assert (Hd : Rabs (zr - a * a) <= 2 * b64ae_u) by (rewrite Uv in *; lra).
  assert (Lip' : Rabs (hz_horner_R (map B2R (tl sp_coeffs)) zr
                       - hz_horner_R (map B2R (tl sp_coeffs)) (a * a))
                 <= / 50 * (2 * b64ae_u)).
  { eapply Rle_trans; [exact Lip|].
    assert (hz_L sp_S1 sp_Z * Rabs (zr - a * a) <= / 50 * Rabs (zr - a * a))
      by (apply Rmult_le_compat_r; [apply Rabs_pos | exact Lb]).
    assert (/ 50 * Rabs (zr - a * a) <= / 50 * (2 * b64ae_u))
      by (apply Rmult_le_compat_l; [lra | exact Hd]).
    lra. }
  assert (Hcoef : Rabs (hz_horner_R (map B2R (tl sp_coeffs)) (a * a)
                        - hz_horner_R (tl sp_exact) (a * a))
                  <= 11182133 / 302231454903657293676544).
  { rewrite sg_delta_eq.
    eapply Rle_trans; [apply (hz_horner_R_bound_R _ _ (a * a) sp_Z sg_delta_ok Hxx)|].
    exact sg_ds_M. }
  (* Q error: |(-Tr) - Qex(a a)| <= u *)
  assert (HT : Rabs ((- Tr) - sg_Qex (a * a)) <= / 9007199254740992).
  { unfold sg_Qex.
    rewrite (sg_tri3 Tr (hz_horner_R (map B2R (tl sp_coeffs)) zr)
                     (hz_horner_R (map B2R (tl sp_coeffs)) (a * a))
                     (hz_horner_R (tl sp_exact) (a * a))).
    rewrite Rabs_Ropp.
    eapply Rle_trans; [apply Rabs_triang|].
    eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang|].
    rewrite Uv in Lip'.
    exact (Rle_trans _ _ _
             (Rplus_le_compat _ _ _ _ (Rplus_le_compat _ _ _ _ ET' Lip') Hcoef)
             sg_Q_numeric). }
  pose proof (sg_Qex_range a ltac:(lra)) as HQ.
  assert (HTr : Rabs Tr <= 168 / 1000).
  { pose proof (Rabs_le_inv _ _ HT) as [HTl HTu]. apply Rabs_le. split; lra. }
  (* w = fl(a z) *)
  assert (Hzr0 : 0 <= zr) by nra.
  assert (Hzr1 : zr <= 2) by nra.
  assert (Hazr : Rabs (a * zr) <= 2).
  { rewrite Rabs_mult, (Rabs_right a) by lra. rewrite (Rabs_right zr) by lra. nra. }
  destruct (b64ae_mult_err t z Ft Fz ltac:(change (B2R t) with a; change (B2R z) with zr; lra)) as [Fw Ew].
  change (B2R t) with a in Ew. change (B2R z) with zr in Ew.
  set (w := b64_mult t z) in *. set (wr := B2R w) in *.
  assert (Hwr : Rabs wr <= 3).
  { pose proof (Rabs_triang_inv wr (a * zr)).
    assert (b64ae_u * Rabs (a * zr) <= b64ae_u * 2) by (apply Rmult_le_compat_l; lra).
    lra. }
  (* p = fl(w Tm) *)
  assert (Hwt : Rabs (wr * Tr) <= 3 * (168 / 1000))
    by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err w (sg_T z) Fw FT ltac:(change (B2R w) with wr; change (B2R (sg_T z)) with Tr; lra))
    as [Fp Ep].
  change (B2R w) with wr in Ep. change (B2R (sg_T z)) with Tr in Ep.
  destruct (sn_neg_ok _ Fp) as [Fn En].
  assert (Hmf : mf_seg_g_poly t = sn_neg (b64_mult w (sg_T z))) by reflexivity.
  rewrite Hmf. split; [exact Fn|]. rewrite En.
  pose proof (sg_g_enclosure a ltac:(lra)) as [Gl _].
  pose proof (sg_g_poly a ltac:(lra)) as Gp.
  rewrite Uv in *.
  assert (Ez0 : Rabs (zr - a * a) <= / 9007199254740992 * Rabs (a * a) + b64ae_e0)
    by (rewrite R2; exact Ez).
  exact (sg_alg a zr wr Tr (B2R (b64_mult w (sg_T z))) (sg_Qex (a * a)) b64ae_e0
           (conj Ha Hhi) T3 Ez0 Ew Ep HT HQ Gp Gl).
Qed.

(* A positive computed value: the relative bound forces g^ > 0. *)
Corollary mf_seg_g_poly_pos : forall t, fin t = true ->
  bpow radix2 (-338) <= B2R t -> B2R t <= 1 ->
  0 < B2R (mf_seg_g_poly t).
Proof.
  intros t Ft Hlo Hhi.
  destruct (mf_seg_g_poly_rel t Ft Hlo Hhi) as [_ E].
  pose proof sp_u_val as Uv. rewrite Uv in E.
  assert (Ha : 0 < B2R t) by (pose proof (bpow_gt_0 radix2 (-338)); lra).
  pose proof (sg_g_enclosure (B2R t) ltac:(lra)) as [Gl _].
  assert (0 < B2R t * (B2R t * B2R t)) by (apply Rmult_lt_0_compat; [lra | nra]).
  pose proof (Rabs_le_inv _ _ E) as [E1 _].
  assert (0 < B2R t - sin (B2R t)) by lra.
  nra.
Qed.

Print Assumptions sg_g_enclosure.
Print Assumptions sg_g_poly.
Print Assumptions sg_Qex_range.
Print Assumptions sg_alg.
Print Assumptions mf_seg_g_poly_rel.
Print Assumptions mf_seg_g_poly_pos.
