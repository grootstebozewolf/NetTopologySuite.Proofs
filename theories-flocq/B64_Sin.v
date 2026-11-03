(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Sin
   ----------------------------------------------------------------------------
   S2: a binary64 sine with a machine-checked absolute error bound.

     b64_sin_err : sin_accept x = true ->
                   is_finite (b64_sin x) = true /\
                   |B2R (b64_sin x) - sin (B2R x)| <= 2^-49   (16 u)

   Intake (`sin_accept`): finite and |x| <= 10 (covers the arc demand
   theta in [0, 2 pi] and the densification range |t| < 3 pi; inventory
   rows T2 / T5).  Everything outside is declined, not approximated.

   Algorithm (all RNE binary64, extractable):
     x < 0          sin x = -sin(-x)       (negation exact)
     k in {0..3}    by comparisons with dyadic thresholds 1609/1024,
                    603/128, 1005/128 (just above pi/2, 3pi/2, 5pi/2 - 1/1000)
     r = (x - k C1) - k C2                  C1 = pi to 50 bits, C2 = pi - C1 to
                    53 bits; k C1 is exact and x - k C1 is exact (Sterbenz)
     sin x = (-1)^k sin r,   sin r ~ r P(r^2)   (B64_SinPoly, degree 21)

   Budget (each a theorem; numbers in units of u = 2^-53):
     sn_core_err     |core(r) - sin r| <= ~10.9 u for |r| <= 8/5: final
                     product, Horner (b64_sinpoly_eval_err), argument
                     rounding z = fl(r r) through the Lipschitz bound,
                     coefficients (sp_coef_err), truncation (sp_trunc)
     sn_red_err      |r - (x - k pi)| <= ~1.6 u, PI pinned by sp_pi_bounds
   total ~12.6 u, stated as 2^-49 (rounded outward).
   claimId: s2-b64-sin.  witness: b64_sin_err.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core Sterbenz IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import LipInt.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  Constants.                                                             *)
(* -------------------------------------------------------------------------- *)

Definition sn_C1 : binary64 :=
  Binary.B754_finite prec emax false 7074237752028440 (-51) eq_refl.
Definition sn_C2 : binary64 :=
  Binary.B754_finite prec emax false 4967757600021511 (-105) eq_refl.
Definition sn_two_C1 : binary64 :=
  Binary.B754_finite prec emax false 7074237752028440 (-50) eq_refl.
Definition sn_three_C1 : binary64 :=
  Binary.B754_finite prec emax false 5305678314021330 (-49) eq_refl.
Definition sn_one : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition sn_two : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-51) eq_refl.
Definition sn_three : binary64 :=
  Binary.B754_finite prec emax false 6755399441055744 (-51) eq_refl.
Definition sn_T1 : binary64 :=
  Binary.B754_finite prec emax false 7076456836366336 (-52) eq_refl.
Definition sn_T3 : binary64 :=
  Binary.B754_finite prec emax false 5304044092391424 (-50) eq_refl.
Definition sn_T5 : binary64 :=
  Binary.B754_finite prec emax false 8840073487319040 (-50) eq_refl.
Definition sn_ten : binary64 :=
  Binary.B754_finite prec emax false 5629499534213120 (-49) eq_refl.
Definition sn_mten : binary64 :=
  Binary.B754_finite prec emax true 5629499534213120 (-49) eq_refl.

Lemma sn_C1_R : B2R sn_C1 = (884279719003555 / 281474976710656) /\ fin sn_C1 = true.
Proof. split; [|reflexivity]. unfold sn_C1. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.
Lemma sn_C2_R : B2R sn_C2 = (4967757600021511 / 40564819207303340847894502572032) /\ fin sn_C2 = true.
Proof. split; [|reflexivity]. unfold sn_C2. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.
Lemma sn_two_C1_R : B2R sn_two_C1 = (884279719003555 / 140737488355328) /\ fin sn_two_C1 = true.
Proof. split; [|reflexivity]. unfold sn_two_C1. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.
Lemma sn_three_C1_R : B2R sn_three_C1 = (2652839157010665 / 281474976710656) /\ fin sn_three_C1 = true.
Proof. split; [|reflexivity]. unfold sn_three_C1. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.
Lemma sn_one_R : B2R sn_one = 1 /\ fin sn_one = true.
Proof. split; [|reflexivity]. unfold sn_one. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.
Lemma sn_two_R : B2R sn_two = 2 /\ fin sn_two = true.
Proof. split; [|reflexivity]. unfold sn_two. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.
Lemma sn_three_R : B2R sn_three = 3 /\ fin sn_three = true.
Proof. split; [|reflexivity]. unfold sn_three. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.
Lemma sn_T1_R : B2R sn_T1 = (1609 / 1024) /\ fin sn_T1 = true.
Proof. split; [|reflexivity]. unfold sn_T1. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.
Lemma sn_T3_R : B2R sn_T3 = (603 / 128) /\ fin sn_T3 = true.
Proof. split; [|reflexivity]. unfold sn_T3. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.
Lemma sn_T5_R : B2R sn_T5 = (1005 / 128) /\ fin sn_T5 = true.
Proof. split; [|reflexivity]. unfold sn_T5. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.
Lemma sn_ten_R : B2R sn_ten = 10 /\ fin sn_ten = true.
Proof. split; [|reflexivity]. unfold sn_ten. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.
Lemma sn_mten_R : B2R sn_mten = -10 /\ fin sn_mten = true.
Proof. split; [|reflexivity]. unfold sn_mten. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.

Definition sn_c1 : R := (884279719003555 / 281474976710656).
Definition sn_c2 : R := (4967757600021511 / 40564819207303340847894502572032).

Lemma sn_pi_gap : Rabs (PI - (sn_c1 + sn_c2)) <= / 4611686018427387904.
Proof.
  pose proof sp_pi_bounds as [Hl Hh]. unfold sp_pi_lo, sp_pi_hi in *.
  unfold sn_c1, sn_c2. apply Rabs_le. split; lra.
Qed.

Lemma sn_pi_range : (206324479159212898448458737198403541543452221524575397105132418900897592 / 65675121478098948134211473850539027996520477148407130764892740641180475) <= PI <= (10880371204936608049807306858043012643607007771833878115320469157284 / 3463329719880765075895769332412541686258528563434431828555225472825).
Proof. exact sp_pi_bounds. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Exact negation.                                                        *)
(* -------------------------------------------------------------------------- *)

Definition sn_neg (s : binary64) : binary64 := b64_minus hz_zero s.

Lemma sn_neg_ok : forall s, fin s = true ->
  fin (sn_neg s) = true /\ B2R (sn_neg s) = - B2R s.
Proof.
  intros s Fs.
  assert (Hf : b64_format (- B2R s))
    by (apply generic_format_opp; apply b64_format_B2R).
  assert (E : b64_round (B2R hz_zero - B2R s) = - B2R s).
  { replace (B2R hz_zero - B2R s) with (- B2R s) by (cbn; ring).
    apply b64_round_generic. exact Hf. }
  assert (Hs : b64_safe Rminus hz_zero s).
  { split; [reflexivity|]. split; [exact Fs|].
    rewrite E, Rabs_Ropp. apply (Binary.abs_B2R_lt_emax prec emax). }
  destruct (b64_minus_correct _ _ Hs) as [HB HF].
  unfold sn_neg. split; [exact HF|]. rewrite HB, E. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The core: sin r ~ r * P(r^2) for |r| <= 8/5.                           *)
(* -------------------------------------------------------------------------- *)

Definition sn_core (r : binary64) : binary64 :=
  b64_mult r (b64_horner sp_coeffs (b64_mult r r)).

Definition sn_Ecore : R := (1429 / 1152921504606846976).

Lemma sn_core_budget : forall e, 0 < e <= / 9007199254740992 / 9007199254740992 ->
  / 9007199254740992 * (8 / 5 * (7 / 4 + / 2251799813685248)) + e
  + 8 / 5 * / 2251799813685248
  + 8 / 5 * (11 / 32 * (/ 9007199254740992 * (64 / 25) + e))
  + 8 / 5 * (11182133 / 302231454903657293676544)
  + (8 / 5) ^ 23 / 25852016738884976640000 <= sn_Ecore.
Proof.
  intros e He. unfold sn_Ecore.
  replace ((8 / 5) ^ 23) with (590295810358705651712 / 11920928955078125) by (cbn [pow]; field).
  lra.
Qed.

(* The core budget as pure real algebra (no binary64 terms in the lra). *)
Lemma sn_core_alg : forall (x zr pr sr Pz Pxx Exx e : R),
  0 < e <= / 9007199254740992 / 9007199254740992 -> Rabs x <= 8 / 5 ->
  Rabs (sr - x * pr) <= / 9007199254740992 * (8 / 5 * (7 / 4 + / 2251799813685248)) + e ->
  Rabs (pr - Pz) <= / 2251799813685248 ->
  Rabs (Pz - Pxx) <= 11 / 32 * Rabs (zr - x * x) ->
  Rabs (zr - x * x) <= / 9007199254740992 * (64 / 25) + e ->
  Rabs (Pxx - Exx) <= (11182133 / 302231454903657293676544) ->
  Rabs (x * Exx - sin x) <= (8 / 5) ^ 23 / 25852016738884976640000 ->
  Rabs (sr - sin x) <= sn_Ecore.
Proof.
  intros x zr pr sr Pz Pxx Exx e He Hx L1 Ep Lip Ez L4c L5.
  assert (L2 : Rabs (x * (pr - Pz)) <= 8 / 5 * / 2251799813685248)
    by (apply b64ae_abs_mult_le; assumption).
  assert (L3 : Rabs (x * (Pz - Pxx))
               <= 8 / 5 * (11 / 32 * (/ 9007199254740992 * (64 / 25) + e))).
  { apply b64ae_abs_mult_le; [exact Hx|].
    eapply Rle_trans; [exact Lip|]. apply Rmult_le_compat_l; [lra | exact Ez]. }
  assert (L4 : Rabs (x * (Pxx - Exx)) <= 8 / 5 * (11182133 / 302231454903657293676544))
    by (apply b64ae_abs_mult_le; assumption).
  pose proof (sn_core_budget e He) as Bud.
  replace (sr - sin x)
    with ((sr - x * pr) + x * (pr - Pz) + x * (Pz - Pxx)
          + x * (Pxx - Exx) + (x * Exx - sin x)) by ring.
  pose proof (Rabs_triang ((sr - x * pr) + x * (pr - Pz) + x * (Pz - Pxx)
                            + x * (Pxx - Exx)) (x * Exx - sin x)) as T1.
  pose proof (Rabs_triang ((sr - x * pr) + x * (pr - Pz) + x * (Pz - Pxx))
                          (x * (Pxx - Exx))) as T2.
  pose proof (Rabs_triang ((sr - x * pr) + x * (pr - Pz)) (x * (Pz - Pxx))) as T3.
  pose proof (Rabs_triang (sr - x * pr) (x * (pr - Pz))) as T4.
  lra.
Qed.

Lemma sn_core_err : forall r, fin r = true -> Rabs (B2R r) <= 8 / 5 ->
  fin (sn_core r) = true /\ Rabs (B2R (sn_core r) - sin (B2R r)) <= sn_Ecore.
Proof.
  intros r Fr Hr. unfold sn_core.
  pose proof b64ae_u_small as [Hu0 _]. pose proof sp_u_val as Uv.
  pose proof sp_e0_bounds as He. destruct He as [He0 He1].
  set (x := B2R r) in *.
  assert (Hb : 4 <= bpow radix2 1000) by exact sp_bpow1000.
  (* z = fl(r r) *)
  assert (Bz : Rabs (x * x) <= 8 / 5 * (8 / 5)) by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err r r Fr Fr ltac:(fold x; lra)) as [Fz Ez].
  fold x in Ez.
  pose proof (b64ae_u_mul_le _ _ Bz) as Uz.
  set (z := b64_mult r r) in *. clearbody z.
  assert (Ez' : Rabs (B2R z - x * x) <= / 9007199254740992 * (64 / 25) + b64ae_e0).
  { rewrite Uv in Uz, Ez. lra. }
  assert (Hz : Rabs (B2R z) <= 41 / 16).
  { replace (B2R z) with ((B2R z - x * x) + x * x) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  assert (Hxx : Rabs (x * x) <= 41 / 16) by lra.
  (* p = Horner(z) *)
  destruct (b64_sinpoly_eval_err z Fz Hz) as [Fp Ep].
  set (p := b64_horner sp_coeffs z) in *. clearbody p.
  replace (bpow radix2 (-51)) with (/ 2251799813685248) in Ep by (cbn; reflexivity).
  set (Pz := hz_horner_R (map B2R sp_coeffs) (B2R z)) in *.
  set (Pxx := hz_horner_R (map B2R sp_coeffs) (x * x)).
  set (Exx := hz_horner_R sp_exact (x * x)).
  assert (HPz : Rabs Pz <= 7 / 4).
  { eapply Rle_trans; [apply (hz_horner_R_bound sp_coeffs sp_ms (B2R z) sp_Z sp_coeffs_ok);
                        unfold sp_Z; exact Hz|].
    exact sp_M_bound. }
  assert (Hp : Rabs (B2R p) <= 7 / 4 + / 2251799813685248).
  { replace (B2R p) with ((B2R p - Pz) + Pz) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  (* s = fl(r p) *)
  assert (Bs : Rabs (x * B2R p) <= 8 / 5 * (7 / 4 + / 2251799813685248))
    by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err r p Fr Fp ltac:(fold x; lra)) as [Fs Es].
  fold x in Es.
  pose proof (b64ae_u_mul_le _ _ Bs) as Us.
  split; [exact Fs|].
  (* hand the facts to the pure-real budget *)
  apply (sn_core_alg x (B2R z) (B2R p) (B2R (b64_mult r p)) Pz Pxx Exx b64ae_e0
           (conj He0 He1) Hr).
  - rewrite Uv in Us, Es. lra.
  - exact Ep.
  - eapply Rle_trans;
      [apply (hz_horner_R_lip (map B2R sp_coeffs) sp_ms (B2R z) (x * x) sp_Z
                sp_coeffs_ok_R); unfold sp_Z; assumption|].
    apply Rmult_le_compat_r; [apply Rabs_pos | exact sp_L_bound].
  - exact Ez'.
  - apply sp_coef_err. exact Hxx.
  - apply sp_trunc. exact Hr.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Reduction r = (x - k C1) - k C2, k in 1..3.                            *)
(* -------------------------------------------------------------------------- *)

Definition sn_red (x kf : binary64) : binary64 :=
  b64_minus (b64_minus x (b64_mult kf sn_C1)) (b64_mult kf sn_C2).

Definition sn_Ered : R := (103 / 576460752303423488).

Lemma sn_red_budget : forall e, 0 < e <= / 9007199254740992 / 9007199254740992 ->
  (/ 9007199254740992 * (8 / 5) + e) + (/ 9007199254740992 * (3 * sn_c2) + e)
  + 3 * / 4611686018427387904 <= sn_Ered.
Proof. intros e He. unfold sn_Ered, sn_c2. lra. Qed.

Lemma sn_red_err : forall (x kf kc1 : binary64) (k : R),
  fin x = true -> fin kf = true -> B2R kf = k -> 1 <= k <= 3 ->
  B2R kc1 = k * sn_c1 ->
  B2R kc1 / 2 <= B2R x <= 2 * B2R kc1 ->
  Rabs (B2R x - k * PI) <= (15733 / 10000) ->
  fin (sn_red x kf) = true /\
  Rabs (B2R (sn_red x kf) - (B2R x - k * PI)) <= sn_Ered /\
  Rabs (B2R (sn_red x kf)) <= 8 / 5.
Proof.
  intros x kf kc1 k Fx Fk Ek Hk Ekc Hst Hr. unfold sn_red.
  destruct sn_C1_R as [EC1 FC1]. destruct sn_C2_R as [EC2 FC2].
  pose proof b64ae_u_small as [Hu0 _]. pose proof sp_u_val as Uv.
  pose proof sp_e0_bounds as [He0 He1].
  pose proof sn_pi_gap as Gap. pose proof sn_pi_range as [Pl Ph].
  fold sn_c2 in EC2. fold sn_c1 in EC1.
  assert (Hc1 : sn_c1 = (884279719003555 / 281474976710656)) by reflexivity.
  assert (Hc2 : sn_c2 = (4967757600021511 / 40564819207303340847894502572032)) by reflexivity.
  (* t1 = fl(k C1) = k C1 exactly *)
  assert (Et1r : b64_round (B2R kf * B2R sn_C1) = B2R kc1).
  { rewrite Ek, EC1, <- Ekc. apply b64_round_generic. apply b64_format_B2R. }
  assert (St1 : b64_safe Rmult kf sn_C1).
  { split; [exact Fk|]. split; [exact FC1|]. rewrite Et1r.
    apply (Binary.abs_B2R_lt_emax prec emax). }
  destruct (b64_mult_correct _ _ St1) as [Et1 Ft1]. rewrite Et1r in Et1.
  set (t1 := b64_mult kf sn_C1) in *.
  (* r1 = x - t1 exactly (Sterbenz) *)
  assert (Fmt : b64_format (B2R x - B2R kc1)).
  { apply (sterbenz radix2 (SpecFloat.fexp prec emax));
      [apply b64_format_B2R | apply b64_format_B2R | exact Hst]. }
  assert (Er1r : b64_round (B2R x - B2R t1) = B2R x - B2R kc1).
  { rewrite Et1. apply b64_round_generic. exact Fmt. }
  assert (Hr1 : Rabs (B2R x - B2R kc1) <= (15733 / 10000) + 3 * / 1000000000000000).
  { rewrite Ekc. replace (B2R x - k * sn_c1) with ((B2R x - k * PI) + k * (PI - sn_c1)) by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    assert (Rabs (k * (PI - sn_c1)) <= 3 * / 1000000000000000).
    { rewrite Rabs_mult, Rabs_pos_eq by lra.
      assert (Rabs (PI - sn_c1) <= / 1000000000000000)
        by (rewrite Hc1; apply Rabs_le; split; lra).
      apply Rmult_le_compat; try lra; apply Rabs_pos. }
    lra. }
  assert (Sr1 : b64_safe Rminus x t1).
  { split; [exact Fx|]. split; [exact Ft1|]. rewrite Er1r.
    apply Rle_lt_trans with 2; [lra|].
    apply Rle_lt_trans with (bpow radix2 2); [cbn; lra | apply bpow_lt; unfold emax; lia]. }
  destruct (b64_minus_correct _ _ Sr1) as [Er1 Fr1]. rewrite Er1r in Er1.
  set (r1 := b64_minus x t1) in *.
  (* t2 = fl(k C2) *)
  assert (Bt2 : Rabs (B2R kf * B2R sn_C2) <= 3 * sn_c2).
  { rewrite Ek, EC2, Rabs_mult, (Rabs_pos_eq k), (Rabs_pos_eq sn_c2) by (rewrite ?Hc2; lra).
    apply Rmult_le_compat_r; [rewrite Hc2; lra | lra]. }
  destruct (b64ae_mult_err kf sn_C2 Fk FC2
              ltac:(eapply Rle_trans; [exact Bt2|]; rewrite Hc2;
                    apply Rle_trans with 1; [lra|];
                    apply Rle_trans with (bpow radix2 0); [cbn; lra | apply bpow_le; lia]))
    as [Ft2 Et2].
  pose proof (b64ae_u_mul_le _ _ Bt2) as Ut2.
  set (t2 := b64_mult kf sn_C2) in *.
  clearbody r1. clearbody t2. clearbody t1.
  (* r = fl(r1 - t2) *)
  assert (Ht2 : Rabs (B2R t2) <= / 1000000000000000).
  { replace (B2R t2) with ((B2R t2 - B2R kf * B2R sn_C2) + B2R kf * B2R sn_C2) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. rewrite Uv in Ut2, Et2. rewrite Hc2 in Bt2, Ut2. lra. }
  assert (B3 : Rabs (B2R r1 - B2R t2) <= 8 / 5).
  { rewrite Er1. eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. lra. }
  destruct (b64ae_minus_err r1 t2 Fr1 Ft2
              ltac:(eapply Rle_trans; [exact B3|];
                    apply Rle_trans with 4; [lra | exact sp_bpow1000])) as [Fr Er].
  pose proof (b64ae_u_mul_le _ _ B3) as U3.
  split; [exact Fr|].
  assert (Hred : Rabs (B2R (b64_minus r1 t2) - (B2R x - k * PI)) <= sn_Ered).
  { pose proof (sn_red_budget b64ae_e0 (conj He0 He1)) as Bud.
    replace (B2R (b64_minus r1 t2) - (B2R x - k * PI))
      with ((B2R (b64_minus r1 t2) - (B2R r1 - B2R t2))
            + (B2R kf * B2R sn_C2 - B2R t2) + k * (PI - (sn_c1 + sn_c2)))
      by (rewrite Er1, Ek, EC2, Ekc; ring).
    pose proof (Rabs_triang ((B2R (b64_minus r1 t2) - (B2R r1 - B2R t2))
                             + (B2R kf * B2R sn_C2 - B2R t2)) (k * (PI - (sn_c1 + sn_c2)))) as T1.
    pose proof (Rabs_triang (B2R (b64_minus r1 t2) - (B2R r1 - B2R t2))
                            (B2R kf * B2R sn_C2 - B2R t2)) as T2.
    assert (G : Rabs (k * (PI - (sn_c1 + sn_c2))) <= 3 * / 4611686018427387904).
    { rewrite Rabs_mult, (Rabs_pos_eq k) by lra.
      apply Rmult_le_compat; try lra; apply Rabs_pos. }
    rewrite <- Rabs_Ropp in Et2. rewrite Ropp_minus_distr in Et2.
    rewrite Uv in U3, Ut2, Er, Et2.
    clear - T1 T2 G Er Et2 U3 Ut2 Bud.
    lra. }
  split; [exact Hred|].
  replace (B2R (b64_minus r1 t2))
    with ((B2R (b64_minus r1 t2) - (B2R x - k * PI)) + (B2R x - k * PI)) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  unfold sn_Ered in Hred. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Assembly.                                                              *)
(* -------------------------------------------------------------------------- *)

Definition sn_pos (x : binary64) : binary64 :=
  if b64_le x sn_T1 then sn_core x
  else if b64_le x sn_T3 then sn_neg (sn_core (sn_red x sn_one))
  else if b64_le x sn_T5 then sn_core (sn_red x sn_two)
  else sn_neg (sn_core (sn_red x sn_three)).

Definition b64_sin (x : binary64) : binary64 :=
  if b64_le hz_zero x then sn_pos x else sn_neg (sn_pos (sn_neg x)).

Definition sin_accept (x : binary64) : bool :=
  Binary.is_finite prec emax x && b64_le sn_mten x && b64_le x sn_ten.

Lemma sn_sin_shift1 : forall y, sin (y - 1 * PI) = - sin y.
Proof. intro y. rewrite Rmult_1_l, sin_minus, sin_PI, cos_PI. ring. Qed.

Lemma sn_sin_shift2 : forall y, sin (y - 2 * PI) = sin y.
Proof. intro y. rewrite sin_minus, sin_2PI, cos_2PI. ring. Qed.

Lemma sn_sin_shift3 : forall y, sin (y - 3 * PI) = - sin y.
Proof.
  intro y. replace (y - 3 * PI) with ((y - 2 * PI) - 1 * PI) by ring.
  rewrite sn_sin_shift1, sn_sin_shift2. reflexivity.
Qed.

(* One reduced branch: (-1)^k core(r) against sin x. *)
Lemma sn_branch : forall (x kf kc1 : binary64) (k sg : R),
  fin x = true -> fin kf = true -> B2R kf = k -> 1 <= k <= 3 ->
  B2R kc1 = k * sn_c1 ->
  B2R kc1 / 2 <= B2R x <= 2 * B2R kc1 ->
  Rabs (B2R x - k * PI) <= (15733 / 10000) ->
  (sg = 1 \/ sg = -1) -> sin (B2R x - k * PI) = sg * sin (B2R x) ->
  fin (sn_core (sn_red x kf)) = true /\
  Rabs (sg * B2R (sn_core (sn_red x kf)) - sin (B2R x)) <= sn_Ecore + sn_Ered.
Proof.
  intros x kf kc1 k sg Fx Fk Ek Hk Ekc Hst Hr Hsg Hsin.
  destruct (sn_red_err x kf kc1 k Fx Fk Ek Hk Ekc Hst Hr) as [Fr [Er Br]].
  destruct (sn_core_err _ Fr Br) as [Fc Ec].
  split; [exact Fc|].
  set (c := B2R (sn_core (sn_red x kf))) in *.
  set (r := B2R (sn_red x kf)) in *.
  assert (Ls := sin_lip r (B2R x - k * PI)).
  assert (E : sg * c - sin (B2R x) = sg * ((c - sin r) + (sin r - sin (B2R x - k * PI)))).
  { rewrite Hsin. destruct Hsg as [-> | ->]; ring. }
  rewrite E, Rabs_mult.
  assert (Hs : Rabs sg = 1) by (destruct Hsg as [-> | ->]; [apply Rabs_R1 | rewrite Rabs_Ropp; apply Rabs_R1]).
  rewrite Hs, Rmult_1_l.
  eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

Lemma sn_Etot : sn_Ecore + sn_Ered <= bpow radix2 (-49).
Proof.
  replace (bpow radix2 (-49)) with (/ 562949953421312) by (cbn; reflexivity).
  unfold sn_Ecore, sn_Ered. lra.
Qed.

Lemma sn_pos_err : forall x, fin x = true -> 0 <= B2R x <= 10 ->
  fin (sn_pos x) = true /\ Rabs (B2R (sn_pos x) - sin (B2R x)) <= sn_Ecore + sn_Ered.
Proof.
  intros x Fx Hx.
  destruct sn_T1_R as [ET1 FT1]. destruct sn_T3_R as [ET3 FT3]. destruct sn_T5_R as [ET5 FT5].
  destruct sn_one_R as [E1 F1]. destruct sn_two_R as [E2 F2]. destruct sn_three_R as [E3 F3].
  destruct sn_C1_R as [EC1 FC1]. destruct sn_two_C1_R as [E2C F2C]. destruct sn_three_C1_R as [E3C F3C].
  pose proof sn_pi_range as [Pl Ph].
  assert (Hred_pos : 0 <= sn_Ered) by (unfold sn_Ered; lra).
  unfold sn_pos.
  destruct (b64_le x sn_T1) eqn:L1.
  - apply b64ae_le_true in L1; [|exact Fx|exact FT1]. rewrite ET1 in L1.
    destruct (sn_core_err x Fx ltac:(rewrite Rabs_pos_eq by lra; lra)) as [Fc Ec].
    split; [exact Fc|]. lra.
  - apply b64ae_le_false in L1; [|exact Fx|exact FT1]. rewrite ET1 in L1.
    destruct (b64_le x sn_T3) eqn:L3.
    + apply b64ae_le_true in L3; [|exact Fx|exact FT3]. rewrite ET3 in L3.
      destruct (sn_branch x sn_one sn_C1 1 (-1) Fx F1 E1 ltac:(lra)
                  ltac:(rewrite EC1; unfold sn_c1; ring)
                  ltac:(rewrite EC1; split; lra)
                  ltac:(apply Rabs_le; split; lra)
                  ltac:(right; reflexivity)
                  ltac:(rewrite sn_sin_shift1; ring)) as [Fc Ec].
      destruct (sn_neg_ok _ Fc) as [Fn En].
      split; [exact Fn|]. rewrite En.
      replace (- B2R (sn_core (sn_red x sn_one))) with (-1 * B2R (sn_core (sn_red x sn_one))) by ring.
      exact Ec.
    + apply b64ae_le_false in L3; [|exact Fx|exact FT3]. rewrite ET3 in L3.
      destruct (b64_le x sn_T5) eqn:L5.
      * apply b64ae_le_true in L5; [|exact Fx|exact FT5]. rewrite ET5 in L5.
        destruct (sn_branch x sn_two sn_two_C1 2 1 Fx F2 E2 ltac:(lra)
                    ltac:(rewrite E2C; unfold sn_c1; ring)
                    ltac:(rewrite E2C; split; lra)
                    ltac:(apply Rabs_le; split; lra)
                    ltac:(left; reflexivity)
                    ltac:(rewrite sn_sin_shift2; ring)) as [Fc Ec].
        split; [exact Fc|]. rewrite <- (Rmult_1_l (B2R (sn_core (sn_red x sn_two)))). exact Ec.
      * apply b64ae_le_false in L5; [|exact Fx|exact FT5]. rewrite ET5 in L5.
        destruct (sn_branch x sn_three sn_three_C1 3 (-1) Fx F3 E3 ltac:(lra)
                    ltac:(rewrite E3C; unfold sn_c1; ring)
                    ltac:(rewrite E3C; split; lra)
                    ltac:(apply Rabs_le; split; lra)
                    ltac:(right; reflexivity)
                    ltac:(rewrite sn_sin_shift3; ring)) as [Fc Ec].
        destruct (sn_neg_ok _ Fc) as [Fn En].
        split; [exact Fn|]. rewrite En.
        replace (- B2R (sn_core (sn_red x sn_three))) with (-1 * B2R (sn_core (sn_red x sn_three))) by ring.
        exact Ec.
Qed.

(* WITNESS {"claimId":"s2-b64-sin","topic":"numerics","lemma":"b64_sin_err","title":"Binary64 sine: for every finite input with |x| <= 10 (sin_accept), the RNE evaluator b64_sin (mod-pi Sterbenz reduction, degree-21 Horner) is finite and within 2^-49 of sin x","file":"theories-flocq/B64_Sin.v","witness":"b64_sin_err","board":"ADR-0006"} *)
Theorem b64_sin_err : forall x, sin_accept x = true ->
  fin (b64_sin x) = true /\ Rabs (B2R (b64_sin x) - sin (B2R x)) <= bpow radix2 (-49).
Proof.
  intros x Hacc. unfold sin_accept in Hacc.
  apply andb_prop in Hacc as [Hacc Hhi]. apply andb_prop in Hacc as [Fx Hlo].
  destruct sn_ten_R as [Et Ft]. destruct sn_mten_R as [Em Fm].
  apply b64ae_le_true in Hlo; [|exact Fm|exact Fx]. apply b64ae_le_true in Hhi; [|exact Fx|exact Ft].
  rewrite Em in Hlo. rewrite Et in Hhi.
  pose proof sn_Etot as Tot.
  unfold b64_sin.
  destruct (b64_le hz_zero x) eqn:Z0.
  - apply b64ae_le_true in Z0; [|reflexivity|exact Fx].
    replace (B2R hz_zero) with 0 in Z0 by reflexivity.
    destruct (sn_pos_err x Fx ltac:(split; lra)) as [F E].
    split; [exact F | lra].
  - apply b64ae_le_false in Z0; [|reflexivity|exact Fx].
    replace (B2R hz_zero) with 0 in Z0 by reflexivity.
    destruct (sn_neg_ok x Fx) as [Fy Ey].
    destruct (sn_pos_err (sn_neg x) Fy ltac:(rewrite Ey; split; lra)) as [Fp Ep].
    destruct (sn_neg_ok _ Fp) as [Fn En].
    split; [exact Fn|]. rewrite En, Ey in *. rewrite sin_neg in Ep.
    replace (- B2R (sn_pos (sn_neg x)) - sin (B2R x))
      with (- (B2R (sn_pos (sn_neg x)) - - sin (B2R x))) by ring.
    rewrite Rabs_Ropp. lra.
Qed.

Print Assumptions sn_neg_ok.
Print Assumptions sn_core_err.
Print Assumptions sn_red_err.
Print Assumptions sn_pos_err.
Print Assumptions b64_sin_err.

