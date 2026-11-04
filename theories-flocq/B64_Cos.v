(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Cos
   ----------------------------------------------------------------------------
   S4: a binary64 cosine with a machine-checked absolute error bound, built
   by reuse of the S2 sine (claimId: s4-b64-cos, witness: b64_cos_err).

     b64_cos_err : sin_accept x = true ->
                   is_finite (b64_cos x) = true /\
                   |B2R (b64_cos x) - cos (B2R x)| <= 2^-49   (16 u)

   Reused unchanged from B64_Sin: the intake (sin_accept / sin_accept_b,
   |x| <= 10), the exact negation sn_neg, the thresholds and the Sterbenz
   reduction sn_red with its theorem sn_red_err, the argument square
   sn_z_facts.  New: the degree-22 polynomial (B64_CosPoly) and the parity
   bookkeeping, cos (x - k pi) = (-1)^k cos x and cos (-x) = cos x.

   Budget (units of u = 2^-53):
     cs_core_err   |core(r) - cos r| <= ~10.48 u for |r| <= 8/5:
                   Horner (b64_cospoly_eval_err, 8 u), argument rounding
                   through the Lipschitz bound 7/8, coefficients
                   (cq_coef_err), truncation (cq_trunc)
     sn_red_err    reduction, as for sine (~1.61 u)
   total ~12.09 u, stated as 2^-49 (rounded outward).
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import LipInt.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly B64_Sin B64_CosPoly.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  The core: cos r ~ Q(r^2) for |r| <= 8/5.                               *)
(* -------------------------------------------------------------------------- *)

Definition cs_core (r : binary64) : binary64 :=
  b64_horner cq_coeffs (b64_mult r r).

Definition cs_Ecore : R := (671 / 576460752303423488).

(* The core budget as pure real algebra. *)
Lemma cs_core_alg : forall (x zr pr Pz Pxx Exx e : R),
  0 < e <= / 9007199254740992 / 9007199254740992 ->
  Rabs (pr - Pz) <= / 1125899906842624 ->
  Rabs (Pz - Pxx) <= 7 / 8 * Rabs (zr - x * x) ->
  Rabs (zr - x * x) <= / 9007199254740992 * (64 / 25) + e ->
  Rabs (Pxx - Exx) <= (28649227 / 1208925819614629174706176) ->
  Rabs (Exx - cos x) <= (8 / 5) ^ 24 / 25852016738884976640000 ->
  Rabs (pr - cos x) <= cs_Ecore.
Proof.
  intros x zr pr Pz Pxx Exx e He Ep Lip Ez Ec Et.
  replace ((8 / 5) ^ 24 / 25852016738884976640000) with (9007199254740992 / 2939034031770117580890655517578125) in Et by (cbn [pow]; field).
  replace (pr - cos x) with ((pr - Pz) + (Pz - Pxx) + (Pxx - Exx) + (Exx - cos x)) by ring.
  pose proof (Rabs_triang ((pr - Pz) + (Pz - Pxx) + (Pxx - Exx)) (Exx - cos x)) as T1.
  pose proof (Rabs_triang ((pr - Pz) + (Pz - Pxx)) (Pxx - Exx)) as T2.
  pose proof (Rabs_triang (pr - Pz) (Pz - Pxx)) as T3.
  unfold cs_Ecore. lra.
Qed.

Lemma cs_P_lip : forall y w, Rabs y <= 41 / 16 -> Rabs w <= 41 / 16 ->
  Rabs (hz_horner_R (map B2R cq_coeffs) y - hz_horner_R (map B2R cq_coeffs) w)
    <= 7 / 8 * Rabs (y - w).
Proof.
  intros y w Hy Hw.
  eapply Rle_trans;
    [apply (hz_horner_R_lip (map B2R cq_coeffs) cq_ms y w sp_Z cq_coeffs_ok_R);
     unfold sp_Z; assumption|].
  apply Rmult_le_compat_r; [apply Rabs_pos | exact cq_L_bound].
Qed.

Lemma cs_core_err : forall r, fin r = true -> Rabs (B2R r) <= 8 / 5 ->
  fin (cs_core r) = true /\ Rabs (B2R (cs_core r) - cos (B2R r)) <= cs_Ecore.
Proof.
  intros r Fr Hr. unfold cs_core.
  pose proof sp_e0_bounds as [He0 He1].
  destruct (sn_z_facts r Fr Hr) as [Fz [Ez Hz]].
  destruct (b64_cospoly_eval_err _ Fz Hz) as [Fp Ep].
  replace (bpow radix2 (-50)) with (/ 1125899906842624) in Ep by (cbn; reflexivity).
  assert (Hxx : Rabs (B2R r * B2R r) <= 41 / 16).
  { assert (Rabs (B2R r * B2R r) <= 8 / 5 * (8 / 5)) by (apply b64ae_abs_mult_le; assumption).
    lra. }
  split; [exact Fp|].
  exact (cs_core_alg (B2R r) (B2R (b64_mult r r)) (B2R (b64_horner cq_coeffs (b64_mult r r)))
           (hz_horner_R (map B2R cq_coeffs) (B2R (b64_mult r r)))
           (hz_horner_R (map B2R cq_coeffs) (B2R r * B2R r))
           (hz_horner_R cq_exact (B2R r * B2R r)) b64ae_e0
           (conj He0 He1) Ep (cs_P_lip _ _ Hz Hxx) Ez
           (cq_coef_err _ Hxx) (cq_trunc _ Hr)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Assembly (reduction and intake from B64_Sin).                          *)
(* -------------------------------------------------------------------------- *)

Definition cs_pos (x : binary64) : binary64 :=
  if b64_le x sn_T1 then cs_core x
  else if b64_le x sn_T3 then sn_neg (cs_core (sn_red x sn_one))
  else if b64_le x sn_T5 then cs_core (sn_red x sn_two)
  else sn_neg (cs_core (sn_red x sn_three)).

Definition b64_cos (x : binary64) : binary64 :=
  if b64_le hz_zero x then cs_pos x else cs_pos (sn_neg x).

Lemma cs_cos_shift1 : forall y, cos (y - 1 * PI) = - cos y.
Proof. intro y. rewrite Rmult_1_l, cos_minus, sin_PI, cos_PI. ring. Qed.

Lemma cs_cos_shift2 : forall y, cos (y - 2 * PI) = cos y.
Proof. intro y. rewrite cos_minus, sin_2PI, cos_2PI. ring. Qed.

Lemma cs_cos_shift3 : forall y, cos (y - 3 * PI) = - cos y.
Proof.
  intro y. replace (y - 3 * PI) with ((y - 2 * PI) - 1 * PI) by ring.
  rewrite cs_cos_shift1, cs_cos_shift2. reflexivity.
Qed.

(* Sign bookkeeping of a branch, as pure real algebra. *)
Lemma cs_sg_alg : forall sg c cr cx cxk A B,
  (sg = 1 \/ sg = -1) -> cxk = sg * cx ->
  Rabs (c - cr) <= A -> Rabs (cr - cxk) <= B ->
  Rabs (sg * c - cx) <= A + B.
Proof.
  intros sg c cr cx cxk A B Hsg E H1 H2. subst cxk.
  replace (sg * c - cx) with (sg * ((c - cr) + (cr - sg * cx)))
    by (destruct Hsg as [-> | ->]; ring).
  rewrite Rabs_mult.
  assert (Ha : Rabs sg = 1) by (destruct Hsg as [-> | ->]; [apply Rabs_R1 | rewrite Rabs_left by lra; ring]).
  rewrite Ha, Rmult_1_l.
  eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

(* One reduced branch: (-1)^k core(r) against cos x. *)
Lemma cs_branch : forall (x kf kc1 : binary64) (k sg : R),
  fin x = true -> fin kf = true -> B2R kf = k -> 1 <= k <= 3 ->
  B2R kc1 = k * sn_c1 ->
  B2R kc1 / 2 <= B2R x <= 2 * B2R kc1 ->
  Rabs (B2R x - k * PI) <= (15733 / 10000) ->
  (sg = 1 \/ sg = -1) -> cos (B2R x - k * PI) = sg * cos (B2R x) ->
  fin (cs_core (sn_red x kf)) = true /\
  Rabs (sg * B2R (cs_core (sn_red x kf)) - cos (B2R x)) <= cs_Ecore + sn_Ered.
Proof.
  intros x kf kc1 k sg Fx Fk Ek Hk Ekc Hst Hr Hsg Hcos.
  destruct (sn_red_err x kf kc1 k Fx Fk Ek Hk Ekc Hst Hr) as [Fr [Er Br]].
  destruct (cs_core_err _ Fr Br) as [Fc Ec].
  split; [exact Fc|].
  exact (cs_sg_alg sg _ _ _ _ _ _ Hsg Hcos Ec
           (Rle_trans _ _ _ (cos_lip (B2R (sn_red x kf)) (B2R x - k * PI)) Er)).
Qed.

Lemma cs_Etot : cs_Ecore + sn_Ered <= bpow radix2 (-49).
Proof.
  replace (bpow radix2 (-49)) with (/ 562949953421312) by (cbn; reflexivity).
  unfold cs_Ecore, sn_Ered. lra.
Qed.

Lemma cs_pos_err : forall x, fin x = true -> 0 <= B2R x <= 10 ->
  fin (cs_pos x) = true /\ Rabs (B2R (cs_pos x) - cos (B2R x)) <= cs_Ecore + sn_Ered.
Proof.
  intros x Fx Hx.
  destruct sn_T1_R as [ET1 FT1]. destruct sn_T3_R as [ET3 FT3]. destruct sn_T5_R as [ET5 FT5].
  destruct sn_one_R as [E1 F1]. destruct sn_two_R as [E2 F2]. destruct sn_three_R as [E3 F3].
  destruct sn_C1_R as [EC1 FC1]. destruct sn_two_C1_R as [E2C F2C]. destruct sn_three_C1_R as [E3C F3C].
  pose proof sn_pi_range as [Pl Ph].
  assert (Hred_pos : 0 <= sn_Ered) by (unfold sn_Ered; lra).
  unfold cs_pos.
  destruct (b64_le x sn_T1) eqn:L1.
  - apply b64ae_le_true in L1; [|exact Fx|exact FT1]. rewrite ET1 in L1.
    destruct (cs_core_err x Fx ltac:(rewrite Rabs_pos_eq by lra; lra)) as [Fc Ec].
    split; [exact Fc|]. lra.
  - apply b64ae_le_false in L1; [|exact Fx|exact FT1]. rewrite ET1 in L1.
    destruct (b64_le x sn_T3) eqn:L3.
    + apply b64ae_le_true in L3; [|exact Fx|exact FT3]. rewrite ET3 in L3.
      destruct (cs_branch x sn_one sn_C1 1 (-1) Fx F1 E1 ltac:(lra)
                  ltac:(rewrite EC1; unfold sn_c1; lra)
                  ltac:(rewrite EC1; split; lra)
                  ltac:(apply Rabs_le; split; lra)
                  ltac:(right; reflexivity)
                  ltac:(rewrite cs_cos_shift1; ring)) as [Fc Ec].
      destruct (sn_neg_ok _ Fc) as [Fn En].
      split; [exact Fn|]. rewrite En.
      revert Ec. generalize (B2R (cs_core (sn_red x sn_one))). intros c Ec.
      replace (- c) with (-1 * c) by ring. exact Ec.
    + apply b64ae_le_false in L3; [|exact Fx|exact FT3]. rewrite ET3 in L3.
      destruct (b64_le x sn_T5) eqn:L5.
      * apply b64ae_le_true in L5; [|exact Fx|exact FT5]. rewrite ET5 in L5.
        destruct (cs_branch x sn_two sn_two_C1 2 1 Fx F2 E2 ltac:(lra)
                    ltac:(rewrite E2C; unfold sn_c1; lra)
                    ltac:(rewrite E2C; split; lra)
                    ltac:(apply Rabs_le; split; lra)
                    ltac:(left; reflexivity)
                    ltac:(rewrite cs_cos_shift2; ring)) as [Fc Ec].
        split; [exact Fc|]. revert Ec. generalize (B2R (cs_core (sn_red x sn_two))). intros c Ec.
        rewrite Rmult_1_l in Ec. exact Ec.
      * apply b64ae_le_false in L5; [|exact Fx|exact FT5]. rewrite ET5 in L5.
        destruct (cs_branch x sn_three sn_three_C1 3 (-1) Fx F3 E3 ltac:(lra)
                    ltac:(rewrite E3C; unfold sn_c1; lra)
                    ltac:(rewrite E3C; split; lra)
                    ltac:(apply Rabs_le; split; lra)
                    ltac:(right; reflexivity)
                    ltac:(rewrite cs_cos_shift3; ring)) as [Fc Ec].
        destruct (sn_neg_ok _ Fc) as [Fn En].
        split; [exact Fn|]. rewrite En.
        revert Ec. generalize (B2R (cs_core (sn_red x sn_three))). intros c Ec.
        replace (- c) with (-1 * c) by ring. exact Ec.
Qed.

(* WITNESS {"claimId":"s4-b64-cos","topic":"numerics","lemma":"b64_cos_err","title":"Binary64 cosine by reuse of the S2 sine reduction and intake: for every finite input with |x| <= 10 (sin_accept), the RNE evaluator b64_cos (mod-pi Sterbenz reduction, degree-22 Horner) is finite and within 2^-49 of cos x","file":"theories-flocq/B64_Cos.v","witness":"b64_cos_err","board":"ADR-0006"} *)
Theorem b64_cos_err : forall x, sin_accept x = true ->
  fin (b64_cos x) = true /\ Rabs (B2R (b64_cos x) - cos (B2R x)) <= bpow radix2 (-49).
Proof.
  intros x Hacc. unfold sin_accept in Hacc.
  apply andb_prop in Hacc as [Hacc Hhi]. apply andb_prop in Hacc as [Fx Hlo].
  destruct sn_ten_R as [Et Ft]. destruct sn_mten_R as [Em Fm].
  apply b64ae_le_true in Hlo; [|exact Fm|exact Fx]. apply b64ae_le_true in Hhi; [|exact Fx|exact Ft].
  rewrite Em in Hlo. rewrite Et in Hhi.
  pose proof cs_Etot as Tot.
  unfold b64_cos.
  destruct (b64_le hz_zero x) eqn:Z0.
  - apply b64ae_le_true in Z0; [|reflexivity|exact Fx].
    replace (B2R hz_zero) with 0 in Z0 by reflexivity.
    destruct (cs_pos_err x Fx ltac:(split; lra)) as [F E].
    split; [exact F | lra].
  - apply b64ae_le_false in Z0; [|reflexivity|exact Fx].
    replace (B2R hz_zero) with 0 in Z0 by reflexivity.
    destruct (sn_neg_ok x Fx) as [Fy Ey].
    destruct (cs_pos_err (sn_neg x) Fy ltac:(rewrite Ey; split; lra)) as [Fp Ep].
    split; [exact Fp|]. rewrite Ey, cos_neg in Ep. lra.
Qed.

Corollary b64_cos_err_b : forall x, sin_accept_b x = true ->
  fin (b64_cos x) = true /\ Rabs (B2R (b64_cos x) - cos (B2R x)) <= bpow radix2 (-49).
Proof. intros x H. rewrite sin_accept_b_eq in H. exact (b64_cos_err x H). Qed.

Print Assumptions cs_core_alg.
Print Assumptions cs_core_err.
Print Assumptions cs_pos_err.
Print Assumptions b64_cos_err.
Print Assumptions b64_cos_err_b.

