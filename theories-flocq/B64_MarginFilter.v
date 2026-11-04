(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_MarginFilter
   ----------------------------------------------------------------------------
   S9: margin-filtered predicates (claimId: s9-margin-filter, witness:
   compute_decides_sound).

   A consumer gets a three-state answer, not a float to compare carefully:
     mf_decide v thr = MF_POSITIVE   if  thr < v
                       MF_NEGATIVE   if  v < -thr
                       MF_UNDECIDED  otherwise (and on NaN)
   for a computed v with a certified bound |v - spec| <= E.

     compute_decides_sound     E <= thr: POSITIVE -> 0 < v - thr <= spec,
                               NEGATIVE -> spec <= v + thr < 0
     compute_decides_complete  spec > thr + E -> POSITIVE,
                               spec < -(thr + E) -> NEGATIVE  (the exact
                               separation; the "2E" rule is only the
                               corollary thr = E, compute_decides_complete_2E)
     compute_undecided_bound   UNDECIDED -> |spec| <= thr + E

   Fallback policy is per consumer (mf_policy), not global:
     outside the evaluator intake        -> MO_Decline
     UNDECIDED, exact implementation     -> MO_Exact (run the exact path)
     UNDECIDED, no exact implementation  -> MO_Decline
   mf_policy_sound: a signed outcome is always a certified sign.

   First consumer (inventory T3): ARC_AREA_CENTROID divides by
   g = theta - sin theta.  mf_seg_g theta = fl(theta - b64_sin theta) is
   within 2^-48 of g (b64_seg_g_err); a POSITIVE decision certifies the
   denominator lower bound g >= v - 2^-48 > 0 (b64_seg_g_positive_lb), and
   g > 2^-47 forces POSITIVE (b64_seg_g_complete).  No exact path exists for
   a transcendental g, so that consumer's policy is MF_DeclineFallback.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly B64_Sin.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  The three-state decision.                                              *)
(* -------------------------------------------------------------------------- *)

Inductive mf_sign : Type := MF_POSITIVE | MF_NEGATIVE | MF_UNDECIDED.

(* strict <, false whenever either side is NaN *)
Definition mf_lt (x y : binary64) : bool := (b64_le x y && negb (b64_le y x))%bool.

Lemma mf_lt_true : forall x y, fin x = true -> fin y = true ->
  mf_lt x y = true -> B2R x < B2R y.
Proof.
  intros x y Fx Fy H. unfold mf_lt in H. apply andb_prop in H as [_ H2].
  apply negb_true_iff in H2. exact (b64ae_le_false _ _ Fy Fx H2).
Qed.

Lemma mf_lt_false : forall x y, fin x = true -> fin y = true ->
  mf_lt x y = false -> B2R y <= B2R x.
Proof.
  intros x y Fx Fy H. unfold mf_lt in H.
  destruct (b64_le x y) eqn:E1; destruct (b64_le y x) eqn:E2; cbn in H; try discriminate H.
  - exact (b64ae_le_true _ _ Fy Fx E2).
  - left. exact (b64ae_le_false _ _ Fx Fy E1).
  - left. exact (b64ae_le_false _ _ Fx Fy E1).
Qed.

Definition mf_decide (v thr : binary64) : mf_sign :=
  if mf_lt thr v then MF_POSITIVE
  else if mf_lt v (sn_neg thr) then MF_NEGATIVE
  else MF_UNDECIDED.

Lemma mf_decide_cases : forall v thr, fin v = true -> fin thr = true ->
  (mf_decide v thr = MF_POSITIVE -> B2R thr < B2R v) /\
  (mf_decide v thr = MF_NEGATIVE -> B2R v <= B2R thr /\ B2R v < - B2R thr) /\
  (mf_decide v thr = MF_UNDECIDED -> - B2R thr <= B2R v <= B2R thr).
Proof.
  intros v thr Fv Ft.
  destruct (sn_neg_ok thr Ft) as [Fn En].
  unfold mf_decide.
  destruct (mf_lt thr v) eqn:L1.
  - apply mf_lt_true in L1; [|exact Ft|exact Fv].
    split; [intros _; exact L1|]. split; intro H; discriminate H.
  - apply mf_lt_false in L1; [|exact Ft|exact Fv].
    destruct (mf_lt v (sn_neg thr)) eqn:L2.
    + apply mf_lt_true in L2; [|exact Fv|exact Fn]. rewrite En in L2.
      split; [intro H; discriminate H|]. split; [intros _; split; assumption | intro H; discriminate H].
    + apply mf_lt_false in L2; [|exact Fv|exact Fn]. rewrite En in L2.
      split; [intro H; discriminate H|]. split; [intro H; discriminate H|]. intros _. lra.
Qed.

(* WITNESS {"claimId":"s9-margin-filter","topic":"numerics","lemma":"compute_decides_sound","title":"Margin-filtered sign: for a computed v with |v - spec| <= E <= thr, mf_decide v thr = POSITIVE certifies 0 < v - thr <= spec and NEGATIVE certifies spec <= v + thr < 0; spec > thr + E forces a decision; per-consumer fallback policy never emits an uncertified sign","file":"theories-flocq/B64_MarginFilter.v","witness":"compute_decides_sound","board":"ADR-0006"} *)
Theorem compute_decides_sound : forall (v thr : binary64) (spec E : R),
  fin v = true -> fin thr = true ->
  Rabs (B2R v - spec) <= E -> E <= B2R thr ->
  (mf_decide v thr = MF_POSITIVE -> 0 < B2R v - B2R thr <= spec) /\
  (mf_decide v thr = MF_NEGATIVE -> spec <= B2R v + B2R thr < 0).
Proof.
  intros v thr spec E Fv Ft He Ht.
  destruct (mf_decide_cases v thr Fv Ft) as [P [N _]].
  apply Rabs_le_inv in He.
  split; intro H; [specialize (P H) | destruct (N H)]; lra.
Qed.

Theorem compute_decides_complete : forall (v thr : binary64) (spec E : R),
  fin v = true -> fin thr = true -> Rabs (B2R v - spec) <= E -> 0 <= B2R thr ->
  (B2R thr + E < spec -> mf_decide v thr = MF_POSITIVE) /\
  (spec < - (B2R thr + E) -> mf_decide v thr = MF_NEGATIVE).
Proof.
  intros v thr spec E Fv Ft He Ht.
  destruct (mf_decide_cases v thr Fv Ft) as [P [N U]].
  apply Rabs_le_inv in He.
  split; intro Hs; destruct (mf_decide v thr) eqn:D; try reflexivity; exfalso.
  - destruct (N eq_refl). lra.
  - specialize (U eq_refl). lra.
  - specialize (P eq_refl). lra.
  - specialize (U eq_refl). lra.
Qed.

Corollary compute_decides_complete_2E : forall (v thr : binary64) (spec : R),
  fin v = true -> fin thr = true -> Rabs (B2R v - spec) <= B2R thr ->
  (2 * B2R thr < spec -> mf_decide v thr = MF_POSITIVE) /\
  (spec < - (2 * B2R thr) -> mf_decide v thr = MF_NEGATIVE).
Proof.
  intros v thr spec Fv Ft He.
  assert (Ht : 0 <= B2R thr) by (pose proof (Rabs_pos (B2R v - spec)); lra).
  destruct (compute_decides_complete v thr spec (B2R thr) Fv Ft He Ht) as [P N].
  split; intro H; [apply P | apply N]; lra.
Qed.

Theorem compute_undecided_bound : forall (v thr : binary64) (spec E : R),
  fin v = true -> fin thr = true -> Rabs (B2R v - spec) <= E ->
  mf_decide v thr = MF_UNDECIDED -> Rabs spec <= B2R thr + E.
Proof.
  intros v thr spec E Fv Ft He H.
  destruct (mf_decide_cases v thr Fv Ft) as [_ [_ U]]. specialize (U H).
  apply Rabs_le_inv in He. apply Rabs_le. split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Per-consumer fallback policy.                                          *)
(* -------------------------------------------------------------------------- *)

Inductive mf_fallback : Type := MF_ExactFallback | MF_DeclineFallback.
Inductive mf_outcome : Type := MO_Positive | MO_Negative | MO_Exact | MO_Decline.

Definition mf_policy (fb : mf_fallback) (intake : bool) (d : mf_sign) : mf_outcome :=
  if intake then
    match d with
    | MF_POSITIVE => MO_Positive
    | MF_NEGATIVE => MO_Negative
    | MF_UNDECIDED => match fb with MF_ExactFallback => MO_Exact | MF_DeclineFallback => MO_Decline end
    end
  else MO_Decline.

Theorem mf_policy_sound : forall fb (intake : bool) (v thr : binary64) (spec E : R),
  (intake = true -> fin v = true /\ fin thr = true /\ Rabs (B2R v - spec) <= E /\ E <= B2R thr) ->
  (mf_policy fb intake (mf_decide v thr) = MO_Positive -> 0 < spec) /\
  (mf_policy fb intake (mf_decide v thr) = MO_Negative -> spec < 0) /\
  (intake = false -> mf_policy fb intake (mf_decide v thr) = MO_Decline) /\
  (mf_policy fb intake (mf_decide v thr) = MO_Exact -> fb = MF_ExactFallback).
Proof.
  intros fb intake v thr spec E Hcert.
  destruct intake.
  - destruct (Hcert eq_refl) as [Fv [Ft [He Ht]]].
    destruct (compute_decides_sound v thr spec E Fv Ft He Ht) as [P N].
    unfold mf_policy.
    destruct (mf_decide v thr) eqn:D.
    + split; [intros _; destruct (P eq_refl); lra|].
      split; [intro H; discriminate H|]. split; [intro H; discriminate H | intro H; discriminate H].
    + split; [intro H; discriminate H|].
      split; [intros _; destruct (N eq_refl); lra|].
      split; [intro H; discriminate H | intro H; discriminate H].
    + destruct fb; (split; [intro H; discriminate H|]); (split; [intro H; discriminate H|]);
        (split; [intro H; discriminate H|]); intro H; [reflexivity | discriminate H].
  - unfold mf_policy. split; [intro H; discriminate H|].
    split; [intro H; discriminate H|]. split; [reflexivity | intro H; discriminate H].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  First consumer: the ARC_AREA_CENTROID denominator g = t - sin t.       *)
(* -------------------------------------------------------------------------- *)

Definition mf_seg_g (t : binary64) : binary64 := b64_minus t (b64_sin t).

(* 2^-48 *)
Definition mf_seg_thr : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-100) eq_refl.

Lemma mf_seg_thr_R : B2R mf_seg_thr = / 281474976710656 /\ fin mf_seg_thr = true.
Proof. split; [|reflexivity]. unfold mf_seg_thr. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.

Lemma b64_seg_g_err : forall t, sin_accept t = true ->
  fin (mf_seg_g t) = true /\
  Rabs (B2R (mf_seg_g t) - (B2R t - sin (B2R t))) <= / 281474976710656.
Proof.
  intros t Ht.
  destruct (b64_sin_err t Ht) as [Fs Es].
  replace (bpow radix2 (-49)) with (/ 562949953421312) in Es by (cbn; reflexivity).
  assert (Ft : fin t = true).
  { unfold sin_accept in Ht. apply andb_prop in Ht as [Ht _]. apply andb_prop in Ht as [Ft _]. exact Ft. }
  assert (Bt : Rabs (B2R t) <= 10).
  { unfold sin_accept in Ht. apply andb_prop in Ht as [Ht Hhi]. apply andb_prop in Ht as [_ Hlo].
    destruct sn_ten_R as [E10 F10]. destruct sn_mten_R as [Em Fm].
    apply b64ae_le_true in Hlo; [|exact Fm|exact Ft]. apply b64ae_le_true in Hhi; [|exact Ft|exact F10].
    rewrite Em in Hlo. rewrite E10 in Hhi. apply Rabs_le. split; lra. }
  pose proof (SIN_bound (B2R t)) as Sb.
  assert (Bs : Rabs (B2R (b64_sin t)) <= 1 + / 562949953421312).
  { pose proof (Rabs_triang_inv (B2R (b64_sin t)) (sin (B2R t))).
    assert (Rabs (sin (B2R t)) <= 1) by (apply Rabs_le; lra). lra. }
  assert (Bd : Rabs (B2R t - B2R (b64_sin t)) <= 10 + (1 + / 562949953421312)).
  { pose proof (Rabs_triang (B2R t) (- B2R (b64_sin t))). rewrite Rabs_Ropp in *.
    unfold Rminus. lra. }
  pose proof sp_u_val as Uv. pose proof sp_e0_bounds as [He0 He1].
  destruct (b64ae_minus_err t (b64_sin t) Ft Fs
              ltac:(eapply Rle_trans; [exact Bd|]; apply Rle_trans with 4096;
                    [lra | apply Rle_trans with (bpow radix2 12); [cbn; lra | apply bpow_le; lia]]))
    as [Fg Eg].
  pose proof (b64ae_u_mul_le _ _ Bd) as Ug. rewrite Uv in Ug, Eg.
  split; [exact Fg|].
  revert Fg Eg. unfold mf_seg_g. generalize (b64_minus t (b64_sin t)). intros g Fg Eg.
  replace (B2R g - (B2R t - sin (B2R t)))
    with ((B2R g - (B2R t - B2R (b64_sin t))) - (B2R (b64_sin t) - sin (B2R t))) by ring.
  set (a := B2R g - (B2R t - B2R (b64_sin t))) in *.
  set (b := B2R (b64_sin t) - sin (B2R t)) in *.
  pose proof (Rabs_triang a (- b)) as T. rewrite Rabs_Ropp in T.
  replace (a + - b) with (a - b) in T by ring. lra.
Qed.

(* POSITIVE certifies the denominator lower bound g >= v - 2^-48 > 0. *)
Theorem b64_seg_g_positive_lb : forall t, sin_accept t = true ->
  mf_decide (mf_seg_g t) mf_seg_thr = MF_POSITIVE ->
  0 < B2R (mf_seg_g t) - / 281474976710656 <= B2R t - sin (B2R t).
Proof.
  intros t Ht H.
  destruct (b64_seg_g_err t Ht) as [Fg Eg]. destruct mf_seg_thr_R as [Et Ft].
  destruct (compute_decides_sound _ _ _ _ Fg Ft Eg ltac:(rewrite Et; lra)) as [P _].
  rewrite Et in P. exact (P H).
Qed.

Theorem b64_seg_g_complete : forall t, sin_accept t = true ->
  / 140737488355328 < B2R t - sin (B2R t) ->
  mf_decide (mf_seg_g t) mf_seg_thr = MF_POSITIVE.
Proof.
  intros t Ht H.
  destruct (b64_seg_g_err t Ht) as [Fg Eg]. destruct mf_seg_thr_R as [Et Ft].
  destruct (compute_decides_complete_2E _ _ _ Fg Ft ltac:(rewrite Et; exact Eg)) as [P _].
  apply P. rewrite Et. lra.
Qed.

(* The consumer, with its policy: no exact path for g, so UNDECIDED declines. *)
Definition mf_seg_g_outcome (t : binary64) : mf_outcome :=
  mf_policy MF_DeclineFallback (sin_accept_b t) (mf_decide (mf_seg_g t) mf_seg_thr).

Theorem mf_seg_g_outcome_sound : forall t,
  (mf_seg_g_outcome t = MO_Positive -> 0 < B2R t - sin (B2R t)) /\
  (mf_seg_g_outcome t = MO_Negative -> B2R t - sin (B2R t) < 0) /\
  mf_seg_g_outcome t <> MO_Exact.
Proof.
  intro t.
  destruct (mf_policy_sound MF_DeclineFallback (sin_accept_b t) (mf_seg_g t) mf_seg_thr
              (B2R t - sin (B2R t)) (/ 281474976710656)) as [P [N [_ X]]].
  { intro H. rewrite sin_accept_b_eq in H. destruct (b64_seg_g_err t H) as [Fg Eg].
    destruct mf_seg_thr_R as [Et Ft]. rewrite Et. repeat split; try assumption. lra. }
  unfold mf_seg_g_outcome. split; [exact P|]. split; [exact N|].
  intro H. specialize (X H). discriminate X.
Qed.

Print Assumptions compute_decides_sound.
Print Assumptions compute_decides_complete.
Print Assumptions compute_undecided_bound.
Print Assumptions mf_policy_sound.
Print Assumptions b64_seg_g_err.
Print Assumptions b64_seg_g_positive_lb.
Print Assumptions b64_seg_g_complete.
Print Assumptions mf_seg_g_outcome_sound.
