(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_stage_d_cc
   ----------------------------------------------------------------------------
   Stage D rebuilt on carry_clean.  Supersedes the conditional
   `b64_orient_sign_exact_sound` / `b64_orient_sign_stage_d_sound`
   (Orient_b64_stage_d.v), which take the REFUTED
   `fast_expansion_sum_strong_nonoverlap_headline` as a hypothesis.  Nothing
   here mentions that headline, directly or through a lemma that takes it.

   DECODERS
     b64_orient_sign_exact_cc     sign of carry_clean (fast_expansion_sum ...)
     b64_orient_sign_stage_d_cc   Stage A filter; on Uncertain / Nan, the
                                  carry_clean exact decoder.  Same shape as
                                  b64_orient_sign_stage_d, only the fallback
                                  changes.

   RESULTS
     b64_orient_sign_exact_cc_sound
        the exact path is sound vs cross_R_BP on the coordinate domain
        |coord| <= 2^507 (orient2d_inputs_cc_domain) under Stage D's safety
        predicate minus fast_expansion_sum_safe (now derived).  No integer
        regime: this is the orient2d soundness headline of the rebuild.
        STILL ASSUMED (b64_orient2d_expansion_cc_safe): the four coordinate
        differences are computed EXACTLY (no TwoDiff tail is tracked), every
        Dekker operation is overflow-safe, and Dekker's no-underflow
        precondition holds.  None of these follows from the domain.
     b64_orient_sign_stage_d_cc_sound
        the full decoder, under the integer regime (for the filter path, as
        before) and the same expansion safety.  The domain is implied by the
        integer regime (int_safe_cc_domain: 2^25 <= 2^507).
     b64_orient_sign_stage_d_cc_tiny_regime_decisive
        the tiny-regime decisiveness carries over.

   topic: binary64
   claimId: orient2d-stage-d-carry-clean
   witness: b64_orient_sign_exact_cc_sound

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed (2026-11-10, J. Bloemscheer, PR #1017 @ 16a1b47);
     the non-vacuity witness (b64_small .. orient2d_cc_witness), added after
     that review, approved with the file (PR #1017 @ 55b9089).
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib Orient_b64_sound
     Orient_b64_exact Orientation_b64 B64_Pff_bridge B64_Expansion B64_CarryCleanAlgo
     Orient_b64_expansion Orient_b64_stage_d Orient_b64_expansion_cc.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Exact decoder on carry_clean.                                              *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient_sign_exact_cc (P0 P1 Q : BPoint) : orient_sign_robust :=
  expansion_sign_to_orient_robust (b64_orient2d_expansion_cc_sign P0 P1 Q).

Theorem b64_orient_sign_exact_cc_sound :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_cc_domain P0 P1 Q ->
    b64_orient2d_expansion_cc_safe P0 P1 Q ->
    match b64_orient_sign_exact_cc P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hd Hs.
  unfold b64_orient_sign_exact_cc, expansion_sign_to_orient_robust.
  pose proof (b64_orient2d_expansion_cc_sign_correct P0 P1 Q Hs Hd) as H.
  destruct (b64_orient2d_expansion_cc_sign P0 P1 Q); exact H.
Qed.

(* The exact decoder never declines. *)
Lemma b64_orient_sign_exact_cc_definite :
  forall P0 P1 Q,
    b64_orient_sign_exact_cc P0 P1 Q <> OrientRNan
    /\ b64_orient_sign_exact_cc P0 P1 Q <> OrientRUncertain.
Proof.
  intros P0 P1 Q. unfold b64_orient_sign_exact_cc, expansion_sign_to_orient_robust.
  destruct (b64_orient2d_expansion_cc_sign P0 P1 Q); split; discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Full Stage D decoder: filter, then carry_clean exact fallback.            *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient_sign_stage_d_cc (P0 P1 Q : BPoint) : orient_sign_robust :=
  match b64_orient_sign_filtered P0 P1 Q with
  | OrientRPos       => OrientRPos
  | OrientRNeg       => OrientRNeg
  | OrientRZero      => OrientRZero
  | OrientRUncertain => b64_orient_sign_exact_cc P0 P1 Q
  | OrientRNan       => b64_orient_sign_exact_cc P0 P1 Q
  end.

Lemma coord_int_safe_cc_domain :
  forall c, coord_int_safe c -> coord_in_cc_domain c.
Proof.
  intros c (Fc & n & Hn & Hb). split; [ exact Fc | ].
  rewrite Hn, <- abs_IZR.
  apply Rle_trans with (bpow radix2 25).
  - rewrite <- IZR_Zpower by lia. apply IZR_le. exact Hb.
  - apply bpow_le. unfold orient2d_cc_coord_exp. lia.
Qed.

Lemma int_safe_cc_domain :
  forall P0 P1 Q, orient2d_inputs_int_safe P0 P1 Q -> orient2d_inputs_cc_domain P0 P1 Q.
Proof.
  intros P0 P1 Q (H1 & H2 & H3 & H4 & H5 & H6).
  repeat split; apply coord_int_safe_cc_domain; assumption.
Qed.

Theorem b64_orient_sign_stage_d_cc_sound :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_expansion_cc_safe P0 P1 Q ->
    match b64_orient_sign_stage_d_cc P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hint Hs.
  unfold b64_orient_sign_stage_d_cc.
  pose proof (b64_orient_sign_filtered_sound_small_int P0 P1 Q Hint) as Hfilt.
  pose proof (b64_orient_sign_exact_cc_sound P0 P1 Q (int_safe_cc_domain P0 P1 Q Hint) Hs)
    as Hexact.
  destruct (b64_orient_sign_filtered P0 P1 Q);
    [ exact Hfilt | exact Hfilt | exact Hfilt | exact Hexact | exact Hexact ].
Qed.

Theorem b64_orient_sign_stage_d_cc_tiny_regime_decisive :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_tiny_int_safe P0 P1 Q ->
    cross_R_BP P0 P1 Q <> 0 ->
    b64_orient_sign_stage_d_cc P0 P1 Q <> OrientRUncertain.
Proof.
  intros P0 P1 Q Htiny Hnz.
  pose proof (b64_orient_sign_filtered_tiny_regime_decisive P0 P1 Q Htiny Hnz) as HnotU.
  unfold b64_orient_sign_stage_d_cc.
  destruct (b64_orient_sign_filtered P0 P1 Q) eqn:Hf; try congruence.
  exact (proj2 (b64_orient_sign_exact_cc_definite P0 P1 Q)).
Qed.

(* -------------------------------------------------------------------------- *)
(* Non-vacuity: a concrete non-collinear input OUTSIDE the integer regime     *)
(* satisfies every hypothesis, and the decoder returns OrientRPos.            *)
(*                                                                            *)
(*   P0 = (0, 0),  P1 = (N, 1),  Q = (1, N),  N = 2^30 + 1  (> 2^25).        *)
(*   dx1 = dy1 = N: the first Dekker product N^2 = 2^60 + 2^31 + 1 needs 61   *)
(*   bits, so its low part is nonzero (r = 2^60 + 2^31, t = 1); the second    *)
(*   product is (-1)(1).  cross = N^2 - 1 > 0.                                *)
(*                                                                            *)
(* Per-operation safety is checked by a computable magnitude test             *)
(* (b64_small: digits + exponent <= 454, so |x| <= 2^454), which makes every  *)
(* sum, difference and product overflow-free.                                 *)
(* -------------------------------------------------------------------------- *)

Local Abbreviation b2r := (Binary.B2R prec emax).

Definition b64_small (x : binary64) : bool :=
  match x with
  | Binary.B754_zero _ => true
  | Binary.B754_finite _ m e _ => Z.leb (Z.pos (digits2_pos m) + e) 454
  | _ => false
  end.

Lemma b64_small_bound :
  forall x, b64_small x = true ->
    Binary.is_finite prec emax x = true /\ Rabs (b2r x) <= bpow radix2 454.
Proof.
  intros [s | s | s pl Hpl | s m e H] Hs; cbn [b64_small] in Hs; try discriminate.
  - split; [ reflexivity | ]. cbn [Binary.B2R]. rewrite Rabs_R0. apply bpow_ge_0.
  - split; [ reflexivity | ]. rewrite abs_B2R_fin. apply Z.leb_le in Hs.
    pose proof (IZR_pos_bpow_bounds m) as [_ Hm].
    apply Rle_trans with (bpow radix2 (Z.pos (digits2_pos m)) * bpow radix2 e).
    + apply Rmult_le_compat_r; [ apply bpow_ge_0 | lra ].
    + rewrite <- bpow_plus. apply bpow_le. exact Hs.
Qed.

Lemma b64_safe_small :
  forall (op : R -> R -> R) x y,
    (forall a b, Rabs a <= bpow radix2 454 -> Rabs b <= bpow radix2 454 ->
                 Rabs (op a b) <= bpow radix2 1000) ->
    b64_small x = true -> b64_small y = true -> b64_safe op x y.
Proof.
  intros op x y Hop Hx Hy.
  destruct (b64_small_bound x Hx) as [Fx Bx]. destruct (b64_small_bound y Hy) as [Fy By].
  refine (conj Fx (conj Fy _)).
  apply Rle_lt_trans with (bpow radix2 1000).
  - apply rnd64_abs_le_bpow; [ unfold prec, emax; lia | exact (Hop _ _ Bx By) ].
  - apply bpow_lt. unfold emax. lia.
Qed.

Lemma op_bound_plus : forall a b, Rabs a <= bpow radix2 454 -> Rabs b <= bpow radix2 454 ->
  Rabs (a + b) <= bpow radix2 1000.
Proof.
  intros a b Ha Hb. eapply Rle_trans; [ apply Rabs_triang | ].
  pose proof (bpow_le radix2 455 1000 ltac:(lia)).
  replace (bpow radix2 455) with (2 * bpow radix2 454) in H
    by (replace 455%Z with (1 + 454)%Z by reflexivity; rewrite bpow_plus; reflexivity). lra.
Qed.

Lemma op_bound_minus : forall a b, Rabs a <= bpow radix2 454 -> Rabs b <= bpow radix2 454 ->
  Rabs (a - b) <= bpow radix2 1000.
Proof.
  intros a b Ha Hb. unfold Rminus. apply op_bound_plus; [ exact Ha | rewrite Rabs_Ropp; exact Hb ].
Qed.

Lemma op_bound_mult : forall a b, Rabs a <= bpow radix2 454 -> Rabs b <= bpow radix2 454 ->
  Rabs (a * b) <= bpow radix2 1000.
Proof.
  intros a b Ha Hb. rewrite Rabs_mult.
  apply Rle_trans with (bpow radix2 454 * bpow radix2 454).
  - apply Rmult_le_compat; try apply Rabs_pos; assumption.
  - rewrite <- bpow_plus. apply bpow_le. lia.
Qed.

Ltac b64_safe_by_small :=
  first [ apply (b64_safe_small Rplus _ _ op_bound_plus)
        | apply (b64_safe_small Rminus _ _ op_bound_minus)
        | apply (b64_safe_small Rmult _ _ op_bound_mult) ];
  vm_compute; reflexivity.

Definition wit_0 : binary64 := Binary.B754_zero prec emax false.
Definition wit_1 : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition wit_N : binary64 := Binary.B754_finite prec emax false 4503599631564800 (-22) eq_refl.
Definition wit_r : binary64 := Binary.B754_finite prec emax false 4503599635759104 8 eq_refl.

Definition wit_P0 : BPoint := mkBP wit_0 wit_0.
Definition wit_P1 : BPoint := mkBP wit_N wit_1.
Definition wit_Q  : BPoint := mkBP wit_1 wit_N.

Lemma wit_vals :
  b2r wit_0 = IZR 0 /\ b2r wit_1 = IZR 1 /\ b2r wit_N = IZR (2 ^ 30 + 1).
Proof.
  split; [ reflexivity | split ].
  - unfold wit_1. rewrite B2R_fin. cbn [cond_Zopp].
    replace (IZR (Z.pos 4503599627370496)) with (bpow radix2 52)
      by (rewrite <- IZR_Zpower by lia; reflexivity).
    rewrite <- bpow_plus. reflexivity.
  - unfold wit_N. rewrite B2R_fin. cbn [cond_Zopp].
    replace (IZR (Z.pos 4503599631564800)) with (IZR (2 ^ 30 + 1) * bpow radix2 22)
      by (rewrite <- IZR_Zpower by lia; rewrite <- mult_IZR; reflexivity).
    rewrite Rmult_assoc, <- bpow_plus. change (bpow radix2 (22 + -22)) with 1. ring.
Qed.

Lemma wit_minus :
  forall x y a b, b2r x = IZR a -> b2r y = IZR b ->
    Binary.is_finite prec emax x = true -> Binary.is_finite prec emax y = true ->
    (Z.abs (a - b) <= 2 ^ prec)%Z ->
    b2r (b64_minus x y) = b2r x - b2r y.
Proof.
  intros x y a b Hx Hy Fx Fy Hb.
  destruct (b64_minus_int_exact x y a b Fx Fy Hx Hy Hb) as [H _].
  rewrite H, minus_IZR, Hx, Hy. reflexivity.
Qed.

(* The first Dekker pair has a nonzero low part: (2^60 + 2^31, 1). *)
Lemma wit_dekker1 :
  b64_Dekker (b64_minus wit_N wit_0) (b64_minus wit_N wit_0) = (wit_r, wit_1).
Proof.
  apply (f_equal2 pair); apply Binary.B2FF_inj; vm_compute; reflexivity.
Qed.

Theorem orient2d_cc_witness :
  orient2d_inputs_cc_domain wit_P0 wit_P1 wit_Q
  /\ b64_orient2d_expansion_cc_safe wit_P0 wit_P1 wit_Q
  /\ ~ coord_int_safe (bx wit_P1)
  /\ cross_R_BP wit_P0 wit_P1 wit_Q = IZR ((2 ^ 30 + 1) * (2 ^ 30 + 1) - 1)
  /\ b64_orient_sign_exact_cc wit_P0 wit_P1 wit_Q = OrientRPos.
Proof.
  destruct wit_vals as (V0 & V1 & VN).
  assert (F0 : Binary.is_finite prec emax wit_0 = true) by reflexivity.
  assert (F1 : Binary.is_finite prec emax wit_1 = true) by reflexivity.
  assert (FN : Binary.is_finite prec emax wit_N = true) by reflexivity.
  assert (Hle : forall n : Z, (0 <= n <= 2 ^ 31)%Z -> Rabs (IZR n) <= bpow radix2 orient2d_cc_coord_exp).
  { intros n Hn. rewrite Rabs_pos_eq by (apply IZR_le; lia).
    apply Rle_trans with (bpow radix2 31).
    - rewrite <- IZR_Zpower by lia. apply IZR_le. cbn. lia.
    - apply bpow_le. unfold orient2d_cc_coord_exp. lia. }
  assert (Dom : orient2d_inputs_cc_domain wit_P0 wit_P1 wit_Q).
  { unfold orient2d_inputs_cc_domain, coord_in_cc_domain, wit_P0, wit_P1, wit_Q; cbn [bx by_].
    rewrite V0, V1, VN.
    repeat split; try assumption; apply Hle; lia. }
  (* the four differences, exact *)
  assert (D1 : b2r (b64_minus wit_N wit_0) = b2r wit_N - b2r wit_0)
    by (apply (wit_minus _ _ (2 ^ 30 + 1) 0); try assumption; unfold prec; lia).
  assert (D2 : b2r (b64_minus wit_0 wit_1) = b2r wit_0 - b2r wit_1)
    by (apply (wit_minus _ _ 0 1); try assumption; unfold prec; lia).
  assert (D3 : b2r (b64_minus wit_1 wit_0) = b2r wit_1 - b2r wit_0)
    by (apply (wit_minus _ _ 1 0); try assumption; unfold prec; lia).
  assert (Hund : forall a b : R, 1 <= Rabs (a * b) ->
            a * b = 0 \/ bpow radix2 (3 - emax - prec + 2 * prec - 1) <= Rabs (a * b)).
  { intros a b H. right. apply Rle_trans with 1; [ | exact H ].
    change 1 with (bpow radix2 0). apply bpow_le. unfold emax, prec. lia. }
  assert (Safe : b64_orient2d_expansion_cc_safe wit_P0 wit_P1 wit_Q).
  { unfold b64_orient2d_expansion_cc_safe, b64_orient2d_expansion_diffs_safe,
      b64_orient2d_expansion_diffs_exact, wit_P0, wit_P1, wit_Q; cbn [bx by_].
    split; [ repeat split; b64_safe_by_small | ].
    split; [ repeat split; assumption | ].
    split; [ unfold b64_Dekker_safe; cbv zeta;
             repeat match goal with |- _ /\ _ => split end; b64_safe_by_small | ].
    split; [ unfold b64_Dekker_safe; cbv zeta;
             repeat match goal with |- _ /\ _ => split end; b64_safe_by_small | ].
    split; unfold dekker_no_underflow; apply Hund.
    - rewrite D1, V0, VN, Rminus_0_r, <- mult_IZR, <- abs_IZR. apply IZR_le. cbn. lia.
    - rewrite D2, D3, V0, V1. rewrite Rminus_0_l, Rminus_0_r, <- opp_IZR, <- mult_IZR, <- abs_IZR.
      apply IZR_le. cbn. lia. }
  assert (Hcross : cross_R_BP wit_P0 wit_P1 wit_Q = IZR ((2 ^ 30 + 1) * (2 ^ 30 + 1) - 1)).
  { unfold cross_R_BP, wit_P0, wit_P1, wit_Q; cbn [bx by_]. rewrite V0, V1, VN.
    rewrite minus_IZR, !mult_IZR. ring. }
  refine (conj Dom (conj Safe (conj _ (conj Hcross _)))).
  - intros (_ & n & Hn & Hb). cbn [bx wit_P1] in Hn. rewrite VN in Hn. apply eq_IZR in Hn.
    subst n. cbn in Hb. lia.
  - pose proof (b64_orient_sign_exact_cc_sound wit_P0 wit_P1 wit_Q Dom Safe) as Hs.
    pose proof (b64_orient_sign_exact_cc_definite wit_P0 wit_P1 wit_Q) as [HnN HnU].
    assert (Hpos : 0 < cross_R_BP wit_P0 wit_P1 wit_Q) by (rewrite Hcross; apply IZR_lt; cbn; lia).
    destruct (b64_orient_sign_exact_cc wit_P0 wit_P1 wit_Q).
    + reflexivity.
    + lra.
    + lra.
    + exfalso. exact (HnN eq_refl).
    + exfalso. exact (HnU eq_refl).
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient_sign_exact_cc_sound.
Print Assumptions b64_orient_sign_exact_cc_definite.
Print Assumptions int_safe_cc_domain.
Print Assumptions b64_orient_sign_stage_d_cc_sound.
Print Assumptions b64_orient_sign_stage_d_cc_tiny_regime_decisive.
Print Assumptions b64_small_bound.
Print Assumptions b64_safe_small.
Print Assumptions wit_dekker1.
Print Assumptions orient2d_cc_witness.
