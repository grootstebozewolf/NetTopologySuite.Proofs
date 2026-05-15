(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_bridge
   ----------------------------------------------------------------------------
   Lift Flocq's `Bplus_correct` / `Bminus_correct` / `Bmult_correct` to the
   binary64 helpers `b64_plus` / `b64_minus` / `b64_mult` defined in
   `Validate_binary64.v`.

   This is the critical-path module identified in
   `docs/audit-shewchuk-stages.md`.  A clean wrapper here unlocks three
   currently-blocked theorems simultaneously:

     1. `greedy_simplify_binary64_sound`   (the simplifier R-bridge).
     2. The R-side arithmetic identities for `b64_orient2d`
        (antisymmetry, cyclic permutation, translation invariance).
     3. `b64_orient2d_exact_sound`          (orient2d Stages B / C).

   The proofs here are thin -- each one is `pose proof BPLUS_correct;
   destruct on the Rlt_bool guard; split`.  The interesting work is on
   the caller side: discharging the no-overflow precondition for
   specific operand magnitudes (e.g. NTS coordinates fitting in
   2^500), and composing the per-op lifts into the larger soundness
   bridges for the simplifier and orient2d.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.

Local Open Scope R_scope.

(* The binary64 FLT exponent function.  Flocq's `Binary.Bplus_correct`    *)
(* internally states its rounding via `SpecFloat.fexp prec emax`, which   *)
(* is `FLT_exp (3 - emax - prec) prec` definitionally; use SpecFloat's    *)
(* spelling so our theorem statements unify with `Bplus_correct`'s        *)
(* conclusion without an extra `change` step.                              *)
Local Notation b64_fexp := (SpecFloat.fexp prec emax).
Local Notation b64_round := (round radix2 b64_fexp (round_mode mode_b64)).

(* -------------------------------------------------------------------------- *)
(* Bundled precondition predicate for per-op correctness.                     *)
(*                                                                            *)
(* `b64_safe op x y` packages the three obligations each per-op lift          *)
(* needs (finiteness of both operands + no-overflow on the rounded result).   *)
(* Parameterised by the R-side operation so the same shape works for plus,    *)
(* minus and mult; downstream consumers state one premise per op call         *)
(* instead of three.                                                           *)
(* -------------------------------------------------------------------------- *)

Definition b64_safe (op : R -> R -> R) (x y : binary64) : Prop :=
  Binary.is_finite prec emax x = true /\
  Binary.is_finite prec emax y = true /\
  Rabs (b64_round (op (Binary.B2R prec emax x) (Binary.B2R prec emax y)))
    < bpow radix2 emax.

(* -------------------------------------------------------------------------- *)
(* `b64_plus_correct`: under finiteness of both operands and a no-overflow    *)
(* precondition stated as `R`-side inequality, `b64_plus x y` is bit-exactly  *)
(* the rounded sum of `B2R x + B2R y`, and the result is finite.              *)
(* -------------------------------------------------------------------------- *)

Theorem b64_plus_correct :
  forall x y : binary64,
    b64_safe Rplus x y ->
    Binary.B2R prec emax (b64_plus x y)
      = b64_round (Binary.B2R prec emax x + Binary.B2R prec emax y)
    /\ Binary.is_finite prec emax (b64_plus x y) = true.
Proof.
  intros x y (Fx & Fy & Hbnd).
  pose proof (Binary.Bplus_correct prec emax prec_gt_0_b64 prec_lt_emax_b64
                default_nan_b64 mode_b64 x y Fx Fy) as H.
  apply Rlt_bool_true in Hbnd.
  unfold b64_plus.
  destruct (Rlt_bool _ _) eqn:E in H.
  - destruct H as [HB2R [Hfin _]].
    split; assumption.
  - rewrite E in Hbnd. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* `b64_minus_correct`: under finiteness + no-overflow on the rounded         *)
(* subtraction, `b64_minus x y` is the exact rounded difference.              *)
(* -------------------------------------------------------------------------- *)

Theorem b64_minus_correct :
  forall x y : binary64,
    b64_safe Rminus x y ->
    Binary.B2R prec emax (b64_minus x y)
      = b64_round (Binary.B2R prec emax x - Binary.B2R prec emax y)
    /\ Binary.is_finite prec emax (b64_minus x y) = true.
Proof.
  intros x y (Fx & Fy & Hbnd).
  pose proof (Binary.Bminus_correct prec emax prec_gt_0_b64 prec_lt_emax_b64
                default_nan_b64 mode_b64 x y Fx Fy) as H.
  apply Rlt_bool_true in Hbnd.
  unfold b64_minus.
  destruct (Rlt_bool _ _) eqn:E in H.
  - destruct H as [HB2R [Hfin _]].
    split; assumption.
  - rewrite E in Hbnd. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* `b64_mult_correct`: under finiteness + no-overflow on the rounded          *)
(* product, `b64_mult x y` is the exact rounded product.                      *)
(* -------------------------------------------------------------------------- *)

Theorem b64_mult_correct :
  forall x y : binary64,
    b64_safe Rmult x y ->
    Binary.B2R prec emax (b64_mult x y)
      = b64_round (Binary.B2R prec emax x * Binary.B2R prec emax y)
    /\ Binary.is_finite prec emax (b64_mult x y) = true.
Proof.
  intros x y (Fx & Fy & Hbnd).
  pose proof (Binary.Bmult_correct prec emax prec_gt_0_b64 prec_lt_emax_b64
                default_nan_b64 mode_b64 x y) as H.
  apply Rlt_bool_true in Hbnd.
  unfold b64_mult.
  destruct (Rlt_bool _ _) eqn:E in H.
  - destruct H as [HB2R [Hfin _]].
    split.
    + exact HB2R.
    + rewrite Hfin. rewrite Fx, Fy. reflexivity.
  - rewrite E in Hbnd. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Zero-arithmetic helpers.                                                   *)
(*                                                                            *)
(* Small facts that the per-op correctness theorems make trivial to derive    *)
(* but that downstream vertex-coincidence proofs need over and over.  Worth   *)
(* factoring once here so the orient2d degenerate cases stay short.           *)
(* -------------------------------------------------------------------------- *)

Lemma b64_round_0 : b64_round 0 = 0.
Proof. apply round_0. apply valid_rnd_N. Qed.

(* Subtracting any finite binary64 from itself gives exactly zero in R.       *)
(* The no-overflow precondition is trivially discharged: `b64_round 0 = 0`    *)
(* and `Rabs 0 = 0 < bpow emax`.                                              *)
Lemma b64_minus_self_R :
  forall x : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.B2R prec emax (b64_minus x x) = 0.
Proof.
  intros x Fx.
  assert (Hsafe : b64_safe Rminus x x).
  { repeat split; try assumption.
    rewrite Rminus_diag, b64_round_0, Rabs_R0.
    apply bpow_gt_0. }
  pose proof (b64_minus_correct _ _ Hsafe) as [HB2R _].
  rewrite HB2R, Rminus_diag.
  apply b64_round_0.
Qed.

(* Multiplying a binary64 whose B2R is zero by any finite binary64 gives      *)
(* exactly zero in R.  Same trivial no-overflow story: `b64_round 0 = 0`.    *)
Lemma b64_mult_zero_l_R :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax x = 0 ->
    Binary.B2R prec emax (b64_mult x y) = 0.
Proof.
  intros x y Fx Fy HxR.
  assert (Hsafe : b64_safe Rmult x y).
  { repeat split; try assumption.
    rewrite HxR, Rmult_0_l, b64_round_0, Rabs_R0.
    apply bpow_gt_0. }
  pose proof (b64_mult_correct _ _ Hsafe) as [HB2R _].
  rewrite HB2R, HxR, Rmult_0_l.
  apply b64_round_0.
Qed.

Lemma b64_mult_zero_r_R :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax y = 0 ->
    Binary.B2R prec emax (b64_mult x y) = 0.
Proof.
  intros x y Fx Fy HyR.
  assert (Hsafe : b64_safe Rmult x y).
  { repeat split; try assumption.
    rewrite HyR, Rmult_0_r, b64_round_0, Rabs_R0.
    apply bpow_gt_0. }
  pose proof (b64_mult_correct _ _ Hsafe) as [HB2R _].
  rewrite HB2R, HyR, Rmult_0_r.
  apply b64_round_0.
Qed.

(* `b64_minus` preserves finiteness when there is no overflow.  Convenience  *)
(* corollary of `b64_minus_correct`'s second conjunct, separated out so       *)
(* downstream proofs can chain finiteness through several b64_* without       *)
(* re-destructing each correctness tuple.                                     *)
Lemma b64_minus_self_finite :
  forall x : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax (b64_minus x x) = true.
Proof.
  intros x Fx.
  assert (Hsafe : b64_safe Rminus x x).
  { repeat split; try assumption.
    rewrite Rminus_diag, b64_round_0, Rabs_R0.
    apply bpow_gt_0. }
  apply (b64_minus_correct _ _ Hsafe).
Qed.

(* `b64_minus` of any two finite binary64 values whose `B2R`s are zero gives *)
(* exactly zero in R.  Generalises `b64_minus_self_R` from `x = y` to        *)
(* `B2R x = 0 /\ B2R y = 0`, which is what the vertex-coincidence proofs    *)
(* need after lifting both products through `b64_mult_zero_{l,r}_R`.        *)
Lemma b64_minus_zeros_R :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax x = 0 ->
    Binary.B2R prec emax y = 0 ->
    Binary.B2R prec emax (b64_minus x y) = 0.
Proof.
  intros x y Fx Fy HxR HyR.
  assert (Hsafe : b64_safe Rminus x y).
  { repeat split; try assumption.
    rewrite HxR, HyR, Rminus_0_r, b64_round_0, Rabs_R0.
    apply bpow_gt_0. }
  pose proof (b64_minus_correct _ _ Hsafe) as [HB2R _].
  rewrite HB2R, HxR, HyR, Rminus_0_r.
  apply b64_round_0.
Qed.

(* Finiteness lemmas for `b64_mult` when one operand has `B2R = 0`.  Used   *)
(* in the same chain as the `_R` lemmas above so the downstream proof can   *)
(* satisfy `b64_safe`'s finiteness conjuncts without re-applying            *)
(* `b64_mult_correct` for each.                                              *)
Lemma b64_mult_zero_l_finite :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax x = 0 ->
    Binary.is_finite prec emax (b64_mult x y) = true.
Proof.
  intros x y Fx Fy HxR.
  assert (Hsafe : b64_safe Rmult x y).
  { repeat split; try assumption.
    rewrite HxR, Rmult_0_l, b64_round_0, Rabs_R0.
    apply bpow_gt_0. }
  apply (b64_mult_correct _ _ Hsafe).
Qed.

Lemma b64_mult_zero_r_finite :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax y = 0 ->
    Binary.is_finite prec emax (b64_mult x y) = true.
Proof.
  intros x y Fx Fy HyR.
  assert (Hsafe : b64_safe Rmult x y).
  { repeat split; try assumption.
    rewrite HyR, Rmult_0_r, b64_round_0, Rabs_R0.
    apply bpow_gt_0. }
  apply (b64_mult_correct _ _ Hsafe).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_plus_correct.
Print Assumptions b64_minus_correct.
Print Assumptions b64_mult_correct.
Print Assumptions b64_minus_self_R.
Print Assumptions b64_mult_zero_l_R.
Print Assumptions b64_mult_zero_r_R.
