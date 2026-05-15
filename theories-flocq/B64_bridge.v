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
(* `b64_plus_correct`: under finiteness of both operands and a no-overflow    *)
(* precondition stated as `R`-side inequality, `b64_plus x y` is bit-exactly  *)
(* the rounded sum of `B2R x + B2R y`, and the result is finite.              *)
(* -------------------------------------------------------------------------- *)

Theorem b64_plus_correct :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Rabs (b64_round (Binary.B2R prec emax x + Binary.B2R prec emax y))
      < bpow radix2 emax ->
    Binary.B2R prec emax (b64_plus x y)
      = b64_round (Binary.B2R prec emax x + Binary.B2R prec emax y)
    /\ Binary.is_finite prec emax (b64_plus x y) = true.
Proof.
  intros x y Fx Fy Hbnd.
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
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Rabs (b64_round (Binary.B2R prec emax x - Binary.B2R prec emax y))
      < bpow radix2 emax ->
    Binary.B2R prec emax (b64_minus x y)
      = b64_round (Binary.B2R prec emax x - Binary.B2R prec emax y)
    /\ Binary.is_finite prec emax (b64_minus x y) = true.
Proof.
  intros x y Fx Fy Hbnd.
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
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Rabs (b64_round (Binary.B2R prec emax x * Binary.B2R prec emax y))
      < bpow radix2 emax ->
    Binary.B2R prec emax (b64_mult x y)
      = b64_round (Binary.B2R prec emax x * Binary.B2R prec emax y)
    /\ Binary.is_finite prec emax (b64_mult x y) = true.
Proof.
  intros x y Fx Fy Hbnd.
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
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_plus_correct.
Print Assumptions b64_minus_correct.
Print Assumptions b64_mult_correct.
