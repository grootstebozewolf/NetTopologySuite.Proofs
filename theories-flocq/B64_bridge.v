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
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

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
(* `b64_div_correct`: lift of Flocq's `Bdiv_correct`.  Division has a         *)
(* different precondition shape than +/-/* -- the divisor must be non-zero    *)
(* (an `R`-side condition, not just `is_finite`).  Phase 1's intersection-     *)
(* point computation is the first consumer.                                    *)
(* -------------------------------------------------------------------------- *)

Theorem b64_div_correct :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax y <> 0 ->
    Rabs (b64_round (Binary.B2R prec emax x / Binary.B2R prec emax y))
      < bpow radix2 emax ->
    Binary.B2R prec emax (b64_div x y)
      = b64_round (Binary.B2R prec emax x / Binary.B2R prec emax y)
    /\ Binary.is_finite prec emax (b64_div x y) = true.
Proof.
  intros x y Fx Fy Hy_nonzero Hbnd.
  pose proof (Binary.Bdiv_correct prec emax prec_gt_0_b64 prec_lt_emax_b64
                default_nan_b64 mode_b64 x y Hy_nonzero) as H.
  apply Rlt_bool_true in Hbnd.
  unfold b64_div.
  destruct (Rlt_bool _ _) eqn:E in H.
  - destruct H as [HB2R [Hfin _]].
    split.
    + exact HB2R.
    + rewrite Hfin. exact Fx.
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

(* ============================================================================
   Magnitude-bounded interface (Flavour B from the Phase 0 audit).
   ----------------------------------------------------------------------------
   The `b64_safe op x y` predicates above package operand finiteness + a
   no-overflow check stated as `Rabs (b64_round (op (B2R x) (B2R y))) <
   bpow emax`.  That's the natural shape for stating per-op correctness,
   but it's painful for downstream callers: an orient2d soundness theorem
   needs seven such checks, one per sub-operation, and the bound itself
   refers to internal rounded values that the caller doesn't directly
   see.

   The magnitude-bounded interface replaces those seven checks with one
   coordinate-magnitude bound per input.  Concrete choice: every
   coordinate has `Rabs (B2R coord) <= 2^500`.  This is comfortably below
   the overflow threshold (`2^1024`); the chain of intermediate
   operations in `b64_orient2d` (four subtractions producing values up to
   `2^501`, two multiplications producing values up to `2^1002`, one
   outer subtraction producing values up to `2^1003`) never approaches
   overflow.

   With this interface a downstream caller writes one `b64_coord_safe`
   per coordinate and gets the corresponding `b64_safe op` predicates
   for free through the helpers below.
   ============================================================================ *)

(* Helper: `bpow radix2 (e + 1) = 2 * bpow radix2 e`.  Needed throughout *)
(* the magnitude chain below; centralised to avoid re-deriving the      *)
(* `IZR (radix_val radix2) = 2` step inline.                            *)
Lemma bpow_succ_radix2 :
  forall e : Z, bpow radix2 (e + 1) = 2 * bpow radix2 e.
Proof.
  intros e.
  rewrite bpow_plus.
  rewrite bpow_1.
  simpl.
  ring.
Qed.

(* The Valid_exp instance for `SpecFloat.fexp prec emax`.  Flocq's       *)
(* `FLT_exp_valid` covers the FLT form `FLT_exp emin prec`; we bridge    *)
(* via `change` because `SpecFloat.fexp prec emax` is definitionally     *)
(* `FLT_exp (3 - emax - prec) prec` but Coq's typeclass resolution does  *)
(* not see through the definitional unfolding.  Registering this         *)
(* instance lets `round_le` and other Flocq lemmas resolve their         *)
(* implicit `Valid_exp` hypotheses automatically.                         *)
Instance valid_exp_b64_fexp : Valid_exp (SpecFloat.fexp prec emax).
Proof.
  change (SpecFloat.fexp prec emax) with (FLT_exp (3 - emax - prec) prec).
  apply FLT_exp_valid.
  exact prec_gt_0_b64.
Qed.

(* The magnitude bound chosen for safe orient2d (and similar few-step      *)
(* compositions).  `bpow radix2 500 ≈ 3.3 * 10^150`.  Leaves ~24 binades  *)
(* of headroom before overflow, enough for orient2d's three-stage chain.  *)
Definition b64_safe_coord_bound : R := bpow radix2 500.

(* A binary64 value is "coord-safe" if it is finite and its R-image lies *)
(* within the coordinate bound above.  Six of these per orient2d call    *)
(* (one per coordinate of the three input points) is enough to discharge *)
(* every `b64_safe` obligation in `b64_orient2d_safe`.                    *)
Definition b64_coord_safe (x : binary64) : Prop :=
  Binary.is_finite prec emax x = true /\
  Rabs (Binary.B2R prec emax x) <= b64_safe_coord_bound.

(* The bound is positive; used throughout the chain. *)
Lemma b64_safe_coord_bound_pos : 0 < b64_safe_coord_bound.
Proof. unfold b64_safe_coord_bound. apply bpow_gt_0. Qed.

(* `bpow e` is in the FLT format when `e + 1 - prec >= emin`, i.e. for     *)
(* binary64 when `e >= -1020`.  Our chain only uses bpow at e in [500,    *)
(* 1010], well within range.  Phrased as a re-usable helper.              *)
Lemma generic_format_bpow_b64 :
  forall e : Z,
    (3 - emax <= e + 1)%Z ->
    generic_format radix2 (SpecFloat.fexp prec emax) (bpow radix2 e).
Proof.
  intros e He.
  apply generic_format_bpow.
  change (SpecFloat.fexp prec emax (e + 1))
    with (Z.max (e + 1 - 53) (3 - 1024 - 53)).
  unfold prec, emax in He.
  apply Z.max_lub; lia.
Qed.

(* Round-to-nearest-even preserves the magnitude bound `bpow e` whenever  *)
(* the input's magnitude is already `<= bpow e`, provided bpow e is in    *)
(* the format (the side-condition discharged by `generic_format_bpow_b64`).*)
Lemma b64_round_abs_le_bpow :
  forall x : R, forall e : Z,
    (3 - emax <= e + 1)%Z ->
    Rabs x <= bpow radix2 e ->
    Rabs (b64_round x) <= bpow radix2 e.
Proof.
  intros x e He Hx.
  pose proof (generic_format_bpow_b64 e He) as Hfmt.
  pose proof (generic_format_opp _ _ _ Hfmt) as Hfmt_neg.
  apply Rabs_le_inv in Hx.
  apply Rabs_le.
  split.
  - rewrite <- (round_generic radix2 (SpecFloat.fexp prec emax)
                  (round_mode mode_b64) (- bpow radix2 e) Hfmt_neg).
    apply (round_le radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64)).
    tauto.
  - rewrite <- (round_generic radix2 (SpecFloat.fexp prec emax)
                  (round_mode mode_b64) (bpow radix2 e) Hfmt).
    apply (round_le radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64)).
    tauto.
Qed.

(* Coord-safe operands give a safe `b64_minus`: the rounded difference   *)
(* has magnitude at most `bpow 501`, well below `bpow emax = bpow 1024`. *)
Lemma b64_safe_minus_of_bounded :
  forall x y : binary64,
    b64_coord_safe x -> b64_coord_safe y ->
    b64_safe Rminus x y.
Proof.
  intros x y [Fx Hx] [Fy Hy].
  unfold b64_safe.
  split; [exact Fx | split; [exact Fy | ]].
  apply (Rle_lt_trans _ (bpow radix2 501)).
  - apply b64_round_abs_le_bpow.
    + unfold emax. lia.
    + unfold Rminus.
      apply (Rle_trans _ (Rabs (Binary.B2R prec emax x)
                          + Rabs (- Binary.B2R prec emax y))).
      * apply Rabs_triang.
      * rewrite Rabs_Ropp.
        unfold b64_safe_coord_bound in Hx, Hy.
        replace 501%Z with (500 + 1)%Z by lia.
        rewrite bpow_succ_radix2.
        lra.
  - apply bpow_lt. unfold emax. lia.
Qed.

(* The result of a coord-safe `b64_minus` is itself bounded by `bpow 501`,  *)
(* and is finite.  Needed for chaining: the products in orient2d multiply   *)
(* these differences, so we need bounds on them.                            *)
Lemma b64_minus_bounded_R :
  forall x y : binary64,
    b64_coord_safe x -> b64_coord_safe y ->
    Rabs (Binary.B2R prec emax (b64_minus x y)) <= bpow radix2 501
    /\ Binary.is_finite prec emax (b64_minus x y) = true.
Proof.
  intros x y Hx Hy.
  pose proof (b64_safe_minus_of_bounded _ _ Hx Hy) as Hsafe.
  pose proof (b64_minus_correct _ _ Hsafe) as [HB2R Hfin].
  split; [|exact Hfin].
  rewrite HB2R.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  destruct Hx as [_ Hx_bound].
  destruct Hy as [_ Hy_bound].
  unfold Rminus.
  apply (Rle_trans _ (Rabs (Binary.B2R prec emax x)
                      + Rabs (- Binary.B2R prec emax y))).
  - apply Rabs_triang.
  - rewrite Rabs_Ropp.
    unfold b64_safe_coord_bound in Hx_bound, Hy_bound.
    replace 501%Z with (500 + 1)%Z by lia.
    rewrite bpow_succ_radix2.
    lra.
Qed.

(* The mult counterpart: if both operands are bounded by bpow 501 (the     *)
(* output of one coord-safe minus), the rounded product is bounded by     *)
(* bpow 1002 and finite.                                                    *)
Lemma b64_mult_bounded_R :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Rabs (Binary.B2R prec emax x) <= bpow radix2 501 ->
    Rabs (Binary.B2R prec emax y) <= bpow radix2 501 ->
    Rabs (Binary.B2R prec emax (b64_mult x y)) <= bpow radix2 1002
    /\ Binary.is_finite prec emax (b64_mult x y) = true.
Proof.
  intros x y Fx Fy Hx Hy.
  assert (Hsafe : b64_safe Rmult x y).
  { repeat split; try assumption.
    apply (Rle_lt_trans _ (bpow radix2 1002)).
    - apply b64_round_abs_le_bpow; [unfold emax; lia |].
      rewrite Rabs_mult.
      replace 1002%Z with (501 + 501)%Z by lia.
      rewrite bpow_plus.
      apply Rmult_le_compat; try apply Rabs_pos; assumption.
    - apply bpow_lt. unfold emax. lia. }
  pose proof (b64_mult_correct _ _ Hsafe) as [HB2R Hfin].
  split; [|exact Hfin].
  rewrite HB2R.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  rewrite Rabs_mult.
  replace 1002%Z with (501 + 501)%Z by lia.
  rewrite bpow_plus.
  apply Rmult_le_compat; try apply Rabs_pos; assumption.
Qed.

(* Finally, the outer subtraction in orient2d: if both products are       *)
(* bounded by bpow 1002, their rounded difference is bounded by bpow 1003 *)
(* and finite -- and `bpow 1003 < bpow emax = bpow 1024`, so we have a    *)
(* safe outer minus.                                                       *)
Lemma b64_safe_minus_of_products_bounded :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Rabs (Binary.B2R prec emax x) <= bpow radix2 1002 ->
    Rabs (Binary.B2R prec emax y) <= bpow radix2 1002 ->
    b64_safe Rminus x y.
Proof.
  intros x y Fx Fy Hx Hy.
  unfold b64_safe.
  split; [exact Fx | split; [exact Fy | ]].
  apply (Rle_lt_trans _ (bpow radix2 1003)).
  - apply b64_round_abs_le_bpow; [unfold emax; lia |].
    unfold Rminus.
    apply (Rle_trans _ (Rabs (Binary.B2R prec emax x)
                        + Rabs (- Binary.B2R prec emax y))).
    + apply Rabs_triang.
    + rewrite Rabs_Ropp.
      replace 1003%Z with (1002 + 1)%Z by lia.
      rewrite bpow_succ_radix2.
      lra.
  - apply bpow_lt. unfold emax. lia.
Qed.

(* ============================================================================
   Forward-error lemmas (Slice 2 of the Phase 0 chokepoint).
   ----------------------------------------------------------------------------
   Per-operation bounds on `|B2R(b64_op x y) - exact_op(B2R x, B2R y)|`.
   Building blocks for the eventual Shewchuk Stage A forward-error
   theorem (Slice 2 deliverable) and from there the cross_R-valued
   soundness theorem (Slice 3) in `Orient_b64_sound.v`.

   Two flavours each:

   - **Absolute** -- `Rabs (error) <= ulp (exact_op (B2R x) (B2R y))`.
     Unconditional (no normal-range precondition).  Looser bound but
     always applicable.  Builds on `error_le_ulp` from
     `Flocq.Core.Ulp`.

   - **Relative** (deferred).  `Rabs (error) <= (1/2) * bpow(-prec+1) *
     Rabs (exact_op ...)`.  Tighter (this is the eps_half = 2^-52 form
     that Shewchuk's analysis uses), but conditional on the exact
     value being above the smallest normal binary64 magnitude
     (`bpow (emin + prec - 1) = bpow (-1022)`).  Builds on
     `Prop.Relative.relative_error_N_FLT`.

   The absolute version below is sufficient to *state* the chain
   bound; the relative version is what's needed to *match*
   Shewchuk's specific `(3 + 16 * eps) * eps` coefficient.  The
   relative-version lemmas are documented in PROOF STATUS as
   the next slice.
   ============================================================================ *)

Lemma b64_minus_abs_error :
  forall x y : binary64,
    b64_safe Rminus x y ->
    Rabs (Binary.B2R prec emax (b64_minus x y)
          - (Binary.B2R prec emax x - Binary.B2R prec emax y))
      <= ulp radix2 (SpecFloat.fexp prec emax)
                    (Binary.B2R prec emax x - Binary.B2R prec emax y).
Proof.
  intros x y Hsafe.
  pose proof (b64_minus_correct _ _ Hsafe) as [HB2R _].
  rewrite HB2R.
  apply (error_le_ulp radix2 (SpecFloat.fexp prec emax)
                      (round_mode mode_b64)).
Qed.

Lemma b64_plus_abs_error :
  forall x y : binary64,
    b64_safe Rplus x y ->
    Rabs (Binary.B2R prec emax (b64_plus x y)
          - (Binary.B2R prec emax x + Binary.B2R prec emax y))
      <= ulp radix2 (SpecFloat.fexp prec emax)
                    (Binary.B2R prec emax x + Binary.B2R prec emax y).
Proof.
  intros x y Hsafe.
  pose proof (b64_plus_correct _ _ Hsafe) as [HB2R _].
  rewrite HB2R.
  apply (error_le_ulp radix2 (SpecFloat.fexp prec emax)
                      (round_mode mode_b64)).
Qed.

Lemma b64_mult_abs_error :
  forall x y : binary64,
    b64_safe Rmult x y ->
    Rabs (Binary.B2R prec emax (b64_mult x y)
          - Binary.B2R prec emax x * Binary.B2R prec emax y)
      <= ulp radix2 (SpecFloat.fexp prec emax)
                    (Binary.B2R prec emax x * Binary.B2R prec emax y).
Proof.
  intros x y Hsafe.
  pose proof (b64_mult_correct _ _ Hsafe) as [HB2R _].
  rewrite HB2R.
  apply (error_le_ulp radix2 (SpecFloat.fexp prec emax)
                      (round_mode mode_b64)).
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
Print Assumptions b64_safe_minus_of_bounded.
Print Assumptions b64_mult_bounded_R.
Print Assumptions b64_plus_abs_error.
Print Assumptions b64_minus_abs_error.
Print Assumptions b64_mult_abs_error.
