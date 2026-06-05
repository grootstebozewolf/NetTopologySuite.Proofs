(* ============================================================================
   NetTopologySuite.Proofs.Flocq.DivRoundPow2_b64
   ----------------------------------------------------------------------------
   The DIVISION-ROUNDING CORE for power-of-two snap grids.

   `SnapRounding_b64.v` proves the snap-rounding correctness invariant on the
   UNIT grid (`scale = 1`), where `snap_round_coord x 1 = round(x * 1) / 1`
   has both the multiply and the divide collapse to no-ops (`Rmult_1_r`,
   `Rdiv_1_r`), so every bridge (`b64_snap_coord_B2R`, idempotence) is clean.

   Generalising to a real grid of spacing `1/scale` with `scale` a POSITIVE
   POWER OF TWO requires controlling the rounding in

       snap_round_coord x scale = round_FIX0 (x * scale) / scale.

   On the R side grid-exactness already holds for ANY `0 < scale`
   (`HotPixel_b64.snap_round_on_grid`).  The hard part is the binary64 side:
   `b64_div`'s rounding step.  This file isolates the load-bearing fact ---

       DIVISION BY A POWER OF TWO IS EXACT.

   When the divisor `s` is a power of two `2^k`, `B2R x / B2R s = v * bpow(-k)`
   only shifts the exponent of the dividend, so it stays in the binary64 FLT
   format and `b64_round` fixes it on the nose.  This mirrors the integer-
   regime exactness lemmas (`b64_mult_int_exact` etc.) in `Orient_b64_exact.v`,
   reusing `generic_format_IZR_le_bpow_prec` (which already handles the
   `|a| = 2^prec` boundary) plus FLT closure under multiplication by `bpow`.

   This is the cleanly-isolated core; later slices wire it into a scaled
   `b64_snap_coord` and lift the unit-grid theorems of `SnapRounding_b64.v`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.
From Flocq Require Import Mult_error.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.

Local Open Scope R_scope.

Local Notation b64_fexp := (SpecFloat.fexp prec emax).
Local Notation b64_round := (round radix2 b64_fexp (round_mode mode_b64)).
Local Notation emin := (3 - emax - prec)%Z.

(* `prec_gt_0_b64` is a `Lemma` (not a registered `Instance`); expose it for
   typeclass resolution so Flocq's FLT lemmas (`mult_bpow_pos_exact_FLT`)
   discharge their `Prec_gt_0 prec` context here. *)
Local Existing Instance prec_gt_0_b64.

(* -------------------------------------------------------------------------- *)
(* Step 1.  `IZR a / bpow k = IZR a * bpow (-k)` -- divide-by-pow2 is a       *)
(* mantissa-preserving exponent shift.                                        *)
(* -------------------------------------------------------------------------- *)

Lemma div_bpow_eq_mult_bpow_neg :
  forall (a : Z) (k : Z),
    IZR a / bpow radix2 k = IZR a * bpow radix2 (- k).
Proof.
  intros a k. unfold Rdiv. rewrite bpow_opp. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Step 2.  Format closure.                                                    *)
(*                                                                            *)
(* The single boundary-complete fact this file (and SnapRoundingScale_b64)    *)
(* leans on: a dyadic `m * 2^e` is in the binary64 FLT format whenever the    *)
(* mantissa fits (`|m| <= 2^prec`) and the exponent is at or above emin.       *)
(* The `|m| = 2^prec` boundary (where `mag = prec+1`) is the pure power of     *)
(* two `bpow (prec + e)`, handled by `generic_format_bpow_b64`; the strict     *)
(* interior goes through `generic_format_F2R` with a `mag` bound.  This is the *)
(* general-exponent analogue of `Orient_b64_exact.generic_format_IZR_le_      *)
(* bpow_prec` (the `e = 0` instance).                                          *)
(* -------------------------------------------------------------------------- *)

Lemma generic_format_F2R_le_pow_prec :
  forall (m e : Z),
    (Z.abs m <= 2 ^ prec)%Z ->
    (emin <= e)%Z ->
    generic_format radix2 b64_fexp (F2R (Float radix2 m e)).
Proof.
  intros m e Hm He.
  destruct (Z.eq_dec m 0) as [-> | Hnz].
  { rewrite F2R_0. apply generic_format_0. }
  destruct (Z.eq_dec (Z.abs m) (2 ^ prec)) as [Hb | Hs].
  - (* boundary |m| = 2^prec: F2R = +/- bpow (prec + e) *)
    assert (HFm : F2R (Float radix2 m e) = IZR m * bpow radix2 e) by reflexivity.
    rewrite HFm.
    destruct (Z_lt_le_dec m 0) as [Hneg | Hpos].
    + assert (Hm_eq : (m = - (2 ^ prec))%Z) by lia.
      rewrite Hm_eq, opp_IZR, <- (bpow_radix2_eq_IZR_pow prec) by (unfold prec; lia).
      replace (- bpow radix2 prec * bpow radix2 e)
        with (- bpow radix2 (prec + e)) by (rewrite bpow_plus; ring).
      apply generic_format_opp, generic_format_bpow_b64.
      unfold prec, emax in *. lia.
    + assert (Hm_eq : (m = 2 ^ prec)%Z) by lia.
      rewrite Hm_eq, <- (bpow_radix2_eq_IZR_pow prec) by (unfold prec; lia).
      rewrite <- bpow_plus.
      apply generic_format_bpow_b64. unfold prec, emax in *. lia.
  - (* strict |m| < 2^prec: F2R route via mag_F2R *)
    apply generic_format_F2R. intros _.
    unfold cexp. rewrite (mag_F2R radix2 m e Hnz).
    assert (Hmag : (mag radix2 (IZR m) <= prec)%Z).
    { apply mag_le_bpow.
      - apply IZR_neq; exact Hnz.
      - rewrite <- abs_IZR, bpow_radix2_eq_IZR_pow by (unfold prec; lia).
        apply IZR_lt; lia. }
    unfold SpecFloat.fexp.
    apply Z.max_lub; unfold SpecFloat.emin, emax, prec in *; lia.
Qed.

(* `IZR a * bpow (-k)` in format: the `e := -k` instance of the F2R lemma. *)
Lemma generic_format_IZR_mult_bpow_neg :
  forall (a k : Z),
    (Z.abs a <= 2 ^ prec)%Z ->
    (emin <= - k)%Z ->
    generic_format radix2 b64_fexp (IZR a * bpow radix2 (- k)).
Proof.
  intros a k Hbound Hk.
  replace (IZR a * bpow radix2 (- k)) with (F2R (Float radix2 a (- k)))
    by (unfold F2R; reflexivity).
  apply generic_format_F2R_le_pow_prec; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Step 3.  THE CORE.  Dividing an integer-valued binary64 by a power-of-two  *)
(* binary64 is bit-exact: the result is `IZR a * bpow(-k)` with no rounding.  *)
(* -------------------------------------------------------------------------- *)

Lemma b64_div_pow2_exact :
  forall (x s : binary64) (a k : Z),
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax s = true ->
    Binary.B2R prec emax x = IZR a ->
    Binary.B2R prec emax s = bpow radix2 k ->
    (Z.abs a <= 2 ^ prec)%Z ->
    (0 <= k)%Z ->
    (emin <= - k)%Z ->
    Binary.B2R prec emax (b64_div x s) = IZR a * bpow radix2 (- k)
    /\ Binary.is_finite prec emax (b64_div x s) = true.
Proof.
  intros x s a k Fx Fs HxR HsR Hbound Hk_pos Hk_fmt.
  (* divisor is nonzero (it is a positive power of two) *)
  assert (Hs_nz : Binary.B2R prec emax s <> 0).
  { rewrite HsR. apply Rgt_not_eq, bpow_gt_0. }
  (* the exact quotient value *)
  assert (Hval : Binary.B2R prec emax x / Binary.B2R prec emax s
                   = IZR a * bpow radix2 (- k)).
  { rewrite HxR, HsR. apply div_bpow_eq_mult_bpow_neg. }
  (* the quotient is already in format, so rounding fixes it *)
  assert (Hfmt : generic_format radix2 b64_fexp (IZR a * bpow radix2 (- k)))
    by (apply generic_format_IZR_mult_bpow_neg; assumption).
  assert (Hround : b64_round (Binary.B2R prec emax x / Binary.B2R prec emax s)
                     = IZR a * bpow radix2 (- k)).
  { rewrite Hval. apply round_generic; [apply valid_rnd_N | exact Hfmt]. }
  (* no overflow: |a * 2^-k| <= 2^prec < 2^emax (k >= 0) *)
  assert (Hbnd : Rabs (b64_round (Binary.B2R prec emax x / Binary.B2R prec emax s))
                   < bpow radix2 emax).
  { rewrite Hround, Rabs_mult.
    rewrite (Rabs_pos_eq (bpow radix2 (- k))) by (apply Rlt_le, bpow_gt_0).
    apply Rle_lt_trans with (bpow radix2 prec).
    - apply Rle_trans with (bpow radix2 prec * bpow radix2 (- k)).
      + apply Rmult_le_compat_r; [apply Rlt_le, bpow_gt_0|].
        rewrite <- abs_IZR.
        rewrite bpow_radix2_eq_IZR_pow by (unfold prec; lia).
        apply IZR_le. exact Hbound.
      + rewrite <- bpow_plus.
        apply bpow_le. lia.
    - apply bpow_lt. unfold prec, emax. lia. }
  pose proof (b64_div_correct x s Fx Fs Hs_nz Hbnd) as [HB2R Hfin].
  split; [rewrite HB2R; exact Hround | exact Hfin].
Qed.

(* -------------------------------------------------------------------------- *)
(* Step 4.  The MULTIPLICATIVE twin.  Multiplying ANY finite binary64 by a    *)
(* power-of-two binary64 is bit-exact (no rounding): it only shifts the       *)
(* exponent.  For a general dividend `x` (not necessarily integer) this is    *)
(* the pre-rounding step of a scaled snap `round(x * scale) / scale`.  No     *)
(* magnitude bound on `a` is available, so no-overflow is taken as a premise  *)
(* (the `b64_safe`-style `Rabs (...) < bpow emax`).  Closure under `* bpow k` *)
(* with `k >= 0` is Flocq's `mult_bpow_pos_exact_FLT`; `B2R x` is in format   *)
(* by `Binary.generic_format_B2R`.                                            *)
(* -------------------------------------------------------------------------- *)

Lemma b64_mult_pow2_exact :
  forall (x s : binary64) (k : Z),
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax s = true ->
    Binary.B2R prec emax s = bpow radix2 k ->
    (0 <= k)%Z ->
    Rabs (Binary.B2R prec emax x * bpow radix2 k) < bpow radix2 emax ->
    Binary.B2R prec emax (b64_mult x s) = Binary.B2R prec emax x * bpow radix2 k
    /\ Binary.is_finite prec emax (b64_mult x s) = true.
Proof.
  intros x s k Fx Fs HsR Hk Hovf.
  assert (Hfmt_x : generic_format radix2 b64_fexp (Binary.B2R prec emax x))
    by apply (Binary.generic_format_B2R prec emax x).
  assert (Hfmt : generic_format radix2 b64_fexp
                   (Binary.B2R prec emax x * bpow radix2 k)).
  { change (SpecFloat.fexp prec emax) with (FLT_exp (3 - emax - prec) prec).
    apply mult_bpow_pos_exact_FLT; [exact Hfmt_x | exact Hk]. }
  assert (Hround : b64_round (Binary.B2R prec emax x * Binary.B2R prec emax s)
                     = Binary.B2R prec emax x * bpow radix2 k).
  { rewrite HsR. apply round_generic; [apply valid_rnd_N | exact Hfmt]. }
  assert (Hsafe : b64_safe Rmult x s).
  { unfold b64_safe. split; [exact Fx | split; [exact Fs|]].
    rewrite Hround. exact Hovf. }
  pose proof (b64_mult_correct x s Hsafe) as [HB2R Hfin].
  split; [rewrite HB2R; exact Hround | exact Hfin].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_div_pow2_exact.
Print Assumptions b64_mult_pow2_exact.
