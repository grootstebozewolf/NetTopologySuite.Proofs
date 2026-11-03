(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_AbsErr
   ----------------------------------------------------------------------------
   Absolute error of one binary64 round-to-nearest-even operation, in the
   form forward-error proofs compose:
     |fl(x op y) - (x op y)| <= u |x op y| + e0,   u = 2^-53, e0 = 2^-1075,
   valid for normal AND subnormal results (Flocq error_N_FLT), with
   finiteness discharged from a |x op y| <= 2^1000 magnitude premise.
   Moved verbatim from ClothoidArcSpline_b64.v (prefix cas_ renamed b64ae_) so
   the polynomial kernel B64_Horner.v reuses it instead of a copy.
   claimId: none.  No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* Unit roundoff of binary64 round-to-nearest. *)
Definition b64ae_u : R := bpow radix2 (-53).

Lemma b64ae_u_small : 0 < b64ae_u <= / 1000.
Proof.
  unfold b64ae_u. split; [apply bpow_gt_0|].
  apply Rle_trans with (bpow radix2 (-10)).
  - apply bpow_le. lia.
  - cbn. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Absolute error of one RNE op (normal or subnormal, no overflow).          *)
(* -------------------------------------------------------------------------- *)

(* Half the smallest subnormal: the absolute floor of an RNE rounding. *)
Definition b64ae_e0 : R := bpow radix2 (-1075).

Lemma b64ae_e0_small : 0 < b64ae_e0 <= / 1000.
Proof.
  unfold b64ae_e0. split; [apply bpow_gt_0|].
  apply Rle_trans with (bpow radix2 (-10)).
  - apply bpow_le. lia.
  - cbn. lra.
Qed.

Lemma b64ae_round_err : forall z,
  Rabs (b64_round z - z) <= b64ae_u * Rabs z + b64ae_e0.
Proof.
  intro z.
  destruct (error_N_FLT radix2 (3 - emax - prec) prec prec_gt_0_b64
              (fun t => negb (Z.even t)) z) as [d [e [Hd [He [_ Hr]]]]].
  assert (Hr' : b64_round z = z * (1 + d) + e) by exact Hr.
  rewrite Hr'.
  replace (z * (1 + d) + e - z) with (z * d + e) by ring.
  assert (Eu : / 2 * bpow radix2 (- prec + 1) = b64ae_u).
  { unfold b64ae_u, prec. replace (/ 2) with (bpow radix2 (-1)) by reflexivity.
    rewrite <- bpow_plus. f_equal. }
  assert (Ee : / 2 * bpow radix2 (3 - emax - prec) = b64ae_e0).
  { unfold b64ae_e0, emax, prec. replace (/ 2) with (bpow radix2 (-1)) by reflexivity.
    rewrite <- bpow_plus. f_equal. }
  rewrite Eu in Hd. rewrite Ee in He.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_mult.
  pose proof (Rabs_pos z).
  apply Rplus_le_compat; [|exact He].
  rewrite Rmult_comm. apply Rmult_le_compat_r; [exact H | exact Hd].
Qed.

Lemma b64ae_safe_of : forall (op : R -> R -> R) x y,
  fin x = true -> fin y = true ->
  Rabs (op (B2R x) (B2R y)) <= bpow radix2 1000 -> b64_safe op x y.
Proof.
  intros op x y Fx Fy Hb. split; [exact Fx|]. split; [exact Fy|].
  eapply Rle_lt_trans.
  - apply (b64_round_abs_le_bpow _ 1000); [unfold emax; lia | exact Hb].
  - apply bpow_lt. unfold emax. lia.
Qed.

Lemma b64ae_mult_err : forall x y,
  fin x = true -> fin y = true ->
  Rabs (B2R x * B2R y) <= bpow radix2 1000 ->
  fin (b64_mult x y) = true /\
  Rabs (B2R (b64_mult x y) - B2R x * B2R y)
    <= b64ae_u * Rabs (B2R x * B2R y) + b64ae_e0.
Proof.
  intros x y Fx Fy Hb.
  destruct (b64_mult_correct x y (b64ae_safe_of Rmult x y Fx Fy Hb)) as [E F].
  split; [exact F|]. rewrite E. apply b64ae_round_err.
Qed.

Lemma b64ae_plus_err : forall x y,
  fin x = true -> fin y = true ->
  Rabs (B2R x + B2R y) <= bpow radix2 1000 ->
  fin (b64_plus x y) = true /\
  Rabs (B2R (b64_plus x y) - (B2R x + B2R y))
    <= b64ae_u * Rabs (B2R x + B2R y) + b64ae_e0.
Proof.
  intros x y Fx Fy Hb.
  destruct (b64_plus_correct x y (b64ae_safe_of Rplus x y Fx Fy Hb)) as [E F].
  split; [exact F|]. rewrite E. apply b64ae_round_err.
Qed.

Lemma b64ae_minus_err : forall x y,
  fin x = true -> fin y = true ->
  Rabs (B2R x - B2R y) <= bpow radix2 1000 ->
  fin (b64_minus x y) = true /\
  Rabs (B2R (b64_minus x y) - (B2R x - B2R y))
    <= b64ae_u * Rabs (B2R x - B2R y) + b64ae_e0.
Proof.
  intros x y Fx Fy Hb.
  destruct (b64_minus_correct x y (b64ae_safe_of Rminus x y Fx Fy Hb)) as [E F].
  split; [exact F|]. rewrite E. apply b64ae_round_err.
Qed.

Lemma b64ae_abs_mult_le : forall p q P Q,
  Rabs p <= P -> Rabs q <= Q -> Rabs (p * q) <= P * Q.
Proof.
  intros. rewrite Rabs_mult.
  apply Rmult_le_compat; try apply Rabs_pos; assumption.
Qed.

Lemma b64ae_u_mul_le : forall z M, Rabs z <= M -> b64ae_u * Rabs z <= b64ae_u * M.
Proof.
  intros z M H. apply Rmult_le_compat_l; [|exact H].
  apply Rlt_le, b64ae_u_small.
Qed.


Print Assumptions b64ae_u_small.
Print Assumptions b64ae_e0_small.
Print Assumptions b64ae_round_err.
Print Assumptions b64ae_safe_of.
Print Assumptions b64ae_mult_err.
Print Assumptions b64ae_plus_err.
Print Assumptions b64ae_minus_err.
Print Assumptions b64ae_abs_mult_le.
Print Assumptions b64ae_u_mul_le.
