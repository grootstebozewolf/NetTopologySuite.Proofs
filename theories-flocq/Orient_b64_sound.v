(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_sound
   ----------------------------------------------------------------------------
   Soundness bridge for `b64_orient_sign_filtered`.  Connects the five-valued
   sign decoder of the Stage A filter to the (a) sign of the binary64
   `b64_orient2d` value (this file) and, eventually, (b) the exact R-valued
   cross product (next slice, see PROOF STATUS).

   PROOF STATUS
   ============
   - `cross_R_BP P0 P1 Q`                  -- defined.  The exact R-valued
                                              cross product on `BPoint` inputs
                                              via `B2R` on each coordinate.
                                              No rounding: the mathematical
                                              standard against which the
                                              binary64 evaluation is compared.
   - `b64_orient2d_finite_of_safe`         -- proved.  Under
                                              `b64_orient2d_safe`, the result
                                              of `b64_orient2d P0 P1 Q` is
                                              `is_finite = true`.
   - `b64_orient_sign_filtered_consistent_with_b64` -- proved.  The five-
                                              valued sign decoder is
                                              consistent with the sign of
                                              the rounded binary64 value:
                                              OrientRPos / OrientRNeg /
                                              OrientRZero match the sign of
                                              `B2R (b64_orient2d ...)`;
                                              OrientRNan and OrientRUncertain
                                              make no claim.

   NOT YET claimed (the real-valued soundness):
     Theorem b64_orient_sign_filtered_sound :
       forall P0 P1 Q,
         b64_orient2d_inputs_safe P0 P1 Q ->
         match b64_orient_sign_filtered P0 P1 Q with
         | OrientRPos       => 0 < cross_R_BP P0 P1 Q
         | OrientRNeg       => cross_R_BP P0 P1 Q < 0
         | OrientRZero      => cross_R_BP P0 P1 Q = 0   (* may need adjusting *)
         | OrientRNan       => True
         | OrientRUncertain => True
         end.

   This theorem requires the Shewchuk Stage A forward-error bound:

     Theorem b64_orient2d_forward_error :
       forall P0 P1 Q,
         b64_orient2d_inputs_safe P0 P1 Q ->
         Rabs (B2R (b64_orient2d P0 P1 Q) - cross_R_BP P0 P1 Q)
           <= B2R b64_errbound_A_coeff * b64_detsum_R P0 P1 Q.

   The forward-error theorem in turn needs per-op forward-error lemmas
   (`Plus_error.plus_error`, `Mult_error.mult_error_FLT`, etc.) plus an
   accumulation analysis through the four `b64_minus` and two `b64_mult`
   sub-operations.  That is the substantive proof slice -- approximately
   1-3 days of focused work, mirroring Shewchuk 1997 §4.

   Once the forward-error theorem lands, the cross_R soundness follows
   mechanically from this file's decoder-consistency lemma:
     filter passes => |B2R det| > errbound (filter check)
     forward error => |B2R det - cross_R| <= errbound (Stage A bound)
     subtraction  => sign(cross_R) = sign(B2R det)
     consistency  => sign(B2R det) = sign returned by the decoder.

   No `Admitted`, no `Axiom`, no `Parameter`.  The corpus invariant holds:
   the slice 2 / 3 statements above are prose comments, not Coq syntax.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import Orient_b64_R.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The exact mathematical cross product on `BPoint` inputs.  Each coordinate *)
(* is lifted to R via `Binary.B2R`; the cross product itself is computed in   *)
(* exact R-arithmetic, no rounding.  This is the standard the binary64       *)
(* `b64_orient2d` evaluation is eventually compared against in slice 2/3.    *)
(* -------------------------------------------------------------------------- *)

Definition cross_R_BP (P0 P1 Q : BPoint) : R :=
  (Binary.B2R prec emax (bx P1)  - Binary.B2R prec emax (bx P0))
  * (Binary.B2R prec emax (by_ Q) - Binary.B2R prec emax (by_ P0))
  - (Binary.B2R prec emax (bx Q)  - Binary.B2R prec emax (bx P0))
  * (Binary.B2R prec emax (by_ P1) - Binary.B2R prec emax (by_ P0)).

(* -------------------------------------------------------------------------- *)
(* Finiteness of `b64_orient2d P0 P1 Q` chains directly out of                *)
(* `b64_orient2d_safe`: every safe predicate carries finiteness of its       *)
(* operands, and `b64_minus_correct` / `b64_mult_correct` carry finiteness    *)
(* of their result.                                                            *)
(* -------------------------------------------------------------------------- *)

Lemma b64_orient2d_finite_of_safe :
  forall P0 P1 Q : BPoint,
    b64_orient2d_safe P0 P1 Q ->
    Binary.is_finite prec emax (b64_orient2d P0 P1 Q) = true.
Proof.
  intros P0 P1 Q (_ & _ & _ & _ & _ & _ & Sdet).
  pose proof (b64_minus_correct _ _ Sdet) as [_ Fdet].
  unfold b64_orient2d, Orientation_b64.b64_orient2d_terms.
  cbn iota.
  exact Fdet.
Qed.

(* -------------------------------------------------------------------------- *)
(* Decoder consistency.                                                       *)
(*                                                                            *)
(* Under `b64_orient2d_safe`, the five-valued sign decoder agrees with the   *)
(* sign of the rounded binary64 value.  In particular: OrientRPos appears    *)
(* exactly when `B2R (b64_orient2d ...) > 0`, OrientRNeg when `< 0`, and     *)
(* OrientRZero when `= 0`.  OrientRNan and OrientRUncertain make no claim   *)
(* about `B2R (b64_orient2d ...)` -- by design, those are the cases where   *)
(* the predicate refuses to commit.                                           *)
(*                                                                            *)
(* This is the "internal consistency" half of soundness.  The cross_R-       *)
(* valued half (slice 2/3) requires the Shewchuk Stage A forward-error      *)
(* bound; see PROOF STATUS in the header.                                    *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient_sign_filtered_consistent_with_b64 :
  forall P0 P1 Q : BPoint,
    b64_orient2d_safe P0 P1 Q ->
    match b64_orient_sign_filtered P0 P1 Q with
    | OrientRPos       => 0 < Binary.B2R prec emax (b64_orient2d P0 P1 Q)
    | OrientRNeg       => Binary.B2R prec emax (b64_orient2d P0 P1 Q) < 0
    | OrientRZero      => Binary.B2R prec emax (b64_orient2d P0 P1 Q) = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hsafe.
  pose proof (b64_orient2d_finite_of_safe _ _ _ Hsafe) as Fdet.
  assert (Fzero : Binary.is_finite prec emax
                    (Binary.B754_zero prec emax false) = true)
    by reflexivity.
  (* Universal `b64_compare _ zero` rewrite, instantiable at any finite     *)
  (* operand.  Avoids syntactic-equality issues with the let-bound `det`    *)
  (* inside `b64_orient_sign_filtered`: the rewrite finds `det` by          *)
  (* unification, with `Fdet` discharging the finiteness side-condition.   *)
  assert (Hcmp_gen : forall d : binary64,
            Binary.is_finite prec emax d = true ->
            b64_compare d (Binary.B754_zero prec emax false)
            = Some (Rcompare (Binary.B2R prec emax d) 0)).
  { intros d Fd.
    unfold b64_compare.
    rewrite (Binary.Bcompare_correct prec emax _ _ Fd Fzero).
    replace (Binary.B2R prec emax
               (Binary.B754_zero prec emax false)) with 0 by reflexivity.
    reflexivity. }
  unfold b64_orient_sign_filtered, b64_orient2d,
         Orientation_b64.b64_orient2d_terms in *.
  cbv beta iota in *.
  rewrite Hcmp_gen by exact Fdet.
  destruct (Rcompare _ 0) eqn:Ecmp.
  - apply Rcompare_Eq_inv. exact Ecmp.
  - apply Rcompare_Lt_inv in Ecmp.
    destruct (b64_compare _ _) as [c|]; [destruct c|]; cbn; auto.
  - apply Rcompare_Gt_inv in Ecmp.
    destruct (b64_compare _ _) as [c|]; [destruct c|]; cbn; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient2d_finite_of_safe.
Print Assumptions b64_orient_sign_filtered_consistent_with_b64.
