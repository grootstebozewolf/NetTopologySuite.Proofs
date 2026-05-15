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

   Path 2 (shipped, Qed-closed): cross_R-valued soundness restricted to
   the integer regime, in `Orient_b64_exact.v`.

     Theorem b64_orient_sign_filtered_sound_small_int :
       forall P0 P1 Q,
         orient2d_inputs_int_safe P0 P1 Q ->
         match b64_orient_sign_filtered P0 P1 Q with
         | OrientRPos       => 0 < cross_R_BP P0 P1 Q
         | OrientRNeg       => cross_R_BP P0 P1 Q < 0
         | OrientRZero      => cross_R_BP P0 P1 Q = 0
         | OrientRNan       => True
         | OrientRUncertain => True
         end.

   `orient2d_inputs_int_safe` says each input coordinate is an integer-
   valued binary64 with `|coord| <= 2^25`.  In that regime every
   intermediate value in the orient2d chain stays within binary64's
   53-bit integer-exactness window, so `B2R det = cross_R_BP` on the
   nose -- composing with this file's decoder-consistency lemma gives
   the headline.

   Companion R-side identities in the same regime (Orient_b64_exact.v):
     - b64_orient2d_cyclic_int_R, _cyclic2_int_R -- the two cyclic
       permutations of (P0, P1, Q).

   And in `Orient_b64_R.v` under the safe-magnitude regime:
     - b64_orient2d_antisymmetric_R
     - b64_orient2d_at_P0_R, _at_P1_R, _at_P0_eq_P1_R -- vertex
       coincidences and degenerate base.

   Open (and the only remaining gap for Phase 0 soundness): cross_R
   soundness for the *general* bounded-magnitude regime
   `b64_orient2d_inputs_safe` (`|coord| <= 2^500`).  Closing it
   requires Shewchuk's Stages B/C/D -- in particular Stage D
   (renormalization + reliable sign-of-expansion extraction), which is
   qualitatively harder than the work shipped so far.  See
   `docs/soundness-strategy.md` for the consolidation discussion.

   Path 1 below (forward-error analysis) is the alternative angle on
   the same gap.  Slice 2a is in B64_bridge.v; remaining slices are
   scaffolding-heavy and were demoted from critical path on 2026-05-15.

   Under Path 1 the general theorem would require the Shewchuk Stage A
   forward-error bound:

     Theorem b64_orient2d_forward_error :
       forall P0 P1 Q,
         b64_orient2d_inputs_safe P0 P1 Q ->
         Rabs (B2R (b64_orient2d P0 P1 Q) - cross_R_BP P0 P1 Q)
           <= B2R b64_errbound_A_coeff * b64_detsum_R P0 P1 Q.

   Building blocks now in `B64_bridge.v` (Slice 2a, shipped this commit):

     b64_plus_abs_error :  Rabs (B2R (b64_plus x y) - (B2R x + B2R y))
                           <= ulp (B2R x + B2R y).
     b64_minus_abs_error : analogous for `b64_minus`.
     b64_mult_abs_error  : analogous for `b64_mult`.

   These give per-operation absolute error bounds (unconditional --
   no normal-range precondition).  Loose: `ulp v` is up to `bpow(-prec+1)
   * |v|` for normal v, so the bound is a constant factor worse than
   the relative-error version below.

   Still pending (Slice 2b, ~1-2 sessions):

     Relative-error versions: `b64_*_rel_error` giving
       `Rabs (error) <= (1/2) * bpow(-prec+1) * Rabs (exact_op ...)`
     under the precondition that `Rabs (exact_op ...) >= bpow(emin + prec - 1)`
     (above the smallest normal binary64).  Builds on
     `Prop.Relative.relative_error_N_FLT`.  These are what Shewchuk's
     analysis directly uses.

   Still pending (Slice 2c, ~2-3 sessions):

     Chain composition: thread the per-op errors through the four
     `b64_minus` / two `b64_mult` / outer `b64_minus` chain of
     `b64_orient2d` to derive the Shewchuk Stage A bound
     `(3 + 16 * eps) * eps * (|t1| + |t2|)`.  The "3 * eps" is the
     contribution of three rounding operations (two products + outer
     subtraction); the "16 * eps" is higher-order cross terms.

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
