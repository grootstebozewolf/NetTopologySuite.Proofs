(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_R
   ----------------------------------------------------------------------------
   R-side arithmetic identities for `b64_orient2d`, proved via composition of
   the per-op correctness lifts in `B64_bridge.v`.

   PROOF STATUS
   ============
   Currently in the file:
     - `b64_orient2d_safe P0 P1 Q`         -- bundled no-overflow precondition
                                              for one call to `b64_orient2d`.
     - `b64_orient2d_antisymmetric_R`      -- swapping the last two arguments
                                              negates the R-valued result.
                                              Holds because the intermediate
                                              binary64 values are identical
                                              between the two calls and
                                              `round_NE_opp` closes the outer
                                              subtraction.
     - `b64_orient2d_at_P0_R`              -- vertex coincidence Q = P0: the
                                              R-valued result is exactly
                                              zero, no rounding error.

   Deliberately not here (with reasons):
     - Cyclic permutation `B2R (b64_orient2d A B C) = B2R (b64_orient2d B C A)`.
       The two calls compute *different* intermediate `b64_minus` and
       `b64_mult` values; lifting via `b64_*_correct` produces nested
       `b64_round(b64_round(...) * b64_round(...))` terms that are not
       syntactically equal under cyclic permutation.  In R-arithmetic the
       identity holds by `ring`; in binary64 the accumulated rounding
       errors don't structurally cancel.  Provable only with much stronger
       preconditions (Sterbenz exactness on every subtraction), or as an
       error-bounded version.  Deferred.
     - Translation invariance.  Same issue -- `(x + v) - (y + v)` in
       binary64 is generally not equal to `x - y` after rounding.
       Sterbenz exactness can rescue it in restricted regimes; full
       generality needs more work.  Deferred.
     - Magnitude-bounded variant of the precondition + the
       "bounded inputs imply safe chain" helper (Flavour B in the audit
       discussion).  One-time work that buys easier callers; do
       immediately after the remaining vertex-coincidence theorems.

   What's true about cyclic / translation but not directly Provable here:
   they hold for the *exact* ℝ-valued `cross` predicate in
   `theories/Orientation.v`, just not for its binary64 evaluation.
   The eventual `b64_orient2d_exact_sound` theorem (Shewchuk Stages B/C)
   restores them by routing `OrientRUncertain` through expansion
   arithmetic.

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

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* `b64_orient2d_safe P0 P1 Q` -- the seven no-overflow obligations for one   *)
(* call to `b64_orient2d`, one per sub-operation, packaged as a single Prop. *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient2d_safe (P0 P1 Q : BPoint) : Prop :=
  let dx1 := b64_minus (bx P1) (bx P0) in
  let dy1 := b64_minus (by_ Q)  (by_ P0) in
  let dx2 := b64_minus (bx Q)   (bx P0) in
  let dy2 := b64_minus (by_ P1) (by_ P0) in
  let t1  := b64_mult dx1 dy1 in
  let t2  := b64_mult dx2 dy2 in
  b64_safe Rminus (bx P1) (bx P0) /\
  b64_safe Rminus (by_ Q)  (by_ P0) /\
  b64_safe Rminus (bx Q)   (bx P0) /\
  b64_safe Rminus (by_ P1) (by_ P0) /\
  b64_safe Rmult  dx1 dy1 /\
  b64_safe Rmult  dx2 dy2 /\
  b64_safe Rminus t1 t2.

(* -------------------------------------------------------------------------- *)
(* Antisymmetry on the R-side.                                                *)
(*                                                                            *)
(* The two calls `b64_orient2d P0 P1 Q` and `b64_orient2d P0 Q P1` share      *)
(* identical intermediate binary64 values (`dx1`, `dy1`, `dx2`, `dy2`, `t1`,  *)
(* `t2`) -- the only difference is the order of arguments to the outermost   *)
(* `b64_minus`.  At the R-level, `round_NE` is symmetric under negation, so  *)
(* the two R-valued results are exact negatives of each other under the      *)
(* no-overflow preconditions.                                                 *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_antisymmetric_R :
  forall P0 P1 Q : BPoint,
    b64_orient2d_safe P0 P1 Q ->
    b64_orient2d_safe P0 Q  P1 ->
    Binary.B2R prec emax (b64_orient2d P0 P1 Q)
      = - Binary.B2R prec emax (b64_orient2d P0 Q P1).
Proof.
  intros P0 P1 Q Hsafe1 Hsafe2.
  (* Unpack the seventh conjuncts -- the only ones we need for the proof,    *)
  (* since the outer b64_minus is the only operation whose B2R we compute.   *)
  destruct Hsafe1 as (_ & _ & _ & _ & _ & _ & Sdet1).
  destruct Hsafe2 as (_ & _ & _ & _ & _ & _ & Sdet2).
  (* `b64_orient2d` is defined as `let (t1, t2) := b64_orient2d_terms ... in *)
  (* b64_minus t1 t2`.  Unfold both layers and reduce the let so the goal   *)
  (* contains the same concrete `b64_minus` form that `Sdet1` / `Sdet2`     *)
  (* talk about.                                                             *)
  unfold b64_orient2d, Orientation_b64.b64_orient2d_terms.
  cbn iota.
  (* Lift each outer subtraction to R via b64_minus_correct. *)
  pose proof (b64_minus_correct _ _ Sdet1) as [Hdet1 _].
  pose proof (b64_minus_correct _ _ Sdet2) as [Hdet2 _].
  rewrite Hdet1, Hdet2.
  (* Goal: `round (a - b) = - round (b - a)` for a, b being the two t-values. *)
  (* Pull the negation inside the rounding via `round_NE_opp` (RTL), then    *)
  (* simplify `-(b - a)` to `a - b`.                                         *)
  rewrite <- round_NE_opp.
  rewrite Ropp_minus_distr.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Vertex coincidence: Q = P0.                                                *)
(*                                                                            *)
(* Mirrors `cross_at_P0_is_collinear` from the R-side `Orientation.v`.  In   *)
(* binary64 the identity is genuine (not a rounded approximation): every     *)
(* product collapses to 0 because one factor is the "self minus" subtraction *)
(* `b64_minus z z` whose B2R is exactly 0.  The outer subtraction is then    *)
(* `0 - 0 = 0`.                                                               *)
(*                                                                            *)
(* Preconditions are `b64_safe Rminus` on the two non-self subtractions      *)
(* (`bx P1 - bx P0`, `by_ P1 - by_ P0`).  Those are the only ones whose      *)
(* magnitude is not trivially zero -- they need a no-overflow guard for the  *)
(* downstream `b64_mult` to be finite.  The other five `b64_safe`-style      *)
(* obligations in the full `b64_orient2d_safe` are trivially discharged when *)
(* Q = P0 (everything is `round 0 = 0`).                                     *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_at_P0_R :
  forall P0 P1 : BPoint,
    b64_safe Rminus (bx P1) (bx P0) ->
    b64_safe Rminus (by_ P1) (by_ P0) ->
    Binary.B2R prec emax (b64_orient2d P0 P1 P0) = 0.
Proof.
  intros P0 P1 Hdx Hdy.
  pose proof Hdx as Hdx'.  (* keep an unbroken copy for b64_minus_correct *)
  pose proof Hdy as Hdy'.
  destruct Hdx as (FxP1 & FxP0 & _).
  destruct Hdy as (FyP1 & FyP0 & _).
  unfold b64_orient2d, Orientation_b64.b64_orient2d_terms.
  cbn iota.
  (* Self-minus on by_ P0 and bx P0 both give R-zero, finite results. *)
  pose proof (b64_minus_self_R (by_ P0) FyP0) as Hdy1_R.
  pose proof (b64_minus_self_finite (by_ P0) FyP0) as Fdy1.
  pose proof (b64_minus_self_R (bx P0)  FxP0) as Hdx2_R.
  pose proof (b64_minus_self_finite (bx P0)  FxP0) as Fdx2.
  (* Non-self subtractions: finiteness comes from the bridge under the safe  *)
  (* premises accepted as theorem hypotheses.                                 *)
  pose proof (b64_minus_correct _ _ Hdx') as [_ Fdx1].
  pose proof (b64_minus_correct _ _ Hdy') as [_ Fdy2].
  (* Two products: each has an R-zero factor, so B2R = 0 and finite. *)
  pose proof (b64_mult_zero_r_R _ _ Fdx1 Fdy1 Hdy1_R) as Ht1_R.
  pose proof (b64_mult_zero_r_finite _ _ Fdx1 Fdy1 Hdy1_R) as Ft1.
  pose proof (b64_mult_zero_l_R _ _ Fdx2 Fdy2 Hdx2_R) as Ht2_R.
  pose proof (b64_mult_zero_l_finite _ _ Fdx2 Fdy2 Hdx2_R) as Ft2.
  (* Outer b64_minus on two R-zero finite values: B2R = 0. *)
  apply (b64_minus_zeros_R _ _ Ft1 Ft2 Ht1_R Ht2_R).
Qed.
