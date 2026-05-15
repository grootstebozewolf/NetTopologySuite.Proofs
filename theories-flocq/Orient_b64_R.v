(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_R
   ----------------------------------------------------------------------------
   R-side arithmetic identities for `b64_orient2d`, proved via composition of
   the per-op correctness lifts in `B64_bridge.v`.

   First consumer of the bridge module.  Establishes the pattern downstream
   identities (cyclic permutation, translation invariance, etc.) and the
   simplifier R-bridge will reuse.

   What this file proves now:
     - `b64_orient2d_safe P0 P1 Q`         -- bundled no-overflow precondition
                                              for one call to `b64_orient2d`.
     - `b64_orient2d_antisymmetric_R`      -- swapping the last two arguments
                                              negates the R-valued result.

   Not yet:
     - cyclic permutation, translation invariance, etc. (same pattern,
       deferred to a follow-up slice).
     - the magnitude-bounded variant of the precondition + the
       "bounded inputs imply safe chain" helper (Flavour B in the audit
       discussion; one-time work that buys easier callers).

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
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient2d_antisymmetric_R.
