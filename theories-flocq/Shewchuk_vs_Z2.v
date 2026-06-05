(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Shewchuk_vs_Z2
   ----------------------------------------------------------------------------
   "Shewchuk adaptive predicate vs the exact integer-determinant model."

   Grounded restatement of the issue-#66 hypothesis ("Shewchuk >= Z^2 exact
   model in power, >> in speed").  The original draft of this idea was written
   against invented symbols (`shewchuk_full`, `b64_orient2d_exact_Z2`,
   `in_Z2_regime`, ...) and stated its claims as `Hypothesis`es -- i.e. local
   axioms -- which both fails to compile and violates the corpus invariant
   (no `Axiom` / `Parameter`; only the three classical-reals axioms).

   This file replaces that draft with theorems that COMPOSE already-Qed-closed
   results over the real corpus symbols.  Two corrections to the framing:

     1. The corpus already has something STRONGER than a "Z^2 / integer grid"
        model: `Orient_b64_exact_full.b64_orient2d_exact`, the sign of a
        common-exponent integer determinant, is exact for the ENTIRE finite
        binary64 plane (`all_finite`), not merely for integer coordinates with
        |coord| <= 2^25.  That is the honest exact ground truth this file
        compares against.

     2. Shewchuk is not "stronger" than the exact model -- both decide the
        sign of the same real determinant `cross_R_BP`.  The accurate claim is
        AGREEMENT (they return the same verdict) plus SPEED (Stage A's filter
        is decisive in the common case, so the expansion fallback is skipped).

   COMPOSES (all Qed-closed upstream)
   ----------------------------------
     - `b64_orient_sign_stage_d_sound`  (Orient_b64_stage_d.v):
         the Shewchuk adaptive decoder (Stage A filter -> exact expansion
         fallback) is sound vs `cross_R_BP` under the integer + expansion
         safety predicates.
     - `b64_orient2d_exact_sound`       (Orient_b64_exact_full.v):
         the integer-determinant sign equals the sign of `cross_R_BP` for all
         finite doubles.
     - `b64_orient_sign_stage_d_tiny_regime_decisive` (Orient_b64_stage_d.v):
         in the tiny integer regime the decoder never returns `Uncertain`
         (the Stage A fast path resolves every non-zero cross) -- the formal
         proxy for the "speed" half of the hypothesis.

   DELIVERABLES
   ------------
     1. `int_safe_all_finite`: the integer regime entails `all_finite`
        (so the full-plane exact model applies).
     2. `shewchuk_stage_d_agrees_with_exact_intdet`: in the integer +
        expansion-safe regime, whenever the Shewchuk decoder commits to a
        sign it agrees with the exact integer-determinant model.  (Power.)
     3. `shewchuk_vs_z2_tiny_headline`: in the tiny regime, the decoder is
        decisive (never `Uncertain`, no fallback) AND agrees with the exact
        model.  (Speed + power, combined.)

   NTS cross-reference: this is the soundness spec behind
   `RobustLineIntersector` / `CGAlgorithmsDD.orientationIndex`
   (JTS Orientation.index, double-double adaptive predicate).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import Orient_b64_sound.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.
From NTS.Proofs.Flocq Require Import Orient_b64_exact_full.
From NTS.Proofs.Flocq Require Import Orient_b64_expansion.
From NTS.Proofs.Flocq Require Import Orient_b64_stage_d.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The integer regime entails `all_finite`, so the full-plane exact model     *)
(* (`Orient_b64_exact_full.b64_orient2d_exact_sound`) applies.  Each          *)
(* `coord_int_safe` carries `is_finite = true` as its first conjunct.         *)
(* -------------------------------------------------------------------------- *)

Lemma int_safe_all_finite :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    all_finite P0 P1 Q.
Proof.
  intros P0 P1 Q (Hx0 & Hy0 & Hx1 & Hy1 & Hxq & Hyq).
  destruct Hx0 as (Fx0 & _). destruct Hy0 as (Fy0 & _).
  destruct Hx1 as (Fx1 & _). destruct Hy1 as (Fy1 & _).
  destruct Hxq as (Fxq & _). destruct Hyq as (Fyq & _).
  unfold all_finite. repeat split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* POWER.  When the Shewchuk Stage D decoder commits to a definite sign       *)
(* (Pos / Neg / Zero), that verdict agrees with the exact integer-determinant *)
(* model `b64_orient2d_exact` (value in {1, -1, 0}).                          *)
(*                                                                            *)
(* Both decide the sign of the same real determinant `cross_R_BP`:            *)
(*   - the decoder via `b64_orient_sign_stage_d_sound`,                       *)
(*   - the integer model via `b64_orient2d_exact_sound`.                      *)
(* The Nan / Uncertain arms make no claim (the decoder declined to commit).   *)
(* -------------------------------------------------------------------------- *)

Theorem shewchuk_stage_d_agrees_with_exact_intdet :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_expansion_safe P0 P1 Q ->
    match b64_orient_sign_stage_d P0 P1 Q with
    | OrientRPos       => Orient_b64_exact_full.b64_orient2d_exact P0 P1 Q = 1%Z
    | OrientRNeg       => Orient_b64_exact_full.b64_orient2d_exact P0 P1 Q = (-1)%Z
    | OrientRZero      => Orient_b64_exact_full.b64_orient2d_exact P0 P1 Q = 0%Z
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hint Hexp.
  pose proof (int_safe_all_finite P0 P1 Q Hint) as Hfin.
  pose proof (b64_orient_sign_stage_d_sound P0 P1 Q Hint Hexp) as Hsd.
  pose proof (Orient_b64_exact_full.b64_orient2d_exact_sound P0 P1 Q Hfin)
    as (Hpos & Hneg & Hzero).
  destruct (b64_orient_sign_stage_d P0 P1 Q).
  - apply (proj1 Hpos).  exact Hsd.
  - apply (proj1 Hneg).  exact Hsd.
  - apply (proj1 Hzero). exact Hsd.
  - exact I.
  - exact I.
Qed.

(* -------------------------------------------------------------------------- *)
(* SPEED + POWER (tiny regime).  In the tiny integer regime (|coord| <= 2^22) *)
(* with a non-zero cross product, the decoder:                                *)
(*   - never returns `Uncertain` -- the Stage A filter alone resolves the     *)
(*     sign, so the expensive expansion fallback is never invoked (speed),    *)
(*   - and its committed verdict still agrees with the exact integer model    *)
(*     (power).                                                               *)
(*                                                                            *)
(* `orient2d_inputs_tiny_int_safe_imp_int_safe` lifts the tiny regime to the  *)
(* standard integer regime for the agreement half.                           *)
(* -------------------------------------------------------------------------- *)

Theorem shewchuk_vs_z2_tiny_headline :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_tiny_int_safe P0 P1 Q ->
    b64_orient2d_expansion_safe P0 P1 Q ->
    cross_R_BP P0 P1 Q <> 0 ->
    b64_orient_sign_stage_d P0 P1 Q <> OrientRUncertain
    /\ match b64_orient_sign_stage_d P0 P1 Q with
       | OrientRPos       => Orient_b64_exact_full.b64_orient2d_exact P0 P1 Q = 1%Z
       | OrientRNeg       => Orient_b64_exact_full.b64_orient2d_exact P0 P1 Q = (-1)%Z
       | OrientRZero      => Orient_b64_exact_full.b64_orient2d_exact P0 P1 Q = 0%Z
       | OrientRNan       => True
       | OrientRUncertain => True
       end.
Proof.
  intros P0 P1 Q Htiny Hexp Hnz.
  split.
  - exact (b64_orient_sign_stage_d_tiny_regime_decisive P0 P1 Q Htiny Hnz).
  - apply shewchuk_stage_d_agrees_with_exact_intdet.
    + exact (orient2d_inputs_tiny_int_safe_imp_int_safe P0 P1 Q Htiny).
    + exact Hexp.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions shewchuk_stage_d_agrees_with_exact_intdet.
Print Assumptions shewchuk_vs_z2_tiny_headline.
