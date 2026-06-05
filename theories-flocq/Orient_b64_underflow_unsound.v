(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_underflow_unsound
   ----------------------------------------------------------------------------
   A machine-checked UNSOUNDNESS WITNESS for the Stage A orientation filter
   `b64_orient_sign_filtered` in the underflow regime.

   Motivation (issue #66 / the "Shewchuk vs exact model" thread).  The Stage A
   filter is only proven sound under explicit safety preconditions
   (`coord_int_safe`, the tiny integer regime, `no_overflow`).  This file
   exhibits CONCRETE finite binary64 points OUTSIDE those regimes where the
   filter is unsound -- it reports "collinear" (`OrientRZero`) while the true
   determinant is strictly positive.  This is the constructive justification
   for the safety preconditions and for the exact fallback that makes the
   adaptive predicate powerful.

   This is NOT a counterexample to any proven theorem (no soundness theorem
   claims anything in this regime), so it needs no `admitted-counterexamples`
   registry entry.  It is a Qed-closed POSITIVE theorem.

   THE WITNESS.  Powers of two, exactly representable in binary64:

       P0 = (0, 0)
       P1 = (2^-200, 0)
       Q  = (2^-200, 2^-900)

   The orientation determinant is
       cross = (P1x - P0x)*(Qy - P0y) - (Qx - P0x)*(P1y - P0y)
             = 2^-200 * 2^-900 - 2^-200 * 0
             = 2^-1100   > 0   (Q lies just above the x-axis through P0,P1).

   But 2^-1100 is far below the smallest binary64 subnormal 2^-1074, so the
   floating product `b64_mult (2^-200) (2^-900)` ROUNDS TO +0.  The Stage A
   filter therefore sees `det = 0` and commits to `OrientRZero` -- a wrong,
   unsound verdict.  The exact integer-determinant model
   `Orient_b64_exact_full.b64_orient2d_exact` (which never forms the float
   product, working on integer mantissas at a common exponent) returns +1,
   the correct sign.

   NTS cross-reference: same lineage as `RobustLineIntersector` /
   `CGAlgorithmsDD.orientationIndex` -- the DD adaptive predicate exists
   precisely because the plain double filter fails like this.

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
From NTS.Proofs.Flocq Require Import Orient_b64_exact_full.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The concrete witness points.  4503599627370496 = 2^52 is the canonical     *)
(* binary64 mantissa, so `2^52 * 2^e = 2^(52+e)`:                             *)
(*   2^52 * 2^(-252) = 2^-200,   2^52 * 2^(-952) = 2^-900.                    *)
(* The `eq_refl` is the `bounded prec emax m e = true` proof; it type-checks  *)
(* because |m| has 53 bits and -1074 <= e <= 971.                            *)
(* -------------------------------------------------------------------------- *)

Definition b64_zero : binary64 := Binary.B754_zero prec emax false.
Definition b64_2pow_m200 : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-252) eq_refl.
Definition b64_2pow_m900 : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-952) eq_refl.

Definition uP0 : BPoint := mkBP b64_zero        b64_zero.
Definition uP1 : BPoint := mkBP b64_2pow_m200   b64_zero.
Definition uQ  : BPoint := mkBP b64_2pow_m200   b64_2pow_m900.

(* -------------------------------------------------------------------------- *)
(* All six coordinates are finite, so the full-plane exact model applies.     *)
(* -------------------------------------------------------------------------- *)

Lemma uWitness_all_finite : all_finite uP0 uP1 uQ.
Proof. unfold all_finite. vm_compute. repeat split; reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* (1) Stage A filter underflows: it reports OrientRZero ("collinear").       *)
(* -------------------------------------------------------------------------- *)

Lemma uWitness_filter_says_zero :
  b64_orient_sign_filtered uP0 uP1 uQ = OrientRZero.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* (2) Exact integer-determinant model returns +1 (strictly positive).        *)
(* -------------------------------------------------------------------------- *)

Lemma uWitness_exact_says_pos :
  b64_orient2d_exact uP0 uP1 uQ = 1%Z.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* (3) The true real determinant is strictly positive -- so the filter's      *)
(* "collinear" verdict is genuinely WRONG, not merely a different encoding.   *)
(* Derived from the exact model's soundness over all finite doubles.          *)
(* -------------------------------------------------------------------------- *)

Lemma uWitness_true_cross_pos : 0 < cross_R_BP uP0 uP1 uQ.
Proof.
  pose proof (b64_orient2d_exact_sound uP0 uP1 uQ uWitness_all_finite)
    as (Hpos & _ & _).
  apply (proj2 Hpos). exact uWitness_exact_says_pos.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: the Stage A filter is unsound in the underflow regime.           *)
(*                                                                            *)
(*   - it commits to OrientRZero (claims the three points are collinear),     *)
(*   - yet the exact model returns +1 and the true cross product is > 0.      *)
(*                                                                            *)
(* A `Zero` from `b64_orient_sign_filtered` therefore does NOT imply          *)
(* `cross_R_BP = 0` without a safety precondition -- exactly why the proven   *)
(* soundness theorems carry `coord_int_safe` / tiny-regime / no-overflow      *)
(* hypotheses, and why the exact fallback is necessary.                       *)
(* -------------------------------------------------------------------------- *)

Theorem stage_a_filter_unsound_under_underflow :
  b64_orient_sign_filtered uP0 uP1 uQ = OrientRZero
  /\ b64_orient2d_exact uP0 uP1 uQ = 1%Z
  /\ 0 < cross_R_BP uP0 uP1 uQ.
Proof.
  split; [exact uWitness_filter_says_zero |].
  split; [exact uWitness_exact_says_pos |].
  exact uWitness_true_cross_pos.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions stage_a_filter_unsound_under_underflow.
