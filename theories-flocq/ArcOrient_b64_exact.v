(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ArcOrient_b64_exact
   ----------------------------------------------------------------------------
   Phase 4 Session C: discharge `b64_inCircle_R_correct` (the load-bearing
   Section Variable in ArcOrient_b64.v / ArcIntersect_b64.v).

   Proves the unconditional theorem
       inCircle_inputs_int_safe A B C P ->
       B2R (b64_inCircle_R A B C P)
         = inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P)
       /\ is_finite (b64_inCircle_R A B C P) = true
   via the standard Stage A chain of `b64_*_int_exact` lemmas from
   `Orient_b64_exact.v`, applied to each of the ~22 arithmetic operations
   inside `b64_inCircle_R`.

   STATUS.  The headline theorem `b64_inCircle_R_exact` is currently
   **Admitted**.  An initial monolithic Ltac script of the full ~22-step
   chain triggered an OOM kill (exit 137) during the Coq term-elaboration
   phase -- the cumulative size of the integer-bound hypotheses + the
   final `B2R = inCircle_R` reflexivity over fully-unfolded BPoint
   accessors exceeded available memory.

   The proof IS provable; what remains is restructuring into ~6-8 small
   sub-lemmas (one per magnitude tier) so each step's term explosion
   stays bounded.  Magnitude budget under arc_coord_int_safe (|n| <= 2^11):
     differences          : |d|   <= 2^12   (b64_minus_int_exact x 6)
     squared differences  : |s|   <= 2^24   (b64_mult_int_exact x 6)
     sums of squares      : |.|   <= 2^25   (b64_plus_int_exact x 3 -> na, nb, nc)
     degree-3 products    : |.|   <= 2^37   (b64_mult_int_exact x 6)
     degree-3 differences : |.|   <= 2^38   (b64_minus_int_exact x 3)
     degree-4 products    : |.|   <= 2^50   (b64_mult_int_exact x 3 -> row_a, row_b, row_c)
     degree-4 differences : |.|   <= 2^51   (b64_minus_int_exact x 1)
     degree-4 final sum   : |.|   <= 2^52   (b64_plus_int_exact x 1)
   All comfortably <= 2^53 = 2^prec.

   Registered in `docs/admitted-deferred-proofs.txt`.  Discharge is a
   structural / mechanical exercise -- factor the chain into per-tier
   lemmas with bounded proof contexts.

   Unconditional corollaries below USE `b64_inCircle_R_exact` to
   instantiate the Section-Variable-conditional theorems from
   ArcOrient_b64.v; they Qed-close under the Admitted hypothesis,
   matching the corpus's existing deferred-proof pattern.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs        Require Import Distance.
From NTS.Proofs        Require Import ArcOrient.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import B64_bridge.
From NTS.Proofs.Flocq  Require Import HotPixel_b64.
From NTS.Proofs.Flocq  Require Import Orient_b64_exact.   (* b64_*_int_exact *)
From NTS.Proofs.Flocq  Require Import ArcOrient_b64.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Integer bound helpers.                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma int_prod_bound :
  forall (a b Na Nb : Z),
    (Z.abs a <= Na)%Z -> (Z.abs b <= Nb)%Z ->
    (Z.abs (a * b) <= Na * Nb)%Z.
Proof.
  intros a b Na Nb Ha Hb.
  rewrite Z.abs_mul. apply Z.mul_le_mono_nonneg; lia.
Qed.

Lemma int_diff_bound :
  forall (a b Na Nb : Z),
    (Z.abs a <= Na)%Z -> (Z.abs b <= Nb)%Z ->
    (Z.abs (a - b) <= Na + Nb)%Z.
Proof. intros. lia. Qed.

Lemma int_sum_bound :
  forall (a b Na Nb : Z),
    (Z.abs a <= Na)%Z -> (Z.abs b <= Nb)%Z ->
    (Z.abs (a + b) <= Na + Nb)%Z.
Proof. intros. lia. Qed.

Lemma le_2pN_le_2pprec :
  forall (n : Z) (N : Z),
    (0 <= N <= 53)%Z ->
    (Z.abs n <= 2 ^ N)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof.
  intros n N HN H.
  apply Z.le_trans with (2 ^ N)%Z; [exact H|].
  unfold prec.
  apply Z.pow_le_mono_r; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The exactness theorem -- Admitted; registered as deferred.             *)
(* -------------------------------------------------------------------------- *)

(* Proof structure (Stage A chain).  Per-step sub-lemmas to land in the
   follow-up restructuring session:

     b64_inCircle_R_differences_exact:
       Under arc_coord_int_safe, the six b64_minus calls compute the six
       coordinate differences exactly (each |result| <= 2^12).

     b64_inCircle_R_squared_diffs_exact:
       Under the differences exactness, the six b64_mult calls compute the
       six squared-difference terms exactly (each |result| <= 2^24).

     b64_inCircle_R_sums_of_squares_exact:
       The three b64_plus calls computing na, nb, nc are exact under the
       squared-diff bounds (each |result| <= 2^25).

     b64_inCircle_R_row3_exact:
       The four cross-products and two differences forming the inner
       (by_*nc - cy*nb) and (bx*nc - cx*nb) expressions are exact
       (each <= 2^38).

     b64_inCircle_R_row4_exact:
       The two outer row multiplications + the row_c chain (two
       degree-2 mults + their difference + the na multiplication) are
       exact (each <= 2^50).

     b64_inCircle_R_outer_sum_exact:
       The final (row_a - row_b) + row_c sum is exact (<= 2^52).

   Each sub-lemma has bounded context size, so the term-elaboration
   memory pressure stays within the build environment's budget.  The
   composition is then a small algebra step rewriting through the six
   sub-lemmas' B2R = IZR equations to match inCircle_R's R-side
   expansion. *)

Theorem b64_inCircle_R_exact :
  forall A B C P : BPoint,
    inCircle_inputs_int_safe A B C P ->
    Binary.B2R prec emax (b64_inCircle_R A B C P)
      = inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) /\
    Binary.is_finite prec emax (b64_inCircle_R A B C P) = true.
Admitted.

(* -------------------------------------------------------------------------- *)
(* §3  Unconditional corollaries.                                             *)
(*                                                                            *)
(* Instantiate the Section-Variable-conditional theorems from                 *)
(* ArcOrient_b64.v with the (Admitted) b64_inCircle_R_exact.                  *)
(* -------------------------------------------------------------------------- *)

Theorem b64_inCircle_sign_sound_unconditional :
  forall A B C P : BPoint,
    inCircle_inputs_int_safe A B C P ->
    match b64_inCircle_sign A B C P with
    | ICS_Pos  => 0 < inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P)
    | ICS_Neg  => inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) < 0
    | ICS_Zero => inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) = 0
    | ICS_Nan  => True
    end.
Proof.
  intros. apply (b64_inCircle_sign_sound b64_inCircle_R_exact); assumption.
Qed.

Theorem b64_inCircle_sign_pos_sound_unconditional :
  forall A B C P : BPoint,
    inCircle_inputs_int_safe A B C P ->
    b64_inCircle_sign A B C P = ICS_Pos ->
    0 < inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P).
Proof.
  intros. apply (b64_inCircle_sign_pos_sound b64_inCircle_R_exact); assumption.
Qed.

Theorem b64_inCircle_sign_neg_sound_unconditional :
  forall A B C P : BPoint,
    inCircle_inputs_int_safe A B C P ->
    b64_inCircle_sign A B C P = ICS_Neg ->
    inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) < 0.
Proof.
  intros. apply (b64_inCircle_sign_neg_sound b64_inCircle_R_exact); assumption.
Qed.

Theorem b64_inCircle_sign_zero_sound_unconditional :
  forall A B C P : BPoint,
    inCircle_inputs_int_safe A B C P ->
    b64_inCircle_sign A B C P = ICS_Zero ->
    inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) = 0.
Proof.
  intros. apply (b64_inCircle_sign_zero_sound b64_inCircle_R_exact); assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_inCircle_R_exact.
Print Assumptions b64_inCircle_sign_sound_unconditional.
Print Assumptions b64_inCircle_sign_pos_sound_unconditional.
Print Assumptions b64_inCircle_sign_neg_sound_unconditional.
Print Assumptions b64_inCircle_sign_zero_sound_unconditional.
