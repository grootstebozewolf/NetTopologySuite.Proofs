(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_int_safe_coords
   ----------------------------------------------------------------------------
   Stage D: the orient2d integer-regime guarantee, stated directly on integer
   POINT COORDINATES (`orient2d_inputs_int_safe`) instead of on the coordinate
   differences.

   `Orient_b64_int_safe.v` proved `b64_orient2d_expansion_int_sign_correct`
   taking, as hypotheses, that the four coordinate differences are
   integer-valued and that the two cross-products fit in 53 bits.  Under the
   standard integer-coordinate contract (`orient2d_inputs_int_safe`: every
   coordinate is an integer with `|n| <= 2^25`) both of those are AUTOMATIC:

     - each difference is the exact integer difference, by `b64_minus_int_exact`
       (already in Orient_b64_exact.v), with magnitude `<= 2^26`;
     - hence each cross-product has magnitude `<= 2^52`, and their sum
       `<= 2^53 = 2^prec` -- the budget is discharged by construction.

   So this file removes those hypotheses, exposing the clean statement

     `b64_orient2d_expansion_int_sign_correct_coords` :
        orient2d_inputs_int_safe P0 P1 Q ->
        b64_orient2d_expansion_safe P0 P1 Q ->
        the expansion sign matches the sign of `cross_R_BP P0 P1 Q`.

   (The remaining `b64_orient2d_expansion_safe` hypothesis -- the per-op
   no-overflow chain for the two Dekker products and the fast-expansion-sum --
   is the separate, magnitude-bookkeeping-heavy piece; discharging it from
   `orient2d_inputs_int_safe` is left as a follow-up slice.)

   Still NO dependence on the deferred general
   `fast_expansion_sum_nonoverlap_shewchuk`.

   Pure-Flocq (binary64); no `Admitted` / `Axiom` / `Parameter` introduced.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
                                     Orient_b64_sound Orient_b64_exact
                                     B64_Expansion B64_Expansion_Shewchuk
                                     B64_Pff_bridge Orient_b64_expansion
                                     Orient_b64_int_safe.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Helper: the magnitude budget holds for any four integers bounded by 2^26.  *)
(* -------------------------------------------------------------------------- *)

Lemma cross_budget_of_diff_bounds :
  forall a1 b1 a2 b2 : Z,
    (Z.abs a1 <= 2 ^ 26)%Z -> (Z.abs b1 <= 2 ^ 26)%Z ->
    (Z.abs a2 <= 2 ^ 26)%Z -> (Z.abs b2 <= 2 ^ 26)%Z ->
    (Z.abs (a1 * b1) + Z.abs (a2 * b2) <= 2 ^ prec)%Z.
Proof.
  intros a1 b1 a2 b2 Ha1 Hb1 Ha2 Hb2.
  assert (Hp1 : (Z.abs (a1 * b1) <= 2 ^ 52)%Z).
  { rewrite Z.abs_mul. replace (2 ^ 52)%Z with (2 ^ 26 * 2 ^ 26)%Z by lia.
    apply Z.mul_le_mono_nonneg;
      [ apply Z.abs_nonneg | exact Ha1 | apply Z.abs_nonneg | exact Hb1 ]. }
  assert (Hp2 : (Z.abs (a2 * b2) <= 2 ^ 52)%Z).
  { rewrite Z.abs_mul. replace (2 ^ 52)%Z with (2 ^ 26 * 2 ^ 26)%Z by lia.
    apply Z.mul_le_mono_nonneg;
      [ apply Z.abs_nonneg | exact Ha2 | apply Z.abs_nonneg | exact Hb2 ]. }
  replace (2 ^ prec)%Z with (2 ^ 52 + 2 ^ 52)%Z by (unfold prec; lia).
  lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Helper: each coordinate difference is the exact integer difference, with    *)
(* magnitude <= 2^26, under the integer-coordinate contract.                   *)
(* -------------------------------------------------------------------------- *)

Lemma coord_diff_int_exact :
  forall x y : binary64,
    coord_int_safe x -> coord_int_safe y ->
    exists d : Z,
      Binary.B2R prec emax (b64_minus x y) = IZR d /\ (Z.abs d <= 2 ^ 26)%Z.
Proof.
  intros x y (Fx & a & HxR & Hxb) (Fy & b & HyR & Hyb).
  assert (Hbnd26 : (Z.abs (a - b) <= 2 ^ 26)%Z).
  { replace (2 ^ 26)%Z with (2 ^ 25 + 2 ^ 25)%Z by lia. lia. }
  assert (Hbndp : (Z.abs (a - b) <= 2 ^ prec)%Z).
  { apply (Z.le_trans _ (2 ^ 26)); [ exact Hbnd26 | unfold prec; lia ]. }
  pose proof (b64_minus_int_exact x y a b Fx Fy HxR HyR Hbndp) as [Hd _].
  exists (a - b)%Z. split; [ exact Hd | exact Hbnd26 ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  Integer-coordinate nonoverlap.                                         *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_expansion_int_nonoverlap_coords :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_expansion_safe P0 P1 Q ->
    nonoverlap_shewchuk (b64_orient2d_expansion P0 P1 Q).
Proof.
  intros P0 P1 Q Hints Hsafe.
  destruct Hints as [HxP0 [HyP0 [HxP1 [HyP1 [HxQ HyQ]]]]].
  destruct (coord_diff_int_exact (bx P1) (bx P0) HxP1 HxP0) as [a1 [Hd1 Hb_a1]].
  destruct (coord_diff_int_exact (by_ Q)  (by_ P0) HyQ  HyP0) as [b1 [Hd2 Hb_b1]].
  destruct (coord_diff_int_exact (bx P0) (bx Q)  HxP0 HxQ)  as [a2 [Hd3 Hb_a2]].
  destruct (coord_diff_int_exact (by_ P1) (by_ P0) HyP1 HyP0) as [b2 [Hd4 Hb_b2]].
  apply (b64_orient2d_expansion_int_nonoverlap P0 P1 Q a1 b1 a2 b2
           Hsafe Hd1 Hd2 Hd3 Hd4).
  apply cross_budget_of_diff_bounds; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Integer-coordinate sign-correctness -- the headline.                   *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_expansion_int_sign_correct_coords :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_expansion_safe P0 P1 Q ->
    match b64_orient2d_expansion_sign P0 P1 Q with
    | ExpPos  => 0 < cross_R_BP P0 P1 Q
    | ExpNeg  => cross_R_BP P0 P1 Q < 0
    | ExpZero => cross_R_BP P0 P1 Q = 0
    end.
Proof.
  intros P0 P1 Q Hints Hsafe.
  destruct Hints as [HxP0 [HyP0 [HxP1 [HyP1 [HxQ HyQ]]]]].
  destruct (coord_diff_int_exact (bx P1) (bx P0) HxP1 HxP0) as [a1 [Hd1 Hb_a1]].
  destruct (coord_diff_int_exact (by_ Q)  (by_ P0) HyQ  HyP0) as [b1 [Hd2 Hb_b1]].
  destruct (coord_diff_int_exact (bx P0) (bx Q)  HxP0 HxQ)  as [a2 [Hd3 Hb_a2]].
  destruct (coord_diff_int_exact (by_ P1) (by_ P0) HyP1 HyP0) as [b2 [Hd4 Hb_b2]].
  apply (b64_orient2d_expansion_int_sign_correct P0 P1 Q a1 b1 a2 b2
           Hsafe Hd1 Hd2 Hd3 Hd4).
  apply cross_budget_of_diff_bounds; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient2d_expansion_int_nonoverlap_coords.
Print Assumptions b64_orient2d_expansion_int_sign_correct_coords.
