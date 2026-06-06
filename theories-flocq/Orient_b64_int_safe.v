(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_int_safe
   ----------------------------------------------------------------------------
   Stage D: orient2d exact-expansion nonoverlap on the integer-coordinate
   regime, WITHOUT the deferred general Shewchuk headline.

   `b64_orient2d_expansion P0 P1 Q` (Orient_b64_expansion.v) is the
   fast-expansion-sum of two Dekker products of the coordinate differences.
   The proven, UNCONDITIONAL Stage-D headline
   `fast_expansion_sum_nonoverlap_shewchuk_int_safe_two_pairs`
   (B64_FastExpansionSum_Shewchuk_Route2.v) handles exactly the (2,2) shape,
   but requires each Dekker pair to be (integer-high, zero-low) and finite.

   The just-landed `b64_Dekker_int_exact` (Orient_b64_dekker_int.v) supplies the
   (integer-high, zero-low) half on integer inputs; this file adds the
   finiteness half (`b64_Dekker_finite`) and composes the two into

     `b64_orient2d_expansion_int_nonoverlap` :
        whenever the four coordinate differences are integer-valued with the
        two cross-products fitting in 53 bits, the orient2d expansion is
        nonoverlap_shewchuk -- with NO dependence on the deferred general
        `fast_expansion_sum_nonoverlap_shewchuk`.

   Composing with the existing `b64_orient2d_expansion_sum` (= `cross_R_BP`)
   and `sign_of_expansion_correct_shewchuk` then gives the end-to-end int-safe
   sign-correctness `b64_orient2d_expansion_int_sign_correct`.

   Pure-Flocq (binary64); no `Admitted` / `Axiom` / `Parameter` introduced.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
                                     Orient_b64_sound B64_Expansion
                                     B64_Expansion_Shewchuk B64_Pff_bridge
                                     B64_FastExpansionSum
                                     B64_FastExpansionSum_Shewchuk
                                     B64_FastExpansionSum_Shewchuk_Route2
                                     Orient_b64_expansion Orient_b64_dekker_int.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Dekker outputs are finite under the Dekker safety chain.               *)
(* -------------------------------------------------------------------------- *)

Lemma b64_Dekker_finite : forall x y : binary64,
  b64_Dekker_safe x y ->
  Binary.is_finite prec emax (fst (b64_Dekker x y)) = true
  /\ Binary.is_finite prec emax (snd (b64_Dekker x y)) = true.
Proof.
  intros x y Hsafe.
  pose proof Hsafe as Hsafe'.
  unfold b64_Dekker_safe in Hsafe'. cbv zeta in Hsafe'.
  destruct Hsafe' as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hr [_ [_ [_ Ht4]]]]]]]]]]]]]]]].
  split.
  - rewrite b64_Dekker_fst. exact (proj2 (b64_mult_correct _ _ Hr)).
  - unfold b64_Dekker. cbv zeta. cbn [snd].
    exact (proj2 (b64_plus_correct _ _ Ht4)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Integer-regime nonoverlap, via the proven (2,2) int-safe headline.     *)
(*                                                                            *)
(* Hypotheses: the standard expansion-safety bundle, plus the four coordinate *)
(* differences being integer-valued, plus the magnitude budget               *)
(* |a1*b1| + |a2*b2| <= 2^prec on the two cross-products.                     *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_expansion_int_nonoverlap :
  forall (P0 P1 Q : BPoint) (a1 b1 a2 b2 : Z),
    b64_orient2d_expansion_safe P0 P1 Q ->
    Binary.B2R prec emax (b64_minus (bx P1) (bx P0)) = IZR a1 ->
    Binary.B2R prec emax (b64_minus (by_ Q)  (by_ P0)) = IZR b1 ->
    Binary.B2R prec emax (b64_minus (bx P0) (bx Q))  = IZR a2 ->
    Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)) = IZR b2 ->
    (Z.abs (a1 * b1) + Z.abs (a2 * b2) <= 2 ^ prec)%Z ->
    nonoverlap_shewchuk (b64_orient2d_expansion P0 P1 Q).
Proof.
  intros P0 P1 Q a1 b1 a2 b2 Hsafe Ha1 Hb1 Ha2 Hb2 Hbudget.
  assert (Hbnd1 : (Z.abs (a1 * b1) <= 2 ^ prec)%Z) by lia.
  assert (Hbnd2 : (Z.abs (a2 * b2) <= 2 ^ prec)%Z) by lia.
  unfold b64_orient2d_expansion_safe in Hsafe.
  destruct Hsafe as [_ [_ [HDek1 [HDek2 [_ [_ Hfes]]]]]].
  (* Exactness (integer-high, zero-low) and finiteness for each Dekker pair. *)
  pose proof (b64_Dekker_int_exact _ _ a1 b1 HDek1 Ha1 Hb1 Hbnd1) as [Hr1 Ht1].
  pose proof (b64_Dekker_int_exact _ _ a2 b2 HDek2 Ha2 Hb2 Hbnd2) as [Hr2 Ht2].
  pose proof (b64_Dekker_finite _ _ HDek1) as [Hf_r1 Hf_t1].
  pose proof (b64_Dekker_finite _ _ HDek2) as [Hf_r2 Hf_t2].
  unfold b64_orient2d_expansion.
  destruct (b64_Dekker (b64_minus (bx P1) (bx P0))
                       (b64_minus (by_ Q) (by_ P0))) as [r1 t1] eqn:HD1.
  destruct (b64_Dekker (b64_minus (bx P0) (bx Q))
                       (b64_minus (by_ P1) (by_ P0))) as [r2 t2] eqn:HD2.
  cbn [fst snd] in Hr1, Ht1, Hr2, Ht2, Hf_r1, Hf_t1, Hf_r2, Hf_t2, Hfes.
  apply (fast_expansion_sum_nonoverlap_shewchuk_int_safe_two_pairs
           r1 t1 r2 t2 (a1 * b1) (a2 * b2)
           Hfes Hf_r1 Hf_t1 Hf_r2 Hf_t2 Hr1 Ht1 Hr2 Ht2 Hbudget).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  End-to-end integer-regime sign-correctness.                            *)
(*                                                                            *)
(* Composes the int-safe nonoverlap (§2) with the existing sum-correctness     *)
(* (`b64_orient2d_expansion_sum` = `cross_R_BP`) and                          *)
(* `sign_of_expansion_correct_shewchuk`.  This is the orient2d-level result    *)
(* that previously routed through the deferred general headline; here it is    *)
(* unconditional on the integer regime.                                        *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_expansion_int_sign_correct :
  forall (P0 P1 Q : BPoint) (a1 b1 a2 b2 : Z),
    b64_orient2d_expansion_safe P0 P1 Q ->
    Binary.B2R prec emax (b64_minus (bx P1) (bx P0)) = IZR a1 ->
    Binary.B2R prec emax (b64_minus (by_ Q)  (by_ P0)) = IZR b1 ->
    Binary.B2R prec emax (b64_minus (bx P0) (bx Q))  = IZR a2 ->
    Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)) = IZR b2 ->
    (Z.abs (a1 * b1) + Z.abs (a2 * b2) <= 2 ^ prec)%Z ->
    match b64_orient2d_expansion_sign P0 P1 Q with
    | ExpPos  => 0 < cross_R_BP P0 P1 Q
    | ExpNeg  => cross_R_BP P0 P1 Q < 0
    | ExpZero => cross_R_BP P0 P1 Q = 0
    end.
Proof.
  intros P0 P1 Q a1 b1 a2 b2 Hsafe Ha1 Hb1 Ha2 Hb2 Hbudget.
  unfold b64_orient2d_expansion_sign.
  pose proof (b64_orient2d_expansion_int_nonoverlap P0 P1 Q a1 b1 a2 b2
                Hsafe Ha1 Hb1 Ha2 Hb2 Hbudget) as Hno.
  pose proof (sign_of_expansion_correct_shewchuk
                (b64_orient2d_expansion P0 P1 Q) Hno) as Hsign.
  pose proof (b64_orient2d_expansion_sum P0 P1 Q Hsafe) as Hsum.
  rewrite Hsum in Hsign. exact Hsign.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_Dekker_finite.
Print Assumptions b64_orient2d_expansion_int_nonoverlap.
Print Assumptions b64_orient2d_expansion_int_sign_correct.
