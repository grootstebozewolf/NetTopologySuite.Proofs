(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_dekker_int
   ----------------------------------------------------------------------------
   Stage D bridge: Dekker's TwoProduct is EXACT (zero low part) on the
   integer-coordinate regime.

   Context (docs/stage-d-feasibility.md, docs/audit-shewchuk-stages.md).  The
   orient2d exact predicate sums two Dekker products via fast-expansion-sum.
   The proven, UNCONDITIONAL Stage-D headline
   `fast_expansion_sum_nonoverlap_shewchuk_int_safe_two_pairs`
   (B64_FastExpansionSum_Shewchuk_Route2.v) takes two length-2 expansions
   `[r1; t1]`, `[r2; t2]` and requires each LOW part to vanish (`B2R t = 0`)
   with integer high parts.  That hypothesis is exactly the statement that the
   Dekker products are exactly representable -- which is what integer
   coordinates buy you: a product of two bounded integers fits in the 53-bit
   significand with no round-off, so Dekker's error term is identically zero.

   This file supplies that missing brick, no dependence on the deferred general
   `fast_expansion_sum_nonoverlap_shewchuk`:

     - `b64_Dekker_exact_of_format` : if `B2R x * B2R y` is in binary64 format,
        then `b64_Dekker x y = (round-exact high, zero low)`.
     - `b64_Dekker_int_exact`       : the integer instantiation -- for
        integer-valued `x, y` with `|x*y| <= 2^prec`, the high part is the exact
        integer product and the low part is `0`.

   The proof is short because the heavy lifting already exists:
   `b64_Dekker_correct` (x*y = r + t exactly) + `b64_round_generic`
   (rounding is the identity on representable reals) collapse the low term.

   Pure-Flocq (binary64); no `Admitted` / `Axiom` / `Parameter` introduced.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
                                     Orient_b64_exact B64_Pff_bridge.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The high part of `b64_Dekker` is, by construction, `b64_mult x y`.         *)
(* -------------------------------------------------------------------------- *)

Lemma b64_Dekker_fst : forall x y : binary64,
  fst (b64_Dekker x y) = b64_mult x y.
Proof. intros x y. unfold b64_Dekker. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Exactness on representable products: high = product, low = 0.              *)
(* -------------------------------------------------------------------------- *)

Lemma b64_Dekker_exact_of_format :
  forall x y : binary64,
    b64_Dekker_safe x y ->
    (Binary.B2R prec emax x * Binary.B2R prec emax y = 0
     \/ bpow radix2 (3 - emax - prec + 2 * prec - 1)
        <= Rabs (Binary.B2R prec emax x * Binary.B2R prec emax y)) ->
    b64_format (Binary.B2R prec emax x * Binary.B2R prec emax y) ->
    Binary.B2R prec emax (fst (b64_Dekker x y))
      = Binary.B2R prec emax x * Binary.B2R prec emax y
    /\ Binary.B2R prec emax (snd (b64_Dekker x y)) = 0.
Proof.
  intros x y Hsafe Hund Hfmt.
  pose proof (b64_Dekker_correct x y Hsafe Hund) as Hcorr.
  (* Turn the `let '(r,t) := ...` into explicit fst/snd, then expose fst. *)
  rewrite (surjective_pairing (b64_Dekker x y)) in Hcorr.
  cbv beta iota zeta in Hcorr.
  rewrite b64_Dekker_fst in Hcorr.
  (* Hcorr : B2R x * B2R y
              = B2R (b64_mult x y) + B2R (snd (b64_Dekker x y)). *)
  rewrite b64_Dekker_fst.
  (* Goal : B2R (b64_mult x y) = B2R x * B2R y
            /\ B2R (snd (b64_Dekker x y)) = 0. *)
  unfold b64_Dekker_safe in Hsafe. cbv zeta in Hsafe.
  destruct Hsafe as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hr _]]]]]]]]]]]]].
  pose proof (b64_mult_correct x y Hr) as [HBr _].
  rewrite (b64_round_generic _ Hfmt) in HBr.    (* HBr : B2R (b64_mult x y) = prod *)
  split.
  - exact HBr.
  - rewrite HBr in Hcorr. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Integer instantiation: the regime Stage D's `_int_safe_two_pairs` needs.   *)
(* -------------------------------------------------------------------------- *)

Lemma b64_Dekker_int_exact :
  forall (x y : binary64) (a b : Z),
    b64_Dekker_safe x y ->
    Binary.B2R prec emax x = IZR a ->
    Binary.B2R prec emax y = IZR b ->
    (Z.abs (a * b) <= 2 ^ prec)%Z ->
    Binary.B2R prec emax (fst (b64_Dekker x y)) = IZR (a * b)
    /\ Binary.B2R prec emax (snd (b64_Dekker x y)) = 0.
Proof.
  intros x y a b Hsafe Hxa Hyb Hbnd.
  assert (Hprod : Binary.B2R prec emax x * Binary.B2R prec emax y = IZR (a * b)).
  { rewrite Hxa, Hyb, <- mult_IZR. reflexivity. }
  assert (Hfmt : b64_format (Binary.B2R prec emax x * Binary.B2R prec emax y)).
  { rewrite Hprod. apply generic_format_IZR_le_bpow_prec. exact Hbnd. }
  assert (Hund :
    Binary.B2R prec emax x * Binary.B2R prec emax y = 0
    \/ bpow radix2 (3 - emax - prec + 2 * prec - 1)
       <= Rabs (Binary.B2R prec emax x * Binary.B2R prec emax y)).
  { rewrite Hprod. destruct (Z.eq_dec (a * b) 0) as [Hz | Hnz].
    - left. rewrite Hz. reflexivity.
    - right.
      assert (Hge1 : 1 <= Rabs (IZR (a * b))).
      { rewrite <- abs_IZR. replace 1 with (IZR 1) by reflexivity.
        apply IZR_le. lia. }
      assert (Hble1 : bpow radix2 (3 - emax - prec + 2 * prec - 1) <= 1).
      { replace 1 with (bpow radix2 0) by reflexivity.
        apply bpow_le. unfold prec, emax. lia. }
      lra. }
  destruct (b64_Dekker_exact_of_format x y Hsafe Hund Hfmt) as [H1 H2].
  split.
  - rewrite H1. exact Hprod.
  - exact H2.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_Dekker_exact_of_format.
Print Assumptions b64_Dekker_int_exact.
