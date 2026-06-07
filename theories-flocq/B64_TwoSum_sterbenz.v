(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_TwoSum_sterbenz
   ----------------------------------------------------------------------------
   Shewchuk Theorem 13, the "pathB" exact-cancellation brick.

   ATTEMPT CONTEXT (docs/shewchuk-theorem-13-proof-structure.md,
   theories-flocq/B64_Shewchuk_Thm13_pathA_defect.v).  The general headline
   `fast_expansion_sum_nonoverlap_shewchuk` is Admitted/deferred.  The Route-2
   framework reduces it to a per-step invariant `cascade_pathA_chain`, but that
   reduction was *verified false* (`cascade_handover_fails_mixed_sign`, Qed):
   when the two magnitude-smallest cascade inputs are cross-source,
   opposite-sign, similar-magnitude, every disjunct of
   `cascade_invariant_handover` (pathA only) fails.

   The documented fix is to widen the per-step invariant from pathA-only to
   pathA OR pathB, where pathB is exactly this case: an opposite-sign,
   similar-magnitude pair.  Its defining property -- the reason the cascade
   survives it -- is that the `b64_TwoSum` of such a pair is EXACT: by Sterbenz,
   the sum is representable, so the high part is the exact sum and the error
   term is identically zero (which `compress` then deletes, and the cascade
   continues with a strictly smaller carry).

   This file proves that defining property, the load-bearing arithmetic fact
   for pathB:

     - `b64_TwoSum_exact_of_format_sum` : whenever `B2R x + B2R y` is
        representable, `b64_TwoSum x y = (exact sum, 0)`.  (General: also
        covers integer sums, not just Sterbenz cancellation.)
     - `b64_TwoSum_sterbenz_exact` : the pathB instance -- for an opposite-sign
        pair in Sterbenz range, the error term is zero and the high part is the
        exact sum.

   WHAT REMAINS for the full headline (NOT in this file): adding the pathB
   disjunct to `cascade_invariant_handover` and re-proving that the cascade
   step preserves the widened invariant and keeps the output
   `nonoverlap_shewchuk` (`cascade_run_output_nonoverlap`).  That is the
   multi-day magnitude-bookkeeping remainder the proof-structure doc estimates;
   this brick supplies its arithmetic core.

   Pure-Flocq (binary64); no `Admitted` / `Axiom` / `Parameter` introduced.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From Flocq Require Import IEEE754.Binary Core.
From Flocq Require Import Sterbenz.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
                                     B64_Pff_bridge.
Local Open Scope R_scope.

(* Rounding fixes zero (instance of b64_round_generic at 0). *)
Lemma b64_round_0 : b64_round 0 = 0.
Proof. apply b64_round_generic. apply generic_format_0. Qed.

(* -------------------------------------------------------------------------- *)
(* Core: when the exact sum is representable, TwoSum has a zero error term.    *)
(*                                                                            *)
(* Trace (each intermediate is a representable value, so its round is the      *)
(* identity):                                                                  *)
(*   a   = round(x + y)           = x + y       (hypothesis: format (x+y))     *)
(*   x'  = round(a - x)           = round(y)    = y                            *)
(*   a-x'= round(a - x')          = round(x)    = x                            *)
(*   dx  = round(x - (a - x'))    = round(0)    = 0                            *)
(*   dy  = round(y - x')          = round(0)    = 0                            *)
(*   b   = round(dx + dy)         = round(0)    = 0                            *)
(* -------------------------------------------------------------------------- *)

Lemma b64_TwoSum_exact_of_format_sum :
  forall x y : binary64,
    b64_TwoSum_safe x y ->
    b64_format (Binary.B2R prec emax x + Binary.B2R prec emax y) ->
    let '(a, b) := b64_TwoSum x y in
    Binary.B2R prec emax a
      = Binary.B2R prec emax x + Binary.B2R prec emax y
    /\ Binary.B2R prec emax b = 0.
Proof.
  intros x y Hsafe Hfmt.
  destruct Hsafe as [Hsa [Hsxp [Hsaxp [Hsdx [Hsdy Hsb]]]]].
  unfold b64_TwoSum.
  pose proof (b64_plus_correct  x y Hsa)  as [HBa _].
  pose proof (b64_minus_correct (b64_plus x y) x Hsxp) as [HBxp _].
  pose proof (b64_minus_correct (b64_plus x y)
                (b64_minus (b64_plus x y) x) Hsaxp) as [HBaxp _].
  pose proof (b64_minus_correct x
                (b64_minus (b64_plus x y) (b64_minus (b64_plus x y) x)) Hsdx)
    as [HBdx _].
  pose proof (b64_minus_correct y (b64_minus (b64_plus x y) x) Hsdy) as [HBdy _].
  pose proof (b64_plus_correct
                (b64_minus x
                   (b64_minus (b64_plus x y) (b64_minus (b64_plus x y) x)))
                (b64_minus y (b64_minus (b64_plus x y) x)) Hsb) as [HBb _].
  pose proof (Binary.generic_format_B2R prec emax x) as FxR.
  pose proof (Binary.generic_format_B2R prec emax y) as FyR.
  (* a = x + y exactly *)
  rewrite (b64_round_generic _ Hfmt) in HBa.
  (* x' = round(a - x) = round(y) = y *)
  rewrite HBa in HBxp.
  replace (Binary.B2R prec emax x + Binary.B2R prec emax y
           - Binary.B2R prec emax x)
    with (Binary.B2R prec emax y) in HBxp by ring.
  rewrite (b64_round_generic _ FyR) in HBxp.
  (* a - x' = round(a - x') = round(x) = x *)
  rewrite HBa, HBxp in HBaxp.
  replace (Binary.B2R prec emax x + Binary.B2R prec emax y
           - Binary.B2R prec emax y)
    with (Binary.B2R prec emax x) in HBaxp by ring.
  rewrite (b64_round_generic _ FxR) in HBaxp.
  (* dx = round(x - (a - x')) = round(0) = 0 *)
  rewrite HBaxp in HBdx.
  replace (Binary.B2R prec emax x - Binary.B2R prec emax x) with 0 in HBdx by ring.
  rewrite b64_round_0 in HBdx.
  (* dy = round(y - x') = round(0) = 0 *)
  rewrite HBxp in HBdy.
  replace (Binary.B2R prec emax y - Binary.B2R prec emax y) with 0 in HBdy by ring.
  rewrite b64_round_0 in HBdy.
  (* b = round(dx + dy) = round(0) = 0 *)
  rewrite HBdx, HBdy in HBb.
  replace (0 + 0) with 0 in HBb by ring.
  rewrite b64_round_0 in HBb.
  split; [ exact HBa | exact HBb ].
Qed.

(* -------------------------------------------------------------------------- *)
(* pathB instance: an opposite-sign pair in Sterbenz range cancels exactly.   *)
(*                                                                            *)
(* For `x > 0`, `y < 0` with `|y|/2 <= x <= 2|y|` (the similar-magnitude       *)
(* window), `x + y = x - (-y)` is representable by Sterbenz, so TwoSum's error *)
(* term is zero.                                                               *)
(* -------------------------------------------------------------------------- *)

Lemma b64_TwoSum_sterbenz_exact :
  forall x y : binary64,
    b64_TwoSum_safe x y ->
    (- Binary.B2R prec emax y) / 2 <= Binary.B2R prec emax x
      <= 2 * (- Binary.B2R prec emax y) ->
    let '(a, b) := b64_TwoSum x y in
    Binary.B2R prec emax a
      = Binary.B2R prec emax x + Binary.B2R prec emax y
    /\ Binary.B2R prec emax b = 0.
Proof.
  intros x y Hsafe Hrange.
  assert (Hfmt : b64_format
                   (Binary.B2R prec emax x + Binary.B2R prec emax y)).
  { replace (Binary.B2R prec emax x + Binary.B2R prec emax y)
      with (Binary.B2R prec emax x - (- Binary.B2R prec emax y)) by ring.
    apply (@sterbenz radix2 b64_fexp b64_fexp_valid b64_fexp_monotone).
    - apply Binary.generic_format_B2R.
    - apply generic_format_opp. apply Binary.generic_format_B2R.
    - exact Hrange. }
  apply (b64_TwoSum_exact_of_format_sum x y Hsafe Hfmt).
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_TwoSum_exact_of_format_sum.
Print Assumptions b64_TwoSum_sterbenz_exact.
