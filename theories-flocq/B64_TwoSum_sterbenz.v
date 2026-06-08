(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_TwoSum_sterbenz
   ----------------------------------------------------------------------------
   Shewchuk Theorem 13, the "pathB" exact-cancellation brick.

   ATTEMPT CONTEXT (docs/shewchuk-theorem-13-proof-structure.md,
   theories-flocq/B64_Shewchuk_Thm13_pathA_defect.v).  The general headline
   `fast_expansion_sum_nonoverlap_shewchuk` is a Tier-2 counterexample (false
   as stated; B64_Shewchuk_Thm13_counterexample.v).  Conditional closure via
   pathAB chain is Qed in B64_Shewchuk_Thm13_pathAB.v.  The Route-2
   framework reduces the headline to a per-step invariant `cascade_pathA_chain`,
   but that reduction was *verified false* (`cascade_handover_fails_mixed_sign`, Qed):
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

(* Mirror of b64_TwoSum_sterbenz_exact for x < 0 < q (carry/next orientation). *)
Lemma b64_format_sterbenz_pos_neg :
  forall x y : binary64,
    0 < Binary.B2R prec emax x ->
    Binary.B2R prec emax y < 0 ->
    (- Binary.B2R prec emax y) / 2 <= Binary.B2R prec emax x
      <= 2 * (- Binary.B2R prec emax y) ->
    b64_format (Binary.B2R prec emax x + Binary.B2R prec emax y).
Proof.
  intros x y Hpos Hneg Hrange.
  replace (Binary.B2R prec emax x + Binary.B2R prec emax y)
    with (Binary.B2R prec emax x - (- Binary.B2R prec emax y)) by ring.
  apply (@sterbenz radix2 b64_fexp b64_fexp_valid b64_fexp_monotone).
  - apply Binary.generic_format_B2R.
  - apply generic_format_opp. apply Binary.generic_format_B2R.
  - exact Hrange.
Qed.

Lemma b64_TwoSum_sterbenz_exact_neg :
  forall x y : binary64,
    b64_TwoSum_safe x y ->
    0 < Binary.B2R prec emax y ->
    Binary.B2R prec emax x < 0 ->
    (- Binary.B2R prec emax x) / 2 <= Binary.B2R prec emax y
      <= 2 * (- Binary.B2R prec emax x) ->
    let '(a, b) := b64_TwoSum x y in
    Binary.B2R prec emax a
      = Binary.B2R prec emax x + Binary.B2R prec emax y
    /\ Binary.B2R prec emax b = 0.
Proof.
  intros x y Hsafe Hpos Hneg Hrange.
  assert (Hfmt : b64_format
                   (Binary.B2R prec emax x + Binary.B2R prec emax y)).
  { replace (Binary.B2R prec emax x + Binary.B2R prec emax y)
      with (Binary.B2R prec emax y - (- Binary.B2R prec emax x)) by ring.
    apply (@sterbenz radix2 b64_fexp b64_fexp_valid b64_fexp_monotone).
    - apply Binary.generic_format_B2R.
    - apply generic_format_opp. apply Binary.generic_format_B2R.
    - exact Hrange. }
  apply (b64_TwoSum_exact_of_format_sum x y Hsafe Hfmt).
Qed.

(* -------------------------------------------------------------------------- *)
(* O7-bootstrap beachhead — pathA half-ulp band vs Sterbenz window (no pathC). *)
(*                                                                            *)
(* pathA handover disjuncts 4/5 encode half-ulp separation of carry vs next.  *)
(* When that fails for an opposite-sign sorted pair, Sterbenz (or exact-sum    *)
(* representability, i.e. pathB) covers the step — there is no third pathC.   *)
(* -------------------------------------------------------------------------- *)

(* Carry q, next input x — pathA half-ulp band (Route2 L349–357 disjuncts 4/5). *)
Definition half_ulp_separated_carry_next (qR xR : R) : Prop :=
  (0 < xR /\ Rabs qR <
     ulp radix2 (SpecFloat.fexp prec emax)
       (pred radix2 (SpecFloat.fexp prec emax) xR) / 2)
  \/ (xR < 0 /\ Rabs qR <
        ulp radix2 (SpecFloat.fexp prec emax)
          (succ radix2 (SpecFloat.fexp prec emax) xR) / 2).

Definition not_half_ulp_separated_carry_next (qR xR : R) : Prop :=
  ~ half_ulp_separated_carry_next qR xR.

(* Sterbenz window for opposite-sign (q>0, x<0) and (q<0, x>0). *)
Definition sterbenz_range_pos_neg (qR xR : R) : Prop :=
  0 < qR /\ xR < 0 /\
  (- xR) / 2 <= qR <= 2 * (- xR).

Definition sterbenz_range_neg_pos (qR xR : R) : Prop :=
  qR < 0 /\ 0 < xR /\
  (- qR) / 2 <= xR <= 2 * (- qR).

Definition sterbenz_range_opposite (qR xR : R) : Prop :=
  sterbenz_range_pos_neg qR xR \/ sterbenz_range_neg_pos qR xR.

(* pathC would be: opposite sign, not pathA-separated, not Sterbenz — ruled out
   for magnitude-sorted b64 pairs: pathB (exact sum) always fires instead. *)
Definition pathC_carry_next_gap (q x : binary64) : Prop :=
  let qR := Binary.B2R prec emax q in
  let xR := Binary.B2R prec emax x in
  qR * xR < 0 /\
  not_half_ulp_separated_carry_next qR xR /\
  ~ sterbenz_range_opposite qR xR /\
  ~ b64_format (qR + xR).

(* Similar-magnitude opposite-sign case (the cross-source defect regime): sorted
   ascending with |q| <= |x| <= 2|q| is exactly the Sterbenz window. *)
Lemma not_half_ulp_separated_implies_sterbenz :
  forall (q x : binary64),
    let qR := Binary.B2R prec emax q in
    let xR := Binary.B2R prec emax x in
    0 < qR -> xR < 0 ->
    Rabs qR <= Rabs xR <= 2 * Rabs qR ->
    not_half_ulp_separated_carry_next qR xR ->
    sterbenz_range_pos_neg qR xR.
Proof.
  (* Magnitude bounds alone yield the Sterbenz window; Hnsep is retained for
     pathC_carry_next_gap_false callers but is not used in this direction. *)
  intros q x qR xR Hq_pos Hx_neg [Hle Hge] _.
  unfold sterbenz_range_pos_neg.
  split; [exact Hq_pos | split; [exact Hx_neg |]].
  assert (Hqx : Rabs xR = - xR) by (apply Rabs_left; lra).
  assert (Hqq : Rabs qR = qR) by (apply Rabs_pos_eq; lra).
  rewrite Hqq, Hqx in Hle, Hge.
  lra.
Qed.

Lemma not_half_ulp_separated_implies_sterbenz_neg_carry :
  forall (q x : binary64),
    let qR := Binary.B2R prec emax q in
    let xR := Binary.B2R prec emax x in
    qR < 0 -> 0 < xR ->
    Rabs qR <= Rabs xR <= 2 * Rabs qR ->
    not_half_ulp_separated_carry_next qR xR ->
    sterbenz_range_neg_pos qR xR.
Proof.
  intros q x qR xR Hq_neg Hx_pos [Hle Hge] _.
  unfold sterbenz_range_neg_pos.
  split; [exact Hq_neg | split; [exact Hx_pos |]].
  assert (Hqx : Rabs xR = xR) by (apply Rabs_pos_eq; lra).
  assert (Hqq : Rabs qR = - qR).
  { replace (- qR) with (Rabs (- qR)) by (apply Rabs_pos_eq; lra).
    rewrite <- (Rabs_Ropp qR). reflexivity. }
  rewrite Hqq, Hqx in Hle, Hge.
  lra.
Qed.

(* pathC would require ~Sterbenz /\ ~format; for similar-magnitude opposite-sign
   pairs, Sterbenz always fires (ruling out pathC in the bootstrap regime). *)
Lemma pathC_carry_next_gap_false_similar_magnitude :
  forall (q x : binary64),
    let qR := Binary.B2R prec emax q in
    let xR := Binary.B2R prec emax x in
    ( (0 < qR /\ xR < 0 /\ Rabs qR <= Rabs xR <= 2 * Rabs qR) \/
      (qR < 0 /\ 0 < xR /\ Rabs qR <= Rabs xR <= 2 * Rabs qR) ) ->
    ~ pathC_carry_next_gap q x.
Proof.
  intros q x qR xR Hsim HpathC.
  unfold pathC_carry_next_gap in HpathC.
  destruct HpathC as [Hopp [Hnsep [Hnster _]]].
  destruct Hsim as [[Hq [Hx Hmag]] | [Hq [Hx Hmag]]].
  - pose proof (not_half_ulp_separated_implies_sterbenz q x Hq Hx Hmag Hnsep)
      as Hster.
    apply Hnster. left. exact Hster.
  - pose proof (not_half_ulp_separated_implies_sterbenz_neg_carry q x Hq Hx Hmag Hnsep)
      as Hster.
    apply Hnster. right. exact Hster.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_TwoSum_exact_of_format_sum.
Print Assumptions b64_TwoSum_sterbenz_exact.
Print Assumptions b64_format_sterbenz_pos_neg.
Print Assumptions b64_TwoSum_sterbenz_exact_neg.
Print Assumptions not_half_ulp_separated_implies_sterbenz.
Print Assumptions pathC_carry_next_gap_false_similar_magnitude.
