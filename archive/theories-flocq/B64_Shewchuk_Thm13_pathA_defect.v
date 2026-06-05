(* ==========================================================================
   B64_Shewchuk_Thm13_pathA_defect.v
   --------------------------------------------------------------------------
   FINDING (verified): the Route-2 reduction of the deferred headline
   `fast_expansion_sum_nonoverlap_shewchuk` to `cascade_pathA_chain` is
   TOO STRONG -- the pathA-only invariant is *false* on a configuration
   reachable from valid inputs, so it can never be discharged
   unconditionally.  The next attempt should generalise the invariant to
   pathA OR pathB (mixed-provenance cancellation), not grind the pathA chain.

   Why.  `B64_FastExpansionSum_Shewchuk_Route2.v` proves the conditional
   headline `fast_expansion_sum_nonoverlap_shewchuk_general_conditional`,
   whose hypothesis is, for the two smallest (magnitude-sorted) inputs
   `x` (carry of the initial state) and `x2`:

       cascade_invariant_handover (initial_cascade_state x prov) ((x2,_)::_)

   which (after `b64_TwoSum_safe`) requires the carry/next-input pair to be
   same-sign, or carry = 0, or the carry to be < 1/2 ulp of (pred/succ of)
   the next input -- i.e. >= ~53 bits smaller.

   `nonoverlap_shewchuk` constrains only SAME-SOURCE consecutive elements.
   After the magnitude merge-sort, the two globally-smallest elements can
   come from DIFFERENT sources, with similar magnitude and OPPOSITE sign --
   between which there is no half-ulp separation.  Then every handover
   disjunct fails.  The lemma below proves exactly that.

   Concrete witness: e = [1.0], f = [-1.0].  Each singleton is trivially
   `nonoverlap_shewchuk`; the sum is 0 so the headline
   `nonoverlap_shewchuk (fast_expansion_sum e f)` is TRUE (the output
   compresses to []).  Yet `cascade_pathA_chain (initial ...) ...` is FALSE
   (the lemma applies with B2R x = 1, B2R x2 = -1, and
   1/2 ulp(succ(-1)) ~ 2^-53 <= 1).  So the headline is true while the
   Route-2 reduction is false: the reduction is unsound, not merely hard.

   `cascade_pathA_chain` contains `cascade_invariant_handover` on the next
   state as a conjunct, so falsifying the handover falsifies the whole chain.

   See docs/shewchuk-theorem-13-proof-structure.md (amended).
   ========================================================================== *)

From Stdlib Require Import Reals ZArith List Lra.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
                                      B64_Expansion B64_Expansion_Shewchuk
                                      B64_Pff_bridge B64_FastExpansionSum
                                      B64_FastExpansionSum_Shewchuk
                                      B64_FastExpansionSum_Shewchuk_Route2.

Open Scope R_scope.

(* The handover clause (hence `cascade_pathA_chain`) is UNSATISFIABLE when the
   leading carry is positive, the next input is negative, and the carry is not
   ~53 bits smaller than that input -- the cross-source opposite-sign case. *)
Lemma cascade_handover_fails_mixed_sign :
  forall (x x2 : binary64) (prov p2 : provenance) (rest : list tagged_b64),
    0 < Binary.B2R prec emax x ->
    Binary.B2R prec emax x2 < 0 ->
    ulp radix2 (SpecFloat.fexp prec emax)
        (succ radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax x2)) / 2
      <= Binary.B2R prec emax x ->
    ~ cascade_invariant_handover (initial_cascade_state x prov) ((x2, p2) :: rest).
Proof.
  intros x x2 prov p2 rest Hpos Hneg Hsep Hho.
  destruct prov;
    unfold cascade_invariant_handover, initial_cascade_state in Hho;
    cbn [cs_carry] in Hho;
    destruct Hho as [_ Hdisj];
    rewrite (Rabs_pos_eq (Binary.B2R prec emax x)) in Hdisj by lra;
    destruct Hdisj as [[_ H]|[[H _]|[H|[[H _]|[_ H]]]]]; lra.
Qed.

Print Assumptions cascade_handover_fails_mixed_sign.
