(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryClean
   ----------------------------------------------------------------------------
   Going beyond Priest and Shewchuk: a cleanup pass for the output of the
   corpus's `fast_expansion_sum` that does no rounding work at all, measured
   against Shewchuk's Compress (1997 Fig. 15) as the baseline.

   THE PROBLEM.  B64_Priest_FES_counterexample.v shows `fast_expansion_sum`
   does not keep even Shewchuk-nonoverlapping output on Priest-valid input.
   Priest repairs his sum with a renormalization pass; Shewchuk's cleanup is
   Compress, two Fast-Two-Sum sweeps under IEEE round-to-nearest-even.

   THE ALGORITHM (`carry_clean`).  One sweep over the components, largest
   first, with a stack whose top is compared to each incoming nonzero x:

     top = -x   ->  pop          (the pair cancels exactly; no arithmetic)
     top =  x   ->  pop, carry 2x and compare again   (one exact doubling)
     otherwise  ->  push x

   Zeros are skipped.  The idea is the carry of binary addition: the
   overlaps observed in `fast_expansion_sum` output on Priest-valid input are
   pairs of equal-magnitude powers of two, created by two round-half-to-even
   ties in a row (see the traces below).  Equal pairs carry, opposite pairs
   cancel, and nothing is ever rounded.  `cancel_clean` is the same sweep
   without the carry, kept as the first (refuted) plan.

   WHAT IS PROVED, all Qed:

     COST     carry_clean_flops_le       flops(carry_clean e) <= |e|
              compress_flops_ge          flops(Compress e)    >= 3 (|e| - 1)
              carry_clean_fewer_flops    strictly fewer flops for |e| >= 2;
                                         comparisons NOT counted (below)
     EXACT    carry_clean_exact          the exact sum is preserved, given
                                         finite components whose absolute
                                         values sum below 2^emax
     QEX 1    cancel_clean_priest_false  cancelling alone does not give a
                                         nonoverlapping result on
                                         Priest-valid input
     QEX 2    carry_clean_beyond_priest_false
                                         carry_clean does not give one when
                                         only ONE input is Priest-valid and
                                         the other is merely nonoverlapping
     CORE     carry_clean_priest_core    rounding-free: on any list whose
                                         nonzero components split into
                                         singles, twins (x, x) and anti pairs
                                         (x, -x) with strictly decreasing
                                         block magnitudes (the PATTERN),
                                         carry_clean IS the block reduction
                                         -- anti pairs deleted, twins doubled
                                         exactly -- and the sum is preserved.
                                         Nonoverlap is not concluded here.
              carry_clean_nonoverlap_of_shape
                                         if the reduction is also
                                         nonoverlapping, so is the output
                                         (that hypothesis passed through)
     BRIDGE   carry_clean_priest_target_of_bridge
                                         the two open parts below imply
                                         carry_clean_priest_target -- ONE
                                         way: the bridge is strictly stronger
     RUNG 2   (B64_CarryCleanRung2.v)    three components in total: both
                                         bridge parts and the target, proved
     BASE     fes_carry_bridge_base_case the trivial base case: at most two
                                         components in total, one TwoSum, no
                                         twins or anti pairs; and
              carry_clean_priest_target_base_case   the target there
     SAFETY   b64_TwoSum_safe_bound      one TwoSum never overflows for
                                         |x|, |y| <= 2^(emax-4)
              fes_cascade_safe           no TwoSum of the sum's cascade
                                         overflows when abs_sum e + abs_sum f
                                         <= 2^(emax-5): every accumulator
                                         stays below 2 * abs_sum, because
                                         RN(q + e) is no further from q + e
                                         than q is

   The flop counts are produced by the algorithm definitions themselves
   (each returns its result paired with the number of `b64_plus` /
   `b64_minus` / `b64_mult` calls it made); `carry_clean` and
   `shewchuk_compress` are the first projections.  Comparisons are NOT
   counted: Compress makes 2(m-1) zero tests; carry_clean makes at most 5m
   (one zero test per component, up to two equality tests per stack step,
   at most 2m steps).  Counting everything, carry_clean is at most 6m and
   Compress at least 5(m-1): fewer flops, not proved cheaper overall, and
   carry_clean's branches are data-dependent.  On witness 1 the flop counts
   are pinned: 1 for carry_clean (`q1_carry_flops`), 21 for Compress
   (`q1_compress_flops`).

   WHAT IS NOT PROVED (do not overclaim).  The correctness claim that would
   make the cost result matter -- that `carry_clean` output IS nonoverlapping
   on `fast_expansion_sum` of two Priest-valid inputs -- is stated below as
   `carry_clean_priest_target`, a Definition, and is OPEN.  The core reduces
   it to a two-part bridge, both parts Definitions, both OPEN:
     (a) `fes_priest_carry_pattern`: the sum's zero-filtered output splits
         into blocks with strictly decreasing magnitudes;
     (b) `fes_priest_reduction_nonoverlap`: the block reduction of such an
         output is nonoverlapping -- the round-to-even content.
   The implication is one way (`carry_clean_priest_target_of_bridge`).  The
   bridge is strictly STRONGER than the target: strict keys exclude carry
   cascades (a 2x followed by a twin (x, x) carries twice, which `cc_push`
   handles and `carry_pattern` rejects).  So a counterexample to the bridge
   refutes the bridge only; whether it also refutes the target has to be
   checked on its own.  `q1_carry_shape` shows a real sum attains the
   shape, so the bridge is not vacuous.  "Rounding-free" describes the
   CONTENT of the core: its axiom footprint still carries `classic`, because
   `cblock_reduce` mentions `b64_mult` (Flocq C1).

   EVIDENCE (reconnaissance, not proof obligation; every number below is
   reproducible with tests/CarryCleanExhaustive, whose header lists the
   exact command lines): an exhaustive check in a p-bit round-to-nearest-
   even model finds carry_clean nonoverlapping on every Priest-valid input
   pair at p = 3 (lengths <= 3, 366,766,976 pairs; lengths <= 4,
   4,670,763,328), p = 4 (lengths <= 3, 2,146,417,920), p = 2 (lengths
   <= 4, 148,581,504; lengths <= 5, 1,196,510,640) and p = 5 (lengths <= 2,
   420,560,896), and under an underflow floor at p = 2, 3, 4; against 680
   failures for `cancel_clean` at p = 3.  The harness also counts bridge
   parts (a) and (b) and carry cascades; its header records those counts
   per run (0, 0 and 0 on every run that printed them).
   Nor is `carry_clean` a drop-in replacement for Compress: QEX 2 shows its
   domain is narrower, and Compress repairs both QEX witnesses
   (`q1_compress_nonoverlapping`, `q2_compress_nonoverlapping`).

   THE BASELINE.  `shewchuk_compress` transcribes Fig. 15: a top-down sweep
   of Fast-Two-Sum keeping each nonzero error as the new accumulator, then a
   bottom-up sweep emitting nonzero errors.  `b64_Fast2Sum` (B64_Pff_bridge)
   is three operations, so Compress costs 3 (m - 1) + 3 g flops, g the number
   of components kept by the first sweep.

   NTS / JTS COUNTERPART.  None in-library: JTS and NTS compute robust
   orientation with double-double arithmetic (`CGAlgorithmsDD`, `DD`), not
   with Shewchuk expansions.  This lane serves the corpus's exact
   orientation (Orient_b64_expansion.v), the predicate behind
   `Orientation.Index`, where expansion sums are chained.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human review pending.
     Assisted-by: Claude
   ========================================================================== *)

(* Umbrella.  The declarations live in three parts, byte-identical, each with
   its own `Print Assumptions` footer (docs/macro-meso-micro.md, module split
   gate). *)
From NTS.Proofs.Flocq Require Export B64_CarryCleanAlgo B64_CarryCleanWitness
     B64_CarryCleanCore.
