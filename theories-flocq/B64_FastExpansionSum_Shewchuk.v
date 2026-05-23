(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_FastExpansionSum_Shewchuk
   ----------------------------------------------------------------------------
   Slice A Piece 3: Shewchuk's fast-expansion-sum at binary64.

   THE ALGORITHM
   -------------
   Two-phase:
     1. Merge the two input expansions into a single list sorted
        ASCENDING by magnitude.  Insertion sort by `Rabs (B2R x)`.
     2. Apply the TwoSum cascade (reusing `b64_grow_expansion_aux`
        from B64_FastExpansionSum.v) from smallest to largest,
        producing the output expansion `qfinal :: rev hs`
        (largest first, our nonoverlap convention).

   The cascade structure is structurally identical to grow-expansion's
   cascade -- the difference is the SORT preprocessing, which is what
   gives fast-expansion-sum its general-magnitude reach.

   WHY THIS WORKS WHERE GROW-EXPANSION DOESN'T
   -------------------------------------------
   Grow-expansion adds a single new value to an expansion; if the
   new value's magnitude is comparable to the expansion's largest
   component (the orient2d case), the cascade hits the boundary issues
   documented in `docs/stage-d-grow-expansion-nonoverlap-tangent.md`.

   Fast-expansion-sum sorts FIRST, so the cascade always processes
   smallest-to-largest.  Each step's accumulator is bounded relative
   to the next input, which is what Shewchuk Theorem 13 relies on.

   PIECE 3 SCOPE (this file)
   --------------------------
   Definition only -- no nonoverlap proof here (that's piece 5).  But
   the SUM-PRESERVATION through the sort step is included as small
   structural helpers, since piece 4 (sum-correctness of the full
   algorithm) will compose them with the cascade's sum invariant.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.
From Stdlib Require Import List.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import B64_lib.
From NTS.Proofs.Flocq Require Import B64_Expansion.
From NTS.Proofs.Flocq Require Import B64_Expansion_Shewchuk.
From NTS.Proofs.Flocq Require Import B64_Pff_bridge.
From NTS.Proofs.Flocq Require Import B64_FastExpansionSum.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Insertion sort by `Rabs (B2R x)` ascending.                                *)
(*                                                                            *)
(* `Rle_dec` is classical-decidable (returns `{a <= b} + {b < a}`).  It       *)
(* compiles to a constructor, so the sort is computable.  Same classical     *)
(* reasoning as the rest of the expansion-arithmetic stack.                  *)
(* -------------------------------------------------------------------------- *)

Fixpoint insert_by_abs (x : binary64) (xs : list binary64) : list binary64 :=
  match xs with
  | nil => x :: nil
  | y :: ys =>
      if Rle_dec (Rabs (Binary.B2R prec emax x))
                 (Rabs (Binary.B2R prec emax y))
      then x :: y :: ys
      else y :: insert_by_abs x ys
  end.

Fixpoint sort_by_abs (xs : list binary64) : list binary64 :=
  match xs with
  | nil => nil
  | x :: xs' => insert_by_abs x (sort_by_abs xs')
  end.

(* -------------------------------------------------------------------------- *)
(* Sum preservation through the sort step.                                    *)
(*                                                                            *)
(* Insertion sort permutes elements; `expansion_R` sums them.  Sum is        *)
(* invariant under permutation, expressed here as two structural lemmas.    *)
(* These are piece-4's sum-correctness's load-bearing helpers.               *)
(* -------------------------------------------------------------------------- *)

Lemma expansion_R_insert_by_abs :
  forall (x : binary64) (xs : list binary64),
    expansion_R (insert_by_abs x xs) = Binary.B2R prec emax x + expansion_R xs.
Proof.
  intros x xs. revert x.
  induction xs as [|y ys IH]; intros x.
  - simpl. lra.
  - simpl.
    destruct (Rle_dec (Rabs (Binary.B2R prec emax x))
                      (Rabs (Binary.B2R prec emax y))).
    + simpl. lra.
    + simpl. rewrite IH. lra.
Qed.

Lemma expansion_R_sort_by_abs :
  forall xs : list binary64,
    expansion_R (sort_by_abs xs) = expansion_R xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl. rewrite expansion_R_insert_by_abs. rewrite IH. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* HEADLINE: fast_expansion_sum.                                              *)
(*                                                                            *)
(* Merge the two input expansions, sort by magnitude ascending, run the     *)
(* TwoSum cascade.  The cascade reuses `b64_grow_expansion_aux` from        *)
(* B64_FastExpansionSum.v, which produces `(hs, qfinal)` with `qfinal` the  *)
(* final accumulator and `hs` the error sequence smallest-first.  Output    *)
(* shape `qfinal :: rev hs` puts the accumulated head at front (largest)   *)
(* and the smallest error at the tail -- matching `nonoverlap_strict`'s    *)
(* descending-magnitude convention.                                          *)
(* -------------------------------------------------------------------------- *)

Definition fast_expansion_sum (e f : list binary64) : list binary64 :=
  match sort_by_abs (e ++ f) with
  | nil => nil
  | x :: xs =>
      let '(hs, qfinal) := b64_grow_expansion_aux x xs in
      qfinal :: rev hs
  end.

(* -------------------------------------------------------------------------- *)
(* PIECE 4 / 5 PROOF OBLIGATIONS (deferred to follow-up commits)              *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* Piece 4 (sum-correctness): under appropriate safety preconditions,        *)
(*   `expansion_R (fast_expansion_sum e f) = expansion_R e + expansion_R f`. *)
(* Proof structure: combine `expansion_R_sort_by_abs` (this file) with the  *)
(* existing `b64_grow_expansion_aux_correct` (B64_FastExpansionSum.v).      *)
(*                                                                            *)
(* Piece 5 (nonoverlap-preservation): under input expansions being          *)
(* `nonoverlap_shewchuk` AND appropriate safety, the output is              *)
(* `nonoverlap_shewchuk`.  Proof structure: Shewchuk Theorem 13              *)
(* formalisation; per-step `b64_TwoSum_nonoverlap` carries the half-ulp     *)
(* invariant, magnitude bookkeeping through the sort ensures the chain      *)
(* propagates correctly.                                                     *)
(*                                                                            *)
(* This file lands the definition (piece 3) + the sort-level sum            *)
(* invariance (piece-4 dependency).  Pieces 4/5 are next commits.            *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions fast_expansion_sum.
Print Assumptions expansion_R_sort_by_abs.
