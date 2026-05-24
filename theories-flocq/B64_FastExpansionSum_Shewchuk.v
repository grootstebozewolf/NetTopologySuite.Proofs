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
(* PIECE 4: sum-correctness of fast_expansion_sum.                            *)
(*                                                                            *)
(* Composes three structural results:                                         *)
(*   1. `expansion_R_sort_by_abs` (this file): sort preserves expansion_R.   *)
(*   2. `expansion_R_app` (B64_FastExpansionSum.v): expansion_R distributes  *)
(*      over append.                                                          *)
(*   3. `b64_grow_expansion_aux_correct` (B64_FastExpansionSum.v):           *)
(*      cascade preserves the running sum.                                    *)
(*                                                                            *)
(* Safety: the cascade input (head of sorted list as accumulator, tail as    *)
(* cascade input) must satisfy the per-step TwoSum safety chain.             *)
(* -------------------------------------------------------------------------- *)

Definition fast_expansion_sum_safe (e f : list binary64) : Prop :=
  match sort_by_abs (e ++ f) with
  | nil => True
  | x :: xs => b64_grow_expansion_aux_safe x xs
  end.

Theorem fast_expansion_sum_correct :
  forall (e f : list binary64),
    fast_expansion_sum_safe e f ->
    expansion_R (fast_expansion_sum e f) = expansion_R e + expansion_R f.
Proof.
  intros e f Hsafe.
  unfold fast_expansion_sum, fast_expansion_sum_safe in *.
  destruct (sort_by_abs (e ++ f)) as [|x xs] eqn:Hsort.
  - (* Sorted list is empty -- e ++ f had expansion_R 0. *)
    cbn [expansion_R].
    pose proof (expansion_R_sort_by_abs (e ++ f)) as Hsum.
    rewrite Hsort in Hsum. cbn in Hsum.
    pose proof (expansion_R_app e f) as Happ.
    lra.
  - (* Apply the cascade invariant. *)
    destruct (b64_grow_expansion_aux x xs) as [hs qfinal] eqn:Hrec.
    pose proof (b64_grow_expansion_aux_correct xs x Hsafe hs qfinal Hrec) as Hinv.
    cbn [expansion_R].
    rewrite expansion_R_rev.
    pose proof (expansion_R_sort_by_abs (e ++ f)) as Hsum.
    rewrite Hsort in Hsum. cbn [expansion_R] in Hsum.
    rewrite expansion_R_app in Hsum.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* PIECE 5a: sort correctness.                                                *)
(*                                                                            *)
(* `sort_by_abs` produces an ascending-by-magnitude list.  Standard           *)
(* insertion-sort correctness.  Structural foundation for piece 5b            *)
(* (the cascade-nonoverlap proof, deferred to a follow-up).                   *)
(* -------------------------------------------------------------------------- *)

Inductive sorted_asc : list binary64 -> Prop :=
  | sorted_asc_nil : sorted_asc nil
  | sorted_asc_singleton : forall x, sorted_asc (x :: nil)
  | sorted_asc_cons : forall x y rest,
      Rabs (Binary.B2R prec emax x) <= Rabs (Binary.B2R prec emax y) ->
      sorted_asc (y :: rest) ->
      sorted_asc (x :: y :: rest).

Lemma sorted_asc_tail :
  forall x xs, sorted_asc (x :: xs) -> sorted_asc xs.
Proof.
  intros x xs H. inversion H; subst.
  - apply sorted_asc_nil.
  - assumption.
Qed.

Lemma sorted_asc_cons_head :
  forall x xs,
    sorted_asc xs ->
    (forall y rest, xs = y :: rest ->
      Rabs (Binary.B2R prec emax x) <= Rabs (Binary.B2R prec emax y)) ->
    sorted_asc (x :: xs).
Proof.
  intros x xs Hxs Hbnd.
  destruct xs as [|y rest].
  - apply sorted_asc_singleton.
  - apply sorted_asc_cons.
    + apply (Hbnd y rest). reflexivity.
    + exact Hxs.
Qed.

Lemma insert_by_abs_sorted :
  forall (x : binary64) (xs : list binary64),
    sorted_asc xs ->
    sorted_asc (insert_by_abs x xs).
Proof.
  intros x xs.
  induction xs as [|y ys IH]; intros Hsorted.
  - cbn. apply sorted_asc_singleton.
  - cbn.
    destruct (Rle_dec (Rabs (Binary.B2R prec emax x))
                      (Rabs (Binary.B2R prec emax y))) as [Hle | Hgt].
    + apply sorted_asc_cons; assumption.
    + assert (Hgt' : Rabs (Binary.B2R prec emax y)
                     <= Rabs (Binary.B2R prec emax x)) by lra.
      apply sorted_asc_cons_head.
      * apply IH. apply (sorted_asc_tail y). exact Hsorted.
      * intros z rest Hz.
        destruct ys as [|w ws].
        -- cbn in Hz. inversion Hz; subst. exact Hgt'.
        -- cbn in Hz.
           destruct (Rle_dec (Rabs (Binary.B2R prec emax x))
                             (Rabs (Binary.B2R prec emax w))) as [Hxw | Hxw].
           ++ inversion Hz; subst. exact Hgt'.
           ++ inversion Hz; subst.
              inversion Hsorted; subst. assumption.
Qed.

Lemma sort_by_abs_sorted :
  forall xs : list binary64,
    sorted_asc (sort_by_abs xs).
Proof.
  induction xs as [|x xs IH].
  - cbn. apply sorted_asc_nil.
  - cbn. apply insert_by_abs_sorted. exact IH.
Qed.

(* -------------------------------------------------------------------------- *)
(* PIECE 5b: nonoverlap_shewchuk preservation (DEFERRED).                     *)
(*                                                                            *)
(* Theorem statement (NOT compiled here -- the proof is multi-session work):  *)
(*                                                                            *)
(*   Theorem fast_expansion_sum_nonoverlap_shewchuk :                          *)
(*     forall (e f : list binary64),                                           *)
(*       fast_expansion_sum_safe e f ->                                        *)
(*       nonoverlap_shewchuk e ->                                              *)
(*       nonoverlap_shewchuk f ->                                              *)
(*       nonoverlap_shewchuk (fast_expansion_sum e f).                         *)
(*                                                                            *)
(* This is Shewchuk Theorem 13 (1997, ~1 page of dense magnitude analysis).  *)
(* Coq formalization estimate: 200-400 lines.  Requires:                      *)
(*                                                                            *)
(*   - A cascade invariant relating each accumulator Q_i to the inputs        *)
(*     processed so far (smallest-first, by sort_by_abs_sorted above).        *)
(*   - A magnitude chain showing the cascade's error sequence h_1, h_2,...   *)
(*     forms an appropriately ordered set after rev'ing.                      *)
(*   - The compress step (in nonoverlap_shewchuk's definition) removes any   *)
(*     internal zeros from exact-cascade steps; the magnitude chain on        *)
(*     non-zero h's gives the half-ulp bound that nonoverlap_strict needs.   *)
(*                                                                            *)
(* The sort-correctness lemmas above give the structural foundation: the     *)
(* cascade input is provably ordered, which is what Shewchuk's analysis      *)
(* relies on.                                                                 *)
(*                                                                            *)
(* Per the corpus's epistemic invariant (`scripts/check_admitted.sh`), the   *)
(* theorem is NOT stated here -- stating it without a proof OR a verified    *)
(* counterexample would create an unregistered gap.  Follow-up commits will  *)
(* land the proof when ready.                                                 *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions fast_expansion_sum.
Print Assumptions expansion_R_sort_by_abs.
Print Assumptions fast_expansion_sum_correct.
Print Assumptions sort_by_abs_sorted.
