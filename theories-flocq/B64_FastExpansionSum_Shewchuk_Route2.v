(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_FastExpansionSum_Shewchuk_Route2
   ----------------------------------------------------------------------------
   Slice A Piece 5b -- Route 2 framework.

   This file is Session 1 of the Route 2 design for closing
   `fast_expansion_sum_nonoverlap_shewchuk` (currently Admitted/deferred
   in `B64_FastExpansionSum_Shewchuk.v`).

   Per `docs/shewchuk-theorem-13-proof-structure.md` §6.1-§6.5, Route 2
   adds an auxiliary `cascade_invariant` predicate over the cascade
   input tagged with provenance.  The cascade definition and existing
   correctness lemmas remain untouched.

   SCOPE OF THIS FILE
   ------------------
   This file lands the *framework* with no new Admitteds:
     - `provenance` type (from_e / from_f).
     - `tagged_sort_by_abs`: insertion sort that carries provenance.
     - Length/membership lemmas relating the tagged sort to its inputs.
     - The `cascade_invariant` predicate (stated only; preservation
       deferred to Session 2).

   The headline `fast_expansion_sum_nonoverlap_shewchuk` remains
   Admitted in `B64_FastExpansionSum_Shewchuk.v` until Session 2's
   preservation lemma + Session 3-4's composition land.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
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
From NTS.Proofs.Flocq Require Import B64_FastExpansionSum_Shewchuk.

Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* PROVENANCE TAGS                                                            *)
(*                                                                            *)
(* Each cascade-input element came from either the first input list (e)      *)
(* or the second (f).  The tag is computed from the source decomposition    *)
(* and threads through the sort and cascade for use in the invariant.       *)
(* -------------------------------------------------------------------------- *)

Inductive provenance : Set := from_e | from_f.

Definition provenance_eq_dec (p q : provenance) : {p = q} + {p <> q}.
Proof. decide equality. Defined.

(* -------------------------------------------------------------------------- *)
(* TAGGED INSERTION SORT                                                      *)
(*                                                                            *)
(* Mirrors `insert_by_abs` / `sort_by_abs` from B64_FastExpansionSum_Shewchuk *)
(* but operates on `list (binary64 * provenance)`.  The sort key is the      *)
(* Rabs of the binary64 component; the provenance tag rides along.          *)
(* -------------------------------------------------------------------------- *)

Definition tagged_b64 : Type := binary64 * provenance.

Definition tagged_val (t : tagged_b64) : binary64 := fst t.
Definition tagged_prov (t : tagged_b64) : provenance := snd t.

Fixpoint insert_by_abs_tagged
  (x : tagged_b64) (xs : list tagged_b64)
  : list tagged_b64 :=
  match xs with
  | nil => x :: nil
  | y :: ys =>
      if Rle_dec (Rabs (Binary.B2R prec emax (tagged_val x)))
                 (Rabs (Binary.B2R prec emax (tagged_val y)))
      then x :: y :: ys
      else y :: insert_by_abs_tagged x ys
  end.

Fixpoint sort_by_abs_tagged (xs : list tagged_b64) : list tagged_b64 :=
  match xs with
  | nil => nil
  | x :: xs' => insert_by_abs_tagged x (sort_by_abs_tagged xs')
  end.

(* -------------------------------------------------------------------------- *)
(* Tagging the input expansions.                                              *)
(*                                                                            *)
(* Given two input expansions e and f, construct the tagged-merge by         *)
(* tagging e's elements with from_e and f's with from_f, then concatenating. *)
(* -------------------------------------------------------------------------- *)

Definition tag_list (p : provenance) (xs : list binary64) : list tagged_b64 :=
  map (fun x => (x, p)) xs.

Definition tagged_merge (e f : list binary64) : list tagged_b64 :=
  tag_list from_e e ++ tag_list from_f f.

Definition tagged_input (e f : list binary64) : list tagged_b64 :=
  sort_by_abs_tagged (tagged_merge e f).

(* The untagged projection: erase provenance from a tagged list. *)
Definition untag (xs : list tagged_b64) : list binary64 :=
  map tagged_val xs.

(* -------------------------------------------------------------------------- *)
(* Basic structural lemmas relating the tagged and untagged sort.            *)
(* -------------------------------------------------------------------------- *)

(* length of tagged sort matches its input. *)
Lemma length_insert_by_abs_tagged :
  forall x xs, length (insert_by_abs_tagged x xs) = S (length xs).
Proof.
  intros x xs. revert x.
  induction xs as [|y ys IH]; intros x.
  - reflexivity.
  - cbn.
    destruct (Rle_dec (Rabs (Binary.B2R prec emax (tagged_val x)))
                      (Rabs (Binary.B2R prec emax (tagged_val y)))).
    + reflexivity.
    + cbn. rewrite IH. reflexivity.
Qed.

Lemma length_sort_by_abs_tagged :
  forall xs, length (sort_by_abs_tagged xs) = length xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn. rewrite length_insert_by_abs_tagged.
    rewrite IH. reflexivity.
Qed.

Lemma length_tagged_merge :
  forall e f, length (tagged_merge e f) = (length e + length f)%nat.
Proof.
  intros e f.
  unfold tagged_merge.
  rewrite app_length.
  unfold tag_list.
  rewrite !map_length.
  reflexivity.
Qed.

Lemma length_tagged_input :
  forall e f, length (tagged_input e f) = (length e + length f)%nat.
Proof.
  intros e f. unfold tagged_input.
  rewrite length_sort_by_abs_tagged.
  apply length_tagged_merge.
Qed.

(* untag of insert_by_abs_tagged matches insert_by_abs on the values. *)
Lemma untag_insert_by_abs_tagged :
  forall x xs,
    untag (insert_by_abs_tagged x xs)
      = insert_by_abs (tagged_val x) (untag xs).
Proof.
  intros x xs. revert x.
  induction xs as [|y ys IH]; intros x.
  - reflexivity.
  - cbn.
    destruct (Rle_dec (Rabs (Binary.B2R prec emax (tagged_val x)))
                      (Rabs (Binary.B2R prec emax (tagged_val y)))).
    + reflexivity.
    + cbn. unfold untag in IH. rewrite IH.
      reflexivity.
Qed.

Lemma untag_sort_by_abs_tagged :
  forall xs,
    untag (sort_by_abs_tagged xs) = sort_by_abs (untag xs).
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn. rewrite untag_insert_by_abs_tagged.
    rewrite IH. reflexivity.
Qed.

Lemma untag_tag_list :
  forall p xs, untag (tag_list p xs) = xs.
Proof.
  intros p xs.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

Lemma untag_tagged_merge :
  forall e f, untag (tagged_merge e f) = e ++ f.
Proof.
  intros e f.
  unfold tagged_merge, untag.
  rewrite map_app.
  fold (untag (tag_list from_e e)).
  fold (untag (tag_list from_f f)).
  rewrite !untag_tag_list.
  reflexivity.
Qed.

Theorem untag_tagged_input :
  forall e f, untag (tagged_input e f) = sort_by_abs (e ++ f).
Proof.
  intros e f. unfold tagged_input.
  rewrite untag_sort_by_abs_tagged.
  rewrite untag_tagged_merge.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* THE CASCADE INVARIANT (stated; preservation deferred)                      *)
(*                                                                            *)
(* The invariant tracks the cascade state after processing some prefix of    *)
(* the tagged input.  It has three clauses (per proof structure doc §6.2):  *)
(*                                                                            *)
(*   (a) Output well-formed: the running output (q :: rev hs) is             *)
(*       nonoverlap_shewchuk.  This is the property we ultimately need on    *)
(*       the final state.                                                    *)
(*                                                                            *)
(*   (b) Magnitude bound: the accumulator q has magnitude bounded by the     *)
(*       maximum of the inputs processed so far.  Composes with the         *)
(*       already-Qed-closed b64_TwoSum_step_dominates_* lemmas (§2.1         *)
(*       building blocks).                                                   *)
(*                                                                            *)
(*   (c) Chain-handover: the relationship between q and the next input     *)
(*       (if any) is compatible with the TwoSum step's bounds.  This is     *)
(*       the load-bearing clause whose precise form will be refined in     *)
(*       Session 2 when the preservation proof attempt surfaces what's     *)
(*       actually needed.                                                    *)
(* -------------------------------------------------------------------------- *)

(* The output state: accumulator q and the accumulated h's (smallest-first). *)
Definition cascade_state : Type := binary64 * list binary64.

(* The maximum magnitude of a list of binary64s.  Zero on empty. *)
Fixpoint max_abs_b64 (xs : list binary64) : R :=
  match xs with
  | nil => 0
  | x :: nil => Rabs (Binary.B2R prec emax x)
  | x :: xs' => Rmax (Rabs (Binary.B2R prec emax x)) (max_abs_b64 xs')
  end.

Definition cascade_invariant_output (q : binary64) (hs : list binary64) : Prop :=
  nonoverlap_shewchuk (q :: rev hs).

Definition cascade_invariant_magnitude
  (q : binary64) (processed : list binary64) : Prop :=
  Rabs (Binary.B2R prec emax q) <= max_abs_b64 processed
  \/ processed = nil.

(* Placeholder for clause (c) -- refined in Session 2. *)
Definition cascade_invariant_handover
  (q : binary64) (remaining : list tagged_b64) : Prop :=
  True.

Definition cascade_invariant
  (state : cascade_state)
  (processed : list binary64)
  (remaining : list tagged_b64)
  : Prop :=
  let '(q, hs) := state in
  cascade_invariant_output q hs /\
  cascade_invariant_magnitude q processed /\
  cascade_invariant_handover q remaining.

(* -------------------------------------------------------------------------- *)
(* Sanity check: empty-state invariant.                                       *)
(*                                                                            *)
(* When the cascade hasn't processed any inputs yet, the state is             *)
(* (q_initial, nil) where q_initial is the head of the tagged input.  The   *)
(* invariant holds trivially because:                                       *)
(*   - (a) output is just [q_initial], trivially nonoverlap_shewchuk.        *)
(*   - (b) processed = nil, so the disjunction's right branch fires.        *)
(*   - (c) placeholder True.                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_invariant_empty :
  forall q remaining,
    cascade_invariant (q, nil) nil remaining.
Proof.
  intros q remaining.
  unfold cascade_invariant.
  cbn [rev].
  split; [|split].
  - (* (a) output well-formed *)
    unfold cascade_invariant_output.
    cbn [rev].
    unfold nonoverlap_shewchuk.
    cbn [compress].
    destruct (Rcompare (Binary.B2R prec emax q) 0);
      cbn [nonoverlap_strict]; exact I.
  - (* (b) magnitude *)
    right. reflexivity.
  - (* (c) placeholder *)
    exact I.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions tagged_input.
Print Assumptions untag_tagged_input.
Print Assumptions length_tagged_input.
Print Assumptions cascade_invariant_empty.
