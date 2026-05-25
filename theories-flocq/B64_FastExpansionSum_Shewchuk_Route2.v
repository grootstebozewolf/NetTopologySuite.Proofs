(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_FastExpansionSum_Shewchuk_Route2
   ----------------------------------------------------------------------------
   Slice A Piece 5b -- Route 2 framework + Route 1 cascade_state evolution.

   This file was originally Session 1 of the Route 2 design for closing
   `fast_expansion_sum_nonoverlap_shewchuk` (currently Admitted/deferred
   in `B64_FastExpansionSum_Shewchuk.v`).

   After Session 2's Route 2 collapse
   (`docs/slice-a-piece-5b-session-2-collapse.md`) and the Route 1
   design session
   (`docs/slice-a-piece-5b-route1-design-session.md`), the
   `cascade_state` was upgraded to a Form B record with a `cs_prov`
   field carrying the provenance of the last input absorbed into the
   carry.  The h-chain magnitude argument (the load-bearing content
   the design session attempted to encode in clause (c) of the
   invariant) is intentionally NOT in the invariant: it will land as
   a separate `cascade_h_chain` lemma that consumes
   `cascade_invariant` + `cs_prov` + sort/nonoverlap hypotheses.

   Per `docs/shewchuk-theorem-13-proof-structure.md` §6.1-§6.5, the
   provenance tagging, tagged sort, and structural bridges remain
   intact.  The cascade definition and existing correctness lemmas
   remain untouched.

   SCOPE OF THIS FILE
   ------------------
   This file lands the *framework* with no new Admitteds:
     - `provenance` type (from_e / from_f).
     - `tagged_sort_by_abs`: insertion sort that carries provenance.
     - Length/membership lemmas relating the tagged sort to its inputs.
     - The `cascade_invariant` predicate over the Form B record
       `cascade_state` (preservation + h-chain deferred to the next
       session).

   The headline `fast_expansion_sum_nonoverlap_shewchuk` remains
   Admitted in `B64_FastExpansionSum_Shewchuk.v` until the
   preservation lemma + h-chain + composition land.

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
(*       (if any) is compatible with the TwoSum step's bounds.  Stays a    *)
(*       True placeholder; the actual magnitude/sign analysis lives in a   *)
(*       separate `cascade_h_chain` lemma (see Route 1 design artifact     *)
(*       `docs/slice-a-piece-5b-route1-design-session.md`) that consumes  *)
(*       cascade_invariant + cs_prov + sort/nonoverlap hypotheses.  This   *)
(*       split is the load-bearing recommendation from the design          *)
(*       session: the h-chain is NOT statable as an invariant clause      *)
(*       because the required information does not propagate as a clean   *)
(*       state predicate.                                                   *)
(* -------------------------------------------------------------------------- *)

(* The cascade state.  Form B (record) is chosen over the lighter tuple     *)
(* form because the inductive proof of cascade_step_preserves_invariant    *)
(* will case-split on cs_prov repeatedly; named accessors prevent          *)
(* positional-pattern-match bugs across the four provenance combinations.  *)
(*                                                                          *)
(* cs_carry  : the running accumulator (`q` in the cascade).               *)
(* cs_prov   : provenance of the LAST input absorbed into cs_carry.        *)
(*             For the initial state, this is the provenance of the head   *)
(*             of the tagged input.                                         *)
(* cs_output : the accumulated h's (smallest-first, as produced by the     *)
(*             cascade -- reversed at the end to put largest-first for     *)
(*             nonoverlap_strict).                                          *)
Record cascade_state : Type := mk_cascade_state {
  cs_carry  : binary64;
  cs_prov   : provenance;
  cs_output : list binary64
}.

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

(* Refined clause (c) -- Route 1 Session 2.                                 *)
(*                                                                          *)
(* Encodes: the next TwoSum step is in coverage of one of the existing      *)
(* b64_TwoSum_step_dominates_xxx lemmas.  Five-arm disjunction over the     *)
(* preconditions:                                                           *)
(*   - same-sign positive (pos)                                             *)
(*   - same-sign negative (neg)                                             *)
(*   - zero carry (q_zero)                                                  *)
(*   - any-sign with strict magnitude bound on |q| for positive x           *)
(*     (strict_pos)                                                         *)
(*   - any-sign with strict magnitude bound on |q| for negative x           *)
(*     (strict_neg)                                                         *)
(* Plus a `b64_TwoSum_safe` conjunct so the lemmas can fire.                *)
(*                                                                          *)
(* This is the strongest clause (c) form provable from the                  *)
(* dominates_* family alone.  Per the Route 1 design artifact               *)
(* (docs/slice-a-piece-5b-route1-design-session.md §Task 3), this           *)
(* disjunction covers all SAME-SIGN inputs and all STRICT-MAGNITUDE         *)
(* cases; it is the right starting point for the inductive case             *)
(* analysis.                                                                *)
Definition cascade_invariant_handover
  (state : cascade_state) (remaining : list tagged_b64) : Prop :=
  match remaining with
  | nil => True
  | (x, _) :: _ =>
      let q  := cs_carry state in
      let qR := Binary.B2R prec emax q in
      let xR := Binary.B2R prec emax x in
      b64_TwoSum_safe x q /\
      ( (0 < qR /\ 0 < xR)
        \/ (qR < 0 /\ xR < 0)
        \/ qR = 0
        \/ (0 < xR /\ Rabs qR <
              ulp radix2 (SpecFloat.fexp prec emax)
                (pred radix2 (SpecFloat.fexp prec emax) xR) / 2)
        \/ (xR < 0 /\ Rabs qR <
              ulp radix2 (SpecFloat.fexp prec emax)
                (succ radix2 (SpecFloat.fexp prec emax) xR) / 2) )
  end.

Definition cascade_invariant
  (state : cascade_state)
  (processed : list binary64)
  (remaining : list tagged_b64)
  : Prop :=
  cascade_invariant_output (cs_carry state) (cs_output state) /\
  cascade_invariant_magnitude (cs_carry state) processed /\
  cascade_invariant_handover state remaining.

(* -------------------------------------------------------------------------- *)
(* Sanity check: empty-state invariant under refined clause (c).              *)
(*                                                                            *)
(* When the cascade hasn't processed any inputs yet, the state is             *)
(* mk_cascade_state q_initial p_initial nil where (q_initial, p_initial) is  *)
(* the head of the tagged input.  Clauses (a) and (b) hold trivially:         *)
(*   - (a) output is just [q_initial], trivially nonoverlap_shewchuk.         *)
(*   - (b) processed = nil, so the disjunction's right branch fires.         *)
(* Clause (c) is no longer vacuous; it is taken as a hypothesis.  The         *)
(* bootstrap lemma `fast_expansion_sum_bootstrap` discharges this             *)
(* hypothesis from the input preconditions (sorted-ascending merge +          *)
(* per-source nonoverlap_shewchuk).                                           *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_invariant_empty :
  forall q p remaining,
    cascade_invariant_handover (mk_cascade_state q p nil) remaining ->
    cascade_invariant (mk_cascade_state q p nil) nil remaining.
Proof.
  intros q p remaining Hho.
  unfold cascade_invariant.
  cbn [cs_carry cs_prov cs_output rev].
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
  - (* (c) handover -- supplied as hypothesis. *)
    exact Hho.
Qed.

(* -------------------------------------------------------------------------- *)
(* GREEN-PHASE ATTEMPT: cascade_step_preserves_invariant.                     *)
(*                                                                            *)
(* Per docs/shewchuk-theorem-13-proof-structure.md §6.3, after one cascade   *)
(* step consuming (x, prov_x) from the head of remaining:                     *)
(*   - cs_carry := fst (b64_TwoSum x q_old)                                   *)
(*   - cs_prov  := prov_x                                                     *)
(*   - cs_output := cs_output_old ++ [snd (b64_TwoSum x q_old)]               *)
(*     (APPEND to oldest-first convention so cascade_invariant_output's       *)
(*     `q :: rev hs` shape is preserved.)                                     *)
(*                                                                            *)
(* Clause (a) preservation requires nonoverlap_shewchuk on                    *)
(* (qnew :: rev (hs ++ [h])) = (qnew :: h :: rev hs).                         *)
(* That decomposes into:                                                      *)
(*   (1) strict_succ qnew h        -- TwoSum's |h| <= ulp(qnew)/2 property    *)
(*   (2) strict_succ h h_prev      -- THE H-CHAIN, between consecutive errs   *)
(*   (3) rest of the chain         -- inherited from old clause (a)           *)
(*                                                                            *)
(* (2) is the load-bearing claim per the Route 1 design artifact.  It is     *)
(* not in the refined clause (c) (which is about q's relationship to the     *)
(* NEXT x), nor in clause (b) (max-abs bound), nor derivable from the        *)
(* existing dominates_* family alone.                                         *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_step_preserves_invariant :
  forall (state : cascade_state)
         (processed : list binary64)
         (x : binary64) (prov : provenance)
         (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    cascade_invariant
      (mk_cascade_state
         (fst (b64_TwoSum x (cs_carry state)))
         prov
         (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]))
      (processed ++ [x])
      rest.
Proof.
  intros state processed x prov rest Hinv.
  unfold cascade_invariant in Hinv.
  destruct Hinv as [Ha [Hb Hc]].
  unfold cascade_invariant_handover in Hc.
  cbn [cs_carry] in Hc.
  destruct Hc as [Hsafe Hcases].
  unfold cascade_invariant.
  cbn [cs_carry cs_prov cs_output].
  split; [|split].
  - (* (a) Output well-formed.                                                 *)
    (*                                                                          *)
    (* GOAL: nonoverlap_shewchuk                                                *)
    (*         (fst (b64_TwoSum x (cs_carry state))                             *)
    (*          :: rev (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]))*)
    (*       = nonoverlap_shewchuk                                              *)
    (*         (qnew :: h :: rev (cs_output state))                             *)
    (*                                                                          *)
    (* by rev_app_distr and rev (cons h nil) = [h].                             *)
    (*                                                                          *)
    (* The hypothesis Ha gives us:                                              *)
    (*   nonoverlap_shewchuk (cs_carry state :: rev (cs_output state))         *)
    (* i.e., (q_old :: rev hs_old).                                             *)
    (*                                                                          *)
    (* We need to establish a chain:                                            *)
    (*   strict_succ_b64 qnew h        (after compress)                         *)
    (*   strict_succ_b64 h h_prev      (where h_prev is head of rev hs_old)    *)
    (*   ... rest of chain from Ha                                              *)
    (*                                                                          *)
    (* The second link, `strict_succ_b64 h h_prev`, is the H-CHAIN claim       *)
    (* that the Route 1 design artifact and Route 2 collapse artifact          *)
    (* identified as Shewchuk Theorem 13's load-bearing content.  It is        *)
    (* NOT in the refined clause (c); clause (c) is about q's relationship    *)
    (* to the NEXT input x, not about h_prev's relationship to the new h.     *)
    (*                                                                          *)
    (* COLLAPSE: this subgoal cannot be discharged from Ha + Hb + Hcases       *)
    (* + the input preconditions alone.  See                                    *)
    (* docs/slice-a-piece-5b-route1-session-2-collapse.md.                      *)
Abort.

(* -------------------------------------------------------------------------- *)
(* MISSING PROPERTY -- the h-chain link between consecutive cascade errors.   *)
(*                                                                            *)
(* Stated here as a Prop type so the corpus type-checks the obligation that  *)
(* the Route 1 Session 2 collapse identified.  NOT proved -- a successor     *)
(* session targets this lemma as a SEPARATE cascade-step result, not as an  *)
(* invariant clause.                                                          *)
(*                                                                            *)
(* Reads:                                                                     *)
(*                                                                            *)
(*   Given the invariant before a step (state + processed + remaining =     *)
(*   (x, prov_x) :: rest), assume cs_output has at least one element with   *)
(*   h_prev at its tail (the most recently produced cascade error, before  *)
(*   reversal).  Assume the cascade input is the sorted-by-magnitude merge *)
(*   of two per-source-nonoverlap_shewchuk expansions e and f.  Then the   *)
(*   new error h := snd (b64_TwoSum x (cs_carry state)) dominates h_prev   *)
(*   in the half-ulp sense.                                                 *)
(*                                                                            *)
(* This is Shewchuk Theorem 13's load-bearing magnitude claim, restated in   *)
(* cascade form.  Estimated 200-400 lines of Coq; requires deep magnitude   *)
(* case analysis on provenance + sign + binade position.                     *)
(* -------------------------------------------------------------------------- *)

Definition cascade_h_chain_statement : Prop :=
  forall (state : cascade_state)
         (processed : list binary64)
         (x : binary64) (prov_x : provenance)
         (rest : list tagged_b64)
         (h_prev : binary64) (hs_tail : list binary64)
         (e f : list binary64),
    cascade_invariant state processed ((x, prov_x) :: rest) ->
    cs_output state = hs_tail ++ [h_prev] ->
    nonoverlap_shewchuk e ->
    nonoverlap_shewchuk f ->
    sorted_asc (untag (tagged_input e f)) ->
    Rabs (Binary.B2R prec emax h_prev) <=
      ulp radix2 (SpecFloat.fexp prec emax)
        (Binary.B2R prec emax
           (snd (b64_TwoSum x (cs_carry state)))) / 2.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions tagged_input.
Print Assumptions untag_tagged_input.
Print Assumptions length_tagged_input.
Print Assumptions cascade_invariant_empty.
Print Assumptions cascade_h_chain_statement.
