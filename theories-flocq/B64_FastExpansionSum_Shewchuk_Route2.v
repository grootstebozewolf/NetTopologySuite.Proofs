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
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
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
(* Per-source maxes -- Route 1 Session 5 refinement of the Session 4         *)
(* single-cs_run_max formulation.                                             *)
(*                                                                            *)
(* cs_e_max : largest-by-magnitude element from `e` absorbed so far.          *)
(* cs_f_max : largest-by-magnitude element from `f` absorbed so far.          *)
(*                                                                            *)
(* Either field is `b64_zero` (sign-agnostic +0) when no element from that   *)
(* source has yet been absorbed.  Per-source nonoverlap_shewchuk on e and f *)
(* gives the within-source half-ulp gap that the preservation proof uses.    *)
Record cascade_state : Type := mk_cascade_state {
  cs_carry   : binary64;
  cs_prov    : provenance;
  cs_output  : list binary64;
  cs_e_max   : binary64;
  cs_f_max   : binary64
}.

(* Canonical zero element for cascade-state initialisation.  B2R = 0, sign *)
(* +0.  Used when one source has had no absorptions yet.                    *)
Definition b64_zero : binary64 :=
  Binary.B754_zero prec emax false.

Lemma B2R_b64_zero : Binary.B2R prec emax b64_zero = 0.
Proof. reflexivity. Qed.

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

(* Clause (d) -- Route 1 Session 5 per-source run-bound conjunct.            *)
(*                                                                            *)
(* The carry's magnitude is bounded by the sum (with constant 2) of the      *)
(* per-source maxes.  Each source individually satisfies                     *)
(* nonoverlap_shewchuk, so each source's accumulated contribution to the    *)
(* carry is bounded by 2 * (largest absorbed in that source) via the         *)
(* half-ulp geometric sum.  The two contributions add, giving the bound     *)
(* below.                                                                     *)
(*                                                                            *)
(* This is the Session 4 outcome's refined clause (d').  Session 4 verified *)
(* on paper that this preserves under both continue-run and cross-prov       *)
(* cascade steps via per-source nonoverlap_shewchuk.  Session 5 formalises  *)
(* the preservation in Coq.                                                  *)
Definition cascade_invariant_run_bound (state : cascade_state) : Prop :=
  Rabs (Binary.B2R prec emax (cs_carry state))
    <= 2 * Rabs (Binary.B2R prec emax (cs_e_max state))
       + 2 * Rabs (Binary.B2R prec emax (cs_f_max state)).

Definition cascade_invariant
  (state : cascade_state)
  (processed : list binary64)
  (remaining : list tagged_b64)
  : Prop :=
  cascade_invariant_output (cs_carry state) (cs_output state) /\
  cascade_invariant_magnitude (cs_carry state) processed /\
  cascade_invariant_handover state remaining /\
  cascade_invariant_run_bound state.

(* -------------------------------------------------------------------------- *)
(* Initial cascade state -- helper for the bootstrap.                         *)
(*                                                                            *)
(* The first absorbed element x_0 has provenance p_0.  The "active" max     *)
(* (matching p_0) is set to x_0; the other source's max is b64_zero (no    *)
(* absorption yet).  Clause (d) then becomes:                                *)
(*                                                                            *)
(*   |x_0| <= 2|x_0| + 2*|b64_zero| = 2|x_0|.                                *)
(*                                                                            *)
(* which holds trivially.                                                     *)
(* -------------------------------------------------------------------------- *)

Definition initial_cascade_state
  (q : binary64) (p : provenance) : cascade_state :=
  match p with
  | from_e => mk_cascade_state q p nil q       b64_zero
  | from_f => mk_cascade_state q p nil b64_zero q
  end.

(* -------------------------------------------------------------------------- *)
(* Sanity check: empty-state invariant under refined clauses (c) and (d).     *)
(*                                                                            *)
(* Clauses (a), (b), (d) hold trivially:                                      *)
(*   - (a) output is just [q], trivially nonoverlap_shewchuk.                 *)
(*   - (b) processed = nil, so the disjunction's right branch fires.          *)
(*   - (d) per-source bound: |q| <= 2|q| + 0 (one source's max is q, the   *)
(*     other is b64_zero with |B2R| = 0).                                    *)
(* Clause (c) is taken as a hypothesis; the bootstrap discharges it from     *)
(* input preconditions.                                                       *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_invariant_empty :
  forall q p remaining,
    cascade_invariant_handover (initial_cascade_state q p) remaining ->
    cascade_invariant (initial_cascade_state q p) nil remaining.
Proof.
  intros q p remaining Hho.
  unfold cascade_invariant, initial_cascade_state.
  destruct p; cbn [cs_carry cs_prov cs_output cs_e_max cs_f_max rev];
    (split; [|split; [|split]]).
  - (* (a) output well-formed -- from_e branch. *)
    unfold cascade_invariant_output.
    cbn [cs_carry cs_output rev].
    unfold nonoverlap_shewchuk.
    cbn [compress].
    destruct (Rcompare (Binary.B2R prec emax q) 0);
      cbn [nonoverlap_strict]; exact I.
  - (* (b) magnitude -- from_e *)
    right. reflexivity.
  - (* (c) handover -- from_e *)
    exact Hho.
  - (* (d) run-bound -- from_e: |q| <= 2|q| + 2*|b64_zero| = 2|q|. *)
    unfold cascade_invariant_run_bound.
    cbn [cs_carry cs_e_max cs_f_max].
    rewrite B2R_b64_zero, Rabs_R0.
    pose proof (Rabs_pos (Binary.B2R prec emax q)) as Hpos.
    lra.
  - (* (a) -- from_f branch. *)
    unfold cascade_invariant_output.
    cbn [cs_carry cs_output rev].
    unfold nonoverlap_shewchuk.
    cbn [compress].
    destruct (Rcompare (Binary.B2R prec emax q) 0);
      cbn [nonoverlap_strict]; exact I.
  - (* (b) -- from_f *)
    right. reflexivity.
  - (* (c) -- from_f *)
    exact Hho.
  - (* (d) -- from_f: |q| <= 2*|b64_zero| + 2|q| = 2|q|. *)
    unfold cascade_invariant_run_bound.
    cbn [cs_carry cs_e_max cs_f_max].
    rewrite B2R_b64_zero, Rabs_R0.
    pose proof (Rabs_pos (Binary.B2R prec emax q)) as Hpos.
    lra.
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

(* The cascade step's effect on cs_e_max / cs_f_max.                          *)
(*                                                                            *)
(* After absorbing (x, prov), the active source's max updates to x (sorted   *)
(* ascending guarantees x is the new largest in its source absorbed so far);  *)
(* the other source's max stays unchanged.                                    *)
Definition cascade_step_state
  (state : cascade_state) (x : binary64) (prov : provenance)
  : cascade_state :=
  match prov with
  | from_e =>
      mk_cascade_state
        (fst (b64_TwoSum x (cs_carry state)))
        prov
        (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))])
        x
        (cs_f_max state)
  | from_f =>
      mk_cascade_state
        (fst (b64_TwoSum x (cs_carry state)))
        prov
        (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))])
        (cs_e_max state)
        x
  end.

Lemma cascade_step_preserves_invariant :
  forall (state : cascade_state)
         (processed : list binary64)
         (x : binary64) (prov : provenance)
         (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    cascade_invariant
      (cascade_step_state state x prov)
      (processed ++ [x])
      rest.
Proof.
  (* Composition of clause (a-d) preservation lemmas (Deliverable 2 below). *)
  (* Aborted at this top level until all four sub-preservation lemmas are  *)
  (* Qed-closed; the clause (d) preservation is the Session 5 deliverable. *)
  (* Reason: clause (a)'s h-chain link still needs cascade_h_chain (the    *)
  (* lemma whose statement lives in cascade_h_chain_statement below).      *)
Abort.

(* -------------------------------------------------------------------------- *)
(* AUXILIARY -- absolute-error bound on b64_plus.                             *)
(*                                                                            *)
(* The cornerstone of the clause (d') preservation: after b64_plus,           *)
(* the result is within a half-ulp of the exact sum, so its magnitude is     *)
(* bounded by the triangle-sum plus a half-ulp slack.                         *)
(* -------------------------------------------------------------------------- *)

Lemma b64_plus_abs_bound :
  forall x y : binary64,
    b64_safe Rplus x y ->
    Rabs (Binary.B2R prec emax (b64_plus x y)) <=
      Rabs (Binary.B2R prec emax x)
      + Rabs (Binary.B2R prec emax y)
      + b64_ulp (Binary.B2R prec emax (b64_plus x y)) / 2.
Proof.
  intros x y Hsafe.
  pose proof (b64_plus_correct x y Hsafe) as [HB2R _].
  pose proof (b64_error_le_half_ulp_round
                (Binary.B2R prec emax x + Binary.B2R prec emax y)) as Herr.
  rewrite <- HB2R in Herr.
  pose proof (Rabs_triang_inv
                (Binary.B2R prec emax (b64_plus x y))
                (Binary.B2R prec emax x + Binary.B2R prec emax y)) as Htri.
  pose proof (Rabs_triang (Binary.B2R prec emax x) (Binary.B2R prec emax y))
    as Hsum.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* eps_b64 -- the binary64 round-off relative error bound.                    *)
(*                                                                            *)
(* For normal-range binary64, `ulp(x) <= |x| * eps_b64` (via                  *)
(* `ulp_FLT_le_eps_b64` below).  Numerically `eps_b64 = 2^-52`.               *)
(* -------------------------------------------------------------------------- *)

Definition eps_b64 : R := / IZR (Z.pow_pos 2 52).

Lemma eps_b64_pos : 0 < eps_b64.
Proof. unfold eps_b64. apply Rinv_0_lt_compat. apply IZR_lt. lia. Qed.

Lemma eps_b64_le_quarter : eps_b64 <= / 4.
Proof.
  unfold eps_b64. apply Rinv_le_contravar; [lra|].
  assert (4 <= IZR (Z.pow_pos 2 52)) by (apply IZR_le; lia).
  lra.
Qed.

Lemma eps_b64_eq_bpow : eps_b64 = bpow radix2 (1 - prec).
Proof. unfold eps_b64. reflexivity. Qed.

(* Tight ulp bound for normal-range binary64: ulp(x) <= |x| * eps_b64. *)
Lemma ulp_FLT_le_eps_b64 :
  forall x : R,
    bpow radix2 (b64_emin + prec - 1) <= Rabs x ->
    b64_ulp x <= Rabs x * eps_b64.
Proof.
  intros x Hnorm.
  rewrite eps_b64_eq_bpow.
  apply (ulp_FLT_le radix2 b64_emin prec).
  exact Hnorm.
Qed.

(* The clause-(d') preservation workhorse.  Combines b64_plus_abs_bound      *)
(* with the normal-range ulp bound on the result, giving a clean form that  *)
(* feeds nra/lra without nonlinear-witness hunting.                          *)
Lemma b64_plus_abs_bound_with_normal :
  forall x y : binary64,
    b64_safe Rplus x y ->
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax (b64_plus x y)) ->
    Rabs (Binary.B2R prec emax (b64_plus x y))
      * (1 - eps_b64 / 2)
      <= Rabs (Binary.B2R prec emax x)
         + Rabs (Binary.B2R prec emax y).
Proof.
  intros x y Hsafe Hpn.
  pose proof (b64_plus_abs_bound x y Hsafe) as Hbnd.
  pose proof (ulp_FLT_le_eps_b64 _ Hpn) as Hulp.
  (* Hbnd: |b64_plus x y| <= |x| + |y| + ulp(b64_plus x y) / 2
     Hulp: ulp(b64_plus x y) <= |b64_plus x y| * eps_b64
     So:   ulp(b64_plus x y) / 2 <= |b64_plus x y| * eps_b64 / 2
     Hbnd: |b64_plus x y| <= |x| + |y| + |b64_plus x y| * eps_b64 / 2
     =>    |b64_plus x y| * (1 - eps_b64/2) <= |x| + |y|. *)
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* DELIVERABLE 2 -- clause (d') preservation lemmas.                          *)
(*                                                                            *)
(* Two cases (not four), parameterised by the new step's provenance.          *)
(* The within-run vs cross-prov distinction collapses to the SAME proof       *)
(* because the within-source hypothesis (|cs_X_max| <= ulp(x)/2) holds        *)
(* whenever the new x is from source X, regardless of what was last           *)
(* absorbed: by sort_by_abs_sorted, OLD cs_X_max and new x are consecutive   *)
(* in X (any intervening sorted-merge elements come from the OTHER source).  *)
(*                                                                            *)
(* This is a nicer structural property than the prompt anticipated.          *)
(* -------------------------------------------------------------------------- *)

(* Absorb an e-element: clause (d') preservation when new prov = from_e.    *)
(* Uses |cs_e_max| <= ulp(x)/2 (within-e nonoverlap) and |cs_f_max| <= |x|   *)
(* (sorted-ascending).                                                       *)
Lemma run_bound_absorb_e :
  forall (state : cascade_state) (x : binary64),
    cascade_invariant_run_bound state ->
    (* Within-source structure on cs_e_max. *)
    Rabs (Binary.B2R prec emax (cs_e_max state)) <=
      b64_ulp (Binary.B2R prec emax x) / 2 ->
    b64_safe Rplus x (cs_carry state) ->
    (* Normal range on x. *)
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax x) ->
    (* Normal range on b64_plus result. *)
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax
              (b64_plus x (cs_carry state))) ->
    (* Sorted: |cs_f_max| <= |x|. *)
    Rabs (Binary.B2R prec emax (cs_f_max state)) <=
      Rabs (Binary.B2R prec emax x) ->
    cascade_invariant_run_bound
      (cascade_step_state state x from_e).
Proof.
  intros state x Hd Hgap Hsafe Hxn Hpn Hfsort.
  unfold cascade_invariant_run_bound in *.
  unfold cascade_step_state.
  cbn [cs_carry cs_e_max cs_f_max].
  pose proof (b64_plus_abs_bound_with_normal x (cs_carry state) Hsafe Hpn) as Hbnd.
  pose proof (ulp_FLT_le_eps_b64 _ Hxn) as Hux.
  pose proof eps_b64_pos as Heps_pos.
  pose proof eps_b64_le_quarter as Heps_small.
  pose proof (Rabs_pos (Binary.B2R prec emax (cs_e_max state))) as HE_pos.
  pose proof (Rabs_pos (Binary.B2R prec emax (cs_f_max state))) as HF_pos.
  pose proof (Rabs_pos (Binary.B2R prec emax (cs_carry state))) as HQ_pos.
  pose proof (Rabs_pos (Binary.B2R prec emax x)) as HX_pos.
  pose proof (Rabs_pos
                (Binary.B2R prec emax (b64_plus x (cs_carry state)))) as HA_pos.
  pose proof (ulp_ge_0 radix2 b64_fexp (Binary.B2R prec emax x)) as HUX_pos.
  (* Stage the chain.  Let:                                                   *)
  (*   E := |cs_e_max|, F := |cs_f_max|, Q := |cs_carry|, X := |x|            *)
  (*   A := |b64_plus x cs_carry|, UX := ulp x, eps := eps_b64.               *)
  (* Hd:    Q <= 2*E + 2*F.                                                   *)
  (* Hgap:  E <= UX / 2.                                                      *)
  (* Hbnd:  A * (1 - eps/2) <= X + Q.                                         *)
  (* Hux:   UX <= X * eps.                                                    *)
  (* Hfsort: F <= X.                                                          *)
  set (E := Rabs (Binary.B2R prec emax (cs_e_max state))) in *.
  set (F := Rabs (Binary.B2R prec emax (cs_f_max state))) in *.
  set (Q := Rabs (Binary.B2R prec emax (cs_carry state))) in *.
  set (X := Rabs (Binary.B2R prec emax x)) in *.
  set (A := Rabs (Binary.B2R prec emax
                    (b64_plus x (cs_carry state)))) in *.
  set (UX := b64_ulp (Binary.B2R prec emax x)) in *.
  set (eps := eps_b64) in *.
  (* Step 1: Q <= UX + 2*F. *)
  assert (HQ_UX : Q <= UX + 2 * F) by lra.
  (* Step 2: Q <= X*eps + 2*F. *)
  assert (HQ_X : Q <= X * eps + 2 * F) by nra.
  (* Step 3: A * (1 - eps/2) <= X + X*eps + 2*F. *)
  assert (HA_1 : A * (1 - eps / 2) <= X + X * eps + 2 * F) by lra.
  (* Step 4: (2*X + 2*F) * (1 - eps/2) >= X + X*eps + 2*F.                    *)
  (* Equivalent: 2*X - X*eps + 2*F - F*eps >= X + X*eps + 2*F                 *)
  (* i.e., X*(1 - 2*eps) >= F*eps, which holds since F <= X and 3*eps <= 1.   *)
  assert (Hgoal_aux : X * (1 - 2 * eps) >= F * eps) by nra.
  assert (Htarget_expand :
    (2 * X + 2 * F) * (1 - eps / 2) >= X + X * eps + 2 * F) by nra.
  (* Step 5: Combine HA_1 + Htarget_expand to get A <= 2*X + 2*F.             *)
  assert (Hpos_factor : 0 < 1 - eps / 2) by lra.
  assert (Hmul_compare : A * (1 - eps / 2) <= (2 * X + 2 * F) * (1 - eps / 2))
    by lra.
  (* Cancel the positive factor (1 - eps/2). *)
  apply (Rmult_le_reg_r (1 - eps / 2) A (2 * X + 2 * F)
            Hpos_factor Hmul_compare).
Qed.

(* Absorb an f-element: symmetric to run_bound_absorb_e.  Uses                *)
(* |cs_f_max| <= ulp(x)/2 (within-f nonoverlap) and |cs_e_max| <= |x|         *)
(* (sorted-ascending).                                                       *)
Lemma run_bound_absorb_f :
  forall (state : cascade_state) (x : binary64),
    cascade_invariant_run_bound state ->
    Rabs (Binary.B2R prec emax (cs_f_max state)) <=
      b64_ulp (Binary.B2R prec emax x) / 2 ->
    b64_safe Rplus x (cs_carry state) ->
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax x) ->
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax
              (b64_plus x (cs_carry state))) ->
    Rabs (Binary.B2R prec emax (cs_e_max state)) <=
      Rabs (Binary.B2R prec emax x) ->
    cascade_invariant_run_bound
      (cascade_step_state state x from_f).
Proof.
  intros state x Hd Hgap Hsafe Hxn Hpn Hesort.
  unfold cascade_invariant_run_bound in *.
  unfold cascade_step_state.
  cbn [cs_carry cs_e_max cs_f_max].
  pose proof (b64_plus_abs_bound_with_normal x (cs_carry state) Hsafe Hpn) as Hbnd.
  pose proof (ulp_FLT_le_eps_b64 _ Hxn) as Hux.
  pose proof eps_b64_pos as Heps_pos.
  pose proof eps_b64_le_quarter as Heps_small.
  pose proof (Rabs_pos (Binary.B2R prec emax (cs_e_max state))) as HE_pos.
  pose proof (Rabs_pos (Binary.B2R prec emax (cs_f_max state))) as HF_pos.
  pose proof (Rabs_pos (Binary.B2R prec emax (cs_carry state))) as HQ_pos.
  pose proof (Rabs_pos (Binary.B2R prec emax x)) as HX_pos.
  pose proof (Rabs_pos
                (Binary.B2R prec emax (b64_plus x (cs_carry state)))) as HA_pos.
  pose proof (ulp_ge_0 radix2 b64_fexp (Binary.B2R prec emax x)) as HUX_pos.
  (* Symmetric to run_bound_absorb_e: |cs_f_max| <= ulp(x)/2 plays the role  *)
  (* of |cs_e_max| <= ulp(x)/2, with E and F swapped in the chain.           *)
  set (E := Rabs (Binary.B2R prec emax (cs_e_max state))) in *.
  set (F := Rabs (Binary.B2R prec emax (cs_f_max state))) in *.
  set (Q := Rabs (Binary.B2R prec emax (cs_carry state))) in *.
  set (X := Rabs (Binary.B2R prec emax x)) in *.
  set (A := Rabs (Binary.B2R prec emax
                    (b64_plus x (cs_carry state)))) in *.
  set (UX := b64_ulp (Binary.B2R prec emax x)) in *.
  set (eps := eps_b64) in *.
  assert (HQ_UX : Q <= 2 * E + UX) by lra.
  assert (HQ_X : Q <= 2 * E + X * eps) by nra.
  assert (HA_1 : A * (1 - eps / 2) <= X + 2 * E + X * eps) by lra.
  assert (Hgoal_aux : X * (1 - 2 * eps) >= E * eps) by nra.
  assert (Htarget_expand :
    (2 * E + 2 * X) * (1 - eps / 2) >= X + 2 * E + X * eps) by nra.
  assert (Hpos_factor : 0 < 1 - eps / 2) by lra.
  assert (Hmul_compare : A * (1 - eps / 2) <= (2 * E + 2 * X) * (1 - eps / 2))
    by lra.
  apply (Rmult_le_reg_r (1 - eps / 2) A (2 * E + 2 * X)
            Hpos_factor Hmul_compare).
Qed.

(* Composition: clause (d') preservation under any cascade step.              *)
(*                                                                            *)
(* Given a state satisfying clause (d') and a step (x, prov) with the         *)
(* appropriate within-source hypothesis on x's source max plus the sorted    *)
(* hypothesis on the other source's max, plus the normal-range and safety    *)
(* hypotheses, clause (d') is preserved.                                      *)
Lemma run_bound_step_preserves :
  forall (state : cascade_state) (x : binary64) (prov : provenance),
    cascade_invariant_run_bound state ->
    b64_safe Rplus x (cs_carry state) ->
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax x) ->
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax
              (b64_plus x (cs_carry state))) ->
    (* The within-source gap is on the active source's max. *)
    match prov with
    | from_e =>
        Rabs (Binary.B2R prec emax (cs_e_max state)) <=
          b64_ulp (Binary.B2R prec emax x) / 2
        /\ Rabs (Binary.B2R prec emax (cs_f_max state)) <=
             Rabs (Binary.B2R prec emax x)
    | from_f =>
        Rabs (Binary.B2R prec emax (cs_f_max state)) <=
          b64_ulp (Binary.B2R prec emax x) / 2
        /\ Rabs (Binary.B2R prec emax (cs_e_max state)) <=
             Rabs (Binary.B2R prec emax x)
    end ->
    cascade_invariant_run_bound (cascade_step_state state x prov).
Proof.
  intros state x prov Hd Hsafe Hxn Hpn Hprov.
  destruct prov as [|]; destruct Hprov as [Hgap Hsort].
  - apply run_bound_absorb_e; assumption.
  - apply run_bound_absorb_f; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* DELIVERABLE 3 -- the h-chain link.                                         *)
(*                                                                            *)
(* Under Path A's strict precondition `|q| < ulp(pred x) / 2` (positive x),  *)
(* `b64_TwoSum_pathA_exact_step` (Qed-closed in B64_FastExpansionSum.v) gives *)
(* `B2R(snd(b64_TwoSum x q)) = B2R q` exactly: the rounding error is the     *)
(* small operand itself.  This means `ulp(snd) = ulp(q)`, so a bound          *)
(* `|h_prev| <= ulp(q)/2` lifts directly to the h-chain link                   *)
(* `|h_prev| <= ulp(snd)/2` -- which is the load-bearing claim of             *)
(* cascade_h_chain_statement, restricted to positive within-source            *)
(* continuation.                                                              *)
(*                                                                            *)
(* This closes the Route 1 series for the typical Stage D path.  The         *)
(* negative-x analog needs a symmetric `pathA_exact_step_negative` lemma     *)
(* (not currently in the corpus); the zero-x edge case is the round-to-even *)
(* boundary tangent the prompt warned about.                                  *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_h_chain_pathA_pos :
  forall (x q h_prev : binary64),
    0 < Binary.B2R prec emax x ->
    strict_succ_pathA_R (Binary.B2R prec emax x)
                        (Binary.B2R prec emax q) ->
    Rabs (Binary.B2R prec emax h_prev)
      <= b64_ulp (Binary.B2R prec emax q) / 2 ->
    b64_TwoSum_safe x q ->
    Rabs (Binary.B2R prec emax h_prev)
      <= b64_ulp (Binary.B2R prec emax (snd (b64_TwoSum x q))) / 2.
Proof.
  intros x q h_prev Hx Hpw Hhprev Hsafe.
  pose proof (b64_TwoSum_pathA_exact_step x q Hx Hpw Hsafe) as [_ Hsnd_eq].
  rewrite Hsnd_eq.
  exact Hhprev.
Qed.

(* Negative-x analog: symmetric structure via round_eq_pathA_negative.       *)
(* Mechanical to derive once b64_TwoSum_pathA_exact_step_negative is added  *)
(* to B64_FastExpansionSum.v (a Session 8 task; the structure mirrors the  *)
(* positive case via Ropp).                                                  *)

(* -------------------------------------------------------------------------- *)
(* SESSION 6 OUTCOME: clause (d') preservation lemmas Qed-closed above.       *)
(*                                                                            *)
(* Three Qed-closed lemmas:                                                   *)
(*   - run_bound_absorb_e   (covers continue-run from_e + cross-prov to e)    *)
(*   - run_bound_absorb_f   (covers continue-run from_f + cross-prov to f)    *)
(*   - run_bound_step_preserves (compositional case split on prov)            *)
(*                                                                            *)
(* The four-case decomposition collapsed to two by observing that the         *)
(* within-source nonoverlap hypothesis on cs_X_max is the SAME in both       *)
(* "continue run" and "cross-prov" cases (since sort_by_abs places           *)
(* same-source elements consecutively in their source even when interleaved  *)
(* with the other source in the merge).                                       *)
(* -------------------------------------------------------------------------- *)

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
(* PRECONDITION TEST: what does the existing invariant actually provide       *)
(* about `h_prev`?                                                            *)
(*                                                                            *)
(* From `cascade_invariant state ... ` with `cs_output state = hs_tail ++    *)
(* [h_prev]` we can decompose clause (a):                                     *)
(*                                                                            *)
(*   nonoverlap_shewchuk (cs_carry state :: rev (cs_output state))            *)
(* = nonoverlap_shewchuk (cs_carry state :: h_prev :: rev hs_tail)            *)
(*                                                                            *)
(* When neither cs_carry state nor h_prev is zero (so `compress` does not    *)
(* remove them), the head of the half-ulp chain gives:                       *)
(*                                                                            *)
(*   strict_succ_b64 (cs_carry state) h_prev                                  *)
(*   = |h_prev| <= ulp(cs_carry state) / 2.                                   *)
(*                                                                            *)
(* That bound is Qed-closed below.                                            *)
(*                                                                            *)
(* THE GAP.  `cascade_h_chain_statement`'s conclusion is:                     *)
(*                                                                            *)
(*   |h_prev| <= ulp(snd (b64_TwoSum x (cs_carry state))) / 2.                *)
(*                                                                            *)
(* The "snd b64_TwoSum" value `h := snd (b64_TwoSum x q)` is the rounding   *)
(* error of `b64_plus x q`.  By the TwoSum theorem |h| <= ulp(qnew)/2 with  *)
(* `qnew := b64_plus x q`; in particular |h| is in `qnew`'s low binade,     *)
(* so `ulp(h)` is roughly `ulp(qnew) * 2^-53 ≈ ulp(q) * 2^-53` in the       *)
(* generic no-cancellation case.                                              *)
(*                                                                            *)
(* The invariant gives `|h_prev| <= ulp(q)/2`.                                *)
(* The h-chain wants `|h_prev| <= ulp(h)/2 ≈ ulp(q) * 2^-54`.                *)
(*                                                                            *)
(* Gap: the invariant's bound is roughly **2^53 too loose**.  Closing the   *)
(* gap requires showing that `h_prev` is not merely below `ulp(q)/2` but   *)
(* far below it -- specifically below `ulp(h)/2`.  This needs the          *)
(* magnitude bookkeeping of Shewchuk §4 (provenance + sort ordering +      *)
(* per-source nonoverlap) that the invariant alone does not encode.        *)
(* -------------------------------------------------------------------------- *)

Lemma test_invariant_implies_h_prev_bound :
  forall (state : cascade_state)
         (processed : list binary64)
         (remaining : list tagged_b64)
         (h_prev : binary64) (hs_tail : list binary64),
    cascade_invariant state processed remaining ->
    cs_output state = hs_tail ++ [h_prev] ->
    Binary.B2R prec emax (cs_carry state) <> 0 ->
    Binary.B2R prec emax h_prev <> 0 ->
    Rabs (Binary.B2R prec emax h_prev) <=
      ulp radix2 (SpecFloat.fexp prec emax)
        (Binary.B2R prec emax (cs_carry state)) / 2.
Proof.
  intros state processed remaining h_prev hs_tail Hinv Hout Hcq Hch.
  unfold cascade_invariant in Hinv.
  destruct Hinv as [Ha _].
  unfold cascade_invariant_output in Ha.
  rewrite Hout in Ha.
  rewrite rev_app_distr in Ha. cbn [rev app] in Ha.
  unfold nonoverlap_shewchuk in Ha.
  cbn [compress] in Ha.
  destruct (Rcompare (Binary.B2R prec emax (cs_carry state)) 0) eqn:Hcq_cmp.
  - apply Rcompare_Eq_inv in Hcq_cmp. contradiction.
  - destruct (Rcompare (Binary.B2R prec emax h_prev) 0) eqn:Hch_cmp.
    + apply Rcompare_Eq_inv in Hch_cmp. contradiction.
    + cbn [nonoverlap_strict] in Ha.
      destruct Ha as [Hss _]. unfold strict_succ_b64 in Hss. exact Hss.
    + cbn [nonoverlap_strict] in Ha.
      destruct Ha as [Hss _]. unfold strict_succ_b64 in Hss. exact Hss.
  - destruct (Rcompare (Binary.B2R prec emax h_prev) 0) eqn:Hch_cmp.
    + apply Rcompare_Eq_inv in Hch_cmp. contradiction.
    + cbn [nonoverlap_strict] in Ha.
      destruct Ha as [Hss _]. unfold strict_succ_b64 in Hss. exact Hss.
    + cbn [nonoverlap_strict] in Ha.
      destruct Ha as [Hss _]. unfold strict_succ_b64 in Hss. exact Hss.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions tagged_input.
Print Assumptions untag_tagged_input.
Print Assumptions length_tagged_input.
Print Assumptions cascade_invariant_empty.
Print Assumptions cascade_h_chain_statement.
Print Assumptions test_invariant_implies_h_prev_bound.
Print Assumptions b64_plus_abs_bound.
Print Assumptions ulp_FLT_le_eps_b64.
Print Assumptions b64_plus_abs_bound_with_normal.
Print Assumptions run_bound_absorb_e.
Print Assumptions run_bound_absorb_f.
Print Assumptions run_bound_step_preserves.
Print Assumptions cascade_h_chain_pathA_pos.
