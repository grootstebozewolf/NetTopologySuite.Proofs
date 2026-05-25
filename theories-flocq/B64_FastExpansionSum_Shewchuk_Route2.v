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
(* Session 13: integer-safe specialised headline pulls in coord_int_safe   *)
(* + b64_plus_int_exact from Orient_b64_exact.                              *)
From NTS.Proofs.Flocq Require Import Orient_b64_exact.

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

(* SESSION 10 REFACTOR.  Clause (b) (cascade_invariant_magnitude) was        *)
(* structurally non-preservable: the triangle bound on b64_plus gives        *)
(* |new cs_carry| <= |x| + |cs_carry|, which exceeds |max_abs_b64 processed| *)
(* for any constant factor (1 + C > C for finite C).  No consumers used it. *)
(* Dropped from the invariant; processed parameter retained for backwards   *)
(* compatibility with existing call sites that pass it.                      *)
Definition cascade_invariant
  (state : cascade_state)
  (_processed : list binary64)
  (remaining : list tagged_b64)
  : Prop :=
  cascade_invariant_output (cs_carry state) (cs_output state) /\
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
    (split; [|split]).
  - (* (a) output well-formed -- from_e branch. *)
    unfold cascade_invariant_output.
    cbn [cs_carry cs_output rev].
    unfold nonoverlap_shewchuk.
    cbn [compress].
    destruct (Rcompare (Binary.B2R prec emax q) 0);
      cbn [nonoverlap_strict]; exact I.
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

(* Aborted placeholder retained as Session 1 documentation of the structural *)
(* obstacle.  Now superseded by cascade_step_preserves_invariant_pathA      *)
(* (Session 10, below) which composes the Sessions 6-9 preservation         *)
(* lemmas under explicit Path A and within-source/sorted hypotheses.        *)
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

(* b64_TwoSum exact-step for negative x.  Mirrors the corpus's              *)
(* b64_TwoSum_pathA_exact_step (positive x) via round_eq_pathA_negative.     *)
Lemma b64_TwoSum_pathA_exact_step_negative :
  forall e q : binary64,
    Binary.B2R prec emax e < 0 ->
    Rabs (Binary.B2R prec emax q) <
      ulp radix2 (SpecFloat.fexp prec emax)
        (succ radix2 (SpecFloat.fexp prec emax)
          (Binary.B2R prec emax e)) / 2 ->
    b64_TwoSum_safe e q ->
    Binary.B2R prec emax (fst (b64_TwoSum e q)) = Binary.B2R prec emax e /\
    Binary.B2R prec emax (snd (b64_TwoSum e q)) = Binary.B2R prec emax q.
Proof.
  intros e q He Hpw Hsafe.
  unfold b64_TwoSum_safe in Hsafe.
  destruct Hsafe as [Hs1 [Hs2 [Hs3 [Hs4 [Hs5 Hs6]]]]].
  pose proof (b64_TwoSum_correct e q Hs1 Hs2 Hs3 Hs4 Hs5 Hs6) as HTC.
  destruct (b64_TwoSum e q) as [a b] eqn:HTS.
  cbn [fst snd] in *.
  assert (Ha : a = b64_plus e q).
  { rewrite <- (b64_TwoSum_fst e q). rewrite HTS. reflexivity. }
  subst a.
  pose proof (b64_plus_correct e q Hs1) as [HBplus _].
  pose proof (b64_format_B2R e) as Hfe.
  pose proof (round_eq_pathA_negative
                (Binary.B2R prec emax e) (Binary.B2R prec emax q)
                He Hfe Hpw) as Hround.
  assert (HBplus_eq :
    Binary.B2R prec emax (b64_plus e q) = Binary.B2R prec emax e).
  { rewrite HBplus. exact Hround. }
  split. exact HBplus_eq. lra.
Qed.

(* The cascade_h_chain link, negative case. *)
Lemma cascade_h_chain_pathA_neg :
  forall (x q h_prev : binary64),
    Binary.B2R prec emax x < 0 ->
    Rabs (Binary.B2R prec emax q) <
      ulp radix2 (SpecFloat.fexp prec emax)
        (succ radix2 (SpecFloat.fexp prec emax)
          (Binary.B2R prec emax x)) / 2 ->
    Rabs (Binary.B2R prec emax h_prev)
      <= b64_ulp (Binary.B2R prec emax q) / 2 ->
    b64_TwoSum_safe x q ->
    Rabs (Binary.B2R prec emax h_prev)
      <= b64_ulp (Binary.B2R prec emax (snd (b64_TwoSum x q))) / 2.
Proof.
  intros x q h_prev Hx Hpw Hhprev Hsafe.
  pose proof (b64_TwoSum_pathA_exact_step_negative x q Hx Hpw Hsafe)
    as [_ Hsnd_eq].
  rewrite Hsnd_eq.
  exact Hhprev.
Qed.

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
(* DELIVERABLE 4 -- cascade-level h-chain step.                               *)
(*                                                                            *)
(* Composes test_invariant_implies_h_prev_bound (clause (a) gives             *)
(* |h_prev| <= ulp(cs_carry)/2) with cascade_h_chain_pathA_pos (under         *)
(* Path A, ulp(snd) = ulp(cs_carry), so the bound lifts).                     *)
(*                                                                            *)
(* This is the cascade-level h-chain link: at a Path A step (positive x,     *)
(* small carry, nonzero cs_carry/h_prev), the cascade's most-recent error   *)
(* h_prev is bounded by half-ulp of the NEW error h_new.  This is the        *)
(* load-bearing claim for clause (a) preservation when Path A holds.        *)
(*                                                                            *)
(* The remaining structural work (for cascade_step_preserves_invariant       *)
(* clause (a) under non-Path-A cases) is documented for Session 9.           *)
(* -------------------------------------------------------------------------- *)

(* compress preserves map B2R equality.  Two binary64 lists with the same    *)
(* sequence of B2R values produce compressed lists with the same B2R         *)
(* sequence (the binary64 representations may differ, but the values match). *)
Lemma compress_map_B2R_eq :
  forall xs ys : list binary64,
    map (Binary.B2R prec emax) xs = map (Binary.B2R prec emax) ys ->
    map (Binary.B2R prec emax) (compress xs)
      = map (Binary.B2R prec emax) (compress ys).
Proof.
  induction xs as [|x xs IH]; intros ys Hmap.
  - destruct ys; [reflexivity | discriminate].
  - destruct ys as [|y ys]; [discriminate|].
    simpl in Hmap. inversion Hmap as [[Hxy Hrest]].
    cbn [compress].
    rewrite Hxy.
    destruct (Rcompare (Binary.B2R prec emax y) 0) eqn:Hcmp.
    + apply IH; exact Hrest.
    + simpl. f_equal; [exact Hxy | apply IH; exact Hrest].
    + simpl. f_equal; [exact Hxy | apply IH; exact Hrest].
Qed.

(* nonoverlap_shewchuk preserves under map-B2R equality. *)
Lemma nonoverlap_shewchuk_B2R_compat :
  forall xs ys : list binary64,
    map (Binary.B2R prec emax) xs = map (Binary.B2R prec emax) ys ->
    nonoverlap_shewchuk xs <-> nonoverlap_shewchuk ys.
Proof.
  intros xs ys Hmap.
  unfold nonoverlap_shewchuk.
  apply nonoverlap_strict_B2R_compat.
  apply compress_map_B2R_eq. exact Hmap.
Qed.

Lemma cascade_h_chain_step :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov_x : provenance)
         (rest : list tagged_b64)
         (h_prev : binary64) (hs_tail : list binary64),
    cascade_invariant state processed ((x, prov_x) :: rest) ->
    cs_output state = hs_tail ++ [h_prev] ->
    0 < Binary.B2R prec emax x ->
    strict_succ_pathA_R (Binary.B2R prec emax x)
                        (Binary.B2R prec emax (cs_carry state)) ->
    Binary.B2R prec emax (cs_carry state) <> 0 ->
    Binary.B2R prec emax h_prev <> 0 ->
    Rabs (Binary.B2R prec emax h_prev)
      <= b64_ulp (Binary.B2R prec emax
                    (snd (b64_TwoSum x (cs_carry state)))) / 2.
Proof.
  intros state processed x prov_x rest h_prev hs_tail
         Hinv Hout Hx Hpw Hcq Hch.
  (* Step 1: extract |h_prev| <= ulp(cs_carry)/2 from clause (a). *)
  pose proof (test_invariant_implies_h_prev_bound
                state processed ((x, prov_x) :: rest) h_prev hs_tail
                Hinv Hout Hcq Hch) as Hh_bound.
  (* Step 2: extract b64_TwoSum_safe from clause (c). *)
  unfold cascade_invariant in Hinv.
  destruct Hinv as [_ [Hc _]].
  unfold cascade_invariant_handover in Hc.
  cbn [cs_carry] in Hc.
  destruct Hc as [Hsafe _].
  (* Step 3: apply cascade_h_chain_pathA_pos. *)
  exact (cascade_h_chain_pathA_pos x (cs_carry state) h_prev
            Hx Hpw Hh_bound Hsafe).
Qed.

(* -------------------------------------------------------------------------- *)
(* DELIVERABLE 5 -- clause (a) preservation under Path A.                     *)
(*                                                                            *)
(* Under Path A's hypothesis (positive x, |cs_carry| < ulp(pred x)/2) and    *)
(* cs_carry ≠ 0, b64_TwoSum_pathA_exact_step gives B2R(fst) = B2R x and      *)
(* B2R(snd) = B2R cs_carry.  Then nonoverlap_shewchuk_B2R_compat lifts the   *)
(* output predicate from the new state to (x :: cs_carry :: rev cs_output), *)
(* where the chain reduces to (Path A precondition) + (old clause (a)).      *)
(*                                                                            *)
(* The cs_carry = 0 case is degenerate (perfect cancellation in the cascade *)
(* history); excluded here as an explicit hypothesis.                         *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_step_clause_a_pathA_pos :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov : provenance) (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    0 < Binary.B2R prec emax x ->
    strict_succ_pathA_R (Binary.B2R prec emax x)
                        (Binary.B2R prec emax (cs_carry state)) ->
    Binary.B2R prec emax (cs_carry state) <> 0 ->
    cascade_invariant_output
      (fst (b64_TwoSum x (cs_carry state)))
      (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]).
Proof.
  intros state processed x prov rest Hinv Hx Hpw Hcq.
  unfold cascade_invariant_output.
  rewrite rev_app_distr. cbn [rev app].
  (* Goal: nonoverlap_shewchuk
            (fst (b64_TwoSum x (cs_carry state))
             :: snd (b64_TwoSum x (cs_carry state)) :: rev (cs_output state)) *)
  (* Extract safety from clause (c). *)
  unfold cascade_invariant in Hinv.
  destruct Hinv as [Ha [Hc _]].
  unfold cascade_invariant_handover in Hc.
  cbn [cs_carry] in Hc.
  destruct Hc as [Hsafe _].
  (* Apply b64_TwoSum_pathA_exact_step: B2R fst = B2R x, B2R snd = B2R q. *)
  pose proof (b64_TwoSum_pathA_exact_step x (cs_carry state) Hx Hpw Hsafe)
    as [Hfst Hsnd].
  (* Lift via B2R compat to the goal with x and cs_carry in place. *)
  apply (nonoverlap_shewchuk_B2R_compat
    (fst (b64_TwoSum x (cs_carry state)) ::
     snd (b64_TwoSum x (cs_carry state)) :: rev (cs_output state))
    (x :: (cs_carry state) :: rev (cs_output state))).
  { cbn [map].
    rewrite Hfst, Hsnd. reflexivity. }
  (* Now show nonoverlap_shewchuk (x :: cs_carry :: rev cs_output).         *)
  unfold cascade_invariant_output in Ha.
  unfold nonoverlap_shewchuk in *.
  cbn [compress].
  (* Rcompare (B2R x) 0 = Gt (since 0 < B2R x). *)
  destruct (Rcompare (Binary.B2R prec emax x) 0) eqn:Hxcmp.
  { apply Rcompare_Eq_inv in Hxcmp. lra. }
  { apply Rcompare_Lt_inv in Hxcmp. lra. }
  (* Rcompare (B2R cs_carry) 0 = Lt or Gt (since nonzero). *)
  destruct (Rcompare (Binary.B2R prec emax (cs_carry state)) 0) eqn:Hccmp.
  { apply Rcompare_Eq_inv in Hccmp. contradiction. }
  (* Lt case *)
  { cbn [nonoverlap_strict].
    split.
    - (* strict_succ_b64 x cs_carry: |cs_carry| <= ulp(x)/2 from Path A. *)
      unfold strict_succ_b64.
      unfold strict_succ_pathA_R in Hpw.
      pose proof (pred_le_id radix2 (SpecFloat.fexp prec emax)
                    (Binary.B2R prec emax x)) as Hpred_le.
      pose proof (b64_format_B2R x) as Hfx.
      pose proof (@pred_ge_0 radix2 _ b64_fexp_valid
                    (Binary.B2R prec emax x) Hx Hfx) as Hpred_ge.
      pose proof (@ulp_le_pos radix2 _ b64_fexp_valid b64_fexp_monotone
                    _ _ Hpred_ge Hpred_le) as Hulp_le.
      lra.
    - (* nonoverlap_strict (cs_carry :: compress (rev cs_output)) from Ha. *)
      cbn [compress] in Ha.
      rewrite Hccmp in Ha.
      cbn [nonoverlap_strict] in Ha.
      destruct (compress (rev (cs_output state))).
      + cbn [nonoverlap_strict] in *. exact I.
      + cbn [nonoverlap_strict] in *. exact Ha. }
  (* Gt case (symmetric) *)
  { cbn [nonoverlap_strict].
    split.
    - unfold strict_succ_b64.
      unfold strict_succ_pathA_R in Hpw.
      pose proof (pred_le_id radix2 (SpecFloat.fexp prec emax)
                    (Binary.B2R prec emax x)) as Hpred_le.
      pose proof (b64_format_B2R x) as Hfx.
      pose proof (@pred_ge_0 radix2 _ b64_fexp_valid
                    (Binary.B2R prec emax x) Hx Hfx) as Hpred_ge.
      pose proof (@ulp_le_pos radix2 _ b64_fexp_valid b64_fexp_monotone
                    _ _ Hpred_ge Hpred_le) as Hulp_le.
      lra.
    - cbn [compress] in Ha.
      rewrite Hccmp in Ha.
      cbn [nonoverlap_strict] in Ha.
      destruct (compress (rev (cs_output state))).
      + cbn [nonoverlap_strict] in *. exact I.
      + cbn [nonoverlap_strict] in *. exact Ha. }
Qed.

(* Clause (a) preservation under Path A, negative x.                         *)
(*                                                                            *)
(* Mirrors cascade_step_clause_a_pathA_pos but uses                          *)
(* b64_TwoSum_pathA_exact_step_negative for the B2R equalities and           *)
(* derives ulp(succ x) <= ulp(x) (for x < 0) via succ_opp + pred_le_id        *)
(* + ulp_le_pos + ulp_opp.                                                    *)
Lemma cascade_step_clause_a_pathA_neg :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov : provenance) (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    Binary.B2R prec emax x < 0 ->
    Rabs (Binary.B2R prec emax (cs_carry state)) <
      ulp radix2 (SpecFloat.fexp prec emax)
        (succ radix2 (SpecFloat.fexp prec emax)
          (Binary.B2R prec emax x)) / 2 ->
    Binary.B2R prec emax (cs_carry state) <> 0 ->
    cascade_invariant_output
      (fst (b64_TwoSum x (cs_carry state)))
      (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]).
Proof.
  intros state processed x prov rest Hinv Hx Hpw Hcq.
  unfold cascade_invariant_output.
  rewrite rev_app_distr. cbn [rev app].
  unfold cascade_invariant in Hinv.
  destruct Hinv as [Ha [Hc _]].
  unfold cascade_invariant_handover in Hc.
  cbn [cs_carry] in Hc.
  destruct Hc as [Hsafe _].
  pose proof (b64_TwoSum_pathA_exact_step_negative
                x (cs_carry state) Hx Hpw Hsafe) as [Hfst Hsnd].
  apply (nonoverlap_shewchuk_B2R_compat
    (fst (b64_TwoSum x (cs_carry state)) ::
     snd (b64_TwoSum x (cs_carry state)) :: rev (cs_output state))
    (x :: (cs_carry state) :: rev (cs_output state))).
  { cbn [map]. rewrite Hfst, Hsnd. reflexivity. }
  unfold cascade_invariant_output in Ha.
  unfold nonoverlap_shewchuk in *.
  cbn [compress].
  destruct (Rcompare (Binary.B2R prec emax x) 0) eqn:Hxcmp.
  { apply Rcompare_Eq_inv in Hxcmp. lra. }
  2: { apply Rcompare_Gt_inv in Hxcmp. lra. }
  (* Now x < 0 branch. *)
  destruct (Rcompare (Binary.B2R prec emax (cs_carry state)) 0) eqn:Hccmp.
  { apply Rcompare_Eq_inv in Hccmp. contradiction. }
  (* Both Lt and Gt sub-cases for cs_carry have the same structure: derive  *)
  (* ulp(succ x) <= ulp(x) for x < 0 using succ_opp + ulp_opp + pred_le_id. *)
  - cbn [nonoverlap_strict].
    split.
    + (* strict_succ_b64 x cs_carry under x < 0. *)
      unfold strict_succ_b64.
      rewrite <- (Ropp_involutive (succ radix2 (SpecFloat.fexp prec emax)
                                     (Binary.B2R prec emax x))) in Hpw.
      rewrite <- pred_opp in Hpw.
      rewrite ulp_opp in Hpw.
      assert (Hxopp_pos : 0 < - Binary.B2R prec emax x) by lra.
      pose proof (b64_format_B2R x) as Hfx.
      assert (Hfx_opp : generic_format radix2 (SpecFloat.fexp prec emax)
                         (- Binary.B2R prec emax x)).
      { apply generic_format_opp. exact Hfx. }
      pose proof (@pred_ge_0 radix2 _ b64_fexp_valid
                    (- Binary.B2R prec emax x) Hxopp_pos Hfx_opp) as Hpred_ge.
      pose proof (pred_le_id radix2 (SpecFloat.fexp prec emax)
                    (- Binary.B2R prec emax x)) as Hpred_le.
      pose proof (@ulp_le_pos radix2 _ b64_fexp_valid b64_fexp_monotone
                    _ _ Hpred_ge Hpred_le) as Hulp_le.
      rewrite (ulp_opp radix2 (SpecFloat.fexp prec emax)
                 (Binary.B2R prec emax x)) in Hulp_le.
      lra.
    + cbn [compress] in Ha.
      rewrite Hccmp in Ha.
      cbn [nonoverlap_strict] in Ha.
      destruct (compress (rev (cs_output state))).
      * cbn [nonoverlap_strict] in *. exact I.
      * cbn [nonoverlap_strict] in *. exact Ha.
  - cbn [nonoverlap_strict].
    split.
    + unfold strict_succ_b64.
      rewrite <- (Ropp_involutive (succ radix2 (SpecFloat.fexp prec emax)
                                     (Binary.B2R prec emax x))) in Hpw.
      rewrite <- pred_opp in Hpw.
      rewrite ulp_opp in Hpw.
      assert (Hxopp_pos : 0 < - Binary.B2R prec emax x) by lra.
      pose proof (b64_format_B2R x) as Hfx.
      assert (Hfx_opp : generic_format radix2 (SpecFloat.fexp prec emax)
                         (- Binary.B2R prec emax x)).
      { apply generic_format_opp. exact Hfx. }
      pose proof (@pred_ge_0 radix2 _ b64_fexp_valid
                    (- Binary.B2R prec emax x) Hxopp_pos Hfx_opp) as Hpred_ge.
      pose proof (pred_le_id radix2 (SpecFloat.fexp prec emax)
                    (- Binary.B2R prec emax x)) as Hpred_le.
      pose proof (@ulp_le_pos radix2 _ b64_fexp_valid b64_fexp_monotone
                    _ _ Hpred_ge Hpred_le) as Hulp_le.
      rewrite (ulp_opp radix2 (SpecFloat.fexp prec emax)
                 (Binary.B2R prec emax x)) in Hulp_le.
      lra.
    + cbn [compress] in Ha.
      rewrite Hccmp in Ha.
      cbn [nonoverlap_strict] in Ha.
      destruct (compress (rev (cs_output state))).
      * cbn [nonoverlap_strict] in *. exact I.
      * cbn [nonoverlap_strict] in *. exact Ha.
Qed.

(* Combined clause (a) preservation under Path A.  Dispatches to the         *)
(* positive or negative case based on the sign of B2R x.  Covers all          *)
(* nonzero-x Path A scenarios.                                                *)
Lemma cascade_step_clause_a_pathA :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov : provenance) (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    Binary.B2R prec emax x <> 0 ->
    Binary.B2R prec emax (cs_carry state) <> 0 ->
    ((0 < Binary.B2R prec emax x /\
      strict_succ_pathA_R (Binary.B2R prec emax x)
                          (Binary.B2R prec emax (cs_carry state)))
     \/
     (Binary.B2R prec emax x < 0 /\
      Rabs (Binary.B2R prec emax (cs_carry state)) <
        ulp radix2 (SpecFloat.fexp prec emax)
          (succ radix2 (SpecFloat.fexp prec emax)
            (Binary.B2R prec emax x)) / 2)) ->
    cascade_invariant_output
      (fst (b64_TwoSum x (cs_carry state)))
      (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]).
Proof.
  intros state processed x prov rest Hinv Hxnz Hcq Hcases.
  destruct Hcases as [[Hx Hpw] | [Hx Hpw]].
  - eapply cascade_step_clause_a_pathA_pos; eassumption.
  - eapply cascade_step_clause_a_pathA_neg; eassumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* DELIVERABLE 6 -- cascade_step_preserves_invariant under Path A.            *)
(*                                                                            *)
(* Composes the Session 6 (clause d′ preservation) and Sessions 8-9 (clause  *)
(* a preservation under Path A) results into the full invariant preservation *)
(* under Path A.  Clause (c) preservation requires knowing the NEXT step's   *)
(* handover, which is supplied as an explicit hypothesis (the cascade        *)
(* driver provides it from input preconditions and the next remaining input).*)
(*                                                                            *)
(* Path A is the structural assumption: at every cascade step, the next     *)
(* input dominates the current carry by the strict half-ulp margin.  This   *)
(* holds for within-source consecutive steps in the typical Stage D path.   *)
(* Cross-prov transitions or non-Path-A configurations are out of scope     *)
(* here -- they remain the deferred-proof obstacle.                          *)
(* -------------------------------------------------------------------------- *)

(* cs_carry / cs_output / cs_e_max / cs_f_max access on the step state.      *)
Lemma cs_carry_cascade_step_state :
  forall state x prov,
    cs_carry (cascade_step_state state x prov)
      = fst (b64_TwoSum x (cs_carry state)).
Proof. intros. destruct prov; reflexivity. Qed.

Lemma cs_output_cascade_step_state :
  forall state x prov,
    cs_output (cascade_step_state state x prov)
      = cs_output state ++ [snd (b64_TwoSum x (cs_carry state))].
Proof. intros. destruct prov; reflexivity. Qed.

Lemma cascade_step_preserves_invariant_pathA :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov : provenance) (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    Binary.B2R prec emax x <> 0 ->
    Binary.B2R prec emax (cs_carry state) <> 0 ->
    (* Path A on this step. *)
    ((0 < Binary.B2R prec emax x /\
      strict_succ_pathA_R (Binary.B2R prec emax x)
                          (Binary.B2R prec emax (cs_carry state)))
     \/
     (Binary.B2R prec emax x < 0 /\
      Rabs (Binary.B2R prec emax (cs_carry state)) <
        ulp radix2 (SpecFloat.fexp prec emax)
          (succ radix2 (SpecFloat.fexp prec emax)
            (Binary.B2R prec emax x)) / 2)) ->
    (* Within-source structure for clause (d′) preservation. *)
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
    (* Normal-range hypotheses for clause (d′) preservation. *)
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax x) ->
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax (b64_plus x (cs_carry state))) ->
    (* Next-step handover supplied by the cascade driver. *)
    cascade_invariant_handover (cascade_step_state state x prov) rest ->
    cascade_invariant
      (cascade_step_state state x prov)
      (processed ++ [x])
      rest.
Proof.
  intros state processed x prov rest Hinv Hxnz Hcq Hpath Hwithin
         Hxnorm Hpnorm Hho_new.
  (* Extract safety from old clause (c). *)
  pose proof Hinv as Hinv_full.
  unfold cascade_invariant in Hinv_full.
  destruct Hinv_full as [_ [Hc_old Hd_old]].
  unfold cascade_invariant_handover in Hc_old.
  cbn [cs_carry] in Hc_old.
  destruct Hc_old as [Hsafe _].
  (* Now assemble the three clauses for the new state. *)
  unfold cascade_invariant.
  split; [|split].
  - (* Clause (a) preservation via cascade_step_clause_a_pathA. *)
    rewrite cs_carry_cascade_step_state, cs_output_cascade_step_state.
    eapply cascade_step_clause_a_pathA; eassumption.
  - (* Clause (c): supplied as hypothesis. *)
    exact Hho_new.
  - (* Clause (d′) preservation via run_bound_step_preserves. *)
    unfold b64_TwoSum_safe in Hsafe.
    destruct Hsafe as [Hsafe_plus _].
    apply (run_bound_step_preserves state x prov
             Hd_old Hsafe_plus Hxnorm Hpnorm Hwithin).
Qed.

(* -------------------------------------------------------------------------- *)
(* DELIVERABLE 7 -- cascade_run: cascade as a state-transition function.      *)
(*                                                                            *)
(* Iterates cascade_step_state over a tagged input.  This connects            *)
(* cascade_invariant (a state predicate) to the actual cascade computation,  *)
(* which is the missing link between the per-step preservation lemmas and    *)
(* the headline.                                                              *)
(*                                                                            *)
(* The relation to b64_grow_expansion_aux (the corpus's cascade): for a      *)
(* tagged input xs starting from state s,                                     *)
(*                                                                            *)
(*   cascade_run s xs                                                          *)
(*                                                                            *)
(* produces a final state whose cs_carry equals qfinal and whose              *)
(* cs_output equals (cs_output s) ++ hs, where                                *)
(*   (hs, qfinal) := b64_grow_expansion_aux (cs_carry s) (untag xs).         *)
(*                                                                            *)
(* cascade_run_correctness (below) Qed-closes this equivalence.               *)
(* -------------------------------------------------------------------------- *)

Fixpoint cascade_run
  (state : cascade_state) (xs : list tagged_b64) : cascade_state :=
  match xs with
  | nil => state
  | (x, prov) :: rest =>
      cascade_run (cascade_step_state state x prov) rest
  end.

Lemma untag_cons_pair :
  forall (x : binary64) (prov : provenance) (xs : list tagged_b64),
    untag ((x, prov) :: xs) = x :: untag xs.
Proof. intros. unfold untag. reflexivity. Qed.

(* The cascade_step_state's effect on cs_carry is provenance-independent.    *)
(* So is cs_output's append shape (snd of b64_TwoSum).  cascade_run's         *)
(* final cs_carry tracks b64_grow_expansion_aux's qfinal exactly.            *)
Lemma cascade_run_cs_carry :
  forall xs state,
    cs_carry (cascade_run state xs)
      = snd (b64_grow_expansion_aux (cs_carry state) (untag xs)).
Proof.
  induction xs as [|tx xs IH]; intros state.
  - reflexivity.
  - destruct tx as [x prov].
    cbn [cascade_run].
    rewrite IH, cs_carry_cascade_step_state, untag_cons_pair.
    cbn [b64_grow_expansion_aux].
    rewrite (surjective_pairing (b64_TwoSum x (cs_carry state))).
    cbn [fst snd].
    destruct (b64_grow_expansion_aux _ (untag xs)) as [hs qfinal] eqn:Hrec.
    reflexivity.
Qed.

Lemma cascade_run_cs_output :
  forall xs state,
    cs_output (cascade_run state xs)
      = cs_output state
        ++ fst (b64_grow_expansion_aux (cs_carry state) (untag xs)).
Proof.
  induction xs as [|tx xs IH]; intros state.
  - cbn. rewrite app_nil_r. reflexivity.
  - destruct tx as [x prov].
    cbn [cascade_run].
    rewrite IH, cs_output_cascade_step_state, cs_carry_cascade_step_state,
            untag_cons_pair.
    cbn [b64_grow_expansion_aux].
    rewrite (surjective_pairing (b64_TwoSum x (cs_carry state))).
    cbn [fst snd].
    destruct (b64_grow_expansion_aux _ (untag xs)) as [hs qfinal] eqn:Hrec.
    cbn [fst]. rewrite <- app_assoc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* DELIVERABLE 8 -- cascade_pathA_chain and the conditional headline.         *)
(*                                                                            *)
(* `cascade_pathA_chain state xs` asserts that EVERY step processing xs       *)
(* from state satisfies Path A's hypotheses (sign + strict_succ +             *)
(* within-source + normal-range + handover-for-next).  Recursive in xs.       *)
(*                                                                            *)
(* Under this chain, the cascade's invariant is preserved throughout, so      *)
(* clause (a) on the final state gives nonoverlap_shewchuk on the cascade   *)
(* output -- which is precisely fast_expansion_sum's output (via              *)
(* cascade_run_cs_carry / cascade_run_cs_output).                             *)
(*                                                                            *)
(* The chain hypothesis is the cut point: Stage D consumers discharge it     *)
(* via input-specific reasoning, or via the not-yet-formalised               *)
(* cross-prov-with-snd=0 case analysis.                                       *)
(* -------------------------------------------------------------------------- *)

Fixpoint cascade_pathA_chain
  (state : cascade_state) (xs : list tagged_b64) : Prop :=
  match xs with
  | nil => True
  | (x, prov) :: rest =>
      Binary.B2R prec emax x <> 0 /\
      Binary.B2R prec emax (cs_carry state) <> 0 /\
      ((0 < Binary.B2R prec emax x /\
        strict_succ_pathA_R (Binary.B2R prec emax x)
                            (Binary.B2R prec emax (cs_carry state)))
       \/
       (Binary.B2R prec emax x < 0 /\
        Rabs (Binary.B2R prec emax (cs_carry state)) <
          ulp radix2 (SpecFloat.fexp prec emax)
            (succ radix2 (SpecFloat.fexp prec emax)
              (Binary.B2R prec emax x)) / 2)) /\
      (match prov with
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
       end) /\
      bpow radix2 (b64_emin + prec - 1) <=
        Rabs (Binary.B2R prec emax x) /\
      bpow radix2 (b64_emin + prec - 1) <=
        Rabs (Binary.B2R prec emax (b64_plus x (cs_carry state))) /\
      cascade_invariant_handover (cascade_step_state state x prov) rest /\
      cascade_pathA_chain (cascade_step_state state x prov) rest
  end.

(* The cascade processes xs from state under Path A throughout: the invariant *)
(* on (state, xs) lifts to the invariant on (final state, nil) at the end.   *)
Lemma cascade_run_preserves_invariant_under_pathA :
  forall xs state processed,
    cascade_invariant state processed xs ->
    cascade_pathA_chain state xs ->
    cascade_invariant (cascade_run state xs)
                      (processed ++ untag xs) nil.
Proof.
  induction xs as [|tx xs IH]; intros state processed Hinv Hchain.
  - cbn [cascade_run untag map].
    rewrite app_nil_r.
    (* Hinv : cascade_invariant state processed nil.  Conclusion: same.    *)
    exact Hinv.
  - destruct tx as [x prov].
    cbn [cascade_pathA_chain] in Hchain.
    destruct Hchain as [Hxnz [Hcq [Hpath [Hwithin
                       [Hxnorm [Hpnorm [Hho_new Hchain']]]]]]].
    cbn [cascade_run].
    rewrite untag_cons_pair.
    (* Goal: cascade_invariant ... (processed ++ (x :: untag xs)) nil. *)
    (* Rearrange to ((processed ++ [x]) ++ untag xs) form for IH.       *)
    change (processed ++ x :: untag xs)
      with (processed ++ [x] ++ untag xs).
    rewrite app_assoc.
    apply IH.
    + (* cascade_invariant on the new state after one step *)
      eapply cascade_step_preserves_invariant_pathA; eassumption.
    + exact Hchain'.
Qed.

(* The headline output predicate: under Path A throughout, the cascade       *)
(* output is nonoverlap_shewchuk.  Direct consequence of clause (a) on the   *)
(* final state.                                                               *)
Lemma cascade_run_output_nonoverlap :
  forall init_state tagged_rest,
    cascade_invariant init_state nil tagged_rest ->
    cascade_pathA_chain init_state tagged_rest ->
    nonoverlap_shewchuk
      (cs_carry (cascade_run init_state tagged_rest)
       :: rev (cs_output (cascade_run init_state tagged_rest))).
Proof.
  intros init_state tagged_rest Hinv Hchain.
  pose proof (cascade_run_preserves_invariant_under_pathA
                tagged_rest init_state nil Hinv Hchain) as Hfinal.
  unfold cascade_invariant in Hfinal.
  destruct Hfinal as [Ha _].
  unfold cascade_invariant_output in Ha.
  exact Ha.
Qed.

(* -------------------------------------------------------------------------- *)
(* DELIVERABLE 9 -- integer-safe specialisation (Session 13).                 *)
(*                                                                            *)
(* Per the Session 12 prerequisite analysis, the integer regime has its own  *)
(* structural path to the headline: every b64_TwoSum step on int-exact       *)
(* operands produces snd = 0 in B2R, so the cascade output's h's are all     *)
(* zero, and `compress` filters them to leave a singleton -- trivially       *)
(* nonoverlap_shewchuk.                                                       *)
(*                                                                            *)
(* This bypasses cascade_pathA_chain entirely (Path A fails in the integer  *)
(* regime since |cs_carry| >= 1 while ulp(pred x)/2 << 1).                   *)
(* -------------------------------------------------------------------------- *)

(* compress filters all-zero lists to nil. *)
Lemma compress_all_zero_nil :
  forall zs : list binary64,
    Forall (fun z => Binary.B2R prec emax z = 0) zs ->
    compress zs = nil.
Proof.
  induction zs as [|z zs IH]; intros Hall.
  - reflexivity.
  - inversion Hall as [|? ? Hz Hrest]; subst.
    cbn [compress].
    rewrite (Rcompare_Eq _ _ Hz).
    apply IH. exact Hrest.
Qed.

(* nonoverlap_shewchuk holds for any list whose first element is followed     *)
(* only by B2R-zero elements: after `compress`, the result is at most a      *)
(* singleton, trivially nonoverlap.                                          *)
Lemma nonoverlap_shewchuk_first_then_zeros :
  forall (x : binary64) (zs : list binary64),
    Forall (fun z => Binary.B2R prec emax z = 0) zs ->
    nonoverlap_shewchuk (x :: zs).
Proof.
  intros x zs Hall.
  unfold nonoverlap_shewchuk.
  cbn [compress].
  rewrite (compress_all_zero_nil zs Hall).
  destruct (Rcompare (Binary.B2R prec emax x) 0);
    cbn [nonoverlap_strict]; exact I.
Qed.

(* Under integer exactness, b64_TwoSum's snd has B2R = 0: the sum has no    *)
(* rounding error, so the "low bits" of TwoSum are exactly zero.            *)
Lemma b64_TwoSum_snd_B2R_zero_under_int_exact :
  forall (x y : binary64) (a b : Z),
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax x = IZR a ->
    Binary.B2R prec emax y = IZR b ->
    (Z.abs (a + b) <= 2 ^ prec)%Z ->
    b64_TwoSum_safe x y ->
    Binary.B2R prec emax (snd (b64_TwoSum x y)) = 0.
Proof.
  intros x y a b Hfx Hfy HxR HyR Hbnd Hsafe.
  unfold b64_TwoSum_safe in Hsafe.
  destruct Hsafe as [Hs1 [Hs2 [Hs3 [Hs4 [Hs5 Hs6]]]]].
  pose proof (b64_TwoSum_correct x y Hs1 Hs2 Hs3 Hs4 Hs5 Hs6) as HTC.
  destruct (b64_TwoSum x y) as [fst_v snd_v] eqn:Hts.
  cbn [snd] in *.
  assert (Hfst_eq : fst_v = b64_plus x y).
  { rewrite <- (b64_TwoSum_fst x y). rewrite Hts. reflexivity. }
  subst fst_v.
  pose proof (b64_plus_int_exact x y a b Hfx Hfy HxR HyR Hbnd) as [HB2R _].
  rewrite HB2R, HxR, HyR in HTC.
  rewrite <- plus_IZR in HTC.
  lra.
Qed.

(* The two-singletons int-safe headline: for fast_expansion_sum [a] [b]    *)
(* on integer-valued operands with sum bounded by 2^prec, the output is    *)
(* nonoverlap_shewchuk.                                                    *)
(*                                                                          *)
(* This is the cleanest concrete int-regime headline: the cascade has one *)
(* step, produces an error of zero (in B2R), and compress filters it to   *)
(* a singleton output.                                                     *)
Theorem fast_expansion_sum_nonoverlap_shewchuk_int_safe_singletons :
  forall (a b : binary64) (na nb : Z),
    fast_expansion_sum_safe [a] [b] ->
    Binary.is_finite prec emax a = true ->
    Binary.is_finite prec emax b = true ->
    Binary.B2R prec emax a = IZR na ->
    Binary.B2R prec emax b = IZR nb ->
    (Z.abs (na + nb) <= 2 ^ prec)%Z ->
    nonoverlap_shewchuk (fast_expansion_sum [a] [b]).
Proof.
  intros a b na nb Hsafe Hfa Hfb HaR HbR Hbnd.
  unfold fast_expansion_sum, fast_expansion_sum_safe in *.
  cbn [app sort_by_abs insert_by_abs] in *.
  destruct (Rle_dec (Rabs (Binary.B2R prec emax a))
                    (Rabs (Binary.B2R prec emax b))) as [Hle | Hgt].
  - (* sorted = [a; b], cascade processes [b] starting from a. *)
    cbn [b64_grow_expansion_aux b64_grow_expansion_aux_safe] in *.
    destruct Hsafe as [Hts_safe _].
    destruct (b64_TwoSum b a) as [qnew h] eqn:Hts.
    cbn [fst snd rev].
    apply nonoverlap_shewchuk_first_then_zeros.
    constructor; [|constructor].
    (* Goal: B2R h = 0. *)
    pose proof (b64_TwoSum_snd_B2R_zero_under_int_exact
                  b a nb na Hfb Hfa HbR HaR) as Hzero.
    rewrite Z.add_comm in Hzero.
    specialize (Hzero Hbnd Hts_safe).
    rewrite Hts in Hzero. cbn [snd] in Hzero. exact Hzero.
  - (* sorted = [b; a], cascade processes [a] starting from b. *)
    cbn [b64_grow_expansion_aux b64_grow_expansion_aux_safe] in *.
    destruct Hsafe as [Hts_safe _].
    destruct (b64_TwoSum a b) as [qnew h] eqn:Hts.
    cbn [fst snd rev].
    apply nonoverlap_shewchuk_first_then_zeros.
    constructor; [|constructor].
    pose proof (b64_TwoSum_snd_B2R_zero_under_int_exact
                  a b na nb Hfa Hfb HaR HbR Hbnd Hts_safe) as Hzero.
    rewrite Hts in Hzero. cbn [snd] in Hzero. exact Hzero.
Qed.

(* -------------------------------------------------------------------------- *)
(* DELIVERABLE 10 -- general two-singleton headline (Session 14).             *)
(*                                                                            *)
(* For arbitrary binary64 a, b (no integer-safe assumption),                  *)
(* fast_expansion_sum [a] [b] produces a nonoverlap_shewchuk output.  The    *)
(* proof: one cascade step, b64_TwoSum_nonoverlap gives strict_succ_b64 on  *)
(* the resulting pair, which is exactly the half-ulp chain.                  *)
(*                                                                            *)
(* This is the FIRST unconditional general-case headline -- no Path A, no    *)
(* integer-safe, no special structural assumption on inputs.  Only           *)
(* fast_expansion_sum_safe (the safety chain).                                *)
(* -------------------------------------------------------------------------- *)

(* Pair-form nonoverlap_shewchuk: a chain of two elements where the second  *)
(* is half-ulp-bounded by the first.  Handles all four compress cases.      *)
Lemma nonoverlap_shewchuk_pair :
  forall (a b : binary64),
    strict_succ_b64 a b ->
    nonoverlap_shewchuk (a :: b :: nil).
Proof.
  intros a b Hss.
  unfold nonoverlap_shewchuk.
  cbn [compress].
  destruct (Rcompare (Binary.B2R prec emax a) 0);
    destruct (Rcompare (Binary.B2R prec emax b) 0);
    cbn [nonoverlap_strict].
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - split; [exact Hss | exact I].
  - split; [exact Hss | exact I].
  - exact I.
  - split; [exact Hss | exact I].
  - split; [exact Hss | exact I].
Qed.

Theorem fast_expansion_sum_nonoverlap_shewchuk_two_singletons :
  forall (a b : binary64),
    fast_expansion_sum_safe [a] [b] ->
    nonoverlap_shewchuk (fast_expansion_sum [a] [b]).
Proof.
  intros a b Hsafe.
  unfold fast_expansion_sum, fast_expansion_sum_safe in *.
  cbn [app sort_by_abs insert_by_abs] in *.
  destruct (Rle_dec (Rabs (Binary.B2R prec emax a))
                    (Rabs (Binary.B2R prec emax b))) as [Hle | Hgt].
  - (* sorted = [a; b].  Cascade processes [b] starting from a. *)
    cbn [b64_grow_expansion_aux b64_grow_expansion_aux_safe] in *.
    destruct Hsafe as [Hts_safe _].
    unfold b64_TwoSum_safe in Hts_safe.
    destruct Hts_safe as [Hs1 [Hs2 [Hs3 [Hs4 [Hs5 Hs6]]]]].
    pose proof (b64_TwoSum_nonoverlap b a Hs1 Hs2 Hs3 Hs4 Hs5 Hs6) as Hno.
    destruct (b64_TwoSum b a) as [qnew h] eqn:Hts.
    cbn [fst snd rev].
    apply nonoverlap_shewchuk_pair.
    unfold strict_succ_b64.
    exact Hno.
  - (* sorted = [b; a].  Cascade processes [a] starting from b. *)
    cbn [b64_grow_expansion_aux b64_grow_expansion_aux_safe] in *.
    destruct Hsafe as [Hts_safe _].
    unfold b64_TwoSum_safe in Hts_safe.
    destruct Hts_safe as [Hs1 [Hs2 [Hs3 [Hs4 [Hs5 Hs6]]]]].
    pose proof (b64_TwoSum_nonoverlap a b Hs1 Hs2 Hs3 Hs4 Hs5 Hs6) as Hno.
    destruct (b64_TwoSum a b) as [qnew h] eqn:Hts.
    cbn [fst snd rev].
    apply nonoverlap_shewchuk_pair.
    unfold strict_succ_b64.
    exact Hno.
Qed.

(* -------------------------------------------------------------------------- *)
(* DELIVERABLE 11 -- general case attempt (Session 14).                       *)
(*                                                                            *)
(* Attempt the full Admitted headline from B64_FastExpansionSum_Shewchuk.v   *)
(* directly.  Drops the integer-safe and Path-A hypotheses; takes only the   *)
(* fast_expansion_sum_safe + nonoverlap_shewchuk preconditions of the        *)
(* original Admitted Theorem.                                                 *)
(*                                                                            *)
(* The proof structure: case-split on sort_by_abs's length.                  *)
(*   - Length 0: nonoverlap_shewchuk nil = True.                              *)
(*   - Length 1: nonoverlap_shewchuk [x] = True.                              *)
(*   - Length 2: cascade has one step; b64_TwoSum_nonoverlap gives the chain.*)
(*   - Length 3+: cascade has 2+ steps; the h-chain link between consecutive *)
(*     h's is the open obstacle.                                              *)
(*                                                                            *)
(* This lemma reaches Length 3+ and Aborts.  The Aborted goal is the        *)
(* concrete demonstration of the deferred-proof obstacle: from the          *)
(* invariant + nonoverlap_shewchuk inputs, deriving strict_succ_b64 between *)
(* consecutive cascade errors requires Shewchuk Theorem 13's deep magnitude *)
(* bookkeeping (Path A everywhere, or the cross-prov-with-snd=0 case        *)
(* analysis).                                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma fast_expansion_sum_nonoverlap_shewchuk_route1_attempt :
  forall (e f : list binary64),
    fast_expansion_sum_safe e f ->
    nonoverlap_shewchuk e ->
    nonoverlap_shewchuk f ->
    nonoverlap_shewchuk (fast_expansion_sum e f).
Proof.
  intros e f Hsafe Hne Hnf.
  unfold fast_expansion_sum, fast_expansion_sum_safe in *.
  destruct (sort_by_abs (e ++ f)) as [|x xs] eqn:Hsort.
  - (* Length 0: nonoverlap_shewchuk nil. *)
    unfold nonoverlap_shewchuk. cbn [compress nonoverlap_strict]. exact I.
  - destruct xs as [|x' xs'].
    + (* Length 1: nonoverlap_shewchuk on singleton. *)
      cbn [b64_grow_expansion_aux rev].
      unfold nonoverlap_shewchuk. cbn [compress].
      destruct (Rcompare (Binary.B2R prec emax x) 0);
        cbn [nonoverlap_strict]; exact I.
    + destruct xs' as [|x'' xs''].
      * (* Length 2: single cascade step, b64_TwoSum_nonoverlap suffices. *)
        cbn [b64_grow_expansion_aux b64_grow_expansion_aux_safe] in *.
        destruct Hsafe as [Hts_safe _].
        unfold b64_TwoSum_safe in Hts_safe.
        destruct Hts_safe as [Hs1 [Hs2 [Hs3 [Hs4 [Hs5 Hs6]]]]].
        pose proof (b64_TwoSum_nonoverlap x' x Hs1 Hs2 Hs3 Hs4 Hs5 Hs6) as Hno.
        destruct (b64_TwoSum x' x) as [qnew h] eqn:Hts.
        cbn [fst snd rev].
        apply nonoverlap_shewchuk_pair.
        unfold strict_succ_b64. exact Hno.
      * (* Length 3+: cascade has 2+ steps.  Output is qfinal :: rev hs       *)
        (* with |hs| >= 2.  After compress (assuming no zeros), need the     *)
        (* h-chain link strict_succ_b64 h_k h_{k-1} between consecutive      *)
        (* cascade errors.                                                    *)
        (*                                                                    *)
        (* This is the load-bearing claim from Sessions 1-12: under Path A   *)
        (* it holds (cascade_h_chain_pathA_pos/_neg); for arbitrary inputs   *)
        (* with non-Path-A configurations it remains the deferred-proof      *)
        (* obstacle.                                                          *)
        (*                                                                    *)
        (* The Sessions 1-12 machinery (cascade_invariant, cascade_step_-    *)
        (* preserves_invariant_pathA, cascade_run_output_nonoverlap) closes  *)
        (* this case CONDITIONAL on cascade_pathA_chain.  For arbitrary      *)
        (* inputs, cascade_pathA_chain is not directly derivable from        *)
        (* nonoverlap_shewchuk e + nonoverlap_shewchuk f + fast_expansion_-  *)
        (* sum_safe.                                                          *)
        (*                                                                    *)
        (* WALL: this is where the proof bails.  Aborting documents the      *)
        (* concrete point where the original deferred-proof obstacle         *)
        (* surfaces.                                                          *)
Abort.

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
Print Assumptions cascade_h_chain_step.
Print Assumptions compress_map_B2R_eq.
Print Assumptions nonoverlap_shewchuk_B2R_compat.
Print Assumptions cascade_step_clause_a_pathA_pos.
Print Assumptions b64_TwoSum_pathA_exact_step_negative.
Print Assumptions cascade_h_chain_pathA_neg.
Print Assumptions cascade_step_clause_a_pathA_neg.
Print Assumptions cascade_step_clause_a_pathA.
Print Assumptions cs_carry_cascade_step_state.
Print Assumptions cs_output_cascade_step_state.
Print Assumptions cascade_step_preserves_invariant_pathA.
Print Assumptions untag_cons_pair.
Print Assumptions cascade_run_cs_carry.
Print Assumptions cascade_run_cs_output.
Print Assumptions cascade_run_preserves_invariant_under_pathA.
Print Assumptions cascade_run_output_nonoverlap.
Print Assumptions compress_all_zero_nil.
Print Assumptions nonoverlap_shewchuk_first_then_zeros.
Print Assumptions b64_TwoSum_snd_B2R_zero_under_int_exact.
Print Assumptions fast_expansion_sum_nonoverlap_shewchuk_int_safe_singletons.
Print Assumptions nonoverlap_shewchuk_pair.
Print Assumptions fast_expansion_sum_nonoverlap_shewchuk_two_singletons.
