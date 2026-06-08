(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Shewchuk_Thm13_pathAB
   ----------------------------------------------------------------------------
   Shewchuk Theorem 13, pathA ∨ pathB cascade scaffolding (P2).

   DEFS: widened handover, pathB trigger, pathAB chain (plan §2).
   O1–O6: all Qed; O7 beachhead + bootstrap; O8 conditional headline.

   See docs/history/sessions/shewchuk-thm13-4A-verify-outcome.md (§4.A decision)
   and origin/claude/shewchuk-thm13-obligations (O2–O7 prompts).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lra Lia List.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core Sterbenz.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
                                     B64_Expansion B64_Expansion_Shewchuk
                                     B64_Pff_bridge B64_FastExpansionSum
                                     B64_FastExpansionSum_Shewchuk
                                     B64_FastExpansionSum_Shewchuk_Route2
                                     B64_TwoSum_sterbenz B64_residue_granularity
                                     B64_nonoverlap_head.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* DEFS — plan §2 (compile-clean).                                            *)
(* -------------------------------------------------------------------------- *)

(* pathB fires when the exact sum is representable (Sterbenz is a sufficient   *)
(* discharge; this is the hypothesis of b64_TwoSum_exact_of_format_sum).      *)
Definition cascade_step_pathB (state : cascade_state) (x : binary64) : Prop :=
  let q := cs_carry state in
  b64_TwoSum_safe x q /\
  b64_format (Binary.B2R prec emax x + Binary.B2R prec emax q).

(* The five pathA disjuncts from cascade_invariant_handover (Route2 L348–357). *)
Definition cascade_invariant_handover_pathA_disj (qR xR : R) : Prop :=
  (0 < qR /\ 0 < xR)
  \/ (qR < 0 /\ xR < 0)
  \/ qR = 0
  \/ (0 < xR /\ Rabs qR <
        ulp radix2 (SpecFloat.fexp prec emax)
          (pred radix2 (SpecFloat.fexp prec emax) xR) / 2)
  \/ (xR < 0 /\ Rabs qR <
        ulp radix2 (SpecFloat.fexp prec emax)
          (succ radix2 (SpecFloat.fexp prec emax) xR) / 2).

(* Widened handover: pathA disjunction OR exact-sum (pathB) disjunct.          *)
Definition cascade_invariant_handover_AB
  (state : cascade_state) (remaining : list tagged_b64) : Prop :=
  match remaining with
  | nil => True
  | (x, _) :: _ =>
      let q  := cs_carry state in
      let qR := Binary.B2R prec emax q in
      let xR := Binary.B2R prec emax x in
      b64_TwoSum_safe x q /\
      ( cascade_invariant_handover_pathA_disj qR xR
        \/ b64_format (xR + qR) )
  end.

(* Within-source + normal-range conjuncts shared by pathA and pathB steps
   (Route2 L1530–1545 / run_bound_step_preserves). *)
Definition cascade_step_run_bound_inputs
  (state : cascade_state) (x : binary64) (prov : provenance) : Prop :=
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
    Rabs (Binary.B2R prec emax (b64_plus x (cs_carry state))).

(* PathA dominance disjunct (strict_succ / neg half-ulp), without run-bound. *)
Definition cascade_step_pathA_dominance
  (state : cascade_state) (x : binary64) : Prop :=
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
          (Binary.B2R prec emax x)) / 2)).

(* PathA step hypotheses extracted from cascade_pathA_chain (Route2 L1519–1545). *)
Definition cascade_step_pathA_conditions
  (state : cascade_state) (x : binary64) (prov : provenance) : Prop :=
  cascade_step_pathA_dominance state x /\
  cascade_step_run_bound_inputs state x prov.

(* Resolution-1-extended emission bound (plan §4.A). *)
Definition pathB_output_head_bound
  (state : cascade_state) (x : binary64) : Prop :=
  forall (h : binary64) (ts : list binary64),
    compress (rev (cs_output state)) = h :: ts ->
    Rabs (Binary.B2R prec emax h) <=
      ulp radix2 (SpecFloat.fexp prec emax)
        (Binary.B2R prec emax (fst (b64_TwoSum x (cs_carry state)))) / 2.

(* Extra pathB hypotheses for O1 (§4.A resolution-1-extended). *)
Definition cascade_step_pathB_side_conditions
  (state : cascade_state) (x : binary64) : Prop :=
  pathB_output_head_bound state x /\
  Binary.B2R prec emax (cs_carry state) <> 0 /\
  Rabs (Binary.B2R prec emax (cs_carry state)) / 2
    <= Rabs (Binary.B2R prec emax x).

(* Full invariant with widened handover (clause (a) + AB-handover + run-bound). *)
Definition cascade_invariant_AB
  (state : cascade_state)
  (_processed : list binary64)
  (remaining : list tagged_b64)
  : Prop :=
  cascade_invariant_output (cs_carry state) (cs_output state) /\
  cascade_invariant_handover_AB state remaining /\
  cascade_invariant_run_bound state.

Fixpoint cascade_pathAB_chain
  (state : cascade_state) (xs : list tagged_b64) : Prop :=
  match xs with
  | nil => True
  | (x, prov) :: rest =>
      cascade_step_run_bound_inputs state x prov /\
      ( cascade_step_pathA_dominance state x
        \/ cascade_step_pathB state x ) /\
      ( cascade_step_pathB state x ->
          cascade_step_pathB_side_conditions state x ) /\
      cascade_invariant_handover_AB (cascade_step_state state x prov) rest /\
      cascade_pathAB_chain (cascade_step_state state x prov) rest
  end.

(* -------------------------------------------------------------------------- *)
(* O1 helpers — exact TwoSum (#135) + list head surgery (#137) + O1′ (#136).  *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_step_pathB_twosum_exact :
  forall (state : cascade_state) (x : binary64) (carry' err : binary64),
    cascade_step_pathB state x ->
    b64_TwoSum x (cs_carry state) = (carry', err) ->
    Binary.B2R prec emax carry' =
      Binary.B2R prec emax x + Binary.B2R prec emax (cs_carry state) /\
    Binary.B2R prec emax err = 0.
Proof.
  intros state x carry' err [Hsafe Hfmt] Hts.
  assert (H := b64_TwoSum_exact_of_format_sum x (cs_carry state) Hsafe Hfmt).
  rewrite Hts in H. cbn in H. destruct H as [Hcarry Herr]. split; assumption.
Qed.

(* When the cancellation residue is zero, clause (a) follows from cons_zero +
   head_replace with B2R carry' = 0 (Traces A/B). *)
Lemma cascade_step_pathB_preserves_output_zero_residue :
  forall (state : cascade_state) (x : binary64) (prov : provenance),
    cascade_invariant_output (cs_carry state) (cs_output state) ->
    cascade_step_pathB state x ->
    Binary.B2R prec emax x + Binary.B2R prec emax (cs_carry state) = 0 ->
    cascade_invariant_output
      (cs_carry (cascade_step_state state x prov))
      (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]).
Proof.
  intros state x prov Hout Hpath Hzero.
  destruct (b64_TwoSum x (cs_carry state)) as [carry' err] eqn:Hts.
  pose proof (cascade_step_pathB_twosum_exact state x carry' err Hpath Hts)
    as [Hcarry' Herr].
  rewrite Hzero in Hcarry'.
  unfold cascade_invariant_output in *.
  rewrite cs_carry_cascade_step_state.
  rewrite rev_app_distr.
  assert (Hsnd : snd (b64_TwoSum x (cs_carry state)) = err).
  { rewrite Hts. reflexivity. }
  replace (snd (b64_TwoSum x (cs_carry state))) with err.
  pattern (fst (b64_TwoSum x (cs_carry state))).
  rewrite Hts. simpl.
  assert (Hout' : nonoverlap_shewchuk
                    (cs_carry state :: err :: rev (cs_output state))).
  { rewrite (nonoverlap_shewchuk_cons_zero (cs_carry state) err
               (rev (cs_output state)) Herr). exact Hout. }
  apply (nonoverlap_shewchuk_head_replace (cs_carry state) carry'
           (err :: rev (cs_output state))).
  - exact Hout'.
  - left. rewrite Hcarry'. reflexivity.
Qed.

(* When compress(rev output) = nil, head_replace's empty-tail disjunct fires
   (Trace A empty-output regime). *)
Lemma cascade_step_pathB_preserves_output_nil_compress :
  forall (state : cascade_state) (x : binary64) (prov : provenance),
    cascade_invariant_output (cs_carry state) (cs_output state) ->
    cascade_step_pathB state x ->
    compress (rev (cs_output state)) = nil ->
    cascade_invariant_output
      (cs_carry (cascade_step_state state x prov))
      (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]).
Proof.
  intros state x prov Hout Hpath Hnil.
  destruct (b64_TwoSum x (cs_carry state)) as [carry' err] eqn:Hts.
  pose proof (cascade_step_pathB_twosum_exact state x carry' err Hpath Hts) as [_ Herr].
  unfold cascade_invariant_output in *.
  rewrite cs_carry_cascade_step_state.
  rewrite rev_app_distr.
  assert (Hsnd : snd (b64_TwoSum x (cs_carry state)) = err).
  { rewrite Hts. reflexivity. }
  replace (snd (b64_TwoSum x (cs_carry state))) with err.
  pattern (fst (b64_TwoSum x (cs_carry state))).
  rewrite Hts. simpl.
  assert (Hout' : nonoverlap_shewchuk
                    (cs_carry state :: err :: rev (cs_output state))).
  { rewrite (nonoverlap_shewchuk_cons_zero (cs_carry state) err
               (rev (cs_output state)) Herr). exact Hout. }
  apply (nonoverlap_shewchuk_head_replace (cs_carry state) carry'
           (err :: rev (cs_output state))).
  - exact Hout'.
  - right.
    destruct (compress (err :: rev (cs_output state))) eqn:Hc.
    + exact I.
    + exfalso.
      cbn [compress] in Hc.
      rewrite (Rcompare_Eq (Binary.B2R prec emax err) 0 Herr) in Hc.
      rewrite Hnil in Hc. discriminate.
Qed.

Lemma cascade_step_pathB_preserves_output :
  forall (state : cascade_state) (x : binary64) (prov : provenance),
    cascade_invariant_output (cs_carry state) (cs_output state) ->
    cascade_step_pathB state x ->
    pathB_output_head_bound state x ->
    Binary.B2R prec emax (cs_carry state) <> 0 ->
    Rabs (Binary.B2R prec emax (cs_carry state)) / 2
      <= Rabs (Binary.B2R prec emax x) ->
    cascade_invariant_output
      (cs_carry (cascade_step_state state x prov))
      (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]).
Proof.
  intros state x prov Hout Hpath Hhead Hq0 Hster.
  destruct (Rcompare (Binary.B2R prec emax x + Binary.B2R prec emax (cs_carry state)) 0)
    eqn:Hsum.
  - apply Rcompare_Eq_inv in Hsum.
    apply cascade_step_pathB_preserves_output_zero_residue; assumption.
  - assert (Hsum0 : Binary.B2R prec emax x + Binary.B2R prec emax (cs_carry state) <> 0).
    { intro H0. apply Rcompare_Lt_inv in Hsum. lra. }
    destruct (compress (rev (cs_output state))) as [|h ts] eqn:Hc.
    + apply cascade_step_pathB_preserves_output_nil_compress; assumption.
    + destruct (b64_TwoSum x (cs_carry state)) as [carry' err] eqn:Hts.
      pose proof (compress_head_nonzero (rev (cs_output state)) h ts Hc) as Hh0.
      pose proof (cascade_step_pathB_twosum_exact state x carry' err Hpath Hts)
        as [Hcarry' Herr].
      pose proof (nonoverlap_output_first_strict_succ
                    (cs_carry state) (cs_output state) h ts Hout Hc Hq0 Hh0) as Hqh.
      pose proof (Hhead h ts Hc) as Hhead'.
      unfold cascade_invariant_output in *.
      rewrite cs_carry_cascade_step_state.
      rewrite rev_app_distr.
      assert (Hsnd : snd (b64_TwoSum x (cs_carry state)) = err).
      { rewrite Hts. reflexivity. }
      replace (snd (b64_TwoSum x (cs_carry state))) with err.
      pattern (fst (b64_TwoSum x (cs_carry state))).
      rewrite Hts. simpl.
      assert (Hout' : nonoverlap_shewchuk
                        (cs_carry state :: err :: rev (cs_output state))).
      { rewrite (nonoverlap_shewchuk_cons_zero (cs_carry state) err
                   (rev (cs_output state)) Herr). exact Hout. }
      apply (nonoverlap_shewchuk_head_replace (cs_carry state) carry'
               (err :: rev (cs_output state))).
      * exact Hout'.
      * right.
        cbn [compress].
        rewrite (Rcompare_Eq (Binary.B2R prec emax err) 0 Herr).
        rewrite Hc.
        unfold strict_succ_b64.
        rewrite Hts in Hhead'. simpl fst in Hhead'.
        exact Hhead'.
  - assert (Hsum0 : Binary.B2R prec emax x + Binary.B2R prec emax (cs_carry state) <> 0).
    { intro H0. apply Rcompare_Gt_inv in Hsum. lra. }
    destruct (compress (rev (cs_output state))) as [|h ts] eqn:Hc.
    + apply cascade_step_pathB_preserves_output_nil_compress; assumption.
    + destruct (b64_TwoSum x (cs_carry state)) as [carry' err] eqn:Hts.
      pose proof (compress_head_nonzero (rev (cs_output state)) h ts Hc) as Hh0.
      pose proof (cascade_step_pathB_twosum_exact state x carry' err Hpath Hts)
        as [Hcarry' Herr].
      pose proof (nonoverlap_output_first_strict_succ
                    (cs_carry state) (cs_output state) h ts Hout Hc Hq0 Hh0) as Hqh.
      pose proof (Hhead h ts Hc) as Hhead'.
      unfold cascade_invariant_output in *.
      rewrite cs_carry_cascade_step_state.
      rewrite rev_app_distr.
      assert (Hsnd : snd (b64_TwoSum x (cs_carry state)) = err).
      { rewrite Hts. reflexivity. }
      replace (snd (b64_TwoSum x (cs_carry state))) with err.
      pattern (fst (b64_TwoSum x (cs_carry state))).
      rewrite Hts. simpl.
      assert (Hout' : nonoverlap_shewchuk
                        (cs_carry state :: err :: rev (cs_output state))).
      { rewrite (nonoverlap_shewchuk_cons_zero (cs_carry state) err
                   (rev (cs_output state)) Herr). exact Hout. }
      apply (nonoverlap_shewchuk_head_replace (cs_carry state) carry'
               (err :: rev (cs_output state))).
      * exact Hout'.
      * right.
        cbn [compress].
        rewrite (Rcompare_Eq (Binary.B2R prec emax err) 0 Herr).
        rewrite Hc.
        unfold strict_succ_b64.
        rewrite Hts in Hhead'. simpl fst in Hhead'.
        exact Hhead'.
Qed.

(* -------------------------------------------------------------------------- *)
(* O2 — pathB preserves AB-handover (half-ulp absorption beachhead).            *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_step_pathB_preserves_handover_next_pathB :
  forall (state : cascade_state) (x : binary64) (prov : provenance)
         (x' : binary64) (prov' : provenance) (rest' : list tagged_b64),
    cascade_invariant_handover_AB state ((x, prov) :: (x', prov') :: rest') ->
    cascade_step_pathB state x ->
    cascade_step_pathB (cascade_step_state state x prov) x' ->
    cascade_invariant_handover_AB
      (cascade_step_state state x prov) ((x', prov') :: rest').
Proof.
  intros state x prov x' prov' rest' _ _ [Hsafe' Hfmt'].
  unfold cascade_invariant_handover_AB, cascade_step_state. cbn.
  split; [exact Hsafe' | right; exact Hfmt'].
Qed.

Lemma cascade_step_pathB_preserves_handover :
  forall (state : cascade_state) (x : binary64) (prov : provenance)
         (rest : list tagged_b64),
    cascade_invariant_handover_AB state ((x, prov) :: rest) ->
    cascade_step_pathB state x ->
    (rest = nil \/
     (exists (x' : binary64) (prov' : provenance) (rest' : list tagged_b64),
        rest = (x', prov') :: rest' /\
        cascade_step_pathB (cascade_step_state state x prov) x')) ->
    cascade_invariant_handover_AB (cascade_step_state state x prov) rest.
Proof.
  intros state x prov rest Hho Hpath Hcases.
  destruct Hcases as [Hnil | Hex].
  - subst rest. exact I.
  - destruct Hex as [x' [prov' [rest' [Hrest Hnext]]]].
    subst rest.
    apply cascade_step_pathB_preserves_handover_next_pathB; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* O3 — pathB preserves run-bound (mirror Route2 run_bound_absorb_* / L769).  *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_step_pathB_preserves_run_bound :
  forall (state : cascade_state) (x : binary64) (prov : provenance),
    cascade_invariant_run_bound state ->
    cascade_step_pathB state x ->
    b64_safe Rplus x (cs_carry state) ->
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax x) ->
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax (b64_plus x (cs_carry state))) ->
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
     end) ->
    cascade_invariant_run_bound (cascade_step_state state x prov).
Proof.
  intros state x prov Hd HpathB Hsafe Hxn Hpn Hwithin.
  (* Mirror Route2 run_bound_step_preserves (L769): pathB only supplies the
     exact-sum fact; the geometric hypotheses match pathA's chain. *)
  apply run_bound_step_preserves; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* O4 — combined single-step preservation.                                    *)
(* pathA → cascade_step_clause_a_pathA; pathB → O1 (a) + O3 (d);            *)
(* handover_AB on rest is supplied by the chain driver.                         *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_step_preserves_invariant_AB :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov : provenance) (rest : list tagged_b64),
    cascade_invariant_AB state processed ((x, prov) :: rest) ->
    cascade_step_run_bound_inputs state x prov ->
    ( cascade_step_pathA_dominance state x
      \/ cascade_step_pathB state x ) ->
    ( cascade_step_pathB state x ->
        cascade_step_pathB_side_conditions state x ) ->
    cascade_invariant_handover_AB (cascade_step_state state x prov) rest ->
    cascade_invariant_AB (cascade_step_state state x prov)
                        (processed ++ [x]) rest.
Proof.
  intros state processed x prov rest Hinv Hrb Hstep HpathBside Hho_new.
  unfold cascade_invariant_AB in Hinv.
  destruct Hinv as [Hout [Hho_cur Hd]].
  destruct Hho_cur as [Hsafe Hdisj_handover].
  destruct Hrb as [Hwithin [Hxn Hpn]].
  destruct Hstep as [Hdom | HpathB].
  unfold cascade_invariant_AB.
  - (* pathA step. *)
    split.
    + unfold cascade_invariant_output.
      rewrite cs_carry_cascade_step_state, cs_output_cascade_step_state.
      assert (Hinv' : cascade_invariant state processed ((x, prov) :: rest)).
      { unfold cascade_invariant. split; [|split].
        - exact Hout.
        - unfold cascade_invariant_handover. cbn.
          split; [exact Hsafe|].
          destruct Hdom as [_ [_ Hcases]].
          destruct Hcases as [[Hx Hpw] | [Hx Hpw]].
          + right. right. right. left. split; assumption.
          + right. right. right. right. split; assumption.
        - exact Hd. }
      destruct Hdom as [Hxnz [Hcq Hcases]].
      exact (cascade_step_clause_a_pathA state processed x prov rest Hinv'
               Hxnz Hcq Hcases).
    + split.
      * exact Hho_new.
      * destruct Hdom as [_ [Hcq _]].
        destruct Hsafe as [Hsafe_plus _].
        exact (run_bound_step_preserves state x prov Hd Hsafe_plus Hxn Hpn Hwithin).
  - (* pathB step. *)
    destruct (HpathBside HpathB) as [Hhead [Hq0 Hster]].
    split.
    + unfold cascade_invariant_output.
      rewrite cs_output_cascade_step_state.
      exact (cascade_step_pathB_preserves_output state x prov Hout HpathB
               Hhead Hq0 Hster).
    + split.
      * exact Hho_new.
      * destruct HpathB as [Hts Hfmt].
        destruct Hts as [Hsa _].
        assert (HpB : cascade_step_pathB state x) by (split; assumption).
        exact (cascade_step_pathB_preserves_run_bound state x prov Hd HpB Hsa
                 Hxn Hpn Hwithin).
Qed.

(* -------------------------------------------------------------------------- *)
(* O5 — run lift under pathAB (COPY Route2 L1552; call O4 not pathA step).   *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_run_preserves_invariant_under_pathAB :
  forall (xs : list tagged_b64) (state : cascade_state)
         (processed : list binary64),
    cascade_invariant_AB state processed xs ->
    cascade_pathAB_chain state xs ->
    cascade_invariant_AB (cascade_run state xs)
                        (processed ++ untag xs) nil.
Proof.
  induction xs as [|tx xs IH]; intros state processed Hinv Hchain.
  - cbn [cascade_run untag map]. rewrite app_nil_r. exact Hinv.
  - destruct tx as [x prov].
    cbn [cascade_pathAB_chain] in Hchain.
    destruct Hchain as [Hrb [Hstep [HpathBside [Hho_new Hchain']]]].
    cbn [cascade_run].
    rewrite untag_cons_pair.
    change (processed ++ x :: untag xs) with (processed ++ [x] ++ untag xs).
    rewrite app_assoc.
    apply IH.
    + eapply cascade_step_preserves_invariant_AB; eauto.
    + exact Hchain'.
Qed.

(* -------------------------------------------------------------------------- *)
(* O6 — output nonoverlap under pathAB (COPY Route2 L1584; apply O5).        *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_run_output_nonoverlap_AB :
  forall (init_state : cascade_state) (tagged_rest : list tagged_b64),
    cascade_invariant_AB init_state nil tagged_rest ->
    cascade_pathAB_chain init_state tagged_rest ->
    nonoverlap_shewchuk
      (cs_carry (cascade_run init_state tagged_rest)
       :: rev (cs_output (cascade_run init_state tagged_rest))).
Proof.
  intros init_state tagged_rest Hinv Hchain.
  pose proof (cascade_run_preserves_invariant_under_pathAB
                tagged_rest init_state nil Hinv Hchain) as Hfinal.
  unfold cascade_invariant_AB in Hfinal.
  destruct Hfinal as [Ha _].
  unfold cascade_invariant_output in Ha.
  exact Ha.
Qed.

Print Assumptions cascade_step_preserves_invariant_AB.
Print Assumptions cascade_step_pathB_preserves_output.
Print Assumptions cascade_step_pathB_preserves_handover.
Print Assumptions cascade_step_pathB_preserves_run_bound.
Print Assumptions cascade_run_preserves_invariant_under_pathAB.
Print Assumptions cascade_run_output_nonoverlap_AB.

(* -------------------------------------------------------------------------- *)
(* O7 — bootstrap: initial handover_AB + first-step pathB for mixed-sign pair. *)
(* O8 — conditional headline (mirror Route2 L2196 with pathAB chain).         *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_invariant_AB_empty :
  forall (q : binary64) (p : provenance) (remaining : list tagged_b64),
    cascade_invariant_handover_AB (initial_cascade_state q p) remaining ->
    cascade_invariant_AB (initial_cascade_state q p) nil remaining.
Proof.
  intros q p remaining Hho.
  unfold cascade_invariant_AB, initial_cascade_state.
  destruct p; cbn [cs_carry cs_output cs_e_max cs_f_max rev];
    (split; [|split]).
  - unfold cascade_invariant_output. cbn.
    unfold nonoverlap_shewchuk. cbn [compress].
    destruct (Rcompare (Binary.B2R prec emax q) 0);
      cbn [nonoverlap_strict]; exact I.
  - exact Hho.
  - unfold cascade_invariant_run_bound. cbn.
    replace (Binary.B2R prec emax b64_zero) with 0 by exact B2R_b64_zero.
    rewrite Rabs_R0. pose proof (Rabs_pos (Binary.B2R prec emax q)) as Hpos. lra.
  - unfold cascade_invariant_output. cbn.
    unfold nonoverlap_shewchuk. cbn [compress].
    destruct (Rcompare (Binary.B2R prec emax q) 0);
      cbn [nonoverlap_strict]; exact I.
  - exact Hho.
  - unfold cascade_invariant_run_bound. cbn.
    replace (Binary.B2R prec emax b64_zero) with 0 by exact B2R_b64_zero.
    rewrite Rabs_R0. pose proof (Rabs_pos (Binary.B2R prec emax q)) as Hpos. lra.
Qed.

(* The e=[1], f=[-1] bootstrap: first step is pathB (Sterbenz), not pathA. *)
Lemma cascade_pathAB_chain_two_singletons_mixed_sign :
  forall (x x2 : binary64) (prov p2 : provenance),
    0 < Binary.B2R prec emax x ->
    Binary.B2R prec emax x2 < 0 ->
    Rabs (Binary.B2R prec emax x) <= Rabs (Binary.B2R prec emax x2)
      <= 2 * Rabs (Binary.B2R prec emax x) ->
    not_half_ulp_separated_carry_next
      (Binary.B2R prec emax x) (Binary.B2R prec emax x2) ->
    b64_TwoSum_safe x2 x ->
    cascade_step_run_bound_inputs (initial_cascade_state x prov) x2 p2 ->
    cascade_pathAB_chain (initial_cascade_state x prov) [(x2, p2)].
Proof.
  intros x x2 prov p2 Hx_pos Hx2_neg Hmag Hnsep Hsafe Hrb.
  pose proof (not_half_ulp_separated_implies_sterbenz x x2
                Hx_pos Hx2_neg Hmag Hnsep) as Hster.
  destruct Hster as [_ [_ [Hlo Hhi]]].
  pose proof (b64_format_sterbenz_pos_neg x x2 Hx_pos Hx2_neg (conj Hlo Hhi))
    as Hfmt.
  assert (HpathB : cascade_step_pathB (initial_cascade_state x prov) x2).
  { destruct prov.
    - cbn [initial_cascade_state cs_carry]. unfold cascade_step_pathB.
      split; [exact Hsafe | rewrite Rplus_comm; exact Hfmt].
    - cbn [initial_cascade_state cs_carry]. unfold cascade_step_pathB.
      split; [exact Hsafe | rewrite Rplus_comm; exact Hfmt]. }
  assert (Hside :
    cascade_step_pathB_side_conditions (initial_cascade_state x prov) x2).
  { destruct prov.
    - cbn [initial_cascade_state cs_carry cs_output].
      unfold cascade_step_pathB_side_conditions, pathB_output_head_bound.
      repeat split.
      + intros h ts Hc. cbn [rev compress] in Hc. discriminate Hc.
      + cbn. intro Heq. apply Rlt_not_eq in Hx_pos. lra.
      + destruct Hmag as [Hle _]. cbn.
        assert (Hxabs : Rabs (Binary.B2R prec emax x) = Binary.B2R prec emax x)
          by (apply Rabs_pos_eq; lra).
        assert (Hx2abs : Rabs (Binary.B2R prec emax x2) = - Binary.B2R prec emax x2)
          by (apply Rabs_left; lra).
        rewrite Hxabs, Hx2abs. lra.
    - cbn [initial_cascade_state cs_carry cs_output].
      unfold cascade_step_pathB_side_conditions, pathB_output_head_bound.
      repeat split.
      + intros h ts Hc. cbn [rev compress] in Hc. discriminate Hc.
      + cbn. intro Heq. apply Rlt_not_eq in Hx_pos. lra.
      + destruct Hmag as [Hle _]. cbn.
        assert (Hxabs : Rabs (Binary.B2R prec emax x) = Binary.B2R prec emax x)
          by (apply Rabs_pos_eq; lra).
        assert (Hx2abs : Rabs (Binary.B2R prec emax x2) = - Binary.B2R prec emax x2)
          by (apply Rabs_left; lra).
        rewrite Hxabs, Hx2abs. lra. }
  unfold cascade_pathAB_chain.
  split; [exact Hrb |].
  split; [right; exact HpathB |].
  split; [intros _; exact Hside |].
  split; [exact I | exact I].
Qed.

(* General completeness: derive cascade_pathAB_chain from nonoverlap inputs.
   Thesis-scale per-step case analysis; registered deferred until landed. *)
Lemma cascade_pathAB_chain_from_nonoverlap :
  forall (e f : list binary64),
    fast_expansion_sum_safe e f ->
    nonoverlap_shewchuk e ->
    nonoverlap_shewchuk f ->
    match tagged_input e f with
    | nil => True
    | (x, prov) :: rest =>
        cascade_invariant_handover_AB (initial_cascade_state x prov) rest /\
        cascade_pathAB_chain (initial_cascade_state x prov) rest
    end.
Proof.
  (* O7 remainder: per-step provenance + magnitude bookkeeping (thesis-scale).
     Bootstrap lemmas above + pathC_carry_next_gap_false_similar_magnitude
     discharge the mixed-sign similar-magnitude first step; full induction
     on tagged_input is the deferred-proof obstacle for the general headline. *)
Admitted.

Theorem fast_expansion_sum_nonoverlap_shewchuk_pathAB_conditional :
  forall (e f : list binary64),
    fast_expansion_sum_safe e f ->
    (match tagged_input e f with
     | nil => True
     | (x, prov) :: rest =>
         cascade_invariant_handover_AB (initial_cascade_state x prov) rest /\
         cascade_pathAB_chain (initial_cascade_state x prov) rest
     end) ->
    nonoverlap_shewchuk (fast_expansion_sum e f).
Proof.
  intros e f Hsafe Hcond.
  destruct (tagged_input e f) as [|p rest] eqn:Htagged.
  - unfold fast_expansion_sum.
    pose proof (untag_tagged_input e f) as Huntag.
    rewrite Htagged in Huntag. cbn [untag map] in Huntag.
    rewrite <- Huntag.
    unfold nonoverlap_shewchuk. cbn [compress nonoverlap_strict]. exact I.
  - destruct p as [x prov]. destruct Hcond as [Hho Hchain].
    rewrite (fast_expansion_sum_via_cascade_run e f x prov rest Htagged).
    apply cascade_run_output_nonoverlap_AB.
    + apply cascade_invariant_AB_empty. exact Hho.
    + exact Hchain.
Qed.

Print Assumptions cascade_invariant_AB_empty.
Print Assumptions cascade_pathAB_chain_two_singletons_mixed_sign.
Print Assumptions fast_expansion_sum_nonoverlap_shewchuk_pathAB_conditional.