(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Shewchuk_Thm13_pathAB
   ----------------------------------------------------------------------------
   Shewchuk Theorem 13, pathA ∨ pathB cascade scaffolding (P2).

   DEFS: widened handover, pathB trigger, pathAB chain (plan §2).
   O3–O6: preservation lemmas — O3 Qed; O4 deferred (needs O1/O2); O5/O6
   mechanical copies of Route2 L1552/L1584 calling O4.

   See docs/history/sessions/shewchuk-thm13-4A-verify-outcome.md (§4.A decision)
   and origin/claude/shewchuk-thm13-obligations (O2–O7 prompts).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lra Lia List.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
                                     B64_Expansion B64_Expansion_Shewchuk
                                     B64_Pff_bridge B64_FastExpansionSum
                                     B64_FastExpansionSum_Shewchuk
                                     B64_FastExpansionSum_Shewchuk_Route2
                                     B64_TwoSum_sterbenz.
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

(* PathA step hypotheses extracted from cascade_pathA_chain (Route2 L1519–1545). *)
Definition cascade_step_pathA_conditions
  (state : cascade_state) (x : binary64) (prov : provenance) : Prop :=
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
    Rabs (Binary.B2R prec emax (b64_plus x (cs_carry state))).

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
      ( cascade_step_pathA_conditions state x prov
        \/ cascade_step_pathB state x ) /\
      cascade_invariant_handover_AB (cascade_step_state state x prov) rest /\
      cascade_pathAB_chain (cascade_step_state state x prov) rest
  end.

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
(* O4 — combined single-step preservation (deferred: needs O1 ∧ O2).          *)
(* COPY tactic: destruct pathA ∨ pathB; pathA →                              *)
(*   cascade_step_preserves_invariant_pathA (Route2 L1360);                    *)
(* pathB → split cascade_invariant_AB; O1 (a), O2 (handover_AB), O3 (d).    *)
(* -------------------------------------------------------------------------- *)

Lemma cascade_step_preserves_invariant_AB :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov : provenance) (rest : list tagged_b64),
    cascade_invariant_AB state processed ((x, prov) :: rest) ->
    ( cascade_step_pathA_conditions state x prov
      \/ cascade_step_pathB state x ) ->
    cascade_invariant_handover_AB (cascade_step_state state x prov) rest ->
    cascade_invariant_AB (cascade_step_state state x prov)
                        (processed ++ [x]) rest.
Proof.
Admitted.

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
    destruct Hchain as [Hstep [Hho_new Hchain']].
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

Print Assumptions cascade_step_pathB_preserves_run_bound.
Print Assumptions cascade_run_output_nonoverlap_AB.