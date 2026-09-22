(* ============================================================================
   NetTopologySuite.Proofs.HostRhoLeftoverBagTerm
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Parks ρ leftover-bag term
   (claimId 0007-rho-leftover-bag-term).

   LeftoverBagTermArm =
     leftover_quad_width_decreases
     ∧ leftover_quad_kiss_arm
     ∧ leftover_quad_share_mint_arm
   (SheetHenCookLoop.v). cook_loop_status = LoopObligation.
   cook_loop_status <> LoopDischarged.

   QED would inhabit ALL three conjuncts on leftover quads (not only
   the locked lens, not only the donut) and flip cook_loop_status to
   LoopDischarged with termination + confluence on leftover bags.
   That constructor is still missing.

   QEX (this letter): named missing constructors
     LeftoverWidthDecreases
     LeftoverKissArm
     LeftoverShareMintArm
   stay uninhabited. Do not fake leftover_quad_width_decreases against
   leftover_quad_width_conserved. Do not flip LoopDischarged.

   Sibling QED (cite, do not remint as bag-loop Discharge):
     I.8 pairwise split
       (Adr0007NodingEpic.v : ticket_0007_pairwise_split_qed_or_qex)
     leftover_quad_width_conserved
     donut T5 constant-and-already-noded
       (SheetHenDonutBag.v : ticket_0007_linear_donut_rho_qed_or_qex;
        full-lane only — not imported here)
     circ leftover |H|=2 on the locked lens
       (CircularCookLeftoverTwoHit.v :
        ticket_0007_circ_leftover_two_hit_qed_or_qex)
     modulo iterator / term measure on LStepHit
       (SheetHenCookLoopModulo.v : ticket_0007_rho_modulo_iter_qed_or_qex;
        SheetHenCookLoopTerm.v : ticket_0007_rho_bag_term_measure_qed_or_qex)

   Honesty fences:
     Do not remint I.8 / pairwise as bag-loop Discharge.
     Do not remint leftover_quad_width as a bag-sum measure.
     Do not expand first_cook_scope. Do not remint I_ok_mixed.
     Do not remint CircGamma / ι. Host CircGamma is CircGammaDischarged
     (MkCirc). NURBS / SIN / ellipse / geodesic / Karney / atan2 /
     classic / Category C stay out. Not “ρ closed”, not “noder loop
     done”. ADR-0007 Status stays Accepted.

   WITNESS topic: overlay · claimId: 0007-rho-leftover-bag-term
   witness: 0007-rho-leftover-bag-term
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenCookLoop.
From NTS.Proofs Require Import SheetHenCookLoopModulo SheetHenCookLoopTerm.
From NTS.Proofs Require Import Adr0007NodingEpic.
Local Open Scope R_scope.

(* WITNESS: campaign=rho rung=leftover-bag-term claim=0007-rho-leftover-bag-term
   file=theories/HostRhoLeftoverBagTerm.v
   kind=QEX-named-missing-ctors
   park=LeftoverBagTermArm
   missing=LeftoverWidthDecreases,LeftoverKissArm,LeftoverShareMintArm
   not=LoopDischarged,I.8-bag-Discharge,leftover_quad_width-measure
   not=first-cook-expand,I_ok_mixed,CircGamma-remint,NURBS,SIN,ellipse
   not=geodesic,Karney,atan2,classic,Category-C,rho-closed,noder-loop-done
   sibling=pairwise-I.8,width-conserved,donut-T5,circ-two-hit,modulo-iter,term-measure
   note=letter-not-rho-discharge *)

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. Not bools. Inhabitance is the SheetHenCookLoop *)
(* conjunct; each is already shown uninhabited there.                         *)
(* -------------------------------------------------------------------------- *)

Inductive LeftoverBagTermCtor : Type :=
| LeftoverWidthDecreases
| LeftoverKissArm
| LeftoverShareMintArm.

Definition leftover_bag_term_ctor_inhabits (c : LeftoverBagTermCtor) : Prop :=
  match c with
  | LeftoverWidthDecreases => leftover_quad_width_decreases
  | LeftoverKissArm => leftover_quad_kiss_arm
  | LeftoverShareMintArm => leftover_quad_share_mint_arm
  end.

Lemma leftover_width_decreases_missing :
  ~ leftover_bag_term_ctor_inhabits LeftoverWidthDecreases.
Proof.
  exact leftover_quad_width_does_not_decrease.
Qed.

Lemma leftover_kiss_arm_missing :
  ~ leftover_bag_term_ctor_inhabits LeftoverKissArm.
Proof.
  exact leftover_quad_kiss_arm_missing.
Qed.

Lemma leftover_share_mint_arm_missing :
  ~ leftover_bag_term_ctor_inhabits LeftoverShareMintArm.
Proof.
  exact leftover_quad_share_mint_arm_missing.
Qed.

Lemma leftover_bag_term_ctors_uninhabited :
  ~ leftover_bag_term_ctor_inhabits LeftoverWidthDecreases
  /\ ~ leftover_bag_term_ctor_inhabits LeftoverKissArm
  /\ ~ leftover_bag_term_ctor_inhabits LeftoverShareMintArm
  /\ ~ leftover_bag_term_arm
  /\ LeftoverBagTermArm = leftover_bag_term_arm
  /\ leftover_bag_term_arm =
       (leftover_quad_width_decreases
        /\ leftover_quad_kiss_arm
        /\ leftover_quad_share_mint_arm).
Proof.
  split; [exact leftover_width_decreases_missing|].
  split; [exact leftover_kiss_arm_missing|].
  split; [exact leftover_share_mint_arm_missing|].
  split; [exact leftover_bag_term_arm_missing|].
  split; [reflexivity|].
  reflexivity.
Qed.

Lemma leftover_bag_term_loop_unchanged :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged
  /\ ~ cook_loop_ctor_inhabits CookLoopBagTerm.
Proof.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  exact cook_loop_bag_term_missing.
Qed.

Lemma leftover_bag_term_scope_unchanged :
  first_cook_scope EggChord EggChord
  /\ first_cook_scope EggNurbs EggNurbs
  /\ cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact nurbs_nurbs_first_cook_scope|].
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

(* -------------------------------------------------------------------------- *)
(* Sibling QED cites — packaging, not bag-loop Discharge.                     *)
(* -------------------------------------------------------------------------- *)

Lemma sibling_i8_pairwise_not_bag_discharge :
  (interior_split_finite /\ split_step_confluent_holds)
  /\ cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  destruct ticket_0007_pairwise_split_qed_or_qex as [H | Hfail].
  - split; [exact H|].
    split; [exact cook_loop_is_obligation|].
    exact cook_loop_not_discharged.
  - exfalso. apply Hfail. exact interior_split_finite_holds.
Qed.

Lemma sibling_leftover_quad_width_conserved_not_measure :
  (forall ti tj,
     0 < ti < 1 ->
     0 < tj < 1 ->
     leftover_quad_width ti tj =
     leftover_width 0 1 + leftover_width 0 1)
  /\ ~ leftover_quad_width_decreases
  /\ ~ leftover_bag_term_ctor_inhabits LeftoverWidthDecreases.
Proof.
  split; [exact leftover_quad_width_conserved|].
  split; [exact leftover_quad_width_does_not_decrease|].
  exact leftover_width_decreases_missing.
Qed.

Lemma sibling_modulo_iter_not_bag_discharge :
  leftover_bag_cook_fuel 1 locked_parent_bag locked_quad_bag
  /\ leftover_pair_step_ok locked_parent_bag 0 1
       cross_pt (1 / 2) (1 / 2)
  /\ leftover_bag_cook_fuel 1 locked_quad_bag locked_quad_bag
  /\ cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  destruct ticket_0007_rho_modulo_iter_qed_or_qex as [H | Hdis].
  - destruct H as [_ [Hnstep [Hok [Hdec [_ [_ [Hob Hnd]]]]]]].
    split; [exact Hnstep|].
    split; [exact Hok|].
    split; [exact Hdec|].
    split; [exact Hob|].
    exact Hnd.
  - exfalso. exact (cook_loop_not_discharged Hdis).
Qed.

Lemma sibling_term_measure_not_bag_discharge :
  leftover_bag_term_measure locked_parent_bag 1
  /\ leftover_bag_term_measure locked_quad_bag 0
  /\ leftover_bag_step locked_parent_bag locked_quad_bag
  /\ leftover_bag_step locked_quad_bag locked_quad_bag
  /\ cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged
  /\ ~ leftover_quad_width_decreases.
Proof.
  destruct ticket_0007_rho_bag_term_measure_qed_or_qex as [H | Hdec].
  - destruct H as [Hp [Hq [Hhit [_ [_ [Hidle [_ [_ [_ _]]]]]]]]].
    split; [exact Hp|].
    split; [exact Hq|].
    split; [exact Hhit|].
    split; [exact Hidle|].
    split; [exact cook_loop_is_obligation|].
    split; [exact cook_loop_not_discharged|].
    exact leftover_quad_width_does_not_decrease.
  - exfalso. exact (leftover_quad_width_does_not_decrease Hdec).
Qed.

(* Circ leftover |H|=2 (CircularCookLeftoverTwoHit.v :
   ticket_0007_circ_leftover_two_hit_qed_or_qex) is locked-lens QED.
   Not imported: that module is a 2195-line monolith; a Require would
   trip the module-split gate. It does not inhabit LeftoverBagTermArm. *)
(* Donut T5 (SheetHenDonutBag.v : ticket_0007_linear_donut_rho_qed_or_qex)
   is constant-and-already-noded on that bag. Full-lane only; not imported.
   It does not inhabit LeftoverBagTermArm. The host park is the same hole. *)
Lemma sibling_circ_two_hit_and_donut_t5_not_bag_discharge :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged
  /\ ~ leftover_bag_term_arm.
Proof.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  exact leftover_bag_term_arm_missing.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stop.                                               *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-rho-leftover-bag-term","topic":"overlay","lemma":"ticket_0007_rho_leftover_qed_or_qex","title":"rho leftover-bag term: LeftoverWidthDecreases LeftoverKissArm LeftoverShareMintArm inhabit leftover_quad_width_decreases kiss/share/mint leftover-quad rewrites and cook_loop is LoopDischarged (QED) or those ctors stay missing leftover_quad width is conserved and cook_loop stays LoopObligation (QEX); discharged QEX; sibling I.8 / term-measure / modulo-iter / circ |H|=2 / donut T5 are not bag Discharge","file":"theories/HostRhoLeftoverBagTerm.v","witness":"0007-rho-leftover-bag-term","board":"ADR-0007"} *)
Theorem ticket_0007_rho_leftover_qed_or_qex :
  (leftover_bag_term_ctor_inhabits LeftoverWidthDecreases
   /\ leftover_bag_term_ctor_inhabits LeftoverKissArm
   /\ leftover_bag_term_ctor_inhabits LeftoverShareMintArm
   /\ leftover_bag_term_arm
   /\ cook_loop_status = LoopDischarged)
  \/
  (cook_loop_status = LoopObligation
   /\ cook_loop_status <> LoopDischarged
   /\ ~ leftover_bag_term_arm
   /\ LeftoverBagTermArm = leftover_bag_term_arm
   /\ leftover_bag_term_arm =
        (leftover_quad_width_decreases
         /\ leftover_quad_kiss_arm
         /\ leftover_quad_share_mint_arm)
   /\ ~ leftover_bag_term_ctor_inhabits LeftoverWidthDecreases
   /\ ~ leftover_bag_term_ctor_inhabits LeftoverKissArm
   /\ ~ leftover_bag_term_ctor_inhabits LeftoverShareMintArm
   /\ ~ leftover_quad_width_decreases
   /\ ~ leftover_quad_kiss_arm
   /\ ~ leftover_quad_share_mint_arm
   /\ ~ cook_loop_ctor_inhabits CookLoopBagTerm
   /\ (forall ti tj,
         0 < ti < 1 ->
         0 < tj < 1 ->
         leftover_quad_width ti tj =
         leftover_width 0 1 + leftover_width 0 1)
   /\ interior_split_finite
   /\ split_step_confluent_holds
   /\ first_cook_scope EggChord EggChord
   /\ first_cook_scope EggNurbs EggNurbs).
Proof.
  right.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact leftover_bag_term_arm_missing|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact leftover_width_decreases_missing|].
  split; [exact leftover_kiss_arm_missing|].
  split; [exact leftover_share_mint_arm_missing|].
  split; [exact leftover_quad_width_does_not_decrease|].
  split; [exact leftover_quad_kiss_arm_missing|].
  split; [exact leftover_quad_share_mint_arm_missing|].
  split; [exact cook_loop_bag_term_missing|].
  split; [exact leftover_quad_width_conserved|].
  split; [exact interior_split_finite_holds|].
  split; [exact split_step_confluent_holds_proof|].
  split; [exact first_cook_scope_chord_chord|].
  exact nurbs_nurbs_first_cook_scope.
Qed.

Print Assumptions leftover_width_decreases_missing.
Print Assumptions leftover_kiss_arm_missing.
Print Assumptions leftover_share_mint_arm_missing.
Print Assumptions leftover_bag_term_ctors_uninhabited.
Print Assumptions leftover_bag_term_loop_unchanged.
Print Assumptions leftover_bag_term_scope_unchanged.
Print Assumptions sibling_i8_pairwise_not_bag_discharge.
Print Assumptions sibling_leftover_quad_width_conserved_not_measure.
Print Assumptions sibling_modulo_iter_not_bag_discharge.
Print Assumptions sibling_term_measure_not_bag_discharge.
Print Assumptions sibling_circ_two_hit_and_donut_t5_not_bag_discharge.
Print Assumptions ticket_0007_rho_leftover_qed_or_qex.
