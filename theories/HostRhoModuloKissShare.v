(* ============================================================================
   NetTopologySuite.Proofs.HostRhoModuloKissShare
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Parks ρ modulo kiss / share-mint
   (claimId 0007-rho-modulo-kiss-share).

   leftover_bag_step has LStepHit and LStepDecline only.
   Fuel 1 Hit-splits the locked parent under leftover_pair_step_ok
   (SheetHenCookLoopModulo.v : ticket_0007_rho_modulo_iter_qed_or_qex).
   Decline on a leftover-quad join pair leaves the bag.
   Kiss and share-mint are not leftover_bag_step constructors.

   QED would add leftover_pair_kiss_ok and leftover_pair_share_mint_ok
   as leftover_bag_step constructors leftover_bag_cook_fuel can
   consume on leftover quads, keep cook_loop_status = LoopObligation,
   and leave leftover_quad_width_decreases uninhabited. That needs a
   third leftover_bag_step constructor and leftover_quad_kiss_arm /
   leftover_quad_share_mint_arm. Wiring kiss/share-mint as Hit or
   Decline remints I.8 / pretends leftover_quad_width_decreases.

   QEX (this letter): named missing constructors
     ModuloKissStep
     ModuloShareMintStep
   stay uninhabited. leftover_pair_kiss_ok / leftover_pair_share_mint_ok
   stay missing. Do not fake leftover_quad_width_decreases. Do not
   flip LoopDischarged. Do not remint LeftoverBagTermArm.

   Sibling QED / sibling QEX (cite, do not remint as bag-loop Discharge):
     modulo iterator Hit-split + Decline idle
       (SheetHenCookLoopModulo.v : ticket_0007_rho_modulo_iter_qed_or_qex)
     #797 leftover-bag term named holes
       (HostRhoLeftoverBagTerm.v : LeftoverKissArm / LeftoverShareMintArm;
        ticket_0007_rho_leftover_qed_or_qex)

   Honesty fences:
     Do not remint LeftoverKissArm / LeftoverShareMintArm as inhabited
     without the Loop conjuncts. Do not remint LeftoverBagTermArm.
     Do not remint I.8 / pairwise as bag-loop Discharge.
     Do not remint leftover_quad_width as a bag-sum measure.
     Do not expand first_cook_scope. Do not remint I_ok_mixed.
     Do not remint CircGamma / ι. Host CircGamma is CircGammaDischarged
     (MkCirc). NURBS / SIN / ellipse / geodesic / Karney / atan2 /
     classic / Category C stay out. Not “ρ closed”, not “noder loop
     done”. ADR-0007 Status stays Accepted.

   WITNESS topic: overlay · claimId: 0007-rho-modulo-kiss-share
   witness: 0007-rho-modulo-kiss-share
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenCookLoop.
From NTS.Proofs Require Import SheetHenCookLoopModulo.
From NTS.Proofs Require Import HostRhoLeftoverBagTerm.
Local Open Scope R_scope.

(* WITNESS: campaign=rho rung=modulo-kiss-share claim=0007-rho-modulo-kiss-share
   file=theories/HostRhoModuloKissShare.v
   kind=QEX-named-missing-ctors
   park=ModuloKissStep,ModuloShareMintStep
   missing=leftover_pair_kiss_ok,leftover_pair_share_mint_ok
   not=LoopDischarged,leftover_quad_width-decreases,LeftoverBagTermArm
   not=I.8-bag-Discharge,first-cook-expand,I_ok_mixed,CircGamma-remint
   not=NURBS,SIN,ellipse,geodesic,Karney,atan2,classic,Category-C
   not=rho-closed,noder-loop-done
   sibling=modulo-iter,LeftoverKissArm,LeftoverShareMintArm
   note=letter-not-rho-discharge *)

(* -------------------------------------------------------------------------- *)
(* leftover_bag_step is Hit-split or Decline. No third constructor.           *)
(* -------------------------------------------------------------------------- *)

Definition leftover_bag_step_is_hit (b b' : leftover_span_bag) : Prop :=
  exists i j p ua ub,
    leftover_pair_step_ok b i j p ua ub /\
    lbag_pair_replace b i j ua ub = Some b'.

Definition leftover_bag_step_is_decline (b b' : leftover_span_bag) : Prop :=
  b' = b /\ exists i j, leftover_pair_decline b i j.

Lemma leftover_bag_step_hit_or_decline :
  forall b b',
    leftover_bag_step b b' ->
    leftover_bag_step_is_hit b b' \/ leftover_bag_step_is_decline b b'.
Proof.
  intros b b' Hstep.
  inversion Hstep; subst.
  - left. exists i, j, p, ua, ub. split; assumption.
  - right. split; [reflexivity|]. exists i, j. assumption.
Qed.

Lemma leftover_bag_step_no_third_ctor :
  forall b b',
    leftover_bag_step b b' ->
    leftover_bag_step_is_hit b b' \/ leftover_bag_step_is_decline b b'.
Proof.
  exact leftover_bag_step_hit_or_decline.
Qed.

(* leftover_pair_kiss_ok would be a leftover-quad kiss leftover_bag_step
   leftover_bag_cook_fuel can consume. leftover_quad_kiss_arm is the
   sibling #797 hole (LeftoverKissArm), not this constructor. A third
   leftover_bag_step ctor is also missing. *)
Definition leftover_pair_kiss_ok : Prop :=
  leftover_quad_kiss_arm /\
  exists b b',
    lbag_count b = 4%nat /\
    leftover_bag_step b b' /\
    ~ leftover_bag_step_is_hit b b' /\
    ~ leftover_bag_step_is_decline b b'.

(* leftover_pair_share_mint_ok would be a leftover-quad share/mint
   leftover_bag_step leftover_bag_cook_fuel can consume.
   leftover_quad_share_mint_arm is the sibling #797 hole
   (LeftoverShareMintArm), not this constructor. *)
Definition leftover_pair_share_mint_ok : Prop :=
  leftover_quad_share_mint_arm /\
  exists b b',
    lbag_count b = 4%nat /\
    leftover_bag_step b b' /\
    ~ leftover_bag_step_is_hit b b' /\
    ~ leftover_bag_step_is_decline b b'.

Lemma leftover_pair_kiss_ok_missing :
  ~ leftover_pair_kiss_ok.
Proof.
  intros [Hkiss _].
  exact (leftover_quad_kiss_arm_missing Hkiss).
Qed.

Lemma leftover_pair_share_mint_ok_missing :
  ~ leftover_pair_share_mint_ok.
Proof.
  intros [Hshare _].
  exact (leftover_quad_share_mint_arm_missing Hshare).
Qed.

Lemma leftover_pair_kiss_ok_not_a_bag_step :
  forall b b',
    leftover_bag_step b b' ->
    leftover_bag_step_is_hit b b' \/ leftover_bag_step_is_decline b b'.
Proof.
  exact leftover_bag_step_hit_or_decline.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. Not bools. Inhabitance is the leftover-quad    *)
(* kiss / share-mint leftover_bag_step. leftover_bag_step has no such ctor.   *)
(* -------------------------------------------------------------------------- *)

Inductive ModuloKissShareCtor : Type :=
| ModuloKissStep
| ModuloShareMintStep.

Definition modulo_kiss_share_ctor_inhabits (c : ModuloKissShareCtor) : Prop :=
  match c with
  | ModuloKissStep => leftover_pair_kiss_ok
  | ModuloShareMintStep => leftover_pair_share_mint_ok
  end.

Lemma modulo_kiss_step_missing :
  ~ modulo_kiss_share_ctor_inhabits ModuloKissStep.
Proof.
  exact leftover_pair_kiss_ok_missing.
Qed.

Lemma modulo_share_mint_step_missing :
  ~ modulo_kiss_share_ctor_inhabits ModuloShareMintStep.
Proof.
  exact leftover_pair_share_mint_ok_missing.
Qed.

Lemma modulo_kiss_share_ctors_uninhabited :
  ~ modulo_kiss_share_ctor_inhabits ModuloKissStep
  /\ ~ modulo_kiss_share_ctor_inhabits ModuloShareMintStep
  /\ ~ leftover_pair_kiss_ok
  /\ ~ leftover_pair_share_mint_ok.
Proof.
  split; [exact modulo_kiss_step_missing|].
  split; [exact modulo_share_mint_step_missing|].
  split; [exact leftover_pair_kiss_ok_missing|].
  exact leftover_pair_share_mint_ok_missing.
Qed.

Lemma leftover_bag_cook_fuel_no_kiss_share :
  leftover_bag_cook_fuel 1 locked_parent_bag locked_quad_bag /\
  leftover_pair_step_ok locked_parent_bag 0 1
    cross_pt (1 / 2) (1 / 2) /\
  leftover_bag_cook_fuel 1 locked_quad_bag locked_quad_bag /\
  leftover_pair_decline locked_quad_bag 0 2 /\
  ~ leftover_pair_kiss_ok /\
  ~ leftover_pair_share_mint_ok.
Proof.
  split; [exact locked_hit_nstep|].
  split; [exact locked_parent_step_ok|].
  split; [exact locked_decline_nstep|].
  split; [exact locked_quad_decline|].
  split; [exact leftover_pair_kiss_ok_missing|].
  exact leftover_pair_share_mint_ok_missing.
Qed.

Lemma modulo_kiss_share_loop_unchanged :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged
  /\ ~ leftover_quad_width_decreases
  /\ ~ leftover_bag_term_arm
  /\ ~ cook_loop_ctor_inhabits CookLoopBagTerm.
Proof.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact leftover_quad_width_does_not_decrease|].
  split; [exact leftover_bag_term_arm_missing|].
  exact cook_loop_bag_term_missing.
Qed.

Lemma modulo_kiss_share_scope_unchanged :
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
(* Sibling cites — packaging, not bag-loop Discharge.                         *)
(* -------------------------------------------------------------------------- *)

Lemma sibling_modulo_iter_not_kiss_share :
  leftover_bag_cook_fuel 1 locked_parent_bag locked_quad_bag
  /\ leftover_pair_step_ok locked_parent_bag 0 1
       cross_pt (1 / 2) (1 / 2)
  /\ leftover_bag_cook_fuel 1 locked_quad_bag locked_quad_bag
  /\ leftover_pair_decline locked_quad_bag 0 2
  /\ cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged
  /\ ~ leftover_pair_kiss_ok
  /\ ~ leftover_pair_share_mint_ok.
Proof.
  destruct ticket_0007_rho_modulo_iter_qed_or_qex as [H | Hdis].
  - destruct H as [_ [Hnstep [Hok [Hdec [Hjoin [_ [Hob Hnd]]]]]]].
    split; [exact Hnstep|].
    split; [exact Hok|].
    split; [exact Hdec|].
    split; [exact Hjoin|].
    split; [exact Hob|].
    split; [exact Hnd|].
    split; [exact leftover_pair_kiss_ok_missing|].
    exact leftover_pair_share_mint_ok_missing.
  - exfalso. exact (cook_loop_not_discharged Hdis).
Qed.

Lemma sibling_leftover_kiss_share_not_modulo_step :
  ~ leftover_bag_term_ctor_inhabits LeftoverKissArm
  /\ ~ leftover_bag_term_ctor_inhabits LeftoverShareMintArm
  /\ ~ leftover_quad_kiss_arm
  /\ ~ leftover_quad_share_mint_arm
  /\ ~ leftover_pair_kiss_ok
  /\ ~ leftover_pair_share_mint_ok
  /\ ~ leftover_bag_term_arm
  /\ cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact leftover_kiss_arm_missing|].
  split; [exact leftover_share_mint_arm_missing|].
  split; [exact leftover_quad_kiss_arm_missing|].
  split; [exact leftover_quad_share_mint_arm_missing|].
  split; [exact leftover_pair_kiss_ok_missing|].
  split; [exact leftover_pair_share_mint_ok_missing|].
  split; [exact leftover_bag_term_arm_missing|].
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stop.                                               *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-rho-modulo-kiss-share","topic":"overlay","lemma":"ticket_0007_rho_modulo_kiss_share_qed_or_qex","title":"rho modulo kiss/share-mint: leftover_pair_kiss_ok and leftover_pair_share_mint_ok inhabit leftover-quad leftover_bag_step constructors leftover_bag_cook_fuel can consume while cook_loop stays LoopObligation and leftover_quad_width_decreases stays false (QED) or ModuloKissStep and ModuloShareMintStep stay missing leftover_bag_step stays Hit-or-Decline and cook_loop stays LoopObligation (QEX); discharged QEX; sibling modulo-iter QED and LeftoverKissArm/LeftoverShareMintArm are not bag Discharge","file":"theories/HostRhoModuloKissShare.v","witness":"0007-rho-modulo-kiss-share","board":"ADR-0007"} *)
Theorem ticket_0007_rho_modulo_kiss_share_qed_or_qex :
  (leftover_pair_kiss_ok
   /\ leftover_pair_share_mint_ok
   /\ cook_loop_status = LoopObligation
   /\ ~ leftover_quad_width_decreases)
  \/
  (cook_loop_status = LoopObligation
   /\ cook_loop_status <> LoopDischarged
   /\ ~ leftover_pair_kiss_ok
   /\ ~ leftover_pair_share_mint_ok
   /\ ~ modulo_kiss_share_ctor_inhabits ModuloKissStep
   /\ ~ modulo_kiss_share_ctor_inhabits ModuloShareMintStep
   /\ ~ leftover_bag_term_ctor_inhabits LeftoverKissArm
   /\ ~ leftover_bag_term_ctor_inhabits LeftoverShareMintArm
   /\ ~ leftover_quad_width_decreases
   /\ ~ leftover_quad_kiss_arm
   /\ ~ leftover_quad_share_mint_arm
   /\ ~ leftover_bag_term_arm
   /\ LeftoverBagTermArm = leftover_bag_term_arm
   /\ ~ cook_loop_ctor_inhabits CookLoopBagTerm
   /\ leftover_bag_cook_fuel 1 locked_parent_bag locked_quad_bag
   /\ leftover_pair_step_ok locked_parent_bag 0 1
        cross_pt (1 / 2) (1 / 2)
   /\ leftover_bag_cook_fuel 1 locked_quad_bag locked_quad_bag
   /\ leftover_pair_decline locked_quad_bag 0 2
   /\ first_cook_scope EggChord EggChord
   /\ first_cook_scope EggNurbs EggNurbs).
Proof.
  right.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact leftover_pair_kiss_ok_missing|].
  split; [exact leftover_pair_share_mint_ok_missing|].
  split; [exact modulo_kiss_step_missing|].
  split; [exact modulo_share_mint_step_missing|].
  split; [exact leftover_kiss_arm_missing|].
  split; [exact leftover_share_mint_arm_missing|].
  split; [exact leftover_quad_width_does_not_decrease|].
  split; [exact leftover_quad_kiss_arm_missing|].
  split; [exact leftover_quad_share_mint_arm_missing|].
  split; [exact leftover_bag_term_arm_missing|].
  split; [reflexivity|].
  split; [exact cook_loop_bag_term_missing|].
  split; [exact locked_hit_nstep|].
  split; [exact locked_parent_step_ok|].
  split; [exact locked_decline_nstep|].
  split; [exact locked_quad_decline|].
  split; [exact first_cook_scope_chord_chord|].
  exact nurbs_nurbs_first_cook_scope.
Qed.

Print Assumptions leftover_bag_step_hit_or_decline.
Print Assumptions leftover_bag_step_no_third_ctor.
Print Assumptions leftover_pair_kiss_ok_missing.
Print Assumptions leftover_pair_share_mint_ok_missing.
Print Assumptions leftover_pair_kiss_ok_not_a_bag_step.
Print Assumptions modulo_kiss_step_missing.
Print Assumptions modulo_share_mint_step_missing.
Print Assumptions modulo_kiss_share_ctors_uninhabited.
Print Assumptions leftover_bag_cook_fuel_no_kiss_share.
Print Assumptions modulo_kiss_share_loop_unchanged.
Print Assumptions modulo_kiss_share_scope_unchanged.
Print Assumptions sibling_modulo_iter_not_kiss_share.
Print Assumptions sibling_leftover_kiss_share_not_modulo_step.
Print Assumptions ticket_0007_rho_modulo_kiss_share_qed_or_qex.
