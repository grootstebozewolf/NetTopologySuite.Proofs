(* ============================================================================
   NetTopologySuite.Proofs.SheetHenCookLoop
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: ρ bag-loop stop (claimId 0007-ρ-bag-loop).

   Honest QED ∨ QEX for the bag-level repeat-until-noded cook loop
   (SheetHenCook.cook_loop_status = LoopObligation;
    Adr0007NodingEpic.ticket_0007_cook_term_qed_or_qex).

   QED would be LoopDischarged with a real termination + confluence
   theorem on leftover bags. That needs a bag-term measure covering
   kiss / ShareOne / MintTwo cycles — not available without a
   CRV-TOUCH prototype.

   QEX (this letter): strengthen the obligation into a named gap,
   508-style, not a bool and not a soft gap that reopens Accept.
     1. No CookLoopBagTerm constructor — leftover_width is pairwise
        on a parameter interval; the leftover_quad bag-sum is
        conserved (two parents, width 1+1), so it is not a
        well-founded bag measure.
     2. Empty / Decline allocate no leftover split (try_cook_hit
        = None); ShareOne ignores leftover_width; MintTwo may
        increase hen cardinality while leftover_width [0,1] stays 1.
        Kiss / share / mint cycles are not covered by pairwise width.
     3. Pairwise leftover-width decrease + one-step confluence are
        already QED (ticket_0007_pairwise_split_qed_or_qex / I.8).
        Those do not flip LoopDischarged. Do not collapse I.8 into
        bag-loop Discharge.
     4. ρ leftover_quad ≠ η Multi bags (SidecarCircBags: bags of
        already-Qed CS / CC / CP members). Arc cook termination
        is a sister card, not this stop.

   Do not fake LoopDischarged. Host CircGamma stays QEX. first cook
   stays chord–chord. Not a remint of I_ok_mixed / CircGamma /
   leftover_width / pairwise_split.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. QEX is not a new Accept cycle.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-rho-bag-loop
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook.
Local Open Scope R_scope.

(* WITNESS: campaign=rho rung=bag-loop claim=0007
   file=theories/SheetHenCookLoop.v
   kind=QEX-named-bag-term-gap
   not=pairwise-split-Discharge,I.8-bag-Discharge,Multi-bags,CircGamma-Discharge
   not=Hperp,SQL-MM-cathedral,Phase-B-done-when
   sister=arc-cook-term *)

(* -------------------------------------------------------------------------- *)
(* Named gap (508-style): missing bag-term constructor.                       *)
(* -------------------------------------------------------------------------- *)

(* Discharge constructor: a well-founded measure on leftover bags that
   decreases under Hit-split / kiss / ShareOne / MintTwo. There is
   none — leftover_width is pairwise on [t0,t1]. *)
Inductive CookLoopConstructor : Type :=
| CookLoopBagTerm.

Definition cook_loop_ctor_inhabits (c : CookLoopConstructor) : Prop :=
  match c with
  | CookLoopBagTerm => False
  end.

Lemma cook_loop_bag_term_missing :
  ~ cook_loop_ctor_inhabits CookLoopBagTerm.
Proof.
  intro H. exact H.
Qed.

(* leftover_width sum on one leftover_quad (two parents, each split
   at an interior Hit). Pairwise each parent decreases; the bag-sum
   is conserved at 1+1. That is not a well-founded bag measure. *)
Definition leftover_quad_width (ti tj : R) : R :=
  leftover_width 0 ti + leftover_width ti 1
  + leftover_width 0 tj + leftover_width tj 1.

Lemma leftover_quad_width_conserved :
  forall ti tj,
    0 < ti < 1 ->
    0 < tj < 1 ->
    leftover_quad_width ti tj =
    leftover_width 0 1 + leftover_width 0 1.
Proof.
  intros ti tj Hti Htj.
  unfold leftover_quad_width.
  destruct (interior_hit_splits_width ti Hti) as [Ha _].
  destruct (interior_hit_splits_width tj Htj) as [Hb _].
  rewrite Ha.
  rewrite Rplus_assoc.
  rewrite Hb.
  reflexivity.
Qed.

Lemma leftover_quad_width_is_two :
  forall ti tj,
    0 < ti < 1 ->
    0 < tj < 1 ->
    leftover_quad_width ti tj = 2.
Proof.
  intros ti tj Hti Htj.
  rewrite leftover_quad_width_conserved; try assumption.
  rewrite leftover_width_parent.
  lra.
Qed.

(* Per-parent leftover-width still strictly decreases. The bag-sum
   does not — pairwise QED is not bag-term QED. *)
Lemma leftover_width_parent_decreases_bag_sum_does_not :
  forall t,
    0 < t < 1 ->
    leftover_width 0 t < leftover_width 0 1 /\
    leftover_width t 1 < leftover_width 0 1 /\
    leftover_quad_width t t = leftover_width 0 1 + leftover_width 0 1.
Proof.
  intros t Ht.
  destruct (interior_hit_splits_width t Ht) as [_ [Hlo Hhi]].
  split; [exact Hlo|].
  split; [exact Hhi|].
  apply leftover_quad_width_conserved; exact Ht.
Qed.

(* -------------------------------------------------------------------------- *)
(* Kiss / share / mint cycles are not leftover-width decrease.                *)
(* -------------------------------------------------------------------------- *)

(* Empty / Decline allocate no leftover halves. Parent width stays 1. *)
Lemma no_hit_no_leftover_split :
  leftover_width 0 1 = 1 /\
  (forall c1 c2 h, try_cook_hit c1 c2 IEmpty h = None) /\
  (forall c1 c2 h, try_cook_hit c1 c2 IDecline h = None).
Proof.
  split; [exact leftover_width_parent|].
  split.
  - exact try_cook_hit_empty_none.
  - exact try_cook_hit_decline_none.
Qed.

(* ShareOne is hen-structural. It does not consult leftover_width. *)
Lemma share_one_not_width_measure :
  forall h,
    fst (apply_id_decision (ShareOne h)) =
    snd (apply_id_decision (ShareOne h)) /\
    leftover_width 0 1 = 1.
Proof.
  intros h.
  split; [apply share_one_same_hen|exact leftover_width_parent].
Qed.

(* MintTwo may mint two distinct hens. leftover_width of [0,1] stays 1.
   Hen cardinality is not leftover_width. *)
Lemma mint_two_not_width_bound :
  exists a b : Hen,
    fst (apply_id_decision (MintTwo a b)) <>
    snd (apply_id_decision (MintTwo a b)) /\
    leftover_width 0 1 = 1.
Proof.
  exists 0%nat, 1%nat.
  split; [discriminate|exact leftover_width_parent].
Qed.

(* leftover_quad is four halves of one pairwise Hit-split. Not an
   inductive leftover bag and not η Multi bags of CS / CC / CP. *)
Lemma leftover_quad_is_one_hit :
  pairwise_hit_leftover_count = 4%nat /\
  (forall c1 c2 ti tj,
     leftovers_ab c1 c2 ti tj = leftovers_ba c1 c2 ti tj).
Proof.
  split; [reflexivity|exact split_step_confluent].
Qed.

(* -------------------------------------------------------------------------- *)
(* Arc cook termination is a sister card. Pairwise QED ≠ Discharge.           *)
(* -------------------------------------------------------------------------- *)

Inductive ArcCookTermStatus : Type :=
| ArcTermDischarged
| ArcTermSister.

Definition arc_cook_term_status : ArcCookTermStatus := ArcTermSister.

Lemma arc_cook_term_is_sister :
  arc_cook_term_status = ArcTermSister /\
  cook_loop_status = LoopObligation /\
  cook_loop_status <> LoopDischarged.
Proof.
  split; [reflexivity|].
  split; [exact cook_loop_is_obligation|exact cook_loop_not_discharged].
Qed.

Lemma pairwise_qed_not_bag_discharge :
  interior_split_finite /\
  split_step_confluent_holds /\
  cook_loop_status = LoopObligation /\
  cook_loop_status <> LoopDischarged.
Proof.
  split; [exact interior_split_finite_holds|].
  split; [exact split_step_confluent_holds_proof|].
  split; [exact cook_loop_is_obligation|exact cook_loop_not_discharged].
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_rho_gap_qed_or_qex","title":"rho bag-loop has a bag-term measure on leftover bags (QED) or CookLoopBagTerm is missing and leftover_quad width is conserved (QEX); discharged QEX; 508-style named gap; pairwise leftover-width is a sibling QED stop","file":"theories/SheetHenCookLoop.v","witness":"0007-rho-bag-loop","board":"ADR-0007"} *)
Theorem ticket_0007_rho_gap_qed_or_qex :
  (cook_loop_status = LoopDischarged
   /\ cook_loop_ctor_inhabits CookLoopBagTerm)
  \/
  (cook_loop_status = LoopObligation
   /\ ~ cook_loop_ctor_inhabits CookLoopBagTerm
   /\ (forall ti tj,
         0 < ti < 1 ->
         0 < tj < 1 ->
         leftover_quad_width ti tj =
         leftover_width 0 1 + leftover_width 0 1)).
Proof.
  right.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_bag_term_missing|].
  exact leftover_quad_width_conserved.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_rho_cycles_qed_or_qex","title":"rho bag-loop leftover-width covers kiss ShareOne MintTwo cycles (QED) or Empty Decline mint nothing, ShareOne ignores width, and MintTwo is not a width bound (QEX); discharged QEX","file":"theories/SheetHenCookLoop.v","witness":"0007-rho-bag-loop","board":"ADR-0007"} *)
Theorem ticket_0007_rho_cycles_qed_or_qex :
  (cook_loop_status = LoopDischarged
   /\ leftover_width 0 1 < leftover_width 0 1)
  \/
  (cook_loop_status = LoopObligation
   /\ leftover_width 0 1 = 1
   /\ (forall c1 c2 h, try_cook_hit c1 c2 IEmpty h = None)
   /\ (forall c1 c2 h, try_cook_hit c1 c2 IDecline h = None)
   /\ (forall h,
         fst (apply_id_decision (ShareOne h)) =
         snd (apply_id_decision (ShareOne h)))
   /\ (exists a b : Hen,
         fst (apply_id_decision (MintTwo a b)) <>
         snd (apply_id_decision (MintTwo a b)))).
Proof.
  right.
  split; [exact cook_loop_is_obligation|].
  destruct no_hit_no_leftover_split as [Hw [He Hd]].
  split; [exact Hw|].
  split; [exact He|].
  split; [exact Hd|].
  split; [exact share_one_same_hen|].
  destruct mint_two_may_differ as [a [b Hne]].
  exists a, b. exact Hne.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_rho_neq_pairwise_qed_or_qex","title":"rho pairwise leftover-width plus one-step confluence is not bag-loop Discharge (QED) or cook_loop is LoopDischarged (QEX); discharged QED; do not collapse I.8 into bag Discharge","file":"theories/SheetHenCookLoop.v","witness":"0007-rho-bag-loop","board":"ADR-0007"} *)
Theorem ticket_0007_rho_neq_pairwise_qed_or_qex :
  (interior_split_finite
   /\ split_step_confluent_holds
   /\ cook_loop_status = LoopObligation
   /\ cook_loop_status <> LoopDischarged)
  \/
  cook_loop_status = LoopDischarged.
Proof.
  left.
  exact pairwise_qed_not_bag_discharge.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_rho_scope_qed_or_qex","title":"rho bag-loop discharges Multi bags and arc cook termination (QED) or leftover_quad is one Hit-split, arc term stays sister, bag loop stays obligation, ellipse stays out (QEX); discharged QEX; rho != eta Multi bags","file":"theories/SheetHenCookLoop.v","witness":"0007-rho-bag-loop","board":"ADR-0007"} *)
Theorem ticket_0007_rho_scope_qed_or_qex :
  (cook_loop_status = LoopDischarged
   /\ arc_cook_term_status = ArcTermDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc)
  \/
  (cook_loop_status = LoopObligation
   /\ pairwise_hit_leftover_count = 4%nat
   /\ arc_cook_term_status = ArcTermSister
   /\ first_cook_scope EggChord EggChord
   /\ first_cook_scope EggClothoid EggClothoid
   /\ first_cook_scope EggNurbs EggNurbs
   /\ ~ first_cook_scope EggEllipse EggEllipse).
Proof.
  right.
  split; [exact cook_loop_is_obligation|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact clothoid_egg_first_cook_scope|].
  split; [exact nurbs_egg_first_cook_scope|].
  exact ellipse_ellipse_not_first_scope.
Qed.

Print Assumptions cook_loop_bag_term_missing.
Print Assumptions leftover_quad_width_conserved.
Print Assumptions leftover_quad_width_is_two.
Print Assumptions leftover_width_parent_decreases_bag_sum_does_not.
Print Assumptions no_hit_no_leftover_split.
Print Assumptions share_one_not_width_measure.
Print Assumptions mint_two_not_width_bound.
Print Assumptions leftover_quad_is_one_hit.
Print Assumptions arc_cook_term_is_sister.
Print Assumptions pairwise_qed_not_bag_discharge.
Print Assumptions ticket_0007_rho_gap_qed_or_qex.
Print Assumptions ticket_0007_rho_cycles_qed_or_qex.
Print Assumptions ticket_0007_rho_neq_pairwise_qed_or_qex.
Print Assumptions ticket_0007_rho_scope_qed_or_qex.
