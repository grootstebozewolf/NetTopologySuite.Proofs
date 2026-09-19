(* ============================================================================
   NetTopologySuite.Proofs.PassesThroughC2WidthPark
   ----------------------------------------------------------------------------
   Letter #66 C2 / width 2²⁵ / arc-Hobby park
   (claimId 66-c2-width-split). Precision / snap-rounding lane.

   The user typo “2²” is not a letter. The park is width 2²⁵ (full
   coord_int_safe) versus the closed C1 regime 2²².

   Already QED — cite, do not remint:
     C1 2²²  PassesThrough_b64_grid_exact.v : b64_passes_through_grid_exact
             claimId 66-c1. |n| ≤ 2²², integer/unit grid, compute ≡ spec.
     #518    host arrow + side-condition Qed via #794.
             ticket_518_core_qed_or_qex is QEX on HobbyFullyIntersectedToHost.

   Already QEX — do not flip to LEFT / Discharge:
     OverlayNG.v : ticket_0007_overlayng_hobby41_qed_or_qex RIGHT
     #805 draft QEX HostSnapRound / HostHobby41 / HostPairPreservation
          HOLD; do not remint as Discharge; do not merge #805.
     C2 rounded-filter completeness (spec ⇒ compute off-grid / full b64)
          is STOP-chased (docs/snap-rounding-rgr-pivot.md).

   This letter owns the SPLIT as three named holes, one stop:
     1. PassesThroughWidth25 — extend C1 from 2²² to 2²⁵
     2. RoundedFilterC2     — off-grid / full-b64 spec⇒compute of the
                              *rounded* filter
     3. ArcHobbyAnalog      — curve-aware Hobby; out-of-scope sibling,
                              cite only

   LEFT only if all three inhabit without weakening C1 2²² and without
   reminting #518 / #805. RIGHT if any ctor is missing.

   This letter does not prove width 2²⁵. It does not bless the off-grid
   rounded filter as sound. QEX ≠ owner accept; #66 stays Urgent /
   closing-gaps.

   Honesty fences:
     Do not weaken C1 2²² Qed.
     Do not fake C2 completeness.
     Do not remint HobbyFullyIntersectedToHost or HostHobby41 as Discharge.
     Do not reopen CircGamma; no first-cook mixed; no CS extend.
     Do not remint 522 / 523 / 508 stops.
     Do not merge #805 from this card.

   Stdlib-only host park. Flocq C1 is cited, not Required.
   0-axiom. No Admitted / Axiom / Parameter.

   WITNESS topic: precision · claimId: 66-c2-width-split
   witness: 66-c2-width-split

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

(* WITNESS: campaign=66-c2 rung=width-split claim=66-c2-width-split
   file=theories/PassesThroughC2WidthPark.v
   kind=QEX-named-missing-ctors
   park=C2WidthSplit
   missing=PassesThroughWidth25,RoundedFilterC2,ArcHobbyAnalog
   cite=66-c1-C1-2^22-Qed,518-HobbyFullyIntersectedToHost-QEX
   cite=overlayng-hobby41-RIGHT,805-HostSnapRound-HostHobby41-HostPairPreservation-HOLD
   not=C1-weaken,C2-completeness-fake,Hobby41-Discharge,518-remint
   not=CircGamma-reopen,first-cook-mixed,CS-extend,522,523,508,805-merge
   note=QEX-not-owner-accept;#66-stays-Urgent-closing-gaps *)

(* -------------------------------------------------------------------------- *)
(* Three named holes. Inhabitance is False: none is constructed here.         *)
(* -------------------------------------------------------------------------- *)

Inductive C2WidthParkCtor : Type :=
| PassesThroughWidth25
| RoundedFilterC2
| ArcHobbyAnalog.

Definition c2_width_ctor_inhabits (c : C2WidthParkCtor) : Prop :=
  match c with
  | PassesThroughWidth25 => False
  | RoundedFilterC2 => False
  | ArcHobbyAnalog => False
  end.

Lemma passes_through_width25_missing :
  ~ c2_width_ctor_inhabits PassesThroughWidth25.
Proof.
  intro H. exact H.
Qed.

Lemma rounded_filter_c2_missing :
  ~ c2_width_ctor_inhabits RoundedFilterC2.
Proof.
  intro H. exact H.
Qed.

Lemma arc_hobby_analog_missing :
  ~ c2_width_ctor_inhabits ArcHobbyAnalog.
Proof.
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* C1 2²² stays QED. Width 2²⁵ is not discharged by this letter.              *)
(* -------------------------------------------------------------------------- *)

Inductive C1Regime : Type :=
| C1GridExact22Qed
| C1Width25Discharged.

Definition c1_regime : C1Regime := C1GridExact22Qed.

Lemma c1_stays_22_qed :
  c1_regime = C1GridExact22Qed.
Proof.
  reflexivity.
Qed.

Lemma c1_width25_not_discharged :
  c1_regime <> C1Width25Discharged.
Proof.
  discriminate.
Qed.

(* Off-grid rounded filter stays unsound (cite, do not bless).                *)
Inductive RoundedFilterOffGrid : Type :=
| RoundedFilterOffGridUnsound
| RoundedFilterC2Blessed.

Definition rounded_filter_off_grid : RoundedFilterOffGrid :=
  RoundedFilterOffGridUnsound.

Lemma rounded_filter_stays_unsound_off_grid :
  rounded_filter_off_grid = RoundedFilterOffGridUnsound.
Proof.
  reflexivity.
Qed.

Lemma rounded_filter_c2_not_blessed :
  rounded_filter_off_grid <> RoundedFilterC2Blessed.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Sibling QEX / HOLD. Do not remint as Discharge.                            *)
(* -------------------------------------------------------------------------- *)

Inductive Ticket518Bridge : Type :=
| HobbyFullyIntersectedToHostMissing
| HobbyFullyIntersectedToHostDischarged.

Definition ticket_518_bridge : Ticket518Bridge :=
  HobbyFullyIntersectedToHostMissing.

Lemma ticket_518_bridge_stays_missing :
  ticket_518_bridge = HobbyFullyIntersectedToHostMissing.
Proof.
  reflexivity.
Qed.

Lemma ticket_518_bridge_not_discharged :
  ticket_518_bridge <> HobbyFullyIntersectedToHostDischarged.
Proof.
  discriminate.
Qed.

Inductive Hobby41HostStatus : Type :=
| OverlayNGHobby41Qex
| Draft805HostHobby41Hold
| Hobby41Discharged.

Definition hobby41_host_status : Hobby41HostStatus := OverlayNGHobby41Qex.

Lemma hobby41_stays_qex :
  hobby41_host_status = OverlayNGHobby41Qex.
Proof.
  reflexivity.
Qed.

Lemma hobby41_not_discharged :
  hobby41_host_status <> Hobby41Discharged.
Proof.
  discriminate.
Qed.

Inductive Draft805Park : Type :=
| Draft805Hold
| Draft805Discharge.

Definition draft_805_park : Draft805Park := Draft805Hold.

Lemma draft_805_stays_hold :
  draft_805_park = Draft805Hold.
Proof.
  reflexivity.
Qed.

Lemma draft_805_not_discharge :
  draft_805_park <> Draft805Discharge.
Proof.
  discriminate.
Qed.

(* #66 stays Urgent / closing-gaps. QEX is not owner accept.                  *)
Inductive Epic66Status : Type :=
| Epic66UrgentClosingGaps
| Epic66OwnerAccept.

Definition epic66_status : Epic66Status := Epic66UrgentClosingGaps.

Lemma epic66_stays_urgent_closing_gaps :
  epic66_status = Epic66UrgentClosingGaps.
Proof.
  reflexivity.
Qed.

Lemma epic66_qex_not_owner_accept :
  epic66_status <> Epic66OwnerAccept.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket stop. QED ∨ QEX. Discharged QEX: all three ctors missing.           *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"66-c2-width-split","topic":"precision","lemma":"ticket_66_c2_width_split_qed_or_qex","title":"#66 C2 / width 2^25 / arc-Hobby park: PassesThroughWidth25 RoundedFilterC2 ArcHobbyAnalog inhabit without weakening C1 2^22 and without reminting #518/#805 (QED); or those three ctors stay missing, C1 2^22 stays Qed, C2 completeness stays STOP-chased, ArcHobby stays unnamed on main, #518 HobbyFullyIntersectedToHost and Hobby 4.1 / #805 HOLD stay un-Discharged (QEX); discharged QEX; QEX is not owner accept; #66 stays Urgent / closing-gaps","file":"theories/PassesThroughC2WidthPark.v","witness":"66-c2-width-split"} *)
Theorem ticket_66_c2_width_split_qed_or_qex :
  (c2_width_ctor_inhabits PassesThroughWidth25
   /\ c2_width_ctor_inhabits RoundedFilterC2
   /\ c2_width_ctor_inhabits ArcHobbyAnalog
   /\ c1_regime = C1GridExact22Qed
   /\ ticket_518_bridge = HobbyFullyIntersectedToHostDischarged
   /\ hobby41_host_status = Hobby41Discharged
   /\ draft_805_park = Draft805Discharge)
  \/
  (~ c2_width_ctor_inhabits PassesThroughWidth25
   /\ ~ c2_width_ctor_inhabits RoundedFilterC2
   /\ ~ c2_width_ctor_inhabits ArcHobbyAnalog
   /\ c1_regime = C1GridExact22Qed
   /\ c1_regime <> C1Width25Discharged
   /\ rounded_filter_off_grid = RoundedFilterOffGridUnsound
   /\ rounded_filter_off_grid <> RoundedFilterC2Blessed
   /\ ticket_518_bridge = HobbyFullyIntersectedToHostMissing
   /\ ticket_518_bridge <> HobbyFullyIntersectedToHostDischarged
   /\ hobby41_host_status = OverlayNGHobby41Qex
   /\ hobby41_host_status <> Hobby41Discharged
   /\ draft_805_park = Draft805Hold
   /\ draft_805_park <> Draft805Discharge
   /\ epic66_status = Epic66UrgentClosingGaps
   /\ epic66_status <> Epic66OwnerAccept).
Proof.
  right.
  split; [exact passes_through_width25_missing |].
  split; [exact rounded_filter_c2_missing |].
  split; [exact arc_hobby_analog_missing |].
  split; [reflexivity |].
  split; [exact c1_width25_not_discharged |].
  split; [reflexivity |].
  split; [exact rounded_filter_c2_not_blessed |].
  split; [reflexivity |].
  split; [exact ticket_518_bridge_not_discharged |].
  split; [reflexivity |].
  split; [exact hobby41_not_discharged |].
  split; [reflexivity |].
  split; [exact draft_805_not_discharge |].
  split; [reflexivity |].
  exact epic66_qex_not_owner_accept.
Qed.

Print Assumptions passes_through_width25_missing.
Print Assumptions rounded_filter_c2_missing.
Print Assumptions arc_hobby_analog_missing.
Print Assumptions c1_stays_22_qed.
Print Assumptions c1_width25_not_discharged.
Print Assumptions rounded_filter_stays_unsound_off_grid.
Print Assumptions ticket_518_bridge_stays_missing.
Print Assumptions hobby41_stays_qex.
Print Assumptions draft_805_stays_hold.
Print Assumptions epic66_stays_urgent_closing_gaps.
Print Assumptions ticket_66_c2_width_split_qed_or_qex.
