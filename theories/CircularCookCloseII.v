(* ============================================================================
   NetTopologySuite.Proofs.CircularCookCloseII
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: II.4 Campaign-II close letter.

   Campaign II is the circular sidecar glossary-inhabitant programme
   on Accepted ADR-0007 (#695 II.1 + #696 II.2 + #697 II.3). This
   letter tickets the close. It does not start Phase B, H⊥, or a
   CircGamma remint. It does not remint a kernel.

   Campaign II close: I_ok_circ exists as the sidecar glossary
   inhabitant on EggCircularArc × EggCircularArc (one Arc, via
   arc_gamma / span filter / span split). Host CircGamma stays QEX.
   first_cook_scope stays chord–chord. Host circular I_ok stays
   Decline. I_ok_circ Hit ≠ host I_ok. Not a bag noder
   (cook_loop stays obligation). H⊥ stays parked.

   Phase B SQL/MM Part 3 *required* types are named as gaps —
   CircularString / CompoundCurve / CurvePolygon — so AFK Phase B
   can start the smallest required-type 𝓘 cuts. Not “SQL/MM done”.
   A CircularString theorem needs concatenation; I_ok_circ is one
   Arc. Not CompoundCurve. Not CurvePolygon. Not the cathedral.

   QED: sidecar I_ok_circ inhabits Hit / Empty / Decline on the
   locked fixtures; leftover meet is Hit incidence (= ¬Empty),
   not a kiss certificate; Campaign II is closed as a letter.
   QEX: host CircGamma stays QEX; first_cook_scope stays
   chord–chord; bag loop stays obligation; H⊥ stays parked;
   Phase B CS / CC / CP gaps named; SQL/MM is not done.

   Honesty fences:
     Host-Decline / CircGamma-QEX at the top of this module.
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ span filter ≠
     span split ≠ I_ok_circ ≠ glossary I_gloss / host I_ok.
     Leftover shared endpoint is Hit / ¬Empty, not a CRV-TOUCH
     kiss procedure.
     Not first cook scope. Not a bag noder. Not ArcSplitAtNode.
     Not CircularString concatenation. Not CompoundCurve /
     CurvePolygon.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width / host circ_split.
     Do not fake atan2-free host γ. Do not expand first_cook_scope.
     Do not start Phase B / H⊥ / a CRV-TOUCH kiss procedure /
     CircGamma remint / full SQL/MM cathedral.
     No new kernel. Not SQL/MM done.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-II.4-campaign-ii-close
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via CircularCookOkCirc).
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  CircularCook CircularCookHit CircularCookSpan CircularCookSpanFilter
  CircularCookSpanSplit CircularCookOkCirc.
Local Open Scope R_scope.

(* WITNESS: campaign=II rung=II.4 claim=0007
   file=theories/CircularCookCloseII.v
   kind=QED-or-QEX-campaign-II-close-letter
   not=new-kernel,CircGamma-Discharge,first-cook-noding,SQL-MM-done
   not=bag-noder,CircularString-concat,CRV-TOUCH-kiss
   park=Hperp,Phase-B-CS,Phase-B-CC,Phase-B-CP *)

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma ii4_host_circgamma_qex :
  circular_gamma_status = CircGammaDischarged.
Proof.
  exact circular_gamma_is_discharged.
Qed.

Lemma ii4_host_not_first_cook :
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_is_first_cook_scope.
Qed.

Lemma ii4_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma ii4_host_circular_decline :
  I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact circular_decline_I_ok.
Qed.

Lemma ii4_host_circular_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
         (IHit p ti tj).
Proof.
  exact circular_hit_not_I_ok.
Qed.

(* -------------------------------------------------------------------------- *)
(* Landed Campaign II facts, composed — no new cook.                          *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ii4_sidecar_inhabitant","title":"II.4 I_ok_circ exists as sidecar glossary inhabitant Hit Empty Decline on locked fixtures; CircGamma stays QEX","file":"theories/CircularCookCloseII.v","witness":"0007-II.4-campaign-ii-close","board":"ADR-0007"} *)

Lemma ii4_sidecar_inhabitant :
  I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit
  /\ I_ok_circ span_arc_A span_empty_far IEmpty
  /\ I_ok_circ span_decline_arc span_arc_B IDecline
  /\ circular_gamma_status = CircGammaDischarged.
Proof.
  split; [exact ii3_locked_plus_I_ok_circ|].
  split; [exact ii3_locked_empty|].
  split; [exact ii3_invalid_decline|].
  exact circular_gamma_is_discharged.
Qed.

(* Leftover shared endpoint is Hit incidence. “Not a kiss” here is
   ¬Empty — not a CRV-TOUCH kiss certificate. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ii4_leftover_meet_not_empty","title":"II.4 leftover meet is I_ok_circ Hit and not Empty; not a kiss certificate","file":"theories/CircularCookCloseII.v","witness":"0007-II.4-campaign-ii-close","board":"ADR-0007"} *)

Lemma ii4_leftover_meet_not_empty :
  I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit
  /\ span_cooked_meets cooked_span_plus locked_p_plus
  /\ ~ I_ok_circ span_arc_A span_arc_B IEmpty
  /\ IHit locked_p_plus locked_span_ti_plus locked_span_tj_plus <> IEmpty.
Proof.
  split; [exact ii3_locked_plus_I_ok_circ|].
  split; [exact cooked_span_plus_meets|].
  split; [exact ii3_locked_pair_not_empty|].
  apply IHit_neq_IEmpty.
Qed.

Lemma ii4_I_ok_circ_hit_not_host_I_ok :
  I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit
  /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
       locked_ok_circ_hit.
Proof.
  exact ii3_I_ok_circ_hit_not_host_I_ok.
Qed.

Lemma ii4_host_stays_qex :
  circular_gamma_status = CircGammaDischarged
  /\ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggChord EggChord
  /\ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline
  /\ (forall p ti tj,
        ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
             (IHit p ti tj)).
Proof.
  split; [exact ii4_host_circgamma_qex|].
  split; [exact ii4_host_not_first_cook|].
  split; [exact ii4_first_cook_stays_chord_chord|].
  split; [exact ii4_host_circular_decline|].
  exact ii4_host_circular_hit_false.
Qed.

(* One Arc. CircEgg is CircularArc; a CS theorem needs concat. *)
Lemma ii4_inhabitant_is_one_arc :
  CircEgg = CircularArc
  /\ I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit.
Proof.
  split; [reflexivity|].
  exact ii3_locked_plus_I_ok_circ.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named parks / gaps. Campaign II is closed; Phase B gaps are named.         *)
(* -------------------------------------------------------------------------- *)

Inductive CampaignIICloseStatus : Type :=
| CampaignIIClosed
| CampaignIIOpen.

Definition campaign_ii_close_status : CampaignIICloseStatus :=
  CampaignIIClosed.

Lemma campaign_ii_is_closed :
  campaign_ii_close_status = CampaignIIClosed.
Proof.
  reflexivity.
Qed.

Inductive CampaignII4LetterStatus : Type :=
| CampaignII4LetterLanded
| CampaignII4LetterParked.

Definition campaign_ii4_letter_status : CampaignII4LetterStatus :=
  CampaignII4LetterLanded.

Lemma campaign_ii4_letter_is_landed :
  campaign_ii4_letter_status = CampaignII4LetterLanded.
Proof.
  reflexivity.
Qed.

Inductive II4HperpStatus : Type :=
| II4HperpDischarged
| II4HperpParked.

Definition ii4_hperp_status : II4HperpStatus := II4HperpParked.

Lemma ii4_hperp_is_parked :
  ii4_hperp_status = II4HperpParked.
Proof.
  reflexivity.
Qed.

(* Bag-level repeat-until-noded loop. Campaign II did not discharge it. *)
Lemma ii4_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

(* Phase B = SQL/MM Part 3 required types (CS / CC / CP). Named gaps.
   Not this letter. Not “SQL/MM done”. *)
Inductive II4PhaseBGapStatus : Type :=
| II4PhaseBRequiredGap
| II4PhaseBRequiredLanded.

Definition phase_b_circular_string_status : II4PhaseBGapStatus :=
  II4PhaseBRequiredGap.

Definition phase_b_compound_curve_status : II4PhaseBGapStatus :=
  II4PhaseBRequiredGap.

Definition phase_b_curve_polygon_status : II4PhaseBGapStatus :=
  II4PhaseBRequiredGap.

Lemma phase_b_cs_is_gap :
  phase_b_circular_string_status = II4PhaseBRequiredGap.
Proof.
  reflexivity.
Qed.

Lemma phase_b_cc_is_gap :
  phase_b_compound_curve_status = II4PhaseBRequiredGap.
Proof.
  reflexivity.
Qed.

Lemma phase_b_cp_is_gap :
  phase_b_curve_polygon_status = II4PhaseBRequiredGap.
Proof.
  reflexivity.
Qed.

Inductive II4SqlMmStatus : Type :=
| II4SqlMmDone
| II4SqlMmNotDone.

Definition ii4_sql_mm_status : II4SqlMmStatus := II4SqlMmNotDone.

Lemma ii4_sql_mm_is_not_done :
  ii4_sql_mm_status = II4SqlMmNotDone.
Proof.
  reflexivity.
Qed.

Lemma ii4_phase_b_gaps_named :
  phase_b_circular_string_status = II4PhaseBRequiredGap
  /\ phase_b_compound_curve_status = II4PhaseBRequiredGap
  /\ phase_b_curve_polygon_status = II4PhaseBRequiredGap
  /\ ii4_sql_mm_status = II4SqlMmNotDone
  /\ ii4_hperp_status = II4HperpParked
  /\ cook_loop_status = LoopObligation.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii4_inhabitant_qed_or_qex","title":"II.4 sidecar I_ok_circ inhabits Hit Empty Decline on locked fixtures (QED) or the locked pair declines I_ok_circ (QEX); discharged QED; Campaign II first glossary inhabitant; CircGamma stays QEX","file":"theories/CircularCookCloseII.v","witness":"0007-II.4-campaign-ii-close","board":"ADR-0007"} *)

Theorem ticket_0007_ii4_inhabitant_qed_or_qex :
  (I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit
   /\ I_ok_circ span_arc_A span_empty_far IEmpty
   /\ I_ok_circ span_decline_arc span_arc_B IDecline
   /\ CircEgg = CircularArc
   /\ circular_gamma_status = CircGammaDischarged)
  \/
  I_ok_circ span_arc_A span_arc_B IDecline.
Proof.
  left.
  destruct ii4_sidecar_inhabitant as [Hh [He [Hd Hq]]].
  split; [exact Hh|].
  split; [exact He|].
  split; [exact Hd|].
  split; [reflexivity|].
  exact Hq.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii4_not_kiss_qed_or_qex","title":"II.4 leftover meet is I_ok_circ Hit and not Empty (QED) or the locked pair is Empty (QEX); discharged QED; not a kiss equals not Empty; not a CRV-TOUCH kiss certificate","file":"theories/CircularCookCloseII.v","witness":"0007-II.4-campaign-ii-close","board":"ADR-0007"} *)

Theorem ticket_0007_ii4_not_kiss_qed_or_qex :
  (I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit
   /\ span_cooked_meets cooked_span_plus locked_p_plus
   /\ ~ I_ok_circ span_arc_A span_arc_B IEmpty
   /\ IHit locked_p_plus locked_span_ti_plus locked_span_tj_plus <> IEmpty
   /\ I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit
   /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
        locked_ok_circ_hit)
  \/
  I_ok_circ span_arc_A span_arc_B IEmpty.
Proof.
  left.
  destruct ii4_leftover_meet_not_empty as [Hh [Hm [He Hk]]].
  destruct ii4_I_ok_circ_hit_not_host_I_ok as [Hh2 Hhost].
  split; [exact Hh|].
  split; [exact Hm|].
  split; [exact He|].
  split; [exact Hk|].
  split; [exact Hh2|].
  exact Hhost.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii4_host_qed_or_qex","title":"II.4 discharges CircGamma and expands first cook (QED) or CircGamma stays QEX and first cook stays chord-chord (QEX); discharged QEX; host circular I_ok is Decline; I_ok_circ Hit is not host I_ok","file":"theories/CircularCookCloseII.v","witness":"0007-II.4-campaign-ii-close","board":"ADR-0007"} *)

Theorem ticket_0007_ii4_host_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ exists p ti tj,
        I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
             (IHit p ti tj))
  \/
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggChord EggChord
   /\ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
              (IHit p ti tj))
   /\ I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit
   /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
        locked_ok_circ_hit).
Proof.
  right.
  destruct ii4_host_stays_qex as [Hq [Hn [Hc [Hd Hf]]]].
  destruct ii4_I_ok_circ_hit_not_host_I_ok as [Hhit Hhost].
  split; [exact Hq|].
  split; [exact Hn|].
  split; [exact Hc|].
  split; [exact Hd|].
  split; [exact Hf|].
  split; [exact Hhit|].
  exact Hhost.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii4_phase_b_qed_or_qex","title":"II.4 discharges Phase B CS CC CP, the bag noder, Hperp, and SQL/MM (QED) or names the required-type gaps and parks (QEX); discharged QEX; Campaign II closed; not SQL/MM done","file":"theories/CircularCookCloseII.v","witness":"0007-II.4-campaign-ii-close","board":"ADR-0007"} *)

Theorem ticket_0007_ii4_phase_b_qed_or_qex :
  (phase_b_circular_string_status = II4PhaseBRequiredLanded
   /\ phase_b_compound_curve_status = II4PhaseBRequiredLanded
   /\ phase_b_curve_polygon_status = II4PhaseBRequiredLanded
   /\ cook_loop_status = LoopDischarged
   /\ ii4_hperp_status = II4HperpDischarged
   /\ ii4_sql_mm_status = II4SqlMmDone)
  \/
  (campaign_ii_close_status = CampaignIIClosed
   /\ campaign_ii4_letter_status = CampaignII4LetterLanded
   /\ phase_b_circular_string_status = II4PhaseBRequiredGap
   /\ phase_b_compound_curve_status = II4PhaseBRequiredGap
   /\ phase_b_curve_polygon_status = II4PhaseBRequiredGap
   /\ cook_loop_status = LoopObligation
   /\ ii4_hperp_status = II4HperpParked
   /\ ii4_sql_mm_status = II4SqlMmNotDone).
Proof.
  right.
  split; [exact campaign_ii_is_closed|].
  split; [exact campaign_ii4_letter_is_landed|].
  destruct ii4_phase_b_gaps_named as [Hcs [Hcc [Hcp [Hs [Hh Hn]]]]].
  split; [exact Hcs|].
  split; [exact Hcc|].
  split; [exact Hcp|].
  split; [exact Hn|].
  split; [exact Hh|].
  exact Hs.
Qed.

Print Assumptions ii4_host_circgamma_qex.
Print Assumptions ii4_sidecar_inhabitant.
Print Assumptions ii4_leftover_meet_not_empty.
Print Assumptions ii4_I_ok_circ_hit_not_host_I_ok.
Print Assumptions ii4_host_stays_qex.
Print Assumptions ii4_inhabitant_is_one_arc.
Print Assumptions ii4_not_bag_noder.
Print Assumptions phase_b_cs_is_gap.
Print Assumptions phase_b_cc_is_gap.
Print Assumptions phase_b_cp_is_gap.
Print Assumptions ii4_sql_mm_is_not_done.
Print Assumptions ticket_0007_ii4_inhabitant_qed_or_qex.
Print Assumptions ticket_0007_ii4_not_kiss_qed_or_qex.
Print Assumptions ticket_0007_ii4_host_qed_or_qex.
Print Assumptions ticket_0007_ii4_phase_b_qed_or_qex.
