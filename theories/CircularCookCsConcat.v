(* ============================================================================
   NetTopologySuite.Proofs.CircularCookCsConcat
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Phase B.1 — CircularString concat joints
   for SQL/MM Part 3 required-type glossary 𝓘 (sidecar reuse).

   II.4 closed Campaign II and named Phase B required-type gaps
   (CircularString / CompoundCurve / CurvePolygon). This letter unparks
   **CircularString joints only**. A CircularString is a sequence of
   CircEgg := CircularArc primitives. A single-arc I_ok_circ fact
   reaches it through a concatenation argument: consecutive members
   share an endpoint (the joint).

   Reuse, not a new kernel: the joint is I_ok_circ Hit at
   (arc_end a, tᵢ=1, tⱼ=0) via arc_gamma_start / arc_gamma_end
   (CircularCookSpan). Span filter / span split / I_ok_circ stay
   the cook. No new 𝓘. Not CompoundCurve. Not CurvePolygon.
   Not a CircGamma remint. Not H⊥.

   Locked fixture: the V-CS odd_closed 5-control CircularString
   CIRCULARSTRING(-5 0, 0 5, 5 0, 0 -5, -5 0) as two CircEgg
   (upper then lower semicircle). Joint at (5,0). Not a remint of
   CircularStringValid.v (control-count lives there).

   QED: ∀ cs_joint is I_ok_circ Hit at (end, 1, 0); joint params
   are not interior (not 0<t<1); locked 2-arc CS is contiguous
   and inhabits; CircEgg = CircularArc (no new kernel).
   QEX: host CircGamma stays QEX; first cook stays chord–chord;
   host circular I_ok is Decline; I_ok_circ Hit ≠ host I_ok;
   CompoundCurve / CurvePolygon / H⊥ stay parked; SQL/MM is
   not done; not a CircGamma remint.

   Honesty fences:
     Host-Decline / CircGamma-QEX at the top of this module.
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ span filter ≠
     span split ≠ I_ok_circ ≠ CS concat joint ≠ glossary I_gloss /
     host I_ok.
     Joint Hit is concat incidence (already a hen), not an interior
     span cook and not a CRV-TOUCH kiss certificate.
     Not first cook scope. Not a bag noder. Not ArcSplitAtNode.
     Not CompoundCurve / CurvePolygon. Not ring closure as CP.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width / host circ_split /
     CircularStringValid control-count.
     Do not fake atan2-free host γ. Do not expand first_cook_scope.
     Do not start CompoundCurve / CurvePolygon / H⊥ / a CRV-TOUCH
     kiss procedure / CircGamma remint / full SQL/MM cathedral.
     No new kernel. Not SQL/MM done.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-B.1-cs-concat-joints
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via CircularCookOkCirc).
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  CircularCook CircularCookHit CircularCookSpan CircularCookSpanFilter
  CircularCookSpanSplit CircularCookOkCirc.
Import ListNotations.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=B.1 claim=0007
   file=theories/CircularCookCsConcat.v
   kind=QED-or-QEX-cs-concat-joints-sidecar-reuse
   gamma=arc-span-not-gamma-full
   reuse=I_ok_circ,arc_gamma,span-filter,span-split
   not=new-kernel,CircGamma-Discharge,first-cook-noding,SQL-MM-done
   not=bag-noder,CompoundCurve,CurvePolygon,CRV-TOUCH-kiss
   park=Hperp,Phase-B-CC,Phase-B-CP *)

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma b1_host_circgamma_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  exact circular_gamma_is_qex.
Qed.

Lemma b1_host_not_first_cook :
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_not_first_cook_scope.
Qed.

Lemma b1_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma b1_host_circular_decline :
  I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact circular_decline_I_ok.
Qed.

Lemma b1_host_circular_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
         (IHit p ti tj).
Proof.
  exact circular_hit_not_I_ok.
Qed.

(* -------------------------------------------------------------------------- *)
(* Concat joints. Reuses arc_gamma / I_ok_circ. No new cook.                  *)
(* -------------------------------------------------------------------------- *)

Definition cs_joint (a b : CircEgg) : Prop :=
  valid_arc a /\ valid_arc b /\ arc_end a = arc_start b.

Definition cs_joint_hit (a b : CircEgg) : IResult :=
  IHit (arc_end a) 1 0.

Definition interior_span_params (ti tj : R) : Prop :=
  0 < ti < 1 /\ 0 < tj < 1.

Definition CircularStringArcs : Type := list CircEgg.

Fixpoint cs_contiguous (cs : CircularStringArcs) : Prop :=
  match cs with
  | [] => True
  | a :: rest =>
      match rest with
      | [] => True
      | b :: _ => cs_joint a b /\ cs_contiguous rest
      end
  end.

Lemma on_arc_gamma_at_start : forall a,
  valid_arc a -> on_arc_gamma a 0 (arc_start a).
Proof.
  intros a Hva.
  unfold on_arc_gamma.
  split.
  - split; lra.
  - symmetry. apply arc_gamma_start. exact Hva.
Qed.

Lemma on_arc_gamma_at_end : forall a,
  valid_arc a -> on_arc_gamma a 1 (arc_end a).
Proof.
  intros a Hva.
  unfold on_arc_gamma.
  split.
  - split; lra.
  - symmetry. apply arc_gamma_end. exact Hva.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"cs_joint_I_ok_circ","title":"Phase B.1 forall CS concat joint is I_ok_circ Hit at (arc_end, t=1, t=0) via sidecar arc_gamma; reuse I_ok_circ; no new kernel","file":"theories/CircularCookCsConcat.v","witness":"0007-B.1-cs-concat-joints","board":"ADR-0007"} *)

Theorem cs_joint_I_ok_circ :
  forall a b : CircEgg,
    cs_joint a b -> I_ok_circ a b (cs_joint_hit a b).
Proof.
  intros a b [Hva [Hvb Heq]].
  unfold cs_joint_hit.
  apply I_ok_circ_hit_iff.
  split; [exact Hva|].
  split; [exact Hvb|].
  split.
  - apply on_arc_gamma_at_end. exact Hva.
  - rewrite Heq. apply on_arc_gamma_at_start. exact Hvb.
Qed.

Lemma joint_params_not_interior :
  ~ interior_span_params 1 0.
Proof.
  intros [[_ H1] _].
  lra.
Qed.

Lemma cs_joint_hit_not_interior :
  forall a b,
    cs_joint a b ->
    I_ok_circ a b (cs_joint_hit a b) /\
    ~ interior_span_params 1 0.
Proof.
  intros a b Hj.
  split; [apply cs_joint_I_ok_circ; exact Hj|].
  exact joint_params_not_interior.
Qed.

(* Joint Hit is concat incidence, not host I_ok. *)
Lemma cs_joint_hit_not_host_I_ok :
  forall a b,
    cs_joint a b ->
    I_ok_circ a b (cs_joint_hit a b) /\
    ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
         (cs_joint_hit a b).
Proof.
  intros a b Hj.
  split; [apply cs_joint_I_ok_circ; exact Hj|].
  unfold cs_joint_hit.
  apply circular_hit_not_I_ok.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked 2-arc CircularString (V-CS odd_closed controls, not reminted).      *)
(* -------------------------------------------------------------------------- *)

Definition locked_cs_arc_1 : CircEgg :=
  mkCircularArc (mkPoint (-5) 0) (mkPoint 0 5) (mkPoint 5 0).

Definition locked_cs_arc_2 : CircEgg :=
  mkCircularArc (mkPoint 5 0) (mkPoint 0 (-5)) (mkPoint (-5) 0).

Definition locked_cs : CircularStringArcs :=
  [locked_cs_arc_1; locked_cs_arc_2].

Definition locked_cs_joint_pt : Point := mkPoint 5 0.

Lemma locked_cs_arc_1_valid : valid_arc locked_cs_arc_1.
Proof.
  unfold valid_arc, locked_cs_arc_1.
  cbn [px py arc_start arc_mid arc_end].
  lra.
Qed.

Lemma locked_cs_arc_2_valid : valid_arc locked_cs_arc_2.
Proof.
  unfold valid_arc, locked_cs_arc_2.
  cbn [px py arc_start arc_mid arc_end].
  lra.
Qed.

Lemma locked_cs_joint :
  cs_joint locked_cs_arc_1 locked_cs_arc_2.
Proof.
  unfold cs_joint, locked_cs_arc_1, locked_cs_arc_2.
  cbn [arc_start arc_end].
  split; [exact locked_cs_arc_1_valid|].
  split; [exact locked_cs_arc_2_valid|].
  reflexivity.
Qed.

Lemma locked_cs_contiguous :
  cs_contiguous locked_cs.
Proof.
  unfold locked_cs, cs_contiguous.
  split; [exact locked_cs_joint|].
  exact I.
Qed.

Lemma locked_cs_joint_I_ok_circ :
  I_ok_circ locked_cs_arc_1 locked_cs_arc_2
    (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2).
Proof.
  apply cs_joint_I_ok_circ.
  exact locked_cs_joint.
Qed.

Lemma locked_cs_joint_pt_eq :
  arc_end locked_cs_arc_1 = locked_cs_joint_pt.
Proof.
  reflexivity.
Qed.

(* Reuse: CircEgg is CircularArc; I_ok_circ is the cook. No new kernel. *)
Lemma b1_reuse_no_new_kernel :
  CircEgg = CircularArc
  /\ I_ok_circ locked_cs_arc_1 locked_cs_arc_2
       (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
  /\ CircularStringArcs = list CircEgg.
Proof.
  split; [reflexivity|].
  split; [exact locked_cs_joint_I_ok_circ|].
  reflexivity.
Qed.

Lemma b1_host_stays_qex :
  circular_gamma_status = CircGammaQEX
  /\ ~ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggChord EggChord
  /\ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline
  /\ (forall p ti tj,
        ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
             (IHit p ti tj)).
Proof.
  split; [exact b1_host_circgamma_qex|].
  split; [exact b1_host_not_first_cook|].
  split; [exact b1_first_cook_stays_chord_chord|].
  split; [exact b1_host_circular_decline|].
  exact b1_host_circular_hit_false.
Qed.

Lemma b1_I_ok_circ_hit_not_host_I_ok :
  I_ok_circ locked_cs_arc_1 locked_cs_arc_2
    (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
  /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
       (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2).
Proof.
  apply cs_joint_hit_not_host_I_ok.
  exact locked_cs_joint.
Qed.

(* -------------------------------------------------------------------------- *)
(* Phase B.1 lands CS joints. CC / CP / H⊥ / SQL/MM cathedral stay parked.    *)
(* -------------------------------------------------------------------------- *)

Inductive PhaseB1Status : Type :=
| PhaseB1Landed
| PhaseB1Parked.

Definition phase_b1_status : PhaseB1Status := PhaseB1Landed.

Lemma phase_b1_is_landed :
  phase_b1_status = PhaseB1Landed.
Proof.
  reflexivity.
Qed.

Inductive PhaseBGapStatus : Type :=
| PhaseBRequiredGap
| PhaseBRequiredLanded.

Definition phase_b_compound_curve_status : PhaseBGapStatus :=
  PhaseBRequiredGap.

Definition phase_b_curve_polygon_status : PhaseBGapStatus :=
  PhaseBRequiredGap.

Lemma phase_b_cc_is_gap :
  phase_b_compound_curve_status = PhaseBRequiredGap.
Proof.
  reflexivity.
Qed.

Lemma phase_b_cp_is_gap :
  phase_b_curve_polygon_status = PhaseBRequiredGap.
Proof.
  reflexivity.
Qed.

Inductive B1HperpStatus : Type :=
| B1HperpDischarged
| B1HperpParked.

Definition b1_hperp_status : B1HperpStatus := B1HperpParked.

Lemma b1_hperp_is_parked :
  b1_hperp_status = B1HperpParked.
Proof.
  reflexivity.
Qed.

Inductive B1SqlMmStatus : Type :=
| B1SqlMmDone
| B1SqlMmNotDone.

Definition b1_sql_mm_status : B1SqlMmStatus := B1SqlMmNotDone.

Lemma b1_sql_mm_is_not_done :
  b1_sql_mm_status = B1SqlMmNotDone.
Proof.
  reflexivity.
Qed.

Inductive B1CircGammaRemintStatus : Type :=
| B1CircGammaReminted
| B1CircGammaRemintParked.

Definition b1_circgamma_remint_status : B1CircGammaRemintStatus :=
  B1CircGammaRemintParked.

Lemma b1_circgamma_remint_is_parked :
  b1_circgamma_remint_status = B1CircGammaRemintParked.
Proof.
  reflexivity.
Qed.

Lemma b1_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

Lemma b1_rest_parked :
  phase_b_compound_curve_status = PhaseBRequiredGap
  /\ phase_b_curve_polygon_status = PhaseBRequiredGap
  /\ b1_hperp_status = B1HperpParked
  /\ b1_sql_mm_status = B1SqlMmNotDone
  /\ b1_circgamma_remint_status = B1CircGammaRemintParked
  /\ cook_loop_status = LoopObligation.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b1_joint_qed_or_qex","title":"Phase B.1 forall CS concat joint is I_ok_circ Hit at (end, 1, 0) (QED) or a joint declines I_ok_circ (QEX); discharged QED; sidecar reuse of arc_gamma / I_ok_circ; no new kernel","file":"theories/CircularCookCsConcat.v","witness":"0007-B.1-cs-concat-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b1_joint_qed_or_qex :
  ((forall a b,
      cs_joint a b -> I_ok_circ a b (cs_joint_hit a b))
   /\ CircEgg = CircularArc)
  \/
  (exists a b, cs_joint a b /\ I_ok_circ a b IDecline).
Proof.
  left.
  split; [exact cs_joint_I_ok_circ|].
  reflexivity.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b1_not_interior_qed_or_qex","title":"Phase B.1 joint params are not interior and locked 2-arc CS is contiguous (QED) or the locked pair is not a joint (QEX); discharged QED; concat incidence not an interior span cook; not a kiss certificate","file":"theories/CircularCookCsConcat.v","witness":"0007-B.1-cs-concat-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b1_not_interior_qed_or_qex :
  (cs_contiguous locked_cs
   /\ I_ok_circ locked_cs_arc_1 locked_cs_arc_2
        (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
   /\ ~ interior_span_params 1 0
   /\ IHit locked_cs_joint_pt 1 0 <> IEmpty)
  \/
  ~ cs_joint locked_cs_arc_1 locked_cs_arc_2.
Proof.
  left.
  split; [exact locked_cs_contiguous|].
  split; [exact locked_cs_joint_I_ok_circ|].
  split; [exact joint_params_not_interior|].
  apply IHit_neq_IEmpty.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b1_reuse_qed_or_qex","title":"Phase B.1 reuses I_ok_circ on CircEgg with no new kernel (QED) or the locked joint declines I_ok_circ (QEX); discharged QED; CircularStringArcs is list CircEgg; not CurveSegment remint","file":"theories/CircularCookCsConcat.v","witness":"0007-B.1-cs-concat-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b1_reuse_qed_or_qex :
  (CircEgg = CircularArc
   /\ CircularStringArcs = list CircEgg
   /\ I_ok_circ locked_cs_arc_1 locked_cs_arc_2
        (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
   /\ I_ok_circ locked_cs_arc_1 locked_cs_arc_2
        (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
   /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
        (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2))
  \/
  I_ok_circ locked_cs_arc_1 locked_cs_arc_2 IDecline.
Proof.
  left.
  destruct b1_reuse_no_new_kernel as [He [Hh Ht]].
  destruct b1_I_ok_circ_hit_not_host_I_ok as [Hh2 Hhost].
  split; [exact He|].
  split; [exact Ht|].
  split; [exact Hh|].
  split; [exact Hh2|].
  exact Hhost.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b1_host_qed_or_qex","title":"Phase B.1 discharges CircGamma and expands first cook (QED) or CircGamma stays QEX and first cook stays chord-chord (QEX); discharged QEX; host circular I_ok is Decline; I_ok_circ joint Hit is not host I_ok","file":"theories/CircularCookCsConcat.v","witness":"0007-B.1-cs-concat-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b1_host_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ exists p ti tj,
        I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
             (IHit p ti tj))
  \/
  (circular_gamma_status = CircGammaQEX
   /\ ~ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggChord EggChord
   /\ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
              (IHit p ti tj))
   /\ I_ok_circ locked_cs_arc_1 locked_cs_arc_2
        (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
   /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
        (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)).
Proof.
  right.
  destruct b1_host_stays_qex as [Hq [Hn [Hc [Hd Hf]]]].
  destruct b1_I_ok_circ_hit_not_host_I_ok as [Hhit Hhost].
  split; [exact Hq|].
  split; [exact Hn|].
  split; [exact Hc|].
  split; [exact Hd|].
  split; [exact Hf|].
  split; [exact Hhit|].
  exact Hhost.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b1_park_qed_or_qex","title":"Phase B.1 discharges CompoundCurve, CurvePolygon, Hperp, CircGamma remint, and SQL/MM (QED) or names them parked / not-done (QEX); discharged QEX; B.1 landed; not SQL/MM done","file":"theories/CircularCookCsConcat.v","witness":"0007-B.1-cs-concat-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b1_park_qed_or_qex :
  (phase_b_compound_curve_status = PhaseBRequiredLanded
   /\ phase_b_curve_polygon_status = PhaseBRequiredLanded
   /\ b1_hperp_status = B1HperpDischarged
   /\ b1_circgamma_remint_status = B1CircGammaReminted
   /\ b1_sql_mm_status = B1SqlMmDone
   /\ cook_loop_status = LoopDischarged)
  \/
  (phase_b1_status = PhaseB1Landed
   /\ phase_b_compound_curve_status = PhaseBRequiredGap
   /\ phase_b_curve_polygon_status = PhaseBRequiredGap
   /\ b1_hperp_status = B1HperpParked
   /\ b1_circgamma_remint_status = B1CircGammaRemintParked
   /\ b1_sql_mm_status = B1SqlMmNotDone
   /\ cook_loop_status = LoopObligation).
Proof.
  right.
  split; [exact phase_b1_is_landed|].
  exact b1_rest_parked.
Qed.

Print Assumptions b1_host_circgamma_qex.
Print Assumptions cs_joint_I_ok_circ.
Print Assumptions joint_params_not_interior.
Print Assumptions locked_cs_joint.
Print Assumptions locked_cs_contiguous.
Print Assumptions locked_cs_joint_I_ok_circ.
Print Assumptions b1_reuse_no_new_kernel.
Print Assumptions b1_I_ok_circ_hit_not_host_I_ok.
Print Assumptions b1_not_bag_noder.
Print Assumptions phase_b1_is_landed.
Print Assumptions phase_b_cc_is_gap.
Print Assumptions phase_b_cp_is_gap.
Print Assumptions b1_sql_mm_is_not_done.
Print Assumptions ticket_0007_b1_joint_qed_or_qex.
Print Assumptions ticket_0007_b1_not_interior_qed_or_qex.
Print Assumptions ticket_0007_b1_reuse_qed_or_qex.
Print Assumptions ticket_0007_b1_host_qed_or_qex.
Print Assumptions ticket_0007_b1_park_qed_or_qex.
