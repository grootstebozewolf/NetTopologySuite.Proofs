(* ============================================================================
   NetTopologySuite.Proofs.CircularCookCpConcat
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Phase B.3 — CurvePolygon ring closure
   for SQL/MM Part 3 required-type glossary 𝓘 (sidecar / host reuse).

   B.2 unparked CompoundCurve joints only and left ring closure as
   CP. This letter unparks **CurvePolygon rings only**. A CurvePolygon
   ring is a closed CircularString or a closed CompoundCurve — the
   SQL/MM Part 3 required-type reading already used in II.4 / B.1 /
   B.2 fences (ring of CircularString / CompoundCurve members). The
   carrier is B.2 CompoundCurveMembers (CcLS | CcCS) that is
   contiguous and closed (last member joins first). A one-member
   [CcCS arcs] is a CS ring. A mixed / multi-member list is a CC
   ring. Not a remint of CurveSegment / CurveGeometry.CurvePolygon
   (year-1 CSChord|CSArc). Not holes-inside-shell (CurvePolygonValid).
   Not G¹ / H⊥.

   Reuse, not a new kernel:
     Sequential member joints stay B.2 (LS–LS host I_ok Hit;
     CS–CS I_ok_circ; mixed I_ok_mixed).
     Closing joint (last to first) uses the same cooks:
       CS–CS closing is I_ok_circ Hit at (arc_end, tᵢ=1, tⱼ=0)
       via B.1 cs_joint / arc_gamma.
       LS–LS closing is host I_ok Hit at (ce_p1, tᵢ=1, tⱼ=0)
       via chord_eval (first cook).
       Mixed closing is sidecar I_ok_mixed Hit at
       (arc_end, tᵢ=1, tⱼ=0) via SidecarCircMixed. Host I_ok
       mixed stays Decline (I.1); I_ok_mixed Hit ≠ host I_ok.
     Concat / ring-close incidence is already a hen, not an
     interior span cook and not a CRV-TOUCH kiss certificate.

   Locked CS-ring fixture (SQL/MM-canonical CS shell):
     CURVEPOLYGON((CIRCULARSTRING(-5 0, 0 5, 5 0, 0 -5, -5 0)))
   as one CcCS of B.1's V-CS arcs. Sequential CS joints are B.1.
   Closing joint at (-5,0): last arc end = first arc start.
   Locked mixed-ring fixture (type-distinct — cannot be a CS):
     CURVEPOLYGON((COMPOUNDCURVE((-5 0, 5 0),
       CIRCULARSTRING(5 0, 0 -5, -5 0))))
   Sequential mixed joint is B.2 I_ok_mixed Hit at (5,0). Closing
   mixed joint is I_ok_mixed Hit at (-5,0). Host I_ok mixed stays
   Decline. Hole-free shells; holes are the same ring type (not
   a new cook).

   QED: locked CS / mixed rings are contiguous and closed; CS
   closing is I_ok_circ Hit at (end, 1, 0); mixed closing is
   I_ok_mixed Hit at (end, 1, 0); host I_ok mixed stays Decline;
   joint params are not interior; hole-free CPs inhabit; reuse
   B.1 / B.2 / SidecarCircMixed — no new kernel.
   QEX: host CircGamma stays QEX; first cook stays chord–chord;
   host circular I_ok is Decline; I_ok_circ / I_ok_mixed Hit ≠
   host I_ok; H⊥ / CircGamma remint / bag-noder / interior mixed
   cook stay parked; SQL/MM is not done (cathedral / Multi /
   optional Part 3 types). CurvePolygon required-type status is
   Landed — mixed LS–CS closing inhabits I_ok_mixed (not host
   I_ok). CompoundCurve required-type is Landed. Phase B stays
   Open. Letter B.3 landed (PhaseB3Landed) ≠ SQL/MM done /
   Phase B done-when. Letter enum vs required-type stay distinct.

   Honesty fences:
     Host-Decline / CircGamma-QEX at the top of this module.
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ span filter ≠
     span split ≠ I_ok_circ ≠ CS concat joint ≠ CC member joint ≠
     CP ring-close joint ≠ glossary I_gloss / host I_ok.
     I_ok_mixed Hit is licensed for concat / ring-close joints
     only. Sidecar ≠ host try_cook_hit / host I_ok. Closing
     joint is ring-close incidence, not an interior span cook
     and not a CRV-TOUCH kiss certificate. Interior mixed cook
     stays parked.
     Not first cook scope. Not a bag noder. Not ArcSplitAtNode.
     Not G¹ / H⊥. Not holes-inside-shell. Not MultiCurve.
     Not a remint of CurveSegment / CurveGeometry.CurvePolygon /
     Exact* / Dart / Hobby / leftover_width / ArcSplitAtNode
     leftover-width / host circ_split / CircularStringValid /
     CompoundCurveKoc family.
     Do not fake atan2-free host γ. Do not expand first_cook_scope.
     Do not start H⊥ / a CRV-TOUCH kiss procedure / CircGamma
     remint / full SQL/MM cathedral. No MerkatorBV.
     No new kernel. Not SQL/MM done.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-B.3-cp-ring-closure
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via CircularCookCcConcat /
     CircularCookCsConcat / CircularCookOkCirc). Category C
     audit-exception: same atan2 lineage as B.2; no extra axioms.
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
From NTS.Proofs Require CircularCookCsConcat.
From NTS.Proofs Require CircularCookCcConcat.
From NTS.Proofs Require SidecarCircMixed.
Import ListNotations.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=B.3 claim=0007
   file=theories/CircularCookCpConcat.v
   kind=QED-or-QEX-cp-ring-closure-sidecar-host-reuse
   gamma=arc-span-not-gamma-full
   reuse=I_ok_circ,I_ok_mixed,arc_gamma,cs_joint,cc_joint,host-I_ok-chord-chord
   not=new-kernel,CircGamma-Discharge,first-cook-noding,SQL-MM-done
   not=bag-noder,CRV-TOUCH-kiss,CurveSegment-remint,CurvePolygon-remint
   park=Hperp,CircGamma-remint,bag-noder,SQL-MM-done,interior-mixed-cook
   land=Phase-B.3,Phase-B-CC-CP-required-type *)

(* B.1 / B.2 names, reused. Not imported so this letter can mark
   PhaseB3Landed without clashing B.2's letter-local Gap.
   Required-type CP / CC are Landed (mixed LS–CS inhabits
   I_ok_mixed). Phase B stays Open. *)
Definition cs_joint := CircularCookCsConcat.cs_joint.
Definition cs_joint_hit := CircularCookCsConcat.cs_joint_hit.
Definition locked_cs_arc_1 := CircularCookCsConcat.locked_cs_arc_1.
Definition locked_cs_arc_2 := CircularCookCsConcat.locked_cs_arc_2.
Definition ls_joint := CircularCookCcConcat.ls_joint.
Definition ls_joint_hit := CircularCookCcConcat.ls_joint_hit.
Definition CcLS := CircularCookCcConcat.CcLS.
Definition CcCS := CircularCookCcConcat.CcCS.
Definition cc_joint := CircularCookCcConcat.cc_joint.
Definition cc_contiguous := CircularCookCcConcat.cc_contiguous.
Definition cc_start := CircularCookCcConcat.cc_start.
Definition cc_end := CircularCookCcConcat.cc_end.
Definition locked_cc_ls := CircularCookCcConcat.locked_cc_ls.
Definition locked_cc_cs := CircularCookCcConcat.locked_cc_cs.
Definition locked_cc_mixed := CircularCookCcConcat.locked_cc_mixed.
Definition interior_span_params :=
  CircularCookCcConcat.interior_span_params.

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma b3_host_circgamma_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  exact circular_gamma_is_qex.
Qed.

Lemma b3_host_not_first_cook :
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_not_first_cook_scope.
Qed.

Lemma b3_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma b3_host_circular_decline :
  I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact circular_decline_I_ok.
Qed.

Lemma b3_host_circular_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
         (IHit p ti tj).
Proof.
  exact circular_hit_not_I_ok.
Qed.

Lemma b3_mixed_not_first_cook :
  ~ first_cook_scope EggChord EggCircularArc.
Proof.
  exact chord_circular_not_first_cook_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* CurvePolygon ring = closed B.2 members. SQL/MM: CS or CC ring.             *)
(* Not CurveSegment / CurveGeometry.CurvePolygon (do not remint).             *)
(* -------------------------------------------------------------------------- *)

Definition CpRing : Type := CircularCookCcConcat.CompoundCurveMembers.

Definition cp_ring_closed (r : CpRing) : Prop :=
  match r with
  | [] => False
  | a :: _ =>
      match CircularCookCcConcat.last_of r with
      | Some z => cc_joint z a
      | None => False
      end
  end.

Definition cp_ring_ok (r : CpRing) : Prop :=
  r <> [] /\ cc_contiguous r /\ cp_ring_closed r.

Record CpPoly : Type := mkCpPoly {
  cp_shell : CpRing;
  cp_holes : list CpRing
}.

Definition cp_poly_ok (cp : CpPoly) : Prop :=
  cp_ring_ok (cp_shell cp) /\ Forall cp_ring_ok (cp_holes cp).

(* -------------------------------------------------------------------------- *)
(* Closing joints. Reuse B.1 I_ok_circ / B.2 host I_ok. No new cook.          *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"cp_closing_cs_cs_I_ok_circ","title":"Phase B.3 forall CS-CS CurvePolygon closing joint reuses I_ok_circ Hit at (end, 1, 0); B.1 cs_joint; ring-close incidence; no new kernel","file":"theories/CircularCookCpConcat.v","witness":"0007-B.3-cp-ring-closure","board":"ADR-0007"} *)

Theorem cp_closing_cs_cs_I_ok_circ :
  forall a b : CircEgg,
    cs_joint a b -> I_ok_circ a b (cs_joint_hit a b).
Proof.
  exact CircularCookCsConcat.cs_joint_I_ok_circ.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"cp_closing_ls_ls_I_ok","title":"Phase B.3 forall LS-LS CurvePolygon closing joint is host I_ok Hit at (ce_p1, t=1, t=0) via chord_eval; first cook reuse; no new kernel","file":"theories/CircularCookCpConcat.v","witness":"0007-B.3-cp-ring-closure","board":"ADR-0007"} *)

Theorem cp_closing_ls_ls_I_ok :
  forall c1 c2 : ChordEgg,
    ls_joint c1 c2 -> I_ok (MkChord c1) (MkChord c2) (ls_joint_hit c1 c2).
Proof.
  exact CircularCookCcConcat.ls_joint_I_ok.
Qed.

Definition cs_ls_joint := SidecarCircMixed.cs_ls_joint.
Definition cs_ls_joint_hit := SidecarCircMixed.cs_ls_joint_hit.
Definition I_ok_mixed := SidecarCircMixed.I_ok_mixed.
Definition MixCsLs := SidecarCircMixed.MixCsLs.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"cp_closing_mixed_cs_ls_I_ok_mixed","title":"Phase B.3 forall CS-LS CurvePolygon closing joint is I_ok_mixed Hit at (arc_end, t=1, t=0); SidecarCircMixed reuse; host I_ok mixed stays Decline; ring-close incidence; no interior arc-chord cook","file":"theories/CircularCookCpConcat.v","witness":"0007-B.3-cp-ring-closure","board":"ADR-0007"} *)

Theorem cp_closing_mixed_cs_ls_I_ok_mixed :
  forall a c,
    cs_ls_joint a c ->
    I_ok_mixed (MixCsLs a c) (cs_ls_joint_hit a c).
Proof.
  exact SidecarCircMixed.cs_ls_joint_I_ok_mixed.
Qed.

Lemma cp_closing_mixed_ls_cs_host_decline :
  forall c,
    I_ok (MkChord c) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact CircularCookCcConcat.cc_mixed_ls_cs_host_decline.
Qed.

Lemma cp_closing_mixed_cs_ls_host_decline :
  forall c,
    I_ok (MkOutOfScope EggCircularArc) (MkChord c) IDecline.
Proof.
  exact CircularCookCcConcat.cc_mixed_cs_ls_host_decline.
Qed.

Lemma cp_closing_mixed_cs_ls_hit_not_I_ok :
  forall c p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkChord c) (IHit p ti tj).
Proof.
  exact CircularCookCcConcat.cc_mixed_cs_ls_hit_not_I_ok.
Qed.

Lemma cp_closing_mixed_ls_cs_hit_not_I_ok :
  forall c p ti tj,
    ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) (IHit p ti tj).
Proof.
  exact CircularCookCcConcat.cc_mixed_ls_cs_hit_not_I_ok.
Qed.

Lemma joint_params_not_interior :
  ~ interior_span_params 1 0.
Proof.
  exact CircularCookCsConcat.joint_params_not_interior.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked CS-ring CurvePolygon (one closed CircularString shell).             *)
(* -------------------------------------------------------------------------- *)

Definition locked_cp_cs_ring : CpRing :=
  [CcCS [locked_cs_arc_1; locked_cs_arc_2]].

Definition locked_cp_cs_close_pt : Point := mkPoint (-5) 0.

Definition locked_cp_cs : CpPoly :=
  mkCpPoly locked_cp_cs_ring [].

Lemma locked_cp_cs_ring_nonempty :
  locked_cp_cs_ring <> [].
Proof.
  discriminate.
Qed.

Lemma locked_cp_cs_ring_contiguous :
  cc_contiguous locked_cp_cs_ring.
Proof.
  unfold locked_cp_cs_ring, cc_contiguous, CircularCookCcConcat.cc_contiguous.
  exact I.
Qed.

Lemma locked_cp_cs_ring_closed :
  cp_ring_closed locked_cp_cs_ring.
Proof.
  unfold locked_cp_cs_ring, cp_ring_closed, cc_joint,
    CircularCookCcConcat.cc_joint, CircularCookCcConcat.cc_end,
    CircularCookCcConcat.cc_start, CircularCookCcConcat.last_of,
    locked_cs_arc_1, locked_cs_arc_2,
    CircularCookCsConcat.locked_cs_arc_1,
    CircularCookCsConcat.locked_cs_arc_2.
  cbn [arc_start arc_end].
  reflexivity.
Qed.

Lemma locked_cp_cs_ring_ok :
  cp_ring_ok locked_cp_cs_ring.
Proof.
  unfold cp_ring_ok.
  split; [exact locked_cp_cs_ring_nonempty|].
  split; [exact locked_cp_cs_ring_contiguous|].
  exact locked_cp_cs_ring_closed.
Qed.

Lemma locked_cp_cs_ok :
  cp_poly_ok locked_cp_cs.
Proof.
  unfold locked_cp_cs, cp_poly_ok.
  split; [exact locked_cp_cs_ring_ok|].
  constructor.
Qed.

Lemma locked_cp_cs_closing_joint :
  cs_joint locked_cs_arc_2 locked_cs_arc_1.
Proof.
  unfold cs_joint, CircularCookCsConcat.cs_joint,
    locked_cs_arc_1, locked_cs_arc_2.
  split; [exact CircularCookCsConcat.locked_cs_arc_2_valid|].
  split; [exact CircularCookCsConcat.locked_cs_arc_1_valid|].
  reflexivity.
Qed.

Lemma locked_cp_cs_closing_I_ok_circ :
  I_ok_circ locked_cs_arc_2 locked_cs_arc_1
    (cs_joint_hit locked_cs_arc_2 locked_cs_arc_1).
Proof.
  apply cp_closing_cs_cs_I_ok_circ.
  exact locked_cp_cs_closing_joint.
Qed.

Lemma locked_cp_cs_close_pt_eq :
  arc_end locked_cs_arc_2 = locked_cp_cs_close_pt.
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked mixed-ring CurvePolygon (closed CompoundCurve shell).               *)
(* -------------------------------------------------------------------------- *)

Definition locked_cp_mixed_ring : CpRing := locked_cc_mixed.

Definition locked_cp_mixed : CpPoly :=
  mkCpPoly locked_cp_mixed_ring [].

Lemma locked_cp_mixed_ring_nonempty :
  locked_cp_mixed_ring <> [].
Proof.
  unfold locked_cp_mixed_ring, locked_cc_mixed,
    CircularCookCcConcat.locked_cc_mixed.
  discriminate.
Qed.

Lemma locked_cp_mixed_ring_contiguous :
  cc_contiguous locked_cp_mixed_ring.
Proof.
  unfold locked_cp_mixed_ring, locked_cc_mixed.
  exact CircularCookCcConcat.locked_cc_mixed_contiguous.
Qed.

Lemma locked_cp_mixed_ring_closed :
  cp_ring_closed locked_cp_mixed_ring.
Proof.
  unfold locked_cp_mixed_ring, locked_cc_mixed,
    CircularCookCcConcat.locked_cc_mixed, cp_ring_closed, cc_joint,
    CircularCookCcConcat.cc_joint, CircularCookCcConcat.cc_end,
    CircularCookCcConcat.cc_start, CircularCookCcConcat.last_of,
    locked_cc_ls, locked_cc_cs,
    CircularCookCcConcat.locked_cc_ls,
    CircularCookCcConcat.locked_cc_cs,
    locked_cs_arc_2, CircularCookCsConcat.locked_cs_arc_2.
  cbn [ce_p0 ce_p1 arc_start arc_end].
  reflexivity.
Qed.

Lemma locked_cp_mixed_ring_ok :
  cp_ring_ok locked_cp_mixed_ring.
Proof.
  unfold cp_ring_ok.
  split; [exact locked_cp_mixed_ring_nonempty|].
  split; [exact locked_cp_mixed_ring_contiguous|].
  exact locked_cp_mixed_ring_closed.
Qed.

Lemma locked_cp_mixed_ok :
  cp_poly_ok locked_cp_mixed.
Proof.
  unfold locked_cp_mixed, cp_poly_ok.
  split; [exact locked_cp_mixed_ring_ok|].
  constructor.
Qed.

Lemma locked_cp_mixed_closing_joint :
  cs_ls_joint locked_cc_cs locked_cc_ls.
Proof.
  unfold cs_ls_joint, SidecarCircMixed.cs_ls_joint,
    locked_cc_ls, locked_cc_cs.
  split; [exact CircularCookCsConcat.locked_cs_arc_2_valid|].
  reflexivity.
Qed.

Lemma locked_cp_mixed_closing_I_ok_mixed :
  I_ok_mixed (MixCsLs locked_cc_cs locked_cc_ls)
    (cs_ls_joint_hit locked_cc_cs locked_cc_ls).
Proof.
  apply cp_closing_mixed_cs_ls_I_ok_mixed.
  exact locked_cp_mixed_closing_joint.
Qed.

Lemma locked_cp_mixed_closing_decline :
  I_ok (MkOutOfScope EggCircularArc) (MkChord locked_cc_ls) IDecline.
Proof.
  apply cp_closing_mixed_cs_ls_host_decline.
Qed.

Lemma locked_cp_mixed_closing_hit_not_I_ok :
  ~ I_ok (MkOutOfScope EggCircularArc) (MkChord locked_cc_ls)
       (IHit locked_cp_cs_close_pt 1 0).
Proof.
  apply cp_closing_mixed_cs_ls_hit_not_I_ok.
Qed.

Lemma locked_cp_mixed_is_mixed :
  CircularCookCcConcat.cc_mixed_pair
    (CcLS [locked_cc_ls]) (CcCS [locked_cc_cs]).
Proof.
  exact CircularCookCcConcat.locked_cc_mixed_is_mixed.
Qed.

(* -------------------------------------------------------------------------- *)
(* Reuse: no new kernel. CpRing is B.2 members; cooks stay B.1 / B.2.         *)
(* -------------------------------------------------------------------------- *)

Lemma b3_reuse_no_new_kernel :
  CircEgg = CircularArc
  /\ CpRing = CircularCookCcConcat.CompoundCurveMembers
  /\ I_ok_circ locked_cs_arc_2 locked_cs_arc_1
       (cs_joint_hit locked_cs_arc_2 locked_cs_arc_1)
  /\ I_ok_mixed (MixCsLs locked_cc_cs locked_cc_ls)
       (cs_ls_joint_hit locked_cc_cs locked_cc_ls)
  /\ I_ok (MkOutOfScope EggCircularArc) (MkChord locked_cc_ls) IDecline
  /\ cp_poly_ok locked_cp_cs
  /\ cp_poly_ok locked_cp_mixed.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact locked_cp_cs_closing_I_ok_circ|].
  split; [exact locked_cp_mixed_closing_I_ok_mixed|].
  split; [exact locked_cp_mixed_closing_decline|].
  split; [exact locked_cp_cs_ok|].
  exact locked_cp_mixed_ok.
Qed.

Lemma b3_host_stays_qex :
  circular_gamma_status = CircGammaQEX
  /\ ~ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggChord EggChord
  /\ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline
  /\ (forall p ti tj,
        ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
             (IHit p ti tj))
  /\ ~ first_cook_scope EggChord EggCircularArc.
Proof.
  split; [exact b3_host_circgamma_qex|].
  split; [exact b3_host_not_first_cook|].
  split; [exact b3_first_cook_stays_chord_chord|].
  split; [exact b3_host_circular_decline|].
  split; [exact b3_host_circular_hit_false|].
  exact b3_mixed_not_first_cook.
Qed.

Lemma b3_I_ok_circ_hit_not_host_I_ok :
  I_ok_circ locked_cs_arc_2 locked_cs_arc_1
    (cs_joint_hit locked_cs_arc_2 locked_cs_arc_1)
  /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
       (cs_joint_hit locked_cs_arc_2 locked_cs_arc_1).
Proof.
  split; [exact locked_cp_cs_closing_I_ok_circ|].
  unfold cs_joint_hit, CircularCookCsConcat.cs_joint_hit.
  apply circular_hit_not_I_ok.
Qed.

(* -------------------------------------------------------------------------- *)
(* Phase B.3 letter landed. CP / CC required-type Landed (mixed
   I_ok_mixed Hit). Phase B stays Open. H⊥ / remint / bag /
   interior mixed cook / SQL/MM stay parked. Letter landed ≠
   SQL/MM done / Phase B done-when. Letter enum vs required-type
   stay distinct.                                                   *)
(* -------------------------------------------------------------------------- *)

Inductive PhaseB3Status : Type :=
| PhaseB3Landed
| PhaseB3Parked.

Definition phase_b3_status : PhaseB3Status := PhaseB3Landed.

Lemma phase_b3_is_landed :
  phase_b3_status = PhaseB3Landed.
Proof.
  reflexivity.
Qed.

Inductive PhaseBGapStatus : Type :=
| PhaseBRequiredGap
| PhaseBRequiredLanded.

(* Mixed LS–CS inhabits I_ok_mixed. CC / CP required-type Landed.
   CS stays Gap (B.1 joints are I_ok_circ; not reminted here).
   Phase B campaign stays Open. Letter enum vs required-type
   stay distinct. *)
Definition phase_b_circular_string_status : PhaseBGapStatus :=
  PhaseBRequiredGap.

Definition phase_b_compound_curve_status : PhaseBGapStatus :=
  PhaseBRequiredLanded.

Definition phase_b_curve_polygon_status : PhaseBGapStatus :=
  PhaseBRequiredLanded.

Lemma phase_b_cs_is_gap :
  phase_b_circular_string_status = PhaseBRequiredGap.
Proof.
  reflexivity.
Qed.

Lemma phase_b_cc_is_landed :
  phase_b_compound_curve_status = PhaseBRequiredLanded.
Proof.
  reflexivity.
Qed.

Lemma phase_b_cp_is_landed :
  phase_b_curve_polygon_status = PhaseBRequiredLanded.
Proof.
  reflexivity.
Qed.

Inductive PhaseBCampaignStatus : Type :=
| PhaseBLanded
| PhaseBOpen.

Definition phase_b_status : PhaseBCampaignStatus := PhaseBOpen.

Lemma phase_b_is_open :
  phase_b_status = PhaseBOpen.
Proof.
  reflexivity.
Qed.

Inductive B3HperpStatus : Type :=
| B3HperpDischarged
| B3HperpParked.

Definition b3_hperp_status : B3HperpStatus := B3HperpParked.

Lemma b3_hperp_is_parked :
  b3_hperp_status = B3HperpParked.
Proof.
  reflexivity.
Qed.

Inductive B3SqlMmStatus : Type :=
| B3SqlMmDone
| B3SqlMmNotDone.

Definition b3_sql_mm_status : B3SqlMmStatus := B3SqlMmNotDone.

Lemma b3_sql_mm_is_not_done :
  b3_sql_mm_status = B3SqlMmNotDone.
Proof.
  reflexivity.
Qed.

Inductive B3CircGammaRemintStatus : Type :=
| B3CircGammaReminted
| B3CircGammaRemintParked.

Definition b3_circgamma_remint_status : B3CircGammaRemintStatus :=
  B3CircGammaRemintParked.

Lemma b3_circgamma_remint_is_parked :
  b3_circgamma_remint_status = B3CircGammaRemintParked.
Proof.
  reflexivity.
Qed.

Lemma b3_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

Lemma b3_rest_parked :
  phase_b3_status = PhaseB3Landed
  /\ phase_b_circular_string_status = PhaseBRequiredGap
  /\ phase_b_compound_curve_status = PhaseBRequiredLanded
  /\ phase_b_curve_polygon_status = PhaseBRequiredLanded
  /\ phase_b_status = PhaseBOpen
  /\ b3_hperp_status = B3HperpParked
  /\ b3_circgamma_remint_status = B3CircGammaRemintParked
  /\ b3_sql_mm_status = B3SqlMmNotDone
  /\ cook_loop_status = LoopObligation.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b3_closed_qed_or_qex","title":"Phase B.3 locked CS and mixed CurvePolygon rings are closed and contiguous; CS closing is I_ok_circ Hit; mixed closing is I_ok_mixed Hit at (end, 1, 0); host I_ok mixed stays Decline (QED) or a locked ring is not closed (QEX); discharged QED; ring-close incidence; SidecarCircMixed reuse; I.1 fence on host I_ok; not a constructed interior mixed Hit","file":"theories/CircularCookCpConcat.v","witness":"0007-B.3-cp-ring-closure","board":"ADR-0007"} *)

Theorem ticket_0007_b3_closed_qed_or_qex :
  (cp_ring_ok locked_cp_cs_ring
   /\ cp_ring_ok locked_cp_mixed_ring
   /\ I_ok_circ locked_cs_arc_2 locked_cs_arc_1
        (cs_joint_hit locked_cs_arc_2 locked_cs_arc_1)
   /\ I_ok_mixed (MixCsLs locked_cc_cs locked_cc_ls)
        (cs_ls_joint_hit locked_cc_cs locked_cc_ls)
   /\ I_ok (MkOutOfScope EggCircularArc) (MkChord locked_cc_ls) IDecline
   /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkChord locked_cc_ls)
          (IHit locked_cp_cs_close_pt 1 0)
   /\ IDecline <> IEmpty)
  \/
  ~ cp_ring_closed locked_cp_cs_ring.
Proof.
  left.
  split; [exact locked_cp_cs_ring_ok|].
  split; [exact locked_cp_mixed_ring_ok|].
  split; [exact locked_cp_cs_closing_I_ok_circ|].
  split; [exact locked_cp_mixed_closing_I_ok_mixed|].
  split; [exact locked_cp_mixed_closing_decline|].
  split; [exact locked_cp_mixed_closing_hit_not_I_ok|].
  discriminate.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b3_reuse_qed_or_qex","title":"Phase B.3 closing joints reuse B.1 I_ok_circ, B.2 host I_ok, and SidecarCircMixed I_ok_mixed; CpRing is B.2 members (QED) or a locked closing declines (QEX); discharged QED; no new kernel; not CurveSegment remint; not CurveGeometry.CurvePolygon remint","file":"theories/CircularCookCpConcat.v","witness":"0007-B.3-cp-ring-closure","board":"ADR-0007"} *)

Theorem ticket_0007_b3_reuse_qed_or_qex :
  (CircEgg = CircularArc
   /\ CpRing = CircularCookCcConcat.CompoundCurveMembers
   /\ (forall a b, cs_joint a b -> I_ok_circ a b (cs_joint_hit a b))
   /\ (forall c1 c2, ls_joint c1 c2 ->
         I_ok (MkChord c1) (MkChord c2) (ls_joint_hit c1 c2))
   /\ (forall a c, cs_ls_joint a c ->
         I_ok_mixed (MixCsLs a c) (cs_ls_joint_hit a c))
   /\ I_ok_circ locked_cs_arc_2 locked_cs_arc_1
        (cs_joint_hit locked_cs_arc_2 locked_cs_arc_1)
   /\ I_ok_mixed (MixCsLs locked_cc_cs locked_cc_ls)
        (cs_ls_joint_hit locked_cc_cs locked_cc_ls)
   /\ I_ok (MkOutOfScope EggCircularArc) (MkChord locked_cc_ls) IDecline
   /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
        (cs_joint_hit locked_cs_arc_2 locked_cs_arc_1))
  \/
  I_ok_circ locked_cs_arc_2 locked_cs_arc_1 IDecline.
Proof.
  left.
  destruct b3_I_ok_circ_hit_not_host_I_ok as [Hh Hhost].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact cp_closing_cs_cs_I_ok_circ|].
  split; [exact cp_closing_ls_ls_I_ok|].
  split; [exact cp_closing_mixed_cs_ls_I_ok_mixed|].
  split; [exact Hh|].
  split; [exact locked_cp_mixed_closing_I_ok_mixed|].
  split; [exact locked_cp_mixed_closing_decline|].
  exact Hhost.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b3_not_interior_qed_or_qex","title":"Phase B.3 closing params are not interior and locked hole-free CurvePolygons inhabit (QED) or a locked ring is not closed (QEX); discharged QED; ring-close incidence not an interior span cook; not a kiss certificate","file":"theories/CircularCookCpConcat.v","witness":"0007-B.3-cp-ring-closure","board":"ADR-0007"} *)

Theorem ticket_0007_b3_not_interior_qed_or_qex :
  (cp_poly_ok locked_cp_cs
   /\ cp_poly_ok locked_cp_mixed
   /\ cp_ring_closed locked_cp_cs_ring
   /\ cp_ring_closed locked_cp_mixed_ring
   /\ ~ interior_span_params 1 0
   /\ IHit locked_cp_cs_close_pt 1 0 <> IEmpty)
  \/
  ~ cp_ring_closed locked_cp_mixed_ring.
Proof.
  left.
  split; [exact locked_cp_cs_ok|].
  split; [exact locked_cp_mixed_ok|].
  split; [exact locked_cp_cs_ring_closed|].
  split; [exact locked_cp_mixed_ring_closed|].
  split; [exact joint_params_not_interior|].
  apply IHit_neq_IEmpty.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b3_host_qed_or_qex","title":"Phase B.3 discharges CircGamma and expands first cook (QED) or CircGamma stays QEX and first cook stays chord-chord (QEX); discharged QEX; host circular I_ok is Decline; mixed closing Hit is not host I_ok; I_ok_circ closing Hit is not host I_ok","file":"theories/CircularCookCpConcat.v","witness":"0007-B.3-cp-ring-closure","board":"ADR-0007"} *)

Theorem ticket_0007_b3_host_qed_or_qex :
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
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ I_ok (MkOutOfScope EggCircularArc) (MkChord locked_cc_ls) IDecline
   /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkChord locked_cc_ls)
          (IHit locked_cp_cs_close_pt 1 0)
   /\ I_ok_circ locked_cs_arc_2 locked_cs_arc_1
        (cs_joint_hit locked_cs_arc_2 locked_cs_arc_1)
   /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
        (cs_joint_hit locked_cs_arc_2 locked_cs_arc_1)).
Proof.
  right.
  destruct b3_host_stays_qex as [Hq [Hn [Hc [Hd [Hf Hm]]]]].
  destruct b3_I_ok_circ_hit_not_host_I_ok as [Hhit Hhost].
  split; [exact Hq|].
  split; [exact Hn|].
  split; [exact Hc|].
  split; [exact Hd|].
  split; [exact Hf|].
  split; [exact Hm|].
  split; [exact locked_cp_mixed_closing_decline|].
  split; [exact locked_cp_mixed_closing_hit_not_I_ok|].
  split; [exact Hhit|].
  exact Hhost.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b3_park_qed_or_qex","title":"Phase B.3 discharges Hperp, CircGamma remint, bag noder, and SQL/MM (QED) or names them parked / not-done (QEX); discharged QEX; B.3 letter landed; CP CC required-type Landed (mixed I_ok_mixed Hit, not host I_ok); CS required-type Gap; Phase B Open; letter enum != SQL/MM done / Phase B done-when","file":"theories/CircularCookCpConcat.v","witness":"0007-B.3-cp-ring-closure","board":"ADR-0007"} *)

Theorem ticket_0007_b3_park_qed_or_qex :
  (b3_hperp_status = B3HperpDischarged
   /\ b3_circgamma_remint_status = B3CircGammaReminted
   /\ b3_sql_mm_status = B3SqlMmDone
   /\ cook_loop_status = LoopDischarged)
  \/
  (phase_b3_status = PhaseB3Landed
   /\ phase_b_circular_string_status = PhaseBRequiredGap
   /\ phase_b_compound_curve_status = PhaseBRequiredLanded
   /\ phase_b_curve_polygon_status = PhaseBRequiredLanded
   /\ phase_b_status = PhaseBOpen
   /\ b3_hperp_status = B3HperpParked
   /\ b3_circgamma_remint_status = B3CircGammaRemintParked
   /\ b3_sql_mm_status = B3SqlMmNotDone
   /\ cook_loop_status = LoopObligation).
Proof.
  right.
  exact b3_rest_parked.
Qed.

Print Assumptions b3_host_circgamma_qex.
Print Assumptions cp_closing_cs_cs_I_ok_circ.
Print Assumptions cp_closing_ls_ls_I_ok.
Print Assumptions cp_closing_mixed_cs_ls_host_decline.
Print Assumptions cp_closing_mixed_cs_ls_I_ok_mixed.
Print Assumptions locked_cp_cs_ring_closed.
Print Assumptions locked_cp_cs_ok.
Print Assumptions locked_cp_cs_closing_I_ok_circ.
Print Assumptions locked_cp_mixed_ring_closed.
Print Assumptions locked_cp_mixed_ok.
Print Assumptions locked_cp_mixed_closing_I_ok_mixed.
Print Assumptions locked_cp_mixed_closing_decline.
Print Assumptions b3_reuse_no_new_kernel.
Print Assumptions b3_I_ok_circ_hit_not_host_I_ok.
Print Assumptions b3_not_bag_noder.
Print Assumptions phase_b3_is_landed.
Print Assumptions phase_b_cs_is_gap.
Print Assumptions phase_b_cc_is_landed.
Print Assumptions phase_b_cp_is_landed.
Print Assumptions phase_b_is_open.
Print Assumptions b3_sql_mm_is_not_done.
Print Assumptions ticket_0007_b3_closed_qed_or_qex.
Print Assumptions ticket_0007_b3_reuse_qed_or_qex.
Print Assumptions ticket_0007_b3_not_interior_qed_or_qex.
Print Assumptions ticket_0007_b3_host_qed_or_qex.
Print Assumptions ticket_0007_b3_park_qed_or_qex.
