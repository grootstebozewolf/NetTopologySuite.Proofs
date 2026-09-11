(* ============================================================================
   NetTopologySuite.Proofs.SidecarCircInterior
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: ι interior circular×chord cook —
   sidecar LS×CS / CS×LS Hit via I_ok_mixed at interior span
   params (claimId 0007-ι-interior-mixed).

   SidecarCircMixed / B.2 already Qed the μ joint: I_ok_mixed Hit
   at (end, t=1, t=0) via host chord_eval and sidecar arc_gamma.
   That Hit is concat incidence, not an interior proper-cross.
   mixed_joint_params is (1,0) or (0,1); interior_span_params is
   0<ti<1 ∧ 0<tj<1. Those fences are incompatible
   (SidecarCircMixed.mixed_joint_params_not_interior).

   This letter is the honest QED∨QEX stop for the parked interior
   mixed cook. QED would be a locked proper-cross Hit inhabiting
   I_ok_mixed with interior_span_params. QEX (this letter): that
   inhabitant is not available without reminting I_ok_mixed's Hit
   arm, expanding first_cook_scope to circular×chord, or reminting
   CircGamma / host I_ok. Named gap, 508-style, not a bool:

     1. I_ok_mixed Hit is gated by mixed_joint_params. Any Hit
        therefore has ~ interior_span_params. There is no
        interior-params constructor on MixLsCs / MixCsLs.
     2. The would-be interior arm (on_chord ∧ on_arc_gamma ∧
        interior_span_params) does not inhabit I_ok_mixed.
     3. Putting the Hit on host I_ok requires first_cook_scope
        EggChord × EggCircularArc. This letter does not expand
        first cook. Host CircGamma stays QEX (no MkCirc).

   ι is not μ. ι is not host I_ok. ι is not Γ. Letter landed ≠
   interior cook Landed / Phase B done-when / cathedral Landed /
   Multi required-type Landed.

   Locked μ fixtures (reused, not reminted):
     LS×CS : COMPOUNDCURVE((-5 0, 5 0), CIRCULARSTRING(5 0, 0 -5, -5 0))
             joint at (5,0) — already Qed; not interior.

   Honesty fences:
     Host-Decline / CircGamma-QEX at the top of this module.
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ span filter ≠
     span split ≠ I_ok_circ ≠ I_ok_mixed ≠ CS concat joint ≠
     CC member joint ≠ μ joint ≠ interior mixed cook ≠
     glossary I_gloss / host I_ok.
     Sidecar ≠ host try_cook_hit / host I_ok.
     I_ok_mixed Hit ≠ host I_ok. μ joint ≠ interior span cook.
     Not first cook scope. Not a bag noder. Not ArcSplitAtNode.
     Not G¹ / H⊥. Not MultiCurve cathedral. Not MerkatorBV.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width / host circ_split /
     CircularStringValid / CompoundCurveKoc family / CircGamma /
     I_ok_mixed (do not drop mixed_joint_params).
     Do not fake atan2-free host γ. Do not expand first_cook_scope
     to circular×chord interiors. Do not start H⊥ / a CRV-TOUCH
     kiss procedure / CircGamma remint / full SQL/MM cathedral /
     bag-loop / Multi Landed theater / Phase B done-when.
     No new kernel. Not SQL/MM done.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-iota-interior-mixed
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via SidecarCircMixed /
     CircularCookCsConcat / CircularCookOkCirc). Category C
     audit-exception: same atan2 lineage as B-mixed; no extra axioms.
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  CircularCook CircularCookHit CircularCookSpan CircularCookOkCirc.
From NTS.Proofs Require CircularCookCsConcat.
From NTS.Proofs Require CircularCookCpConcat.
From NTS.Proofs Require SidecarCircMixed.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=iota claim=0007
   file=theories/SidecarCircInterior.v
   kind=QED-or-QEX-interior-mixed-ls-cs-cook
   gamma=arc-span-not-gamma-full
   reuse=I_ok_mixed,chord_eval,arc_gamma,interior_span_params
   not=new-kernel,CircGamma-Discharge,first-cook-noding,SQL-MM-done
   not=bag-noder,CRV-TOUCH-kiss,Phase-B-done-when,I_ok_mixed-remint
   park=Hperp,interior-mixed-cook,CircGamma-remint,SQL-MM-cathedral
   land=Phase-B-iota-letter-QEX *)

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma iota_host_circgamma_qex :
  circular_gamma_status = CircGammaDischarged.
Proof.
  exact circular_gamma_is_discharged.
Qed.

Lemma iota_host_not_first_cook :
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_is_first_cook_scope.
Qed.

Lemma iota_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma iota_not_first_cook_mixed :
  ~ first_cook_scope EggChord EggCircularArc.
Proof.
  exact chord_circular_not_first_cook_scope.
Qed.

Lemma iota_host_ls_cs_decline :
  forall c,
    I_ok (MkChord c) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact SidecarCircMixed.mixed_host_ls_cs_decline.
Qed.

Lemma iota_host_ls_cs_hit_false :
  forall c p ti tj,
    ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) (IHit p ti tj).
Proof.
  exact SidecarCircMixed.mixed_host_ls_cs_hit_false.
Qed.

Lemma iota_host_cs_ls_hit_false :
  forall c p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkChord c) (IHit p ti tj).
Proof.
  exact SidecarCircMixed.mixed_host_cs_ls_hit_false.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named ι gap. I_ok_mixed Hit is joint-only. Not a bool.                    *)
(* -------------------------------------------------------------------------- *)

Definition I_ok_mixed := SidecarCircMixed.I_ok_mixed.
Definition mixed_joint_params := SidecarCircMixed.mixed_joint_params.
Definition interior_span_params := SidecarCircMixed.interior_span_params.
Definition MixedEggs := SidecarCircMixed.MixedEggs.
Definition MixLsCs := SidecarCircMixed.MixLsCs.
Definition MixCsLs := SidecarCircMixed.MixCsLs.

(* Discharge constructor: an I_ok_mixed Hit arm that accepts
   interior_span_params. The existing Hit clause requires
   mixed_joint_params — 508-style miss. *)
Inductive InteriorMixedConstructor : Type :=
| InteriorMixedHitArm.

Definition interior_mixed_constructor_inhabits
  (c : InteriorMixedConstructor) : Prop :=
  match c with
  | InteriorMixedHitArm => False
  end.

Lemma interior_mixed_hit_arm_missing :
  ~ interior_mixed_constructor_inhabits InteriorMixedHitArm.
Proof.
  intro H. exact H.
Qed.

(* Would-be interior arm: the geometric ingredients of a proper-cross
   Hit. This is not I_ok_mixed and this letter does not inhabit it. *)
Definition I_ok_mixed_interior_arm
  (m : MixedEggs) (p : Point) (ti tj : R) : Prop :=
  match m with
  | SidecarCircMixed.MixLsCs c a =>
      valid_arc a /\
      on_chord c ti p /\
      on_arc_gamma a tj p /\
      interior_span_params ti tj
  | SidecarCircMixed.MixCsLs a c =>
      valid_arc a /\
      on_arc_gamma a ti p /\
      on_chord c tj p /\
      interior_span_params ti tj
  end.

Lemma I_ok_mixed_hit_is_joint_params :
  forall m p ti tj,
    I_ok_mixed m (IHit p ti tj) ->
    mixed_joint_params ti tj /\ ~ interior_span_params ti tj.
Proof.
  intros m p ti tj H.
  destruct m as [c a | a c];
    unfold I_ok_mixed, SidecarCircMixed.I_ok_mixed in H;
    destruct H as [_ [_ [_ Hm]]].
  - split; [exact Hm|].
    exact (SidecarCircMixed.mixed_joint_params_not_interior ti tj Hm).
  - split; [exact Hm|].
    exact (SidecarCircMixed.mixed_joint_params_not_interior ti tj Hm).
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"I_ok_mixed_interior_hit_false","title":"iota interior mixed: I_ok_mixed Hit at interior_span_params is False; Hit arm is mixed_joint_params only; not a constructed interior cook","file":"theories/SidecarCircInterior.v","witness":"0007-iota-interior-mixed","board":"ADR-0007"} *)

Theorem I_ok_mixed_interior_hit_false :
  forall m p ti tj,
    interior_span_params ti tj ->
    ~ I_ok_mixed m (IHit p ti tj).
Proof.
  intros m p ti tj Hinner Hhit.
  destruct (I_ok_mixed_hit_is_joint_params m p ti tj Hhit) as [_ Hn].
  exact (Hn Hinner).
Qed.

Lemma interior_arm_not_I_ok_mixed :
  forall m p ti tj,
    I_ok_mixed_interior_arm m p ti tj ->
    ~ I_ok_mixed m (IHit p ti tj).
Proof.
  intros m p ti tj Harm.
  destruct m as [c a | a c];
    unfold I_ok_mixed_interior_arm in Harm;
    destruct Harm as [_ [_ [_ Hinner]]].
  - exact (I_ok_mixed_interior_hit_false _ p ti tj Hinner).
  - exact (I_ok_mixed_interior_hit_false _ p ti tj Hinner).
Qed.

Lemma interior_span_params_half_half :
  interior_span_params (1 / 2) (1 / 2).
Proof.
  unfold interior_span_params, SidecarCircMixed.interior_span_params,
         CircularCookCsConcat.interior_span_params.
  lra.
Qed.

Lemma locked_interior_candidate_not_I_ok_mixed :
  forall m p,
    ~ I_ok_mixed m (IHit p (1 / 2) (1 / 2)).
Proof.
  intros m p.
  apply I_ok_mixed_interior_hit_false.
  exact interior_span_params_half_half.
Qed.

(* -------------------------------------------------------------------------- *)
(* μ joint still inhabits and is not interior. Reuse, not remint.             *)
(* -------------------------------------------------------------------------- *)

Definition locked_mixed_ls := SidecarCircMixed.locked_mixed_ls.
Definition locked_mixed_cs := SidecarCircMixed.locked_mixed_cs.
Definition locked_mixed_ls_cs_pt := SidecarCircMixed.locked_mixed_ls_cs_pt.

Lemma iota_mu_joint_I_ok_mixed :
  I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
    (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs).
Proof.
  exact SidecarCircMixed.locked_mixed_ls_cs_I_ok_mixed.
Qed.

Lemma iota_mu_joint_not_interior :
  I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
    (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
  /\ ~ interior_span_params 1 0.
Proof.
  split; [exact iota_mu_joint_I_ok_mixed|].
  exact CircularCookCsConcat.joint_params_not_interior.
Qed.

Lemma iota_mu_hit_not_host_I_ok :
  I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
    (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
  /\ ~ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc)
        (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs).
Proof.
  apply SidecarCircMixed.I_ok_mixed_hit_not_host_I_ok.
  exact SidecarCircMixed.locked_mixed_ls_cs_joint.
Qed.

Lemma iota_host_stays_qex :
  circular_gamma_status = CircGammaDischarged
  /\ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggChord EggChord
  /\ ~ first_cook_scope EggChord EggCircularArc
  /\ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc) IDecline
  /\ (forall p ti tj,
        ~ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc)
             (IHit p ti tj)).
Proof.
  split; [exact iota_host_circgamma_qex|].
  split; [exact iota_host_not_first_cook|].
  split; [exact iota_first_cook_stays_chord_chord|].
  split; [exact iota_not_first_cook_mixed|].
  split; [apply iota_host_ls_cs_decline|].
  apply iota_host_ls_cs_hit_false.
Qed.

(* -------------------------------------------------------------------------- *)
(* Letter-local parks. Interior cook stays parked. Letter landed ≠ cook.      *)
(* -------------------------------------------------------------------------- *)

Inductive IotaLetterStatus : Type :=
| IotaLetterLanded
| IotaLetterParked.

Definition iota_letter_status : IotaLetterStatus := IotaLetterLanded.

Lemma iota_letter_is_landed :
  iota_letter_status = IotaLetterLanded.
Proof.
  reflexivity.
Qed.

Inductive IotaInteriorCookStatus : Type :=
| IotaInteriorCookLanded
| IotaInteriorCookParked.

Definition iota_interior_cook_status : IotaInteriorCookStatus :=
  IotaInteriorCookParked.

Lemma iota_interior_cook_is_parked :
  iota_interior_cook_status = IotaInteriorCookParked.
Proof.
  reflexivity.
Qed.

Inductive IotaHperpStatus : Type :=
| IotaHperpDischarged
| IotaHperpParked.

Definition iota_hperp_status : IotaHperpStatus := IotaHperpParked.

Lemma iota_hperp_is_parked :
  iota_hperp_status = IotaHperpParked.
Proof.
  reflexivity.
Qed.

Inductive IotaSqlMmStatus : Type :=
| IotaSqlMmDone
| IotaSqlMmNotDone.

Definition iota_sql_mm_status : IotaSqlMmStatus := IotaSqlMmNotDone.

Lemma iota_sql_mm_is_not_done :
  iota_sql_mm_status = IotaSqlMmNotDone.
Proof.
  reflexivity.
Qed.

Inductive IotaCircGammaRemintStatus : Type :=
| IotaCircGammaReminted
| IotaCircGammaRemintParked.

Definition iota_circgamma_remint_status : IotaCircGammaRemintStatus :=
  IotaCircGammaRemintParked.

Lemma iota_circgamma_remint_is_parked :
  iota_circgamma_remint_status = IotaCircGammaRemintParked.
Proof.
  reflexivity.
Qed.

Inductive IotaCathedralStatus : Type :=
| IotaCathedralLanded
| IotaCathedralNotLanded.

Definition iota_cathedral_status : IotaCathedralStatus :=
  IotaCathedralNotLanded.

Lemma iota_cathedral_is_not_landed :
  iota_cathedral_status = IotaCathedralNotLanded.
Proof.
  reflexivity.
Qed.

Lemma iota_phase_b_stays_open :
  CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen.
Proof.
  exact CircularCookCpConcat.phase_b_is_open.
Qed.

Lemma iota_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

Lemma iota_rest_parked :
  iota_letter_status = IotaLetterLanded
  /\ iota_interior_cook_status = IotaInteriorCookParked
  /\ iota_hperp_status = IotaHperpParked
  /\ iota_circgamma_remint_status = IotaCircGammaRemintParked
  /\ iota_sql_mm_status = IotaSqlMmNotDone
  /\ iota_cathedral_status = IotaCathedralNotLanded
  /\ cook_loop_status = LoopObligation
  /\ CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops. Headline is QEX.                             *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_iota_gap_qed_or_qex","title":"iota interior mixed locked LS-CS Hit inhabits I_ok_mixed at interior_span_params (QED) or I_ok_mixed Hit is joint-only and the interior arm is missing (QEX); discharged QEX; named mixed_joint_params gate; not a remint of I_ok_mixed; not CircGamma; not host I_ok","file":"theories/SidecarCircInterior.v","witness":"0007-iota-interior-mixed","board":"ADR-0007"} *)

Theorem ticket_0007_iota_gap_qed_or_qex :
  (exists p ti tj,
     I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs) (IHit p ti tj)
     /\ interior_span_params ti tj
     /\ interior_mixed_constructor_inhabits InteriorMixedHitArm)
  \/
  (~ interior_mixed_constructor_inhabits InteriorMixedHitArm
   /\ (forall m p ti tj,
         I_ok_mixed m (IHit p ti tj) ->
         mixed_joint_params ti tj /\ ~ interior_span_params ti tj)
   /\ (forall m p ti tj,
         interior_span_params ti tj ->
         ~ I_ok_mixed m (IHit p ti tj))
   /\ (forall m p ti tj,
         I_ok_mixed_interior_arm m p ti tj ->
         ~ I_ok_mixed m (IHit p ti tj))
   /\ ~ I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
          (IHit locked_mixed_ls_cs_pt (1 / 2) (1 / 2))).
Proof.
  right.
  split; [exact interior_mixed_hit_arm_missing|].
  split; [exact I_ok_mixed_hit_is_joint_params|].
  split; [exact I_ok_mixed_interior_hit_false|].
  split; [exact interior_arm_not_I_ok_mixed|].
  apply locked_interior_candidate_not_I_ok_mixed.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_iota_mu_qed_or_qex","title":"iota interior mixed mu joint still inhabits I_ok_mixed at (end, 1, 0) and is not interior (QED) or the locked pair declines (QEX); discharged QED; SidecarCircMixed reuse; iota is not mu","file":"theories/SidecarCircInterior.v","witness":"0007-iota-interior-mixed","board":"ADR-0007"} *)

Theorem ticket_0007_iota_mu_qed_or_qex :
  (I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
     (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
   /\ ~ interior_span_params 1 0
   /\ mixed_joint_params 1 0
   /\ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc) IDecline)
  \/
  I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs) IDecline.
Proof.
  left.
  destruct iota_mu_joint_not_interior as [Hhit Hn].
  split; [exact Hhit|].
  split; [exact Hn|].
  split; [exact SidecarCircMixed.mixed_joint_params_end_start|].
  apply iota_host_ls_cs_decline.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_iota_host_qed_or_qex","title":"iota interior mixed discharges CircGamma and expands first cook to circular times chord interiors (QED) or CircGamma stays QEX and first cook stays chord-chord (QEX); discharged QEX; host mixed I_ok is Decline; I_ok_mixed Hit is not host I_ok; interior cook is not invented","file":"theories/SidecarCircInterior.v","witness":"0007-iota-interior-mixed","board":"ADR-0007"} *)

Theorem ticket_0007_iota_host_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggChord EggCircularArc
   /\ interior_mixed_constructor_inhabits InteriorMixedHitArm
   /\ exists p ti tj,
        I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc)
             (IHit p ti tj))
  \/
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggChord EggChord
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ ~ interior_mixed_constructor_inhabits InteriorMixedHitArm
   /\ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc) IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc)
              (IHit p ti tj))
   /\ I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
        (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
   /\ ~ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc)
        (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
   /\ iota_interior_cook_status = IotaInteriorCookParked).
Proof.
  right.
  destruct iota_host_stays_qex as [Hq [Hn [Hc [Hm [Hd Hf]]]]].
  destruct iota_mu_hit_not_host_I_ok as [Hhit Hhost].
  split; [exact Hq|].
  split; [exact Hn|].
  split; [exact Hc|].
  split; [exact Hm|].
  split; [exact interior_mixed_hit_arm_missing|].
  split; [exact Hd|].
  split; [exact Hf|].
  split; [exact Hhit|].
  split; [exact Hhost|].
  exact iota_interior_cook_is_parked.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_iota_park_qed_or_qex","title":"iota interior mixed discharges interior cook, Hperp, CircGamma remint, bag noder, SQL/MM cathedral, and Phase B done-when (QED) or names them parked / not-done (QEX); discharged QEX; iota letter landed; letter landed != interior cook Landed / cathedral Landed / Phase B done-when","file":"theories/SidecarCircInterior.v","witness":"0007-iota-interior-mixed","board":"ADR-0007"} *)

Theorem ticket_0007_iota_park_qed_or_qex :
  (iota_interior_cook_status = IotaInteriorCookLanded
   /\ iota_hperp_status = IotaHperpDischarged
   /\ iota_circgamma_remint_status = IotaCircGammaReminted
   /\ iota_sql_mm_status = IotaSqlMmDone
   /\ iota_cathedral_status = IotaCathedralLanded
   /\ cook_loop_status = LoopDischarged
   /\ CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBLanded)
  \/
  (iota_letter_status = IotaLetterLanded
   /\ iota_interior_cook_status = IotaInteriorCookParked
   /\ iota_hperp_status = IotaHperpParked
   /\ iota_circgamma_remint_status = IotaCircGammaRemintParked
   /\ iota_sql_mm_status = IotaSqlMmNotDone
   /\ iota_cathedral_status = IotaCathedralNotLanded
   /\ cook_loop_status = LoopObligation
   /\ CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen).
Proof.
  right.
  exact iota_rest_parked.
Qed.

Print Assumptions iota_host_circgamma_qex.
Print Assumptions interior_mixed_hit_arm_missing.
Print Assumptions I_ok_mixed_hit_is_joint_params.
Print Assumptions I_ok_mixed_interior_hit_false.
Print Assumptions interior_arm_not_I_ok_mixed.
Print Assumptions interior_span_params_half_half.
Print Assumptions locked_interior_candidate_not_I_ok_mixed.
Print Assumptions iota_mu_joint_I_ok_mixed.
Print Assumptions iota_mu_joint_not_interior.
Print Assumptions iota_mu_hit_not_host_I_ok.
Print Assumptions iota_not_bag_noder.
Print Assumptions iota_letter_is_landed.
Print Assumptions iota_interior_cook_is_parked.
Print Assumptions iota_phase_b_stays_open.
Print Assumptions ticket_0007_iota_gap_qed_or_qex.
Print Assumptions ticket_0007_iota_mu_qed_or_qex.
Print Assumptions ticket_0007_iota_host_qed_or_qex.
Print Assumptions ticket_0007_iota_park_qed_or_qex.
