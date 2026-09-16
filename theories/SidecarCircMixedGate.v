(* ============================================================================
   NetTopologySuite.Proofs.SidecarCircMixedGate
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: ι mixed-gate successor
   (claimId 0007-iota-mixed-gate-successor).

   I_ok_mixed Hit is definitionally gated by mixed_joint_params.
   mixed_joint_params_not_interior proves that gate is incompatible
   with interior_span_params. A true interior Hit cannot inhabit
   I_ok_mixed without reminting / dropping the joint.

   I_ok_interior is a sibling (interior-only). It does not keep the
   joint arm. This letter is the explicitly gated successor:

     MixedGateJoint     = existing I_ok_mixed (μ joint stands)
     MixedGateInterior  = I_ok_mixed_interior_arm
                          (SidecarCircInteriorHit locked fixture)

   I_ok_mixed is unchanged. mixed_joint_params is not dropped.
   InteriorMixedHitArm on I_ok_mixed itself stays missing.

   QED: locked μ joint inhabits MixedGateJoint; locked proper-cross
   inhabits MixedGateInterior; joint still inhabits I_ok_mixed and
   is not interior; interior Hit still does not inhabit I_ok_mixed.
   QEX: host CircGamma is CircGammaDischarged (MkCirc; do not remint);
   first cook stays chord–chord + circular–circular; mixed host I_ok
   is Decline; I_ok_mixed_gate Hit ≠ host I_ok; InteriorMixedHitArm
   on I_ok_mixed itself stays missing; host interior cook / H⊥ /
   bag noder / SQL/MM cathedral stay parked.

   Honesty fences:
     Host-Decline / CircGammaDischarged at the top of this module.
     I_ok_mixed_gate ≠ I_ok_mixed ≠ I_ok_interior ≠ I_ok_circ ≠
     host I_ok. MixedGateJoint ≠ MixedGateInterior.
     Sidecar ≠ host try_cook_hit / host I_ok.
     Do not drop mixed_joint_params. Do not remint I_ok_mixed /
     CircGamma / MkCirc / host I_ok. Do not expand first_cook_scope
     to circular×chord. Do not promote I_ok_interior as host I_ok.
     Not a bag noder. Not ArcSplitAtNode. Not G¹ / H⊥.
     Not MultiCurve cathedral. Not clothoid / NURBS / ellipse /
     geodesic / spiral. No new kernel. Not SQL/MM done.

   WITNESS topic: overlay · claimId: 0007-iota-mixed-gate-successor
   witness: 0007-iota-mixed-gate-successor
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via SidecarCircInteriorHit).
   Category C audit-exception: same atan2 lineage as Parks ι
   discharge; no extra axioms.
   Host lane stays 3-axiom. No Admitted / Axiom / Parameter.

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
From NTS.Proofs Require SidecarCircInterior.
From NTS.Proofs Require SidecarCircInteriorHit.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=iota-mixed-gate claim=0007-iota-mixed-gate-successor
   file=theories/SidecarCircMixedGate.v
   kind=QED-or-QEX-interior-mixed-gate-successor
   gamma=arc-span-not-gamma-full
   reuse=I_ok_mixed,I_ok_mixed_interior_arm,I_ok_interior,locked_interior_I_ok_interior
   not=new-kernel,CircGamma-remint,first-cook-noding,SQL-MM-done
   not=I_ok_mixed-remint,mixed_joint_params-drop,host-I_ok
   park=Hperp,host-interior-cook,CircGamma-remint,SQL-MM-cathedral
   land=Phase-B-iota-mixed-gate-successor *)

(* -------------------------------------------------------------------------- *)
(* Reuse. I_ok_mixed / interior arm / locked fixtures are not reminted.       *)
(* -------------------------------------------------------------------------- *)

Definition I_ok_mixed := SidecarCircInteriorHit.I_ok_mixed.
Definition mixed_joint_params := SidecarCircInteriorHit.mixed_joint_params.
Definition interior_span_params := SidecarCircInteriorHit.interior_span_params.
Definition MixedEggs := SidecarCircInteriorHit.MixedEggs.
Definition MixLsCs := SidecarCircInteriorHit.MixLsCs.
Definition MixCsLs := SidecarCircInteriorHit.MixCsLs.
Definition I_ok_mixed_interior_arm :=
  SidecarCircInteriorHit.I_ok_mixed_interior_arm.
Definition I_ok_interior := SidecarCircInteriorHit.I_ok_interior.

Definition locked_mixed_ls := SidecarCircInterior.locked_mixed_ls.
Definition locked_mixed_cs := SidecarCircInterior.locked_mixed_cs.
Definition locked_interior_ls := SidecarCircInteriorHit.locked_interior_ls.
Definition locked_interior_cs := SidecarCircInteriorHit.locked_interior_cs.
Definition locked_interior_hit := SidecarCircInteriorHit.locked_interior_hit.
Definition locked_interior_rev_hit :=
  SidecarCircInteriorHit.locked_interior_rev_hit.
Definition locked_interior_ti := SidecarCircInteriorHit.locked_interior_ti.
Definition locked_interior_tj := SidecarCircInteriorHit.locked_interior_tj.

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGammaDischarged fence (load-bearing, not decoration).   *)
(* -------------------------------------------------------------------------- *)

Lemma mixed_gate_circgamma_discharged :
  circular_gamma_status = CircGammaDischarged.
Proof.
  exact circular_gamma_is_discharged.
Qed.

Lemma mixed_gate_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma mixed_gate_circular_is_first_cook :
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_is_first_cook_scope.
Qed.

Lemma mixed_gate_not_first_cook_mixed :
  ~ first_cook_scope EggChord EggCircularArc.
Proof.
  exact chord_circular_not_first_cook_scope.
Qed.

Lemma mixed_gate_host_ls_cs_decline :
  forall c,
    I_ok (MkChord c) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact SidecarCircInteriorHit.iota_hit_host_ls_cs_decline.
Qed.

Lemma mixed_gate_host_ls_cs_hit_false :
  forall c p ti tj,
    ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) (IHit p ti tj).
Proof.
  exact SidecarCircInteriorHit.iota_hit_host_ls_cs_hit_false.
Qed.

(* -------------------------------------------------------------------------- *)
(* Explicitly gated successor. Joint arm = I_ok_mixed. Interior arm =         *)
(* I_ok_mixed_interior_arm. I_ok_mixed itself is not reminted.                *)
(* -------------------------------------------------------------------------- *)

Inductive I_ok_mixed_gate : MixedEggs -> IResult -> Prop :=
| MixedGateJoint :
    forall m o, I_ok_mixed m o -> I_ok_mixed_gate m o
| MixedGateInterior :
    forall m p ti tj,
      I_ok_mixed_interior_arm m p ti tj ->
      I_ok_mixed_gate m (IHit p ti tj).

Lemma mixed_gate_joint_is_I_ok_mixed :
  forall m o, I_ok_mixed m o -> I_ok_mixed_gate m o.
Proof.
  exact MixedGateJoint.
Qed.

Lemma mixed_gate_interior_is_arm :
  forall m p ti tj,
    I_ok_mixed_interior_arm m p ti tj ->
    I_ok_mixed_gate m (IHit p ti tj).
Proof.
  exact MixedGateInterior.
Qed.

Lemma I_ok_interior_inhabits_mixed_gate_interior :
  forall m p ti tj,
    I_ok_interior m (IHit p ti tj) ->
    I_ok_mixed_gate m (IHit p ti tj).
Proof.
  intros m p ti tj H.
  apply MixedGateInterior.
  apply (proj1 (SidecarCircInteriorHit.I_ok_interior_hit_is_arm m p ti tj)).
  exact H.
Qed.

Lemma mixed_gate_joint_hit_is_joint_params :
  forall m p ti tj,
    I_ok_mixed m (IHit p ti tj) ->
    I_ok_mixed_gate m (IHit p ti tj)
    /\ mixed_joint_params ti tj
    /\ ~ interior_span_params ti tj.
Proof.
  intros m p ti tj H.
  split; [apply MixedGateJoint; exact H|].
  exact (SidecarCircInterior.I_ok_mixed_hit_is_joint_params m p ti tj H).
Qed.

(* I_ok_mixed still has no InteriorMixedHitArm. Successor does not
   inhabit that constructor on I_ok_mixed itself. *)
Lemma mixed_gate_I_ok_mixed_interior_arm_still_missing :
  ~ SidecarCircInterior.interior_mixed_constructor_inhabits
      SidecarCircInterior.InteriorMixedHitArm.
Proof.
  exact SidecarCircInterior.interior_mixed_hit_arm_missing.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked μ joint: MixedGateJoint. Locked proper-cross: MixedGateInterior.    *)
(* -------------------------------------------------------------------------- *)

Lemma locked_joint_I_ok_mixed_gate :
  I_ok_mixed_gate (MixLsCs locked_mixed_ls locked_mixed_cs)
    (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs).
Proof.
  apply MixedGateJoint.
  exact SidecarCircInterior.iota_mu_joint_I_ok_mixed.
Qed.

Lemma locked_interior_I_ok_mixed_gate :
  I_ok_mixed_gate (MixLsCs locked_interior_ls locked_interior_cs)
    locked_interior_hit.
Proof.
  apply I_ok_interior_inhabits_mixed_gate_interior.
  exact SidecarCircInteriorHit.locked_interior_I_ok_interior.
Qed.

Lemma locked_interior_rev_I_ok_mixed_gate :
  I_ok_mixed_gate (MixCsLs locked_interior_cs locked_interior_ls)
    locked_interior_rev_hit.
Proof.
  apply I_ok_interior_inhabits_mixed_gate_interior.
  exact SidecarCircInteriorHit.locked_interior_rev_I_ok_interior.
Qed.

Lemma locked_joint_still_I_ok_mixed :
  I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
    (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
  /\ ~ interior_span_params 1 0.
Proof.
  exact SidecarCircInterior.iota_mu_joint_not_interior.
Qed.

Lemma locked_interior_still_not_I_ok_mixed :
  I_ok_mixed_gate (MixLsCs locked_interior_ls locked_interior_cs)
    locked_interior_hit
  /\ ~ I_ok_mixed (MixLsCs locked_interior_ls locked_interior_cs)
        locked_interior_hit.
Proof.
  split; [exact locked_interior_I_ok_mixed_gate|].
  apply SidecarCircInteriorHit.I_ok_interior_hit_not_I_ok_mixed.
  exact SidecarCircInteriorHit.locked_interior_I_ok_interior.
Qed.

Lemma locked_interior_gate_not_host_I_ok :
  I_ok_mixed_gate (MixLsCs locked_interior_ls locked_interior_cs)
    locked_interior_hit
  /\ ~ I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc)
        locked_interior_hit.
Proof.
  split; [exact locked_interior_I_ok_mixed_gate|].
  unfold locked_interior_hit, SidecarCircInteriorHit.locked_interior_hit.
  apply mixed_gate_host_ls_cs_hit_false.
Qed.

(* -------------------------------------------------------------------------- *)
(* Letter-local parks. Successor landed ≠ host interior cook / I_ok_mixed     *)
(* InteriorMixedHitArm. CircGamma is discharged; do not remint it.            *)
(* -------------------------------------------------------------------------- *)

Inductive MixedGateLetterStatus : Type :=
| MixedGateLetterLanded
| MixedGateLetterParked.

Definition mixed_gate_letter_status : MixedGateLetterStatus :=
  MixedGateLetterLanded.

Lemma mixed_gate_letter_is_landed :
  mixed_gate_letter_status = MixedGateLetterLanded.
Proof.
  reflexivity.
Qed.

Lemma mixed_gate_host_cook_stays_parked :
  SidecarCircInterior.iota_interior_cook_status
  = SidecarCircInterior.IotaInteriorCookParked.
Proof.
  exact SidecarCircInterior.iota_interior_cook_is_parked.
Qed.

Lemma mixed_gate_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

Lemma mixed_gate_phase_b_stays_open :
  CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen.
Proof.
  exact CircularCookCpConcat.phase_b_is_open.
Qed.

Lemma mixed_gate_rest_parked :
  mixed_gate_letter_status = MixedGateLetterLanded
  /\ SidecarCircInterior.iota_interior_cook_status
     = SidecarCircInterior.IotaInteriorCookParked
  /\ cook_loop_status = LoopObligation
  /\ CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen
  /\ ~ SidecarCircInterior.interior_mixed_constructor_inhabits
         SidecarCircInterior.InteriorMixedHitArm.
Proof.
  repeat split; try reflexivity.
  exact mixed_gate_I_ok_mixed_interior_arm_still_missing.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops. Headline is QED on the gated successor.      *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-iota-mixed-gate-successor","topic":"overlay","lemma":"ticket_0007_iota_mixed_gate_qed_or_qex","title":"iota mixed-gate successor: locked mu joint inhabits MixedGateJoint and locked proper-cross inhabits MixedGateInterior (QED) or the successor is uninhabited (QEX); discharged QED; I_ok_mixed unchanged; mixed_joint_params stands; not host I_ok; not CircGamma remint","file":"theories/SidecarCircMixedGate.v","witness":"0007-iota-mixed-gate-successor","board":"ADR-0007"} *)

Theorem ticket_0007_iota_mixed_gate_qed_or_qex :
  (I_ok_mixed_gate (MixLsCs locked_mixed_ls locked_mixed_cs)
     (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
   /\ I_ok_mixed_gate (MixLsCs locked_interior_ls locked_interior_cs)
        locked_interior_hit
   /\ I_ok_mixed_gate (MixCsLs locked_interior_cs locked_interior_ls)
        locked_interior_rev_hit
   /\ mixed_joint_params 1 0
   /\ interior_span_params locked_interior_ti locked_interior_tj
   /\ I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
        (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
   /\ ~ I_ok_mixed (MixLsCs locked_interior_ls locked_interior_cs)
        locked_interior_hit)
  \/
  (forall m o, ~ I_ok_mixed_gate m o).
Proof.
  left.
  split; [exact locked_joint_I_ok_mixed_gate|].
  split; [exact locked_interior_I_ok_mixed_gate|].
  split; [exact locked_interior_rev_I_ok_mixed_gate|].
  split; [exact SidecarCircMixed.mixed_joint_params_end_start|].
  split; [exact SidecarCircInteriorHit.locked_interior_params|].
  destruct locked_joint_still_I_ok_mixed as [Hmu _].
  destruct locked_interior_still_not_I_ok_mixed as [_ Hn].
  split; [exact Hmu|].
  exact Hn.
Qed.

(* WITNESS {"claimId":"0007-iota-mixed-gate-successor","topic":"overlay","lemma":"ticket_0007_iota_mixed_gate_joint_stands_qed_or_qex","title":"iota mixed-gate successor: I_ok_mixed Hit stays mixed_joint_params and InteriorMixedHitArm on I_ok_mixed itself stays missing (QED) or I_ok_mixed accepts interior_span_params (QEX); discharged QED; successor does not remint I_ok_mixed; do not drop the joint gate","file":"theories/SidecarCircMixedGate.v","witness":"0007-iota-mixed-gate-successor","board":"ADR-0007"} *)

Theorem ticket_0007_iota_mixed_gate_joint_stands_qed_or_qex :
  (~ SidecarCircInterior.interior_mixed_constructor_inhabits
      SidecarCircInterior.InteriorMixedHitArm
   /\ (forall m p ti tj,
         I_ok_mixed m (IHit p ti tj) ->
         mixed_joint_params ti tj /\ ~ interior_span_params ti tj)
   /\ (forall m p ti tj,
         interior_span_params ti tj ->
         ~ I_ok_mixed m (IHit p ti tj))
   /\ I_ok_mixed_gate (MixLsCs locked_mixed_ls locked_mixed_cs)
        (SidecarCircMixed.ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
   /\ I_ok_mixed_gate (MixLsCs locked_interior_ls locked_interior_cs)
        locked_interior_hit)
  \/
  I_ok_mixed (MixLsCs locked_interior_ls locked_interior_cs)
    locked_interior_hit.
Proof.
  left.
  split; [exact mixed_gate_I_ok_mixed_interior_arm_still_missing|].
  split; [exact SidecarCircInterior.I_ok_mixed_hit_is_joint_params|].
  split; [exact SidecarCircInterior.I_ok_mixed_interior_hit_false|].
  split; [exact locked_joint_I_ok_mixed_gate|].
  exact locked_interior_I_ok_mixed_gate.
Qed.

(* WITNESS {"claimId":"0007-iota-mixed-gate-successor","topic":"overlay","lemma":"ticket_0007_iota_mixed_gate_host_qed_or_qex","title":"iota mixed-gate successor expands first cook to circular times chord and inhabits host I_ok Hit (QED) or CircGamma is CircGammaDischarged and first cook stays chord-chord plus circular-circular (QEX); discharged QEX; host mixed I_ok is Decline; I_ok_mixed_gate Hit is not host I_ok; do not remint MkCirc","file":"theories/SidecarCircMixedGate.v","witness":"0007-iota-mixed-gate-successor","board":"ADR-0007"} *)

Theorem ticket_0007_iota_mixed_gate_host_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggChord EggCircularArc
   /\ SidecarCircInterior.interior_mixed_constructor_inhabits
        SidecarCircInterior.InteriorMixedHitArm
   /\ exists p ti tj,
        I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc)
             (IHit p ti tj))
  \/
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggChord EggChord
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ ~ SidecarCircInterior.interior_mixed_constructor_inhabits
         SidecarCircInterior.InteriorMixedHitArm
   /\ I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc)
        IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc)
              (IHit p ti tj))
   /\ I_ok_mixed_gate (MixLsCs locked_interior_ls locked_interior_cs)
        locked_interior_hit
   /\ ~ I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc)
        locked_interior_hit
   /\ SidecarCircInterior.iota_interior_cook_status
      = SidecarCircInterior.IotaInteriorCookParked).
Proof.
  right.
  destruct locked_interior_gate_not_host_I_ok as [Hhit Hhost].
  split; [exact mixed_gate_circgamma_discharged|].
  split; [exact mixed_gate_circular_is_first_cook|].
  split; [exact mixed_gate_first_cook_stays_chord_chord|].
  split; [exact mixed_gate_not_first_cook_mixed|].
  split; [exact mixed_gate_I_ok_mixed_interior_arm_still_missing|].
  split; [apply mixed_gate_host_ls_cs_decline|].
  split; [apply mixed_gate_host_ls_cs_hit_false|].
  split; [exact Hhit|].
  split; [exact Hhost|].
  exact mixed_gate_host_cook_stays_parked.
Qed.

(* WITNESS {"claimId":"0007-iota-mixed-gate-successor","topic":"overlay","lemma":"ticket_0007_iota_mixed_gate_park_qed_or_qex","title":"iota mixed-gate successor discharges host interior cook, Hperp, CircGamma remint, bag noder, SQL/MM cathedral, and Phase B done-when (QED) or names them parked / not-done (QEX); discharged QEX; successor letter landed; InteriorMixedHitArm on I_ok_mixed itself stays missing; letter landed != host cook Landed / I_ok_mixed remint","file":"theories/SidecarCircMixedGate.v","witness":"0007-iota-mixed-gate-successor","board":"ADR-0007"} *)

Theorem ticket_0007_iota_mixed_gate_park_qed_or_qex :
  (SidecarCircInterior.iota_interior_cook_status
   = SidecarCircInterior.IotaInteriorCookLanded
   /\ cook_loop_status = LoopDischarged
   /\ CircularCookCpConcat.phase_b_status
      = CircularCookCpConcat.PhaseBLanded
   /\ SidecarCircInterior.interior_mixed_constructor_inhabits
        SidecarCircInterior.InteriorMixedHitArm)
  \/
  (mixed_gate_letter_status = MixedGateLetterLanded
   /\ SidecarCircInterior.iota_interior_cook_status
      = SidecarCircInterior.IotaInteriorCookParked
   /\ cook_loop_status = LoopObligation
   /\ CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen
   /\ ~ SidecarCircInterior.interior_mixed_constructor_inhabits
         SidecarCircInterior.InteriorMixedHitArm).
Proof.
  right.
  exact mixed_gate_rest_parked.
Qed.

Print Assumptions mixed_gate_circgamma_discharged.
Print Assumptions mixed_gate_not_first_cook_mixed.
Print Assumptions mixed_gate_joint_is_I_ok_mixed.
Print Assumptions mixed_gate_interior_is_arm.
Print Assumptions I_ok_interior_inhabits_mixed_gate_interior.
Print Assumptions mixed_gate_I_ok_mixed_interior_arm_still_missing.
Print Assumptions locked_joint_I_ok_mixed_gate.
Print Assumptions locked_interior_I_ok_mixed_gate.
Print Assumptions locked_interior_rev_I_ok_mixed_gate.
Print Assumptions locked_joint_still_I_ok_mixed.
Print Assumptions locked_interior_still_not_I_ok_mixed.
Print Assumptions locked_interior_gate_not_host_I_ok.
Print Assumptions mixed_gate_letter_is_landed.
Print Assumptions mixed_gate_host_cook_stays_parked.
Print Assumptions ticket_0007_iota_mixed_gate_qed_or_qex.
Print Assumptions ticket_0007_iota_mixed_gate_joint_stands_qed_or_qex.
Print Assumptions ticket_0007_iota_mixed_gate_host_qed_or_qex.
Print Assumptions ticket_0007_iota_mixed_gate_park_qed_or_qex.
