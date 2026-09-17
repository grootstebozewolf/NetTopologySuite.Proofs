(* ============================================================================
   NetTopologySuite.Proofs.SidecarCircIotaArm
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: ι cell-4 arm stop (claimId 0007-iota-arm).
   Stacked on the six-cell gate (claimId 0007-iota-gate). This letter
   does not remint the gate as cook-discharged.

   Cell 4 𝓘 is InteriorMixedHitArm = I_ok_mixed Hit ∧ interior_span_params
   plus both-window split (circ child + chord child). Tried on the locked
   MixLsCs pair (WinCirc × WinChord, both params interior, not WinColCirc
   / span_decline_arc).

   Blocked by mixed_joint_params on I_ok_mixed Hit. That gate is
   exclusive with interior_span_params
   (SidecarCircMixed.mixed_joint_params_not_interior). Real predicate
   clash, not a missing file.

   Honest next ctor is the already-landed sidecar I_ok_interior
   (packages I_ok_mixed_interior_arm). A new I_ok_mixed_interior would
   remint that arm, not I_ok_mixed. It would not remint first-cook /
   host I_ok while sidecar. Promoting it to host I_ok would remint
   first_cook_scope EggChord EggCircularArc (false). Do not drop
   mixed_joint_params.

   I 𝓘 I here: cells 1–3 reuse existing cooks; cell 4 is this named
   QEX; cells 5–6 are already Empty / Decline.

   Honesty fences:
     Host CircGamma is CircGammaDischarged (MkCirc). Do not remint Γ.
     I_ok_circ / I_ok_mixed / I_ok_interior Hit ≠ host I_ok.
     mixed_joint_params stands. Do not drop it.
     Not LeftoverBagTermArm / LoopDischarged. Not NURBS / clothoid /
     ellipse. Not GEOS / C API / Overlay. Not GeometryNoder.
     Sidecar ≠ host try_cook_hit. Not SQL/MM done.
     Geometric chord_split / span_split on the locked pair is not
     InteriorMixedHitArm and is not a first-cook expand.

   WITNESS topic: overlay · claimId: 0007-iota-arm
   witness: 0007-iota-arm
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via SidecarCircIotaGate /
     SidecarCircInterior* / SidecarCircMixed / CircularCookSpanSplit).
   Category C audit-exception: same atan2 lineage as Parks ι / ι-gate;
   no extra axioms. Host lane stays 3-axiom.
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  CircularCook CircularCookHit CircularCookSpan CircularCookOkCirc
  CircularCookMkCirc.
From NTS.Proofs Require CircularCookSpanFilter.
From NTS.Proofs Require CircularCookSpanSplit.
From NTS.Proofs Require CircularCookCsConcat.
From NTS.Proofs Require CircularCookCpConcat.
From NTS.Proofs Require SidecarCircMixed.
From NTS.Proofs Require SidecarCircInterior.
From NTS.Proofs Require SidecarCircInteriorHit.
From NTS.Proofs Require SidecarCircIotaGate.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=iota-arm claim=0007-iota-arm
   file=theories/SidecarCircIotaArm.v
   kind=QED-or-QEX-iota-cell4-arm
   reuse=I_ok_mixed,I_ok_interior,interior_span_params,mixed_joint_params
   reuse=chord_split,span_split,IotaGate
   not=new-kernel,CircGamma-remint,I_ok_mixed-remint,first-cook-expand
   not=LeftoverBagTermArm,LoopDischarged,NURBS,clothoid,ellipse
   park=InteriorMixedHitArm,host-interior-cook
   land=iota-cell4-blocked-by-mixed_joint_params *)

(* -------------------------------------------------------------------------- *)
(* Aliases. Do not remint.                                                    *)
(* -------------------------------------------------------------------------- *)

Definition I_ok_mixed := SidecarCircInterior.I_ok_mixed.
Definition mixed_joint_params := SidecarCircInterior.mixed_joint_params.
Definition interior_span_params := SidecarCircInterior.interior_span_params.
Definition MixLsCs := SidecarCircInterior.MixLsCs.
Definition I_ok_interior := SidecarCircInteriorHit.I_ok_interior.
Definition I_ok_mixed_interior_arm :=
  SidecarCircInterior.I_ok_mixed_interior_arm.

Definition locked_ls := SidecarCircInteriorHit.locked_interior_ls.
Definition locked_cs := SidecarCircInteriorHit.locked_interior_cs.
Definition locked_ti := SidecarCircInteriorHit.locked_interior_ti.
Definition locked_tj := SidecarCircInteriorHit.locked_interior_tj.
Definition locked_hit := SidecarCircInteriorHit.locked_interior_hit.

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma fence (load-bearing, not decoration).             *)
(* -------------------------------------------------------------------------- *)

Lemma iota_arm_host_circgamma_discharged :
  circular_gamma_status = CircGammaDischarged.
Proof.
  exact circular_gamma_is_discharged.
Qed.

Lemma iota_arm_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma iota_arm_circular_is_first_cook :
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_is_first_cook_scope.
Qed.

Lemma iota_arm_not_first_cook_mixed :
  ~ first_cook_scope EggChord EggCircularArc.
Proof.
  exact chord_circular_not_first_cook_scope.
Qed.

Lemma iota_arm_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

(* -------------------------------------------------------------------------- *)
(* Blocking predicate. I_ok_mixed Hit is joint-gated.                         *)
(* -------------------------------------------------------------------------- *)

Lemma iota_arm_hit_requires_joint_params :
  forall m p ti tj,
    I_ok_mixed m (IHit p ti tj) ->
    mixed_joint_params ti tj /\ ~ interior_span_params ti tj.
Proof.
  exact SidecarCircInterior.I_ok_mixed_hit_is_joint_params.
Qed.

Lemma iota_arm_joint_not_interior :
  forall ti tj,
    mixed_joint_params ti tj -> ~ interior_span_params ti tj.
Proof.
  exact SidecarCircMixed.mixed_joint_params_not_interior.
Qed.

Lemma iota_arm_interior_hit_false :
  forall m p ti tj,
    interior_span_params ti tj ->
    ~ I_ok_mixed m (IHit p ti tj).
Proof.
  exact SidecarCircInterior.I_ok_mixed_interior_hit_false.
Qed.

(* WITNESS {"claimId":"0007-iota-arm","topic":"overlay","lemma":"cell4_blocked_by_mixed_joint_params","title":"iota cell 4 arm: InteriorMixedHitArm is uninhabited because I_ok_mixed Hit requires mixed_joint_params, which is exclusive with interior_span_params; not a missing file; mixed_joint_params stands","file":"theories/SidecarCircIotaArm.v","witness":"0007-iota-arm","board":"ADR-0007"} *)

Theorem cell4_blocked_by_mixed_joint_params :
  ~ SidecarCircInterior.interior_mixed_constructor_inhabits
      SidecarCircInterior.InteriorMixedHitArm
  /\ (forall m p ti tj,
        I_ok_mixed m (IHit p ti tj) ->
        mixed_joint_params ti tj /\ ~ interior_span_params ti tj)
  /\ (forall ti tj,
        mixed_joint_params ti tj -> ~ interior_span_params ti tj).
Proof.
  split; [exact SidecarCircInterior.interior_mixed_hit_arm_missing|].
  split; [exact iota_arm_hit_requires_joint_params|].
  exact iota_arm_joint_not_interior.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked pair: WinCirc × WinChord, interior params, not WinColCirc.          *)
(* -------------------------------------------------------------------------- *)

Lemma locked_iota_circ_valid :
  valid_arc locked_cs.
Proof.
  exact SidecarCircIotaGate.locked_interior_cs_valid.
Qed.

Lemma locked_iota_not_wincolcirc :
  match SidecarCircIotaGate.locked_iota_win_cs with
  | SidecarCircIotaGate.WinColCirc _ _ => False
  | SidecarCircIotaGate.WinCirc _ _ => True
  | SidecarCircIotaGate.WinChord _ => False
  end.
Proof.
  exact I.
Qed.

Lemma locked_iota_cs_neq_span_decline_arc :
  locked_cs <> CircularCookSpanFilter.span_decline_arc.
Proof.
  intro Heq.
  pose proof span_arc_A_valid as Hva.
  unfold locked_cs, SidecarCircInteriorHit.locked_interior_cs in Heq.
  rewrite Heq in Hva.
  exact (CircularCookSpanFilter.span_decline_arc_invalid Hva).
Qed.

Lemma locked_iota_is_cell4_candidate :
  SidecarCircIotaGate.IotaGate
    SidecarCircIotaGate.locked_iota_win_ls
    SidecarCircIotaGate.locked_iota_win_cs
    locked_hit SidecarCircIotaGate.CellIotaCand
  /\ interior_span_params locked_ti locked_tj
  /\ I_ok_interior (MixLsCs locked_ls locked_cs) locked_hit
  /\ ~ I_ok_mixed (MixLsCs locked_ls locked_cs) locked_hit.
Proof.
  exact SidecarCircIotaGate.cell4_is_iota_candidate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Try the arm on the locked pair. The ctor stays missing.                    *)
(* -------------------------------------------------------------------------- *)

Lemma locked_try_InteriorMixedHitArm :
  ~ SidecarCircInterior.I_ok_mixed_interior_hit
      (MixLsCs locked_ls locked_cs)
      locked_p_plus locked_ti locked_tj
  /\ ~ SidecarCircInterior.interior_mixed_constructor_inhabits
        SidecarCircInterior.InteriorMixedHitArm.
Proof.
  split.
  - unfold locked_hit in *.
    apply SidecarCircInterior.I_ok_mixed_interior_hit_uninhabited.
  - exact SidecarCircInterior.interior_mixed_hit_arm_missing.
Qed.

(* -------------------------------------------------------------------------- *)
(* Geometric both-window split. Not InteriorMixedHitArm. Not host 𝓘.         *)
(* -------------------------------------------------------------------------- *)

Definition locked_chord_children : ChordEgg * ChordEgg :=
  chord_split locked_ls locked_ti.

Definition locked_circ_children
  : CircularCookSpanSplit.SpanLeftover * CircularCookSpanSplit.SpanLeftover :=
  CircularCookSpanSplit.span_split locked_cs locked_tj.

Lemma locked_chord_children_meet :
  ce_p1 (fst locked_chord_children) = locked_p_plus
  /\ ce_p0 (snd locked_chord_children) = locked_p_plus.
Proof.
  unfold locked_chord_children, locked_ls, locked_ti.
  destruct (chord_split_join SidecarCircInteriorHit.locked_interior_ls
                             SidecarCircInteriorHit.locked_interior_ti)
    as [Hl Hr].
  destruct SidecarCircInteriorHit.locked_interior_on_chord as [_ Heq].
  rewrite Hl, Hr, <- Heq.
  split; reflexivity.
Qed.

Lemma locked_circ_children_meet :
  CircularCookSpanSplit.span_leftover_eval
    (fst locked_circ_children) 1 = locked_p_plus
  /\ CircularCookSpanSplit.span_leftover_eval
       (snd locked_circ_children) 0 = locked_p_plus.
Proof.
  unfold locked_circ_children.
  destruct (CircularCookSpanSplit.span_split_join locked_cs locked_tj)
    as [Hl Hr].
  rewrite Hl, Hr.
  unfold locked_cs, locked_tj, SidecarCircInteriorHit.locked_interior_cs,
         SidecarCircInteriorHit.locked_interior_tj.
  destruct span_p_plus_on_gamma_A as [_ Heq].
  rewrite <- Heq.
  split; reflexivity.
Qed.

Lemma locked_both_windows_split_meet :
  ce_p1 (fst locked_chord_children) = locked_p_plus
  /\ ce_p0 (snd locked_chord_children) = locked_p_plus
  /\ CircularCookSpanSplit.span_leftover_eval
       (fst locked_circ_children) 1 = locked_p_plus
  /\ CircularCookSpanSplit.span_leftover_eval
       (snd locked_circ_children) 0 = locked_p_plus.
Proof.
  destruct locked_chord_children_meet as [Hc1 Hc2].
  destruct locked_circ_children_meet as [Ha1 Ha2].
  repeat split; assumption.
Qed.

Lemma locked_split_is_not_InteriorMixedHitArm :
  ce_p1 (fst locked_chord_children) = locked_p_plus
  /\ CircularCookSpanSplit.span_leftover_eval
       (fst locked_circ_children) 1 = locked_p_plus
  /\ ~ SidecarCircInterior.interior_mixed_constructor_inhabits
        SidecarCircInterior.InteriorMixedHitArm
  /\ ~ I_ok_mixed (MixLsCs locked_ls locked_cs) locked_hit.
Proof.
  destruct locked_both_windows_split_meet as [Hc [_ [Ha _]]].
  destruct SidecarCircInteriorHit.locked_interior_not_I_ok_mixed as [_ Hn].
  split; [exact Hc|].
  split; [exact Ha|].
  split; [exact SidecarCircInterior.interior_mixed_hit_arm_missing|].
  exact Hn.
Qed.

(* -------------------------------------------------------------------------- *)
(* Honest next ctor: existing I_ok_interior. Not host I_ok.                   *)
(* -------------------------------------------------------------------------- *)

Lemma honest_next_ctor_is_I_ok_interior_not_host :
  (forall m p ti tj,
     I_ok_interior m (IHit p ti tj) <->
     I_ok_mixed_interior_arm m p ti tj)
  /\ ~ first_cook_scope EggChord EggCircularArc
  /\ (forall c p ti tj,
        ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) (IHit p ti tj))
  /\ (forall m p ti tj,
        I_ok_mixed m (IHit p ti tj) -> mixed_joint_params ti tj).
Proof.
  split; [exact SidecarCircInteriorHit.I_ok_interior_hit_is_arm|].
  split; [exact iota_arm_not_first_cook_mixed|].
  split; [exact SidecarCircMixed.mixed_host_ls_cs_hit_false|].
  intros m p ti tj H.
  apply iota_arm_hit_requires_joint_params in H.
  apply H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cells 1–3 cooks and 5–6 Empty/Decline stay as the gate left them.          *)
(* -------------------------------------------------------------------------- *)

Lemma cells_1_3_reuse_existing_cooks :
  I_ok (MkChord diag_ab) (MkChord diag_cd)
       (IHit cross_pt (1 / 2) (1 / 2))
  /\ I_ok (MkCirc locked_circ_A) (MkCirc locked_circ_B)
       (IHit locked_circ_hit_pt locked_circ_ti locked_circ_tj)
  /\ I_ok_mixed (MixLsCs SidecarCircMixed.locked_mixed_ls
                         SidecarCircMixed.locked_mixed_cs)
       (SidecarCircMixed.ls_cs_joint_hit
          SidecarCircMixed.locked_mixed_ls
          SidecarCircMixed.locked_mixed_cs).
Proof.
  split; [exact SidecarCircIotaGate.cell1_reuses_host_crossing_I_ok|].
  split; [exact SidecarCircIotaGate.cell2_reuses_mkcirc_unique_hit|].
  exact SidecarCircIotaGate.cell3_reuses_I_ok_mixed.
Qed.

Lemma cells_5_6_already_empty_decline :
  (forall c a va,
     SidecarCircIotaGate.IotaGate
       (SidecarCircIotaGate.WinChord c)
       (SidecarCircIotaGate.WinCirc a va)
       IEmpty SidecarCircIotaGate.CellMiss)
  /\ (forall c a va,
        SidecarCircIotaGate.IotaGate
          (SidecarCircIotaGate.WinChord c)
          (SidecarCircIotaGate.WinCirc a va)
          IDecline SidecarCircIotaGate.CellDecline).
Proof.
  split; [exact SidecarCircIotaGate.cell5_mixed_empty|].
  exact SidecarCircIotaGate.cell6_mixed_decline.
Qed.

(* -------------------------------------------------------------------------- *)
(* Tickets. Gate stays QED. Cell-4 arm is this named QEX.                     *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-iota-arm","topic":"overlay","lemma":"ticket_0007_iota_arm_qed_or_qex","title":"iota cell 4 arm: InteriorMixedHitArm inhabits I_ok_mixed Hit at interior_span_params and both windows split (QED) or blocked by mixed_joint_params on I_ok_mixed Hit which is exclusive with interior_span_params, mixed_joint_params stands, I_ok_interior is the honest next sidecar ctor and is not host I_ok (QEX); discharged QEX; geometric chord_split plus span_split meet at p+ and do not inhabit the arm; cells 1-3 reuse cooks; cells 5-6 Empty/Decline; not CircGamma remint; LoopDischarged stays false","file":"theories/SidecarCircIotaArm.v","witness":"0007-iota-arm","board":"ADR-0007"} *)

Theorem ticket_0007_iota_arm_qed_or_qex :
  (SidecarCircInterior.interior_mixed_constructor_inhabits
     SidecarCircInterior.InteriorMixedHitArm
   /\ first_cook_scope EggChord EggCircularArc
   /\ cook_loop_status = LoopDischarged)
  \/
  (~ SidecarCircInterior.interior_mixed_constructor_inhabits
      SidecarCircInterior.InteriorMixedHitArm
   /\ (forall m p ti tj,
         I_ok_mixed m (IHit p ti tj) ->
         mixed_joint_params ti tj /\ ~ interior_span_params ti tj)
   /\ (forall ti tj,
         mixed_joint_params ti tj -> ~ interior_span_params ti tj)
   /\ SidecarCircIotaGate.IotaGate
        SidecarCircIotaGate.locked_iota_win_ls
        SidecarCircIotaGate.locked_iota_win_cs
        locked_hit SidecarCircIotaGate.CellIotaCand
   /\ I_ok_interior (MixLsCs locked_ls locked_cs) locked_hit
   /\ ~ I_ok_mixed (MixLsCs locked_ls locked_cs) locked_hit
   /\ ce_p1 (fst locked_chord_children) = locked_p_plus
   /\ CircularCookSpanSplit.span_leftover_eval
        (fst locked_circ_children) 1 = locked_p_plus
   /\ (forall m p ti tj,
         I_ok_interior m (IHit p ti tj) <->
         I_ok_mixed_interior_arm m p ti tj)
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ I_ok (MkChord diag_ab) (MkChord diag_cd)
        (IHit cross_pt (1 / 2) (1 / 2))
   /\ I_ok (MkCirc locked_circ_A) (MkCirc locked_circ_B)
        (IHit locked_circ_hit_pt locked_circ_ti locked_circ_tj)
   /\ I_ok_mixed (MixLsCs SidecarCircMixed.locked_mixed_ls
                          SidecarCircMixed.locked_mixed_cs)
        (SidecarCircMixed.ls_cs_joint_hit
           SidecarCircMixed.locked_mixed_ls
           SidecarCircMixed.locked_mixed_cs)
   /\ (forall c a va,
         SidecarCircIotaGate.IotaGate
           (SidecarCircIotaGate.WinChord c)
           (SidecarCircIotaGate.WinCirc a va)
           IEmpty SidecarCircIotaGate.CellMiss)
   /\ (forall c a va,
         SidecarCircIotaGate.IotaGate
           (SidecarCircIotaGate.WinChord c)
           (SidecarCircIotaGate.WinCirc a va)
           IDecline SidecarCircIotaGate.CellDecline)
   /\ circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggChord EggChord
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ cook_loop_status = LoopObligation
   /\ cook_loop_status <> LoopDischarged
   /\ SidecarCircInterior.iota_interior_cook_status
      = SidecarCircInterior.IotaInteriorCookParked
   /\ locked_cs <> CircularCookSpanFilter.span_decline_arc).
Proof.
  right.
  destruct cell4_blocked_by_mixed_joint_params as [Hmiss [Hgate Hxor]].
  destruct locked_iota_is_cell4_candidate as [Hg [_ [Hint Hnm]]].
  destruct locked_split_is_not_InteriorMixedHitArm as [Hc [_ [_ _]]].
  destruct locked_circ_children_meet as [Ha _].
  destruct cells_1_3_reuse_existing_cooks as [H1 [H2 H3]].
  destruct cells_5_6_already_empty_decline as [H5 H6].
  destruct iota_arm_not_bag_noder as [Hob Hnd].
  split; [exact Hmiss|].
  split; [exact Hgate|].
  split; [exact Hxor|].
  split; [exact Hg|].
  split; [exact Hint|].
  split; [exact Hnm|].
  split; [exact Hc|].
  split; [exact Ha|].
  split; [exact SidecarCircInteriorHit.I_ok_interior_hit_is_arm|].
  split; [exact iota_arm_not_first_cook_mixed|].
  split; [exact H1|].
  split; [exact H2|].
  split; [exact H3|].
  split; [exact H5|].
  split; [exact H6|].
  split; [exact iota_arm_host_circgamma_discharged|].
  split; [exact iota_arm_first_cook_stays_chord_chord|].
  split; [exact iota_arm_circular_is_first_cook|].
  split; [exact Hob|].
  split; [exact Hnd|].
  split; [exact SidecarCircInterior.iota_interior_cook_is_parked|].
  exact locked_iota_cs_neq_span_decline_arc.
Qed.

Print Assumptions iota_arm_host_circgamma_discharged.
Print Assumptions iota_arm_not_bag_noder.
Print Assumptions cell4_blocked_by_mixed_joint_params.
Print Assumptions locked_iota_not_wincolcirc.
Print Assumptions locked_iota_cs_neq_span_decline_arc.
Print Assumptions locked_iota_is_cell4_candidate.
Print Assumptions locked_try_InteriorMixedHitArm.
Print Assumptions locked_chord_children_meet.
Print Assumptions locked_circ_children_meet.
Print Assumptions locked_both_windows_split_meet.
Print Assumptions locked_split_is_not_InteriorMixedHitArm.
Print Assumptions honest_next_ctor_is_I_ok_interior_not_host.
Print Assumptions cells_1_3_reuse_existing_cooks.
Print Assumptions cells_5_6_already_empty_decline.
Print Assumptions ticket_0007_iota_arm_qed_or_qex.
