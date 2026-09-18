(* ============================================================================
   NetTopologySuite.Proofs.SidecarCircIotaTags
   ----------------------------------------------------------------------------
   ADR-0007 letters after Accept: ι-gate RootTag consumer (claimId
   0007-iota-tags) and the interior mixed cook step (claimId 0007-iota-cook).
   Stacked on the six-cell gate (0007-iota-gate), the cell-4 arm stop
   (0007-iota-arm) and the exact chord × arc classifier (0007-line-arc-z).

   T2 — consumer. I_line_arc_z's (ChordEndTag, ArcEndTag) pairs are read into
   the gate's cells: tag_cell tag_interior = CellIotaCand, tag_cell of either
   μ tag = CellMuJoint. Cell 3 is the existing locked LS–CS joint
   (SidecarCircMixed.locked_mixed_ls / _cs): its classifier verdict is the Z file's
   own lv_Z08 (Hit2 with the two μ tags) and the mixed joint it inhabits is
   I_ok_mixed, unchanged. Cell 4 is a NEW integer proper-cross fixture — the
   chord (0,4)→(5,4) through span_arc_A's own mid (3,4) — because the existing
   cell-4 fixture runs through the irrational radical point p+ and cannot be
   fed to I_line_arc_z. On it the classifier says Hit1 RootPlus hen_plus
   tag_interior, and the sidecar I_ok_interior Hit (p = (3,4), t_i = 3/5,
   t_j = arc_t span_arc_A (3,4)) is inhabited and is still not host I_ok.

   T3 — cook step. cooked_line_arc_try consumes the classifier verdict for
   the hen (Hit1: its named root's hen; Hit2: hen_plus, one Hit per sidecar
   IHit — MintTwo is two steps) and the sidecar I_ok_interior IHit for the
   parameters: chord_split at t_i, span_split at t_j. It allocates nothing on
   ILAEmpty / ILATouch / ILADecline, and nothing on IEmpty / IDecline. On the
   locked pair both leftover pairs meet at (3,4). The classifier does not
   produce (p*, t_i, t_j) — that is exactly what I_ok_interior supplies; no t
   is faked from endpoints.

   T3b — host scope. QEX: mixed stays sidecar.
   ~ first_cook_scope EggChord EggCircularArc is re-proved here as the fence.
   The donut machine is sidecar-complete on this pair class, not
   host-complete: cooked_line_arc_try is not try_cook_hit and I_ok_interior
   is not I_ok.

   Honesty fences:
     InteriorMixedHitArm (I_ok_mixed Hit ∧ interior_span_params) stays
     uninhabited; this letter lands on I_ok_interior, the ctor
     0007-iota-arm named as the honest next one. Not a remint of I_ok_mixed.
     Host CircGamma is CircGammaDischarged. Not Γ. Not LeftoverBagTermArm.
     Not H⊥ / Multi Landed / NURBS first cook / a new oracle keyword.
     CircularCookLineArcZ.v is imported; nothing atan2 flows back into it.

   WITNESS topic: overlay · claimId: 0007-iota-tags · witness: 0007-iota-tags
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via SidecarCircIotaGate /
     SidecarCircInterior / SidecarCircInteriorHit / CircularCookSpan). Same lineage as Parks ι;
     no extra axioms. CircularCookLineArcZ stays 0-axiom.
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import ZArith Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry ArcOrient ArcIntersect
  ArcSpanAtan2 CircularCookHit CircularCookSpan CircularCookZ CircularCookLineArcZ.
From NTS.Proofs Require CircularCookSpanSplit.
From NTS.Proofs Require SidecarCircMixed.
From NTS.Proofs Require SidecarCircInterior.
From NTS.Proofs Require SidecarCircInteriorHit.
From NTS.Proofs Require SidecarCircIotaGate.
Local Open Scope R_scope.

Definition CircEgg := CircularArc.
Definition I_ok_interior := SidecarCircInteriorHit.I_ok_interior.
Definition I_ok_mixed := SidecarCircInterior.I_ok_mixed.
Definition MixLsCs := SidecarCircInterior.MixLsCs.
Definition interior_span_params := SidecarCircInterior.interior_span_params.

(* -------------------------------------------------------------------------- *)
(* §1  Tags → cells.                                                          *)
(* -------------------------------------------------------------------------- *)

Definition tag_cell (t : RootTag) : SidecarCircIotaGate.IotaGateCell :=
  match rt_chord t, rt_arc t with
  | ChordInterior, ArcInterior => SidecarCircIotaGate.CellIotaCand
  | ChordEnd, ArcAtStart => SidecarCircIotaGate.CellMuJoint
  | ChordStart, ArcAtEnd => SidecarCircIotaGate.CellMuJoint
  | _, _ => SidecarCircIotaGate.CellDecline
  end.

Lemma tag_cell_interior : tag_cell tag_interior = SidecarCircIotaGate.CellIotaCand.
Proof. reflexivity. Qed.
Lemma tag_cell_mu_end_start : tag_cell tag_mu_end_start = SidecarCircIotaGate.CellMuJoint.
Proof. reflexivity. Qed.
Lemma tag_cell_mu_start_end : tag_cell tag_mu_start_end = SidecarCircIotaGate.CellMuJoint.
Proof. reflexivity. Qed.

(* Integer points read into the sheet. *)
Definition zpt_R (p : ZPt) : Point := mkPoint (IZR (zx p)) (IZR (zy p)).

(* -------------------------------------------------------------------------- *)
(* §2  Cell 3 / μ: the locked LS–CS joint, tags from lv_Z08.                  *)
(* -------------------------------------------------------------------------- *)

Lemma mu_fixture_is_locked_mixed_ls :
  mkChordEgg (zpt_R (zp (-5) 0)) (zpt_R (zp 5 0)) = SidecarCircMixed.locked_mixed_ls.
Proof. reflexivity. Qed.

Lemma mu_fixture_is_locked_mixed_cs :
  mkCircularArc (zpt_R zL_A) (zpt_R zL_M) (zpt_R zL_C) = SidecarCircMixed.locked_mixed_cs.
Proof. reflexivity. Qed.

(* WITNESS {"claimId":"0007-iota-tags","topic":"overlay","lemma":"mu_joint_tags_consumed","title":"iota tags cell 3: the classifier's two mu tags on the locked LS-CS joint read to CellMuJoint, the joint inhabits the existing I_ok_mixed (no new kernel) and the gate says CellMuJoint","file":"theories/SidecarCircIotaTags.v","witness":"0007-iota-tags","board":"ADR-0007"} *)
Theorem mu_joint_tags_consumed :
  I_line_arc_z (zp (-5) 0) (zp 5 0) zL_A zL_M zL_C
    = ILAHit2 hen_plus hen_minus tag_mu_end_start tag_mu_start_end
  /\ tag_cell tag_mu_end_start = SidecarCircIotaGate.CellMuJoint
  /\ tag_cell tag_mu_start_end = SidecarCircIotaGate.CellMuJoint
  /\ I_ok_mixed (MixLsCs SidecarCircMixed.locked_mixed_ls SidecarCircMixed.locked_mixed_cs)
       (SidecarCircMixed.ls_cs_joint_hit SidecarCircMixed.locked_mixed_ls
                                          SidecarCircMixed.locked_mixed_cs)
  /\ SidecarCircIotaGate.IotaGate
       SidecarCircIotaGate.locked_mu_win_ls SidecarCircIotaGate.locked_mu_win_cs
       (SidecarCircMixed.ls_cs_joint_hit SidecarCircMixed.locked_mixed_ls
                                          SidecarCircMixed.locked_mixed_cs)
       SidecarCircIotaGate.CellMuJoint.
Proof.
  split; [exact lv_Z08 |].
  split; [reflexivity |].
  split; [reflexivity |].
  split; [exact SidecarCircIotaGate.cell3_reuses_I_ok_mixed |].
  exact (proj1 SidecarCircIotaGate.cell3_mu_is_joint_not_iota).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Cell 4 / ι: integer proper cross through span_arc_A's mid.             *)
(* -------------------------------------------------------------------------- *)

Definition zI_P  : ZPt := zp 0 4.
Definition zI_P1 : ZPt := zp 5 4.

Definition iota_ls : ChordEgg := mkChordEgg (mkPoint 0 4) (mkPoint 5 4).
Definition iota_cs : CircEgg := span_arc_A.
Definition iota_p  : Point := mkPoint 3 4.
Definition iota_ti : R := 3 / 5.
Definition iota_tj : R := arc_t span_arc_A iota_p.
Definition iota_hit : IResult := IHit iota_p iota_ti iota_tj.

Lemma iota_fixture_is_ls :
  mkChordEgg (zpt_R zI_P) (zpt_R zI_P1) = iota_ls.
Proof. reflexivity. Qed.

Lemma iota_fixture_is_cs :
  mkCircularArc (zpt_R zQ_A) (zpt_R zQ_M) (zpt_R zQ_C) = span_arc_A.
Proof. reflexivity. Qed.

Lemma iota_p_is_mid : iota_p = arc_mid span_arc_A.
Proof. reflexivity. Qed.

(* WITNESS {"claimId":"0007-iota-tags","topic":"overlay","lemma":"iota_tags_classifier","title":"iota tags cell 4: on the integer chord (0,4)-(5,4) x span_arc_A the exact classifier says Hit1 RootPlus hen_plus tag_interior","file":"theories/SidecarCircIotaTags.v","witness":"0007-iota-tags","board":"ADR-0007"} *)
Lemma iota_tags_classifier :
  I_line_arc_z zI_P zI_P1 zQ_A zQ_M zQ_C = ILAHit1 RootPlus hen_plus tag_interior.
Proof. vm_compute. reflexivity. Qed.

Lemma iota_on_chord : on_chord iota_ls iota_ti iota_p.
Proof.
  unfold on_chord, iota_ls, iota_ti, iota_p, chord_eval. cbn [px py ce_p0 ce_p1].
  split; [lra |]. apply (f_equal2 mkPoint); lra.
Qed.

Lemma iota_p_on_circle :
  dist_sq (arc_center span_arc_A) iota_p = arc_radius span_arc_A * arc_radius span_arc_A.
Proof.
  unfold arc_radius, dist. rewrite sqrt_sqrt by apply dist_sq_nonneg.
  rewrite span_arc_A_center. unfold locked_O1, iota_p, span_arc_A, dist_sq.
  cbn [px py arc_start]. lra.
Qed.

Lemma iota_p_span_atan2 : arc_span_contains_atan2 span_arc_A iota_p.
Proof.
  apply (arc_span_contains_atan2_iff_chord_sign span_arc_A iota_p span_arc_A_valid).
  - rewrite iota_p_is_mid. apply inCircle_R_at_B.
  - rewrite iota_p_is_mid. apply arc_span_contains_mid. exact span_arc_A_valid.
Qed.

Lemma iota_on_arc_gamma : on_arc_gamma span_arc_A iota_tj iota_p.
Proof.
  unfold iota_tj. apply arc_gamma_retract.
  - exact span_arc_A_valid.
  - exact iota_p_on_circle.
  - exact span_arc_A_mid_principal.
  - exact iota_p_span_atan2.
Qed.

Lemma iota_p_neq_start : iota_p <> arc_start span_arc_A.
Proof. unfold iota_p, span_arc_A. cbn. intro H. apply (f_equal px) in H. cbn in H. lra. Qed.

Lemma iota_p_neq_end : iota_p <> arc_end span_arc_A.
Proof. unfold iota_p, span_arc_A. cbn. intro H. apply (f_equal px) in H. cbn in H. lra. Qed.

Lemma iota_tj_interior : 0 < iota_tj < 1.
Proof.
  destruct iota_on_arc_gamma as [[Hlo Hhi] Heq].
  split.
  - destruct (Rle_lt_or_eq_dec _ _ Hlo) as [Hlt | Heq0]; [exact Hlt |].
    rewrite <- Heq0 in Heq. rewrite (arc_gamma_start span_arc_A span_arc_A_valid) in Heq.
    exfalso. exact (iota_p_neq_start Heq).
  - destruct (Rle_lt_or_eq_dec _ _ Hhi) as [Hlt | Heq1]; [exact Hlt |].
    rewrite Heq1 in Heq. rewrite (arc_gamma_end span_arc_A span_arc_A_valid) in Heq.
    exfalso. exact (iota_p_neq_end Heq).
Qed.

Lemma iota_params : interior_span_params iota_ti iota_tj.
Proof.
  unfold interior_span_params, SidecarCircInterior.interior_span_params,
         SidecarCircMixed.interior_span_params, CircularCookCsConcat.interior_span_params,
         iota_ti.
  split; [lra | exact iota_tj_interior].
Qed.

(* WITNESS {"claimId":"0007-iota-tags","topic":"overlay","lemma":"iota_I_ok_interior","title":"iota tags cell 4: the integer proper-cross pair inhabits sidecar I_ok_interior at interior_span_params","file":"theories/SidecarCircIotaTags.v","witness":"0007-iota-tags","board":"ADR-0007"} *)
Theorem iota_I_ok_interior :
  I_ok_interior (MixLsCs iota_ls iota_cs) iota_hit.
Proof.
  unfold I_ok_interior, SidecarCircInteriorHit.I_ok_interior, iota_hit, iota_cs,
         SidecarCircInterior.I_ok_mixed_interior_arm.
  split; [exact span_arc_A_valid |].
  split; [exact iota_on_chord |].
  split; [exact iota_on_arc_gamma |].
  exact iota_params.
Qed.

Lemma iota_gate_cell4 :
  SidecarCircIotaGate.IotaGate
    (SidecarCircIotaGate.WinChord iota_ls)
    (SidecarCircIotaGate.WinCirc iota_cs span_arc_A_valid)
    iota_hit SidecarCircIotaGate.CellIotaCand.
Proof.
  eapply SidecarCircIotaGate.GateIotaCand.
  - left. split; exact I.
  - reflexivity.
  - exact iota_params.
Qed.

Lemma iota_hit_not_host_I_ok :
  ~ I_ok (MkChord iota_ls) (MkOutOfScope EggCircularArc) iota_hit.
Proof. intro H. exact H. Qed.

Lemma iota_hit_not_I_ok_mixed :
  ~ I_ok_mixed (MixLsCs iota_ls iota_cs) iota_hit.
Proof.
  apply SidecarCircInteriorHit.I_ok_interior_hit_not_I_ok_mixed.
  exact iota_I_ok_interior.
Qed.

(* WITNESS {"claimId":"0007-iota-tags","topic":"overlay","lemma":"ticket_0007_iota_tags_qed_or_qex","title":"iota tag consumer: a locked integer proper-cross fixture whose classifier tag is tag_interior reads to CellIotaCand, inhabits sidecar I_ok_interior Hit with hen_plus, is gated CellIotaCand, and is not host I_ok nor I_ok_mixed (QED); or the classifier says Hit with tag_interior and the gate still returns the missing-arm constructor (QEX); discharged QED; InteriorMixedHitArm stays uninhabited, the landing ctor is I_ok_interior","file":"theories/SidecarCircIotaTags.v","witness":"0007-iota-tags","board":"ADR-0007"} *)
Theorem ticket_0007_iota_tags_qed_or_qex :
  (I_line_arc_z zI_P zI_P1 zQ_A zQ_M zQ_C = ILAHit1 RootPlus hen_plus tag_interior
   /\ tag_cell tag_interior = SidecarCircIotaGate.CellIotaCand
   /\ I_ok_interior (MixLsCs iota_ls iota_cs) iota_hit
   /\ SidecarCircIotaGate.IotaGate
        (SidecarCircIotaGate.WinChord iota_ls)
        (SidecarCircIotaGate.WinCirc iota_cs span_arc_A_valid)
        iota_hit SidecarCircIotaGate.CellIotaCand
   /\ ~ I_ok (MkChord iota_ls) (MkOutOfScope EggCircularArc) iota_hit
   /\ ~ I_ok_mixed (MixLsCs iota_ls iota_cs) iota_hit
   /\ ~ SidecarCircInterior.interior_mixed_constructor_inhabits
          SidecarCircInterior.InteriorMixedHitArm)
  \/
  (exists r h tag,
     I_line_arc_z zI_P zI_P1 zQ_A zQ_M zQ_C = ILAHit1 r h tag /\ tag = tag_interior
     /\ ~ I_ok_interior (MixLsCs iota_ls iota_cs) iota_hit).
Proof.
  left.
  split; [exact iota_tags_classifier |].
  split; [reflexivity |].
  split; [exact iota_I_ok_interior |].
  split; [exact iota_gate_cell4 |].
  split; [exact iota_hit_not_host_I_ok |].
  split; [exact iota_hit_not_I_ok_mixed |].
  exact SidecarCircInterior.interior_mixed_hit_arm_missing.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  T3: the interior mixed cook step.                                      *)
(* -------------------------------------------------------------------------- *)

Record MixedCookedPair : Type := mkMixedCookedPair {
  mcp_hen : Hen;
  mcp_p : Point;
  mcp_chord_l : ChordEgg;
  mcp_chord_r : ChordEgg;
  mcp_arc_l : CircularCookSpanSplit.SpanLeftover;
  mcp_arc_r : CircularCookSpanSplit.SpanLeftover
}.

Definition is_iota_cand (t : RootTag) : bool :=
  match rt_chord t, rt_arc t with ChordInterior, ArcInterior => true | _, _ => false end.

(* The classifier verdict gives the hen; the sidecar IHit gives (p, t_i, t_j).
   Hit1: the hen of its named root. Hit2: hen_plus for this IHit (MintTwo is a
   second step on the minus root). Touch / Empty / Decline, and any non-Hit
   IResult, allocate nothing. *)
Definition cooked_line_arc_try (r : ILAResult) (c : ChordEgg) (a : CircEgg) (o : IResult)
  : option MixedCookedPair :=
  match r, o with
  | ILAHit1 _ h tag, IHit p ti tj =>
      if is_iota_cand tag then
        let sc := chord_split c ti in
        let sa := CircularCookSpanSplit.span_split a tj in
        Some (mkMixedCookedPair h p (fst sc) (snd sc) (fst sa) (snd sa))
      else None
  | ILAHit2 hp _ tagp _, IHit p ti tj =>
      if is_iota_cand tagp then
        let sc := chord_split c ti in
        let sa := CircularCookSpanSplit.span_split a tj in
        Some (mkMixedCookedPair hp p (fst sc) (snd sc) (fst sa) (snd sa))
      else None
  | _, _ => None
  end.

Lemma cooked_line_arc_empty_none :
  forall c a o, cooked_line_arc_try ILAEmpty c a o = None.
Proof. intros c a []; reflexivity. Qed.
Lemma cooked_line_arc_touch_none :
  forall h t c a o, cooked_line_arc_try (ILATouch h t) c a o = None.
Proof. intros h t c a []; reflexivity. Qed.
Lemma cooked_line_arc_decline_none :
  forall c a o, cooked_line_arc_try ILADecline c a o = None.
Proof. intros c a []; reflexivity. Qed.
Lemma cooked_line_arc_iempty_none :
  forall r c a, cooked_line_arc_try r c a IEmpty = None.
Proof. intros [] c a; reflexivity. Qed.
Lemma cooked_line_arc_idecline_none :
  forall r c a, cooked_line_arc_try r c a IDecline = None.
Proof. intros [] c a; reflexivity. Qed.

Definition iota_cooked : MixedCookedPair :=
  mkMixedCookedPair hen_plus iota_p
    (fst (chord_split iota_ls iota_ti)) (snd (chord_split iota_ls iota_ti))
    (fst (CircularCookSpanSplit.span_split iota_cs iota_tj))
    (snd (CircularCookSpanSplit.span_split iota_cs iota_tj)).

Lemma cooked_line_arc_locked_some :
  cooked_line_arc_try (I_line_arc_z zI_P zI_P1 zQ_A zQ_M zQ_C) iota_ls iota_cs iota_hit
  = Some iota_cooked.
Proof. rewrite iota_tags_classifier. reflexivity. Qed.

Lemma iota_leftovers_meet :
  ce_p1 (mcp_chord_l iota_cooked) = iota_p
  /\ ce_p0 (mcp_chord_r iota_cooked) = iota_p
  /\ CircularCookSpanSplit.span_leftover_eval (mcp_arc_l iota_cooked) 1 = iota_p
  /\ CircularCookSpanSplit.span_leftover_eval (mcp_arc_r iota_cooked) 0 = iota_p.
Proof.
  unfold iota_cooked. cbn [mcp_chord_l mcp_chord_r mcp_arc_l mcp_arc_r].
  destruct (chord_split_join iota_ls iota_ti) as [Hc1 Hc2].
  destruct (CircularCookSpanSplit.span_split_join iota_cs iota_tj) as [Ha1 Ha2].
  destruct iota_on_chord as [_ Hpc].
  destruct iota_on_arc_gamma as [_ Hpa].
  rewrite Hc1, Hc2, Ha1, Ha2. unfold iota_cs. rewrite <- Hpc, <- Hpa.
  repeat split; reflexivity.
Qed.

(* WITNESS {"claimId":"0007-iota-cook","topic":"overlay","lemma":"ticket_0007_iota_cook_qed_or_qex","title":"interior mixed cook step: on the locked integer proper-cross pair cooked_line_arc_try mints hen_plus from the classifier and splits both eggs at the sidecar I_ok_interior parameters, leftovers meet at the hen point, nothing is allocated on Empty/Touch/Decline, Empty <> Decline, host first_cook_scope unchanged (QED); or the split cannot be stated because only tags and no parameters exist (QEX); discharged QED via I_ok_interior's (p,ti,tj), no t faked from endpoints","file":"theories/SidecarCircIotaTags.v","witness":"0007-iota-cook","board":"ADR-0007"} *)
Theorem ticket_0007_iota_cook_qed_or_qex :
  (cooked_line_arc_try (I_line_arc_z zI_P zI_P1 zQ_A zQ_M zQ_C) iota_ls iota_cs iota_hit
     = Some iota_cooked
   /\ mcp_hen iota_cooked = hen_plus
   /\ mcp_p iota_cooked = iota_p
   /\ ce_p1 (mcp_chord_l iota_cooked) = iota_p
   /\ ce_p0 (mcp_chord_r iota_cooked) = iota_p
   /\ CircularCookSpanSplit.span_leftover_eval (mcp_arc_l iota_cooked) 1 = iota_p
   /\ CircularCookSpanSplit.span_leftover_eval (mcp_arc_r iota_cooked) 0 = iota_p
   /\ (forall c a o, cooked_line_arc_try ILAEmpty c a o = None)
   /\ (forall h t c a o, cooked_line_arc_try (ILATouch h t) c a o = None)
   /\ (forall c a o, cooked_line_arc_try ILADecline c a o = None)
   /\ (forall r c a, cooked_line_arc_try r c a IEmpty = None)
   /\ (forall r c a, cooked_line_arc_try r c a IDecline = None)
   /\ IEmpty <> IDecline
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ try_cook_hit (mkChicken 0%nat 1%nat (MkChord iota_ls))
                   (mkChicken 2%nat 3%nat (MkOutOfScope EggCircularArc))
                   iota_hit hen_plus = None)
  \/
  (forall p ti tj, ~ I_ok_interior (MixLsCs iota_ls iota_cs) (IHit p ti tj)).
Proof.
  left.
  destruct iota_leftovers_meet as [H1 [H2 [H3 H4]]].
  split; [exact cooked_line_arc_locked_some |].
  split; [reflexivity |].
  split; [reflexivity |].
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |]. split; [exact H4 |].
  split; [exact cooked_line_arc_empty_none |].
  split; [exact cooked_line_arc_touch_none |].
  split; [exact cooked_line_arc_decline_none |].
  split; [exact cooked_line_arc_iempty_none |].
  split; [exact cooked_line_arc_idecline_none |].
  split; [exact IEmpty_neq_IDecline |].
  split; [exact chord_circular_not_first_cook_scope |].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  T3b: host scope — QEX, mixed stays sidecar.                            *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-iota-cook","topic":"overlay","lemma":"ticket_0007_iota_host_scope_qed_or_qex","title":"host scope for chord x circular arc: first_cook_scope EggChord EggCircularArc with a host I_ok Hit on the locked pair (QED) or mixed stays sidecar (QEX); discharged QEX: the donut machine is sidecar-complete on this class, not host-complete","file":"theories/SidecarCircIotaTags.v","witness":"0007-iota-cook","board":"ADR-0007"} *)
Theorem ticket_0007_iota_host_scope_qed_or_qex :
  (first_cook_scope EggChord EggCircularArc
   /\ exists p ti tj, I_ok (MkChord iota_ls) (MkOutOfScope EggCircularArc) (IHit p ti tj))
  \/
  (~ first_cook_scope EggChord EggCircularArc
   /\ (forall p ti tj, ~ I_ok (MkChord iota_ls) (MkOutOfScope EggCircularArc) (IHit p ti tj))
   /\ I_ok (MkChord iota_ls) (MkOutOfScope EggCircularArc) IDecline
   /\ I_ok_interior (MixLsCs iota_ls iota_cs) iota_hit).
Proof.
  right.
  split; [exact chord_circular_not_first_cook_scope |].
  split; [intros p ti tj H; exact H |].
  split; [intro H; exact H |].
  exact iota_I_ok_interior.
Qed.

Print Assumptions tag_cell_interior.
Print Assumptions mu_joint_tags_consumed.
Print Assumptions iota_tags_classifier.
Print Assumptions iota_I_ok_interior.
Print Assumptions ticket_0007_iota_tags_qed_or_qex.
Print Assumptions ticket_0007_iota_cook_qed_or_qex.
Print Assumptions ticket_0007_iota_host_scope_qed_or_qex.
