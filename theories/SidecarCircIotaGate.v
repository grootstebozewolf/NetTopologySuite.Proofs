(* ============================================================================
   NetTopologySuite.Proofs.SidecarCircIotaGate
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: ι complete gate on circ/chord windows
   (claimId 0007-iota-gate). Then 𝓘 cook on those cells.

   A pair of windows that arrived as circular and/or chord is classified
   by exactly one of six cells:

     1. Both demote to collinear chords → chord × chord first cook
        (not ι, not μ).
     2. circ × circ (neither demotes) → unique-Hit / Empty / two-Hit
        Decline (existing circular cook). Not ι.
     3. circ × chord after demote, mixed_joint_params, endpoint → μ
        (I_ok_mixed joint). Not ι.
     4. circ × chord, mixed_joint_params context, both params interior
        → ι candidate (interior_span_params).
     5. miss → Empty.
     6. anything else on this pair sort → Decline, not ι.

   Pairwise exclusive + complete. Collinear CircularString-as-chord
   (WinColCirc) takes cell 1, never cell 4.

   Cook reuse (do not remint):
     cell 1 — host I_ok first cook (already QED).
     cell 2 — CircularCook / I_ok_circ / MkCirc (already QED).
     cell 3 — I_ok_mixed endpoint μ (already QED).
     cell 4 — InteriorMixedHitArm = I_ok_mixed Hit ∧ interior_span_params.
              Locked interior pair inhabits I_ok_interior / the named
              interior arm, not I_ok_mixed. Host cannot inhabit the arm
              without dropping mixed_joint_params. Cook stays QEX.
              Do not fake LoopDischarged / first-cook expand / split.

   Honesty fences:
     Host CircGamma is CircGammaDischarged (MkCirc). Do not remint Γ.
     I_ok_circ / I_ok_mixed / I_ok_interior Hit ≠ host I_ok.
     mixed_joint_params stands. Do not drop it.
     Not LeftoverBagTermArm / LoopDischarged. Not NURBS / clothoid /
     ellipse. Not GEOS / C API / Overlay. Not GeometryNoder.
     Sidecar ≠ host try_cook_hit. Not SQL/MM done.

   WITNESS topic: overlay · claimId: 0007-iota-gate
   witness: 0007-iota-gate
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via SidecarCircInterior* /
     SidecarCircMixed / CircularCookSpan). Category C audit-exception:
     same atan2 lineage as Parks ι; no extra axioms.
   Host lane stays 3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  CircularCook CircularCookHit CircularCookSpan CircularCookOkCirc
  CircularCookMkCirc.
From NTS.Proofs Require CircularCookCsConcat.
From NTS.Proofs Require CircularCookSpanFilter.
From NTS.Proofs Require CircularCookCpConcat.
From NTS.Proofs Require SidecarCircMixed.
From NTS.Proofs Require SidecarCircInterior.
From NTS.Proofs Require SidecarCircInteriorHit.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=iota-gate claim=0007-iota-gate
   file=theories/SidecarCircIotaGate.v
   kind=QED-or-QEX-iota-complete-gate
   reuse=I_ok,I_ok_circ,I_ok_mixed,interior_span_params,mixed_joint_params
   not=new-kernel,CircGamma-remint,I_ok_mixed-remint,first-cook-expand
   not=LeftoverBagTermArm,LoopDischarged,NURBS,clothoid,ellipse
   park=InteriorMixedHitArm,host-interior-cook
   land=iota-gate-complete-exclusive *)

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma fence (load-bearing, not decoration).             *)
(* -------------------------------------------------------------------------- *)

Lemma iota_gate_host_circgamma_discharged :
  circular_gamma_status = CircGammaDischarged.
Proof.
  exact circular_gamma_is_discharged.
Qed.

Lemma iota_gate_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma iota_gate_circular_is_first_cook :
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_is_first_cook_scope.
Qed.

Lemma iota_gate_first_cook_mixed :
  first_cook_scope EggChord EggCircularArc.
Proof.
  exact first_cook_scope_chord_circular.
Qed.

Lemma iota_gate_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

(* -------------------------------------------------------------------------- *)
(* Arrival windows. Demote check is the collinear CircularString fence.       *)
(* -------------------------------------------------------------------------- *)

Definition CircEgg := CircularArc.
Definition mixed_joint_params := SidecarCircInterior.mixed_joint_params.
Definition interior_span_params := SidecarCircInterior.interior_span_params.
Definition I_ok_mixed := SidecarCircInterior.I_ok_mixed.
Definition MixLsCs := SidecarCircInterior.MixLsCs.
Definition MixCsLs := SidecarCircInterior.MixCsLs.
Definition I_ok_interior := SidecarCircInteriorHit.I_ok_interior.

Inductive CircChordWin : Type :=
| WinChord (c : ChordEgg)
| WinCirc (a : CircEgg) (va : valid_arc a)
| WinColCirc (a : CircEgg) (ncol : ~ valid_arc a).

Definition win_demotes (w : CircChordWin) : Prop :=
  match w with
  | WinChord _ => True
  | WinCirc _ _ => False
  | WinColCirc _ _ => True
  end.

Definition win_remains_circ (w : CircChordWin) : Prop :=
  match w with
  | WinCirc _ _ => True
  | _ => False
  end.

Definition sort_chord_chord (w1 w2 : CircChordWin) : Prop :=
  win_demotes w1 /\ win_demotes w2.

Definition sort_circ_circ (w1 w2 : CircChordWin) : Prop :=
  win_remains_circ w1 /\ win_remains_circ w2.

Definition sort_mixed (w1 w2 : CircChordWin) : Prop :=
  (win_demotes w1 /\ win_remains_circ w2) \/
  (win_remains_circ w1 /\ win_demotes w2).

Inductive IotaGateCell : Type :=
| CellChordChord
| CellCircCirc
| CellMuJoint
| CellIotaCand
| CellMiss
| CellDecline.

Inductive IotaGate (w1 w2 : CircChordWin) (o : IResult)
  : IotaGateCell -> Prop :=
| GateChordChord :
    sort_chord_chord w1 w2 ->
    IotaGate w1 w2 o CellChordChord
| GateCircCirc :
    sort_circ_circ w1 w2 ->
    IotaGate w1 w2 o CellCircCirc
| GateMuJoint (p : Point) (ti tj : R) :
    sort_mixed w1 w2 ->
    o = IHit p ti tj ->
    mixed_joint_params ti tj ->
    IotaGate w1 w2 o CellMuJoint
| GateIotaCand (p : Point) (ti tj : R) :
    sort_mixed w1 w2 ->
    o = IHit p ti tj ->
    interior_span_params ti tj ->
    IotaGate w1 w2 o CellIotaCand
| GateMiss :
    sort_mixed w1 w2 ->
    o = IEmpty ->
    IotaGate w1 w2 o CellMiss
| GateDeclineHit (p : Point) (ti tj : R) :
    sort_mixed w1 w2 ->
    o = IHit p ti tj ->
    ~ mixed_joint_params ti tj ->
    ~ interior_span_params ti tj ->
    IotaGate w1 w2 o CellDecline
| GateDeclineTag :
    sort_mixed w1 w2 ->
    o = IDecline ->
    IotaGate w1 w2 o CellDecline.

(* -------------------------------------------------------------------------- *)
(* Sort trichotomy. Definitional on the three window constructors.            *)
(* -------------------------------------------------------------------------- *)

Lemma win_demotes_xor_circ :
  forall w,
    (win_demotes w /\ ~ win_remains_circ w) \/
    (win_remains_circ w /\ ~ win_demotes w).
Proof.
  intros [c | a va | a ncol]; simpl.
  - left. split; [exact I | intros H; exact H].
  - right. split; [exact I | intros H; exact H].
  - left. split; [exact I | intros H; exact H].
Qed.

Lemma sort_trichotomy :
  forall w1 w2,
    sort_chord_chord w1 w2 \/ sort_circ_circ w1 w2 \/ sort_mixed w1 w2.
Proof.
  intros w1 w2.
  destruct (win_demotes_xor_circ w1) as [[Hd1 Hn1] | [Hr1 Hn1]];
    destruct (win_demotes_xor_circ w2) as [[Hd2 Hn2] | [Hr2 Hn2]].
  - left. split; assumption.
  - right. right. left. split; assumption.
  - right. right. right. split; assumption.
  - right. left. split; assumption.
Qed.

Lemma sort_cc_not_aa :
  forall w1 w2, sort_chord_chord w1 w2 -> ~ sort_circ_circ w1 w2.
Proof.
  intros w1 w2 [Hd1 _] [Hr1 _].
  destruct (win_demotes_xor_circ w1) as [[_ Hn] | [_ Hn]].
  - exact (Hn Hr1).
  - exact (Hn Hd1).
Qed.

Lemma sort_cc_not_mixed :
  forall w1 w2, sort_chord_chord w1 w2 -> ~ sort_mixed w1 w2.
Proof.
  intros w1 w2 [Hd1 Hd2] [[_ Hr2] | [Hr1 _]].
  - destruct (win_demotes_xor_circ w2) as [[_ Hn] | [_ Hn]].
    + exact (Hn Hr2).
    + exact (Hn Hd2).
  - destruct (win_demotes_xor_circ w1) as [[_ Hn] | [_ Hn]].
    + exact (Hn Hr1).
    + exact (Hn Hd1).
Qed.

Lemma sort_aa_not_mixed :
  forall w1 w2, sort_circ_circ w1 w2 -> ~ sort_mixed w1 w2.
Proof.
  intros w1 w2 [Hr1 Hr2] [[Hd1 _] | [_ Hd2]].
  - destruct (win_demotes_xor_circ w1) as [[_ Hn] | [_ Hn]].
    + exact (Hn Hr1).
    + exact (Hn Hd1).
  - destruct (win_demotes_xor_circ w2) as [[_ Hn] | [_ Hn]].
    + exact (Hn Hr2).
    + exact (Hn Hd2).
Qed.

(* -------------------------------------------------------------------------- *)
(* Parameter trichotomy on a mixed Hit.                                       *)
(* -------------------------------------------------------------------------- *)

Lemma interior_or_not :
  forall ti tj,
    interior_span_params ti tj \/ ~ interior_span_params ti tj.
Proof.
  intros ti tj.
  unfold interior_span_params, SidecarCircInterior.interior_span_params,
         SidecarCircMixed.interior_span_params,
         CircularCookCsConcat.interior_span_params.
  destruct (Rlt_dec 0 ti) as [A|A];
    destruct (Rlt_dec ti 1) as [B|B];
    destruct (Rlt_dec 0 tj) as [C|C];
    destruct (Rlt_dec tj 1) as [D|D].
  - left. split; split; assumption.
  - right. intros [_ [_ Hd]]. exact (D Hd).
  - right. intros [_ [Hc _]]. exact (C Hc).
  - right. intros [_ [Hc _]]. exact (C Hc).
  - right. intros [[_ Hb] _]. exact (B Hb).
  - right. intros [[_ Hb] _]. exact (B Hb).
  - right. intros [[_ Hb] _]. exact (B Hb).
  - right. intros [[_ Hb] _]. exact (B Hb).
  - right. intros [[Ha _] _]. exact (A Ha).
  - right. intros [[Ha _] _]. exact (A Ha).
  - right. intros [[Ha _] _]. exact (A Ha).
  - right. intros [[Ha _] _]. exact (A Ha).
  - right. intros [[Ha _] _]. exact (A Ha).
  - right. intros [[Ha _] _]. exact (A Ha).
  - right. intros [[Ha _] _]. exact (A Ha).
  - right. intros [[Ha _] _]. exact (A Ha).
Qed.

Lemma joint_or_not :
  forall ti tj,
    mixed_joint_params ti tj \/ ~ mixed_joint_params ti tj.
Proof.
  intros ti tj.
  unfold mixed_joint_params, SidecarCircInterior.mixed_joint_params,
         SidecarCircMixed.mixed_joint_params.
  destruct (Req_EM_T ti 1) as [Eti1|Nti1];
    destruct (Req_EM_T tj 0) as [Etj0|Ntj0].
  - left. left. split; assumption.
  - destruct (Req_EM_T ti 0) as [Eti0|Nti0];
      destruct (Req_EM_T tj 1) as [Etj1|Ntj1].
    + exfalso. lra.
    + exfalso. lra.
    + right. intros [[_ H0] | [H0 _]].
      * exact (Ntj0 H0).
      * exact (Nti0 H0).
    + right. intros [[_ H0] | [_ H1]].
      * exact (Ntj0 H0).
      * exact (Ntj1 H1).
  - destruct (Req_EM_T ti 0) as [Eti0|Nti0];
      destruct (Req_EM_T tj 1) as [Etj1|Ntj1].
    + left. right. split; assumption.
    + right. intros [[H1 _] | [_ H1]].
      * exact (Nti1 H1).
      * exact (Ntj1 H1).
    + right. intros [[H1 _] | [H0 _]].
      * exact (Nti1 H1).
      * exact (Nti0 H0).
    + right. intros [[H1 _] | [H0 _]].
      * exact (Nti1 H1).
      * exact (Nti0 H0).
  - destruct (Req_EM_T ti 0) as [Eti0|Nti0];
      destruct (Req_EM_T tj 1) as [Etj1|Ntj1].
    + left. right. split; assumption.
    + right. intros [[H1 _] | [_ H1]].
      * exact (Nti1 H1).
      * exact (Ntj1 H1).
    + right. intros [[H1 _] | [H0 _]].
      * exact (Nti1 H1).
      * exact (Nti0 H0).
    + right. intros [[H1 H0] | [H0 H1]].
      * exact (Nti1 H1).
      * exact (Nti0 H0).
Qed.

Lemma joint_not_interior :
  forall ti tj,
    mixed_joint_params ti tj -> ~ interior_span_params ti tj.
Proof.
  exact SidecarCircMixed.mixed_joint_params_not_interior.
Qed.

(* -------------------------------------------------------------------------- *)
(* Exclusive + complete.                                                      *)
(* -------------------------------------------------------------------------- *)

Definition iota_cell_pred (w1 w2 : CircChordWin) (o : IResult)
  (c : IotaGateCell) : Prop :=
  match c with
  | CellChordChord => sort_chord_chord w1 w2
  | CellCircCirc => sort_circ_circ w1 w2
  | CellMuJoint =>
      sort_mixed w1 w2 /\
      (exists p ti tj, o = IHit p ti tj /\ mixed_joint_params ti tj)
  | CellIotaCand =>
      sort_mixed w1 w2 /\
      (exists p ti tj, o = IHit p ti tj /\ interior_span_params ti tj)
  | CellMiss => sort_mixed w1 w2 /\ o = IEmpty
  | CellDecline =>
      sort_mixed w1 w2 /\
      (o = IDecline \/
       exists p ti tj,
         o = IHit p ti tj /\
         ~ mixed_joint_params ti tj /\
         ~ interior_span_params ti tj)
  end.

Lemma IotaGate_iff_pred :
  forall w1 w2 o c,
    IotaGate w1 w2 o c <-> iota_cell_pred w1 w2 o c.
Proof.
  intros w1 w2 o c.
  split.
  - intros H. destruct H; simpl.
    + exact H.
    + exact H.
    + split; [exact H|]. exists p, ti, tj. split; [exact H0 | exact H1].
    + split; [exact H|]. exists p, ti, tj. split; [exact H0 | exact H1].
    + split; [exact H | exact H0].
    + split; [exact H|]. right. exists p, ti, tj.
      split; [exact H0 | split; [exact H1 | exact H2]].
    + split; [exact H|]. left. exact H0.
  - intros H. destruct c; simpl in H.
    + constructor. exact H.
    + constructor. exact H.
    + destruct H as [Hmx [p [ti [tj [Heq Hj]]]]].
      eapply GateMuJoint; [exact Hmx | exact Heq | exact Hj].
    + destruct H as [Hmx [p [ti [tj [Heq Hi]]]]].
      eapply GateIotaCand; [exact Hmx | exact Heq | exact Hi].
    + destruct H as [Hmx Heq]. constructor; [exact Hmx | exact Heq].
    + destruct H as [Hmx [Hdec | [p [ti [tj [Heq [Hnj Hni]]]]]]].
      * apply GateDeclineTag; [exact Hmx | exact Hdec].
      * eapply GateDeclineHit; [exact Hmx | exact Heq | exact Hnj | exact Hni].
Qed.

Lemma iota_cell_pred_exclusive :
  forall w1 w2 o c1 c2,
    iota_cell_pred w1 w2 o c1 ->
    iota_cell_pred w1 w2 o c2 ->
    c1 = c2.
Proof.
  intros w1 w2 o c1 c2 H1 H2.
  destruct c1; destruct c2; simpl in H1, H2;
    try reflexivity;
    try (exfalso; eapply sort_cc_not_aa; eassumption);
    try (exfalso; eapply sort_cc_not_mixed;
         [exact H1 | destruct H2 as [Hmx _]; exact Hmx]);
    try (exfalso; eapply sort_cc_not_mixed;
         [exact H2 | destruct H1 as [Hmx _]; exact Hmx]);
    try (exfalso; eapply sort_aa_not_mixed;
         [exact H1 | destruct H2 as [Hmx _]; exact Hmx]);
    try (exfalso; eapply sort_aa_not_mixed;
         [exact H2 | destruct H1 as [Hmx _]; exact Hmx]).
  - (* Mu / Iota *)
    destruct H1 as [_ [p [ti [tj [Heq Hj]]]]].
    destruct H2 as [_ [p' [ti' [tj' [Heq' Hi]]]]].
    rewrite Heq in Heq'. inversion Heq'; subst.
    exfalso. exact (joint_not_interior ti' tj' Hj Hi).
  - (* Mu / Miss *)
    destruct H1 as [_ [p [ti [tj [Heq _]]]]].
    destruct H2 as [_ Heq']. rewrite Heq in Heq'. discriminate.
  - (* Mu / Decline *)
    destruct H1 as [_ [p [ti [tj [Heq Hj]]]]].
    destruct H2 as [_ [Hdec | [p' [ti' [tj' [Heq' [Hnj _]]]]]]].
    + rewrite Heq in Hdec. discriminate.
    + rewrite Heq in Heq'. inversion Heq'; subst.
      exfalso. exact (Hnj Hj).
  - (* Iota / Mu *)
    destruct H1 as [_ [p [ti [tj [Heq Hi]]]]].
    destruct H2 as [_ [p' [ti' [tj' [Heq' Hj]]]]].
    rewrite Heq in Heq'. inversion Heq'; subst.
    exfalso. exact (joint_not_interior ti' tj' Hj Hi).
  - (* Iota / Miss *)
    destruct H1 as [_ [p [ti [tj [Heq _]]]]].
    destruct H2 as [_ Heq']. rewrite Heq in Heq'. discriminate.
  - (* Iota / Decline *)
    destruct H1 as [_ [p [ti [tj [Heq Hi]]]]].
    destruct H2 as [_ [Hdec | [p' [ti' [tj' [Heq' [_ Hni]]]]]]].
    + rewrite Heq in Hdec. discriminate.
    + rewrite Heq in Heq'. inversion Heq'; subst.
      exfalso. exact (Hni Hi).
  - (* Miss / Mu *)
    destruct H1 as [_ Heq].
    destruct H2 as [_ [p [ti [tj [Heq' _]]]]].
    rewrite Heq' in Heq. discriminate.
  - (* Miss / Iota *)
    destruct H1 as [_ Heq].
    destruct H2 as [_ [p [ti [tj [Heq' _]]]]].
    rewrite Heq' in Heq. discriminate.
  - (* Miss / Decline *)
    destruct H1 as [_ Heq].
    destruct H2 as [_ [Hdec | [p [ti [tj [Heq' _]]]]]].
    + rewrite Heq in Hdec. discriminate.
    + rewrite Heq' in Heq. discriminate.
  - (* Decline / Mu *)
    destruct H1 as [_ [Hdec | [p [ti [tj [Heq [Hnj _]]]]]]].
    + destruct H2 as [_ [p' [ti' [tj' [Heq' _]]]]].
      rewrite Heq' in Hdec. discriminate.
    + destruct H2 as [_ [p' [ti' [tj' [Heq' Hj]]]]].
      rewrite Heq in Heq'. inversion Heq'; subst.
      exfalso. exact (Hnj Hj).
  - (* Decline / Iota *)
    destruct H1 as [_ [Hdec | [p [ti [tj [Heq [_ Hni]]]]]]].
    + destruct H2 as [_ [p' [ti' [tj' [Heq' _]]]]].
      rewrite Heq' in Hdec. discriminate.
    + destruct H2 as [_ [p' [ti' [tj' [Heq' Hi]]]]].
      rewrite Heq in Heq'. inversion Heq'; subst.
      exfalso. exact (Hni Hi).
  - (* Decline / Miss *)
    destruct H1 as [_ [Hdec | [p [ti [tj [Heq _]]]]]].
    + destruct H2 as [_ Heq']. rewrite Heq' in Hdec. discriminate.
    + destruct H2 as [_ Heq']. rewrite Heq in Heq'. discriminate.
Qed.

Lemma iota_gate_exclusive :
  forall w1 w2 o c1 c2,
    IotaGate w1 w2 o c1 ->
    IotaGate w1 w2 o c2 ->
    c1 = c2.
Proof.
  intros w1 w2 o c1 c2 H1 H2.
  apply IotaGate_iff_pred in H1.
  apply IotaGate_iff_pred in H2.
  eapply iota_cell_pred_exclusive; eassumption.
Qed.

Lemma iota_gate_complete :
  forall w1 w2 o, exists c, IotaGate w1 w2 o c.
Proof.
  intros w1 w2 o.
  destruct (sort_trichotomy w1 w2) as [Hcc | [Haa | Hmx]].
  - exists CellChordChord. constructor. exact Hcc.
  - exists CellCircCirc. constructor. exact Haa.
  - destruct o as [p ti tj | | ].
    + destruct (joint_or_not ti tj) as [Hj | Hnj];
        destruct (interior_or_not ti tj) as [Hi | Hni].
      * exfalso. exact (joint_not_interior ti tj Hj Hi).
      * exists CellMuJoint. eapply GateMuJoint; [exact Hmx | reflexivity | exact Hj].
      * exists CellIotaCand. eapply GateIotaCand; [exact Hmx | reflexivity | exact Hi].
      * exists CellDecline.
        eapply GateDeclineHit; [exact Hmx | reflexivity | exact Hnj | exact Hni].
    + exists CellMiss. constructor; [exact Hmx | reflexivity].
    + exists CellDecline. apply GateDeclineTag; [exact Hmx | reflexivity].
Qed.

(* WITNESS {"claimId":"0007-iota-gate","topic":"overlay","lemma":"iota_gate_cells_exclusive_and_complete","title":"iota gate: six circ/chord cells are pairwise exclusive and every arrival pair plus IResult inhabits exactly one cell; collinear CircularString-as-chord is not this theorem","file":"theories/SidecarCircIotaGate.v","witness":"0007-iota-gate","board":"ADR-0007"} *)

Theorem iota_gate_cells_exclusive_and_complete :
  (forall w1 w2 o c1 c2,
     IotaGate w1 w2 o c1 -> IotaGate w1 w2 o c2 -> c1 = c2)
  /\
  (forall w1 w2 o, exists c, IotaGate w1 w2 o c).
Proof.
  split; [exact iota_gate_exclusive | exact iota_gate_complete].
Qed.

(* -------------------------------------------------------------------------- *)
(* Collinear CircularString-as-chord: cell 1, never cell 4.                   *)
(* -------------------------------------------------------------------------- *)

Lemma col_cs_times_chord_is_cell1 :
  forall a ncol c o,
    IotaGate (WinColCirc a ncol) (WinChord c) o CellChordChord.
Proof.
  intros a ncol c o.
  constructor.
  split; exact I.
Qed.

Lemma col_cs_times_chord_not_cell4 :
  forall a ncol c o,
    ~ IotaGate (WinColCirc a ncol) (WinChord c) o CellIotaCand.
Proof.
  intros a ncol c o H.
  apply IotaGate_iff_pred in H.
  destruct H as [Hmx _].
  destruct Hmx as [[_ Hr2] | [Hr1 _]].
  - exact Hr2.
  - exact Hr1.
Qed.

Lemma col_cs_times_col_cs_is_cell1 :
  forall a na b nb o,
    IotaGate (WinColCirc a na) (WinColCirc b nb) o CellChordChord.
Proof.
  intros a na b nb o.
  constructor.
  split; exact I.
Qed.

Lemma col_cs_times_col_cs_not_cell4 :
  forall a na b nb o,
    ~ IotaGate (WinColCirc a na) (WinColCirc b nb) o CellIotaCand.
Proof.
  intros a na b nb o H.
  apply IotaGate_iff_pred in H.
  destruct H as [Hmx _].
  destruct Hmx as [[_ Hr2] | [Hr1 _]].
  - exact Hr2.
  - exact Hr1.
Qed.

Definition locked_col_cs : CircEgg :=
  CircularCookSpanFilter.span_decline_arc.

Lemma locked_col_cs_invalid : ~ valid_arc locked_col_cs.
Proof.
  exact CircularCookSpanFilter.span_decline_arc_invalid.
Qed.

Definition locked_col_win : CircChordWin :=
  WinColCirc locked_col_cs locked_col_cs_invalid.

Definition locked_col_as_chord : ChordEgg :=
  mkChordEgg (arc_start locked_col_cs) (arc_end locked_col_cs).

Definition locked_col_cross_chord : ChordEgg :=
  mkChordEgg (mkPoint 1 (-1)) (mkPoint 1 1).

Definition locked_col_cross_pt : Point := mkPoint 1 0.

Lemma locked_col_cs_as_chord_cell1 :
  forall o, IotaGate locked_col_win (WinChord locked_col_cross_chord) o
              CellChordChord
  /\ ~ IotaGate locked_col_win (WinChord locked_col_cross_chord) o
         CellIotaCand.
Proof.
  intros o.
  split.
  - apply col_cs_times_chord_is_cell1.
  - apply col_cs_times_chord_not_cell4.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cell 1 cook: reuse host I_ok. Do not remint.                               *)
(* -------------------------------------------------------------------------- *)

Lemma cell1_reuses_host_crossing_I_ok :
  I_ok (MkChord diag_ab) (MkChord diag_cd)
       (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  exact crossing_I_ok.
Qed.

Lemma cell1_reuses_host_empty_I_ok :
  I_ok (MkChord hor_bot) (MkChord hor_top) IEmpty.
Proof.
  exact disjoint_I_ok.
Qed.

Lemma locked_col_on_demoted_chord :
  on_chord locked_col_as_chord (1 / 2) locked_col_cross_pt.
Proof.
  unfold on_chord, locked_col_as_chord, locked_col_cross_pt, locked_col_cs,
         CircularCookSpanFilter.span_decline_arc, chord_eval.
  cbn [arc_start arc_end ce_p0 ce_p1 px py].
  split; [lra|].
  apply (f_equal2 mkPoint); simpl; field.
Qed.

Lemma locked_col_on_cross_chord :
  on_chord locked_col_cross_chord (1 / 2) locked_col_cross_pt.
Proof.
  unfold on_chord, locked_col_cross_chord, locked_col_cross_pt, chord_eval.
  split; [lra|].
  apply (f_equal2 mkPoint); simpl; field.
Qed.

Lemma cell1_col_cs_reuses_host_I_ok :
  I_ok (MkChord locked_col_as_chord) (MkChord locked_col_cross_chord)
       (IHit locked_col_cross_pt (1 / 2) (1 / 2)).
Proof.
  unfold I_ok.
  split; [exact locked_col_on_demoted_chord | exact locked_col_on_cross_chord].
Qed.

(* -------------------------------------------------------------------------- *)
(* Cell 2 cook: reuse CircularCook / I_ok_circ / MkCirc. Do not remint.       *)
(* -------------------------------------------------------------------------- *)

Lemma cell2_reuses_mkcirc_unique_hit :
  I_ok (MkCirc locked_circ_A) (MkCirc locked_circ_B)
       (IHit locked_circ_hit_pt locked_circ_ti locked_circ_tj).
Proof.
  exact locked_mkcirc_I_ok.
Qed.

Lemma cell2_reuses_I_ok_circ_hit :
  I_ok_circ span_arc_A span_arc_B CircularCookOkCirc.locked_ok_circ_hit.
Proof.
  exact CircularCookOkCirc.ii3_locked_plus_I_ok_circ.
Qed.

Lemma cell2_reuses_I_ok_circ_empty :
  I_ok_circ span_arc_A span_empty_far IEmpty.
Proof.
  exact CircularCookOkCirc.ii3_locked_empty.
Qed.

Lemma cell2_two_hit_existing_cook :
  I_circles_gamma 0 0 5 7 0 5 <> ICircGEmpty
  /\ I_circles_gamma 0 0 5 7 0 5 <> ICircGDecline
  /\ locked_p_plus <> locked_p_minus.
Proof.
  rewrite locked_I_circles_gamma_hit.
  split; [discriminate|].
  split; [discriminate|].
  intro Heq.
  apply (f_equal py) in Heq.
  pose proof span_p_plus_y_pos as Hy1.
  pose proof span_p_minus_y_neg as Hy2.
  lra.
Qed.

Lemma cell2_span_pair_is_circ_circ :
  forall o,
    IotaGate (WinCirc span_arc_A span_arc_A_valid)
             (WinCirc span_arc_B span_arc_B_valid) o CellCircCirc
    /\ ~ IotaGate (WinCirc span_arc_A span_arc_A_valid)
           (WinCirc span_arc_B span_arc_B_valid) o CellIotaCand.
Proof.
  intros o.
  split.
  - constructor. split; exact I.
  - intros H.
    apply IotaGate_iff_pred in H.
    destruct H as [Hmx _].
    destruct Hmx as [[Hd1 _] | [_ Hd2]].
    + exact Hd1.
    + exact Hd2.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cell 3 cook: reuse I_ok_mixed μ. Do not remint.                            *)
(* -------------------------------------------------------------------------- *)

Lemma locked_mixed_cs_valid :
  valid_arc SidecarCircMixed.locked_mixed_cs.
Proof.
  exact CircularCookCsConcat.locked_cs_arc_2_valid.
Qed.

Definition locked_mu_win_ls : CircChordWin :=
  WinChord SidecarCircMixed.locked_mixed_ls.

Definition locked_mu_win_cs : CircChordWin :=
  WinCirc SidecarCircMixed.locked_mixed_cs locked_mixed_cs_valid.

Lemma cell3_reuses_I_ok_mixed :
  I_ok_mixed (MixLsCs SidecarCircMixed.locked_mixed_ls
                      SidecarCircMixed.locked_mixed_cs)
    (SidecarCircMixed.ls_cs_joint_hit
       SidecarCircMixed.locked_mixed_ls
       SidecarCircMixed.locked_mixed_cs).
Proof.
  exact SidecarCircMixed.locked_mixed_ls_cs_I_ok_mixed.
Qed.

Lemma cell3_mu_is_joint_not_iota :
  IotaGate locked_mu_win_ls locked_mu_win_cs
    (SidecarCircMixed.ls_cs_joint_hit
       SidecarCircMixed.locked_mixed_ls
       SidecarCircMixed.locked_mixed_cs) CellMuJoint
  /\ ~ IotaGate locked_mu_win_ls locked_mu_win_cs
         (SidecarCircMixed.ls_cs_joint_hit
            SidecarCircMixed.locked_mixed_ls
            SidecarCircMixed.locked_mixed_cs) CellIotaCand
  /\ ~ interior_span_params 1 0.
Proof.
  split.
  - eapply GateMuJoint.
    + left. split; exact I.
    + reflexivity.
    + exact SidecarCircMixed.mixed_joint_params_end_start.
  - split.
    + intros H.
      apply IotaGate_iff_pred in H.
      destruct H as [_ [p [ti [tj [Heq Hi]]]]].
      unfold SidecarCircMixed.ls_cs_joint_hit in Heq.
      inversion Heq; subst.
      exact (CircularCookCsConcat.joint_params_not_interior Hi).
    + exact CircularCookCsConcat.joint_params_not_interior.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cell 4: ι candidate. InteriorMixedHitArm stays missing (QEX).              *)
(* -------------------------------------------------------------------------- *)

Lemma locked_interior_cs_valid :
  valid_arc SidecarCircInteriorHit.locked_interior_cs.
Proof.
  exact span_arc_A_valid.
Qed.

Definition locked_iota_win_ls : CircChordWin :=
  WinChord SidecarCircInteriorHit.locked_interior_ls.

Definition locked_iota_win_cs : CircChordWin :=
  WinCirc SidecarCircInteriorHit.locked_interior_cs locked_interior_cs_valid.

Lemma cell4_is_iota_candidate :
  IotaGate locked_iota_win_ls locked_iota_win_cs
    SidecarCircInteriorHit.locked_interior_hit CellIotaCand
  /\ interior_span_params
       SidecarCircInteriorHit.locked_interior_ti
       SidecarCircInteriorHit.locked_interior_tj
  /\ I_ok_interior
       (MixLsCs SidecarCircInteriorHit.locked_interior_ls
                SidecarCircInteriorHit.locked_interior_cs)
       SidecarCircInteriorHit.locked_interior_hit
  /\ ~ I_ok_mixed
        (MixLsCs SidecarCircInteriorHit.locked_interior_ls
                 SidecarCircInteriorHit.locked_interior_cs)
        SidecarCircInteriorHit.locked_interior_hit.
Proof.
  split.
  - eapply GateIotaCand.
    + left. split; exact I.
    + reflexivity.
    + exact SidecarCircInteriorHit.locked_interior_params.
  - split; [exact SidecarCircInteriorHit.locked_interior_params|].
    exact SidecarCircInteriorHit.locked_interior_not_I_ok_mixed.
Qed.

Lemma cell4_arm_uninhabited :
  ~ SidecarCircInterior.interior_mixed_constructor_inhabits
      SidecarCircInterior.InteriorMixedHitArm.
Proof.
  exact SidecarCircInterior.interior_mixed_hit_arm_missing.
Qed.

Lemma cell4_not_discharged_by_I_ok_interior :
  I_ok_interior
    (MixLsCs SidecarCircInteriorHit.locked_interior_ls
             SidecarCircInteriorHit.locked_interior_cs)
    SidecarCircInteriorHit.locked_interior_hit
  /\ ~ SidecarCircInterior.interior_mixed_constructor_inhabits
        SidecarCircInterior.InteriorMixedHitArm
  /\ ~ I_ok_mixed
        (MixLsCs SidecarCircInteriorHit.locked_interior_ls
                 SidecarCircInteriorHit.locked_interior_cs)
        SidecarCircInteriorHit.locked_interior_hit.
Proof.
  exact SidecarCircInteriorHit.iota_park_not_discharged_by_I_ok_interior.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cell 5 miss / cell 6 residual Decline.                                     *)
(* -------------------------------------------------------------------------- *)

Lemma cell5_mixed_empty :
  forall c a va,
    IotaGate (WinChord c) (WinCirc a va) IEmpty CellMiss.
Proof.
  intros c a va.
  constructor.
  - left. split; exact I.
  - reflexivity.
Qed.

Lemma cell6_mixed_decline :
  forall c a va,
    IotaGate (WinChord c) (WinCirc a va) IDecline CellDecline.
Proof.
  intros c a va.
  apply GateDeclineTag.
  - left. split; exact I.
  - reflexivity.
Qed.

Lemma cell6_mixed_half_open_hit :
  IotaGate locked_iota_win_ls locked_iota_win_cs
    (IHit locked_p_plus 1 (1 / 2)) CellDecline.
Proof.
  eapply GateDeclineHit.
  - left. split; exact I.
  - reflexivity.
  - unfold mixed_joint_params, SidecarCircInterior.mixed_joint_params,
           SidecarCircMixed.mixed_joint_params.
    intros [[_ H0] | [H0 _]]; lra.
  - unfold interior_span_params, SidecarCircInterior.interior_span_params,
           SidecarCircMixed.interior_span_params,
           CircularCookCsConcat.interior_span_params.
    intros [[_ H1] _]. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Tickets. Gate completeness QED. ι cook QEX restated.                       *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-iota-gate","topic":"overlay","lemma":"ticket_0007_iota_gate_qed_or_qex","title":"iota gate: six circ/chord cells exclusive and complete (QED) or a pair misses every cell or two cells overlap (QEX); discharged QED; collinear CircularString-as-chord is cell 1 never cell 4; mixed_joint_params stands","file":"theories/SidecarCircIotaGate.v","witness":"0007-iota-gate","board":"ADR-0007"} *)

Theorem ticket_0007_iota_gate_qed_or_qex :
  ((forall w1 w2 o c1 c2,
      IotaGate w1 w2 o c1 -> IotaGate w1 w2 o c2 -> c1 = c2)
   /\ (forall w1 w2 o, exists c, IotaGate w1 w2 o c)
   /\ (forall a ncol c o,
         IotaGate (WinColCirc a ncol) (WinChord c) o CellChordChord
         /\ ~ IotaGate (WinColCirc a ncol) (WinChord c) o CellIotaCand)
   /\ (forall a na b nb o,
         IotaGate (WinColCirc a na) (WinColCirc b nb) o CellChordChord
         /\ ~ IotaGate (WinColCirc a na) (WinColCirc b nb) o CellIotaCand)
   /\ I_ok (MkChord locked_col_as_chord) (MkChord locked_col_cross_chord)
        (IHit locked_col_cross_pt (1 / 2) (1 / 2)))
  \/
  (exists w1 w2 o, forall c, ~ IotaGate w1 w2 o c).
Proof.
  left.
  split; [exact iota_gate_exclusive|].
  split; [exact iota_gate_complete|].
  split.
  - intros a ncol c o.
    split; [apply col_cs_times_chord_is_cell1 | apply col_cs_times_chord_not_cell4].
  - split.
    + intros a na b nb o.
      split; [apply col_cs_times_col_cs_is_cell1 | apply col_cs_times_col_cs_not_cell4].
    + exact cell1_col_cs_reuses_host_I_ok.
Qed.

(* WITNESS {"claimId":"0007-iota-gate","topic":"overlay","lemma":"ticket_0007_iota_cook_qed_or_qex","title":"iota cook: InteriorMixedHitArm inhabits I_ok_mixed Hit at interior_span_params and both windows split (QED) or the ctor stays missing, mixed_joint_params stands, first cook stays chord-chord plus circular-circular, LoopDischarged stays false (QEX); discharged QEX; cell 1/2/3 reuse existing QED cooks; I_ok_interior is not this ctor","file":"theories/SidecarCircIotaGate.v","witness":"0007-iota-gate","board":"ADR-0007"} *)

Theorem ticket_0007_iota_cook_qed_or_qex :
  (SidecarCircInterior.interior_mixed_constructor_inhabits
     SidecarCircInterior.InteriorMixedHitArm
   /\ first_cook_scope EggChord EggCircularArc
   /\ cook_loop_status = LoopDischarged)
  \/
  (~ SidecarCircInterior.interior_mixed_constructor_inhabits
      SidecarCircInterior.InteriorMixedHitArm
   /\ (forall m p ti tj, ~ SidecarCircInterior.I_ok_mixed_interior_hit m p ti tj)
   /\ IotaGate locked_iota_win_ls locked_iota_win_cs
        SidecarCircInteriorHit.locked_interior_hit CellIotaCand
   /\ I_ok_interior
        (MixLsCs SidecarCircInteriorHit.locked_interior_ls
                 SidecarCircInteriorHit.locked_interior_cs)
        SidecarCircInteriorHit.locked_interior_hit
   /\ ~ I_ok_mixed
         (MixLsCs SidecarCircInteriorHit.locked_interior_ls
                  SidecarCircInteriorHit.locked_interior_cs)
         SidecarCircInteriorHit.locked_interior_hit
   /\ I_ok_mixed (MixLsCs SidecarCircMixed.locked_mixed_ls
                          SidecarCircMixed.locked_mixed_cs)
        (SidecarCircMixed.ls_cs_joint_hit
           SidecarCircMixed.locked_mixed_ls
           SidecarCircMixed.locked_mixed_cs)
   /\ I_ok (MkChord diag_ab) (MkChord diag_cd)
        (IHit cross_pt (1 / 2) (1 / 2))
   /\ I_ok (MkCirc locked_circ_A) (MkCirc locked_circ_B)
        (IHit locked_circ_hit_pt locked_circ_ti locked_circ_tj)
   /\ circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggChord EggChord
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ cook_loop_status = LoopObligation
   /\ cook_loop_status <> LoopDischarged
   /\ SidecarCircInterior.iota_interior_cook_status
      = SidecarCircInterior.IotaInteriorCookParked).
Proof.
  right.
  split; [exact cell4_arm_uninhabited|].
  split; [exact SidecarCircInterior.I_ok_mixed_interior_hit_uninhabited|].
  destruct cell4_is_iota_candidate as [Hg [Hp [Hint Hnm]]].
  split; [exact Hg|].
  split; [exact Hint|].
  split; [exact Hnm|].
  split; [exact cell3_reuses_I_ok_mixed|].
  split; [exact cell1_reuses_host_crossing_I_ok|].
  split; [exact cell2_reuses_mkcirc_unique_hit|].
  split; [exact iota_gate_host_circgamma_discharged|].
  split; [exact iota_gate_first_cook_stays_chord_chord|].
  split; [exact iota_gate_circular_is_first_cook|].
  destruct iota_gate_not_bag_noder as [Hob Hnd].
  split; [exact Hob|].
  split; [exact Hnd|].
  exact SidecarCircInterior.iota_interior_cook_is_parked.
Qed.

Print Assumptions iota_gate_host_circgamma_discharged.
Print Assumptions iota_gate_not_bag_noder.
Print Assumptions sort_trichotomy.
Print Assumptions iota_gate_exclusive.
Print Assumptions iota_gate_complete.
Print Assumptions iota_gate_cells_exclusive_and_complete.
Print Assumptions col_cs_times_chord_is_cell1.
Print Assumptions col_cs_times_chord_not_cell4.
Print Assumptions locked_col_cs_as_chord_cell1.
Print Assumptions cell1_reuses_host_crossing_I_ok.
Print Assumptions cell1_col_cs_reuses_host_I_ok.
Print Assumptions cell2_reuses_mkcirc_unique_hit.
Print Assumptions cell2_reuses_I_ok_circ_hit.
Print Assumptions cell2_reuses_I_ok_circ_empty.
Print Assumptions cell2_two_hit_existing_cook.
Print Assumptions cell2_span_pair_is_circ_circ.
Print Assumptions cell3_reuses_I_ok_mixed.
Print Assumptions cell3_mu_is_joint_not_iota.
Print Assumptions cell4_is_iota_candidate.
Print Assumptions cell4_arm_uninhabited.
Print Assumptions cell4_not_discharged_by_I_ok_interior.
Print Assumptions cell5_mixed_empty.
Print Assumptions cell6_mixed_decline.
Print Assumptions cell6_mixed_half_open_hit.
Print Assumptions ticket_0007_iota_gate_qed_or_qex.
Print Assumptions ticket_0007_iota_cook_qed_or_qex.
