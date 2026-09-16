(* ============================================================================
   NetTopologySuite.Proofs.SidecarCircIotaGate
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: ι gate on circ/chord windows
   (claimId 0007-iota-gate).

   A pair that arrived as circular and/or chord is classified by
   exactly one of six cells:

     1. Both demote to collinear chords → chord × chord first cook
        (host I_ok). Not ι, not μ.
     2. circ × circ (neither demotes) → existing circular cook
        (I_ok_circ unique-Hit / Empty; two-root cook stays
        CircularCook*). Not ι.
     3. circ × chord after demote, mixed_joint_params, endpoint → μ
        (I_ok_mixed joint). Not ι.
     4. circ × chord after demote, mixed_joint_params context,
        both parameters interior → ι candidate (interior_span_params /
        I_ok_mixed_interior_arm).
     5. miss → Empty.
     6. anything else on this pair sort → Decline, not ι.

   Collinear CircularString-as-chord takes cell 1, never cell 4.

   Cook reuse (do not remint):
     cell 1 — host I_ok first cook (QED)
     cell 2 — CircularCook / I_ok_circ (QED)
     cell 3 — I_ok_mixed endpoint (QED)
     cell 4 — InteriorMixedHitArm = I_ok_mixed Hit ∧
              interior_span_params. Host / I_ok_mixed cannot inhabit
              the arm (mixed_joint_params stands). QEX restated.
              I_ok_interior is a sibling, not this ctor.

   Honesty fences:
     Do not remint CircGamma / MkCirc / host I_ok / I_ok_mixed
     (do not drop mixed_joint_params). Do not flip LeftoverBagTermArm
     / LoopDischarged. Do not expand first_cook_scope to
     circular×chord. Do not rename Γ to GeometryNoder.
     Not NURBS / clothoid / ellipse. Not GEOS / C API / Overlay.
     Sidecar I_ok_circ / I_ok_mixed / I_ok_interior ≠ host I_ok.
     Parks ι ticket names stay QEX without the ctor.

   WITNESS topic: overlay · claimId: 0007-iota-gate
   witness: 0007-iota-gate
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via SidecarCircInteriorHit
     / CircularCookOkCirc). Category C audit-exception: same atan2
     lineage as Parks ι; classic only for pair-sort / miss LEM.
   Host lane stays 3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Classical_Prop.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  CircularCook CircularCookHit CircularCookSpan CircularCookOkCirc.
From NTS.Proofs Require SidecarCircMixed.
From NTS.Proofs Require SidecarCircInterior.
From NTS.Proofs Require SidecarCircInteriorHit.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=iota-gate claim=0007-iota-gate
   file=theories/SidecarCircIotaGate.v
   kind=QED-or-QEX-iota-gate-circ-chord
   reuse=I_ok,I_ok_circ,I_ok_mixed,interior_span_params,mixed_joint_params
   not=new-kernel,CircGamma-remint,first-cook-noding,I_ok_mixed-remint
   not=LeftoverBagTermArm,LoopDischarged,GeometryNoder
   park=InteriorMixedHitArm,Hperp,SQL-MM-cathedral
   land=iota-gate-complete-exclusive *)

Definition I_ok_mixed := SidecarCircInterior.I_ok_mixed.
Definition mixed_joint_params := SidecarCircInterior.mixed_joint_params.
Definition interior_span_params := SidecarCircInterior.interior_span_params.
Definition MixedEggs := SidecarCircInterior.MixedEggs.
Definition MixLsCs := SidecarCircInterior.MixLsCs.
Definition MixCsLs := SidecarCircInterior.MixCsLs.
Definition I_ok_mixed_interior_arm :=
  SidecarCircInterior.I_ok_mixed_interior_arm.
Definition CircEgg := CircularCookOkCirc.CircEgg.

(* -------------------------------------------------------------------------- *)
(* Arrival windows. Demote is collinear CircularString-as-chord.              *)
(* -------------------------------------------------------------------------- *)

Inductive CircChordWin : Type :=
| WinChord (c : ChordEgg)
| WinCirc (a : CircEgg).

Definition demote_chord (a : CircEgg) : ChordEgg :=
  mkChordEgg (arc_start a) (arc_end a).

Definition as_chord (w : CircChordWin) (c : ChordEgg) : Prop :=
  match w with
  | WinChord c' => c = c'
  | WinCirc a => ~ valid_arc a /\ c = demote_chord a
  end.

Definition remains_circ (w : CircChordWin) (a : CircEgg) : Prop :=
  match w with
  | WinCirc a' => valid_arc a' /\ a = a'
  | WinChord _ => False
  end.

Definition both_chords (w1 w2 : CircChordWin) : Prop :=
  exists c1 c2, as_chord w1 c1 /\ as_chord w2 c2.

Definition both_circs (w1 w2 : CircChordWin) : Prop :=
  exists a b, remains_circ w1 a /\ remains_circ w2 b.

Definition as_mixed (w1 w2 : CircChordWin) (m : MixedEggs) : Prop :=
  match w1, w2, m with
  | WinChord c, WinCirc a, SidecarCircMixed.MixLsCs c' a' =>
      as_chord (WinChord c) c' /\ remains_circ (WinCirc a) a'
  | WinCirc a, WinChord c, SidecarCircMixed.MixCsLs a' c' =>
      remains_circ (WinCirc a) a' /\ as_chord (WinChord c) c'
  | WinCirc a, WinCirc b, SidecarCircMixed.MixLsCs c' a' =>
      as_chord (WinCirc a) c' /\ remains_circ (WinCirc b) a'
  | WinCirc a, WinCirc b, SidecarCircMixed.MixCsLs a' c' =>
      remains_circ (WinCirc a) a' /\ as_chord (WinCirc b) c'
  | _, _, _ => False
  end.

Definition mixed_pair (w1 w2 : CircChordWin) : Prop :=
  exists m, as_mixed w1 w2 m.

Lemma as_chord_not_remains :
  forall w c a, as_chord w c -> ~ remains_circ w a.
Proof.
  intros w c a Hc Hr.
  destruct w as [c' | ar].
  - exact Hr.
  - destruct Hc as [Hn _]. destruct Hr as [Hv _]. exact (Hn Hv).
Qed.

Lemma both_chords_not_both_circs :
  forall w1 w2, both_chords w1 w2 -> ~ both_circs w1 w2.
Proof.
  intros w1 w2 [c1 [c2 [H1 _]]] [a [_ [Ha _]]].
  exact (as_chord_not_remains w1 c1 a H1 Ha).
Qed.

Lemma both_circs_not_both_chords :
  forall w1 w2, both_circs w1 w2 -> ~ both_chords w1 w2.
Proof.
  intros w1 w2 Hci Hch.
  exact (both_chords_not_both_circs w1 w2 Hch Hci).
Qed.

Lemma both_chords_not_mixed :
  forall w1 w2, both_chords w1 w2 -> ~ mixed_pair w1 w2.
Proof.
  intros w1 w2 [c1 [c2 [H1 H2]]] [m Hm].
  destruct w1 as [cA | aA]; destruct w2 as [cB | aB];
    destruct m as [cm am | am cm]; try exact Hm.
  - destruct Hm as [_ Hr].
    destruct H2 as [Hn _]. destruct Hr as [Hv _]. exact (Hn Hv).
  - destruct Hm as [Hr _].
    destruct H1 as [Hn _]. destruct Hr as [Hv _]. exact (Hn Hv).
  - destruct Hm as [_ Hr].
    destruct H2 as [Hn _]. destruct Hr as [Hv _]. exact (Hn Hv).
  - destruct Hm as [Hr _].
    destruct H1 as [Hn _]. destruct Hr as [Hv _]. exact (Hn Hv).
Qed.

Lemma both_circs_not_mixed :
  forall w1 w2, both_circs w1 w2 -> ~ mixed_pair w1 w2.
Proof.
  intros w1 w2 [a [b [Ha Hb]]] [m Hm].
  destruct w1 as [cA | aA]; destruct w2 as [cB | aB];
    destruct m as [cm am | am cm]; try exact Hm.
  - destruct Hm as [Hc _].
    exact (as_chord_not_remains (WinCirc aA) cm a Ha Hc).
  - destruct Hm as [_ Hc].
    exact (as_chord_not_remains (WinCirc aB) cm b Hb Hc).
Qed.

Lemma mixed_not_both_chords :
  forall w1 w2, mixed_pair w1 w2 -> ~ both_chords w1 w2.
Proof.
  intros w1 w2 Hm Hch. exact (both_chords_not_mixed w1 w2 Hch Hm).
Qed.

Lemma mixed_not_both_circs :
  forall w1 w2, mixed_pair w1 w2 -> ~ both_circs w1 w2.
Proof.
  intros w1 w2 Hm Hci. exact (both_circs_not_mixed w1 w2 Hci Hm).
Qed.

Lemma valid_arc_em : forall a, valid_arc a \/ ~ valid_arc a.
Proof.
  intros a. apply classic.
Qed.

Lemma pair_sort_complete :
  forall w1 w2,
    both_chords w1 w2 \/ both_circs w1 w2 \/ mixed_pair w1 w2.
Proof.
  intros w1 w2.
  destruct w1 as [c1 | a1]; destruct w2 as [c2 | a2].
  - left. exists c1, c2. split; reflexivity.
  - destruct (valid_arc_em a2) as [Hv | Hn].
    + right. right. exists (MixLsCs c1 a2).
      unfold as_mixed, as_chord, remains_circ.
      split; [reflexivity|]. split; [exact Hv|reflexivity].
    + left. exists c1, (demote_chord a2).
      split; [reflexivity|]. split; [exact Hn|reflexivity].
  - destruct (valid_arc_em a1) as [Hv | Hn].
    + right. right. exists (MixCsLs a1 c2).
      unfold as_mixed, as_chord, remains_circ.
      split; [split; [exact Hv|reflexivity]|reflexivity].
    + left. exists (demote_chord a1), c2.
      split; [split; [exact Hn|reflexivity]|reflexivity].
  - destruct (valid_arc_em a1) as [Hv1 | Hn1];
      destruct (valid_arc_em a2) as [Hv2 | Hn2].
    + right. left. exists a1, a2.
      split; [split; [exact Hv1|reflexivity]|].
      split; [exact Hv2|reflexivity].
    + right. right. exists (MixCsLs a1 (demote_chord a2)).
      unfold as_mixed, as_chord, remains_circ.
      split; [split; [exact Hv1|reflexivity]|].
      split; [exact Hn2|reflexivity].
    + right. right. exists (MixLsCs (demote_chord a1) a2).
      unfold as_mixed, as_chord, remains_circ.
      split; [split; [exact Hn1|reflexivity]|].
      split; [exact Hv2|reflexivity].
    + left. exists (demote_chord a1), (demote_chord a2).
      split; [split; [exact Hn1|reflexivity]|].
      split; [exact Hn2|reflexivity].
Qed.

(* -------------------------------------------------------------------------- *)
(* Mixed geometry. μ / ι-candidate / other / miss.                            *)
(* -------------------------------------------------------------------------- *)

Definition mixed_geo_on (m : MixedEggs) (p : Point) (ti tj : R) : Prop :=
  match m with
  | SidecarCircMixed.MixLsCs c a =>
      valid_arc a /\ on_chord c ti p /\ on_arc_gamma a tj p
  | SidecarCircMixed.MixCsLs a c =>
      valid_arc a /\ on_arc_gamma a ti p /\ on_chord c tj p
  end.

Definition has_mu (w1 w2 : CircChordWin) : Prop :=
  exists m p ti tj,
    as_mixed w1 w2 m /\ I_ok_mixed m (IHit p ti tj).

Definition has_iota_cand (w1 w2 : CircChordWin) : Prop :=
  exists m p ti tj,
    as_mixed w1 w2 m /\ I_ok_mixed_interior_arm m p ti tj.

Definition has_other (w1 w2 : CircChordWin) : Prop :=
  exists m p ti tj,
    as_mixed w1 w2 m /\
    mixed_geo_on m p ti tj /\
    ~ mixed_joint_params ti tj /\
    ~ interior_span_params ti tj.

(* -------------------------------------------------------------------------- *)
(* Six cells. Priority makes them exclusive.                                  *)
(* -------------------------------------------------------------------------- *)

Inductive IotaGateCell : Type :=
| IotaCellChordChord
| IotaCellCircCirc
| IotaCellMu
| IotaCellIota
| IotaCellEmpty
| IotaCellDecline.

Definition iota_cell (w1 w2 : CircChordWin) (c : IotaGateCell) : Prop :=
  match c with
  | IotaCellChordChord => both_chords w1 w2
  | IotaCellCircCirc => ~ both_chords w1 w2 /\ both_circs w1 w2
  | IotaCellMu =>
      ~ both_chords w1 w2 /\ ~ both_circs w1 w2 /\
      mixed_pair w1 w2 /\ has_mu w1 w2
  | IotaCellIota =>
      ~ both_chords w1 w2 /\ ~ both_circs w1 w2 /\
      mixed_pair w1 w2 /\ ~ has_mu w1 w2 /\ has_iota_cand w1 w2
  | IotaCellEmpty =>
      ~ both_chords w1 w2 /\ ~ both_circs w1 w2 /\
      mixed_pair w1 w2 /\ ~ has_mu w1 w2 /\
      ~ has_iota_cand w1 w2 /\ ~ has_other w1 w2
  | IotaCellDecline =>
      ~ both_chords w1 w2 /\ ~ both_circs w1 w2 /\
      mixed_pair w1 w2 /\ ~ has_mu w1 w2 /\
      ~ has_iota_cand w1 w2 /\ has_other w1 w2
  end.

Lemma iota_cell_exclusive :
  forall w1 w2 c1 c2,
    iota_cell w1 w2 c1 ->
    iota_cell w1 w2 c2 ->
    c1 = c2.
Proof.
  intros w1 w2 c1 c2 H1 H2.
  destruct c1, c2; try reflexivity; unfold iota_cell in H1, H2.
  - destruct H2 as [Hn _]. exfalso. exact (Hn H1).
  - destruct H2 as [Hn _]. exfalso. exact (Hn H1).
  - destruct H2 as [Hn _]. exfalso. exact (Hn H1).
  - destruct H2 as [Hn _]. exfalso. exact (Hn H1).
  - destruct H2 as [Hn _]. exfalso. exact (Hn H1).
  - destruct H1 as [Hn _]. exfalso. exact (Hn H2).
  - destruct H1 as [_ Hci]. destruct H2 as [_ [Hn _]].
    exfalso. exact (Hn Hci).
  - destruct H1 as [_ Hci]. destruct H2 as [_ [Hn _]].
    exfalso. exact (Hn Hci).
  - destruct H1 as [_ Hci]. destruct H2 as [_ [Hn _]].
    exfalso. exact (Hn Hci).
  - destruct H1 as [_ Hci]. destruct H2 as [_ [Hn _]].
    exfalso. exact (Hn Hci).
  - destruct H1 as [Hn _]. exfalso. exact (Hn H2).
  - destruct H1 as [_ [Hn _]]. destruct H2 as [_ Hci].
    exfalso. exact (Hn Hci).
  - destruct H1 as [_ [_ [_ Hmu]]].
    destruct H2 as [_ [_ [_ [Hn _]]]].
    exfalso. exact (Hn Hmu).
  - destruct H1 as [_ [_ [_ Hmu]]].
    destruct H2 as [_ [_ [_ [Hn _]]]].
    exfalso. exact (Hn Hmu).
  - destruct H1 as [_ [_ [_ Hmu]]].
    destruct H2 as [_ [_ [_ [Hn _]]]].
    exfalso. exact (Hn Hmu).
  - destruct H1 as [Hn _]. exfalso. exact (Hn H2).
  - destruct H1 as [_ [Hn _]]. destruct H2 as [_ Hci].
    exfalso. exact (Hn Hci).
  - destruct H1 as [_ [_ [_ [Hn _]]]].
    destruct H2 as [_ [_ [_ Hmu]]].
    exfalso. exact (Hn Hmu).
  - destruct H1 as [_ [_ [_ [_ Hi]]]].
    destruct H2 as [_ [_ [_ [_ [Hn _]]]]].
    exfalso. exact (Hn Hi).
  - destruct H1 as [_ [_ [_ [_ Hi]]]].
    destruct H2 as [_ [_ [_ [_ [Hn _]]]]].
    exfalso. exact (Hn Hi).
  - destruct H1 as [Hn _]. exfalso. exact (Hn H2).
  - destruct H1 as [_ [Hn _]]. destruct H2 as [_ Hci].
    exfalso. exact (Hn Hci).
  - destruct H1 as [_ [_ [_ [Hn _]]]].
    destruct H2 as [_ [_ [_ Hmu]]].
    exfalso. exact (Hn Hmu).
  - destruct H1 as [_ [_ [_ [_ [Hn _]]]]].
    destruct H2 as [_ [_ [_ [_ Hi]]]].
    exfalso. exact (Hn Hi).
  - destruct H1 as [_ [_ [_ [_ [_ Hn]]]]].
    destruct H2 as [_ [_ [_ [_ [_ Ho]]]]].
    exfalso. exact (Hn Ho).
  - destruct H1 as [Hn _]. exfalso. exact (Hn H2).
  - destruct H1 as [_ [Hn _]]. destruct H2 as [_ Hci].
    exfalso. exact (Hn Hci).
  - destruct H1 as [_ [_ [_ [Hn _]]]].
    destruct H2 as [_ [_ [_ Hmu]]].
    exfalso. exact (Hn Hmu).
  - destruct H1 as [_ [_ [_ [_ [Hn _]]]]].
    destruct H2 as [_ [_ [_ [_ Hi]]]].
    exfalso. exact (Hn Hi).
  - destruct H1 as [_ [_ [_ [_ [_ Ho]]]]].
    destruct H2 as [_ [_ [_ [_ [_ Hn]]]]].
    exfalso. exact (Hn Ho).
Qed.

Lemma iota_cell_complete :
  forall w1 w2, exists c, iota_cell w1 w2 c.
Proof.
  intros w1 w2.
  destruct (pair_sort_complete w1 w2) as [Hch | [Hci | Hm]].
  - exists IotaCellChordChord. exact Hch.
  - exists IotaCellCircCirc.
    split; [exact (both_circs_not_both_chords w1 w2 Hci)|exact Hci].
  - destruct (classic (has_mu w1 w2)) as [Hmu | Hnmu].
    + exists IotaCellMu.
      split; [exact (mixed_not_both_chords w1 w2 Hm)|].
      split; [exact (mixed_not_both_circs w1 w2 Hm)|].
      split; [exact Hm|exact Hmu].
    + destruct (classic (has_iota_cand w1 w2)) as [Hi | Hni].
      * exists IotaCellIota.
        split; [exact (mixed_not_both_chords w1 w2 Hm)|].
        split; [exact (mixed_not_both_circs w1 w2 Hm)|].
        split; [exact Hm|]. split; [exact Hnmu|exact Hi].
      * destruct (classic (has_other w1 w2)) as [Ho | Hno].
        -- exists IotaCellDecline.
           split; [exact (mixed_not_both_chords w1 w2 Hm)|].
           split; [exact (mixed_not_both_circs w1 w2 Hm)|].
           split; [exact Hm|]. split; [exact Hnmu|].
           split; [exact Hni|exact Ho].
        -- exists IotaCellEmpty.
           split; [exact (mixed_not_both_chords w1 w2 Hm)|].
           split; [exact (mixed_not_both_circs w1 w2 Hm)|].
           split; [exact Hm|]. split; [exact Hnmu|].
           split; [exact Hni|exact Hno].
Qed.

(* -------------------------------------------------------------------------- *)
(* Collinear CircularString-as-chord: cell 1, never cell 4.                   *)
(* -------------------------------------------------------------------------- *)

Definition collinear_cs : CircEgg :=
  mkCircularArc (mkPoint 0 0) (mkPoint 1 0) (mkPoint 2 0).

Lemma collinear_cs_invalid : ~ valid_arc collinear_cs.
Proof.
  unfold valid_arc, collinear_cs.
  cbn [px py arc_start arc_mid arc_end].
  intros H. apply H. ring.
Qed.

Lemma collinear_cs_as_chord_cell1 :
  forall c,
    iota_cell (WinCirc collinear_cs) (WinChord c) IotaCellChordChord.
Proof.
  intros c.
  exists (demote_chord collinear_cs), c.
  split; [split; [exact collinear_cs_invalid|reflexivity]|reflexivity].
Qed.

Lemma collinear_cs_chord_cell1 :
  forall c,
    iota_cell (WinChord c) (WinCirc collinear_cs) IotaCellChordChord.
Proof.
  intros c.
  exists c, (demote_chord collinear_cs).
  split; [reflexivity|].
  split; [exact collinear_cs_invalid|reflexivity].
Qed.

Lemma collinear_cs_as_chord_not_iota :
  forall c,
    ~ iota_cell (WinCirc collinear_cs) (WinChord c) IotaCellIota.
Proof.
  intros c H.
  destruct H as [Hn _].
  exact (Hn (collinear_cs_as_chord_cell1 c)).
Qed.

Lemma collinear_cs_chord_not_iota :
  forall c,
    ~ iota_cell (WinChord c) (WinCirc collinear_cs) IotaCellIota.
Proof.
  intros c H.
  destruct H as [Hn _].
  exact (Hn (collinear_cs_chord_cell1 c)).
Qed.

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma fence. Do not remint.                             *)
(* -------------------------------------------------------------------------- *)

Lemma iota_gate_circgamma_discharged :
  circular_gamma_status = CircGammaDischarged.
Proof.
  exact circular_gamma_is_discharged.
Qed.

Lemma iota_gate_first_cook_stays :
  first_cook_scope EggChord EggChord
  /\ first_cook_scope EggCircularArc EggCircularArc
  /\ ~ first_cook_scope EggChord EggCircularArc.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact circular_is_first_cook_scope|].
  exact chord_circular_not_first_cook_scope.
Qed.

Lemma iota_gate_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

(* -------------------------------------------------------------------------- *)
(* Part B — cook reuse on cells 1–3; ι arm stays missing.                     *)
(* -------------------------------------------------------------------------- *)

Lemma cell1_reuses_I_ok :
  iota_cell (WinChord diag_ab) (WinChord diag_cd) IotaCellChordChord
  /\ I_ok (MkChord diag_ab) (MkChord diag_cd)
       (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  split.
  - exists diag_ab, diag_cd. split; reflexivity.
  - exact crossing_I_ok.
Qed.

Lemma cell1_not_mu_not_iota :
  iota_cell (WinChord diag_ab) (WinChord diag_cd) IotaCellChordChord
  /\ ~ iota_cell (WinChord diag_ab) (WinChord diag_cd) IotaCellMu
  /\ ~ iota_cell (WinChord diag_ab) (WinChord diag_cd) IotaCellIota.
Proof.
  split; [apply cell1_reuses_I_ok|].
  split.
  - intros H. destruct H as [Hn _].
    destruct cell1_reuses_I_ok as [H1 _]. exact (Hn H1).
  - intros H. destruct H as [Hn _].
    destruct cell1_reuses_I_ok as [H1 _]. exact (Hn H1).
Qed.

Lemma cell2_reuses_I_ok_circ_hit :
  iota_cell (WinCirc span_arc_A) (WinCirc span_arc_B) IotaCellCircCirc
  /\ I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit.
Proof.
  split.
  - split.
    + apply both_circs_not_both_chords.
      exists span_arc_A, span_arc_B.
      split; [split; [exact span_arc_A_valid|reflexivity]|].
      split; [exact span_arc_B_valid|reflexivity].
    + exists span_arc_A, span_arc_B.
      split; [split; [exact span_arc_A_valid|reflexivity]|].
      split; [exact span_arc_B_valid|reflexivity].
  - exact CircularCookOkCirc.ii3_locked_plus_I_ok_circ.
Qed.

Lemma cell2_reuses_I_ok_circ_empty :
  iota_cell (WinCirc span_arc_A) (WinCirc span_empty_far) IotaCellCircCirc
  /\ I_ok_circ span_arc_A span_empty_far IEmpty.
Proof.
  split.
  - split.
    + apply both_circs_not_both_chords.
      exists span_arc_A, span_empty_far.
      split; [split; [exact span_arc_A_valid|reflexivity]|].
      split; [exact span_empty_far_valid|reflexivity].
    + exists span_arc_A, span_empty_far.
      split; [split; [exact span_arc_A_valid|reflexivity]|].
      split; [exact span_empty_far_valid|reflexivity].
  - exact CircularCookOkCirc.ii3_locked_empty.
Qed.

Lemma cell2_not_iota :
  ~ iota_cell (WinCirc span_arc_A) (WinCirc span_arc_B) IotaCellIota.
Proof.
  intros H. destruct H as [_ [Hn _]].
  destruct cell2_reuses_I_ok_circ_hit as [[_ Hci] _].
  exact (Hn Hci).
Qed.

Definition locked_mu_ls := SidecarCircInterior.locked_mixed_ls.
Definition locked_mu_cs := SidecarCircInterior.locked_mixed_cs.

Lemma locked_mu_as_mixed :
  as_mixed (WinChord locked_mu_ls) (WinCirc locked_mu_cs)
    (MixLsCs locked_mu_ls locked_mu_cs).
Proof.
  unfold as_mixed, as_chord, remains_circ, locked_mu_cs.
  split; [reflexivity|].
  split; [|reflexivity].
  apply (proj1 SidecarCircMixed.locked_mixed_ls_cs_joint).
Qed.

Lemma cell3_reuses_I_ok_mixed :
  iota_cell (WinChord locked_mu_ls) (WinCirc locked_mu_cs) IotaCellMu
  /\ I_ok_mixed (MixLsCs locked_mu_ls locked_mu_cs)
       (SidecarCircMixed.ls_cs_joint_hit locked_mu_ls locked_mu_cs)
  /\ ~ interior_span_params 1 0.
Proof.
  assert (Hhit : I_ok_mixed (MixLsCs locked_mu_ls locked_mu_cs)
    (SidecarCircMixed.ls_cs_joint_hit locked_mu_ls locked_mu_cs)).
  { exact SidecarCircInterior.iota_mu_joint_I_ok_mixed. }
  assert (Hm : mixed_pair (WinChord locked_mu_ls) (WinCirc locked_mu_cs)).
  { exists (MixLsCs locked_mu_ls locked_mu_cs). exact locked_mu_as_mixed. }
  split.
  - split; [exact (mixed_not_both_chords _ _ Hm)|].
    split; [exact (mixed_not_both_circs _ _ Hm)|].
    split; [exact Hm|].
    exists (MixLsCs locked_mu_ls locked_mu_cs),
      (ce_p1 locked_mu_ls), 1, 0.
    split; [exact locked_mu_as_mixed|exact Hhit].
  - split; [exact Hhit|].
    apply (proj2 SidecarCircInterior.iota_mu_joint_not_interior).
Qed.

Definition locked_iota_ls := SidecarCircInteriorHit.locked_interior_ls.
Definition locked_iota_cs := SidecarCircInteriorHit.locked_interior_cs.

Lemma locked_iota_as_mixed :
  as_mixed (WinChord locked_iota_ls) (WinCirc locked_iota_cs)
    (MixLsCs locked_iota_ls locked_iota_cs).
Proof.
  unfold as_mixed, as_chord, remains_circ, locked_iota_cs.
  split; [reflexivity|].
  split; [exact span_arc_A_valid|reflexivity].
Qed.

Lemma locked_iota_joint_hit_false :
  forall p ti tj,
    ~ I_ok_mixed (MixLsCs locked_iota_ls locked_iota_cs) (IHit p ti tj).
Proof.
  intros p ti tj Hhit.
  destruct (SidecarCircInterior.I_ok_mixed_hit_is_joint_params
              (MixLsCs locked_iota_ls locked_iota_cs) p ti tj Hhit)
    as [Hjp _].
  unfold I_ok_mixed, SidecarCircMixed.I_ok_mixed in Hhit.
  destruct Hhit as [_ [Honc [Hona _]]].
  unfold locked_iota_ls, SidecarCircInteriorHit.locked_interior_ls,
         locked_iota_cs, SidecarCircInteriorHit.locked_interior_cs in *.
  destruct Hjp as [[Hti Htj] | [Hti Htj]]; subst ti tj.
  - unfold on_chord in Honc. destruct Honc as [_ Hp].
    unfold on_arc_gamma in Hona. destruct Hona as [_ Hg].
    rewrite chord_eval_at_1 in Hp.
    rewrite (arc_gamma_start span_arc_A span_arc_A_valid) in Hg.
    apply (f_equal px) in Hp. apply (f_equal px) in Hg.
    destruct span_p_plus_coords as [Hx _].
    cbn [px ce_p1 mkChordEgg mkPoint] in Hp.
    unfold span_arc_A, arc_start in Hg. cbn [px] in Hg.
    rewrite Hx in Hp. lra.
  - unfold on_chord in Honc. destruct Honc as [_ Hp].
    unfold on_arc_gamma in Hona. destruct Hona as [_ Hg].
    rewrite chord_eval_at_0 in Hp.
    rewrite (arc_gamma_end span_arc_A span_arc_A_valid) in Hg.
    apply (f_equal px) in Hp. apply (f_equal px) in Hg.
    destruct span_p_plus_coords as [Hx _].
    cbn [px ce_p0 mkChordEgg mkPoint] in Hp.
    unfold span_arc_A, arc_end in Hg. cbn [px] in Hg.
    rewrite Hx in Hp. lra.
Qed.

Lemma locked_iota_not_has_mu :
  ~ has_mu (WinChord locked_iota_ls) (WinCirc locked_iota_cs).
Proof.
  intros [m [p [ti [tj [Hm Hhit]]]]].
  destruct m as [c a | a c].
  - destruct Hm as [Hc Ha].
    unfold as_chord in Hc. subst c.
    unfold remains_circ in Ha. destruct Ha as [_ Ha]. subst a.
    exact (locked_iota_joint_hit_false p ti tj Hhit).
  - exact Hm.
Qed.

Lemma locked_iota_has_cand :
  has_iota_cand (WinChord locked_iota_ls) (WinCirc locked_iota_cs).
Proof.
  exists (MixLsCs locked_iota_ls locked_iota_cs),
    locked_p_plus,
    SidecarCircInteriorHit.locked_interior_ti,
    SidecarCircInteriorHit.locked_interior_tj.
  split; [exact locked_iota_as_mixed|].
  apply SidecarCircInteriorHit.I_ok_interior_hit_is_arm.
  exact SidecarCircInteriorHit.locked_interior_I_ok_interior.
Qed.

Lemma cell4_iota_candidate :
  iota_cell (WinChord locked_iota_ls) (WinCirc locked_iota_cs) IotaCellIota
  /\ I_ok_mixed_interior_arm
       (MixLsCs locked_iota_ls locked_iota_cs)
       locked_p_plus
       SidecarCircInteriorHit.locked_interior_ti
       SidecarCircInteriorHit.locked_interior_tj
  /\ ~ SidecarCircInterior.interior_mixed_constructor_inhabits
         SidecarCircInterior.InteriorMixedHitArm.
Proof.
  assert (Hm : mixed_pair (WinChord locked_iota_ls) (WinCirc locked_iota_cs)).
  { exists (MixLsCs locked_iota_ls locked_iota_cs). exact locked_iota_as_mixed. }
  split.
  - split; [exact (mixed_not_both_chords _ _ Hm)|].
    split; [exact (mixed_not_both_circs _ _ Hm)|].
    split; [exact Hm|].
    split; [exact locked_iota_not_has_mu|exact locked_iota_has_cand].
  - split.
    + apply SidecarCircInteriorHit.I_ok_interior_hit_is_arm.
      exact SidecarCircInteriorHit.locked_interior_I_ok_interior.
    + exact SidecarCircInterior.interior_mixed_hit_arm_missing.
Qed.

Lemma iota_arm_still_missing :
  ~ SidecarCircInterior.interior_mixed_constructor_inhabits
      SidecarCircInterior.InteriorMixedHitArm.
Proof.
  exact SidecarCircInterior.interior_mixed_hit_arm_missing.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-iota-gate","topic":"overlay","lemma":"ticket_0007_iota_gate_qed_or_qex","title":"iota gate: circ/chord windows hit exactly one of six cells, pairwise exclusive and complete; collinear CircularString-as-chord is cell 1 never cell 4 (QED) or a pair misses every cell (QEX); discharged QED; not a remint of I_ok_mixed / CircGamma / host I_ok","file":"theories/SidecarCircIotaGate.v","witness":"0007-iota-gate","board":"ADR-0007"} *)

Theorem ticket_0007_iota_gate_qed_or_qex :
  ((forall w1 w2, exists c, iota_cell w1 w2 c)
   /\ (forall w1 w2 c1 c2,
         iota_cell w1 w2 c1 -> iota_cell w1 w2 c2 -> c1 = c2)
   /\ (forall c,
         iota_cell (WinCirc collinear_cs) (WinChord c) IotaCellChordChord
         /\ ~ iota_cell (WinCirc collinear_cs) (WinChord c) IotaCellIota)
   /\ (forall c,
         iota_cell (WinChord c) (WinCirc collinear_cs) IotaCellChordChord
         /\ ~ iota_cell (WinChord c) (WinCirc collinear_cs) IotaCellIota))
  \/
  (exists w1 w2, forall c, ~ iota_cell w1 w2 c).
Proof.
  left.
  split; [exact iota_cell_complete|].
  split; [exact iota_cell_exclusive|].
  split.
  - intros c. split; [exact (collinear_cs_as_chord_cell1 c)|].
    exact (collinear_cs_as_chord_not_iota c).
  - intros c. split; [exact (collinear_cs_chord_cell1 c)|].
    exact (collinear_cs_chord_not_iota c).
Qed.

(* WITNESS {"claimId":"0007-iota-gate","topic":"overlay","lemma":"ticket_0007_iota_cook_qed_or_qex","title":"iota cook: InteriorMixedHitArm inhabits I_ok_mixed Hit at interior_span_params on a locked interior mixed pair (QED) or the ctor is missing, mixed_joint_params stands, cells 1-3 reuse I_ok / I_ok_circ / I_ok_mixed, locked pair is the iota candidate (QEX); discharged QEX; I_ok_interior is not this ctor; do not drop mixed_joint_params; not host I_ok; CircGamma is CircGammaDischarged","file":"theories/SidecarCircIotaGate.v","witness":"0007-iota-gate","board":"ADR-0007"} *)

Theorem ticket_0007_iota_cook_qed_or_qex :
  SidecarCircInterior.interior_mixed_constructor_inhabits
    SidecarCircInterior.InteriorMixedHitArm
  \/
  (~ SidecarCircInterior.interior_mixed_constructor_inhabits
       SidecarCircInterior.InteriorMixedHitArm
   /\ iota_cell (WinChord locked_iota_ls) (WinCirc locked_iota_cs)
        IotaCellIota
   /\ I_ok_mixed_interior_arm
        (MixLsCs locked_iota_ls locked_iota_cs)
        locked_p_plus
        SidecarCircInteriorHit.locked_interior_ti
        SidecarCircInteriorHit.locked_interior_tj
   /\ iota_cell (WinChord diag_ab) (WinChord diag_cd) IotaCellChordChord
   /\ I_ok (MkChord diag_ab) (MkChord diag_cd)
        (IHit cross_pt (1 / 2) (1 / 2))
   /\ iota_cell (WinCirc span_arc_A) (WinCirc span_arc_B) IotaCellCircCirc
   /\ I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit
   /\ iota_cell (WinChord locked_mu_ls) (WinCirc locked_mu_cs) IotaCellMu
   /\ I_ok_mixed (MixLsCs locked_mu_ls locked_mu_cs)
        (SidecarCircMixed.ls_cs_joint_hit locked_mu_ls locked_mu_cs)
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ circular_gamma_status = CircGammaDischarged
   /\ cook_loop_status = LoopObligation).
Proof.
  right.
  destruct cell4_iota_candidate as [H4 [Harm Hmiss]].
  destruct cell1_reuses_I_ok as [H1 Hok].
  destruct cell2_reuses_I_ok_circ_hit as [H2 Hcirc].
  destruct cell3_reuses_I_ok_mixed as [H3 [Hmu _]].
  split; [exact Hmiss|].
  split; [exact H4|].
  split; [exact Harm|].
  split; [exact H1|].
  split; [exact Hok|].
  split; [exact H2|].
  split; [exact Hcirc|].
  split; [exact H3|].
  split; [exact Hmu|].
  split; [exact chord_circular_not_first_cook_scope|].
  split; [exact circular_gamma_is_discharged|].
  exact cook_loop_is_obligation.
Qed.

Print Assumptions as_chord_not_remains.
Print Assumptions pair_sort_complete.
Print Assumptions iota_cell_exclusive.
Print Assumptions iota_cell_complete.
Print Assumptions collinear_cs_as_chord_cell1.
Print Assumptions collinear_cs_as_chord_not_iota.
Print Assumptions cell1_reuses_I_ok.
Print Assumptions cell2_reuses_I_ok_circ_hit.
Print Assumptions cell2_reuses_I_ok_circ_empty.
Print Assumptions cell3_reuses_I_ok_mixed.
Print Assumptions locked_iota_joint_hit_false.
Print Assumptions cell4_iota_candidate.
Print Assumptions iota_arm_still_missing.
Print Assumptions ticket_0007_iota_gate_qed_or_qex.
Print Assumptions ticket_0007_iota_cook_qed_or_qex.
