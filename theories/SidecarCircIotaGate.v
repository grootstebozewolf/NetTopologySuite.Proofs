(* ============================================================================
   NetTopologySuite.Proofs.SidecarCircIotaGate
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: ι gate completeness
   (claimId 0007-iota-gate).

   A pair of windows that arrived as circular and/or chord is
   classified by exactly one of six cells. Parks ι
   (SidecarCircInterior.v : InteriorMixedHitArm) stays the cook
   hole: I_ok_mixed Hit ∧ interior_span_params. This letter does
   not remint that ctor, drop mixed_joint_params, expand first
   cook to circular×chord, remint CircGamma, or flip
   LeftoverBagTermArm / LoopDischarged.

   Cells (circ / chord eggs only; no NURBS / clothoid / ellipse):
     1. Both demote to collinear chords → host I_ok first cook.
        Not ι, not μ.
     2. circ × circ (neither demotes) → existing circular cook
        (I_ok_circ unique Hit / Empty; MintTwo two-root arm).
        Not ι.
     3. circ × chord after demote, mixed_joint_params endpoint
        → μ (I_ok_mixed joint). Not ι.
     4. circ × chord, mixed context, both params interior
        → ι candidate (interior_span_params /
          I_ok_mixed_interior_arm). Cook is InteriorMixedHitArm
        if inhabited; else QEX on the park ticket.
     5. mixed miss → Empty.
     6. anything else on this mixed sort → Decline, not ι.

   Collinear CircularString-as-chord takes cell 1, never cell 4.

   QED: pairwise exclusive; every circ/chord pair hits one cell;
   locked fixtures inhabit 1–6; cell 1/2/3/5 reuse existing
   cooks; collinear CS-as-chord is cell 1.
   QEX: InteriorMixedHitArm stays missing (I_ok_mixed Hit is
   joint-only); I_ok_interior on the locked interior pair is
   not that ctor; host mixed I_ok Decline; first cook stays
   chord–chord + circular–circular; LoopObligation stands.

   Honesty fences:
     Host-Decline / CircGammaDischarged at the top of this module.
     I_ok_circ ≠ I_ok_mixed ≠ I_ok_interior ≠ host I_ok.
     InteriorMixedHitArm is I_ok_mixed Hit ∧ interior_span_params.
     I_ok_interior Hit is not that arm. μ ≠ ι.
     Do not drop mixed_joint_params. Do not remint CircGamma /
     host I_ok / LeftoverBagTermArm / LoopDischarged.
     Not first cook expand. Not a bag noder. Not NURBS /
     clothoid / ellipse. Not GEOS / Overlay.

   WITNESS topic: overlay · claimId: 0007-iota-gate
   witness: 0007-iota-gate
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via SidecarCircInterior /
     SidecarCircInteriorHit / CircularCookOkCirc). Category C
     audit-exception: same atan2 lineage as Parks ι; no extra axioms.
   Host lane stays 3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Nra Classical_Prop.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  CircularCook CircularCookHit CircularCookSpan CircularCookOkCirc.
From NTS.Proofs Require CircularCookCsConcat.
From NTS.Proofs Require CircularCookCpConcat.
From NTS.Proofs Require SidecarCircMixed.
From NTS.Proofs Require SidecarCircInterior.
From NTS.Proofs Require SidecarCircInteriorHit.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=iota-gate claim=0007-iota-gate
   file=theories/SidecarCircIotaGate.v
   kind=QED-or-QEX-iota-gate-completeness
   reuse=I_ok,I_ok_circ,I_ok_mixed,I_ok_interior,interior_span_params
   not=CircGamma-remint,first-cook-expand,LoopDischarged,NURBS
   park=InteriorMixedHitArm,Hperp,SQL-MM-cathedral
   land=Phase-B-iota-gate-completeness *)

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma iota_gate_host_circgamma_qex :
  circular_gamma_status = CircGammaDischarged.
Proof.
  exact circular_gamma_is_discharged.
Qed.

Lemma iota_gate_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma iota_gate_not_first_cook_mixed :
  ~ first_cook_scope EggChord EggCircularArc.
Proof.
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
(* Windows that arrived as circular and/or chord. Demote is ~valid_arc.      *)
(* -------------------------------------------------------------------------- *)

Definition I_ok_mixed := SidecarCircInterior.I_ok_mixed.
Definition mixed_joint_params := SidecarCircInterior.mixed_joint_params.
Definition interior_span_params := SidecarCircInterior.interior_span_params.
Definition MixedEggs := SidecarCircInterior.MixedEggs.
Definition MixLsCs := SidecarCircInterior.MixLsCs.
Definition MixCsLs := SidecarCircInterior.MixCsLs.
Definition I_ok_mixed_interior_arm :=
  SidecarCircInterior.I_ok_mixed_interior_arm.
Definition I_ok_interior := SidecarCircInteriorHit.I_ok_interior.

Inductive CircChordWindow : Type :=
| WChord (c : ChordEgg)
| WCirc (a : CircEgg).

Definition circ_demotes (a : CircEgg) : Prop := ~ valid_arc a.

Definition circ_as_chord (a : CircEgg) : ChordEgg :=
  mkChordEgg (arc_start a) (arc_end a).

Definition demotes_to_chord (w : CircChordWindow) : Prop :=
  match w with
  | WChord _ => True
  | WCirc a => circ_demotes a
  end.

Definition stays_circ (w : CircChordWindow) : Prop :=
  match w with
  | WChord _ => False
  | WCirc a => valid_arc a
  end.

Lemma window_class :
  forall w, demotes_to_chord w \/ stays_circ w.
Proof.
  intros [c | a].
  - left. exact I.
  - destruct (classic (valid_arc a)) as [Hv | Hn].
    + right. exact Hv.
    + left. exact Hn.
Qed.

Definition mixed_payload (w1 w2 : CircChordWindow) (m : MixedEggs) : Prop :=
  match w1, w2, m with
  | WChord c, WCirc a, SidecarCircMixed.MixLsCs c' a' =>
      c = c' /\ a = a' /\ valid_arc a
  | WCirc a, WChord c, SidecarCircMixed.MixCsLs a' c' =>
      a = a' /\ c = c' /\ valid_arc a
  | WCirc a, WCirc b, SidecarCircMixed.MixLsCs c' a' =>
      ~ valid_arc a /\ valid_arc b /\ c' = circ_as_chord a /\ a' = b
  | WCirc a, WCirc b, SidecarCircMixed.MixCsLs a' c' =>
      valid_arc a /\ ~ valid_arc b /\ a' = a /\ c' = circ_as_chord b
  | _, _, _ => False
  end.

Definition mixed_images_meet (m : MixedEggs) : Prop :=
  match m with
  | SidecarCircMixed.MixLsCs c a =>
      exists p ti tj, on_chord c ti p /\ on_arc_gamma a tj p
  | SidecarCircMixed.MixCsLs a c =>
      exists p ti tj, on_arc_gamma a ti p /\ on_chord c tj p
  end.

(* -------------------------------------------------------------------------- *)
(* Six cells. Mixed 3–6 are priority-split so they stay exclusive.           *)
(* -------------------------------------------------------------------------- *)

Definition iota_cell1 (w1 w2 : CircChordWindow) : Prop :=
  demotes_to_chord w1 /\ demotes_to_chord w2.

Definition iota_cell2 (w1 w2 : CircChordWindow) : Prop :=
  stays_circ w1 /\ stays_circ w2.

Definition iota_mixed (w1 w2 : CircChordWindow) : Prop :=
  (demotes_to_chord w1 /\ stays_circ w2) \/
  (stays_circ w1 /\ demotes_to_chord w2).

Definition has_mu_hit (w1 w2 : CircChordWindow) : Prop :=
  exists m p ti tj,
    mixed_payload w1 w2 m /\ I_ok_mixed m (IHit p ti tj).

Definition has_iota_arm (w1 w2 : CircChordWindow) : Prop :=
  exists m p ti tj,
    mixed_payload w1 w2 m /\ I_ok_mixed_interior_arm m p ti tj.

Definition has_miss (w1 w2 : CircChordWindow) : Prop :=
  exists m, mixed_payload w1 w2 m /\ ~ mixed_images_meet m.

Definition iota_cell3 (w1 w2 : CircChordWindow) : Prop :=
  iota_mixed w1 w2 /\ has_mu_hit w1 w2.

Definition iota_cell4 (w1 w2 : CircChordWindow) : Prop :=
  iota_mixed w1 w2 /\ ~ has_mu_hit w1 w2 /\ has_iota_arm w1 w2.

Definition iota_cell5 (w1 w2 : CircChordWindow) : Prop :=
  iota_mixed w1 w2 /\ ~ has_mu_hit w1 w2 /\ ~ has_iota_arm w1 w2
  /\ has_miss w1 w2.

Definition iota_cell6 (w1 w2 : CircChordWindow) : Prop :=
  iota_mixed w1 w2 /\ ~ has_mu_hit w1 w2 /\ ~ has_iota_arm w1 w2
  /\ ~ has_miss w1 w2.

(* -------------------------------------------------------------------------- *)
(* Pair-sort exclusive + complete.                                           *)
(* -------------------------------------------------------------------------- *)

Lemma demote_not_stay :
  forall w, demotes_to_chord w -> stays_circ w -> False.
Proof.
  intros [c | a] Hd Hs.
  - exact Hs.
  - exact (Hd Hs).
Qed.

Lemma cell1_not_cell2 :
  forall w1 w2, iota_cell1 w1 w2 -> ~ iota_cell2 w1 w2.
Proof.
  intros w1 w2 [Hd1 Hd2] [Hs1 Hs2].
  exact (demote_not_stay w1 Hd1 Hs1).
Qed.

Lemma cell1_not_mixed :
  forall w1 w2, iota_cell1 w1 w2 -> ~ iota_mixed w1 w2.
Proof.
  intros w1 w2 [Hd1 Hd2] [[_ Hs2] | [Hs1 _]].
  - exact (demote_not_stay w2 Hd2 Hs2).
  - exact (demote_not_stay w1 Hd1 Hs1).
Qed.

Lemma cell2_not_mixed :
  forall w1 w2, iota_cell2 w1 w2 -> ~ iota_mixed w1 w2.
Proof.
  intros w1 w2 [Hs1 Hs2] [[Hd1 _] | [_ Hd2]].
  - exact (demote_not_stay w1 Hd1 Hs1).
  - exact (demote_not_stay w2 Hd2 Hs2).
Qed.

Lemma pair_sort_complete :
  forall w1 w2,
    iota_cell1 w1 w2 \/ iota_cell2 w1 w2 \/ iota_mixed w1 w2.
Proof.
  intros w1 w2.
  destruct (window_class w1) as [D1 | S1];
    destruct (window_class w2) as [D2 | S2].
  - left. split; assumption.
  - right. right. left. split; assumption.
  - right. right. right. split; assumption.
  - right. left. split; assumption.
Qed.

Lemma mixed_cells_complete :
  forall w1 w2,
    iota_mixed w1 w2 ->
    iota_cell3 w1 w2 \/ iota_cell4 w1 w2 \/ iota_cell5 w1 w2
    \/ iota_cell6 w1 w2.
Proof.
  intros w1 w2 Hm.
  destruct (classic (has_mu_hit w1 w2)) as [Hmu | Hnmu].
  - left. split; assumption.
  - destruct (classic (has_iota_arm w1 w2)) as [Hio | Hnio].
    + right. left. split; [exact Hm|]. split; assumption.
    + destruct (classic (has_miss w1 w2)) as [Hmi | Hnmi].
      * right. right. left.
        split; [exact Hm|]. split; [exact Hnmu|]. split; assumption.
      * right. right. right.
        split; [exact Hm|]. split; [exact Hnmu|]. split; assumption.
Qed.

(* WITNESS {"claimId":"0007-iota-gate","topic":"overlay","lemma":"iota_gate_complete","title":"iota gate: every circ/chord window pair hits one of the six cells; pair-sort then mixed priority; not a remint of I_ok_mixed / CircGamma / host I_ok","file":"theories/SidecarCircIotaGate.v","witness":"0007-iota-gate","board":"ADR-0007"} *)

Theorem iota_gate_complete :
  forall w1 w2,
    iota_cell1 w1 w2 \/ iota_cell2 w1 w2 \/ iota_cell3 w1 w2
    \/ iota_cell4 w1 w2 \/ iota_cell5 w1 w2 \/ iota_cell6 w1 w2.
Proof.
  intros w1 w2.
  destruct (pair_sort_complete w1 w2) as [H1 | [H2 | Hm]].
  - left. exact H1.
  - right. left. exact H2.
  - destruct (mixed_cells_complete w1 w2 Hm) as [H3 | [H4 | [H5 | H6]]].
    + right. right. left. exact H3.
    + right. right. right. left. exact H4.
    + right. right. right. right. left. exact H5.
    + right. right. right. right. right. exact H6.
Qed.

(* -------------------------------------------------------------------------- *)
(* Pairwise exclusive.                                                       *)
(* -------------------------------------------------------------------------- *)

Lemma cell1_not_cell3 :
  forall w1 w2, iota_cell1 w1 w2 -> ~ iota_cell3 w1 w2.
Proof.
  intros w1 w2 H1 [Hm _].
  exact (cell1_not_mixed w1 w2 H1 Hm).
Qed.

Lemma cell1_not_cell4 :
  forall w1 w2, iota_cell1 w1 w2 -> ~ iota_cell4 w1 w2.
Proof.
  intros w1 w2 H1 [Hm _].
  exact (cell1_not_mixed w1 w2 H1 Hm).
Qed.

Lemma cell1_not_cell5 :
  forall w1 w2, iota_cell1 w1 w2 -> ~ iota_cell5 w1 w2.
Proof.
  intros w1 w2 H1 [Hm _].
  exact (cell1_not_mixed w1 w2 H1 Hm).
Qed.

Lemma cell1_not_cell6 :
  forall w1 w2, iota_cell1 w1 w2 -> ~ iota_cell6 w1 w2.
Proof.
  intros w1 w2 H1 [Hm _].
  exact (cell1_not_mixed w1 w2 H1 Hm).
Qed.

Lemma cell2_not_cell3 :
  forall w1 w2, iota_cell2 w1 w2 -> ~ iota_cell3 w1 w2.
Proof.
  intros w1 w2 H2 [Hm _].
  exact (cell2_not_mixed w1 w2 H2 Hm).
Qed.

Lemma cell2_not_cell4 :
  forall w1 w2, iota_cell2 w1 w2 -> ~ iota_cell4 w1 w2.
Proof.
  intros w1 w2 H2 [Hm _].
  exact (cell2_not_mixed w1 w2 H2 Hm).
Qed.

Lemma cell2_not_cell5 :
  forall w1 w2, iota_cell2 w1 w2 -> ~ iota_cell5 w1 w2.
Proof.
  intros w1 w2 H2 [Hm _].
  exact (cell2_not_mixed w1 w2 H2 Hm).
Qed.

Lemma cell2_not_cell6 :
  forall w1 w2, iota_cell2 w1 w2 -> ~ iota_cell6 w1 w2.
Proof.
  intros w1 w2 H2 [Hm _].
  exact (cell2_not_mixed w1 w2 H2 Hm).
Qed.

Lemma cell3_not_cell4 :
  forall w1 w2, iota_cell3 w1 w2 -> ~ iota_cell4 w1 w2.
Proof.
  intros w1 w2 [_ Hmu] [_ [Hnmu _]].
  exact (Hnmu Hmu).
Qed.

Lemma cell3_not_cell5 :
  forall w1 w2, iota_cell3 w1 w2 -> ~ iota_cell5 w1 w2.
Proof.
  intros w1 w2 [_ Hmu] [_ [Hnmu _]].
  exact (Hnmu Hmu).
Qed.

Lemma cell3_not_cell6 :
  forall w1 w2, iota_cell3 w1 w2 -> ~ iota_cell6 w1 w2.
Proof.
  intros w1 w2 [_ Hmu] [_ [Hnmu _]].
  exact (Hnmu Hmu).
Qed.

Lemma cell4_not_cell5 :
  forall w1 w2, iota_cell4 w1 w2 -> ~ iota_cell5 w1 w2.
Proof.
  intros w1 w2 [_ [_ Hio]] [_ [_ [Hnio _]]].
  exact (Hnio Hio).
Qed.

Lemma cell4_not_cell6 :
  forall w1 w2, iota_cell4 w1 w2 -> ~ iota_cell6 w1 w2.
Proof.
  intros w1 w2 [_ [_ Hio]] [_ [_ [Hnio _]]].
  exact (Hnio Hio).
Qed.

Lemma cell5_not_cell6 :
  forall w1 w2, iota_cell5 w1 w2 -> ~ iota_cell6 w1 w2.
Proof.
  intros w1 w2 [_ [_ [_ Hmi]]] [_ [_ [_ Hnmi]]].
  exact (Hnmi Hmi).
Qed.

(* WITNESS {"claimId":"0007-iota-gate","topic":"overlay","lemma":"iota_gate_exclusive","title":"iota gate: the six circ/chord cells are pairwise exclusive; joint vs interior uses mixed_joint_params_not_interior priority; not a remint of InteriorMixedHitArm","file":"theories/SidecarCircIotaGate.v","witness":"0007-iota-gate","board":"ADR-0007"} *)

Theorem iota_gate_exclusive :
  forall w1 w2,
    (iota_cell1 w1 w2 ->
       ~ iota_cell2 w1 w2 /\ ~ iota_cell3 w1 w2 /\ ~ iota_cell4 w1 w2
       /\ ~ iota_cell5 w1 w2 /\ ~ iota_cell6 w1 w2)
    /\ (iota_cell2 w1 w2 ->
          ~ iota_cell3 w1 w2 /\ ~ iota_cell4 w1 w2
          /\ ~ iota_cell5 w1 w2 /\ ~ iota_cell6 w1 w2)
    /\ (iota_cell3 w1 w2 ->
          ~ iota_cell4 w1 w2 /\ ~ iota_cell5 w1 w2 /\ ~ iota_cell6 w1 w2)
    /\ (iota_cell4 w1 w2 -> ~ iota_cell5 w1 w2 /\ ~ iota_cell6 w1 w2)
    /\ (iota_cell5 w1 w2 -> ~ iota_cell6 w1 w2).
Proof.
  intros w1 w2.
  repeat split; intros H.
  - exact (cell1_not_cell2 w1 w2 H).
  - exact (cell1_not_cell3 w1 w2 H).
  - exact (cell1_not_cell4 w1 w2 H).
  - exact (cell1_not_cell5 w1 w2 H).
  - exact (cell1_not_cell6 w1 w2 H).
  - exact (cell2_not_cell3 w1 w2 H).
  - exact (cell2_not_cell4 w1 w2 H).
  - exact (cell2_not_cell5 w1 w2 H).
  - exact (cell2_not_cell6 w1 w2 H).
  - exact (cell3_not_cell4 w1 w2 H).
  - exact (cell3_not_cell5 w1 w2 H).
  - exact (cell3_not_cell6 w1 w2 H).
  - exact (cell4_not_cell5 w1 w2 H).
  - exact (cell4_not_cell6 w1 w2 H).
  - exact (cell5_not_cell6 w1 w2 H).
Qed.

(* -------------------------------------------------------------------------- *)
(* Collinear CircularString-as-chord: cell 1, never cell 4.                  *)
(* -------------------------------------------------------------------------- *)

Lemma collinear_cs_as_chord_cell1 :
  forall a c,
    ~ valid_arc a ->
    iota_cell1 (WCirc a) (WChord c)
    /\ ~ iota_cell4 (WCirc a) (WChord c).
Proof.
  intros a c Hn.
  split.
  - split; [exact Hn|]. exact I.
  - intros [Hm _].
    apply (cell1_not_mixed (WCirc a) (WChord c)); [|exact Hm].
    split; [exact Hn|]. exact I.
Qed.

Lemma locked_collinear_cs_cell1 :
  iota_cell1 (WCirc span_decline_arc) (WChord hor_bot)
  /\ ~ iota_cell4 (WCirc span_decline_arc) (WChord hor_bot).
Proof.
  apply collinear_cs_as_chord_cell1.
  exact span_decline_arc_invalid.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked fixtures + cook reuse (do not remint).                             *)
(* -------------------------------------------------------------------------- *)

Definition locked_w_chord_ab : CircChordWindow := WChord diag_ab.
Definition locked_w_chord_cd : CircChordWindow := WChord diag_cd.
Definition locked_w_circ_A : CircChordWindow := WCirc span_arc_A.
Definition locked_w_circ_B : CircChordWindow := WCirc span_arc_B.
Definition locked_w_mu_ls : CircChordWindow :=
  WChord SidecarCircInterior.locked_mixed_ls.
Definition locked_w_mu_cs : CircChordWindow :=
  WCirc SidecarCircInterior.locked_mixed_cs.
Definition locked_w_iota_ls : CircChordWindow :=
  WChord SidecarCircInteriorHit.locked_interior_ls.
Definition locked_w_iota_cs : CircChordWindow :=
  WCirc SidecarCircInteriorHit.locked_interior_cs.

Definition locked_cell6_ls : ChordEgg :=
  mkChordEgg (mkPoint 5 0) (mkPoint 15 0).

Definition locked_w_cell6_ls : CircChordWindow := WChord locked_cell6_ls.
Definition locked_w_cell6_cs : CircChordWindow := WCirc span_arc_A.
Definition locked_w_miss_ls : CircChordWindow := WChord hor_bot.
Definition locked_w_miss_cs : CircChordWindow := WCirc span_empty_far.

Lemma locked_cell1_inhabits :
  iota_cell1 locked_w_chord_ab locked_w_chord_cd.
Proof.
  split; exact I.
Qed.

Lemma locked_cell1_reuses_I_ok :
  iota_cell1 locked_w_chord_ab locked_w_chord_cd
  /\ I_ok (MkChord diag_ab) (MkChord diag_cd)
       (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  split; [exact locked_cell1_inhabits|].
  exact crossing_I_ok.
Qed.

Lemma locked_cell2_inhabits :
  iota_cell2 locked_w_circ_A locked_w_circ_B.
Proof.
  split; [exact span_arc_A_valid|].
  exact span_arc_B_valid.
Qed.

Lemma locked_cell2_reuses_I_ok_circ :
  iota_cell2 locked_w_circ_A locked_w_circ_B
  /\ I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit
  /\ I_ok_circ span_arc_A span_empty_far IEmpty
  /\ ~ iota_cell4 locked_w_circ_A locked_w_circ_B.
Proof.
  split; [exact locked_cell2_inhabits|].
  split; [exact ii3_locked_plus_I_ok_circ|].
  split; [exact ii3_locked_empty|].
  apply cell2_not_cell4.
  exact locked_cell2_inhabits.
Qed.

Lemma locked_mu_payload :
  mixed_payload locked_w_mu_ls locked_w_mu_cs
    (MixLsCs SidecarCircInterior.locked_mixed_ls
             SidecarCircInterior.locked_mixed_cs).
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  exact CircularCookCsConcat.locked_cs_arc_2_valid.
Qed.

Lemma locked_cell3_inhabits :
  iota_cell3 locked_w_mu_ls locked_w_mu_cs.
Proof.
  split.
  - left. split; [exact I|].
    exact CircularCookCsConcat.locked_cs_arc_2_valid.
  - exists (MixLsCs SidecarCircInterior.locked_mixed_ls
                    SidecarCircInterior.locked_mixed_cs),
           SidecarCircInterior.locked_mixed_ls_cs_pt, 1, 0.
    split; [exact locked_mu_payload|].
    exact SidecarCircInterior.iota_mu_joint_I_ok_mixed.
Qed.

Lemma locked_cell3_reuses_I_ok_mixed :
  iota_cell3 locked_w_mu_ls locked_w_mu_cs
  /\ I_ok_mixed
       (MixLsCs SidecarCircInterior.locked_mixed_ls
                SidecarCircInterior.locked_mixed_cs)
       (SidecarCircMixed.ls_cs_joint_hit
          SidecarCircInterior.locked_mixed_ls
          SidecarCircInterior.locked_mixed_cs)
  /\ ~ interior_span_params 1 0
  /\ ~ iota_cell4 locked_w_mu_ls locked_w_mu_cs.
Proof.
  split; [exact locked_cell3_inhabits|].
  split; [exact SidecarCircInterior.iota_mu_joint_I_ok_mixed|].
  split; [exact CircularCookCsConcat.joint_params_not_interior|].
  apply cell3_not_cell4.
  exact locked_cell3_inhabits.
Qed.

Lemma locked_iota_payload :
  mixed_payload locked_w_iota_ls locked_w_iota_cs
    (MixLsCs SidecarCircInteriorHit.locked_interior_ls
             SidecarCircInteriorHit.locked_interior_cs).
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  exact span_arc_A_valid.
Qed.

Lemma locked_iota_not_mu :
  ~ has_mu_hit locked_w_iota_ls locked_w_iota_cs.
Proof.
  intros [m [p [ti [tj [Hp Hhit]]]]].
  destruct m as [c a | a c].
  2: {
    exact Hp.
  }
  destruct Hp as [Hc [Ha _]].
  rewrite <- Hc, <- Ha in Hhit.
  unfold I_ok_mixed, SidecarCircMixed.I_ok_mixed in Hhit.
  destruct Hhit as [_ [Honc [Hona Hm]]].
  unfold mixed_joint_params, SidecarCircMixed.mixed_joint_params in Hm.
  destruct Honc as [_ Hpch].
  destruct Hona as [_ Hparc].
  destruct Hm as [[-> ->] | [-> ->]].
  - rewrite chord_eval_at_1 in Hpch.
    rewrite (arc_gamma_start _ span_arc_A_valid) in Hparc.
    rewrite Hpch in Hparc.
    apply (f_equal py) in Hparc.
    unfold SidecarCircInteriorHit.locked_interior_ls in Hparc.
    cbn [ce_p1 px py] in Hparc.
    pose proof span_p_plus_y_pos as Hy.
    change (py (mkPoint 5 0)) with 0 in Hparc.
    lra.
  - rewrite chord_eval_at_0 in Hpch.
    rewrite (arc_gamma_end _ span_arc_A_valid) in Hparc.
    rewrite Hpch in Hparc.
    apply (f_equal px) in Hparc.
    unfold SidecarCircInteriorHit.locked_interior_ls in Hparc.
    cbn [ce_p0 px py] in Hparc.
    destruct span_p_plus_coords as [Hx _].
    change (px (mkPoint 0 5)) with 0 in Hparc.
    lra.
Qed.

Lemma locked_cell4_inhabits :
  iota_cell4 locked_w_iota_ls locked_w_iota_cs.
Proof.
  split.
  - left. split; [exact I|]. exact span_arc_A_valid.
  - split; [exact locked_iota_not_mu|].
    exists (MixLsCs SidecarCircInteriorHit.locked_interior_ls
                    SidecarCircInteriorHit.locked_interior_cs),
           locked_p_plus,
           SidecarCircInteriorHit.locked_interior_ti,
           SidecarCircInteriorHit.locked_interior_tj.
    split; [exact locked_iota_payload|].
    apply SidecarCircInteriorHit.I_ok_interior_hit_is_arm.
    exact SidecarCircInteriorHit.locked_interior_I_ok_interior.
Qed.

Lemma locked_cell4_iota_arm_not_InteriorMixedHitArm :
  iota_cell4 locked_w_iota_ls locked_w_iota_cs
  /\ I_ok_interior
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
  split; [exact locked_cell4_inhabits|].
  exact SidecarCircInteriorHit.iota_park_not_discharged_by_I_ok_interior.
Qed.

(* Cell 5: far chord × far arc. Images miss. *)

Lemma locked_miss_payload :
  mixed_payload locked_w_miss_ls locked_w_miss_cs
    (MixLsCs hor_bot span_empty_far).
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  exact span_empty_far_valid.
Qed.

Lemma locked_miss_not_meet :
  ~ mixed_images_meet (MixLsCs hor_bot span_empty_far).
Proof.
  intros [p [ti [tj [Hc Ha]]]].
  destruct Hc as [Hti Hp].
  destruct Ha as [_ Hg].
  pose proof (arc_gamma_on_circle span_empty_far tj) as Hon.
  rewrite <- Hg in Hon.
  rewrite span_empty_far_center, span_empty_far_radius in Hon.
  rewrite Hp in Hon.
  unfold hor_bot, chord_eval, span_empty_far_O, dist_sq in Hon.
  cbn [ce_p0 ce_p1 px py] in Hon.
  replace ((1 - ti) * 0 + ti * 1) with ti in Hon by ring.
  replace ((1 - ti) * 0 + ti * 0) with 0 in Hon by ring.
  replace ((20 - ti) * (20 - ti) + (0 - 0) * (0 - 0))
    with ((20 - ti) * (20 - ti)) in Hon by ring.
  assert (Hsq : (20 - ti) * (20 - ti) = 25) by (rewrite Hon; ring).
  assert (Hbd : 19 <= 20 - ti <= 20) by lra.
  nra.
Qed.

Lemma locked_miss_not_mu :
  ~ has_mu_hit locked_w_miss_ls locked_w_miss_cs.
Proof.
  intros [m [p [ti [tj [Hp Hhit]]]]].
  destruct m as [c a | a c].
  2: {
    exact Hp.
  }
  destruct Hp as [Hc [Ha _]].
  rewrite <- Hc, <- Ha in Hhit.
  unfold I_ok_mixed, SidecarCircMixed.I_ok_mixed in Hhit.
  destruct Hhit as [_ [Honc [Hona _]]].
  apply locked_miss_not_meet.
  exists p, ti, tj.
  split; [exact Honc|exact Hona].
Qed.

Lemma locked_miss_not_iota_arm :
  ~ has_iota_arm locked_w_miss_ls locked_w_miss_cs.
Proof.
  intros [m [p [ti [tj [Hp Harm]]]]].
  destruct m as [c a | a c].
  2: {
    exact Hp.
  }
  destruct Hp as [Hc [Ha _]].
  rewrite <- Hc, <- Ha in Harm.
  unfold I_ok_mixed_interior_arm,
         SidecarCircInterior.I_ok_mixed_interior_arm in Harm.
  destruct Harm as [_ [Honc [Hona _]]].
  apply locked_miss_not_meet.
  exists p, ti, tj.
  split; [exact Honc|exact Hona].
Qed.

Lemma locked_cell5_inhabits :
  iota_cell5 locked_w_miss_ls locked_w_miss_cs.
Proof.
  split.
  - left. split; [exact I|]. exact span_empty_far_valid.
  - split; [exact locked_miss_not_mu|].
    split; [exact locked_miss_not_iota_arm|].
    exists (MixLsCs hor_bot span_empty_far).
    split; [exact locked_miss_payload|].
    exact locked_miss_not_meet.
Qed.

(* Cell 6: start-start coincidence. Meet, not μ, not interior. *)

Lemma locked_cell6_payload :
  mixed_payload locked_w_cell6_ls locked_w_cell6_cs
    (MixLsCs locked_cell6_ls span_arc_A).
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  exact span_arc_A_valid.
Qed.

Lemma locked_cell6_meets :
  mixed_images_meet (MixLsCs locked_cell6_ls span_arc_A).
Proof.
  exists (mkPoint 5 0), 0, 0.
  split.
  - apply SidecarCircMixed.mixed_on_chord_at_start.
  - apply CircularCookCsConcat.on_arc_gamma_at_start.
    exact span_arc_A_valid.
Qed.

Lemma locked_cell6_not_mu :
  ~ has_mu_hit locked_w_cell6_ls locked_w_cell6_cs.
Proof.
  intros [m [p [ti [tj [Hp Hhit]]]]].
  destruct m as [c a | a c].
  2: {
    exact Hp.
  }
  destruct Hp as [Hc [Ha _]].
  rewrite <- Hc, <- Ha in Hhit.
  unfold I_ok_mixed, SidecarCircMixed.I_ok_mixed in Hhit.
  destruct Hhit as [_ [Honc [Hona Hm]]].
  unfold mixed_joint_params, SidecarCircMixed.mixed_joint_params in Hm.
  destruct Honc as [_ Hpch].
  destruct Hona as [_ Hparc].
  destruct Hm as [[-> ->] | [-> ->]].
  - rewrite chord_eval_at_1 in Hpch.
    rewrite (arc_gamma_start _ span_arc_A_valid) in Hparc.
    rewrite Hpch in Hparc.
    apply (f_equal px) in Hparc.
    unfold locked_cell6_ls in Hparc.
    cbn [ce_p1 px] in Hparc.
    change (px (mkPoint 15 0)) with 15 in Hparc.
    change (px (mkPoint 5 0)) with 5 in Hparc.
    lra.
  - rewrite chord_eval_at_0 in Hpch.
    rewrite (arc_gamma_end _ span_arc_A_valid) in Hparc.
    rewrite Hpch in Hparc.
    apply (f_equal px) in Hparc.
    unfold locked_cell6_ls in Hparc.
    cbn [ce_p0 px] in Hparc.
    change (px (mkPoint 5 0)) with 5 in Hparc.
    change (px (mkPoint 0 5)) with 0 in Hparc.
    lra.
Qed.

Lemma locked_cell6_not_iota_arm :
  ~ has_iota_arm locked_w_cell6_ls locked_w_cell6_cs.
Proof.
  intros [m [p [ti [tj [Hp Harm]]]]].
  destruct m as [c a | a c].
  2: {
    exact Hp.
  }
  destruct Hp as [Hc [Ha _]].
  rewrite <- Hc, <- Ha in Harm.
  unfold I_ok_mixed_interior_arm,
         SidecarCircInterior.I_ok_mixed_interior_arm in Harm.
  destruct Harm as [_ [Honc [Hona Hinner]]].
  destruct Honc as [Hti Hpch].
  destruct Hona as [_ Hparc].
  destruct Hinner as [[Hti0 Hti1] _].
  pose proof (arc_gamma_on_circle span_arc_A tj) as Hon.
  rewrite <- Hparc in Hon.
  rewrite span_arc_A_center, span_arc_A_radius in Hon.
  rewrite Hpch in Hon.
  unfold locked_cell6_ls, chord_eval, locked_O1, locked_r, dist_sq in Hon.
  cbn [ce_p0 ce_p1 px py] in Hon.
  replace ((1 - ti) * 5 + ti * 15) with (5 + 10 * ti) in Hon by ring.
  replace ((1 - ti) * 0 + ti * 0) with 0 in Hon by ring.
  replace ((0 - (5 + 10 * ti)) * (0 - (5 + 10 * ti))
           + (0 - 0) * (0 - 0))
    with ((5 + 10 * ti) * (5 + 10 * ti)) in Hon by ring.
  assert (Hsq : (5 + 10 * ti) * (5 + 10 * ti) = 25) by (rewrite Hon; ring).
  assert (Hbd : 5 < 5 + 10 * ti < 15) by lra.
  nra.
Qed.

Lemma locked_cell6_not_miss :
  ~ has_miss locked_w_cell6_ls locked_w_cell6_cs.
Proof.
  intros [m [Hp Hn]].
  destruct m as [c a | a c].
  2: {
    exact Hp.
  }
  destruct Hp as [Hc [Ha _]].
  rewrite <- Hc, <- Ha in Hn.
  exact (Hn locked_cell6_meets).
Qed.

Lemma locked_cell6_inhabits :
  iota_cell6 locked_w_cell6_ls locked_w_cell6_cs.
Proof.
  split.
  - left. split; [exact I|]. exact span_arc_A_valid.
  - split; [exact locked_cell6_not_mu|].
    split; [exact locked_cell6_not_iota_arm|].
    exact locked_cell6_not_miss.
Qed.

(* -------------------------------------------------------------------------- *)
(* Parks / letter-local status.                                              *)
(* -------------------------------------------------------------------------- *)

Inductive IotaGateLetterStatus : Type :=
| IotaGateLetterLanded
| IotaGateLetterParked.

Definition iota_gate_letter_status : IotaGateLetterStatus :=
  IotaGateLetterLanded.

Lemma iota_gate_letter_is_landed :
  iota_gate_letter_status = IotaGateLetterLanded.
Proof.
  reflexivity.
Qed.

Lemma iota_gate_interior_cook_stays_parked :
  SidecarCircInterior.iota_interior_cook_status
  = SidecarCircInterior.IotaInteriorCookParked.
Proof.
  exact SidecarCircInterior.iota_interior_cook_is_parked.
Qed.

Lemma iota_gate_phase_b_stays_open :
  CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen.
Proof.
  exact CircularCookCpConcat.phase_b_is_open.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                             *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-iota-gate","topic":"overlay","lemma":"ticket_0007_iota_gate_qed_or_qex","title":"iota gate every circ/chord pair hits exactly one of six exclusive cells (QED) or a locked collinear CircularString-as-chord inhabits cell 4 (QEX); discharged QED; collinear CS-as-chord is cell 1; mixed_joint_params stands","file":"theories/SidecarCircIotaGate.v","witness":"0007-iota-gate","board":"ADR-0007"} *)

Theorem ticket_0007_iota_gate_qed_or_qex :
  ((forall w1 w2,
      iota_cell1 w1 w2 \/ iota_cell2 w1 w2 \/ iota_cell3 w1 w2
      \/ iota_cell4 w1 w2 \/ iota_cell5 w1 w2 \/ iota_cell6 w1 w2)
   /\ (forall w1 w2,
         iota_cell1 w1 w2 -> ~ iota_cell4 w1 w2)
   /\ iota_cell1 (WCirc span_decline_arc) (WChord hor_bot)
   /\ ~ iota_cell4 (WCirc span_decline_arc) (WChord hor_bot)
   /\ iota_cell1 locked_w_chord_ab locked_w_chord_cd
   /\ iota_cell2 locked_w_circ_A locked_w_circ_B
   /\ iota_cell3 locked_w_mu_ls locked_w_mu_cs
   /\ iota_cell4 locked_w_iota_ls locked_w_iota_cs
   /\ iota_cell5 locked_w_miss_ls locked_w_miss_cs
   /\ iota_cell6 locked_w_cell6_ls locked_w_cell6_cs)
  \/
  iota_cell4 (WCirc span_decline_arc) (WChord hor_bot).
Proof.
  left.
  split; [exact iota_gate_complete|].
  split; [exact cell1_not_cell4|].
  destruct locked_collinear_cs_cell1 as [H1 Hn].
  split; [exact H1|].
  split; [exact Hn|].
  split; [exact locked_cell1_inhabits|].
  split; [exact locked_cell2_inhabits|].
  split; [exact locked_cell3_inhabits|].
  split; [exact locked_cell4_inhabits|].
  split; [exact locked_cell5_inhabits|].
  exact locked_cell6_inhabits.
Qed.

(* WITNESS {"claimId":"0007-iota-gate","topic":"overlay","lemma":"ticket_0007_iota_gate_cook_qed_or_qex","title":"iota gate cell cooks: 1 reuses host I_ok, 2 reuses I_ok_circ, 3 reuses I_ok_mixed mu, 4 inhabits InteriorMixedHitArm and splits both windows (QED) or InteriorMixedHitArm stays missing and I_ok_interior is not that ctor (QEX); discharged QEX on the arm; do not drop mixed_joint_params; not host I_ok; not LoopDischarged","file":"theories/SidecarCircIotaGate.v","witness":"0007-iota-gate","board":"ADR-0007"} *)

Theorem ticket_0007_iota_gate_cook_qed_or_qex :
  (SidecarCircInterior.interior_mixed_constructor_inhabits
     SidecarCircInterior.InteriorMixedHitArm
   /\ first_cook_scope EggChord EggCircularArc
   /\ cook_loop_status = LoopDischarged)
  \/
  (~ SidecarCircInterior.interior_mixed_constructor_inhabits
      SidecarCircInterior.InteriorMixedHitArm
   /\ I_ok (MkChord diag_ab) (MkChord diag_cd)
        (IHit cross_pt (1 / 2) (1 / 2))
   /\ I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit
   /\ I_ok_mixed
        (MixLsCs SidecarCircInterior.locked_mixed_ls
                 SidecarCircInterior.locked_mixed_cs)
        (SidecarCircMixed.ls_cs_joint_hit
           SidecarCircInterior.locked_mixed_ls
           SidecarCircInterior.locked_mixed_cs)
   /\ I_ok_interior
        (MixLsCs SidecarCircInteriorHit.locked_interior_ls
                 SidecarCircInteriorHit.locked_interior_cs)
        SidecarCircInteriorHit.locked_interior_hit
   /\ iota_cell4 locked_w_iota_ls locked_w_iota_cs
   /\ iota_cell5 locked_w_miss_ls locked_w_miss_cs
   /\ (forall m p ti tj,
         I_ok_mixed m (IHit p ti tj) ->
         mixed_joint_params ti tj /\ ~ interior_span_params ti tj)
   /\ circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggChord EggChord
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ cook_loop_status = LoopObligation
   /\ SidecarCircInterior.iota_interior_cook_status
      = SidecarCircInterior.IotaInteriorCookParked).
Proof.
  right.
  split; [exact SidecarCircInterior.interior_mixed_hit_arm_missing|].
  split; [exact crossing_I_ok|].
  split; [exact ii3_locked_plus_I_ok_circ|].
  split; [exact SidecarCircInterior.iota_mu_joint_I_ok_mixed|].
  split; [exact SidecarCircInteriorHit.locked_interior_I_ok_interior|].
  split; [exact locked_cell4_inhabits|].
  split; [exact locked_cell5_inhabits|].
  split; [exact SidecarCircInterior.I_ok_mixed_hit_is_joint_params|].
  split; [exact iota_gate_host_circgamma_qex|].
  split; [exact iota_gate_first_cook_stays_chord_chord|].
  split; [exact circular_is_first_cook_scope|].
  split; [exact iota_gate_not_first_cook_mixed|].
  split; [exact cook_loop_is_obligation|].
  exact iota_gate_interior_cook_stays_parked.
Qed.

(* WITNESS {"claimId":"0007-iota-gate","topic":"overlay","lemma":"ticket_0007_iota_gate_park_qed_or_qex","title":"iota gate discharges InteriorMixedHitArm, expands first cook, and flips LoopDischarged (QED) or names them parked / obligation (QEX); discharged QEX; gate letter landed; letter landed != interior cook Landed / LoopDischarged / CircGamma remint","file":"theories/SidecarCircIotaGate.v","witness":"0007-iota-gate","board":"ADR-0007"} *)

Theorem ticket_0007_iota_gate_park_qed_or_qex :
  (SidecarCircInterior.interior_mixed_constructor_inhabits
     SidecarCircInterior.InteriorMixedHitArm
   /\ SidecarCircInterior.iota_interior_cook_status
      = SidecarCircInterior.IotaInteriorCookLanded
   /\ cook_loop_status = LoopDischarged
   /\ first_cook_scope EggChord EggCircularArc
   /\ CircularCookCpConcat.phase_b_status
      = CircularCookCpConcat.PhaseBLanded)
  \/
  (iota_gate_letter_status = IotaGateLetterLanded
   /\ ~ SidecarCircInterior.interior_mixed_constructor_inhabits
         SidecarCircInterior.InteriorMixedHitArm
   /\ SidecarCircInterior.iota_interior_cook_status
      = SidecarCircInterior.IotaInteriorCookParked
   /\ cook_loop_status = LoopObligation
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen).
Proof.
  right.
  split; [exact iota_gate_letter_is_landed|].
  split; [exact SidecarCircInterior.interior_mixed_hit_arm_missing|].
  split; [exact iota_gate_interior_cook_stays_parked|].
  split; [exact cook_loop_is_obligation|].
  split; [exact iota_gate_not_first_cook_mixed|].
  exact iota_gate_phase_b_stays_open.
Qed.

Print Assumptions iota_gate_host_circgamma_qex.
Print Assumptions iota_gate_complete.
Print Assumptions iota_gate_exclusive.
Print Assumptions collinear_cs_as_chord_cell1.
Print Assumptions locked_collinear_cs_cell1.
Print Assumptions locked_cell1_reuses_I_ok.
Print Assumptions locked_cell2_reuses_I_ok_circ.
Print Assumptions locked_cell3_reuses_I_ok_mixed.
Print Assumptions locked_cell4_iota_arm_not_InteriorMixedHitArm.
Print Assumptions locked_cell5_inhabits.
Print Assumptions locked_cell6_inhabits.
Print Assumptions iota_gate_not_bag_noder.
Print Assumptions ticket_0007_iota_gate_qed_or_qex.
Print Assumptions ticket_0007_iota_gate_cook_qed_or_qex.
Print Assumptions ticket_0007_iota_gate_park_qed_or_qex.
