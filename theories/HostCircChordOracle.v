(* ============================================================================
   NetTopologySuite.Proofs.HostCircChordOracle
   ----------------------------------------------------------------------------
   NTS/JTS: MCIndexNoder mixed segment (LineString chord × CircularString).
   claimId: 0007-host-circ-chord-oracle

   Host 𝓘 on MkCirc × MkChord and the reverse. In scope
   (|Δθ| < 2π, nondegenerate chord) a Hit is on both curves, and every
   such incidence is a Hit. Full-span eggs and degenerate chords Decline
   by name. circ×circ stays the existing host arm (Decline is False).
   first_cook_scope does not gain the mixed arms.

   The locked CC LS+CS joint is a host Hit, so the ∀-bag loop does not
   StepIDecline on that pair. The joint is already a vertex of both
   pieces, so it is not a progress_hit. An interior hit of the same
   locked quarter (F1) is a bag_progress_step and the children keep
   same_support.

   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import
  Distance SheetHenCook SheetHenBag ZetaHostHit ZetaEggBridge
  CircularCookMkCirc IntakeWalker.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* -------------------------------------------------------------------------- *)
(* Soundness and completeness, both argument orders.                          *)
(* -------------------------------------------------------------------------- *)

Lemma I_ok_circ_chord_hit_sound :
  forall c s p ti tj,
    I_ok (MkCirc c) (MkChord s) (IHit p ti tj) ->
    on_circ c ti p /\ on_chord s tj p.
Proof.
  intros c s p ti tj H. destruct H as [_ H]. exact H.
Qed.

Lemma I_ok_chord_circ_hit_sound :
  forall s c p ti tj,
    I_ok (MkChord s) (MkCirc c) (IHit p ti tj) ->
    on_chord s ti p /\ on_circ c tj p.
Proof.
  intros s c p ti tj H. destruct H as [_ H]. exact H.
Qed.

Lemma I_ok_circ_chord_hit_complete :
  forall c s p ti tj,
    circ_chord_host_scope c s ->
    on_circ c ti p ->
    on_chord s tj p ->
    I_ok (MkCirc c) (MkChord s) (IHit p ti tj).
Proof.
  intros c s p ti tj Hs Hc Hh.
  unfold I_ok. split; [exact Hs|]. split; [exact Hc|exact Hh].
Qed.

Lemma I_ok_chord_circ_hit_complete :
  forall s c p ti tj,
    circ_chord_host_scope c s ->
    on_chord s ti p ->
    on_circ c tj p ->
    I_ok (MkChord s) (MkCirc c) (IHit p ti tj).
Proof.
  intros s c p ti tj Hs Hh Hc.
  unfold I_ok. split; [exact Hs|]. split; [exact Hh|exact Hc].
Qed.

Lemma I_ok_circ_chord_no_miss :
  forall c s p ti tj,
    circ_chord_host_scope c s ->
    on_circ c ti p ->
    on_chord s tj p ->
    exists p' ti' tj',
      I_ok (MkCirc c) (MkChord s) (IHit p' ti' tj').
Proof.
  intros c s p ti tj Hs Hc Hh.
  exists p, ti, tj.
  apply I_ok_circ_chord_hit_complete; assumption.
Qed.

Lemma I_ok_chord_circ_no_miss :
  forall s c p ti tj,
    circ_chord_host_scope c s ->
    on_chord s ti p ->
    on_circ c tj p ->
    exists p' ti' tj',
      I_ok (MkChord s) (MkCirc c) (IHit p' ti' tj').
Proof.
  intros s c p ti tj Hs Hh Hc.
  exists p, ti, tj.
  apply I_ok_chord_circ_hit_complete; assumption.
Qed.

Lemma I_ok_circ_chord_empty_sound :
  forall c s,
    I_ok (MkCirc c) (MkChord s) IEmpty ->
    ~ exists X t1 t2, on_circ c t1 X /\ on_chord s t2 X.
Proof.
  intros c s H. destruct H as [_ H]. exact H.
Qed.

Lemma I_ok_chord_circ_empty_sound :
  forall s c,
    I_ok (MkChord s) (MkCirc c) IEmpty ->
    ~ exists X t1 t2, on_chord s t1 X /\ on_circ c t2 X.
Proof.
  intros s c H. destruct H as [_ H]. exact H.
Qed.

Lemma circ_chord_in_scope_not_decline :
  forall c s,
    circ_chord_host_scope c s ->
    ~ I_ok (MkCirc c) (MkChord s) IDecline /\
    ~ I_ok (MkChord s) (MkCirc c) IDecline.
Proof.
  intros c s Hs. split; intro H; apply H; exact Hs.
Qed.

(* Chart hit (host_circ_chord_hit_ok) is a host Hit. *)
Lemma zeta_seg_hit_I_ok :
  forall (c : CircularEgg) (s : ChordEgg) (z : R),
    circ_r c <> 0 ->
    circ_sweep c <> 0 ->
    circ_open_span c ->
    chord_nondeg s ->
    zeta_seg_hit c s z ->
    I_ok (MkCirc c) (MkChord s)
      (IHit (zeta_pt (circ_o c) (egg_pole c) z)
            (t_of_zeta c z) (egg_tj c s z)).
Proof.
  intros c s z Hr Hs Hsp Hnd Hz.
  destruct (host_circ_chord_hit_ok c s Hr Hs Hsp z Hnd Hz) as [Hc Hch].
  apply I_ok_circ_chord_hit_complete.
  - split; assumption.
  - exact Hc.
  - exact Hch.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named declines. Full-span and a degenerate chord are not demoted.          *)
(* circ×circ is already a host arm: Decline is False.                         *)
(* -------------------------------------------------------------------------- *)

Lemma full_span_not_open :
  ~ circ_open_span locked_full_circle_egg.
Proof.
  unfold circ_open_span, locked_full_circle_egg. cbn.
  intros [_ H]. lra.
Qed.

Lemma full_span_circ_chord_decline :
  forall s,
    I_ok (MkCirc locked_full_circle_egg) (MkChord s) IDecline.
Proof.
  intro s. unfold I_ok. intro Hs.
  exact (full_span_not_open (proj1 Hs)).
Qed.

Lemma full_span_chord_circ_decline :
  forall s,
    I_ok (MkChord s) (MkCirc locked_full_circle_egg) IDecline.
Proof.
  intro s. unfold I_ok. intro Hs.
  exact (full_span_not_open (proj1 Hs)).
Qed.

Lemma full_span_hit_false :
  forall s p ti tj,
    ~ I_ok (MkCirc locked_full_circle_egg) (MkChord s) (IHit p ti tj) /\
    ~ I_ok (MkChord s) (MkCirc locked_full_circle_egg) (IHit p ti tj).
Proof.
  intros s p ti tj. split; intro H;
    exact (full_span_not_open (proj1 (proj1 H))).
Qed.

Definition degen_chord : ChordEgg :=
  mkChordEgg (mkPoint 0 0) (mkPoint 0 0).

Lemma degen_not_nondeg : ~ chord_nondeg degen_chord.
Proof.
  unfold chord_nondeg, chord_dx, chord_dy, degen_chord. cbn.
  intro H. apply H. f_equal2; ring.
Qed.

Lemma degen_circ_chord_decline :
  forall c, I_ok (MkCirc c) (MkChord degen_chord) IDecline.
Proof.
  intro c. unfold I_ok. intro Hs.
  exact (degen_not_nondeg (proj2 Hs)).
Qed.

Lemma degen_chord_circ_decline :
  forall c, I_ok (MkChord degen_chord) (MkCirc c) IDecline.
Proof.
  intro c. unfold I_ok. intro Hs.
  exact (degen_not_nondeg (proj2 Hs)).
Qed.

Lemma degen_hit_false :
  forall c p ti tj,
    ~ I_ok (MkCirc c) (MkChord degen_chord) (IHit p ti tj) /\
    ~ I_ok (MkChord degen_chord) (MkCirc c) (IHit p ti tj).
Proof.
  intros c p ti tj. split; intro H;
    exact (degen_not_nondeg (proj2 (proj1 H))).
Qed.

Lemma circ_circ_not_decline :
  forall c1 c2, ~ I_ok (MkCirc c1) (MkCirc c2) IDecline.
Proof.
  intros c1 c2 H. exact H.
Qed.

Lemma mixed_not_first_cook :
  ~ first_cook_scope EggChord EggCircularArc /\
  ~ first_cook_scope EggCircularArc EggChord.
Proof.
  split; [exact chord_circular_not_first_cook_scope|].
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked CC LS+CS. Host Hit, so the pair does not decline the bag.           *)
(* The joint is already a vertex, so it is not a progress hit.                *)
(* -------------------------------------------------------------------------- *)

Definition unit_win : Window := mkWindow 0 1.

Definition locked_ls_pc : BagPiece :=
  mkBagPiece (mkChicken 0%nat 1%nat (MkChord locked_cc_ls_egg))
    (SuppChord locked_cc_ls_egg) unit_win [].

Definition locked_cs_pc : BagPiece :=
  mkBagPiece (mkChicken 2%nat 3%nat (MkCirc locked_circ_A))
    (SuppCircle locked_circ_A) unit_win [].

Definition locked_cc_bag : SheetBag :=
  BagLive default_sheet [locked_ls_pc; locked_cs_pc].

Lemma locked_cc_cs_ls_host_hit :
  I_ok (MkCirc locked_circ_A) (MkChord locked_cc_ls_egg)
       (IHit locked_cc_joint_pt 0 1).
Proof.
  apply I_ok_circ_chord_hit_complete.
  - exact locked_cc_ls_cs_host_scope.
  - unfold on_circ. split; [lra|]. symmetry. exact locked_cc_cs_start.
  - unfold on_chord. split; [lra|].
    unfold locked_cc_joint_pt. symmetry. exact locked_cc_ls_end.
Qed.

Lemma locked_cc_orders_not_decline :
  ~ I_ok (ck_egg (bp_ck locked_ls_pc)) (ck_egg (bp_ck locked_cs_pc)) IDecline /\
  ~ I_ok (ck_egg (bp_ck locked_cs_pc)) (ck_egg (bp_ck locked_ls_pc)) IDecline.
Proof.
  unfold locked_ls_pc, locked_cs_pc. simpl.
  destruct (circ_chord_in_scope_not_decline _ _ locked_cc_ls_cs_host_scope)
    as [Hcs Hsc].
  split; [exact Hsc | exact Hcs].
Qed.

Lemma locked_joint_is_vertex :
  family_vertex [locked_ls_pc; locked_cs_pc]
    (bp_support locked_ls_pc) locked_cc_joint_pt /\
  family_vertex [locked_ls_pc; locked_cs_pc]
    (bp_support locked_cs_pc) locked_cc_joint_pt.
Proof.
  split.
  - exists locked_ls_pc. split; [left; reflexivity|].
    split; [reflexivity|].
    unfold piece_endpoint, locked_ls_pc. simpl.
    right. unfold locked_cc_joint_pt. symmetry. exact locked_cc_ls_end.
  - exists locked_cs_pc. split; [right; left; reflexivity|].
    split; [reflexivity|].
    unfold piece_endpoint, locked_cs_pc. simpl.
    left. symmetry. exact locked_cc_cs_start.
Qed.

Lemma locked_cc_joint_not_progress :
  ~ progress_hit [locked_ls_pc; locked_cs_pc] locked_ls_pc locked_cs_pc
      (IHit locked_cc_joint_pt 1 0).
Proof.
  intro H. apply H. exact locked_joint_is_vertex.
Qed.

Lemma two_piece_nth :
  forall (a b x y : BagPiece) (i j : nat),
    nth_error [a; b] i = Some x ->
    nth_error [a; b] j = Some y ->
    i <> j ->
    (x = a /\ y = b) \/ (x = b /\ y = a).
Proof.
  intros a b x y i j Hi Hj Hne.
  destruct i as [| [| ?]]; destruct j as [| [| ?]];
    simpl in Hi, Hj; try discriminate.
  - congruence.
  - inversion Hi; inversion Hj; subst. left. split; reflexivity.
  - inversion Hi; inversion Hj; subst. right. split; reflexivity.
  - congruence.
Qed.

Lemma bag_decline_live_inv :
  forall sh pcs sh',
    bag_decline_step (BagLive sh pcs) (BagDeclined sh') ->
    exists i j a b,
      nth_error pcs i = Some a /\
      nth_error pcs j = Some b /\
      i <> j /\
      I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) IDecline.
Proof.
  intros sh pcs sh' step.
  inversion step; subst; try discriminate.
  exists i, j, a, b. repeat split; assumption.
Qed.

Lemma locked_cc_no_decline_step :
  ~ bag_decline_step locked_cc_bag (BagDeclined default_sheet).
Proof.
  intros step.
  destruct (bag_decline_live_inv _ _ _ step)
    as [i [j [a [b [Hi [Hj [Hne Hok]]]]]]].
  destruct (two_piece_nth _ _ _ _ _ _ Hi Hj Hne) as [[-> ->]|[-> ->]].
  - destruct locked_cc_orders_not_decline as [Hab _]. exact (Hab Hok).
  - destruct locked_cc_orders_not_decline as [_ Hba]. exact (Hba Hok).
Qed.

(* -------------------------------------------------------------------------- *)
(* Interior hit of the locked quarter. Progress keeps same_support.           *)
(* -------------------------------------------------------------------------- *)

Lemma window_circ_unit : forall c, window_circ c unit_win = c.
Proof.
  intros [o r th sw].
  unfold window_circ, unit_win. cbn.
  replace (th + 0 * sw) with th by ring.
  replace ((1 - 0) * sw) with sw by ring.
  reflexivity.
Qed.

Lemma window_chord_unit : forall s, window_chord s unit_win = s.
Proof.
  intros [p0 p1].
  unfold window_chord, chord_eval, unit_win. cbn.
  apply (f_equal2 mkChordEgg); apply (f_equal2 mkPoint); ring.
Qed.

Lemma f1_egg_is_locked_quarter : F1_egg = locked_circ_A.
Proof. reflexivity. Qed.

Definition f1_hit_pt : Point :=
  zeta_pt (circ_o F1_egg) (egg_pole F1_egg) 0.
Definition f1_ti : R := t_of_zeta F1_egg 0.
Definition f1_tj : R := egg_tj F1_egg F1_chord 0.

Definition f1_circ_pc : BagPiece :=
  mkBagPiece (mkChicken 0%nat 1%nat (MkCirc F1_egg))
    (SuppCircle F1_egg) unit_win [].

Definition f1_chord_pc : BagPiece :=
  mkBagPiece (mkChicken 2%nat 3%nat (MkChord F1_chord))
    (SuppChord F1_chord) unit_win [].

Lemma f1_host_scope : circ_chord_host_scope F1_egg F1_chord.
Proof.
  split.
  - unfold circ_open_span, F1_egg. cbn.
    pose proof PI_RGT_0 as Hpi. lra.
  - unfold chord_nondeg, chord_dx, chord_dy, F1_chord. cbn.
    intro Heq. apply (f_equal fst) in Heq. cbn in Heq. lra.
Qed.

Lemma f1_circ_wf : piece_wf f1_circ_pc.
Proof.
  unfold piece_wf, piece_realizes, f1_circ_pc. cbn.
  split; [| unfold window_ordered, unit_win; cbn; lra].
  symmetry. apply window_circ_unit.
Qed.

Lemma f1_chord_wf : piece_wf f1_chord_pc.
Proof.
  unfold piece_wf, piece_realizes, f1_chord_pc. cbn.
  split; [| unfold window_ordered, unit_win; cbn; lra].
  symmetry. apply window_chord_unit.
Qed.

Lemma f1_hit_pt_mid : f1_hit_pt = circ_eval F1_egg (/ 2).
Proof.
  destruct F1_hit as [[_ Hp] _].
  rewrite t_of_zeta_mid in Hp.
  unfold f1_hit_pt. symmetry. exact Hp.
Qed.

Lemma f1_mid_coords :
  circ_eval F1_egg (/ 2) =
  mkPoint (5 * (sqrt 2 / 2)) (5 * (sqrt 2 / 2)).
Proof.
  unfold circ_eval, F1_egg. cbn.
  replace (0 + / 2 * (PI / 2)) with (PI / 4) by field.
  rewrite cos_PI4, sin_PI4.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma f1_mid_not_ends :
  circ_eval F1_egg (/ 2) <> circ_eval F1_egg 0 /\
  circ_eval F1_egg (/ 2) <> circ_eval F1_egg 1.
Proof.
  rewrite f1_mid_coords, f1_egg_is_locked_quarter.
  rewrite locked_circ_A_at_0, locked_circ_A_at_1.
  pose proof (sqrt_lt_R0 2 ltac:(lra)) as Hq.
  assert (Hpos : 0 < 5 * (sqrt 2 / 2)).
  { apply Rmult_lt_0_compat; [lra|].
    apply Rdiv_lt_0_compat; [exact Hq | lra]. }
  split.
  - intro H. apply (f_equal py) in H. cbn in H. lra.
  - intro H. apply (f_equal px) in H. cbn in H. lra.
Qed.

Lemma f1_not_circ_vertex :
  ~ family_vertex [f1_circ_pc; f1_chord_pc] (SuppCircle F1_egg) f1_hit_pt.
Proof.
  intros [pc [Hin [Hs Hep]]].
  destruct Hin as [Heq|[Heq|[]]].
  - subst pc. unfold piece_endpoint, f1_circ_pc in Hep. simpl in Hep.
    destruct Hep as [Hep|Hep].
    + apply (proj1 f1_mid_not_ends). rewrite <- f1_hit_pt_mid. exact Hep.
    + apply (proj2 f1_mid_not_ends). rewrite <- f1_hit_pt_mid. exact Hep.
  - subst pc. discriminate Hs.
Qed.

Lemma f1_I_ok :
  I_ok (MkCirc F1_egg) (MkChord F1_chord) (IHit f1_hit_pt f1_ti f1_tj).
Proof.
  apply I_ok_circ_chord_hit_complete.
  - exact f1_host_scope.
  - exact (proj1 F1_hit).
  - exact (proj2 F1_hit).
Qed.

Lemma f1_progress_hit :
  progress_hit [f1_circ_pc; f1_chord_pc] f1_circ_pc f1_chord_pc
    (IHit f1_hit_pt f1_ti f1_tj).
Proof.
  unfold progress_hit. intro Hboth. destruct Hboth as [Hv _].
  exact (f1_not_circ_vertex Hv).
Qed.

Theorem locked_quarter_interior_progress :
  F1_egg = locked_circ_A /\
  bag_progress_step
    (BagLive default_sheet [f1_circ_pc; f1_chord_pc])
    (BagLive default_sheet
       (progress_pieces [f1_circ_pc; f1_chord_pc] 0%nat 1%nat
          f1_circ_pc f1_chord_pc f1_ti f1_tj 4%nat)) /\
  same_support (bp_support (fst (split_piece f1_circ_pc f1_ti 4%nat)))
    (bp_support f1_circ_pc) /\
  same_support (bp_support (snd (split_piece f1_circ_pc f1_ti 4%nat)))
    (bp_support f1_circ_pc) /\
  same_support (bp_support (fst (split_piece f1_chord_pc f1_tj 4%nat)))
    (bp_support f1_chord_pc) /\
  same_support (bp_support (snd (split_piece f1_chord_pc f1_tj 4%nat)))
    (bp_support f1_chord_pc).
Proof.
  split; [exact f1_egg_is_locked_quarter|].
  split.
  - eapply StepProgress.
    + reflexivity.
    + reflexivity.
    + discriminate.
    + exact f1_circ_wf.
    + exact f1_chord_wf.
    + exact f1_I_ok.
    + exact f1_progress_hit.
  - destruct (split_preserves_same_support f1_circ_pc f1_ti 4%nat) as [Hs1 Hs2].
    destruct (split_preserves_same_support f1_chord_pc f1_tj 4%nat) as [Ht1 Ht2].
    repeat split; assumption.
Qed.

(* WITNESS {"claimId":"0007-host-circ-chord-oracle","topic":"overlay","lemma":"ticket_0007_host_circ_chord_oracle_qed_or_qex","title":"host circ times chord oracle: in-scope I_ok Hit is on both curves and every in-scope incidence is a Hit, locked CC LS+CS does not decline the bag, interior quarter hit progresses with same_support (QED) or first_cook_scope gains the mixed arms (QEX); discharged QED; full-span and degenerate chord Decline; circ times circ Decline is False; not a chord demote","file":"theories/HostCircChordOracle.v","witness":"0007-host-circ-chord-oracle","board":"ADR-0007"} *)

Theorem ticket_0007_host_circ_chord_oracle_qed_or_qex :
  ((forall c s p ti tj,
      I_ok (MkCirc c) (MkChord s) (IHit p ti tj) ->
      on_circ c ti p /\ on_chord s tj p) /\
   (forall s c p ti tj,
      I_ok (MkChord s) (MkCirc c) (IHit p ti tj) ->
      on_chord s ti p /\ on_circ c tj p) /\
   (forall c s p ti tj,
      circ_chord_host_scope c s ->
      on_circ c ti p -> on_chord s tj p ->
      I_ok (MkCirc c) (MkChord s) (IHit p ti tj)) /\
   (forall s c p ti tj,
      circ_chord_host_scope c s ->
      on_chord s ti p -> on_circ c tj p ->
      I_ok (MkChord s) (MkCirc c) (IHit p ti tj)) /\
   I_ok (MkChord locked_cc_ls_egg) (MkCirc locked_circ_A)
     (IHit locked_cc_joint_pt 1 0) /\
   I_ok (MkCirc locked_circ_A) (MkChord locked_cc_ls_egg)
     (IHit locked_cc_joint_pt 0 1) /\
   ~ bag_decline_step locked_cc_bag (BagDeclined default_sheet) /\
   (F1_egg = locked_circ_A /\
    bag_progress_step
      (BagLive default_sheet [f1_circ_pc; f1_chord_pc])
      (BagLive default_sheet
         (progress_pieces [f1_circ_pc; f1_chord_pc] 0%nat 1%nat
            f1_circ_pc f1_chord_pc f1_ti f1_tj 4%nat))) /\
   (forall s, I_ok (MkCirc locked_full_circle_egg) (MkChord s) IDecline) /\
   (forall c, I_ok (MkCirc c) (MkChord degen_chord) IDecline) /\
   (forall c1 c2, ~ I_ok (MkCirc c1) (MkCirc c2) IDecline) /\
   ~ first_cook_scope EggChord EggCircularArc /\
   ~ first_cook_scope EggCircularArc EggChord)
  \/
  (first_cook_scope EggChord EggCircularArc /\
   first_cook_scope EggCircularArc EggChord).
Proof.
  left.
  split; [exact I_ok_circ_chord_hit_sound|].
  split; [exact I_ok_chord_circ_hit_sound|].
  split; [exact I_ok_circ_chord_hit_complete|].
  split; [exact I_ok_chord_circ_hit_complete|].
  split; [exact locked_cc_ls_cs_host_hit|].
  split; [exact locked_cc_cs_ls_host_hit|].
  split; [exact locked_cc_no_decline_step|].
  split.
  - split; [exact (proj1 locked_quarter_interior_progress)|].
    exact (proj1 (proj2 locked_quarter_interior_progress)).
  - split; [exact full_span_circ_chord_decline|].
    split; [exact degen_circ_chord_decline|].
    split; [exact circ_circ_not_decline|].
    exact mixed_not_first_cook.
Qed.

Print Assumptions I_ok_circ_chord_hit_sound.
Print Assumptions I_ok_chord_circ_hit_sound.
Print Assumptions I_ok_circ_chord_hit_complete.
Print Assumptions I_ok_chord_circ_hit_complete.
Print Assumptions I_ok_circ_chord_no_miss.
Print Assumptions I_ok_chord_circ_no_miss.
Print Assumptions I_ok_circ_chord_empty_sound.
Print Assumptions I_ok_chord_circ_empty_sound.
Print Assumptions circ_chord_in_scope_not_decline.
Print Assumptions zeta_seg_hit_I_ok.
Print Assumptions full_span_not_open.
Print Assumptions full_span_circ_chord_decline.
Print Assumptions full_span_chord_circ_decline.
Print Assumptions full_span_hit_false.
Print Assumptions degen_not_nondeg.
Print Assumptions degen_circ_chord_decline.
Print Assumptions degen_chord_circ_decline.
Print Assumptions degen_hit_false.
Print Assumptions circ_circ_not_decline.
Print Assumptions mixed_not_first_cook.
Print Assumptions locked_cc_cs_ls_host_hit.
Print Assumptions locked_cc_orders_not_decline.
Print Assumptions locked_joint_is_vertex.
Print Assumptions locked_cc_joint_not_progress.
Print Assumptions two_piece_nth.
Print Assumptions bag_decline_live_inv.
Print Assumptions locked_cc_no_decline_step.
Print Assumptions window_circ_unit.
Print Assumptions window_chord_unit.
Print Assumptions f1_egg_is_locked_quarter.
Print Assumptions f1_host_scope.
Print Assumptions f1_circ_wf.
Print Assumptions f1_chord_wf.
Print Assumptions f1_hit_pt_mid.
Print Assumptions f1_mid_coords.
Print Assumptions f1_mid_not_ends.
Print Assumptions f1_not_circ_vertex.
Print Assumptions f1_I_ok.
Print Assumptions f1_progress_hit.
Print Assumptions locked_quarter_interior_progress.
Print Assumptions ticket_0007_host_circ_chord_oracle_qed_or_qex.
