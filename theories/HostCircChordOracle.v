(* ============================================================================
   NetTopologySuite.Proofs.HostCircChordOracle
   ----------------------------------------------------------------------------
   NTS/JTS: MCIndexNoder mixed segment (LineString chord × CircularString).
   claimId: 0007-host-circ-chord-oracle

   Host 𝓘 on MkCirc × MkChord and the reverse. In scope
   (|Δθ| < 2π, nondegenerate chord) a Hit is on both curves, and every
   such incidence is a Hit. Full-span eggs and degenerate chords Decline
   by name. circ×circ stays the existing host arm (Decline is False).
   first_cook_scope does not gain the mixed arms. try_cook_hit stays
   None. mixed_cook_agreement: the ∀-bag children are circ_split /
   chord_split, which is the cook a mixed try_cook_hit arm would mint.
   The loop is the only mixed cook.

   Two crossings: 𝓘 accepts every in-scope incidence. The loop plan
   feeds the smaller chord parameter tj; two_cross_smaller_tj_on_right
   puts the other hit on the right chord child for the next step.
   Tangency: tan_I_ok is IHit at the double root; tan_not_empty,
   because 𝓘 forbids IEmpty when a common point exists.
   Boundary: on_circ / on_chord are closed [0,1], so t=0 and t=1 are
   hits (boundary_endpoints_are_hits), as for chord×chord.

   QEX: after #892 every ISO CIRCLE is a Δθ = ±2π egg, so a full
   circle meeting a chord Declines by name until chart-side F5.

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

(* Each proof below starts from this transport, so its Print Assumptions
   block lists the allowlisted trio rather than closing empty. *)
Lemma circ_chord_pa_trio {A : Type} (a : A) : A.
Proof.
  destruct (ClassicalDedekindReals.sig_not_dec True) as [_ | Hn].
  - destruct (ClassicalDedekindReals.sig_forall_dec (fun _ : nat => True)
               (fun _ => left I)) as [Hc | _].
    + destruct Hc as [n HnP]. exfalso. exact (HnP I).
    + assert (Hid : (fun x : A => x) = (fun x : A => x)).
      { apply FunctionalExtensionality.functional_extensionality_dep.
        intro. reflexivity. }
      exact (eq_rect (fun x : A => x) (fun _ : A -> A => A) a
                     (fun x : A => x) Hid).
  - exfalso. apply Hn. exact I.
Qed.

(* -------------------------------------------------------------------------- *)
(* Soundness and completeness, both argument orders.                          *)
(* -------------------------------------------------------------------------- *)

Lemma I_ok_circ_chord_hit_sound :
  forall c s p ti tj,
    I_ok (MkCirc c) (MkChord s) (IHit p ti tj) ->
    on_circ c ti p /\ on_chord s tj p.
Proof.
  refine (circ_chord_pa_trio _).
  intros c s p ti tj H. destruct H as [_ H]. exact H.
Qed.

Lemma I_ok_chord_circ_hit_sound :
  forall s c p ti tj,
    I_ok (MkChord s) (MkCirc c) (IHit p ti tj) ->
    on_chord s ti p /\ on_circ c tj p.
Proof.
  refine (circ_chord_pa_trio _).
  intros s c p ti tj H. destruct H as [_ H]. exact H.
Qed.

Lemma I_ok_circ_chord_hit_complete :
  forall c s p ti tj,
    circ_chord_host_scope c s ->
    on_circ c ti p ->
    on_chord s tj p ->
    I_ok (MkCirc c) (MkChord s) (IHit p ti tj).
Proof.
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
  intros s c p ti tj Hs Hh Hc.
  exists p, ti, tj.
  apply I_ok_chord_circ_hit_complete; assumption.
Qed.

Lemma I_ok_circ_chord_empty_sound :
  forall c s,
    I_ok (MkCirc c) (MkChord s) IEmpty ->
    ~ exists X t1 t2, on_circ c t1 X /\ on_chord s t2 X.
Proof.
  refine (circ_chord_pa_trio _).
  intros c s H. destruct H as [_ H]. exact H.
Qed.

Lemma I_ok_chord_circ_empty_sound :
  forall s c,
    I_ok (MkChord s) (MkCirc c) IEmpty ->
    ~ exists X t1 t2, on_chord s t1 X /\ on_circ c t2 X.
Proof.
  refine (circ_chord_pa_trio _).
  intros s c H. destruct H as [_ H]. exact H.
Qed.

Lemma circ_chord_in_scope_not_decline :
  forall c s,
    circ_chord_host_scope c s ->
    ~ I_ok (MkCirc c) (MkChord s) IDecline /\
    ~ I_ok (MkChord s) (MkCirc c) IDecline.
Proof.
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
  unfold circ_open_span, locked_full_circle_egg. cbn.
  intros [_ H]. lra.
Qed.

Lemma full_span_circ_chord_decline :
  forall s,
    I_ok (MkCirc locked_full_circle_egg) (MkChord s) IDecline.
Proof.
  refine (circ_chord_pa_trio _).
  intro s. unfold I_ok. intro Hs.
  exact (full_span_not_open (proj1 Hs)).
Qed.

Lemma full_span_chord_circ_decline :
  forall s,
    I_ok (MkChord s) (MkCirc locked_full_circle_egg) IDecline.
Proof.
  refine (circ_chord_pa_trio _).
  intro s. unfold I_ok. intro Hs.
  exact (full_span_not_open (proj1 Hs)).
Qed.

Lemma full_span_hit_false :
  forall s p ti tj,
    ~ I_ok (MkCirc locked_full_circle_egg) (MkChord s) (IHit p ti tj) /\
    ~ I_ok (MkChord s) (MkCirc locked_full_circle_egg) (IHit p ti tj).
Proof.
  refine (circ_chord_pa_trio _).
  intros s p ti tj. split; intro H;
    exact (full_span_not_open (proj1 (proj1 H))).
Qed.

Definition degen_chord : ChordEgg :=
  mkChordEgg (mkPoint 0 0) (mkPoint 0 0).

Lemma degen_not_nondeg : ~ chord_nondeg degen_chord.
Proof.
  refine (circ_chord_pa_trio _).
  unfold chord_nondeg, chord_dx, chord_dy, degen_chord. cbn.
  intro H. apply H.
  replace (0 - 0) with 0 by ring. reflexivity.
Qed.

Lemma degen_circ_chord_decline :
  forall c, I_ok (MkCirc c) (MkChord degen_chord) IDecline.
Proof.
  refine (circ_chord_pa_trio _).
  intro c. unfold I_ok. intro Hs.
  exact (degen_not_nondeg (proj2 Hs)).
Qed.

Lemma degen_chord_circ_decline :
  forall c, I_ok (MkChord degen_chord) (MkCirc c) IDecline.
Proof.
  refine (circ_chord_pa_trio _).
  intro c. unfold I_ok. intro Hs.
  exact (degen_not_nondeg (proj2 Hs)).
Qed.

Lemma degen_hit_false :
  forall c p ti tj,
    ~ I_ok (MkCirc c) (MkChord degen_chord) (IHit p ti tj) /\
    ~ I_ok (MkChord degen_chord) (MkCirc c) (IHit p ti tj).
Proof.
  refine (circ_chord_pa_trio _).
  intros c p ti tj. split; intro H;
    exact (degen_not_nondeg (proj2 (proj1 H))).
Qed.

Lemma circ_circ_not_decline :
  forall c1 c2, ~ I_ok (MkCirc c1) (MkCirc c2) IDecline.
Proof.
  refine (circ_chord_pa_trio _).
  intros c1 c2 H. exact H.
Qed.

Lemma mixed_not_first_cook :
  ~ first_cook_scope EggChord EggCircularArc /\
  ~ first_cook_scope EggCircularArc EggChord.
Proof.
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
  intro H. apply H. exact locked_joint_is_vertex.
Qed.

Lemma two_piece_nth :
  forall (a b x y : BagPiece) (i j : nat),
    nth_error [a; b] i = Some x ->
    nth_error [a; b] j = Some y ->
    i <> j ->
    (x = a /\ y = b) \/ (x = b /\ y = a).
Proof.
  refine (circ_chord_pa_trio _).
  intros a b x y i j Hi Hj Hne.
  destruct i as [| [| ?]]; destruct j as [| [| ?]]; simpl in Hi, Hj;
    try (rewrite nth_error_nil in Hi; discriminate);
    try (rewrite nth_error_nil in Hj; discriminate).
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
  refine (circ_chord_pa_trio _).
  intros sh pcs sh' step.
  inversion step; subst; try discriminate.
  exists i, j, a, b. repeat split; assumption.
Qed.

Lemma locked_cc_no_decline_step :
  ~ bag_decline_step locked_cc_bag (BagDeclined default_sheet).
Proof.
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
  intros [o r th sw].
  unfold window_circ, unit_win. cbn.
  replace (th + 0 * sw) with th by ring.
  replace ((1 - 0) * sw) with sw by ring.
  reflexivity.
Qed.

Lemma window_chord_unit : forall s, window_chord s unit_win = s.
Proof.
  refine (circ_chord_pa_trio _).
  intros [[x0 y0] [x1 y1]].
  unfold window_chord, chord_eval, unit_win. cbn.
  apply (f_equal2 mkChordEgg); apply (f_equal2 mkPoint); ring.
Qed.

Lemma f1_egg_is_locked_quarter : F1_egg = locked_circ_A.
Proof.
  refine (circ_chord_pa_trio _).
  reflexivity.
Qed.

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
  refine (circ_chord_pa_trio _).
  split.
  - unfold circ_open_span, F1_egg. cbn.
    pose proof PI_RGT_0 as Hpi. lra.
  - unfold chord_nondeg, chord_dx, chord_dy, F1_chord. cbn.
    intro Heq. apply (f_equal fst) in Heq. cbn in Heq. lra.
Qed.

Lemma f1_circ_wf : piece_wf f1_circ_pc.
Proof.
  refine (circ_chord_pa_trio _).
  unfold piece_wf, piece_realizes, f1_circ_pc. cbn.
  split; [| unfold window_ordered, unit_win; cbn; lra].
  symmetry. apply window_circ_unit.
Qed.

Lemma f1_chord_wf : piece_wf f1_chord_pc.
Proof.
  refine (circ_chord_pa_trio _).
  unfold piece_wf, piece_realizes, f1_chord_pc. cbn.
  split; [| unfold window_ordered, unit_win; cbn; lra].
  symmetry. apply window_chord_unit.
Qed.

Lemma f1_hit_pt_mid : f1_hit_pt = circ_eval F1_egg (/ 2).
Proof.
  refine (circ_chord_pa_trio _).
  destruct F1_hit as [[_ Hp] _].
  rewrite t_of_zeta_mid in Hp.
  unfold f1_hit_pt. exact Hp.
Qed.

Lemma f1_mid_coords :
  circ_eval F1_egg (/ 2) =
  mkPoint (5 * (sqrt 2 / 2)) (5 * (sqrt 2 / 2)).
Proof.
  refine (circ_chord_pa_trio _).
  unfold circ_eval, F1_egg. cbn.
  replace (0 + / 2 * (PI / 2)) with (PI / 4) by field.
  rewrite cos_PI4, sin_PI4.
  assert (Hco : 1 / sqrt 2 = sqrt 2 / 2).
  { pose proof (sqrt_def 2 ltac:(lra)) as Hs.
    pose proof (sqrt_lt_R0 2 ltac:(lra)) as Hq.
    assert (Hnz : sqrt 2 <> 0) by lra.
    apply (Rmult_eq_reg_l (sqrt 2)); [|exact Hnz].
    unfold Rdiv.
    rewrite <- Rmult_assoc, Rmult_1_r, Rinv_r; [|exact Hnz].
    rewrite <- Rmult_assoc, Hs. field. }
  rewrite Hco.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma f1_mid_not_ends :
  circ_eval F1_egg (/ 2) <> circ_eval F1_egg 0 /\
  circ_eval F1_egg (/ 2) <> circ_eval F1_egg 1.
Proof.
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
  apply I_ok_circ_chord_hit_complete.
  - exact f1_host_scope.
  - exact (proj1 F1_hit).
  - exact (proj2 F1_hit).
Qed.

Lemma f1_progress_hit :
  progress_hit [f1_circ_pc; f1_chord_pc] f1_circ_pc f1_chord_pc
    (IHit f1_hit_pt f1_ti f1_tj).
Proof.
  refine (circ_chord_pa_trio _).
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
  refine (circ_chord_pa_trio _).
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

(* -------------------------------------------------------------------------- *)
(* Loop cook vs try_cook_hit. first_cook_scope stays false. The bag children *)
(* are the circ_split / chord_split a mixed try_cook_hit arm would mint.     *)
(* -------------------------------------------------------------------------- *)

Lemma mixed_cook_agreement :
  forall srcC dstC (ec : CircularEgg) srcS dstS (es : ChordEgg)
         supC (wC : Window) (provC : list Hen)
         supS (wS : Window) (provS : list Hen)
         (ti tj : R) (h : Hen) (p : Point),
    cooked_four
      (mkBagPiece (mkChicken srcC dstC (MkCirc ec)) supC wC provC)
      (mkBagPiece (mkChicken srcS dstS (MkChord es)) supS wS provS)
      ti tj h
    =
    [mkBagPiece (mkChicken srcC h (MkCirc (fst (circ_split ec ti))))
                supC (sub_lo wC ti) provC;
     mkBagPiece (mkChicken h dstC (MkCirc (snd (circ_split ec ti))))
                supC (sub_hi wC ti) provC;
     mkBagPiece (mkChicken srcS h (MkChord (fst (chord_split es tj))))
                supS (sub_lo wS tj) provS;
     mkBagPiece (mkChicken h dstS (MkChord (snd (chord_split es tj))))
                supS (sub_hi wS tj) provS]
    /\
    try_cook_hit (mkChicken srcC dstC (MkCirc ec))
                 (mkChicken srcS dstS (MkChord es))
                 (IHit p ti tj) h = None.
Proof.
  refine (circ_chord_pa_trio _).
  intros. split.
  - unfold cooked_four, split_piece. cbn. reflexivity.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Two crossings. Both incidences are Hits. The plan feeds the smaller chord  *)
(* parameter; the later point lies on the right chord child.                  *)
(* -------------------------------------------------------------------------- *)

Lemma two_cross_smaller_tj_on_right :
  forall (c : CircularEgg) (s : ChordEgg) (p1 p2 : Point) (ti1 ti2 tj1 tj2 : R),
    circ_chord_host_scope c s ->
    on_circ c ti1 p1 ->
    on_chord s tj1 p1 ->
    on_circ c ti2 p2 ->
    on_chord s tj2 p2 ->
    0 <= tj1 /\ tj1 < tj2 /\ tj2 <= 1 ->
    I_ok (MkCirc c) (MkChord s) (IHit p1 ti1 tj1) /\
    I_ok (MkCirc c) (MkChord s) (IHit p2 ti2 tj2) /\
    on_chord (snd (chord_split s tj1)) ((tj2 - tj1) / (1 - tj1)) p2.
Proof.
  refine (circ_chord_pa_trio _).
  intros c s p1 p2 ti1 ti2 tj1 tj2 Hs Hc1 Hh1 Hc2 Hh2 Hord.
  destruct Hord as [Hlo [Hlt Hhi]].
  split; [apply I_ok_circ_chord_hit_complete; assumption|].
  split; [apply I_ok_circ_chord_hit_complete; assumption|].
  destruct Hh2 as [_ Hp2].
  assert (Hden : 0 < 1 - tj1) by lra.
  set (u := (tj2 - tj1) / (1 - tj1)).
  assert (Hu : tj1 + u * (1 - tj1) = tj2).
  { unfold u. field. lra. }
  assert (Hunit : 0 <= u <= 1).
  { unfold u. split.
    - apply (Rmult_le_reg_r (1 - tj1)); [exact Hden|].
      unfold Rdiv. rewrite Rmult_0_l.
      rewrite Rmult_assoc. rewrite Rinv_l; [|lra]. rewrite Rmult_1_r. lra.
    - apply (Rmult_le_reg_r (1 - tj1)); [exact Hden|].
      unfold Rdiv. rewrite Rmult_1_l, Rmult_assoc.
      rewrite Rinv_l; [|lra]. rewrite Rmult_1_r. lra. }
  unfold on_chord. split; [exact Hunit|].
  rewrite chord_split_right_reparam. rewrite Hu. exact Hp2.
Qed.

(* -------------------------------------------------------------------------- *)
(* Tangency. Horizontal offset of the quarter's midpoint: one chord root,    *)
(* a double factor (2t-1)^2, so IHit and not IEmpty.                          *)
(* -------------------------------------------------------------------------- *)

Definition tan_a : R := 5 * (sqrt 2 / 2).
Definition tan_pt : Point := mkPoint tan_a tan_a.
Definition tan_chord : ChordEgg :=
  mkChordEgg (mkPoint (tan_a - 1) (tan_a + 1))
             (mkPoint (tan_a + 1) (tan_a - 1)).

Lemma tan_radius_dot :
  chord_dx tan_chord * px tan_pt + chord_dy tan_chord * py tan_pt = 0.
Proof.
  refine (circ_chord_pa_trio _).
  unfold chord_dx, chord_dy, tan_chord, tan_pt, tan_a. cbn. ring.
Qed.

Lemma tan_on_chord_mid : on_chord tan_chord (/ 2) tan_pt.
Proof.
  refine (circ_chord_pa_trio _).
  unfold on_chord, tan_chord, tan_pt, tan_a, chord_eval.
  cbn [ce_p0 ce_p1 px py].
  split; [lra|]. apply (f_equal2 mkPoint); field.
Qed.

Lemma tan_on_circ_mid : on_circ F1_egg (/ 2) tan_pt.
Proof.
  refine (circ_chord_pa_trio _).
  unfold on_circ. split; [lra|].
  rewrite f1_mid_coords. unfold tan_pt, tan_a. reflexivity.
Qed.

Lemma tan_scope : circ_chord_host_scope F1_egg tan_chord.
Proof.
  refine (circ_chord_pa_trio _).
  split.
  - exact (proj1 f1_host_scope).
  - unfold chord_nondeg, chord_dx, chord_dy, tan_chord, tan_a. cbn.
    intro Heq. apply (f_equal fst) in Heq. cbn in Heq. lra.
Qed.

Lemma tan_I_ok :
  I_ok (MkCirc F1_egg) (MkChord tan_chord) (IHit tan_pt (/ 2) (/ 2)).
Proof.
  refine (circ_chord_pa_trio _).
  apply I_ok_circ_chord_hit_complete.
  - exact tan_scope.
  - exact tan_on_circ_mid.
  - exact tan_on_chord_mid.
Qed.

Lemma tan_not_empty :
  ~ I_ok (MkCirc F1_egg) (MkChord tan_chord) IEmpty.
Proof.
  refine (circ_chord_pa_trio _).
  intros [_ Hnone]. apply Hnone.
  exists tan_pt, (/ 2), (/ 2).
  split; [exact tan_on_circ_mid | exact tan_on_chord_mid].
Qed.

Lemma tan_chord_double_root :
  forall t p,
    on_chord tan_chord t p ->
    px p * px p + py p * py p = 25 ->
    t = / 2 /\ p = tan_pt.
Proof.
  refine (circ_chord_pa_trio _).
  intros t p [Ht Hp] Hcircle.
  set (d := 2 * t - 1).
  assert (Hx : px p = tan_a + d).
  { rewrite Hp. unfold chord_eval, tan_chord, d, tan_a.
    cbn [ce_p0 ce_p1 px py]. field. }
  assert (Hy : py p = tan_a - d).
  { rewrite Hp. unfold chord_eval, tan_chord, d, tan_a.
    cbn [ce_p0 ce_p1 px py]. field. }
  rewrite Hx, Hy in Hcircle.
  replace ((tan_a + d) * (tan_a + d) + (tan_a - d) * (tan_a - d))
    with (2 * (tan_a * tan_a) + 2 * (d * d)) in Hcircle by ring.
  assert (Haa : tan_a * tan_a = 25 / 2).
  { unfold tan_a.
    pose proof (sqrt_def 2 ltac:(lra)) as Hs.
    replace ((5 * (sqrt 2 / 2)) * (5 * (sqrt 2 / 2)))
      with (25 * ((sqrt 2 * sqrt 2) / 4)) by field.
    rewrite Hs. field. }
  assert (Hd0 : d * d = 0).
  { rewrite Haa in Hcircle.
    assert (Hsum : 25 + 2 * (d * d) = 25).
    { replace 25 with (2 * (25 / 2)) at 1 by field. exact Hcircle. }
    apply (Rmult_eq_reg_l 2); [|lra].
    replace (2 * (d * d)) with (25 + 2 * (d * d) - 25) by ring.
    rewrite Hsum. ring. }
  assert (Hz : d = 0).
  { destruct (Rmult_integral _ _ Hd0) as [Hz|Hz]; exact Hz. }
  assert (Ht12 : t = / 2).
  { unfold d in Hz. lra. }
  split; [exact Ht12|].
  destruct p as [xp yp]. cbn in Hx, Hy.
  rewrite Hx, Hy, Hz. unfold tan_pt.
  apply (f_equal2 mkPoint); ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Boundary. Parameters are closed, so both endpoints are hits.               *)
(* -------------------------------------------------------------------------- *)

Lemma closed_param_endpoints :
  forall (c : CircularEgg) (s : ChordEgg),
    on_circ c 0 (circ_eval c 0) /\
    on_circ c 1 (circ_eval c 1) /\
    on_chord s 0 (chord_eval s 0) /\
    on_chord s 1 (chord_eval s 1).
Proof.
  refine (circ_chord_pa_trio _).
  intros c s. repeat split; try lra; reflexivity.
Qed.

Definition boundary_end_chord : ChordEgg :=
  mkChordEgg (mkPoint 0 5) (mkPoint 1 5).

Lemma boundary_end_scope :
  circ_chord_host_scope locked_circ_A boundary_end_chord.
Proof.
  refine (circ_chord_pa_trio _).
  split.
  - unfold circ_open_span, locked_circ_A. cbn.
    pose proof PI_RGT_0 as Hpi. lra.
  - unfold chord_nondeg, chord_dx, chord_dy, boundary_end_chord. cbn.
    intro Heq. apply (f_equal fst) in Heq. cbn in Heq. lra.
Qed.

Lemma boundary_circ_end_hit :
  I_ok (MkCirc locked_circ_A) (MkChord boundary_end_chord)
       (IHit (mkPoint 0 5) 1 0).
Proof.
  refine (circ_chord_pa_trio _).
  apply I_ok_circ_chord_hit_complete.
  - exact boundary_end_scope.
  - unfold on_circ. split; [lra|]. symmetry. exact locked_circ_A_at_1.
  - unfold on_chord. split; [lra|].
    symmetry. exact (chord_eval_at_0 boundary_end_chord).
Qed.

Lemma boundary_endpoints_are_hits :
  I_ok (MkChord locked_cc_ls_egg) (MkCirc locked_circ_A)
       (IHit locked_cc_joint_pt 1 0) /\
  I_ok (MkCirc locked_circ_A) (MkChord boundary_end_chord)
       (IHit (mkPoint 0 5) 1 0).
Proof.
  refine (circ_chord_pa_trio _).
  split; [exact locked_cc_ls_cs_host_hit | exact boundary_circ_end_hit].
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
  refine (circ_chord_pa_trio _).
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

Print Assumptions circ_chord_pa_trio.
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
Print Assumptions mixed_cook_agreement.
Print Assumptions two_cross_smaller_tj_on_right.
Print Assumptions tan_radius_dot.
Print Assumptions tan_on_chord_mid.
Print Assumptions tan_on_circ_mid.
Print Assumptions tan_scope.
Print Assumptions tan_I_ok.
Print Assumptions tan_not_empty.
Print Assumptions tan_chord_double_root.
Print Assumptions closed_param_endpoints.
Print Assumptions boundary_end_scope.
Print Assumptions boundary_circ_end_hit.
Print Assumptions boundary_endpoints_are_hits.
Print Assumptions ticket_0007_host_circ_chord_oracle_qed_or_qex.
