(* ============================================================================
   NetTopologySuite.Proofs.HostCookCircChord
   ----------------------------------------------------------------------------
   ADR-0007 host first-cook circ×chord cook step
   (claimId 0007-host-first-cook-circ-chord-qed).

   Shape C (#770 prototype): IHit carries (p, ti, tj); I_ok checks
   on_circ / on_chord; the cook splits at the carried parameters and
   computes nothing. ti is egg-data sweep fraction, not atan2.
   Locked fixture sweep is π/2, not ±2π (#771).

   try_cook_hit_mixed lives here (SheetHenCook.try_cook_hit stays the
   same-kind mint). Touch mints nothing. Two-hit is MintTwo. Decline
   is tags / off-sheet only. Sidecar I_ok_mixed is not reminted.

   WITNESS topic: overlay · claimId: 0007-host-first-cook-circ-chord-qed
   witness: 0007-host-first-cook-circ-chord-qed
   board: ADR-0007
   3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Rtrigo_calc Rtrigo_facts.
From NTS.Proofs Require Import Distance SheetHenCook CircularCookMkCirc.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Locked fixture: quarter-circle × line-x=y chord, one interior Hit.         *)
(*   Circ  A: O=(0,0) r=5 θ0=0 Δθ=π/2     γ: (5,0) → (0,5)                    *)
(*   Chord S: (5,5) → (0,0)                 line x = y                         *)
(*   Hit   P: (5√2/2, 5√2/2)               angle π/4 on A                      *)
(*   ti = 1/2      sweep fraction, egg data — not atan2 of P                    *)
(*   tj = 1 - √2/2 chord lerp                                                  *)
(* -------------------------------------------------------------------------- *)

Definition mixed_circ : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 0 (PI / 2).

Definition mixed_chord : ChordEgg :=
  mkChordEgg (mkPoint 5 5) (mkPoint 0 0).

Definition mixed_hit_pt : Point :=
  mkPoint (5 * sqrt 2 / 2) (5 * sqrt 2 / 2).

Definition mixed_ti : R := 1 / 2.
Definition mixed_tj : R := 1 - sqrt 2 / 2.

Lemma mixed_sqrt2_bound : 0 < sqrt 2 < 2.
Proof.
  split.
  - apply sqrt_lt_R0. lra.
  - assert (sqrt 2 * sqrt 2 < 2 * 2).
    { rewrite sqrt_sqrt; lra. }
    nra.
Qed.

Lemma mixed_sqrt2_neq_0 : sqrt 2 <> 0.
Proof.
  apply Rgt_not_eq. apply sqrt_lt_R0. lra.
Qed.

Lemma mixed_inv_sqrt2 : 1 / sqrt 2 = sqrt 2 / 2.
Proof.
  unfold Rdiv.
  apply (Rmult_eq_reg_r (sqrt 2)); [|exact mixed_sqrt2_neq_0].
  rewrite Rmult_assoc, (Rinv_l (sqrt 2) mixed_sqrt2_neq_0), Rmult_1_r.
  replace (sqrt 2 * / 2 * sqrt 2) with (sqrt 2 * sqrt 2 * / 2) by ring.
  rewrite (sqrt_sqrt 2 ltac:(lra)).
  field.
Qed.

Lemma mixed_ti_in_01 : 0 <= mixed_ti <= 1.
Proof. unfold mixed_ti. lra. Qed.

Lemma mixed_tj_in_01 : 0 <= mixed_tj <= 1.
Proof.
  unfold mixed_tj.
  pose proof mixed_sqrt2_bound. lra.
Qed.

Lemma mixed_circ_at_ti :
  circ_eval mixed_circ mixed_ti = mixed_hit_pt.
Proof.
  unfold circ_eval, mixed_circ, mixed_ti, mixed_hit_pt.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (0 + (1 / 2) * (PI / 2)) with (PI / 4) by (pose proof PI_RGT_0; field; lra).
  rewrite cos_PI4, sin_PI4, mixed_inv_sqrt2.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma mixed_chord_at_tj :
  chord_eval mixed_chord mixed_tj = mixed_hit_pt.
Proof.
  unfold chord_eval, mixed_chord, mixed_tj, mixed_hit_pt.
  cbn [px py ce_p0 ce_p1].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma mixed_on_circ : on_circ mixed_circ mixed_ti mixed_hit_pt.
Proof.
  unfold on_circ. split; [exact mixed_ti_in_01|].
  symmetry. exact mixed_circ_at_ti.
Qed.

Lemma mixed_on_chord : on_chord mixed_chord mixed_tj mixed_hit_pt.
Proof.
  unfold on_chord. split; [exact mixed_tj_in_01|].
  symmetry. exact mixed_chord_at_tj.
Qed.

Lemma mixed_sweep_not_full :
  circ_sweep mixed_circ <> 2 * PI /\ circ_sweep mixed_circ <> - (2 * PI).
Proof.
  unfold mixed_circ. cbn [circ_sweep].
  pose proof PI_RGT_0. split; lra.
Qed.

Lemma mixed_circ_chord_I_ok :
  I_ok (MkCirc mixed_circ) (MkChord mixed_chord)
       (IHit mixed_hit_pt mixed_ti mixed_tj).
Proof.
  unfold I_ok.
  split; [exact mixed_on_circ | exact mixed_on_chord].
Qed.

Lemma mixed_chord_circ_I_ok :
  I_ok (MkChord mixed_chord) (MkCirc mixed_circ)
       (IHit mixed_hit_pt mixed_tj mixed_ti).
Proof.
  unfold I_ok.
  split; [exact mixed_on_chord | exact mixed_on_circ].
Qed.

Lemma mixed_circ_chord_not_decline :
  ~ I_ok (MkCirc mixed_circ) (MkChord mixed_chord) IDecline.
Proof.
  intro H. exact H.
Qed.

Lemma mixed_chord_circ_not_decline :
  ~ I_ok (MkChord mixed_chord) (MkCirc mixed_circ) IDecline.
Proof.
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cook: split at the carried parameters. Nobody inverts γ.                   *)
(* -------------------------------------------------------------------------- *)

Definition cook_hit_circ_chord
  (ckc cks : Chicken) (c : CircularEgg) (s : ChordEgg) (ti tj : R) (h : Hen)
  : CookedPair :=
  let sc := circ_split c ti in
  let ss := chord_split s tj in
  mkCookedPair h
    (mkChicken (ck_src ckc) h (MkCirc (fst sc)))
    (mkChicken h (ck_dst ckc) (MkCirc (snd sc)))
    (mkChicken (ck_src cks) h (MkChord (fst ss)))
    (mkChicken h (ck_dst cks) (MkChord (snd ss))).

Definition try_cook_hit_mixed (c1 c2 : Chicken) (o : IResult) (h_new : Hen)
  : option CookedPair :=
  match ck_egg c1, ck_egg c2, o with
  | MkCirc c, MkChord s, IHit _ ti tj =>
      Some (cook_hit_circ_chord c1 c2 c s ti tj h_new)
  | MkChord s, MkCirc c, IHit _ tj ti =>
      Some (cook_hit_circ_chord c2 c1 c s ti tj h_new)
  | _, _, _ => None
  end.

Definition mixed_ck_circ : Chicken :=
  mkChicken 0%nat 1%nat (MkCirc mixed_circ).
Definition mixed_ck_chord : Chicken :=
  mkChicken 2%nat 3%nat (MkChord mixed_chord).
Definition mixed_hen : Hen := 4%nat.

Definition mixed_locked_hit : IResult :=
  IHit mixed_hit_pt mixed_ti mixed_tj.

Definition mixed_cooked : CookedPair :=
  cook_hit_circ_chord mixed_ck_circ mixed_ck_chord
    mixed_circ mixed_chord mixed_ti mixed_tj mixed_hen.

Lemma mixed_cooked_shares : cooked_shares_hen mixed_cooked.
Proof. repeat split; reflexivity. Qed.

Lemma mixed_try_cook_hit :
  try_cook_hit_mixed mixed_ck_circ mixed_ck_chord
    mixed_locked_hit mixed_hen = Some mixed_cooked.
Proof. reflexivity. Qed.

Lemma mixed_try_cook_hit_swap :
  try_cook_hit_mixed mixed_ck_chord mixed_ck_circ
    (IHit mixed_hit_pt mixed_tj mixed_ti) mixed_hen =
  Some (cook_hit_circ_chord mixed_ck_circ mixed_ck_chord
          mixed_circ mixed_chord mixed_ti mixed_tj mixed_hen).
Proof. reflexivity. Qed.

Lemma mixed_split_joins_at_hit :
  circ_eval (fst (circ_split mixed_circ mixed_ti)) 1 = mixed_hit_pt /\
  circ_eval (snd (circ_split mixed_circ mixed_ti)) 0 = mixed_hit_pt /\
  chord_eval (fst (chord_split mixed_chord mixed_tj)) 1 = mixed_hit_pt /\
  chord_eval (snd (chord_split mixed_chord mixed_tj)) 0 = mixed_hit_pt.
Proof.
  rewrite (proj1 (circ_split_join mixed_circ mixed_ti)).
  rewrite (proj2 (circ_split_join mixed_circ mixed_ti)).
  rewrite mixed_circ_at_ti.
  rewrite (chord_eval_at_1 (fst (chord_split mixed_chord mixed_tj))).
  rewrite (chord_eval_at_0 (snd (chord_split mixed_chord mixed_tj))).
  rewrite (proj1 (chord_split_join mixed_chord mixed_tj)).
  rewrite (proj2 (chord_split_join mixed_chord mixed_tj)).
  rewrite mixed_chord_at_tj.
  repeat split; reflexivity.
Qed.

(* Touch / Empty / Decline mint nothing. *)
Lemma mixed_try_cook_touch_none :
  forall c1 c2 h, try_cook_hit_mixed c1 c2 IEmpty h = None.
Proof.
  intros [s1 d1 e1] [s2 d2 e2] h.
  destruct e1, e2; reflexivity.
Qed.

Lemma mixed_try_cook_decline_none :
  forall c1 c2 h, try_cook_hit_mixed c1 c2 IDecline h = None.
Proof.
  intros [s1 d1 e1] [s2 d2 e2] h.
  destruct e1, e2; reflexivity.
Qed.

Lemma mixed_tag_still_decline :
  I_ok (MkChord hor_bot) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact chord_circular_decline_I_ok.
Qed.

Lemma mixed_tag_hit_false :
  forall p ti tj,
    ~ I_ok (MkChord hor_bot) (MkOutOfScope EggCircularArc) (IHit p ti tj).
Proof.
  exact chord_circular_hit_not_I_ok.
Qed.

(* CircGamma leftover: hor_bot × locked_circ_A is Empty, not Decline. *)
Lemma hor_bot_locked_circ_A_empty :
  I_ok (MkChord hor_bot) (MkCirc locked_circ_A) IEmpty.
Proof.
  exact mkcirc_mixed_empty.
Qed.

Lemma hor_bot_locked_circ_A_not_decline :
  ~ I_ok (MkChord hor_bot) (MkCirc locked_circ_A) IDecline.
Proof.
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* MintTwo: upper semicircle × horizontal chord, two constructed Hits.        *)
(*   Circ: O=(0,0) r=5 θ0=0 Δθ=π     (5,0) → (−5,0) via (0,5)                 *)
(*   Chord: (−5, 5/2) → (5, 5/2)                                              *)
(*   P+ = (5√3/2, 5/2) at ti=1/6; P− = (−5√3/2, 5/2) at ti=5/6                *)
(* -------------------------------------------------------------------------- *)

Definition mint_two_circ : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 0 PI.

Definition mint_two_chord : ChordEgg :=
  mkChordEgg (mkPoint (-5) (5 / 2)) (mkPoint 5 (5 / 2)).

Definition mint_two_p_plus : Point :=
  mkPoint (5 * sqrt 3 / 2) (5 / 2).

Definition mint_two_p_minus : Point :=
  mkPoint (- (5 * sqrt 3 / 2)) (5 / 2).

Definition mint_two_ti_plus : R := 1 / 6.
Definition mint_two_ti_minus : R := 5 / 6.
Definition mint_two_tj_plus : R := (2 + sqrt 3) / 4.
Definition mint_two_tj_minus : R := (2 - sqrt 3) / 4.

Lemma mint_two_sqrt3_bound : 1 < sqrt 3 < 2.
Proof.
  pose proof (sqrt_lt_R0 3 ltac:(lra)) as Hpos.
  pose proof (sqrt_sqrt 3 ltac:(lra)) as Hsq.
  split.
  - apply Rsqr_incrst_0; unfold Rsqr; lra.
  - apply Rsqr_incrst_0; unfold Rsqr; lra.
Qed.

Lemma mint_two_plus_on_circ :
  on_circ mint_two_circ mint_two_ti_plus mint_two_p_plus.
Proof.
  unfold on_circ, mint_two_circ, mint_two_ti_plus, mint_two_p_plus, circ_eval.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  split; [lra|].
  replace (0 + (1 / 6) * PI) with (PI / 6) by (pose proof PI_RGT_0; field; lra).
  rewrite cos_PI6, sin_PI6.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma five_pi_over_six : 5 * PI / 6 = PI - PI / 6.
Proof.
  pose proof PI_RGT_0. field; lra.
Qed.

Lemma cos_5PI6 : cos (5 * PI / 6) = - (sqrt 3 / 2).
Proof.
  rewrite five_pi_over_six, cos_pi_minus, cos_PI6. reflexivity.
Qed.

Lemma sin_5PI6 : sin (5 * PI / 6) = 1 / 2.
Proof.
  rewrite five_pi_over_six, sin_pi_minus, sin_PI6. reflexivity.
Qed.

Lemma mint_two_minus_on_circ :
  on_circ mint_two_circ mint_two_ti_minus mint_two_p_minus.
Proof.
  unfold on_circ, mint_two_circ, mint_two_ti_minus, mint_two_p_minus, circ_eval.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  split; [lra|].
  replace (0 + (5 / 6) * PI) with (5 * PI / 6) by (pose proof PI_RGT_0; field; lra).
  rewrite cos_5PI6, sin_5PI6.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma mint_two_plus_on_chord :
  on_chord mint_two_chord mint_two_tj_plus mint_two_p_plus.
Proof.
  unfold on_chord, mint_two_chord, mint_two_tj_plus, mint_two_p_plus, chord_eval.
  cbn [px py ce_p0 ce_p1].
  pose proof mint_two_sqrt3_bound. split; [lra|].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma mint_two_minus_on_chord :
  on_chord mint_two_chord mint_two_tj_minus mint_two_p_minus.
Proof.
  unfold on_chord, mint_two_chord, mint_two_tj_minus, mint_two_p_minus, chord_eval.
  cbn [px py ce_p0 ce_p1].
  pose proof mint_two_sqrt3_bound. split; [lra|].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma mint_two_plus_I_ok :
  I_ok (MkCirc mint_two_circ) (MkChord mint_two_chord)
       (IHit mint_two_p_plus mint_two_ti_plus mint_two_tj_plus).
Proof.
  unfold I_ok.
  split; [exact mint_two_plus_on_circ | exact mint_two_plus_on_chord].
Qed.

Lemma mint_two_minus_I_ok :
  I_ok (MkCirc mint_two_circ) (MkChord mint_two_chord)
       (IHit mint_two_p_minus mint_two_ti_minus mint_two_tj_minus).
Proof.
  unfold I_ok.
  split; [exact mint_two_minus_on_circ | exact mint_two_minus_on_chord].
Qed.

Lemma mint_two_pts_distinct : mint_two_p_plus <> mint_two_p_minus.
Proof.
  unfold mint_two_p_plus, mint_two_p_minus. intros H. injection H as Hx.
  pose proof mint_two_sqrt3_bound. lra.
Qed.

Lemma mint_two_sweep_not_full :
  circ_sweep mint_two_circ <> 2 * PI /\ circ_sweep mint_two_circ <> - (2 * PI).
Proof.
  unfold mint_two_circ. cbn [circ_sweep].
  pose proof PI_RGT_0. split; lra.
Qed.

Definition mint_two_hen_plus : Hen := 4%nat.
Definition mint_two_hen_minus : Hen := 5%nat.

Definition mint_two_ck_circ : Chicken :=
  mkChicken 0%nat 1%nat (MkCirc mint_two_circ).
Definition mint_two_ck_chord : Chicken :=
  mkChicken 2%nat 3%nat (MkChord mint_two_chord).

Definition mint_two_cooked_plus : CookedPair :=
  cook_hit_circ_chord mint_two_ck_circ mint_two_ck_chord
    mint_two_circ mint_two_chord mint_two_ti_plus mint_two_tj_plus
    mint_two_hen_plus.

Definition mint_two_cooked_minus : CookedPair :=
  cook_hit_circ_chord mint_two_ck_circ mint_two_ck_chord
    mint_two_circ mint_two_chord mint_two_ti_minus mint_two_tj_minus
    mint_two_hen_minus.

Lemma mint_two_try_plus :
  try_cook_hit_mixed mint_two_ck_circ mint_two_ck_chord
    (IHit mint_two_p_plus mint_two_ti_plus mint_two_tj_plus)
    mint_two_hen_plus = Some mint_two_cooked_plus.
Proof. reflexivity. Qed.

Lemma mint_two_try_minus :
  try_cook_hit_mixed mint_two_ck_circ mint_two_ck_chord
    (IHit mint_two_p_minus mint_two_ti_minus mint_two_tj_minus)
    mint_two_hen_minus = Some mint_two_cooked_minus.
Proof. reflexivity. Qed.

Lemma mint_two_hens_distinct :
  cp_hen mint_two_cooked_plus <> cp_hen mint_two_cooked_minus.
Proof.
  unfold mint_two_cooked_plus, mint_two_cooked_minus. discriminate.
Qed.

Print Assumptions mixed_on_circ.
Print Assumptions mixed_on_chord.
Print Assumptions mixed_circ_chord_I_ok.
Print Assumptions mixed_chord_circ_I_ok.
Print Assumptions mixed_sweep_not_full.
Print Assumptions mixed_try_cook_hit.
Print Assumptions mixed_try_cook_touch_none.
Print Assumptions mixed_try_cook_decline_none.
Print Assumptions mixed_tag_still_decline.
Print Assumptions hor_bot_locked_circ_A_empty.
Print Assumptions mint_two_plus_I_ok.
Print Assumptions mint_two_minus_I_ok.
Print Assumptions mint_two_try_plus.
Print Assumptions mint_two_try_minus.
Print Assumptions mint_two_hens_distinct.
Print Assumptions mint_two_pts_distinct.
Print Assumptions mint_two_sweep_not_full.
