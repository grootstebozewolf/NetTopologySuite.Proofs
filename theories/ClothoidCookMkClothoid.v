(* ============================================================================
   NetTopologySuite.Proofs.ClothoidCookMkClothoid
   ----------------------------------------------------------------------------
   Fixture: two short bent clothoids, θ0=0, L=2.
     A: p0=(0,0)   κ: 0→3    γA(t)=(2t, 2t³)
     B: p0=(0,1/2) κ: 0→-3   γB(t)=(2t, 1/2-2t³)
   Images cross at γ(1/2)=(1,1/4). Endpoint-chords γ(0)–γ(1) cross at
   (1/4,1/4). Not the unit-square diagonal Hit. try_cook_hit = Some.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook.
Local Open Scope R_scope.

Definition locked_cloth_A : ClothoidEgg :=
  mkClothoidEgg (mkPoint 0 0) (mkPoint 2 0) 0 3 2 0.

Definition locked_cloth_B : ClothoidEgg :=
  mkClothoidEgg (mkPoint 0 (1 / 2)) (mkPoint 2 (1 / 2)) 0 (-3) 2 0.

Definition locked_cloth_hit_pt : Point := mkPoint 1 (1 / 4).
Definition locked_cloth_ti : R := 1 / 2.
Definition locked_cloth_tj : R := 1 / 2.

Definition locked_cloth_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkClothoid locked_cloth_A).

Definition locked_cloth_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkClothoid locked_cloth_B).

Lemma locked_cloth_ti_in_01 : 0 <= locked_cloth_ti <= 1.
Proof.
  unfold locked_cloth_ti. lra.
Qed.

Lemma locked_cloth_tj_in_01 : 0 <= locked_cloth_tj <= 1.
Proof.
  unfold locked_cloth_tj. lra.
Qed.

Lemma locked_cloth_A_at_ti :
  cloth_eval locked_cloth_A locked_cloth_ti = locked_cloth_hit_pt.
Proof.
  unfold cloth_eval, cloth_y_off, locked_cloth_A, locked_cloth_ti,
         locked_cloth_hit_pt.
  cbn [px py cloth_p0 cloth_k0 cloth_k1 cloth_L cloth_th0].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_cloth_B_at_tj :
  cloth_eval locked_cloth_B locked_cloth_tj = locked_cloth_hit_pt.
Proof.
  unfold cloth_eval, cloth_y_off, locked_cloth_B, locked_cloth_tj,
         locked_cloth_hit_pt.
  cbn [px py cloth_p0 cloth_k0 cloth_k1 cloth_L cloth_th0].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_on_cloth_A :
  on_cloth locked_cloth_A locked_cloth_ti locked_cloth_hit_pt.
Proof.
  unfold on_cloth. split; [exact locked_cloth_ti_in_01|].
  symmetry. exact locked_cloth_A_at_ti.
Qed.

Lemma locked_on_cloth_B :
  on_cloth locked_cloth_B locked_cloth_tj locked_cloth_hit_pt.
Proof.
  unfold on_cloth. split; [exact locked_cloth_tj_in_01|].
  symmetry. exact locked_cloth_B_at_tj.
Qed.

Lemma locked_mkclothoid_I_ok :
  I_ok (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B)
       (IHit locked_cloth_hit_pt locked_cloth_ti locked_cloth_tj).
Proof.
  unfold I_ok.
  split; [exact locked_on_cloth_A | exact locked_on_cloth_B].
Qed.

(* Endpoint-chords of γ(0)–γ(1) cross at (1/4,1/4), not the clothoid Hit. *)
Lemma locked_mkclothoid_hit_neq_endpoint_chord_x :
  let ca := mkChordEgg (cloth_eval locked_cloth_A 0)
                       (cloth_eval locked_cloth_A 1) in
  let cb := mkChordEgg (cloth_eval locked_cloth_B 0)
                       (cloth_eval locked_cloth_B 1) in
  chord_eval ca (1 / 8) = chord_eval cb (1 / 8) /\
  chord_eval ca (1 / 8) <> locked_cloth_hit_pt.
Proof.
  unfold chord_eval, cloth_eval, cloth_y_off, locked_cloth_A, locked_cloth_B,
         locked_cloth_hit_pt.
  cbn [px py ce_p0 ce_p1 cloth_p0 cloth_k0 cloth_k1 cloth_L cloth_th0].
  split.
  - apply (f_equal2 mkPoint); field.
  - intros H. apply (f_equal px) in H. cbn [px] in H. lra.
Qed.

Lemma cloth_split_changes_k_on_locked_A :
  cloth_k1 (fst (cloth_split locked_cloth_A locked_cloth_ti))
    <> cloth_k1 locked_cloth_A /\
  cloth_k0 (snd (cloth_split locked_cloth_A locked_cloth_ti))
    <> cloth_k0 locked_cloth_A.
Proof.
  unfold cloth_split, cloth_k_at, locked_cloth_A, locked_cloth_ti.
  cbn [fst snd cloth_k0 cloth_k1].
  split; lra.
Qed.

Definition locked_mkclothoid_hit : IResult :=
  IHit locked_cloth_hit_pt locked_cloth_ti locked_cloth_tj.

Definition cooked_mkclothoid : CookedPair :=
  cook_hit_clothoids locked_cloth_ck1 locked_cloth_ck2
    locked_cloth_A locked_cloth_B locked_cloth_ti locked_cloth_tj
    crossing_hen.

Lemma cook_hit_clothoids_shares_hen :
  forall c1 c2 e1 e2 ti tj h,
    cooked_shares_hen (cook_hit_clothoids c1 c2 e1 e2 ti tj h).
Proof.
  intros. repeat split; reflexivity.
Qed.

Lemma cooked_mkclothoid_shares :
  cooked_shares_hen cooked_mkclothoid.
Proof.
  apply cook_hit_clothoids_shares_hen.
Qed.

Lemma cooked_mkclothoid_try :
  try_cook_hit locked_cloth_ck1 locked_cloth_ck2
    locked_mkclothoid_hit crossing_hen = Some cooked_mkclothoid.
Proof.
  reflexivity.
Qed.

Lemma cooked_mkclothoid_children_are_clothoid :
  egg_class (ck_egg (cp_left1 cooked_mkclothoid)) = EggClothoid /\
  egg_class (ck_egg (cp_right1 cooked_mkclothoid)) = EggClothoid /\
  egg_class (ck_egg (cp_left2 cooked_mkclothoid)) = EggClothoid /\
  egg_class (ck_egg (cp_right2 cooked_mkclothoid)) = EggClothoid.
Proof.
  repeat split; reflexivity.
Qed.

Lemma interpolant_pair_mkclothoid :
  interpolant_pair (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B).
Proof.
  exact I.
Qed.

Lemma mkclothoid_tag_still_decline :
  I_ok (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid) IDecline.
Proof.
  exact clothoid_decline_I_ok.
Qed.

Lemma mkclothoid_tag_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid)
         (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma mkclothoid_mixed_still_decline :
  I_ok (MkChord hor_bot) (MkClothoid locked_cloth_A) IDecline.
Proof.
  unfold I_ok, interpolant_pair. intro H. exact H.
Qed.

Lemma clothoid_chord_not_first_cook_scope :
  ~ first_cook_scope EggClothoid EggChord.
Proof.
  intro H. exact H.
Qed.

Lemma mkclothoid_neq_mkchord_locked :
  MkClothoid locked_cloth_A <> MkChord diag_ab.
Proof.
  discriminate.
Qed.

Lemma locked_intake_egg_self_hit :
  I_ok (MkClothoid locked_clothoid_egg) (MkClothoid locked_clothoid_egg)
       (IHit (cloth_eval locked_clothoid_egg (1 / 2)) (1 / 2) (1 / 2)).
Proof.
  unfold I_ok, on_cloth.
  split; [split; [lra|reflexivity]|split; [lra|reflexivity]].
Qed.

Theorem ticket_0007_clothoid_first_cook_qed_or_qex :
  (first_cook_scope EggClothoid EggClothoid /\
   interpolant_pair (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B) /\
   I_ok (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B)
        (IHit locked_cloth_hit_pt locked_cloth_ti locked_cloth_tj) /\
   try_cook_hit locked_cloth_ck1 locked_cloth_ck2
     locked_mkclothoid_hit crossing_hen = Some cooked_mkclothoid /\
   cooked_shares_hen cooked_mkclothoid /\
   egg_class (ck_egg (cp_left1 cooked_mkclothoid)) = EggClothoid /\
   I_ok (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid) IDecline /\
   I_ok (MkChord hor_bot) (MkClothoid locked_cloth_A) IDecline /\
   ~ first_cook_scope EggClothoid EggChord /\
   ~ first_cook_scope EggNurbs EggNurbs /\
   cook_loop_status = LoopObligation)
  \/
  (~ first_cook_scope EggClothoid EggClothoid /\
   forall p ti tj,
     ~ I_ok (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B)
          (IHit p ti tj)).
Proof.
  left.
  split; [exact clothoid_egg_first_cook_scope|].
  split; [exact interpolant_pair_mkclothoid|].
  split; [exact locked_mkclothoid_I_ok|].
  split; [exact cooked_mkclothoid_try|].
  split; [exact cooked_mkclothoid_shares|].
  split; [reflexivity|].
  split; [exact mkclothoid_tag_still_decline|].
  split; [exact mkclothoid_mixed_still_decline|].
  split; [exact clothoid_chord_not_first_cook_scope|].
  split; [exact nurbs_nurbs_not_first_scope|].
  exact cook_loop_is_obligation.
Qed.
