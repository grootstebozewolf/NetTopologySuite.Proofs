(* ============================================================================
   NetTopologySuite.Proofs.SheetHenCookConstructed
   ----------------------------------------------------------------------------
   Split from SheetHenCook.v (module-split gate, docs/module-split-allowlist.txt
   "the allowlist may not grow"). Umbrella re-export pattern: SheetHenCook.v
   re-exports SheetHenCookCore.v plus this file. Carries chord_split / one-Hit
   try_cook_hit and the constructive 𝓘 (proper_cross_signs / constructed_hit),
   built on SheetHenCookCore's ChordEgg / Chicken / IResult / CookWitness.
   No `Admitted`, no `Axiom`, no `Parameter`.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Orientation Segment Intersect.
From NTS.Proofs Require Export SheetHenCookCore.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Letter after Accept: chord split(t) + one Hit cook step. On success the    *)
(* cook mints one hen and replaces each crossed chicken by two incident on    *)
(* that hen. Not the bag-level repeat-until-noded loop. Not a remint of       *)
(* leftover_width / pairwise_split. Not a remint of Intersect.                *)
(* -------------------------------------------------------------------------- *)

Definition chord_split (c : ChordEgg) (t : R) : ChordEgg * ChordEgg :=
  let m := chord_eval c t in
  (mkChordEgg (ce_p0 c) m, mkChordEgg m (ce_p1 c)).

Lemma chord_split_join :
  forall c t,
    ce_p1 (fst (chord_split c t)) = chord_eval c t /\
    ce_p0 (snd (chord_split c t)) = chord_eval c t.
Proof.
  intros c t. split; reflexivity.
Qed.

Lemma chord_split_ends :
  forall c t,
    ce_p0 (fst (chord_split c t)) = ce_p0 c /\
    ce_p1 (snd (chord_split c t)) = ce_p1 c.
Proof.
  intros c t. split; reflexivity.
Qed.

Lemma chord_split_left_reparam :
  forall c t u,
    chord_eval (fst (chord_split c t)) u = chord_eval c (u * t).
Proof.
  intros [p0 p1] t u.
  unfold chord_split, chord_eval. simpl.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma chord_split_right_reparam :
  forall c t u,
    chord_eval (snd (chord_split c t)) u = chord_eval c (t + u * (1 - t)).
Proof.
  intros [p0 p1] t u.
  unfold chord_split, chord_eval. simpl.
  apply (f_equal2 mkPoint); ring.
Qed.

Record CookedPair : Type := mkCookedPair {
  cp_hen : Hen;
  cp_left1 : Chicken;
  cp_right1 : Chicken;
  cp_left2 : Chicken;
  cp_right2 : Chicken
}.

Definition cook_hit_chords
  (c1 c2 : Chicken) (e1 e2 : ChordEgg) (ti tj : R) (h_new : Hen)
  : CookedPair :=
  let s1 := chord_split e1 ti in
  let s2 := chord_split e2 tj in
  mkCookedPair h_new
    (mkChicken (ck_src c1) h_new (MkChord (fst s1)))
    (mkChicken h_new (ck_dst c1) (MkChord (snd s1)))
    (mkChicken (ck_src c2) h_new (MkChord (fst s2)))
    (mkChicken h_new (ck_dst c2) (MkChord (snd s2))).

Definition cook_hit_circs
  (c1 c2 : Chicken) (e1 e2 : CircularEgg) (ti tj : R) (h_new : Hen)
  : CookedPair :=
  let s1 := circ_split e1 ti in
  let s2 := circ_split e2 tj in
  mkCookedPair h_new
    (mkChicken (ck_src c1) h_new (MkCirc (fst s1)))
    (mkChicken h_new (ck_dst c1) (MkCirc (snd s1)))
    (mkChicken (ck_src c2) h_new (MkCirc (fst s2)))
    (mkChicken h_new (ck_dst c2) (MkCirc (snd s2))).

Definition cook_hit_clothoids
  (c1 c2 : Chicken) (e1 e2 : ClothoidEgg) (ti tj : R) (h_new : Hen)
  : CookedPair :=
  let s1 := cloth_split e1 ti in let s2 := cloth_split e2 tj in
  mkCookedPair h_new
    (mkChicken (ck_src c1) h_new (MkClothoid (fst s1)))
    (mkChicken h_new (ck_dst c1) (MkClothoid (snd s1)))
    (mkChicken (ck_src c2) h_new (MkClothoid (fst s2)))
    (mkChicken h_new (ck_dst c2) (MkClothoid (snd s2))).

Definition try_cook_hit (c1 c2 : Chicken) (o : IResult) (h_new : Hen)
  : option CookedPair :=
  match ck_egg c1, ck_egg c2, o with
  | MkChord e1, MkChord e2, IHit _ ti tj =>
      Some (cook_hit_chords c1 c2 e1 e2 ti tj h_new)
  | MkCirc e1, MkCirc e2, IHit _ ti tj =>
      Some (cook_hit_circs c1 c2 e1 e2 ti tj h_new)
  | MkClothoid e1, MkClothoid e2, IHit _ ti tj => Some (cook_hit_clothoids c1 c2 e1 e2 ti tj h_new)
  | MkNurbs _, _, _ => None
  | _, MkNurbs _, _ => None
  | _, _, _ => None
  end.

Definition cooked_shares_hen (cp : CookedPair) : Prop :=
  ck_dst (cp_left1 cp) = cp_hen cp /\
  ck_src (cp_right1 cp) = cp_hen cp /\
  ck_dst (cp_left2 cp) = cp_hen cp /\
  ck_src (cp_right2 cp) = cp_hen cp.

Lemma cook_hit_chords_shares_hen :
  forall c1 c2 e1 e2 ti tj h,
    cooked_shares_hen (cook_hit_chords c1 c2 e1 e2 ti tj h).
Proof.
  intros. repeat split; reflexivity.
Qed.

Lemma try_cook_hit_decline_none :
  forall c1 c2 h, try_cook_hit c1 c2 IDecline h = None.
Proof.
  intros [s1 d1 e1] [s2 d2 e2] h.
  destruct e1, e2; reflexivity.
Qed.

Lemma try_cook_hit_empty_none :
  forall c1 c2 h, try_cook_hit c1 c2 IEmpty h = None.
Proof.
  intros [s1 d1 e1] [s2 d2 e2] h.
  destruct e1, e2; reflexivity.
Qed.

Lemma try_cook_hit_out_of_scope_none :
  forall c1 c2 p ti tj h,
    ~ interpolant_pair (ck_egg c1) (ck_egg c2) ->
    try_cook_hit c1 c2 (IHit p ti tj) h = None.
Proof.
  intros [s1 d1 e1] [s2 d2 e2] p ti tj h H.
  destruct e1, e2; simpl in *; try reflexivity;
    exfalso; apply H; exact I.
Qed.

Lemma try_cook_hit_chord_hit_some :
  forall c1 c2 e1 e2 p ti tj h,
    ck_egg c1 = MkChord e1 ->
    ck_egg c2 = MkChord e2 ->
    exists cp,
      try_cook_hit c1 c2 (IHit p ti tj) h = Some cp /\
      cooked_shares_hen cp /\
      cp_hen cp = h.
Proof.
  intros [s1 d1 eg1] [s2 d2 eg2] e1 e2 p ti tj h He1 He2.
  simpl in He1, He2. subst. simpl.
  exists (cook_hit_chords (mkChicken s1 d1 (MkChord e1))
                          (mkChicken s2 d2 (MkChord e2)) e1 e2 ti tj h).
  split; [reflexivity|].
  split; [apply cook_hit_chords_shares_hen|].
  reflexivity.
Qed.

Definition crossing_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkChord diag_ab).
Definition crossing_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkChord diag_cd).
Definition crossing_hen : Hen := 4%nat.

Definition cooked_crossing : CookedPair :=
  cook_hit_chords crossing_ck1 crossing_ck2 diag_ab diag_cd
    (1 / 2) (1 / 2) crossing_hen.

Lemma cooked_crossing_shares :
  cooked_shares_hen cooked_crossing.
Proof.
  apply cook_hit_chords_shares_hen.
Qed.

Lemma cooked_crossing_try :
  try_cook_hit crossing_ck1 crossing_ck2
    (cw_result crossing_witness) crossing_hen = Some cooked_crossing.
Proof.
  reflexivity.
Qed.

Lemma cooked_crossing_join :
  ce_p1 (fst (chord_split diag_ab (1 / 2))) = cross_pt /\
  ce_p0 (snd (chord_split diag_ab (1 / 2))) = cross_pt /\
  ce_p1 (fst (chord_split diag_cd (1 / 2))) = cross_pt /\
  ce_p0 (snd (chord_split diag_cd (1 / 2))) = cross_pt.
Proof.
  repeat split;
    (rewrite (proj1 (chord_split_join _ _)) ||
     rewrite (proj2 (chord_split_join _ _)));
    unfold cross_pt; unfold chord_eval, diag_ab, diag_cd; simpl;
    apply (f_equal2 mkPoint); field.
Qed.

Definition clothoid_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkOutOfScope EggClothoid).
Definition clothoid_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkOutOfScope EggClothoid).

Lemma try_cook_hit_clothoid_none :
  try_cook_hit clothoid_ck1 clothoid_ck2 IDecline crossing_hen = None.
Proof.
  reflexivity.
Qed.

Definition nurbs_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkOutOfScope EggNurbs).
Definition nurbs_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkOutOfScope EggNurbs).

Lemma try_cook_hit_nurbs_none :
  try_cook_hit nurbs_ck1 nurbs_ck2 IDecline crossing_hen = None.
Proof.
  reflexivity.
Qed.

(* Tags still get None from try_cook_hit. MkCirc mints in CircularCookMkCirc. *)
Definition circular_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkOutOfScope EggCircularArc).
Definition circular_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkOutOfScope EggCircularArc).

Lemma circular_egg_first_cook_scope :
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact I.
Qed.

Lemma try_cook_hit_circular_hit_none :
  forall p ti tj h,
    try_cook_hit circular_ck1 circular_ck2 (IHit p ti tj) h = None.
Proof.
  intros p ti tj h.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Letter after Accept: constructive 𝓘. Proper-cross signs license            *)
(* Intersect.strict_intersection_point as p-star plus the two open-interval   *)
(* parameters. Not a remint of Intersect. Not a total noder. Missing          *)
(* signs is not Decline (Decline is out-of-scope); it is no constructed       *)
(* Hit. Equal constructed p-star (swap of operands) licenses ShareOne.        *)
(* -------------------------------------------------------------------------- *)

Definition proper_cross_signs (c1 c2 : ChordEgg) : Prop :=
  cross (ce_p0 c1) (ce_p1 c1) (ce_p0 c2)
    * cross (ce_p0 c1) (ce_p1 c1) (ce_p1 c2) < 0 /\
  cross (ce_p0 c2) (ce_p1 c2) (ce_p0 c1)
    * cross (ce_p0 c2) (ce_p1 c2) (ce_p1 c1) < 0.

Definition constructed_ab_param (c1 c2 : ChordEgg) : R :=
  let A := ce_p0 c1 in
  let B := ce_p1 c1 in
  let C := ce_p0 c2 in
  let D := ce_p1 c2 in
  cross C D A / (cross C D A - cross C D B).

Definition constructed_cd_param (c1 c2 : ChordEgg) : R :=
  let A := ce_p0 c1 in
  let B := ce_p1 c1 in
  let C := ce_p0 c2 in
  let D := ce_p1 c2 in
  cross A B C / (cross A B C - cross A B D).

Definition constructed_p (c1 c2 : ChordEgg) : Point :=
  strict_intersection_point (ce_p0 c1) (ce_p1 c1) (ce_p0 c2) (ce_p1 c2).

Definition constructed_hit (c1 c2 : ChordEgg) : IResult :=
  IHit (constructed_p c1 c2)
       (constructed_ab_param c1 c2)
       (constructed_cd_param c1 c2).

Lemma proper_cross_signs_sym :
  forall c1 c2,
    proper_cross_signs c1 c2 -> proper_cross_signs c2 c1.
Proof.
  intros c1 c2 [H1 H2]. split; assumption.
Qed.

Lemma constructed_hit_on_c1 :
  forall c1 c2,
    proper_cross_signs c1 c2 ->
    on_chord c1 (constructed_ab_param c1 c2) (constructed_p c1 c2).
Proof.
  intros c1 c2 [H1 H2].
  set (A := ce_p0 c1).
  set (B := ce_p1 c1).
  set (C := ce_p0 c2).
  set (D := ce_p1 c2).
  fold A B C D in H1, H2.
  assert (Hden_t : cross A B C - cross A B D <> 0) by nra.
  assert (Hden_s : cross C D A - cross C D B <> 0) by nra.
  unfold on_chord, constructed_ab_param, constructed_p, chord_eval,
         strict_intersection_point.
  fold A B C D.
  pose proof (div_in_unit_interval (cross C D A) (cross C D B) H2) as Hs.
  split.
  - exact Hs.
  - apply (f_equal2 mkPoint); unfold cross; field; split; assumption.
Qed.

Lemma constructed_hit_on_c2 :
  forall c1 c2,
    proper_cross_signs c1 c2 ->
    on_chord c2 (constructed_cd_param c1 c2) (constructed_p c1 c2).
Proof.
  intros [A B] [C D] [H1 H2].
  unfold on_chord, constructed_cd_param, constructed_p, chord_eval,
         strict_intersection_point.
  simpl.
  pose proof (div_in_unit_interval (cross A B C) (cross A B D) H1) as Ht.
  split.
  - exact Ht.
  - apply (f_equal2 mkPoint); reflexivity.
Qed.

Lemma constructed_hit_I_ok :
  forall c1 c2,
    proper_cross_signs c1 c2 ->
    I_ok (MkChord c1) (MkChord c2) (constructed_hit c1 c2).
Proof.
  intros c1 c2 H.
  unfold constructed_hit, I_ok.
  split.
  - apply constructed_hit_on_c1; exact H.
  - apply constructed_hit_on_c2; exact H.
Qed.

Lemma crossing_proper_cross_signs :
  proper_cross_signs diag_ab diag_cd.
Proof.
  unfold proper_cross_signs, diag_ab, diag_cd, cross.
  simpl. split; lra.
Qed.

Lemma constructed_hit_crossing_eq :
  constructed_hit diag_ab diag_cd = IHit cross_pt (1 / 2) (1 / 2).
Proof.
  unfold constructed_hit, constructed_p, constructed_ab_param,
         constructed_cd_param, strict_intersection_point,
         diag_ab, diag_cd, cross_pt, cross.
  simpl.
  f_equal; [apply (f_equal2 mkPoint); field | field | field].
Qed.

Lemma disjoint_not_proper_cross :
  ~ proper_cross_signs hor_bot hor_top.
Proof.
  unfold proper_cross_signs, hor_bot, hor_top, cross.
  simpl. intros [H _]. lra.
Qed.

Definition hit_point (o : IResult) : option Point :=
  match o with
  | IHit p _ _ => Some p
  | _ => None
  end.

Lemma constructed_hit_sym_same_p :
  forall c1 c2,
    proper_cross_signs c1 c2 ->
    hit_point (constructed_hit c1 c2) = hit_point (constructed_hit c2 c1).
Proof.
  intros [A B] [C D] [H1 H2].
  unfold constructed_hit, constructed_p, hit_point.
  simpl.
  apply f_equal.
  apply strict_intersection_point_sym; assumption.
Qed.

Lemma equal_constructed_p_share :
  forall c1 c2 h,
    proper_cross_signs c1 c2 ->
    hit_point (constructed_hit c1 c2) = hit_point (constructed_hit c2 c1) /\
    fst (apply_id_decision (ShareOne h)) =
    snd (apply_id_decision (ShareOne h)).
Proof.
  intros c1 c2 h H.
  split.
  - apply constructed_hit_sym_same_p; exact H.
  - apply share_one_same_hen.
Qed.

Lemma constructed_p_unique :
  forall c1 c2 X,
    proper_cross_signs c1 c2 ->
    between (ce_p0 c1) (ce_p1 c1) X ->
    between (ce_p0 c2) (ce_p1 c2) X ->
    X = constructed_p c1 c2.
Proof.
  intros [A B] [C D] X [H1 H2] HAB HCD.
  unfold constructed_p. simpl.
  apply (strict_intersection_eq_formula A B C D X H1 H2 HAB HCD).
Qed.

Definition constructed_crossing_witness : CookWitness :=
  mkCookWitness (MkChord diag_ab) (MkChord diag_cd)
    (constructed_hit diag_ab diag_cd)
    (constructed_hit_I_ok diag_ab diag_cd crossing_proper_cross_signs).

Lemma cooked_constructed_crossing :
  try_cook_hit crossing_ck1 crossing_ck2
    (constructed_hit diag_ab diag_cd) crossing_hen = Some cooked_crossing.
Proof.
  rewrite constructed_hit_crossing_eq.
  reflexivity.
Qed.

Print Assumptions first_cook_scope_chord_chord.
Print Assumptions clothoid_egg_first_cook_scope.
Print Assumptions IEmpty_neq_IDecline.
Print Assumptions crossing_witness.
Print Assumptions disjoint_witness.
Print Assumptions share_one_same_hen.
Print Assumptions coord_eq_not_hen_eq.
Print Assumptions noded_crossing.
Print Assumptions crossing_not_nodable_shadow.
Print Assumptions snap_round_neq_I.
Print Assumptions interior_split_finite_holds.
Print Assumptions split_step_confluent.
Print Assumptions leftover_left_on_parent.
Print Assumptions leftover_right_on_parent.
Print Assumptions cook_loop_is_discharged.
Print Assumptions coord_realization_preserves_sheet.
Print Assumptions binary64_same_sheet_as_R.
Print Assumptions overlay_ng_robust_is_snap_not_I.
Print Assumptions overlay_ng_robust_is_finite_snap_holds.
Print Assumptions hen_id_dart_of_twin.
Print Assumptions ddir_migration_one_equation.
Print Assumptions chord_split_left_reparam.
Print Assumptions cook_hit_chords_shares_hen.
Print Assumptions cooked_crossing_try.
Print Assumptions cooked_crossing_join.
Print Assumptions try_cook_hit_clothoid_none.
Print Assumptions nurbs_nurbs_first_cook_scope.
Print Assumptions nurbs_decline_I_ok.
Print Assumptions try_cook_hit_nurbs_none.
Print Assumptions try_cook_hit_circular_hit_none.
Print Assumptions circular_egg_first_cook_scope.
Print Assumptions circular_decline_I_ok.
Print Assumptions circular_hit_not_I_ok.
Print Assumptions chord_circular_decline_I_ok.
Print Assumptions chord_circular_hit_not_I_ok.
Print Assumptions chord_circular_empty_not_I_ok.
Print Assumptions constructed_hit_I_ok.
Print Assumptions constructed_hit_crossing_eq.
Print Assumptions disjoint_not_proper_cross.
Print Assumptions constructed_hit_sym_same_p.
Print Assumptions equal_constructed_p_share.
Print Assumptions cooked_constructed_crossing.
Print Assumptions chord_split_join.
Print Assumptions chord_split_ends.
Print Assumptions chord_split_right_reparam.
Print Assumptions try_cook_hit_decline_none.
Print Assumptions try_cook_hit_empty_none.
Print Assumptions try_cook_hit_out_of_scope_none.
Print Assumptions try_cook_hit_chord_hit_some.
Print Assumptions cooked_crossing_shares.
Print Assumptions proper_cross_signs_sym.
Print Assumptions constructed_hit_on_c1.
Print Assumptions constructed_hit_on_c2.
Print Assumptions crossing_proper_cross_signs.
Print Assumptions constructed_p_unique.
