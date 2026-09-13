(* ============================================================================
   NetTopologySuite.Proofs.ClothoidCookMkClothoid
   ----------------------------------------------------------------------------
   ADR-0007 letter: clothoid×clothoid first-cook / Hit arm
   (claimId 0007-clothoid-first-cook).

   Host interpolant is the closed-form small-angle clothoid
   (cos θ≈1, sin θ≈θ) in SheetHenClothoidEgg — not Fresnel, not
   chord-parameter. Raw mkClothoidEgg is the record constructor;
   the public host ctor is mk_cloth (sets p1:=γ(1)). Do not hide
   the record. Cook fixtures go through mk_cloth only. Algebraic
   model vs instance: locked A/B keep |θ| small on [0,1]
   (named heading bounds).

   Fixture: two short bent clothoids (distinct x(t), ti≠tj).
     A: p0=(0,0) κ: 0→1/10 L=1 θ0=1/20  γA(t)=(t, t/20+t³/60)
     B: p0=(0,91/1620) κ: 0→-1/20 L=2 θ0=-1/40
        γB(t)=(2t, 91/1620 − t/20 − t³/30)
   Images cross at (ti,tj)=(2/3,1/3) → Hit (2/3, 31/810).
   Endpoint-chords meet at named (14/27, 14/405) ≠ Hit.
   locked_cloth_eval_neq_endpoint_chord: γ(ti) ≠ lerp(γ(0),γ(1))(ti)
   (fails if cloth_eval is endpoint lerp). try_cook_hit = Some. bent ≠ zero-κ.

   Mode D host joint; first-cook interior Hit stays A×B;
   this is split-children meet, not example5.

   MkOutOfScope EggClothoid stays Decline. Mixed clothoid×chord
   stays Decline. NURBS / SIN / ellipse / spiral / geodesic stay
   out of first cook. ρ / Campaign / Fresnel-as-noding stay parked.

   WITNESS topic: overlay · claimId: 0007-clothoid-first-cook
   witness: 0007-clothoid-first-cook
   board: ADR-0007
   3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook.
Local Open Scope R_scope.

Definition locked_cloth_A : ClothoidEgg :=
  mk_cloth (mkPoint 0 0) 0 (1 / 10) 1 (1 / 20).

Definition locked_cloth_B : ClothoidEgg :=
  mk_cloth (mkPoint 0 (91 / 1620)) 0 (-1 / 20) 2 (-1 / 40).

Definition locked_cloth_hit_pt : Point := mkPoint (2 / 3) (31 / 810).
Definition locked_cloth_ti : R := 2 / 3.
Definition locked_cloth_tj : R := 1 / 3.
Definition locked_cloth_chord_x : Point := mkPoint (14 / 27) (14 / 405).

Definition locked_cloth_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkClothoid locked_cloth_A).

Definition locked_cloth_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkClothoid locked_cloth_B).

Lemma locked_cloth_A_wf : cloth_wf locked_cloth_A.
Proof.
  unfold locked_cloth_A. apply cloth_wf_mk.
Qed.

Lemma locked_cloth_B_wf : cloth_wf locked_cloth_B.
Proof.
  unfold locked_cloth_B. apply cloth_wf_mk.
Qed.

Lemma locked_cloth_A_p1_is_gamma1 :
  cloth_p1 locked_cloth_A = cloth_eval locked_cloth_A 1.
Proof.
  apply cloth_wf_of_p1. exact locked_cloth_A_wf.
Qed.

Lemma locked_cloth_B_p1_is_gamma1 :
  cloth_p1 locked_cloth_B = cloth_eval locked_cloth_B 1.
Proof.
  apply cloth_wf_of_p1. exact locked_cloth_B_wf.
Qed.

Lemma locked_cloth_A_th :
  forall t, cloth_th locked_cloth_A t = 1 / 20 + (t * t) / 20.
Proof.
  intros t.
  unfold locked_cloth_A, mk_cloth, cloth_th.
  cbn [cloth_th0 cloth_L cloth_k0 cloth_k1].
  field.
Qed.

Lemma locked_cloth_B_th :
  forall t, cloth_th locked_cloth_B t = -1 / 40 - (t * t) / 20.
Proof.
  intros t.
  unfold locked_cloth_B, mk_cloth, cloth_th.
  cbn [cloth_th0 cloth_L cloth_k0 cloth_k1].
  field.
Qed.

Lemma locked_unit_sqr :
  forall t, 0 <= t <= 1 -> 0 <= t * t <= 1.
Proof.
  intros t Ht. split.
  - apply Rle_0_sqr.
  - replace 1 with (1 * 1) by ring.
    apply Rmult_le_compat; lra.
Qed.

Lemma locked_cloth_A_heading_small :
  forall t, 0 <= t <= 1 -> Rabs (cloth_th locked_cloth_A t) <= 1 / 10.
Proof.
  intros t Ht.
  rewrite locked_cloth_A_th.
  pose proof (locked_unit_sqr t Ht) as Ht2.
  rewrite Rabs_right by lra.
  lra.
Qed.

Lemma locked_cloth_B_heading_small :
  forall t, 0 <= t <= 1 -> Rabs (cloth_th locked_cloth_B t) <= 3 / 40.
Proof.
  intros t Ht.
  rewrite locked_cloth_B_th.
  pose proof (locked_unit_sqr t Ht) as Ht2.
  rewrite Rabs_left1 by lra.
  lra.
Qed.

Lemma locked_cloth_ti_in_01 : 0 <= locked_cloth_ti <= 1.
Proof.
  unfold locked_cloth_ti. lra.
Qed.

Lemma locked_cloth_tj_in_01 : 0 <= locked_cloth_tj <= 1.
Proof.
  unfold locked_cloth_tj. lra.
Qed.

Lemma locked_cloth_ti_neq_tj : locked_cloth_ti <> locked_cloth_tj.
Proof.
  unfold locked_cloth_ti, locked_cloth_tj. lra.
Qed.

Lemma locked_cloth_A_at_ti :
  cloth_eval locked_cloth_A locked_cloth_ti = locked_cloth_hit_pt.
Proof.
  unfold locked_cloth_A, locked_cloth_ti, locked_cloth_hit_pt, mk_cloth,
         cloth_eval, cloth_eval_seed, cloth_y_off_seed.
  cbn [px py cloth_p0 cloth_k0 cloth_k1 cloth_L cloth_th0].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_cloth_B_at_tj :
  cloth_eval locked_cloth_B locked_cloth_tj = locked_cloth_hit_pt.
Proof.
  unfold locked_cloth_B, locked_cloth_tj, locked_cloth_hit_pt, mk_cloth,
         cloth_eval, cloth_eval_seed, cloth_y_off_seed.
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

(* Endpoint-chords of γ(0)–γ(1) meet at named (14/27, 14/405) ≠ Hit. *)
Lemma locked_mkclothoid_hit_neq_endpoint_chord_x :
  let ca := mkChordEgg (cloth_p0 locked_cloth_A) (cloth_p1 locked_cloth_A) in
  let cb := mkChordEgg (cloth_p0 locked_cloth_B) (cloth_p1 locked_cloth_B) in
  chord_eval ca (14 / 27) = locked_cloth_chord_x /\
  chord_eval cb (7 / 27) = locked_cloth_chord_x /\
  locked_cloth_chord_x <> locked_cloth_hit_pt.
Proof.
  unfold locked_cloth_A, locked_cloth_B, locked_cloth_hit_pt,
         locked_cloth_chord_x, mk_cloth, cloth_eval_seed, cloth_y_off_seed,
         chord_eval.
  cbn [px py ce_p0 ce_p1 cloth_p0 cloth_p1 cloth_k0 cloth_k1 cloth_L cloth_th0].
  split; [|split].
  - apply (f_equal2 mkPoint); field.
  - apply (f_equal2 mkPoint); field.
  - intros H. apply (f_equal px) in H. cbn [px] in H. lra.
Qed.

(* Mirror of circle locked_circ_eval_neq_endpoint_chord: γ at ti is
   not the endpoint-chord sample at the same parameter. *)
Lemma locked_cloth_eval_neq_endpoint_chord :
  cloth_eval locked_cloth_A locked_cloth_ti
    <> chord_eval
         (mkChordEgg (cloth_eval locked_cloth_A 0)
                     (cloth_eval locked_cloth_A 1))
         locked_cloth_ti.
Proof.
  intros H.
  apply (f_equal py) in H.
  unfold locked_cloth_A, locked_cloth_ti, mk_cloth,
         cloth_eval, cloth_eval_seed, cloth_y_off_seed, chord_eval in H.
  cbn [px py ce_p0 ce_p1 cloth_p0 cloth_k0 cloth_k1 cloth_L cloth_th0] in H.
  lra.
Qed.

Lemma locked_letter_eggs_wf :
  cloth_wf locked_cloth_A /\
  cloth_wf locked_cloth_B /\
  cloth_wf locked_clothoid_egg /\
  cloth_wf (fst (cloth_split locked_cloth_A locked_cloth_ti)) /\
  cloth_wf (snd (cloth_split locked_cloth_A locked_cloth_ti)).
Proof.
  split; [exact locked_cloth_A_wf|].
  split; [exact locked_cloth_B_wf|].
  split; [exact locked_clothoid_egg_wf|].
  split; [apply cloth_wf_split_left|apply cloth_wf_split_right].
Qed.

Lemma cloth_split_changes_k_on_locked_A :
  cloth_k1 (fst (cloth_split locked_cloth_A locked_cloth_ti))
    <> cloth_k1 locked_cloth_A /\
  cloth_k0 (snd (cloth_split locked_cloth_A locked_cloth_ti))
    <> cloth_k0 locked_cloth_A.
Proof.
  unfold locked_cloth_A, locked_cloth_ti, cloth_split, cloth_k_at, mk_cloth.
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

(* WITNESS {"claimId":"0007-clothoid-first-cook","topic":"overlay","lemma":"locked_mkclothoid_I_ok","title":"Host I_ok Hits two MkClothoid chickens on the locked crossing small-angle clothoid pair","file":"theories/ClothoidCookMkClothoid.v","witness":"0007-clothoid-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-clothoid-first-cook","topic":"overlay","lemma":"cooked_mkclothoid_try","title":"try_cook_hit mints MkClothoid hens on the locked clothoid Hit","file":"theories/ClothoidCookMkClothoid.v","witness":"0007-clothoid-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-clothoid-first-cook","topic":"overlay","lemma":"ticket_0007_clothoid_first_cook_qed_or_qex","title":"Clothoid times clothoid is first cook with a locked MkClothoid IHit that try_cook_hit mints (QED) or clothoid times clothoid stays QEX (QEX); discharged QED; small-angle interpolant not Fresnel not chord-parameter; tags and mixed stay Decline","file":"theories/ClothoidCookMkClothoid.v","witness":"0007-clothoid-first-cook","board":"ADR-0007"} *)
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

(* -------------------------------------------------------------------------- *)
(* Mode D: consecutive host ClothoidEgg joints on cloth_eval.                 *)
(* Parallel host joint, not a new interpolant. Joint IHit is concat           *)
(* incidence (t=1 then t=0), not interior I_ok Hit. First-cook interior       *)
(* Hit stays locked_cloth_A × locked_cloth_B. This is cloth_split children    *)
(* of locked_cloth_A at locked_cloth_ti (they meet via cloth_split_join).     *)
(* Not A×B as the joint (those meet in the interior). Not example5.           *)
(* Not two intake clothoids + LS. No CompoundEgg / compound_eval.             *)
(* Do not remint sidecar I_ok_cloth as host I_ok.                             *)
(* -------------------------------------------------------------------------- *)

Definition cloth_joint (A B : ClothoidEgg) : Prop :=
  cloth_eval A 1 = cloth_eval B 0.

Definition cloth_joint_hit (A B : ClothoidEgg) : IResult :=
  IHit (cloth_eval A 1) 1 0.

Lemma cloth_split_cloth_joint :
  forall c t,
    cloth_joint (fst (cloth_split c t)) (snd (cloth_split c t)).
Proof.
  intros c t.
  unfold cloth_joint.
  destruct (cloth_split_join c t) as [Hl Hr].
  rewrite Hl, Hr.
  reflexivity.
Qed.

(* WITNESS {"claimId":"0007-clothoid-first-cook","topic":"overlay","lemma":"cloth_joint_end","title":"Mode D clothoid host joint: two consecutive host ClothoidEggs meet at cloth_eval A 1 = cloth_eval B 0; concat incidence not interior I_ok Hit; first-cook Hit stays A times B","file":"theories/ClothoidCookMkClothoid.v","witness":"0007-clothoid-first-cook","board":"ADR-0007"} *)
Theorem cloth_joint_end :
  forall A B : ClothoidEgg,
    cloth_joint A B ->
    cloth_eval A 1 = cloth_eval B 0.
Proof.
  intros A B H.
  unfold cloth_joint in H.
  exact H.
Qed.

(* WITNESS {"claimId":"0007-clothoid-first-cook","topic":"overlay","lemma":"cloth_joint_is_endpoint_hit","title":"Mode D clothoid joint IResult is IHit (cloth_eval A 1) 1 0 under cloth_joint; concat incidence not interior I_ok Hit; not host I_ok remint","file":"theories/ClothoidCookMkClothoid.v","witness":"0007-clothoid-first-cook","board":"ADR-0007"} *)
Theorem cloth_joint_is_endpoint_hit :
  forall A B : ClothoidEgg,
    cloth_joint A B ->
    cloth_joint_hit A B = IHit (cloth_eval A 1) 1 0
    /\ cloth_joint_hit A B = IHit (cloth_eval B 0) 1 0.
Proof.
  intros A B H.
  unfold cloth_joint_hit.
  split; [reflexivity|].
  unfold cloth_joint in H.
  rewrite H.
  reflexivity.
Qed.

Definition locked_cloth_host_1 : ClothoidEgg :=
  fst (cloth_split locked_cloth_A locked_cloth_ti).

Definition locked_cloth_host_2 : ClothoidEgg :=
  snd (cloth_split locked_cloth_A locked_cloth_ti).

Lemma locked_cloth_host_joint :
  cloth_joint locked_cloth_host_1 locked_cloth_host_2.
Proof.
  unfold locked_cloth_host_1, locked_cloth_host_2.
  apply cloth_split_cloth_joint.
Qed.

Lemma locked_cloth_host_joint_end :
  cloth_eval locked_cloth_host_1 1 = cloth_eval locked_cloth_host_2 0.
Proof.
  apply cloth_joint_end.
  exact locked_cloth_host_joint.
Qed.

Lemma locked_cloth_host_joint_is_endpoint_hit :
  cloth_joint_hit locked_cloth_host_1 locked_cloth_host_2
    = IHit (cloth_eval locked_cloth_host_1 1) 1 0
  /\ cloth_joint_hit locked_cloth_host_1 locked_cloth_host_2
       = IHit (cloth_eval locked_cloth_host_2 0) 1 0.
Proof.
  destruct (cloth_joint_is_endpoint_hit locked_cloth_host_1
              locked_cloth_host_2 locked_cloth_host_joint) as [H1 H2].
  split; [exact H1|exact H2].
Qed.

(* First-cook interior Hit stays A×B. Those meet in the interior, not
   as a Mode D endpoint joint. *)
Lemma locked_cloth_AB_not_joint :
  ~ cloth_joint locked_cloth_A locked_cloth_B.
Proof.
  unfold cloth_joint.
  intros H.
  apply (f_equal px) in H.
  unfold locked_cloth_A, locked_cloth_B, mk_cloth,
         cloth_eval, cloth_eval_seed in H.
  cbn [px py cloth_p0 cloth_k0 cloth_k1 cloth_L cloth_th0] in H.
  lra.
Qed.

Lemma locked_cloth_joint_hit_neq_first_cook_hit :
  cloth_joint_hit locked_cloth_host_1 locked_cloth_host_2
    <> locked_mkclothoid_hit.
Proof.
  unfold cloth_joint_hit, locked_mkclothoid_hit.
  intros H.
  inversion H.
  lra.
Qed.

Print Assumptions cloth_eval_at_0.
Print Assumptions cloth_eval_at_1_mk.
Print Assumptions cloth_wf_of_p1.
Print Assumptions cloth_wf_mk.
Print Assumptions cloth_split_join.
Print Assumptions cloth_split_left_start.
Print Assumptions cloth_split_right_end.
Print Assumptions cloth_eval_L0.
Print Assumptions cloth_eval_kappa0.
Print Assumptions cloth_th0_moves_y.
Print Assumptions locked_cloth_A_p1_is_gamma1.
Print Assumptions locked_cloth_B_p1_is_gamma1.
Print Assumptions locked_cloth_A_heading_small.
Print Assumptions locked_cloth_B_heading_small.
Print Assumptions locked_cloth_A_at_ti.
Print Assumptions locked_cloth_B_at_tj.
Print Assumptions locked_cloth_ti_neq_tj.
Print Assumptions locked_mkclothoid_I_ok.
Print Assumptions locked_mkclothoid_hit_neq_endpoint_chord_x.
Print Assumptions locked_cloth_eval_neq_endpoint_chord.
Print Assumptions locked_letter_eggs_wf.
Print Assumptions cooked_mkclothoid_try.
Print Assumptions cook_hit_clothoids_shares_hen.
Print Assumptions cooked_mkclothoid_shares.
Print Assumptions cooked_mkclothoid_children_are_clothoid.
Print Assumptions interpolant_pair_mkclothoid.
Print Assumptions mkclothoid_mixed_still_decline.
Print Assumptions locked_intake_egg_self_hit.
Print Assumptions ticket_0007_clothoid_first_cook_qed_or_qex.
Print Assumptions cloth_split_cloth_joint.
Print Assumptions cloth_joint_end.
Print Assumptions cloth_joint_is_endpoint_hit.
Print Assumptions locked_cloth_host_joint.
Print Assumptions locked_cloth_host_joint_end.
Print Assumptions locked_cloth_host_joint_is_endpoint_hit.
Print Assumptions locked_cloth_AB_not_joint.
Print Assumptions locked_cloth_joint_hit_neq_first_cook_hit.
