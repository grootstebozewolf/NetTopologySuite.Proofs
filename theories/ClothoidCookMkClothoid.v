(* ============================================================================
   NetTopologySuite.Proofs.ClothoidCookMkClothoid
   ----------------------------------------------------------------------------
   ADR-0007 letter: clothoid×clothoid first-cook / Hit arm
   (claimId 0007-clothoid-first-cook). Same claimId, witness, ticket.

   Host gamma is the Fresnel clothoid in SheetHenClothoidEgg. The
   parameterisation is OUR choice (egg header), not an ISO formula.
   Planar. sigma is the sign of ref1×ref2. Endpoints are gamma(0)
   and gamma(1). Fixtures go through mk_cloth only.

   Fixture: mirror Fresnel windows, A = 1.
     A: east frame at (-1/2, 0), sd = 0, ed = 1.
        gamma_A(t) = (-1/2 + Cx(t), Cy(t))
     B: west frame at (1/2, 0), sd = 1, ed = 0 (sigma = -1).
        gamma_B(u) = (1/2 - Cx(1-u), Cy(1-u))
   ti is the IVT root of Cx(t) = 1/2 on [1/2, 3/5]; tj = 1 - ti.
   Both images meet at (0, Cy(ti)). That point is not the named
   endpoint-chord crossing locked_cloth_chord_x, and gamma_A(ti) is
   not the endpoint chord sampled at ti (that obligation fails if
   gamma were endpoint lerp).

   Mode D host joint; first-cook interior Hit stays A×B;
   this is split-children meet, not example5.

   MkOutOfScope EggClothoid stays Decline. Mixed clothoid×chord
   stays Decline. SIN / ellipse / spiral / geodesic stay out of
   first cook. rho / Campaign / Fresnel-as-noding stay parked.
   first_cook_scope is not expanded.

   WITNESS topic: overlay · claimId: 0007-clothoid-first-cook
   witness: 0007-clothoid-first-cook
   board: ADR-0007
   Stdlib RiemannInt plus IVT. Print Assumptions shows classic
   (Category C). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis5.
From NTS.Proofs Require Import Distance SheetHenCook.
Local Open Scope R_scope.

Definition locked_cloth_A : ClothoidEgg :=
  mk_cloth (place_east (mkPoint (-1 / 2) 0)) 1 0 1 None None.

Definition locked_cloth_B : ClothoidEgg :=
  mk_cloth (place_west (mkPoint (1 / 2) 0)) 1 1 0 None None.

Definition locked_cloth_gap (t : R) : R := cloth_Cx t - 1 / 2.

Lemma half_lt_three_fifth : 1 / 2 < 3 / 5.
Proof. lra. Qed.

Lemma locked_cloth_gap_cont :
  forall a, 1 / 2 <= a <= 3 / 5 -> continuity_pt locked_cloth_gap a.
Proof.
  intros a Ha. unfold locked_cloth_gap. apply cloth_axis_gap_cont. exact Ha.
Qed.

Lemma locked_cloth_gap_half : locked_cloth_gap (1 / 2) < 0.
Proof.
  unfold locked_cloth_gap. pose proof cloth_Cx_half_lt. lra.
Qed.

Lemma locked_cloth_gap_35 : 0 < locked_cloth_gap (3 / 5).
Proof.
  unfold locked_cloth_gap. pose proof cloth_Cx_three_fifth_gt. lra.
Qed.

Definition locked_cloth_ti_sig :
  {z : R | 1 / 2 <= z <= 3 / 5 /\ locked_cloth_gap z = 0} :=
  IVT_interv locked_cloth_gap (1 / 2) (3 / 5)
    locked_cloth_gap_cont half_lt_three_fifth
    locked_cloth_gap_half locked_cloth_gap_35.

Definition locked_cloth_ti : R := proj1_sig locked_cloth_ti_sig.

Definition locked_cloth_tj : R := 1 - locked_cloth_ti.

Lemma locked_cloth_ti_bounds : 1 / 2 <= locked_cloth_ti <= 3 / 5.
Proof.
  unfold locked_cloth_ti. apply (proj1 (proj2_sig locked_cloth_ti_sig)).
Qed.

Lemma locked_cloth_ti_Cx : cloth_Cx locked_cloth_ti = 1 / 2.
Proof.
  unfold locked_cloth_ti.
  pose proof (proj2 (proj2_sig locked_cloth_ti_sig)) as Hz.
  unfold locked_cloth_gap in Hz. simpl in Hz.
  apply Rminus_diag_uniq. exact Hz.
Qed.

Lemma locked_cloth_ti_gt_half : 1 / 2 < locked_cloth_ti.
Proof.
  destruct (proj1 locked_cloth_ti_bounds) as [Hlt|Heq].
  - exact Hlt.
  - exfalso.
    assert (cloth_Cx (1 / 2) = 1 / 2).
    { replace (cloth_Cx (1 / 2)) with (cloth_Cx locked_cloth_ti).
      - apply locked_cloth_ti_Cx.
      - rewrite <- Heq. reflexivity. }
    pose proof cloth_Cx_half_lt. lra.
Qed.

Definition locked_cloth_hit_pt : Point :=
  mkPoint 0 (cloth_Cy locked_cloth_ti).

Definition locked_cloth_chord_x : Point :=
  mkPoint 0 (cloth_Cy 1 / (2 * cloth_Cx 1)).

Definition locked_cloth_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkClothoid locked_cloth_A).

Definition locked_cloth_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkClothoid locked_cloth_B).

Lemma locked_cloth_A_wf : cloth_wf locked_cloth_A.
Proof.
  unfold locked_cloth_A. apply cloth_wf_mk.
  - lra.
  - rewrite east_h2. lra.
  - rewrite east_cross. lra.
  - left. split; reflexivity.
Qed.

Lemma locked_cloth_B_wf : cloth_wf locked_cloth_B.
Proof.
  unfold locked_cloth_B. apply cloth_wf_mk.
  - lra.
  - rewrite west_h2. lra.
  - rewrite west_cross. lra.
  - left. split; reflexivity.
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
  forall t, cloth_th locked_cloth_A t = t * t / 2.
Proof.
  intros t. unfold locked_cloth_A. apply th_east_01.
Qed.

Lemma locked_cloth_B_th :
  forall t, cloth_th locked_cloth_B t = - (1 - t) * (1 - t) / 2.
Proof.
  intros t. unfold locked_cloth_B. apply th_west_10.
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
  forall t, 0 <= t <= 1 -> Rabs (cloth_th locked_cloth_A t) <= 1 / 2.
Proof.
  intros t Ht.
  rewrite locked_cloth_A_th.
  pose proof (locked_unit_sqr t Ht) as Ht2.
  assert (Hnn : 0 <= t * t / 2).
  { destruct Ht2 as [H0 _]. unfold Rdiv.
    apply Rmult_le_pos; [exact H0 | apply Rlt_le; apply Rinv_0_lt_compat; lra]. }
  rewrite (Rabs_right _ (Rle_ge _ _ Hnn)).
  destruct Ht2 as [_ H1].
  unfold Rdiv. apply Rmult_le_compat_r;
    [apply Rlt_le; apply Rinv_0_lt_compat; lra | exact H1].
Qed.

Lemma locked_cloth_B_heading_small :
  forall t, 0 <= t <= 1 -> Rabs (cloth_th locked_cloth_B t) <= 1 / 2.
Proof.
  intros t Ht.
  rewrite locked_cloth_B_th.
  assert (Ht1 : 0 <= 1 - t <= 1) by lra.
  pose proof (locked_unit_sqr (1 - t) Ht1) as Ht2.
  assert (Hnn : - (1 - t) * (1 - t) / 2 <= 0).
  { destruct Ht2 as [H0 _]. unfold Rdiv.
    assert (0 <= (1 - t) * (1 - t) / 2).
    { apply Rmult_le_pos; [exact H0 | apply Rlt_le; apply Rinv_0_lt_compat; lra]. }
    lra. }
  rewrite (Rabs_left1 _ Hnn).
  destruct Ht2 as [_ H1].
  replace (- (- (1 - t) * (1 - t) / 2)) with ((1 - t) * (1 - t) / 2) by field.
  unfold Rdiv. apply Rmult_le_compat_r;
    [apply Rlt_le; apply Rinv_0_lt_compat; lra | exact H1].
Qed.

Lemma locked_cloth_ti_in_01 : 0 <= locked_cloth_ti <= 1.
Proof.
  pose proof locked_cloth_ti_bounds. lra.
Qed.

Lemma locked_cloth_tj_in_01 : 0 <= locked_cloth_tj <= 1.
Proof.
  unfold locked_cloth_tj.
  pose proof locked_cloth_ti_gt_half.
  pose proof locked_cloth_ti_bounds. lra.
Qed.

Lemma locked_cloth_ti_neq_tj : locked_cloth_ti <> locked_cloth_tj.
Proof.
  unfold locked_cloth_tj. pose proof locked_cloth_ti_gt_half. lra.
Qed.

Lemma locked_cloth_A_at_ti :
  cloth_eval locked_cloth_A locked_cloth_ti = locked_cloth_hit_pt.
Proof.
  unfold locked_cloth_A, locked_cloth_hit_pt.
  rewrite eval_east_01. cbn [px py].
  rewrite locked_cloth_ti_Cx.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_cloth_B_at_tj :
  cloth_eval locked_cloth_B locked_cloth_tj = locked_cloth_hit_pt.
Proof.
  unfold locked_cloth_B, locked_cloth_tj, locked_cloth_hit_pt.
  rewrite eval_west_10. cbn [px py].
  replace (1 - (1 - locked_cloth_ti)) with locked_cloth_ti by ring.
  rewrite locked_cloth_ti_Cx.
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

Lemma locked_A_at_0 :
  cloth_eval locked_cloth_A 0 = mkPoint (-1 / 2) 0.
Proof.
  unfold locked_cloth_A. rewrite eval_east_01. cbn [px py].
  rewrite cloth_Cx_0, cloth_Cy_0. apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_A_at_1 :
  cloth_eval locked_cloth_A 1 =
    mkPoint (-1 / 2 + cloth_Cx 1) (cloth_Cy 1).
Proof.
  unfold locked_cloth_A. rewrite eval_east_01. cbn [px py].
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_B_at_0 :
  cloth_eval locked_cloth_B 0 =
    mkPoint (1 / 2 - cloth_Cx 1) (cloth_Cy 1).
Proof.
  unfold locked_cloth_B. rewrite eval_west_10. cbn [px py].
  replace (1 - 0) with 1 by ring.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_B_at_1 :
  cloth_eval locked_cloth_B 1 = mkPoint (1 / 2) 0.
Proof.
  unfold locked_cloth_B. rewrite eval_west_10. cbn [px py].
  replace (1 - 1) with 0 by ring.
  rewrite cloth_Cx_0, cloth_Cy_0. apply (f_equal2 mkPoint); ring.
Qed.

Lemma cloth_Cx_1_nz : cloth_Cx 1 <> 0.
Proof.
  pose proof cloth_Cx_ge_7_8. lra.
Qed.

(* Endpoint chords meet at the named point locked_cloth_chord_x,
   which is not the interior Hit. *)
Lemma locked_mkclothoid_hit_neq_endpoint_chord_x :
  let ca := mkChordEgg (cloth_p0 locked_cloth_A) (cloth_p1 locked_cloth_A) in
  let cb := mkChordEgg (cloth_p0 locked_cloth_B) (cloth_p1 locked_cloth_B) in
  let sA := 1 / (2 * cloth_Cx 1) in
  let sB := 1 - sA in
  chord_eval ca sA = locked_cloth_chord_x /\
  chord_eval cb sB = locked_cloth_chord_x /\
  locked_cloth_chord_x <> locked_cloth_hit_pt.
Proof.
  pose proof cloth_Cx_1_nz as Hnz.
  unfold locked_cloth_chord_x, locked_cloth_hit_pt, cloth_p0, cloth_p1.
  split; [|split].
  - unfold chord_eval. rewrite locked_A_at_0, locked_A_at_1.
    cbn [ce_p0 ce_p1 px py].
    apply (f_equal2 mkPoint); field; exact Hnz.
  - unfold chord_eval. rewrite locked_B_at_0, locked_B_at_1.
    cbn [ce_p0 ce_p1 px py].
    apply (f_equal2 mkPoint); field; exact Hnz.
  - intros Heq. apply (f_equal py) in Heq. cbn [py] in Heq.
    assert (Hti : 0 <= locked_cloth_ti <= 3 / 5).
    { pose proof locked_cloth_ti_bounds. lra. }
    assert (Hy_ti : cloth_Cy locked_cloth_ti <= cloth_Cy (3 / 5)).
    { apply cloth_Cy_mono_01; lra. }
    assert (Hy35 : cloth_Cy (3 / 5) <= 27 / 750) by apply cloth_Cy_three_fifth_le.
    assert (Hlt : 27 / 750 < 55 / 672).
    { assert (27 / 750 = 18144 / 504000) by field.
      assert (55 / 672 = 41250 / 504000) by field.
      lra. }
    pose proof cloth_Cy_ge_55_336 as Hcy.
    assert (Heq672 : 55 / 336 / 2 = 55 / 672) by field.
    assert (Hhalf : 55 / 672 <= cloth_Cy 1 / 2).
    { rewrite <- Heq672. unfold Rdiv.
      apply Rmult_le_compat_r;
        [apply Rlt_le; apply Rinv_0_lt_compat; lra | exact Hcy]. }
    assert (Hcx : 7 / 8 <= cloth_Cx 1 <= 1).
    { split; [apply cloth_Cx_ge_7_8 | apply cloth_Cx_le_1]. }
    assert (Hcypos : 0 < cloth_Cy 1) by lra.
    assert (Hscale : cloth_Cy 1 / 2 <= cloth_Cy 1 / (2 * cloth_Cx 1)).
    { unfold Rdiv. apply Rmult_le_compat_l; [lra|].
      apply Rinv_le_contravar.
      - apply Rmult_lt_0_compat; lra.
      - replace 2 with (2 * 1) at 2 by field.
        apply Rmult_le_compat_l; [lra | apply (proj2 Hcx)]. }
    lra.
Qed.

(* gamma(ti) is not the endpoint chord at the same parameter.
   An endpoint lerp would make this equality, so the obligation fails
   under that reading of eval. *)
Lemma locked_cloth_eval_neq_endpoint_chord :
  cloth_eval locked_cloth_A locked_cloth_ti
    <> chord_eval
         (mkChordEgg (cloth_eval locked_cloth_A 0)
                     (cloth_eval locked_cloth_A 1))
         locked_cloth_ti.
Proof.
  intros Heq.
  apply (f_equal py) in Heq.
  unfold chord_eval in Heq.
  rewrite locked_A_at_0, locked_A_at_1 in Heq.
  rewrite locked_cloth_A_at_ti in Heq.
  unfold locked_cloth_hit_pt in Heq.
  cbn [ce_p0 ce_p1 px py] in Heq.
  assert (Hti : 0 <= locked_cloth_ti <= 3 / 5).
  { pose proof locked_cloth_ti_bounds. lra. }
  assert (Hy_ti : cloth_Cy locked_cloth_ti <= 27 / 750).
  { apply Rle_trans with (cloth_Cy (3 / 5)).
    - apply cloth_Cy_mono_01; lra.
    - apply cloth_Cy_three_fifth_le. }
  assert (Hlt : 27 / 750 < 55 / 672).
  { assert (27 / 750 = 18144 / 504000) by field.
    assert (55 / 672 = 41250 / 504000) by field. lra. }
  pose proof cloth_Cy_ge_55_336 as Hcy.
  assert (Heq672 : 55 / 336 / 2 = 55 / 672) by field.
  assert (Hhalf : 55 / 672 <= / 2 * cloth_Cy 1).
  { rewrite <- Heq672.
    replace (55 / 336 / 2) with (/ 2 * (55 / 336)) by field.
    apply Rmult_le_compat_l;
      [apply Rlt_le; apply Rinv_0_lt_compat; lra | exact Hcy]. }
  pose proof locked_cloth_ti_gt_half as Hgt.
  assert (Hcypos : 0 < cloth_Cy 1) by lra.
  assert (Hinv : / 2 < locked_cloth_ti).
  { assert (/ 2 = 1 / 2) by field. lra. }
  assert (Hbig : / 2 * cloth_Cy 1 < locked_cloth_ti * cloth_Cy 1).
  { apply Rmult_lt_compat_r; [exact Hcypos | exact Hinv]. }
  assert (Hchord : (1 - locked_cloth_ti) * 0
                    + locked_cloth_ti * cloth_Cy 1
                    = locked_cloth_ti * cloth_Cy 1) by ring.
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
  split; [apply cloth_wf_split_left; exact locked_cloth_A_wf
         |apply cloth_wf_split_right; exact locked_cloth_A_wf].
Qed.

Lemma cloth_split_changes_k_on_locked_A :
  cloth_ed (fst (cloth_split locked_cloth_A locked_cloth_ti))
    <> cloth_ed locked_cloth_A /\
  cloth_sd (snd (cloth_split locked_cloth_A locked_cloth_ti))
    <> cloth_sd locked_cloth_A.
Proof.
  unfold cloth_split, locked_cloth_A. cbn [fst snd].
  unfold mk_cloth. cbn [cloth_sd cloth_ed].
  split.
  - replace (0 + locked_cloth_ti * (1 - 0)) with locked_cloth_ti by ring.
    pose proof locked_cloth_ti_bounds. lra.
  - replace (0 + locked_cloth_ti * (1 - 0)) with locked_cloth_ti by ring.
    pose proof locked_cloth_ti_gt_half. lra.
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

(* WITNESS {"claimId":"0007-clothoid-first-cook","topic":"overlay","lemma":"locked_mkclothoid_I_ok","title":"Host I_ok Hits two MkClothoid chickens on the locked crossing Fresnel clothoid pair","file":"theories/ClothoidCookMkClothoid.v","witness":"0007-clothoid-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-clothoid-first-cook","topic":"overlay","lemma":"cooked_mkclothoid_try","title":"try_cook_hit mints MkClothoid hens on the locked clothoid Hit","file":"theories/ClothoidCookMkClothoid.v","witness":"0007-clothoid-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-clothoid-first-cook","topic":"overlay","lemma":"ticket_0007_clothoid_first_cook_qed_or_qex","title":"Clothoid times clothoid is first cook with a locked MkClothoid IHit that try_cook_hit mints (QED) or clothoid times clothoid stays QEX (QEX); discharged QED; Fresnel interpolant not chord-parameter; tags and mixed stay Decline","file":"theories/ClothoidCookMkClothoid.v","witness":"0007-clothoid-first-cook","board":"ADR-0007"} *)
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
   first_cook_scope EggNurbs EggNurbs /\
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
  split; [exact nurbs_nurbs_first_cook_scope|].
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
  unfold cloth_joint. intros H.
  apply (f_equal px) in H.
  rewrite locked_A_at_1, locked_B_at_0 in H.
  cbn [px] in H.
  pose proof cloth_Cx_ge_7_8. lra.
Qed.

Lemma locked_cloth_joint_hit_neq_first_cook_hit :
  cloth_joint_hit locked_cloth_host_1 locked_cloth_host_2
    <> locked_mkclothoid_hit.
Proof.
  assert (Hti : locked_cloth_ti < 1).
  { pose proof locked_cloth_ti_bounds. lra. }
  assert (Htj : 0 < locked_cloth_tj).
  { unfold locked_cloth_tj. pose proof locked_cloth_ti_bounds. lra. }
  unfold cloth_joint_hit, locked_mkclothoid_hit.
  intros H. inversion H. lra.
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
