(* ============================================================================
   NetTopologySuite.Proofs.SheetHenClothoidFrames
   ----------------------------------------------------------------------------
   Unit frames and the locked intake bag. Modelling choice is OUR
   choice, not an ISO formula (SheetHenClothoidCore): planar gamma(t)
   = P(sd + t*(ed-sd)), sigma = sign of ref1 x ref2. East is sigma
   = +1 (the oracle right-handed frame). The locked bag is the law;
   parameterised WKT intake is out of scope.
   No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals RiemannInt Ranalysis1 Rtrigo1 Rtrigo_alt
  Ratan Lra Arith.Factorial.
From Stdlib Require Import Ranalysis_reg.
From NTS.Proofs Require Import Distance SheetHenClothoidCore SheetHenClothoidBounds.
Local Open Scope R_scope.

(* Unit frames. East is the oracle right-handed choice (sigma = +1).
   West flips the first vector, so sigma = -1. North is a quarter
   turn of the first vector, still sigma = +1. *)

Definition place_east (o : Point) : AffPlace :=
  mkAffPlace o (mkPoint 1 0) (mkPoint 0 1).

Definition place_west (o : Point) : AffPlace :=
  mkAffPlace o (mkPoint (-1) 0) (mkPoint 0 1).

Definition place_north (o : Point) : AffPlace :=
  mkAffPlace o (mkPoint 0 1) (mkPoint (-1) 0).

Lemma east_h2 : forall o, aff_h2 (place_east o) = 1.
Proof. intros o. unfold aff_h2, place_east. cbn. ring. Qed.

Lemma east_cross : forall o, aff_cross (place_east o) = 1.
Proof. intros o. unfold aff_cross, place_east. cbn. ring. Qed.

Lemma west_h2 : forall o, aff_h2 (place_west o) = 1.
Proof. intros o. unfold aff_h2, place_west. cbn. ring. Qed.

Lemma west_cross : forall o, aff_cross (place_west o) = -1.
Proof. intros o. unfold aff_cross, place_west. cbn. ring. Qed.

Lemma north_h2 : forall o, aff_h2 (place_north o) = 1.
Proof. intros o. unfold aff_h2, place_north. cbn. ring. Qed.

Lemma north_cross : forall o, aff_cross (place_north o) = 1.
Proof. intros o. unfold aff_cross, place_north. cbn. ring. Qed.

Lemma east_sigma : forall o,
  cloth_sigma (mk_cloth (place_east o) 1 0 1 None None) = 1.
Proof.
  intros o. unfold cloth_sigma.
  replace (cloth_cross (mk_cloth (place_east o) 1 0 1 None None)) with 1.
  - destruct (Rle_dec 0 1) as [_|Hn]; [reflexivity | lra].
  - unfold cloth_cross, mk_cloth. cbn. symmetry. apply east_cross.
Qed.

Lemma west_sigma : forall o,
  cloth_sigma (mk_cloth (place_west o) 1 1 0 None None) = -1.
Proof.
  intros o. unfold cloth_sigma.
  replace (cloth_cross (mk_cloth (place_west o) 1 1 0 None None)) with (-1).
  - destruct (Rle_dec 0 (-1)) as [Hle|Hn]; [lra | reflexivity].
  - unfold cloth_cross, mk_cloth. cbn. symmetry. apply west_cross.
Qed.

Lemma north_sigma : forall o,
  cloth_sigma (mk_cloth (place_north o) 1 0 1 None None) = 1.
Proof.
  intros o. unfold cloth_sigma.
  replace (cloth_cross (mk_cloth (place_north o) 1 0 1 None None)) with 1.
  - destruct (Rle_dec 0 1) as [_|Hn]; [reflexivity | lra].
  - unfold cloth_cross, mk_cloth. cbn. symmetry. apply north_cross.
Qed.

Lemma east_vx : forall o s,
  cloth_vx (mk_cloth (place_east o) 1 0 1 None None) s
    = fresnel_cx_integrand s.
Proof.
  intros o s.
  set (c := mk_cloth (place_east o) 1 0 1 None None).
  unfold cloth_vx, cloth_cos0, cloth_sin0, cloth_hypot, cloth_h2, cloth_psi.
  assert (Hs : cloth_sigma c = 1) by apply east_sigma.
  rewrite Hs.
  unfold c. cbn [cloth_place cloth_A mk_cloth aff_ref1 place_east px py].
  rewrite east_h2. rewrite sqrt_1.
  assert (Epsi : 1 * s * s / (2 * 1 * 1) = fresnel_angle s).
  { unfold fresnel_angle. field. }
  rewrite Epsi. unfold fresnel_cx_integrand. field.
Qed.

Lemma east_vy : forall o s,
  cloth_vy (mk_cloth (place_east o) 1 0 1 None None) s
    = fresnel_cy_integrand s.
Proof.
  intros o s.
  set (c := mk_cloth (place_east o) 1 0 1 None None).
  unfold cloth_vy, cloth_cos0, cloth_sin0, cloth_hypot, cloth_h2, cloth_psi.
  assert (Hs : cloth_sigma c = 1) by apply east_sigma.
  rewrite Hs.
  unfold c. cbn [cloth_place cloth_A mk_cloth aff_ref1 place_east px py].
  rewrite east_h2. rewrite sqrt_1.
  assert (Epsi : 1 * s * s / (2 * 1 * 1) = fresnel_angle s).
  { unfold fresnel_angle. field. }
  rewrite Epsi. unfold fresnel_cy_integrand. field.
Qed.

Lemma west_vx : forall o s,
  cloth_vx (mk_cloth (place_west o) 1 1 0 None None) s
    = - fresnel_cx_integrand s.
Proof.
  intros o s.
  set (c := mk_cloth (place_west o) 1 1 0 None None).
  unfold cloth_vx, cloth_cos0, cloth_sin0, cloth_hypot, cloth_h2, cloth_psi.
  assert (Hs : cloth_sigma c = -1) by apply west_sigma.
  rewrite Hs.
  unfold c. cbn [cloth_place cloth_A mk_cloth aff_ref1 place_west px py].
  rewrite west_h2. rewrite sqrt_1.
  assert (Epsi : -1 * s * s / (2 * 1 * 1) = - fresnel_angle s).
  { unfold fresnel_angle. field. }
  rewrite Epsi. rewrite cos_neg.
  unfold fresnel_cx_integrand. field.
Qed.

Lemma west_vy : forall o s,
  cloth_vy (mk_cloth (place_west o) 1 1 0 None None) s
    = fresnel_cy_integrand s.
Proof.
  intros o s.
  set (c := mk_cloth (place_west o) 1 1 0 None None).
  unfold cloth_vy, cloth_cos0, cloth_sin0, cloth_hypot, cloth_h2, cloth_psi.
  assert (Hs : cloth_sigma c = -1) by apply west_sigma.
  rewrite Hs.
  unfold c. cbn [cloth_place cloth_A mk_cloth aff_ref1 place_west px py].
  rewrite west_h2. rewrite sqrt_1.
  assert (Epsi : -1 * s * s / (2 * 1 * 1) = - fresnel_angle s).
  { unfold fresnel_angle. field. }
  rewrite Epsi. rewrite sin_neg.
  unfold fresnel_cy_integrand. field.
Qed.

Lemma north_vx : forall o s,
  cloth_vx (mk_cloth (place_north o) 1 0 1 None None) s
    = - fresnel_cy_integrand s.
Proof.
  intros o s.
  set (c := mk_cloth (place_north o) 1 0 1 None None).
  unfold cloth_vx, cloth_cos0, cloth_sin0, cloth_hypot, cloth_h2, cloth_psi.
  assert (Hs : cloth_sigma c = 1) by apply north_sigma.
  rewrite Hs.
  unfold c. cbn [cloth_place cloth_A mk_cloth aff_ref1 place_north px py].
  rewrite north_h2. rewrite sqrt_1.
  assert (Epsi : 1 * s * s / (2 * 1 * 1) = fresnel_angle s).
  { unfold fresnel_angle. field. }
  rewrite Epsi. unfold fresnel_cy_integrand. field.
Qed.

Lemma north_vy : forall o s,
  cloth_vy (mk_cloth (place_north o) 1 0 1 None None) s
    = fresnel_cx_integrand s.
Proof.
  intros o s.
  set (c := mk_cloth (place_north o) 1 0 1 None None).
  unfold cloth_vy, cloth_cos0, cloth_sin0, cloth_hypot, cloth_h2, cloth_psi.
  assert (Hs : cloth_sigma c = 1) by apply north_sigma.
  rewrite Hs.
  unfold c. cbn [cloth_place cloth_A mk_cloth aff_ref1 place_north px py].
  rewrite north_h2. rewrite sqrt_1.
  assert (Epsi : 1 * s * s / (2 * 1 * 1) = fresnel_angle s).
  { unfold fresnel_angle. field. }
  rewrite Epsi. unfold fresnel_cx_integrand. field.
Qed.

Lemma east_int_x : forall o s,
  RInt_cont (cloth_vx (mk_cloth (place_east o) 1 0 1 None None))
    (cloth_vx_cont _) 0 s = cloth_Cx s.
Proof.
  intros o s. unfold cloth_Cx.
  apply RInt_cont_ext. intros x. apply east_vx.
Qed.

Lemma east_int_y : forall o s,
  RInt_cont (cloth_vy (mk_cloth (place_east o) 1 0 1 None None))
    (cloth_vy_cont _) 0 s = cloth_Cy s.
Proof.
  intros o s. unfold cloth_Cy.
  apply RInt_cont_ext. intros x. apply east_vy.
Qed.

Lemma west_int_x : forall o s,
  RInt_cont (cloth_vx (mk_cloth (place_west o) 1 1 0 None None))
    (cloth_vx_cont _) 0 s = - cloth_Cx s.
Proof.
  intros o s.
  rewrite (RInt_cont_ext _ (fun u => - fresnel_cx_integrand u)
    _ fresnel_cx_neg_cont 0 s).
  2:{ intros x. apply west_vx. }
  rewrite (RInt_cont_opp fresnel_cx_integrand fresnel_cx_cont
    fresnel_cx_neg_cont 0 s).
  unfold cloth_Cx. reflexivity.
Qed.

Lemma west_int_y : forall o s,
  RInt_cont (cloth_vy (mk_cloth (place_west o) 1 1 0 None None))
    (cloth_vy_cont _) 0 s = cloth_Cy s.
Proof.
  intros o s. unfold cloth_Cy.
  apply RInt_cont_ext. intros x. apply west_vy.
Qed.

Lemma north_int_x : forall o s,
  RInt_cont (cloth_vx (mk_cloth (place_north o) 1 0 1 None None))
    (cloth_vx_cont _) 0 s = - cloth_Cy s.
Proof.
  intros o s.
  assert (Hcy : forall x, continuity_pt (fun u => - fresnel_cy_integrand u) x).
  { intro x. change (continuity_pt (- fresnel_cy_integrand)%F x).
    apply continuity_pt_opp. apply fresnel_cy_cont. }
  rewrite (RInt_cont_ext _ (fun u => - fresnel_cy_integrand u) _ Hcy 0 s).
  2:{ intros x. apply north_vx. }
  rewrite (RInt_cont_opp fresnel_cy_integrand fresnel_cy_cont Hcy 0 s).
  unfold cloth_Cy. reflexivity.
Qed.

Lemma north_int_y : forall o s,
  RInt_cont (cloth_vy (mk_cloth (place_north o) 1 0 1 None None))
    (cloth_vy_cont _) 0 s = cloth_Cx s.
Proof.
  intros o s. unfold cloth_Cx.
  apply RInt_cont_ext. intros x. apply north_vy.
Qed.

Lemma eval_east_01 : forall o t,
  cloth_eval (mk_cloth (place_east o) 1 0 1 None None) t
    = mkPoint (px o + cloth_Cx t) (py o + cloth_Cy t).
Proof.
  intros o t.
  unfold cloth_eval, cloth_P, cloth_Px, cloth_Py, cloth_s.
  cbn [cloth_sd cloth_ed cloth_place mk_cloth aff_loc place_east].
  replace (0 + t * (1 - 0)) with t by ring.
  rewrite east_int_x, east_int_y.
  reflexivity.
Qed.

Lemma eval_west_10 : forall o t,
  cloth_eval (mk_cloth (place_west o) 1 1 0 None None) t
    = mkPoint (px o - cloth_Cx (1 - t)) (py o + cloth_Cy (1 - t)).
Proof.
  intros o t.
  unfold cloth_eval, cloth_P, cloth_Px, cloth_Py, cloth_s.
  cbn [cloth_sd cloth_ed cloth_place mk_cloth aff_loc place_west].
  replace (1 + t * (0 - 1)) with (1 - t) by ring.
  rewrite west_int_x, west_int_y.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma eval_north_01 : forall o t,
  cloth_eval (mk_cloth (place_north o) 1 0 1 None None) t
    = mkPoint (px o - cloth_Cy t) (py o + cloth_Cx t).
Proof.
  intros o t.
  unfold cloth_eval, cloth_P, cloth_Px, cloth_Py, cloth_s.
  cbn [cloth_sd cloth_ed cloth_place mk_cloth aff_loc place_north].
  replace (0 + t * (1 - 0)) with t by ring.
  rewrite north_int_x, north_int_y.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma th_east_01 : forall o t,
  cloth_th (mk_cloth (place_east o) 1 0 1 None None) t = t * t / 2.
Proof.
  intros o t.
  set (c := mk_cloth (place_east o) 1 0 1 None None).
  unfold cloth_th, cloth_psi, cloth_s.
  assert (Hs : cloth_sigma c = 1) by apply east_sigma.
  rewrite Hs. unfold c.
  cbn [cloth_sd cloth_ed cloth_A mk_cloth].
  replace (0 + t * (1 - 0)) with t by ring.
  field.
Qed.

Lemma th_west_10 : forall o t,
  cloth_th (mk_cloth (place_west o) 1 1 0 None None) t
    = - (1 - t) * (1 - t) / 2.
Proof.
  intros o t.
  set (c := mk_cloth (place_west o) 1 1 0 None None).
  unfold cloth_th, cloth_psi, cloth_s.
  assert (Hs : cloth_sigma c = -1) by apply west_sigma.
  rewrite Hs. unfold c.
  cbn [cloth_sd cloth_ed cloth_A mk_cloth].
  replace (1 + t * (0 - 1)) with (1 - t) by ring.
  field.
Qed.

Definition locked_clothoid_egg : ClothoidEgg :=
  mk_cloth (place_east (mkPoint 0 0)) 1 0 1 None None.

Lemma locked_clothoid_egg_wf : cloth_wf locked_clothoid_egg.
Proof.
  unfold locked_clothoid_egg.
  apply cloth_wf_mk.
  - lra.
  - rewrite east_h2. lra.
  - rewrite east_cross. lra.
  - left. split; reflexivity.
Qed.

Lemma locked_clothoid_egg_p1_is_gamma1 :
  cloth_p1 locked_clothoid_egg = cloth_eval locked_clothoid_egg 1.
Proof.
  unfold locked_clothoid_egg. apply cloth_eval_at_1_mk.
Qed.

Lemma locked_clothoid_end_not_unit :
  cloth_eval locked_clothoid_egg 1 <> mkPoint 1 0.
Proof.
  unfold locked_clothoid_egg. rewrite eval_east_01.
  cbn [px py].
  intros H. apply (f_equal py) in H. cbn [py] in H.
  assert (55 / 336 <= cloth_Cy 1) by apply cloth_Cy_ge_55_336.
  lra.
Qed.

Definition th0_probe : ClothoidEgg :=
  mk_cloth (place_north (mkPoint 0 0)) 1 0 1 None None.

Definition th0_probe_flat : ClothoidEgg :=
  mk_cloth (place_east (mkPoint 0 0)) 1 0 1 None None.

Lemma cloth_th0_moves_y :
  py (cloth_eval th0_probe 1) <> py (cloth_eval th0_probe_flat 1).
Proof.
  unfold th0_probe, th0_probe_flat.
  rewrite eval_north_01, eval_east_01. cbn [px py].
  assert (7 / 8 <= cloth_Cx 1) by apply cloth_Cx_ge_7_8.
  assert (cloth_Cy 1 <= 1 / 6) by apply cloth_Cy_le_sixth.
  lra.
Qed.
