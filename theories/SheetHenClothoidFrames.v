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

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance LipInt SheetHenClothoidCore
  SheetHenClothoidBounds.
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

(* cos(psi) on a unit clothoid is the Fresnel cosine once psi is the
   Fresnel angle. The Lipschitz constant collapses to |s| because A = 1. *)
Lemma unit_Icos_Cx : forall c s,
  cloth_A c = 1 ->
  (forall u, cos (cloth_psi c u) = fresnel_cx_integrand u) ->
  cloth_Icos c s = cloth_Cx s.
Proof.
  intros c s HA Heq.
  unfold cloth_Icos, cloth_Cx.
  assert (Hlip : forall x y,
      Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
      Rabs (cos (cloth_psi c x) - cos (cloth_psi c y))
        <= Rabs s * Rabs (x - y)).
  { intros x y Hx Hy. rewrite (Heq x), (Heq y).
    apply fresnel_cx_lip; assumption. }
  rewrite (int_seg_L (fun u => cos (cloth_psi c u))
    (cloth_phi_K c s) (Rabs s) 0 s
    (cloth_phi_K_nonneg c s) (Rabs_pos s)
    (cloth_cos_psi_lip c s) Hlip).
  apply int_seg_ext. intros u _. apply Heq.
Qed.

Lemma unit_Isin_Cy : forall c s,
  cloth_A c = 1 ->
  (forall u, sin (cloth_psi c u) = fresnel_cy_integrand u) ->
  cloth_Isin c s = cloth_Cy s.
Proof.
  intros c s HA Heq.
  unfold cloth_Isin, cloth_Cy.
  assert (Hlip : forall x y,
      Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
      Rabs (sin (cloth_psi c x) - sin (cloth_psi c y))
        <= Rabs s * Rabs (x - y)).
  { intros x y Hx Hy. rewrite (Heq x), (Heq y).
    apply fresnel_cy_lip; assumption. }
  rewrite (int_seg_L (fun u => sin (cloth_psi c u))
    (cloth_phi_K c s) (Rabs s) 0 s
    (cloth_phi_K_nonneg c s) (Rabs_pos s)
    (cloth_sin_psi_lip c s) Hlip).
  apply int_seg_ext. intros u _. apply Heq.
Qed.

Lemma unit_Isin_neg_Cy : forall c s,
  cloth_A c = 1 ->
  (forall u, sin (cloth_psi c u) = - fresnel_cy_integrand u) ->
  cloth_Isin c s = - cloth_Cy s.
Proof.
  intros c s HA Heq.
  unfold cloth_Isin, cloth_Cy.
  assert (Hopp : forall x y,
      Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
      Rabs (- fresnel_cy_integrand x - - fresnel_cy_integrand y)
        <= Rabs s * Rabs (x - y)).
  { intros x y Hx Hy.
    assert (Ed : - fresnel_cy_integrand x - - fresnel_cy_integrand y
                = - (fresnel_cy_integrand x - fresnel_cy_integrand y)) by ring.
    rewrite Ed. rewrite Rabs_Ropp. apply fresnel_cy_lip; assumption. }
  assert (Hlip : forall x y,
      Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
      Rabs (sin (cloth_psi c x) - sin (cloth_psi c y))
        <= Rabs s * Rabs (x - y)).
  { intros x y Hx Hy. rewrite (Heq x), (Heq y). apply Hopp; assumption. }
  rewrite (int_seg_L (fun u => sin (cloth_psi c u))
    (cloth_phi_K c s) (Rabs s) 0 s
    (cloth_phi_K_nonneg c s) (Rabs_pos s)
    (cloth_sin_psi_lip c s) Hlip).
  transitivity (int_seg (fun u => - fresnel_cy_integrand u) (Rabs s) 0 s
    (Rabs_pos s) Hopp).
  - apply int_seg_ext. intros u _. apply Heq.
  - rewrite (int_seg_opp fresnel_cy_integrand (Rabs s) 0 s
      (Rabs_pos s) (fresnel_cy_lip s) Hopp).
    reflexivity.
Qed.

Lemma east_angle : forall o u,
  cloth_psi (mk_cloth (place_east o) 1 0 1 None None) u = fresnel_angle u.
Proof.
  intros o u. unfold cloth_psi. rewrite east_sigma.
  cbn [cloth_A mk_cloth]. unfold fresnel_angle. field.
Qed.

Lemma west_angle : forall o u,
  cloth_psi (mk_cloth (place_west o) 1 1 0 None None) u = - fresnel_angle u.
Proof.
  intros o u. unfold cloth_psi. rewrite west_sigma.
  cbn [cloth_A mk_cloth]. unfold fresnel_angle. field.
Qed.

Lemma north_angle : forall o u,
  cloth_psi (mk_cloth (place_north o) 1 0 1 None None) u = fresnel_angle u.
Proof.
  intros o u. unfold cloth_psi. rewrite north_sigma.
  cbn [cloth_A mk_cloth]. unfold fresnel_angle. field.
Qed.

Lemma east_cos0 : forall o,
  cloth_cos0 (mk_cloth (place_east o) 1 0 1 None None) = 1.
Proof.
  intros o. unfold cloth_cos0, cloth_hypot, cloth_h2.
  cbn [cloth_place mk_cloth aff_ref1 place_east px py].
  rewrite east_h2, sqrt_1. field.
Qed.

Lemma east_sin0 : forall o,
  cloth_sin0 (mk_cloth (place_east o) 1 0 1 None None) = 0.
Proof.
  intros o. unfold cloth_sin0, cloth_hypot, cloth_h2.
  cbn [cloth_place mk_cloth aff_ref1 place_east px py].
  rewrite east_h2, sqrt_1. field.
Qed.

Lemma west_cos0 : forall o,
  cloth_cos0 (mk_cloth (place_west o) 1 1 0 None None) = -1.
Proof.
  intros o. unfold cloth_cos0, cloth_hypot, cloth_h2.
  cbn [cloth_place mk_cloth aff_ref1 place_west px py].
  rewrite west_h2, sqrt_1. field.
Qed.

Lemma west_sin0 : forall o,
  cloth_sin0 (mk_cloth (place_west o) 1 1 0 None None) = 0.
Proof.
  intros o. unfold cloth_sin0, cloth_hypot, cloth_h2.
  cbn [cloth_place mk_cloth aff_ref1 place_west px py].
  rewrite west_h2, sqrt_1. field.
Qed.

Lemma north_cos0 : forall o,
  cloth_cos0 (mk_cloth (place_north o) 1 0 1 None None) = 0.
Proof.
  intros o. unfold cloth_cos0, cloth_hypot, cloth_h2.
  cbn [cloth_place mk_cloth aff_ref1 place_north px py].
  rewrite north_h2, sqrt_1. field.
Qed.

Lemma north_sin0 : forall o,
  cloth_sin0 (mk_cloth (place_north o) 1 0 1 None None) = 1.
Proof.
  intros o. unfold cloth_sin0, cloth_hypot, cloth_h2.
  cbn [cloth_place mk_cloth aff_ref1 place_north px py].
  rewrite north_h2, sqrt_1. field.
Qed.

Lemma east_int_x : forall o s,
  cloth_Icos (mk_cloth (place_east o) 1 0 1 None None) s = cloth_Cx s.
Proof.
  intros o s.
  apply unit_Icos_Cx; [reflexivity|].
  intros u. rewrite east_angle. reflexivity.
Qed.

Lemma east_int_y : forall o s,
  cloth_Isin (mk_cloth (place_east o) 1 0 1 None None) s = cloth_Cy s.
Proof.
  intros o s.
  apply unit_Isin_Cy; [reflexivity|].
  intros u. rewrite east_angle. reflexivity.
Qed.

Lemma west_int_x : forall o s,
  cloth_Icos (mk_cloth (place_west o) 1 1 0 None None) s = cloth_Cx s.
Proof.
  intros o s.
  apply unit_Icos_Cx; [reflexivity|].
  intros u. rewrite west_angle, cos_neg. reflexivity.
Qed.

Lemma west_int_y : forall o s,
  cloth_Isin (mk_cloth (place_west o) 1 1 0 None None) s = - cloth_Cy s.
Proof.
  intros o s.
  apply unit_Isin_neg_Cy; [reflexivity|].
  intros u. rewrite west_angle, sin_neg. reflexivity.
Qed.

Lemma north_int_x : forall o s,
  cloth_Icos (mk_cloth (place_north o) 1 0 1 None None) s = cloth_Cx s.
Proof.
  intros o s.
  apply unit_Icos_Cx; [reflexivity|].
  intros u. rewrite north_angle. reflexivity.
Qed.

Lemma north_int_y : forall o s,
  cloth_Isin (mk_cloth (place_north o) 1 0 1 None None) s = cloth_Cy s.
Proof.
  intros o s.
  apply unit_Isin_Cy; [reflexivity|].
  intros u. rewrite north_angle. reflexivity.
Qed.

Lemma eval_east_01 : forall o t,
  cloth_eval (mk_cloth (place_east o) 1 0 1 None None) t
    = mkPoint (px o + cloth_Cx t) (py o + cloth_Cy t).
Proof.
  intros o t.
  unfold cloth_eval, cloth_P, cloth_Px, cloth_Py, cloth_s.
  cbn [cloth_sd cloth_ed cloth_place mk_cloth aff_loc place_east].
  replace (0 + t * (1 - 0)) with t by ring.
  rewrite east_cos0, east_sin0, east_int_x, east_int_y.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma eval_west_10 : forall o t,
  cloth_eval (mk_cloth (place_west o) 1 1 0 None None) t
    = mkPoint (px o - cloth_Cx (1 - t)) (py o + cloth_Cy (1 - t)).
Proof.
  intros o t.
  unfold cloth_eval, cloth_P, cloth_Px, cloth_Py, cloth_s.
  cbn [cloth_sd cloth_ed cloth_place mk_cloth aff_loc place_west].
  replace (1 + t * (0 - 1)) with (1 - t) by ring.
  rewrite west_cos0, west_sin0, west_int_x, west_int_y.
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
  rewrite north_cos0, north_sin0, north_int_x, north_int_y.
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
