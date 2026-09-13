(* ============================================================================
   NetTopologySuite.Proofs.IntakeFamousGeodesic
   ----------------------------------------------------------------------------
   ADR-0007 letter: famous GEODESICSTRING fixtures
   (claimId 0007-famous-geodesicstring).

   Cite (CONTEXT lock): Rohit Chabukswar and Adwait Kumar Mukherjee,
   "Longest straight line paths on water or land on the Earth",
   arXiv:1804.07389. Science news on the longest ocean / land
   straight paths. Endpoints locked DMS → decimal lon lat
   (OGC order).

   This letter is fixtures + τ honesty park on existing μ
   (0007-intake-geodesic / #744). Not a new cook. Not a remint
   of 0007-intake-geodesic or tools #745.

   Water / sailable: Sonmiani PK → Karaginsky RU
     GEODESICSTRING (66.6666666667 25.2833333333,
                     162.2333333333 58.6166666667)
   Land / drivable: Quanzhou CN → Sagres PT
     GEODESICSTRING (118.6333333333 24.55,
                     -8.9166666667 37.0333333333)

   QED: each tagged CST is TGeodesicString pts; μ → IntakeBag
   whose chickens are MkChord only — the same bag as the
   matching LINESTRING on those two points. τ of the minted
   egg is LINESTRING; cst_prod_tag stays None; T_signed has
   no TagGeodesic; κ does not gain 13. Empty / singleton still
   ID_Empty / ID_BadPointCount; SPIRALCURVE still Declines.

   Named QEX (do not discharge): Earth great-circle length
   (~32090 km / ~11241 km) or angular span (~288°35′ / ~101°6′);
   ETOPO1 land/water mask / "longest uninterrupted"; sphere vs
   WGS84 ellipsoid / geoid; optimality of branch-and-bound;
   emit of GEODESICSTRING bytes / WKB 13 as signed I/O.

   Hard no: MkGeodesic / geodesic_eval / MkSpiral / spiral_eval
   as γ; first_cook_scope expand; CompoundEgg / compound_eval;
   Halley/Fresnel as γ or 𝓘; unhold #729 NURBS; silent chord
   demote framed as Earth geodesic / "we proved the Science
   path length"; remint 0007-intake-geodesic / #744 / #745.

   WITNESS topic: overlay · claimId: 0007-famous-geodesicstring
   witness: 0007-famous-geodesicstring
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance SheetHenCook IntakeWalker SqlMmSignedTag IntakeGeodesic.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Locked endpoints. OGC order: lon lat. DMS → decimal as cited.              *)
(* -------------------------------------------------------------------------- *)

Definition famous_water_a : Point := mkPoint 66.6666666667 25.2833333333.
Definition famous_water_b : Point := mkPoint 162.2333333333 58.6166666667.
Definition famous_water_pts : list Point := [famous_water_a; famous_water_b].
Definition famous_water_g_cst : TaggedCst := TGeodesicString famous_water_pts.
Definition famous_water_ls_cst : TaggedCst := TLineString famous_water_pts.

Definition famous_land_a : Point := mkPoint 118.6333333333 24.55.
Definition famous_land_b : Point := mkPoint (-8.9166666667) 37.0333333333.
Definition famous_land_pts : list Point := [famous_land_a; famous_land_b].
Definition famous_land_g_cst : TaggedCst := TGeodesicString famous_land_pts.
Definition famous_land_ls_cst : TaggedCst := TLineString famous_land_pts.

(* -------------------------------------------------------------------------- *)
(* QED: tagged CST + μ → IntakeBag, MkChord only, same bag as LINESTRING.     *)
(* -------------------------------------------------------------------------- *)

Lemma famous_water_tagged :
  famous_water_g_cst = TGeodesicString famous_water_pts.
Proof. reflexivity. Qed.

Lemma famous_land_tagged :
  famous_land_g_cst = TGeodesicString famous_land_pts.
Proof. reflexivity. Qed.

Lemma famous_water_maps :
  intake_map default_sheet famous_water_g_cst =
    IntakeBag (map_ls default_sheet famous_water_pts).
Proof. reflexivity. Qed.

Lemma famous_land_maps :
  intake_map default_sheet famous_land_g_cst =
    IntakeBag (map_ls default_sheet famous_land_pts).
Proof. reflexivity. Qed.

Lemma famous_water_same_bag_as_ls :
  intake_map default_sheet famous_water_g_cst =
    intake_map default_sheet famous_water_ls_cst.
Proof. exact (geodesic_ls_same_mu default_sheet famous_water_pts). Qed.

Lemma famous_land_same_bag_as_ls :
  intake_map default_sheet famous_land_g_cst =
    intake_map default_sheet famous_land_ls_cst.
Proof. exact (geodesic_ls_same_mu default_sheet famous_land_pts). Qed.

Lemma famous_water_chickens_mkchord :
  bag_chickens (map_ls default_sheet famous_water_pts) =
    [mkChicken 0%nat 1%nat (MkChord (mkChordEgg famous_water_a famous_water_b))].
Proof. reflexivity. Qed.

Lemma famous_land_chickens_mkchord :
  bag_chickens (map_ls default_sheet famous_land_pts) =
    [mkChicken 0%nat 1%nat (MkChord (mkChordEgg famous_land_a famous_land_b))].
Proof. reflexivity. Qed.

Lemma famous_water_eggs_mkchord :
  forall ck,
    In ck (bag_chickens (map_ls default_sheet famous_water_pts)) ->
    exists p q, ck_egg ck = MkChord (mkChordEgg p q).
Proof.
  intros ck Hin.
  apply (geodesic_bag_eggs_mkchord default_sheet famous_water_pts ck Hin).
Qed.

Lemma famous_land_eggs_mkchord :
  forall ck,
    In ck (bag_chickens (map_ls default_sheet famous_land_pts)) ->
    exists p q, ck_egg ck = MkChord (mkChordEgg p q).
Proof.
  intros ck Hin.
  apply (geodesic_bag_eggs_mkchord default_sheet famous_land_pts ck Hin).
Qed.

Lemma famous_water_not_mkcirc :
  forall ck γ,
    In ck (bag_chickens (map_ls default_sheet famous_water_pts)) ->
    ck_egg ck <> MkCirc γ.
Proof.
  intros ck γ Hin.
  apply (geodesic_bag_not_mkcirc default_sheet famous_water_pts ck γ Hin).
Qed.

Lemma famous_land_not_mkcirc :
  forall ck γ,
    In ck (bag_chickens (map_ls default_sheet famous_land_pts)) ->
    ck_egg ck <> MkCirc γ.
Proof.
  intros ck γ Hin.
  apply (geodesic_bag_not_mkcirc default_sheet famous_land_pts ck γ Hin).
Qed.

Lemma famous_water_not_geodesic_egg :
  forall ck,
    In ck (bag_chickens (map_ls default_sheet famous_water_pts)) ->
    ck_egg ck <> MkOutOfScope EggGeodesicString /\
    egg_class (ck_egg ck) = EggChord.
Proof.
  intros ck Hin.
  rewrite famous_water_chickens_mkchord in Hin.
  destruct Hin as [Heq|[]].
  rewrite <- Heq. split; [discriminate|reflexivity].
Qed.

Lemma famous_land_not_geodesic_egg :
  forall ck,
    In ck (bag_chickens (map_ls default_sheet famous_land_pts)) ->
    ck_egg ck <> MkOutOfScope EggGeodesicString /\
    egg_class (ck_egg ck) = EggChord.
Proof.
  intros ck Hin.
  rewrite famous_land_chickens_mkchord in Hin.
  destruct Hin as [Heq|[]].
  rewrite <- Heq. split; [discriminate|reflexivity].
Qed.

(* -------------------------------------------------------------------------- *)
(* τ honesty: LINESTRING on the minted egg; production tag None; no κ=13.     *)
(* -------------------------------------------------------------------------- *)

Lemma famous_water_tau :
  first_slice_tag (MkChord (mkChordEgg famous_water_a famous_water_b)) =
    Some TagLineString.
Proof. reflexivity. Qed.

Lemma famous_land_tau :
  first_slice_tag (MkChord (mkChordEgg famous_land_a famous_land_b)) =
    Some TagLineString.
Proof. reflexivity. Qed.

Lemma famous_water_prod_tag :
  cst_prod_tag famous_water_g_cst = None /\
  cst_prod_name famous_water_g_cst = PiGeodesicString /\
  cst_prod_name famous_water_ls_cst = PiLineString.
Proof. split; [reflexivity|split; reflexivity]. Qed.

Lemma famous_land_prod_tag :
  cst_prod_tag famous_land_g_cst = None /\
  cst_prod_name famous_land_g_cst = PiGeodesicString /\
  cst_prod_name famous_land_ls_cst = PiLineString.
Proof. split; [reflexivity|split; reflexivity]. Qed.

Lemma famous_t_signed_cases :
  forall t : SqlMmSignedTag,
    t = TagLineString \/ t = TagCircularString \/
    t = TagCircle \/ t = TagClothoid.
Proof.
  intros t. destruct t; [left|right; left|right; right; left|right; right; right];
    reflexivity.
Qed.

Lemma famous_no_tag_geodesic :
  forall t : SqlMmSignedTag,
    t = TagLineString \/ t = TagCircularString \/
    t = TagCircle \/ t = TagClothoid.
Proof. exact famous_t_signed_cases. Qed.

Lemma famous_kappa_not_13 :
  forall t, sqlmm_kappa t <> Some 13%nat.
Proof. exact kappa_not_13. Qed.

Lemma famous_water_tau_mu :
  exists b e,
    intake_map default_sheet famous_water_g_cst = IntakeBag b /\
    bag_eggs b = [e] /\
    e = MkChord (mkChordEgg famous_water_a famous_water_b) /\
    first_slice_tag e = Some TagLineString /\
    cst_prod_tag famous_water_g_cst = None.
Proof.
  exists (map_ls default_sheet famous_water_pts).
  exists (MkChord (mkChordEgg famous_water_a famous_water_b)).
  split; [exact famous_water_maps|].
  split; [unfold bag_eggs; rewrite famous_water_chickens_mkchord; reflexivity|].
  split; [reflexivity|].
  split; [exact famous_water_tau|].
  reflexivity.
Qed.

Lemma famous_land_tau_mu :
  exists b e,
    intake_map default_sheet famous_land_g_cst = IntakeBag b /\
    bag_eggs b = [e] /\
    e = MkChord (mkChordEgg famous_land_a famous_land_b) /\
    first_slice_tag e = Some TagLineString /\
    cst_prod_tag famous_land_g_cst = None.
Proof.
  exists (map_ls default_sheet famous_land_pts).
  exists (MkChord (mkChordEgg famous_land_a famous_land_b)).
  split; [exact famous_land_maps|].
  split; [unfold bag_eggs; rewrite famous_land_chickens_mkchord; reflexivity|].
  split; [reflexivity|].
  split; [exact famous_land_tau|].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Empty / singleton / spiral honesty: same Decline names as #744.            *)
(* -------------------------------------------------------------------------- *)

Lemma famous_empty_declines :
  intake_map default_sheet (TGeodesicString []) = IntakeDecline ID_Empty.
Proof. exact geodesic_empty_declines. Qed.

Lemma famous_singleton_declines :
  intake_map default_sheet (TGeodesicString [p00]) =
    IntakeDecline ID_BadPointCount.
Proof. exact geodesic_badcount_declines. Qed.

Lemma famous_spiral_declines :
  intake_map default_sheet TSpiralCurve = IntakeDecline ID_SpiralCurve.
Proof. exact spiral_declines. Qed.

(* -------------------------------------------------------------------------- *)
(* Named QEX park. Do not inhabit. Not Earth length / mask / ellipsoid.       *)
(* -------------------------------------------------------------------------- *)

Inductive FamousGeodesicQex : Type :=
| FG_EarthGreatCircleLength
| FG_Etopo1LandWaterMask
| FG_SphereVsWgs84
| FG_BranchBoundOptimality
| FG_EmitWkb13SignedIo.

Definition famous_geodesic_qex_inhabits (_ : FamousGeodesicQex) : Prop := False.

Lemma famous_earth_length_missing :
  ~ famous_geodesic_qex_inhabits FG_EarthGreatCircleLength.
Proof. intro H. exact H. Qed.

Lemma famous_etopo1_missing :
  ~ famous_geodesic_qex_inhabits FG_Etopo1LandWaterMask.
Proof. intro H. exact H. Qed.

Lemma famous_sphere_vs_wgs84_missing :
  ~ famous_geodesic_qex_inhabits FG_SphereVsWgs84.
Proof. intro H. exact H. Qed.

Lemma famous_branch_bound_missing :
  ~ famous_geodesic_qex_inhabits FG_BranchBoundOptimality.
Proof. intro H. exact H. Qed.

Lemma famous_emit_wkb13_missing :
  ~ famous_geodesic_qex_inhabits FG_EmitWkb13SignedIo.
Proof. intro H. exact H. Qed.

(* WITNESS {"claimId":"0007-famous-geodesicstring","topic":"overlay","lemma":"ticket_0007_famous_geodesicstring_qed_or_qex","title":"Famous Science/arXiv 1804.07389 GEODESICSTRING fixtures: Sonmiani-Karaginsky water and Quanzhou-Sagres land bag as TGeodesicString MkChord-only IntakeBag, same bag as matching LINESTRING; tau=LINESTRING; cst_prod_tag None; no TagGeodesic; kappa not 13; empty/singleton/spiral still Decline (QED) or Earth great-circle length / ETOPO1 mask / sphere-vs-WGS84 / branch-and-bound optimality / emit-WKB-13 inhabit (QEX); discharged QED; not MkGeodesic; not a silent Earth-chord demote; not a remint of 0007-intake-geodesic","file":"theories/IntakeFamousGeodesic.v","witness":"0007-famous-geodesicstring","board":"ADR-0007"} *)
Theorem ticket_0007_famous_geodesicstring_qed_or_qex :
  (famous_water_g_cst = TGeodesicString famous_water_pts /\
   famous_land_g_cst = TGeodesicString famous_land_pts /\
   intake_map default_sheet famous_water_g_cst =
     IntakeBag (map_ls default_sheet famous_water_pts) /\
   intake_map default_sheet famous_land_g_cst =
     IntakeBag (map_ls default_sheet famous_land_pts) /\
   intake_map default_sheet famous_water_g_cst =
     intake_map default_sheet famous_water_ls_cst /\
   intake_map default_sheet famous_land_g_cst =
     intake_map default_sheet famous_land_ls_cst /\
   bag_chickens (map_ls default_sheet famous_water_pts) =
     [mkChicken 0%nat 1%nat (MkChord (mkChordEgg famous_water_a famous_water_b))] /\
   bag_chickens (map_ls default_sheet famous_land_pts) =
     [mkChicken 0%nat 1%nat (MkChord (mkChordEgg famous_land_a famous_land_b))] /\
   first_slice_tag (MkChord (mkChordEgg famous_water_a famous_water_b)) =
     Some TagLineString /\
   first_slice_tag (MkChord (mkChordEgg famous_land_a famous_land_b)) =
     Some TagLineString /\
   cst_prod_tag famous_water_g_cst = None /\
   cst_prod_tag famous_land_g_cst = None /\
   (forall t, sqlmm_kappa t <> Some 13%nat) /\
   (forall t : SqlMmSignedTag,
      t = TagLineString \/ t = TagCircularString \/
      t = TagCircle \/ t = TagClothoid) /\
   intake_map default_sheet (TGeodesicString []) = IntakeDecline ID_Empty /\
   intake_map default_sheet (TGeodesicString [p00]) =
     IntakeDecline ID_BadPointCount /\
   intake_map default_sheet TSpiralCurve = IntakeDecline ID_SpiralCurve)
  \/
  (famous_geodesic_qex_inhabits FG_EarthGreatCircleLength /\
   famous_geodesic_qex_inhabits FG_Etopo1LandWaterMask /\
   famous_geodesic_qex_inhabits FG_SphereVsWgs84 /\
   famous_geodesic_qex_inhabits FG_BranchBoundOptimality /\
   famous_geodesic_qex_inhabits FG_EmitWkb13SignedIo).
Proof.
  left.
  split; [exact famous_water_tagged|].
  split; [exact famous_land_tagged|].
  split; [exact famous_water_maps|].
  split; [exact famous_land_maps|].
  split; [exact famous_water_same_bag_as_ls|].
  split; [exact famous_land_same_bag_as_ls|].
  split; [exact famous_water_chickens_mkchord|].
  split; [exact famous_land_chickens_mkchord|].
  split; [exact famous_water_tau|].
  split; [exact famous_land_tau|].
  split; [exact (proj1 famous_water_prod_tag)|].
  split; [exact (proj1 famous_land_prod_tag)|].
  split; [exact famous_kappa_not_13|].
  split; [exact famous_no_tag_geodesic|].
  split; [exact famous_empty_declines|].
  split; [exact famous_singleton_declines|].
  exact famous_spiral_declines.
Qed.

Print Assumptions famous_water_maps.
Print Assumptions famous_land_maps.
Print Assumptions famous_water_same_bag_as_ls.
Print Assumptions famous_land_same_bag_as_ls.
Print Assumptions famous_water_chickens_mkchord.
Print Assumptions famous_land_chickens_mkchord.
Print Assumptions famous_water_tau.
Print Assumptions famous_land_tau.
Print Assumptions famous_water_prod_tag.
Print Assumptions famous_land_prod_tag.
Print Assumptions famous_no_tag_geodesic.
Print Assumptions famous_kappa_not_13.
Print Assumptions famous_empty_declines.
Print Assumptions famous_singleton_declines.
Print Assumptions famous_spiral_declines.
Print Assumptions famous_earth_length_missing.
Print Assumptions famous_etopo1_missing.
Print Assumptions famous_sphere_vs_wgs84_missing.
Print Assumptions famous_branch_bound_missing.
Print Assumptions famous_emit_wkb13_missing.
Print Assumptions ticket_0007_famous_geodesicstring_qed_or_qex.
