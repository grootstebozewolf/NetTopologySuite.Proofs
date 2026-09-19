(* ============================================================================
   NetTopologySuite.Proofs.IntakeGeodesicCook
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: the planar geodesic machine (claimId
   0007-geodesic-cook). On the sheet S = (O; e1, e2) a geodesic is the chord;
   this file makes the accepted intake letter (IntakeGeodesic.v,
   0007-intake-geodesic) actually cook. No MkGeodesic egg, no new classifier,
   no import of CircularCookLineArc*: intake -> chord bag -> host I_ok ->
   try_cook_hit on EggChord x EggChord.

   G0 — intake is a function. Any well-formed GEODESICSTRING CST (two or
        more points) maps to a bag, never Decline; its eggs are
        definitionally MkChord and the bag equals the LINESTRING bag on the
        same vertices. Decline happens exactly on [] / [_].
   G1 — a locked self-crossing geodesic polyline (three segments, one proper
        crossing) cooks: host I_ok Hit on the crossing pair, try_cook_hit
        mints one hen, the leftovers meet at it, tau stays LINESTRING.
   G2 — the famous nets (IntakeFamousGeodesic.v) are chord bags; the Egg
        type has no MkGeodesic constructor to inhabit.
   G3 — ambient manifold stays QEX with a closed term: the sheet chord
        (-90,45)-(90,45) never passes through (0,90), where the great circle
        through those two points does. A second sheet class is a new ADR.
   G4 — wire format stays QEX (WKB 13 / emit / tau = pi), as already named
        in IntakeGeodesic.v; no view letter here.
   G5 — first cook is not expanded: EggGeodesicString is never in
        first_cook_scope, and ~ first_cook_scope EggChord EggCircularArc.

   Not touched: host I_ok, first_cook_scope, sidecar cooks, the oracle wire.

   WITNESS topic: overlay · claimId: 0007-geodesic-cook · witness: 0007-geodesic-cook
   board: ADR-0007
   3-axiom host lane (Stdlib Reals). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook IntakeWalker SqlMmSignedTag
  IntakeGeodesic IntakeFamousGeodesic.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  G0: intake is a function on well-formed input.                         *)
(* -------------------------------------------------------------------------- *)

Lemma geodesic_wellformed_bags :
  forall s p q rest,
    intake_map s (TGeodesicString (p :: q :: rest)) =
      IntakeBag (map_ls s (p :: q :: rest)).
Proof. intros. reflexivity. Qed.

Lemma geodesic_wellformed_no_decline :
  forall s p q rest r,
    intake_map s (TGeodesicString (p :: q :: rest)) <> IntakeDecline r.
Proof. intros. rewrite geodesic_wellformed_bags. apply intake_bag_neq_decline. Qed.

Lemma geodesic_decline_iff :
  forall s pts,
    (exists r, intake_map s (TGeodesicString pts) = IntakeDecline r) <->
    (pts = [] \/ exists p, pts = [p]).
Proof.
  intros s pts. split.
  - intros [r Hr]. destruct pts as [|p [|q rest]].
    + left. reflexivity.
    + right. exists p. reflexivity.
    + exfalso. exact (geodesic_wellformed_no_decline s p q rest r Hr).
  - intros [H | [p H]]; subst.
    + exists ID_Empty. reflexivity.
    + exists ID_BadPointCount. reflexivity.
Qed.

Lemma geodesic_wellformed_same_bag_as_ls :
  forall s p q rest,
    intake_map s (TGeodesicString (p :: q :: rest)) =
    intake_map s (TLineString (p :: q :: rest)).
Proof. intros. reflexivity. Qed.

Lemma geodesic_wellformed_eggs_mkchord :
  forall s p q rest ck,
    In ck (bag_chickens (map_ls s (p :: q :: rest))) ->
    exists a b, ck_egg ck = MkChord (mkChordEgg a b).
Proof. intros s p q rest ck. apply geodesic_bag_eggs_mkchord. Qed.

(* WITNESS {"claimId":"0007-geodesic-cook","topic":"overlay","lemma":"ticket_0007_geodesic_intake_fn_qed_or_qex","title":"G0 intake is a function: every well-formed GEODESICSTRING CST (2+ points) maps to a non-Decline bag whose eggs are MkChord and which equals the LINESTRING bag on the same vertices, and Decline holds exactly on [] or [p] (QED); or the walker Declines a well-formed CST (QEX); discharged QED","file":"theories/IntakeGeodesicCook.v","witness":"0007-geodesic-cook","board":"ADR-0007"} *)
Theorem ticket_0007_geodesic_intake_fn_qed_or_qex :
  ((forall s p q rest,
      intake_map s (TGeodesicString (p :: q :: rest)) =
        IntakeBag (map_ls s (p :: q :: rest)))
   /\ (forall s p q rest,
         intake_map s (TGeodesicString (p :: q :: rest)) =
         intake_map s (TLineString (p :: q :: rest)))
   /\ (forall s p q rest ck,
         In ck (bag_chickens (map_ls s (p :: q :: rest))) ->
         exists a b, ck_egg ck = MkChord (mkChordEgg a b))
   /\ (forall s pts,
         (exists r, intake_map s (TGeodesicString pts) = IntakeDecline r) <->
         (pts = [] \/ exists p, pts = [p])))
  \/
  (exists s p q rest r,
      intake_map s (TGeodesicString (p :: q :: rest)) = IntakeDecline r).
Proof.
  left.
  split; [exact geodesic_wellformed_bags |].
  split; [exact geodesic_wellformed_same_bag_as_ls |].
  split; [exact geodesic_wellformed_eggs_mkchord |].
  exact geodesic_decline_iff.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  G1: a locked self-crossing geodesic polyline cooks.                     *)
(* -------------------------------------------------------------------------- *)

(* Bow-tie: (0,0) -> (4,4) -> (4,0) -> (0,4). Segment 0 and segment 2 cross
   properly at (2,2), t = 1/2 on both. Three segments, hens 0..3. *)
Definition gx_a : Point := mkPoint 0 0.
Definition gx_b : Point := mkPoint 4 4.
Definition gx_c : Point := mkPoint 4 0.
Definition gx_d : Point := mkPoint 0 4.
Definition gx_pts : list Point := [gx_a; gx_b; gx_c; gx_d].
Definition locked_geodesic_cross_cst : TaggedCst := TGeodesicString gx_pts.

Definition gx_e0 : ChordEgg := mkChordEgg gx_a gx_b.
Definition gx_e1 : ChordEgg := mkChordEgg gx_b gx_c.
Definition gx_e2 : ChordEgg := mkChordEgg gx_c gx_d.
Definition gx_ck0 : Chicken := mkChicken 0%nat 1%nat (MkChord gx_e0).
Definition gx_ck1 : Chicken := mkChicken 1%nat 2%nat (MkChord gx_e1).
Definition gx_ck2 : Chicken := mkChicken 2%nat 3%nat (MkChord gx_e2).

Definition gx_x : Point := mkPoint 2 2.
Definition gx_hit : IResult := IHit gx_x (1/2) (1/2).
(* Fresh hen: the bag's hens are 0..3, so 4 is the first unused one. *)
Definition gx_hen : Hen := 4%nat.

Lemma gx_intake :
  intake_map default_sheet locked_geodesic_cross_cst =
    IntakeBag (map_ls default_sheet gx_pts).
Proof. reflexivity. Qed.

Lemma gx_bag_chickens :
  bag_chickens (map_ls default_sheet gx_pts) = [gx_ck0; gx_ck1; gx_ck2].
Proof. reflexivity. Qed.

Lemma gx_bag_hens :
  bag_hens (map_ls default_sheet gx_pts) = [0%nat; 1%nat; 2%nat; 3%nat].
Proof. reflexivity. Qed.

Lemma gx_hen_fresh : ~ In gx_hen (bag_hens (map_ls default_sheet gx_pts)).
Proof. rewrite gx_bag_hens. cbn. intro H. repeat destruct H as [H | H]; try discriminate H; exact H. Qed.

Lemma gx_three_segments : length (bag_chickens (map_ls default_sheet gx_pts)) = 3%nat.
Proof. reflexivity. Qed.

Lemma gx_cross_hit : I_ok (ck_egg gx_ck0) (ck_egg gx_ck2) gx_hit.
Proof.
  unfold I_ok, gx_hit, on_chord, chord_eval; cbn [ck_egg gx_ck0 gx_ck2 gx_e0 gx_e2 ce_p0 ce_p1 px py gx_a gx_b gx_c gx_d gx_x].
  split; (split; [split; lra | apply (f_equal2 mkPoint); lra]).
Qed.

Lemma gx_cross_proper :
  0 < 1/2 < 1 /\ gx_x <> gx_a /\ gx_x <> gx_b /\ gx_x <> gx_c /\ gx_x <> gx_d.
Proof.
  split; [lra |].
  repeat split; intro H; injection H; lra.
Qed.

Lemma gx_first_cook_scope :
  first_cook_scope (egg_class (ck_egg gx_ck0)) (egg_class (ck_egg gx_ck2)).
Proof. exact I. Qed.

Definition gx_cooked : CookedPair :=
  cook_hit_chords gx_ck0 gx_ck2 gx_e0 gx_e2 (1/2) (1/2) gx_hen.

Lemma gx_try_cook_some :
  try_cook_hit gx_ck0 gx_ck2 gx_hit gx_hen = Some gx_cooked.
Proof. reflexivity. Qed.

Lemma gx_mints_one_hen :
  cp_hen gx_cooked = gx_hen /\ cooked_shares_hen gx_cooked.
Proof. split; [reflexivity | apply cook_hit_chords_shares_hen]. Qed.

(* Leftovers meet at the crossing: both splits join at (2,2). *)
Lemma gx_leftovers_meet :
  ce_p1 (fst (chord_split gx_e0 (1/2))) = gx_x /\
  ce_p0 (snd (chord_split gx_e0 (1/2))) = gx_x /\
  ce_p1 (fst (chord_split gx_e2 (1/2))) = gx_x /\
  ce_p0 (snd (chord_split gx_e2 (1/2))) = gx_x.
Proof.
  unfold chord_split, chord_eval, gx_e0, gx_e2, gx_x; cbn [fst snd ce_p0 ce_p1 px py gx_a gx_b gx_c gx_d].
  repeat split; apply (f_equal2 mkPoint); lra.
Qed.

(* τ stays LINESTRING on all four leftovers. *)
Lemma gx_tau_linestring :
  first_slice_tag (ck_egg (cp_left1 gx_cooked)) = Some TagLineString /\
  first_slice_tag (ck_egg (cp_right1 gx_cooked)) = Some TagLineString /\
  first_slice_tag (ck_egg (cp_left2 gx_cooked)) = Some TagLineString /\
  first_slice_tag (ck_egg (cp_right2 gx_cooked)) = Some TagLineString.
Proof. repeat split; reflexivity. Qed.

Lemma gx_prod_tag :
  cst_prod_name locked_geodesic_cross_cst = PiGeodesicString /\
  t_signed_of_prod PiGeodesicString = None.
Proof. split; reflexivity. Qed.

(* WITNESS {"claimId":"0007-geodesic-cook","topic":"overlay","lemma":"ticket_0007_geodesic_cook_qed_or_qex","title":"G1 locked geodesic polyline cooks: the bow-tie GEODESICSTRING (0,0)(4,4)(4,0)(0,4) bags three MkChord, host I_ok Hit on segments 0 x 2 at (2,2) with t=1/2 on both, try_cook_hit mints the one fresh hen 4, both splits meet at (2,2), tau stays LINESTRING on all four leftovers (QED); or try_cook_hit returns None on the bag and the machine is intake-only (QEX); discharged QED","file":"theories/IntakeGeodesicCook.v","witness":"0007-geodesic-cook","board":"ADR-0007"} *)
Theorem ticket_0007_geodesic_cook_qed_or_qex :
  (intake_map default_sheet locked_geodesic_cross_cst =
     IntakeBag (map_ls default_sheet gx_pts)
   /\ bag_chickens (map_ls default_sheet gx_pts) = [gx_ck0; gx_ck1; gx_ck2]
   /\ I_ok (ck_egg gx_ck0) (ck_egg gx_ck2) gx_hit
   /\ 0 < 1/2 < 1
   /\ try_cook_hit gx_ck0 gx_ck2 gx_hit gx_hen = Some gx_cooked
   /\ ~ In gx_hen (bag_hens (map_ls default_sheet gx_pts))
   /\ cooked_shares_hen gx_cooked
   /\ ce_p1 (fst (chord_split gx_e0 (1/2))) = gx_x
   /\ ce_p0 (snd (chord_split gx_e2 (1/2))) = gx_x
   /\ first_slice_tag (ck_egg (cp_left1 gx_cooked)) = Some TagLineString
   /\ first_slice_tag (ck_egg (cp_right2 gx_cooked)) = Some TagLineString
   /\ t_signed_of_prod (cst_prod_name locked_geodesic_cross_cst) = None)
  \/
  try_cook_hit gx_ck0 gx_ck2 gx_hit gx_hen = None.
Proof.
  left.
  split; [exact gx_intake |].
  split; [exact gx_bag_chickens |].
  split; [exact gx_cross_hit |].
  split; [exact (proj1 gx_cross_proper) |].
  split; [exact gx_try_cook_some |].
  split; [exact gx_hen_fresh |].
  split; [exact (proj2 gx_mints_one_hen) |].
  destruct gx_leftovers_meet as [H1 [_ [_ H4]]].
  split; [exact H1 |].
  split; [exact H4 |].
  destruct gx_tau_linestring as [T1 [_ [_ T4]]].
  split; [exact T1 |].
  split; [exact T4 |].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  G2: famous nets are chord bags; Egg has no MkGeodesic constructor.      *)
(* -------------------------------------------------------------------------- *)

(* Every Egg is one of the three interpolants or an out-of-scope class tag;
   the only way to say "geodesic" in Egg is MkOutOfScope EggGeodesicString,
   and no chord bag contains it. *)
Lemma egg_no_mkgeodesic :
  forall e : Egg,
    (exists c, e = MkChord c) \/ (exists g, e = MkCirc g) \/
    (exists k, e = MkClothoid k) \/ (exists cls, e = MkOutOfScope cls).
Proof.
  intros [c | g | k | cls].
  - left. exists c. reflexivity.
  - right. left. exists g. reflexivity.
  - right. right. left. exists k. reflexivity.
  - right. right. right. exists cls. reflexivity.
Qed.

Lemma geodesic_bag_not_outofscope :
  forall s pts ck cls,
    In ck (bag_chickens (map_ls s pts)) ->
    ck_egg ck <> MkOutOfScope cls.
Proof.
  intros s pts ck cls Hin Heq.
  destruct (geodesic_bag_eggs_mkchord s pts ck Hin) as [p [q Hpq]].
  rewrite Hpq in Heq. discriminate.
Qed.

(* WITNESS {"claimId":"0007-geodesic-cook","topic":"overlay","lemma":"ticket_0007_geodesic_famous_chords_qed_or_qex","title":"G2 famous instances are chord bags: the Sonmiani-Karaginsky water and Jinjiang-Sagres land nets bag MkChord only, no chicken in any geodesic bag is MkOutOfScope, and Egg has no MkGeodesic constructor (QED); or a famous net is not a planar chord interpolant (sphere / WGS84) which is the park FG_SphereVsWgs84, not a new egg (QEX); discharged QED","file":"theories/IntakeGeodesicCook.v","witness":"0007-geodesic-cook","board":"ADR-0007"} *)
Theorem ticket_0007_geodesic_famous_chords_qed_or_qex :
  ((forall ck, In ck (bag_chickens (map_ls default_sheet famous_water_pts)) ->
      ck_egg ck <> MkOutOfScope EggGeodesicString /\ egg_class (ck_egg ck) = EggChord)
   /\ (forall ck, In ck (bag_chickens (map_ls default_sheet famous_land_pts)) ->
      ck_egg ck <> MkOutOfScope EggGeodesicString /\ egg_class (ck_egg ck) = EggChord)
   /\ (forall s pts ck cls,
         In ck (bag_chickens (map_ls s pts)) -> ck_egg ck <> MkOutOfScope cls)
   /\ (forall e : Egg,
         (exists c, e = MkChord c) \/ (exists g, e = MkCirc g) \/
         (exists k, e = MkClothoid k) \/ (exists cls, e = MkOutOfScope cls)))
  \/
  famous_geodesic_qex_inhabits FG_SphereVsWgs84.
Proof.
  left.
  split; [exact famous_water_not_geodesic_egg |].
  split; [exact famous_land_not_geodesic_egg |].
  split; [exact geodesic_bag_not_outofscope |].
  exact egg_no_mkgeodesic.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  G3: ambient manifold — one closed term, stays QEX.                      *)
(* -------------------------------------------------------------------------- *)

(* Read the sheet as (lon, lat). The great circle through (-90,45) and
   (90,45) is the meridian pair through the north pole (0,90). The sheet
   chord between them is the parallel y = 45 and never reaches the pole. *)
Definition g3_a : Point := mkPoint (-90) 45.
Definition g3_b : Point := mkPoint 90 45.
Definition g3_pole : Point := mkPoint 0 90.
Definition g3_chord : ChordEgg := mkChordEgg g3_a g3_b.

Lemma sheet_chord_misses_pole :
  ~ exists t, on_chord g3_chord t g3_pole.
Proof.
  intros [t [_ Ht]].
  unfold chord_eval, g3_chord, g3_a, g3_b, g3_pole in Ht; cbn [ce_p0 ce_p1 px py] in Ht.
  injection Ht as _ Hy. lra.
Qed.

Lemma sheet_chord_midpoint_on_parallel :
  chord_eval g3_chord (1/2) = mkPoint 0 45.
Proof.
  unfold chord_eval, g3_chord, g3_a, g3_b; cbn [ce_p0 ce_p1 px py].
  apply (f_equal2 mkPoint); lra.
Qed.

(* WITNESS {"claimId":"0007-geodesic-cook","topic":"overlay","lemma":"ticket_0007_geodesic_ambient_qed_or_qex","title":"G3 ambient manifold: a second sheet class with a sphere / ellipsoid geodesic interpolant inhabits (QED, needs a new ADR); or the sheet chord (-90,45)-(90,45) never passes through the pole (0,90) that the great circle through those points does, so IntakeGeodesic on S^2 does not inhabit MkChord equality and IG_AmbientManifold stays a park (QEX); discharged QEX","file":"theories/IntakeGeodesicCook.v","witness":"0007-geodesic-cook","board":"ADR-0007"} *)
Theorem ticket_0007_geodesic_ambient_qed_or_qex :
  intake_geodesic_qex_inhabits IG_AmbientManifold
  \/
  (~ intake_geodesic_qex_inhabits IG_AmbientManifold
   /\ ~ intake_geodesic_qex_inhabits IG_EllipsoidGamma
   /\ ~ (exists t, on_chord g3_chord t g3_pole)
   /\ chord_eval g3_chord (1/2) = mkPoint 0 45).
Proof.
  right.
  split; [exact intake_geodesic_ambient_missing |].
  split; [exact intake_geodesic_ellipsoid_missing |].
  split; [exact sheet_chord_misses_pole |].
  exact sheet_chord_midpoint_on_parallel.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  G4: wire format — stays QEX; kernel stores chords, tau = LINESTRING.    *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-geodesic-cook","topic":"overlay","lemma":"ticket_0007_geodesic_wire_qed_or_qex","title":"G4 wire format: emit / WKB 13 / tau = pi inhabit so the view prints GEODESICSTRING (QED, needs a view letter); or they stay parks while every egg the kernel stores carries tau = LINESTRING and pi(GEODESICSTRING) has no signed tag (QEX); discharged QEX","file":"theories/IntakeGeodesicCook.v","witness":"0007-geodesic-cook","board":"ADR-0007"} *)
Theorem ticket_0007_geodesic_wire_qed_or_qex :
  (intake_geodesic_qex_inhabits IG_Wkb13SignedIo
   /\ intake_geodesic_qex_inhabits IG_EmitGeodesicBytes
   /\ intake_geodesic_qex_inhabits IG_TauEqPiOnGeodesicProd)
  \/
  (~ intake_geodesic_qex_inhabits IG_Wkb13SignedIo
   /\ ~ intake_geodesic_qex_inhabits IG_EmitGeodesicBytes
   /\ ~ intake_geodesic_qex_inhabits IG_TauEqPiOnGeodesicProd
   /\ (forall c, first_slice_tag (MkChord c) = Some TagLineString)
   /\ t_signed_of_prod PiGeodesicString = None).
Proof.
  right.
  split; [exact intake_geodesic_wkb13_missing |].
  split; [exact intake_geodesic_emit_missing |].
  split; [exact intake_geodesic_tau_eq_pi_missing |].
  split; [exact first_slice_tag_chord |].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  G5: first cook is not expanded.                                         *)
(* -------------------------------------------------------------------------- *)

Lemma geodesic_class_never_first_cook :
  forall c, ~ first_cook_scope EggGeodesicString c /\ ~ first_cook_scope c EggGeodesicString.
Proof. intros c; destruct c; split; intro H; exact H. Qed.

Lemma chord_arc_not_first_cook : ~ first_cook_scope EggChord EggCircularArc.
Proof. intro H. exact H. Qed.

(* WITNESS {"claimId":"0007-geodesic-cook","topic":"overlay","lemma":"ticket_0007_geodesic_scope_qed_or_qex","title":"G5 first cook not expanded: EggGeodesicString is in first_cook_scope with nothing, ~ first_cook_scope EggChord EggCircularArc still holds, and every chicken of a geodesic bag has class EggChord (QED); or first_cook_scope EggGeodesicString EggGeodesicString inhabits (QEX, reject); discharged QED","file":"theories/IntakeGeodesicCook.v","witness":"0007-geodesic-cook","board":"ADR-0007"} *)
Theorem ticket_0007_geodesic_scope_qed_or_qex :
  ((forall c, ~ first_cook_scope EggGeodesicString c /\ ~ first_cook_scope c EggGeodesicString)
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ ~ intake_geodesic_qex_inhabits IG_FirstCookExpand
   /\ (forall s pts ck, In ck (bag_chickens (map_ls s pts)) -> egg_class (ck_egg ck) = EggChord))
  \/
  first_cook_scope EggGeodesicString EggGeodesicString.
Proof.
  left.
  split; [exact geodesic_class_never_first_cook |].
  split; [exact chord_arc_not_first_cook |].
  split; [exact intake_geodesic_no_first_cook_expand |].
  intros s pts ck Hin.
  destruct (geodesic_bag_eggs_mkchord s pts ck Hin) as [p [q Hpq]].
  rewrite Hpq. reflexivity.
Qed.

Print Assumptions ticket_0007_geodesic_intake_fn_qed_or_qex.
Print Assumptions ticket_0007_geodesic_cook_qed_or_qex.
Print Assumptions ticket_0007_geodesic_famous_chords_qed_or_qex.
Print Assumptions ticket_0007_geodesic_ambient_qed_or_qex.
Print Assumptions ticket_0007_geodesic_wire_qed_or_qex.
Print Assumptions ticket_0007_geodesic_scope_qed_or_qex.
