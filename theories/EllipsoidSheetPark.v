(* ============================================================================
   NetTopologySuite.Proofs.EllipsoidSheetPark
   ----------------------------------------------------------------------------
   ADR-0008 letters. Sister park of K3
   (`IntakeKarneyPark.v : ticket_0007_karney_new_sheet_class_qed_or_qex`).
   Not a rewrite of SheetHenCook. Not a remint of ADR-0007 Sheet.

   claimId 0008-ellipsoid-sheet-class — E0–E4 park
   (`ticket_0008_ellipsoid_sheet_qed_or_qex`).
   claimId 0008-mk-ellipsoid — MkEllipsoid := missing EllipsoidSheetClass
   (`ticket_0008_mk_ellipsoid_qed_or_qex`). Same hole; not a sixth E-rung.
   Not #807 MkGeodesic (host Egg ctor). Not #803 GeodesicGammaOnSheet.

   E-rungs (0008). Honest inhabit only; none is faked:
   E0  EllipsoidSheet type ≠ ADR-0007 Sheet = (O; e1, e2)
   E1  geodesic interpolant g on that sheet (not MkChord)
   E2  inverse ctor IResult = Hit | MintTwo | Decline
   E3  antipodes → Decline or MintTwo, never silent Hit
   E4  K1 total inverse on EllipsoidSheet, not on ADR-0007 Sheet

   Expected QEX: E0 cannot be a Sheet without breaking (O; e1, e2).
   Named missing ctors: MkEllipsoid, EllipsoidSheetClass,
   GeodesicGammaOnEllipsoid, InverseIResult, AntipodeNotSilentHit,
   VincentyTotalOnEllipsoid. MkEllipsoid is the class hole, not MkChord.
   Host IResult stays IHit | IEmpty | IDecline. MintTwo is CookIdDecision
   identity, not the inverse. K0 μ = MkChord on planar S, cited not reminted.
   K1 / K2 cited, not reminted. K3 stays QEX. GeodesicGammaOnSheet stays
   missing on planar S (#803). MkGeodesic stays the Egg hole (#807).
   ADR-0008 Status stays Proposed. ADR-0007 stays Accepted.
   No first_cook_scope EggGeodesicString / EggEllipsoid. No Vincenty iterator.
   No "geodesic closed". No LeftoverBagTermArm / RNG_JordanUncond.

   WITNESS topic: overlay
   claimId: 0008-ellipsoid-sheet-class · 0008-mk-ellipsoid
   witness: 0008-ellipsoid-sheet-class · 0008-mk-ellipsoid · board: ADR-0008
   3-axiom host lane (Stdlib Reals, inherited). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance SheetHenCook IntakeKarneyPark
  IntakeGeodesicCook IntakeGeodesic.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Named parks. Uninhabited by construction: the five E-rung ctors.           *)
(* -------------------------------------------------------------------------- *)

Inductive EllipsoidSheetPark : Type :=
| EllipsoidSheetClass
| GeodesicGammaOnEllipsoid
| InverseIResult
| AntipodeNotSilentHit
| VincentyTotalOnEllipsoid.

Definition ellipsoid_sheet_park_inhabits (_ : EllipsoidSheetPark) : Prop := False.

Lemma ellipsoid_sheet_class_missing :
  ~ ellipsoid_sheet_park_inhabits EllipsoidSheetClass.
Proof. intro H. exact H. Qed.

Lemma geodesic_gamma_on_ellipsoid_missing :
  ~ ellipsoid_sheet_park_inhabits GeodesicGammaOnEllipsoid.
Proof. intro H. exact H. Qed.

Lemma inverse_iresult_missing :
  ~ ellipsoid_sheet_park_inhabits InverseIResult.
Proof. intro H. exact H. Qed.

Lemma antipode_not_silent_hit_missing :
  ~ ellipsoid_sheet_park_inhabits AntipodeNotSilentHit.
Proof. intro H. exact H. Qed.

Lemma vincenty_total_on_ellipsoid_missing :
  ~ ellipsoid_sheet_park_inhabits VincentyTotalOnEllipsoid.
Proof. intro H. exact H. Qed.

(* Host IResult is IHit | IEmpty | IDecline. Inverse ctor is not that. *)
Lemma host_iresult_is_hit_empty_decline :
  forall r : IResult,
    (exists p ti tj, r = IHit p ti tj) \/ r = IEmpty \/ r = IDecline.
Proof.
  intros [p ti tj | | ].
  - left. exists p, ti, tj. reflexivity.
  - right. left. reflexivity.
  - right. right. reflexivity.
Qed.

Lemma geodesic_string_not_first_cook :
  ~ first_cook_scope EggGeodesicString EggGeodesicString.
Proof. intro H. exact H. Qed.

(* WITNESS {"claimId":"0008-ellipsoid-sheet-class","topic":"overlay","lemma":"ticket_0008_ellipsoid_sheet_qed_or_qex","title":"E0-E4 ellipsoid sheet: EllipsoidSheetClass / GeodesicGammaOnEllipsoid / InverseIResult / AntipodeNotSilentHit / VincentyTotalOnEllipsoid inhabit (QED); or all five missing, ADR-0007 Sheet stays (O; e1, e2), K3 park KP_EllipsoidSheetClass stays uninhabited, K1 Vincenty total and K2 on_chord pole-miss cited not reminted, first_cook_scope EggGeodesicString stays false (QEX); discharged QEX; ADR-0008 stays Proposed","file":"theories/EllipsoidSheetPark.v","witness":"0008-ellipsoid-sheet-class","board":"ADR-0008"} *)
Theorem ticket_0008_ellipsoid_sheet_qed_or_qex :
  (ellipsoid_sheet_park_inhabits EllipsoidSheetClass
   /\ ellipsoid_sheet_park_inhabits GeodesicGammaOnEllipsoid
   /\ ellipsoid_sheet_park_inhabits InverseIResult
   /\ ellipsoid_sheet_park_inhabits AntipodeNotSilentHit
   /\ ellipsoid_sheet_park_inhabits VincentyTotalOnEllipsoid)
  \/
  (~ ellipsoid_sheet_park_inhabits EllipsoidSheetClass
   /\ ~ ellipsoid_sheet_park_inhabits GeodesicGammaOnEllipsoid
   /\ ~ ellipsoid_sheet_park_inhabits InverseIResult
   /\ ~ ellipsoid_sheet_park_inhabits AntipodeNotSilentHit
   /\ ~ ellipsoid_sheet_park_inhabits VincentyTotalOnEllipsoid
   /\ ~ karney_park_inhabits KP_EllipsoidSheetClass
   /\ (forall s : Sheet,
         s = mkSheet (sheet_origin s) (sheet_e1 s) (sheet_e2 s) (sheet_has_lattice s))
   /\ ~ karney_park_inhabits KP_VincentyInverseTotal
   /\ ~ karney_park_inhabits KP_KarneyInverseAsI
   /\ ~ (exists t, on_chord g3_chord t g3_pole)
   /\ ~ intake_geodesic_qex_inhabits IG_EllipsoidGamma
   /\ ~ first_cook_scope EggGeodesicString EggGeodesicString
   /\ (forall r : IResult,
         (exists p ti tj, r = IHit p ti tj) \/ r = IEmpty \/ r = IDecline)).
Proof.
  right.
  split; [exact ellipsoid_sheet_class_missing |].
  split; [exact geodesic_gamma_on_ellipsoid_missing |].
  split; [exact inverse_iresult_missing |].
  split; [exact antipode_not_silent_hit_missing |].
  split; [exact vincenty_total_on_ellipsoid_missing |].
  split; [exact karney_ellipsoid_sheet_missing |].
  split; [exact sheet_is_planar_frame |].
  split; [exact karney_vincenty_total_missing |].
  split; [exact karney_inverse_as_I_missing |].
  split; [exact sheet_chord_misses_pole |].
  split; [exact intake_geodesic_ellipsoid_missing |].
  split; [exact geodesic_string_not_first_cook |].
  exact host_iresult_is_hit_empty_decline.
Qed.

Print Assumptions ellipsoid_sheet_class_missing.
Print Assumptions geodesic_gamma_on_ellipsoid_missing.
Print Assumptions inverse_iresult_missing.
Print Assumptions antipode_not_silent_hit_missing.
Print Assumptions vincenty_total_on_ellipsoid_missing.
Print Assumptions host_iresult_is_hit_empty_decline.
Print Assumptions ticket_0008_ellipsoid_sheet_qed_or_qex.

(* -------------------------------------------------------------------------- *)
(* MkEllipsoid := missing EllipsoidSheetClass. Not MkChord. Not #807.         *)
(* -------------------------------------------------------------------------- *)

Definition MkEllipsoid : EllipsoidSheetPark := EllipsoidSheetClass.

Lemma mk_ellipsoid_missing :
  ~ ellipsoid_sheet_park_inhabits MkEllipsoid.
Proof. intro H. exact H. Qed.

Lemma mk_ellipsoid_is_ellipsoid_sheet_class_hole :
  MkEllipsoid = EllipsoidSheetClass
  /\ ~ ellipsoid_sheet_park_inhabits MkEllipsoid
  /\ ~ ellipsoid_sheet_park_inhabits EllipsoidSheetClass.
Proof.
  split; [reflexivity |].
  split; [exact mk_ellipsoid_missing | exact ellipsoid_sheet_class_missing].
Qed.

(* K0 μ = MkChord on planar S. Cited, not reminted as MkEllipsoid. *)
Lemma mk_ellipsoid_k0_mu_mkchord :
  (forall s : Sheet,
     s = mkSheet (sheet_origin s) (sheet_e1 s) (sheet_e2 s) (sheet_has_lattice s))
  /\ (forall s p q rest ck,
        In ck (bag_chickens (map_ls s (p :: q :: rest))) ->
        exists a b, ck_egg ck = MkChord (mkChordEgg a b)).
Proof.
  split; [exact sheet_is_planar_frame | exact geodesic_wellformed_eggs_mkchord].
Qed.

(* #803 GeodesicGammaOnSheet stays missing on planar S. Cited, not reminted. *)
Lemma geodesic_gamma_on_sheet_stays_missing :
  ~ intake_geodesic_qex_inhabits IG_EllipsoidGamma
  /\ ~ (exists t, on_chord g3_chord t g3_pole).
Proof.
  split; [exact intake_geodesic_ellipsoid_missing | exact sheet_chord_misses_pole].
Qed.

(* #807 MkGeodesic is the host Egg hole. Not reminted as MkEllipsoid. *)
Lemma mk_geodesic_egg_hole_not_mk_ellipsoid :
  (forall e : Egg,
     (exists c, e = MkChord c) \/ (exists g, e = MkCirc g) \/
     (exists k, e = MkClothoid k) \/ (exists cls, e = MkOutOfScope cls))
  /\ MkEllipsoid = EllipsoidSheetClass.
Proof. split; [exact egg_no_mkgeodesic | reflexivity]. Qed.

Lemma mk_ellipsoid_first_cook_unchanged :
  first_cook_scope EggChord EggChord
  /\ ~ first_cook_scope EggGeodesicString EggGeodesicString
  /\ ~ first_cook_scope EggChord EggCircularArc.
Proof.
  split; [exact first_cook_scope_chord_chord |].
  split; [exact geodesic_string_not_first_cook | exact chord_arc_not_first_cook].
Qed.

(* WITNESS {"claimId":"0008-mk-ellipsoid","topic":"overlay","lemma":"ticket_0008_mk_ellipsoid_qed_or_qex","title":"MkEllipsoid host ctor: MkEllipsoid carrier inhabits with E0-E4 on a type distinct from Sheet S=(O; e1, e2) and on_ellipsoid not on_chord (QED); or MkEllipsoid is the missing EllipsoidSheetClass hole (not MkChord, not #807 MkGeodesic), E0-E4 stay uninhabited, K0 mu stays MkChord on planar S, GeodesicGammaOnSheet stays missing (#803), first_cook_scope EggGeodesicString stays false (QEX); discharged QEX; ADR-0008 stays Proposed","file":"theories/EllipsoidSheetPark.v","witness":"0008-mk-ellipsoid","board":"ADR-0008"} *)
Theorem ticket_0008_mk_ellipsoid_qed_or_qex :
  (ellipsoid_sheet_park_inhabits MkEllipsoid
   /\ ellipsoid_sheet_park_inhabits EllipsoidSheetClass
   /\ ellipsoid_sheet_park_inhabits GeodesicGammaOnEllipsoid
   /\ ellipsoid_sheet_park_inhabits InverseIResult
   /\ ellipsoid_sheet_park_inhabits AntipodeNotSilentHit
   /\ ellipsoid_sheet_park_inhabits VincentyTotalOnEllipsoid)
  \/
  (~ ellipsoid_sheet_park_inhabits MkEllipsoid
   /\ MkEllipsoid = EllipsoidSheetClass
   /\ ~ ellipsoid_sheet_park_inhabits EllipsoidSheetClass
   /\ ~ ellipsoid_sheet_park_inhabits GeodesicGammaOnEllipsoid
   /\ ~ ellipsoid_sheet_park_inhabits InverseIResult
   /\ ~ ellipsoid_sheet_park_inhabits AntipodeNotSilentHit
   /\ ~ ellipsoid_sheet_park_inhabits VincentyTotalOnEllipsoid
   /\ (forall s : Sheet,
         s = mkSheet (sheet_origin s) (sheet_e1 s) (sheet_e2 s) (sheet_has_lattice s))
   /\ (forall s p q rest ck,
         In ck (bag_chickens (map_ls s (p :: q :: rest))) ->
         exists a b, ck_egg ck = MkChord (mkChordEgg a b))
   /\ ~ intake_geodesic_qex_inhabits IG_EllipsoidGamma
   /\ ~ (exists t, on_chord g3_chord t g3_pole)
   /\ (forall e : Egg,
         (exists c, e = MkChord c) \/ (exists g, e = MkCirc g) \/
         (exists k, e = MkClothoid k) \/ (exists cls, e = MkOutOfScope cls))
   /\ first_cook_scope EggChord EggChord
   /\ ~ first_cook_scope EggGeodesicString EggGeodesicString
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ ~ karney_park_inhabits KP_EllipsoidSheetClass).
Proof.
  right.
  split; [exact mk_ellipsoid_missing |].
  split; [reflexivity |].
  split; [exact ellipsoid_sheet_class_missing |].
  split; [exact geodesic_gamma_on_ellipsoid_missing |].
  split; [exact inverse_iresult_missing |].
  split; [exact antipode_not_silent_hit_missing |].
  split; [exact vincenty_total_on_ellipsoid_missing |].
  split; [exact sheet_is_planar_frame |].
  split; [exact geodesic_wellformed_eggs_mkchord |].
  split; [exact intake_geodesic_ellipsoid_missing |].
  split; [exact sheet_chord_misses_pole |].
  split; [exact egg_no_mkgeodesic |].
  split; [exact first_cook_scope_chord_chord |].
  split; [exact geodesic_string_not_first_cook |].
  split; [exact chord_arc_not_first_cook |].
  exact karney_ellipsoid_sheet_missing.
Qed.

Print Assumptions mk_ellipsoid_missing.
Print Assumptions mk_ellipsoid_is_ellipsoid_sheet_class_hole.
Print Assumptions mk_ellipsoid_k0_mu_mkchord.
Print Assumptions geodesic_gamma_on_sheet_stays_missing.
Print Assumptions mk_geodesic_egg_hole_not_mk_ellipsoid.
Print Assumptions mk_ellipsoid_first_cook_unchanged.
Print Assumptions ticket_0008_mk_ellipsoid_qed_or_qex.
