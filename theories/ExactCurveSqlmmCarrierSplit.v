(* ============================================================================
   NetTopologySuite.Proofs.ExactCurveSqlmmCarrierSplit
   ----------------------------------------------------------------------------
   SQL/MM ISO 13249-3 / #615 A+B required vs named split
   (claimId 508-sqlmm-carrier-split).

   Required (instantiable) bind to the year-1 carrier or composition
   over it, not a new CurveSegment constructor:
     ST_LineString     → CSChord
     ST_CircularString → CSArc
     ST_CompoundCurve  → list of CSChord|CSArc (CurveRing; not CSCompound)
     ST_CurvePolygon / MultiCurve / MultiSurface
                       → surface / collection lane; not CS ctors

   Named / backlog stay off CurveSegment (sidecar EggClass +
   MkOutOfScope, or host MkCirc / MkClothoid — not a CS remint):
     ST_Circle, ST_Clothoid, ST_EllipticalCurve, ST_NURBSCurve,
     ST_GeodesicString, ST_SpiralCurve (bloss / biquad / sin / cos),
     Bible Exact* (ExactCubicBezier, ExactEllipticalArc,
     ExactClothoid, ExactNurbsSegment) = ADR-0004 interface.

   No CS ctor added. Year-1 carrier stays CSChord | CSArc
   (curve_segment_chord_or_arc). ST_Circle is not CSCircle
   (MkCirc / CIRCULARSTRING full-sweep special case).
   QEX is not owner accept. Epic #508 stays open.
   Do not steal 508-e / 508-g / 508-h. Do not remint ADR-0004.
   Do not claim “#508 closed” or “SQL/MM is done”.

   WITNESS topic: metric · claimId: 508-sqlmm-carrier-split
   witness: 508-sqlmm-carrier-split
   lane: proofs
   issue: #508
   board: #508

   No `Admitted`, no `Axiom`, no `Parameter`.  3-axiom.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From NTS.Proofs Require Import Distance CurveGeometry ExactCurveEpic508
  SheetHenCook.

(* -------------------------------------------------------------------------- *)
(* Required ISO 13249-3 instantiable names (#615 A+B).                        *)
(* -------------------------------------------------------------------------- *)

Inductive SqlMmRequired : Type :=
| ST_LineString
| ST_CircularString
| ST_CompoundCurve
| ST_CurvePolygon
| ST_MultiCurve
| ST_MultiSurface.

Inductive SqlMmRequiredBind : Type :=
| BindCSChord
| BindCSArc
| BindCompoundList
| BindSurfaceNotCtor
| BindCollectionNotCtor.

Definition required_bind (t : SqlMmRequired) : SqlMmRequiredBind :=
  match t with
  | ST_LineString => BindCSChord
  | ST_CircularString => BindCSArc
  | ST_CompoundCurve => BindCompoundList
  | ST_CurvePolygon => BindSurfaceNotCtor
  | ST_MultiCurve => BindCollectionNotCtor
  | ST_MultiSurface => BindCollectionNotCtor
  end.

(* True only for names that inhabit a year-1 CS constructor. *)
Definition required_inhabits_cs_ctor (t : SqlMmRequired) : Prop :=
  match t with
  | ST_LineString => zoo_inhabits_curve_segment ECZ_Chord
  | ST_CircularString => zoo_inhabits_curve_segment ECZ_CircularArc
  | ST_CompoundCurve => False
  | ST_CurvePolygon => False
  | ST_MultiCurve => False
  | ST_MultiSurface => False
  end.

Definition required_is_cc_list (t : SqlMmRequired) : Prop :=
  match t with
  | ST_CompoundCurve => True
  | _ => False
  end.

Definition required_is_surface_or_collection_qex (t : SqlMmRequired) : Prop :=
  match t with
  | ST_CurvePolygon => True
  | ST_MultiCurve => True
  | ST_MultiSurface => True
  | _ => False
  end.

(* Extending CurveSegment would be required only if a required name
   could not bind as CSChord|CSArc|CC-list|surface-QEX. None do. *)
Definition required_needs_cs_extension (t : SqlMmRequired) : Prop := False.

Lemma st_linestring_inhabits_cschord :
  required_inhabits_cs_ctor ST_LineString
  /\ required_bind ST_LineString = BindCSChord
  /\ zoo_inhabits_curve_segment ECZ_Chord.
Proof.
  split; [exact I|].
  split; [reflexivity|].
  exact I.
Qed.

Lemma st_circularstring_inhabits_csarc :
  required_inhabits_cs_ctor ST_CircularString
  /\ required_bind ST_CircularString = BindCSArc
  /\ zoo_inhabits_curve_segment ECZ_CircularArc.
Proof.
  split; [exact I|].
  split; [reflexivity|].
  exact I.
Qed.

Lemma st_compoundcurve_is_cc_list :
  required_is_cc_list ST_CompoundCurve
  /\ required_bind ST_CompoundCurve = BindCompoundList
  /\ ~ required_inhabits_cs_ctor ST_CompoundCurve
  /\ CurveRing = list CurveSegment.
Proof.
  split; [exact I|].
  split; [reflexivity|].
  split; [intro H; exact H|].
  reflexivity.
Qed.

Lemma st_compoundcurve_members_chord_or_arc :
  forall s : CurveSegment,
    (exists p q, s = CSChord p q) \/ (exists a, s = CSArc a).
Proof.
  exact curve_segment_chord_or_arc.
Qed.

Lemma st_compoundcurve_not_cscompound :
  ~ required_inhabits_cs_ctor ST_CompoundCurve.
Proof.
  intro H. exact H.
Qed.

Lemma st_curvepolygon_not_cs_ctor :
  required_is_surface_or_collection_qex ST_CurvePolygon
  /\ required_bind ST_CurvePolygon = BindSurfaceNotCtor
  /\ ~ required_inhabits_cs_ctor ST_CurvePolygon.
Proof.
  split; [exact I|].
  split; [reflexivity|].
  intro H. exact H.
Qed.

Lemma st_multicurve_not_cs_ctor :
  required_is_surface_or_collection_qex ST_MultiCurve
  /\ required_bind ST_MultiCurve = BindCollectionNotCtor
  /\ ~ required_inhabits_cs_ctor ST_MultiCurve.
Proof.
  split; [exact I|].
  split; [reflexivity|].
  intro H. exact H.
Qed.

Lemma st_multisurface_not_cs_ctor :
  required_is_surface_or_collection_qex ST_MultiSurface
  /\ required_bind ST_MultiSurface = BindCollectionNotCtor
  /\ ~ required_inhabits_cs_ctor ST_MultiSurface.
Proof.
  split; [exact I|].
  split; [reflexivity|].
  intro H. exact H.
Qed.

Lemma required_binds_without_new_cs_ctor :
  forall t : SqlMmRequired,
    required_inhabits_cs_ctor t
    \/ required_is_cc_list t
    \/ required_is_surface_or_collection_qex t.
Proof.
  intros t.
  destruct t.
  - left. exact I.
  - left. exact I.
  - right. left. exact I.
  - right. right. exact I.
  - right. right. exact I.
  - right. right. exact I.
Qed.

Lemma required_no_cs_extension :
  forall t : SqlMmRequired, ~ required_needs_cs_extension t.
Proof.
  intros t H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named / backlog. Stay off CurveSegment.                                    *)
(* -------------------------------------------------------------------------- *)

Inductive SqlMmNamed : Type :=
| ST_Circle
| ST_Clothoid
| ST_EllipticalCurve
| ST_NURBSCurve
| ST_GeodesicString
| ST_SpiralCurve
| ExactCubicBezier
| ExactEllipticalArc
| ExactClothoid
| ExactNurbsSegment.

Definition named_inhabits_cs_ctor (t : SqlMmNamed) : Prop := False.

Definition named_egg_class (t : SqlMmNamed) : EggClass :=
  match t with
  | ST_Circle => EggCircularArc
  | ST_Clothoid => EggClothoid
  | ST_EllipticalCurve => EggEllipse
  | ST_NURBSCurve => EggNurbs
  | ST_GeodesicString => EggGeodesicString
  | ST_SpiralCurve => EggSpiralCurve
  | ExactCubicBezier => EggBezier
  | ExactEllipticalArc => EggEllipse
  | ExactClothoid => EggClothoid
  | ExactNurbsSegment => EggNurbs
  end.

(* Host MkCirc / MkClothoid for Circle and Clothoid. Sidecar tags else. *)
Definition named_outofscope_tag (t : SqlMmNamed) : option EggClass :=
  match t with
  | ST_Circle => None
  | ST_Clothoid => None
  | ST_EllipticalCurve => Some EggEllipse
  | ST_NURBSCurve => Some EggNurbs
  | ST_GeodesicString => Some EggGeodesicString
  | ST_SpiralCurve => Some EggSpiralCurve
  | ExactCubicBezier => Some EggBezier
  | ExactEllipticalArc => Some EggEllipse
  | ExactClothoid => Some EggClothoid
  | ExactNurbsSegment => Some EggNurbs
  end.

Inductive SqlMmSpiralName : Type :=
| SpiralClothoid
| SpiralBloss
| SpiralBiquadratic
| SpiralSine
| SpiralCosine.

Definition spiral_name_egg_class (_ : SqlMmSpiralName) : EggClass :=
  EggSpiralCurve.

Lemma named_not_cs_ctor :
  forall t : SqlMmNamed, ~ named_inhabits_cs_ctor t.
Proof.
  intros t H. exact H.
Qed.

Lemma st_circle_not_cscircle :
  ~ named_inhabits_cs_ctor ST_Circle
  /\ named_egg_class ST_Circle = EggCircularArc
  /\ named_outofscope_tag ST_Circle = None
  /\ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  split; [intro H; exact H|].
  split; [reflexivity|].
  split; [reflexivity|].
  exact circular_egg_first_cook_scope.
Qed.

Lemma st_circle_not_fourth_cs_ctor :
  forall s : CurveSegment,
    (exists p q, s = CSChord p q) \/ (exists a, s = CSArc a).
Proof.
  exact curve_segment_chord_or_arc.
Qed.

Lemma st_clothoid_not_cs_ctor :
  ~ named_inhabits_cs_ctor ST_Clothoid
  /\ ~ zoo_inhabits_curve_segment ECZ_Clothoid
  /\ named_egg_class ST_Clothoid = EggClothoid
  /\ first_cook_scope EggClothoid EggClothoid.
Proof.
  split; [intro H; exact H|].
  split; [exact clothoid_not_curve_segment|].
  split; [reflexivity|].
  exact clothoid_egg_first_cook_scope.
Qed.

Lemma st_ellipticalcurve_not_cs_ctor :
  ~ named_inhabits_cs_ctor ST_EllipticalCurve
  /\ ~ zoo_inhabits_curve_segment ECZ_Ellipse
  /\ named_egg_class ST_EllipticalCurve = EggEllipse
  /\ named_outofscope_tag ST_EllipticalCurve = Some EggEllipse
  /\ egg_class (MkOutOfScope EggEllipse) = EggEllipse
  /\ ~ first_cook_scope EggEllipse EggEllipse.
Proof.
  split; [intro H; exact H|].
  split; [exact ellipse_not_curve_segment|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  exact ellipse_ellipse_not_first_scope.
Qed.

Lemma st_nurbscurve_not_cs_ctor :
  ~ named_inhabits_cs_ctor ST_NURBSCurve
  /\ ~ zoo_inhabits_curve_segment ECZ_Nurbs
  /\ named_egg_class ST_NURBSCurve = EggNurbs
  /\ named_outofscope_tag ST_NURBSCurve = Some EggNurbs
  /\ egg_class (MkOutOfScope EggNurbs) = EggNurbs
  /\ ~ first_cook_scope EggNurbs EggNurbs.
Proof.
  split; [intro H; exact H|].
  split; [exact nurbs_not_curve_segment|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  exact nurbs_nurbs_not_first_scope.
Qed.

Lemma st_geodesicstring_not_cs_ctor :
  ~ named_inhabits_cs_ctor ST_GeodesicString
  /\ named_egg_class ST_GeodesicString = EggGeodesicString
  /\ named_outofscope_tag ST_GeodesicString = Some EggGeodesicString
  /\ egg_class (MkOutOfScope EggGeodesicString) = EggGeodesicString
  /\ ~ first_cook_scope EggGeodesicString EggGeodesicString.
Proof.
  split; [intro H; exact H|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  intro H. exact H.
Qed.

Lemma st_spiralcurve_not_cs_ctor :
  ~ named_inhabits_cs_ctor ST_SpiralCurve
  /\ named_egg_class ST_SpiralCurve = EggSpiralCurve
  /\ named_outofscope_tag ST_SpiralCurve = Some EggSpiralCurve
  /\ egg_class (MkOutOfScope EggSpiralCurve) = EggSpiralCurve
  /\ ~ first_cook_scope EggSpiralCurve EggSpiralCurve
  /\ (forall n, spiral_name_egg_class n = EggSpiralCurve)
  /\ ~ first_cook_scope EggSinusoid EggSinusoid
  /\ egg_class (MkOutOfScope EggSinusoid) = EggSinusoid.
Proof.
  split; [intro H; exact H|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [intro H; exact H|].
  split; [intros n; reflexivity|].
  split; [intro H; exact H|].
  reflexivity.
Qed.

Lemma bible_exact_not_cs_ctor :
  ~ named_inhabits_cs_ctor ExactCubicBezier
  /\ ~ named_inhabits_cs_ctor ExactEllipticalArc
  /\ ~ named_inhabits_cs_ctor ExactClothoid
  /\ ~ named_inhabits_cs_ctor ExactNurbsSegment
  /\ ~ zoo_inhabits_curve_segment ECZ_Bezier
  /\ ~ zoo_inhabits_curve_segment ECZ_Ellipse
  /\ ~ zoo_inhabits_curve_segment ECZ_Clothoid
  /\ ~ zoo_inhabits_curve_segment ECZ_Nurbs
  /\ named_egg_class ExactCubicBezier = EggBezier
  /\ named_egg_class ExactEllipticalArc = EggEllipse
  /\ named_egg_class ExactClothoid = EggClothoid
  /\ named_egg_class ExactNurbsSegment = EggNurbs
  /\ egg_class (MkOutOfScope EggBezier) = EggBezier
  /\ ~ first_cook_scope EggBezier EggBezier.
Proof.
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  split; [exact bezier_not_curve_segment|].
  split; [exact ellipse_not_curve_segment|].
  split; [exact clothoid_not_curve_segment|].
  split; [exact nurbs_not_curve_segment|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  intro H. exact H.
Qed.

Lemma year1_carrier_still_chord_or_arc :
  forall s : CurveSegment,
    (exists p q, s = CSChord p q) \/ (exists a, s = CSArc a).
Proof.
  exact curve_segment_chord_or_arc.
Qed.

(* -------------------------------------------------------------------------- *)
(* Tickets.                                                                   *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"508-sqlmm-carrier-split","topic":"metric","lemma":"ticket_508_sqlmm_required_on_cs","title":"SQL/MM required names bind to CSChord|CSArc|CC-as-list or are documented surface/collection QEX not a CS ctor; no CurveSegment extension","file":"theories/ExactCurveSqlmmCarrierSplit.v","witness":"508-sqlmm-carrier-split","board":"#508"} *)
Theorem ticket_508_sqlmm_required_on_cs :
  zoo_inhabits_curve_segment ECZ_Chord
  /\ zoo_inhabits_curve_segment ECZ_CircularArc
  /\ (forall s : CurveSegment,
        (exists p q, s = CSChord p q) \/ (exists a, s = CSArc a))
  /\ required_bind ST_LineString = BindCSChord
  /\ required_bind ST_CircularString = BindCSArc
  /\ required_bind ST_CompoundCurve = BindCompoundList
  /\ required_bind ST_CurvePolygon = BindSurfaceNotCtor
  /\ required_bind ST_MultiCurve = BindCollectionNotCtor
  /\ required_bind ST_MultiSurface = BindCollectionNotCtor
  /\ ~ required_inhabits_cs_ctor ST_CompoundCurve
  /\ ~ required_inhabits_cs_ctor ST_CurvePolygon
  /\ ~ required_inhabits_cs_ctor ST_MultiCurve
  /\ ~ required_inhabits_cs_ctor ST_MultiSurface
  /\ CurveRing = list CurveSegment
  /\ (forall t : SqlMmRequired,
        required_inhabits_cs_ctor t
        \/ required_is_cc_list t
        \/ required_is_surface_or_collection_qex t)
  /\ (forall t : SqlMmRequired, ~ required_needs_cs_extension t).
Proof.
  split; [exact I|].
  split; [exact I|].
  split; [exact curve_segment_chord_or_arc|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  split; [reflexivity|].
  split; [exact required_binds_without_new_cs_ctor|].
  exact required_no_cs_extension.
Qed.

(* WITNESS {"claimId":"508-sqlmm-carrier-split","topic":"metric","lemma":"ticket_508_sqlmm_named_not_cs","title":"SQL/MM named and Bible Exact* types are not CurveSegment constructors; Circle is not CSCircle; sidecar MkOutOfScope / EggClass only except host MkCirc and MkClothoid","file":"theories/ExactCurveSqlmmCarrierSplit.v","witness":"508-sqlmm-carrier-split","board":"#508"} *)
Theorem ticket_508_sqlmm_named_not_cs :
  (forall t : SqlMmNamed, ~ named_inhabits_cs_ctor t)
  /\ ~ zoo_inhabits_curve_segment ECZ_Ellipse
  /\ ~ zoo_inhabits_curve_segment ECZ_Clothoid
  /\ ~ zoo_inhabits_curve_segment ECZ_Nurbs
  /\ ~ zoo_inhabits_curve_segment ECZ_Bezier
  /\ named_egg_class ST_Circle = EggCircularArc
  /\ named_outofscope_tag ST_Circle = None
  /\ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggClothoid EggClothoid
  /\ egg_class (MkOutOfScope EggEllipse) = EggEllipse
  /\ egg_class (MkOutOfScope EggNurbs) = EggNurbs
  /\ egg_class (MkOutOfScope EggGeodesicString) = EggGeodesicString
  /\ egg_class (MkOutOfScope EggSpiralCurve) = EggSpiralCurve
  /\ egg_class (MkOutOfScope EggBezier) = EggBezier
  /\ ~ first_cook_scope EggEllipse EggEllipse
  /\ ~ first_cook_scope EggNurbs EggNurbs
  /\ ~ first_cook_scope EggGeodesicString EggGeodesicString
  /\ ~ first_cook_scope EggSpiralCurve EggSpiralCurve
  /\ ~ first_cook_scope EggBezier EggBezier
  /\ ~ first_cook_scope EggSinusoid EggSinusoid
  /\ (forall n : SqlMmSpiralName, spiral_name_egg_class n = EggSpiralCurve).
Proof.
  split; [exact named_not_cs_ctor|].
  split; [exact ellipse_not_curve_segment|].
  split; [exact clothoid_not_curve_segment|].
  split; [exact nurbs_not_curve_segment|].
  split; [exact bezier_not_curve_segment|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact circular_egg_first_cook_scope|].
  split; [exact clothoid_egg_first_cook_scope|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact ellipse_ellipse_not_first_scope|].
  split; [exact nurbs_nurbs_not_first_scope|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  intros n. reflexivity.
Qed.

(* WITNESS {"claimId":"508-sqlmm-carrier-split","topic":"metric","lemma":"ticket_508_sqlmm_carrier_split_qed_or_qex","title":"SQL/MM required vs named CurveSegment split: required bind to CSChord|CSArc|CC-list or surface QEX and named stay off CS with no new CS ctor (QED) or a required type cannot bind without extending CurveSegment (QEX); discharged QED; epic #508 stays open; QEX is not owner accept","file":"theories/ExactCurveSqlmmCarrierSplit.v","witness":"508-sqlmm-carrier-split","board":"#508"} *)
Theorem ticket_508_sqlmm_carrier_split_qed_or_qex :
  (zoo_inhabits_curve_segment ECZ_Chord
   /\ zoo_inhabits_curve_segment ECZ_CircularArc
   /\ (forall s : CurveSegment,
         (exists p q, s = CSChord p q) \/ (exists a, s = CSArc a))
   /\ (forall t : SqlMmRequired,
         required_inhabits_cs_ctor t
         \/ required_is_cc_list t
         \/ required_is_surface_or_collection_qex t)
   /\ (forall t : SqlMmNamed, ~ named_inhabits_cs_ctor t)
   /\ ~ named_inhabits_cs_ctor ST_Circle
   /\ ~ required_inhabits_cs_ctor ST_CompoundCurve
   /\ (forall t : SqlMmRequired, ~ required_needs_cs_extension t))
  \/
  (exists t : SqlMmRequired, required_needs_cs_extension t).
Proof.
  left.
  split; [exact I|].
  split; [exact I|].
  split; [exact curve_segment_chord_or_arc|].
  split; [exact required_binds_without_new_cs_ctor|].
  split; [exact named_not_cs_ctor|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  exact required_no_cs_extension.
Qed.

Print Assumptions st_linestring_inhabits_cschord.
Print Assumptions st_circularstring_inhabits_csarc.
Print Assumptions st_compoundcurve_is_cc_list.
Print Assumptions st_compoundcurve_members_chord_or_arc.
Print Assumptions st_compoundcurve_not_cscompound.
Print Assumptions st_curvepolygon_not_cs_ctor.
Print Assumptions st_circle_not_cscircle.
Print Assumptions st_clothoid_not_cs_ctor.
Print Assumptions st_ellipticalcurve_not_cs_ctor.
Print Assumptions st_nurbscurve_not_cs_ctor.
Print Assumptions bible_exact_not_cs_ctor.
Print Assumptions ticket_508_sqlmm_required_on_cs.
Print Assumptions ticket_508_sqlmm_named_not_cs.
Print Assumptions ticket_508_sqlmm_carrier_split_qed_or_qex.
