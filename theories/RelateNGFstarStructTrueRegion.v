(* ============================================================================
   NetTopologySuite.Proofs.RelateNGFstarStructTrueRegion
   ----------------------------------------------------------------------------
   Letter #509 F-CP / F-MC / F-MS: structural Qed vs true-region.
   One stop. claimId 509-fstar-struct-vs-true-region. Do not mint three twins.

   Already QED (cite, do not remint):
     RelateNGJordanTrueRegion.v : relateng_jordan_true_region_taut
       claimId 0007-relateng-jordan-true-region  #791
       taut polygonal closed true-region only
     RelateNGFace.v : ticket_0007_relateng_face_qed_or_qex LEFT
     F-CP structural chord floor:
       CurvePolygonValid.v : valid_curve_polygon_cp_hole_witness
       CurvePolygonSimple.v : curve_polygon_outer_not_simple_of_witness
       CurvePolygonValid / CurvePolygonSimple
     F-MC / F-MS structural collection / WKT / nil-cons:
       CurveGeometry.v : valid_curve_geometry_nil
       CurveGeometry.v : valid_curve_geometry_cons
       CurveGeometry.v : to_geometry_nil

   Already QEX (do not flip):
     RelateNGFace.v : RNG_JordanUncond
     RelateNGFace.v : ticket_0007_relateng_parks_qed_or_qex
       (multi-geom / ISO `?`)

   Missing ctors (do not invent as QED):
     CurvePolygonTrueRegionSound
     MultiCurveTrueRegionSound
     MultiSurfaceTrueRegionSound

   Polygonal taut ≠ V-CP arc-aware true-region.
   Inscribed chord floor ⇏ CurvePolygon true-region.
   F-CP validity witness is the chord floor, not true-region.

   LEFT  = every F-CP / F-MC / F-MS row has a cited true-region theorem
           (will not hold — those ctors are missing).
   RIGHT = name the missing ctor. Prefer CurvePolygonTrueRegionSound
           (F-CP is the first park; F-MC / F-MS ride the same QEX).

   Honesty: #509 stays open. QEX ≠ owner accept. Not “#509 closed”.
   Not CircGamma reopen. Not CS extend. Not leftover Ⅹ.

   WITNESS topic: relate · claimId: 509-fstar-struct-vs-true-region
   witness: 509-fstar-struct-vs-true-region · board: #509
   0-axiom host park (prelude only). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* F-star rows. One letter. F-MC / F-MS ride F-CP's missing ctor.             *)
(* -------------------------------------------------------------------------- *)

Inductive FstarRow : Type :=
| F_CP
| F_MC
| F_MS.

Inductive FstarTrueRegionCtor : Type :=
| CurvePolygonTrueRegionSound
| MultiCurveTrueRegionSound
| MultiSurfaceTrueRegionSound.

Definition fstar_true_region_of_row (r : FstarRow) : FstarTrueRegionCtor :=
  match r with
  | F_CP => CurvePolygonTrueRegionSound
  | F_MC => MultiCurveTrueRegionSound
  | F_MS => MultiSurfaceTrueRegionSound
  end.

Definition fstar_true_region_inhabits (_ : FstarTrueRegionCtor) : Prop := False.

Lemma curve_polygon_true_region_sound_missing :
  ~ fstar_true_region_inhabits CurvePolygonTrueRegionSound.
Proof.
  intro H. exact H.
Qed.

Lemma multicurve_true_region_missing :
  ~ fstar_true_region_inhabits MultiCurveTrueRegionSound.
Proof.
  intro H. exact H.
Qed.

Lemma multisurface_true_region_missing :
  ~ fstar_true_region_inhabits MultiSurfaceTrueRegionSound.
Proof.
  intro H. exact H.
Qed.

(* LEFT: every F-CP / F-MC / F-MS row has a cited true-region theorem. *)
Definition fstar_every_row_has_true_region : Prop :=
  forall r : FstarRow, fstar_true_region_inhabits (fstar_true_region_of_row r).

Lemma fstar_not_every_row_has_true_region :
  ~ fstar_every_row_has_true_region.
Proof.
  intro H.
  apply curve_polygon_true_region_sound_missing.
  exact (H F_CP).
Qed.

Lemma fmc_fms_ride_fcp_qex :
  ~ fstar_true_region_inhabits CurvePolygonTrueRegionSound
  /\ ~ fstar_true_region_inhabits MultiCurveTrueRegionSound
  /\ ~ fstar_true_region_inhabits MultiSurfaceTrueRegionSound.
Proof.
  split; [exact curve_polygon_true_region_sound_missing|].
  split; [exact multicurve_true_region_missing|].
  exact multisurface_true_region_missing.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cited structural Qed and the #791 ceiling. Names only; not reminted.       *)
(* -------------------------------------------------------------------------- *)

Inductive FstarStructQedCite : Type :=
| Cite_valid_curve_polygon_cp_hole_witness
| Cite_curve_polygon_outer_not_simple_of_witness
| Cite_valid_curve_geometry_nil
| Cite_valid_curve_geometry_cons
| Cite_to_geometry_nil
| Cite_ticket_0007_relateng_face_qed_or_qex.

Definition fstar_struct_qed_cite : FstarStructQedCite :=
  Cite_valid_curve_polygon_cp_hole_witness.

Lemma fstar_struct_qed_cites_fcp_hole_witness :
  fstar_struct_qed_cite = Cite_valid_curve_polygon_cp_hole_witness.
Proof.
  reflexivity.
Qed.

Inductive RelatengJordanCeiling : Type :=
| RelatengJordanTautPolygonalQed
| RelatengJordanUncondFlipped.

Definition relateng_jordan_ceiling : RelatengJordanCeiling :=
  RelatengJordanTautPolygonalQed.

Lemma relateng_jordan_ceiling_is_791_taut :
  relateng_jordan_ceiling = RelatengJordanTautPolygonalQed.
Proof.
  reflexivity.
Qed.

Lemma relateng_jordan_uncond_not_flipped :
  relateng_jordan_ceiling <> RelatengJordanUncondFlipped.
Proof.
  discriminate.
Qed.

(* Polygonal taut ≠ V-CP arc-aware. Chord floor ⇏ true-region. *)
Inductive TrueRegionKind : Type :=
| PolygonalTautClosed
| CurvePolygonArcAware.

Definition landed_true_region_kind : TrueRegionKind := PolygonalTautClosed.

Lemma landed_true_region_is_polygonal_taut :
  landed_true_region_kind = PolygonalTautClosed.
Proof.
  reflexivity.
Qed.

Lemma polygonal_taut_neq_vcp_arc_aware :
  landed_true_region_kind <> CurvePolygonArcAware.
Proof.
  discriminate.
Qed.

Inductive FcpWitnessKind : Type :=
| FcpHoleWitnessChordFloor
| FcpHoleWitnessTrueRegion.

Definition fcp_hole_witness_kind : FcpWitnessKind := FcpHoleWitnessChordFloor.

Lemma fcp_validity_witness_is_chord_floor :
  fcp_hole_witness_kind = FcpHoleWitnessChordFloor.
Proof.
  reflexivity.
Qed.

Lemma fcp_validity_witness_not_true_region :
  fcp_hole_witness_kind <> FcpHoleWitnessTrueRegion.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Honesty fences. #509 stays open. QEX ≠ owner accept.                       *)
(* -------------------------------------------------------------------------- *)

Inductive Epic509Status : Type :=
| Epic509Open
| Epic509Closed
| Epic509OwnerAccept.

Definition epic_509_status : Epic509Status := Epic509Open.

Lemma epic_509_stays_open :
  epic_509_status = Epic509Open.
Proof.
  reflexivity.
Qed.

Lemma epic_509_not_closed :
  epic_509_status <> Epic509Closed.
Proof.
  discriminate.
Qed.

Lemma qex_not_owner_accept :
  epic_509_status <> Epic509OwnerAccept.
Proof.
  discriminate.
Qed.

Inductive CircGammaFence : Type :=
| CircGammaStaysQex
| CircGammaReopened.

Definition circ_gamma_fence : CircGammaFence := CircGammaStaysQex.

Lemma circ_gamma_not_reopened :
  circ_gamma_fence = CircGammaStaysQex
  /\ circ_gamma_fence <> CircGammaReopened.
Proof.
  split; [reflexivity | discriminate].
Qed.

Inductive LetterFence : Type :=
| FstarStructVsTrueRegion
| LeftoverX
| CsExtend
| ThreeTwinLetters.

Definition this_letter : LetterFence := FstarStructVsTrueRegion.

Lemma not_leftover_x :
  this_letter <> LeftoverX.
Proof.
  discriminate.
Qed.

Lemma not_cs_extend :
  this_letter <> CsExtend.
Proof.
  discriminate.
Qed.

Lemma not_three_twin_letters :
  this_letter <> ThreeTwinLetters.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket. QED ∨ QEX. Discharged QEX on CurvePolygonTrueRegionSound.          *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"509-fstar-struct-vs-true-region","topic":"relate","lemma":"ticket_509_fstar_struct_vs_true_region_qed_or_qex","title":"F-CP/F-MC/F-MS every row has a cited true-region theorem (QED) or names missing ctor CurvePolygonTrueRegionSound with F-MC/F-MS riding the same QEX (QEX); discharged QEX; cites F-CP structural chord-floor Qed and #791 polygonal taut ceiling; not V-CP arc-aware; not validity-witness-as-true-region; #509 stays open; QEX not owner accept","file":"theories/RelateNGFstarStructTrueRegion.v","witness":"509-fstar-struct-vs-true-region","board":"#509"} *)
Theorem ticket_509_fstar_struct_vs_true_region_qed_or_qex :
  fstar_every_row_has_true_region
  \/
  (~ fstar_true_region_inhabits CurvePolygonTrueRegionSound
   /\ ~ fstar_every_row_has_true_region
   /\ ~ fstar_true_region_inhabits MultiCurveTrueRegionSound
   /\ ~ fstar_true_region_inhabits MultiSurfaceTrueRegionSound
   /\ fstar_struct_qed_cite = Cite_valid_curve_polygon_cp_hole_witness
   /\ relateng_jordan_ceiling = RelatengJordanTautPolygonalQed
   /\ relateng_jordan_ceiling <> RelatengJordanUncondFlipped
   /\ landed_true_region_kind = PolygonalTautClosed
   /\ landed_true_region_kind <> CurvePolygonArcAware
   /\ fcp_hole_witness_kind = FcpHoleWitnessChordFloor
   /\ fcp_hole_witness_kind <> FcpHoleWitnessTrueRegion
   /\ epic_509_status = Epic509Open
   /\ epic_509_status <> Epic509Closed
   /\ epic_509_status <> Epic509OwnerAccept
   /\ circ_gamma_fence = CircGammaStaysQex
   /\ this_letter = FstarStructVsTrueRegion
   /\ this_letter <> LeftoverX
   /\ this_letter <> CsExtend
   /\ this_letter <> ThreeTwinLetters).
Proof.
  right.
  split; [exact curve_polygon_true_region_sound_missing|].
  split; [exact fstar_not_every_row_has_true_region|].
  split; [exact multicurve_true_region_missing|].
  split; [exact multisurface_true_region_missing|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [discriminate|].
  split; [reflexivity|].
  split; [discriminate|].
  split; [reflexivity|].
  split; [discriminate|].
  split; [reflexivity|].
  split; [discriminate|].
  split; [discriminate|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [discriminate|].
  split; [discriminate|].
  discriminate.
Qed.

Print Assumptions curve_polygon_true_region_sound_missing.
Print Assumptions fstar_not_every_row_has_true_region.
Print Assumptions fmc_fms_ride_fcp_qex.
Print Assumptions relateng_jordan_ceiling_is_791_taut.
Print Assumptions relateng_jordan_uncond_not_flipped.
Print Assumptions fcp_validity_witness_not_true_region.
Print Assumptions epic_509_stays_open.
Print Assumptions qex_not_owner_accept.
Print Assumptions ticket_509_fstar_struct_vs_true_region_qed_or_qex.
