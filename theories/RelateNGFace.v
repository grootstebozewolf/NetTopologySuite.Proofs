(* ============================================================================
   NetTopologySuite.Proofs.RelateNGFace
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: RelateNG product face
   (claimId 0007-relateng-face).

   Product face: RelateNG = DE-9IM matrix algebra + witnesses on the
   chord lane. This module packages Accepted #67 / RelateNG facts as
   the API face — not a remint of the RelateNG* / RelateNoding* zoo,
   not NodingNG, not OverlayNG.

   RelateNG is:
     - DE-9IM matrix algebra + witnesses
     - honesty decline (relate_unsupported_no_predicate)
     - line×line noding spine through the 67-c exterior-row pin
     - triangle touch / JCT cell-dim where already Qed
     - prepared-cache refinement where Qed
   It consumes NodingNG: the noding spine assumes sheet cook /
   noded edges (NodingNG.v / NodedOnSheet). Do not remint cook here.

   RelateNG is not: OverlayNG snap. Not Shewchuk A–D / Hobby / Priest.
   Not full unconditional Jordan for every curve ring. Not #522 leftover
   remint / T-junction wire complete / geom_de9im_pointset nine-cell.
   Not SQL/MM cathedral / Multi Landed. Not DCEL / Geometry subclass.

   QED: named inhabitant packaging the matrix/witness surface, the
   honesty decline, the locked 67-c parallel-unit exterior-row pin
   (same chords as NodingNG's Empty no-mint pair), and the prepared
   cache short-circuit. Triangle shared-edge touch stays the cited
   sibling pin.

   QEX: completeness false / T-junction unsupported; full Jordan
   true-region; S15l+ multi-geom leftovers; ticket 523 ISO `?`
   (cell_none_iff_empty is the Coq emptiness side — cite, do not
   fake 523 closed).

   Parks Γ / ι / ρ (named QEX, landed). This letter cites NodingNG;
   it does not remint CircGamma, ι, leftover_width, or LoopDischarged.
   First cook stays chord–chord. Host CircGamma stays QEX. No H⊥ /
   Multi Landed / Phase B done-when / SQL/MM cathedral / MerkatorBV /
   522-n.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. QEX is not a new Accept cycle.

   Testable relate results sit on the accepted Oracle line protocol
   (ADR-0006). This module mints no keyword and no second external
   seam.

   WITNESS topic: relate · claimId: 0007-relateng-face
   witness: 0007-relateng-face
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import
  DE9IM
  SheetHenCook
  NodingNG
  RelateNG
  RelateNodingLineLineExtPinned
  RelatePrepared
  RelateCurveMatrix
  RelateCurveAlphabet.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Product face: RelateNG packages DE-9IM + honesty + one locked pin.         *)
(* Consumes NodingNG / NodedOnSheet; does not cook.                           *)
(* -------------------------------------------------------------------------- *)

(* The 67-c locked fixture is the same two chords NodingNG Empty-noded. *)
Lemma relateng_67c_same_chords_as_nodingng_disjoint :
  ck_egg (nng_c1 nodingng_disjoint_pair) = MkChord hor_bot /\
  ck_egg (nng_c2 nodingng_disjoint_pair) = MkChord hor_top /\
  ce_p0 hor_bot = ext_pin_A /\
  ce_p1 hor_bot = ext_pin_B /\
  ce_p0 hor_top = ext_pin_C /\
  ce_p1 hor_top = ext_pin_D.
Proof.
  repeat split; reflexivity.
Qed.

Lemma relateng_consumes_nodingng :
  nodingng_kind = NNG_I_plus_cook /\
  nodingng_empty_no_mint nodingng_disjoint_pair /\
  noded_sheet nodingng_disjoint_noded = default_sheet /\
  nodingng_kind <> NNG_RelateNG.
Proof.
  split; [exact nodingng_is_I_plus_cook|].
  split; [exact nodingng_disjoint_empty_no_mint|].
  split; [reflexivity|].
  exact nodingng_not_relateng.
Qed.

(* Matrix / witness surface reused from DE9IM. *)
Lemma relateng_matrix_witness_surface :
  (forall r : RelatePredicate, ~ predicate_holds r im_unsupported) /\
  (forall m : IntersectionMatrix,
     im_contains m <-> im_within (matrix_transpose m)).
Proof.
  split; [exact im_unsupported_no_predicate|].
  exact im_contains_transpose_within.
Qed.

(* Honesty decline: empty/empty (and any off-dispatch pair) supports no
   predicate. Not a disjoint fill. *)
Lemma relateng_honesty_decline :
  (forall r : RelatePredicate, ~ predicate_holds r (relate [] [])) /\
  ~ matrix_ok (relate [] []) /\
  ~ im_disjoint (relate [] []).
Proof.
  split; [exact relate_unsupported_no_predicate|].
  split; [exact relate_unsupported_not_ok|].
  exact relate_unsupported_not_disjoint.
Qed.

(* Locked line×line pin: 67-c exterior-row true-dim on parallel units. *)
Lemma relateng_locked_line_line_pin :
  line_cell_ok_pinned_ext (Some 1%nat) LSInt LSExt
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
  line_cell_ok_pinned_ext (Some 1%nat) LSExt LSInt
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
  line_cell_ok_pinned_ext (Some 0%nat) LSBnd LSExt
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
  line_cell_ok_pinned_ext (Some 0%nat) LSExt LSBnd
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
  line_cell_ok_pinned_ext (Some 2%nat) LSExt LSExt
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D.
Proof.
  exact parallel_unit_segments_exterior_row_pinned.
Qed.

(* Triangle shared-edge touch — already-Qed sibling pin, not reminted. *)
Lemma relateng_locked_triangle_touch :
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  exact classified_touch_pair.
Qed.

(* Prepared-cache refinement where Qed (#574 / 522-e). *)
Lemma relateng_prepared_cache :
  let A := triangle_geometry 0 0 1 0 0 1 in
  let B := triangle_geometry 2 0 3 0 2 1 in
  let pg := prepare A in
  pg_tri_cache pg = Some (0, 0, 1, 0, 0, 1) /\
  pg_cache pg = None /\
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint /\
  evaluate pg B = aa_matrix_disjoint /\
  relate A B = aa_matrix_disjoint.
Proof.
  exact prepared_evaluate_cache_short_circuit.
Qed.

(* Coq emptiness stays None. Ticket 523 ISO `?` stays a named QEX. *)
Lemma relateng_cell_none_iff_empty :
  forall d sX sY A B,
    RelateCurveMatrix.cell_ok d sX sY A B ->
    (d = None <->
     ~ exists p, RelateCurveMatrix.in_stratum sX A p /\
                 RelateCurveMatrix.in_stratum sY B p).
Proof.
  exact RelateCurveMatrix.cell_none_iff_empty.
Qed.

(* -------------------------------------------------------------------------- *)
(* What RelateNG is / is not. Kind tag, not a second kernel.                  *)
(* -------------------------------------------------------------------------- *)

Inductive RelateNGKind : Type :=
| RNG_DE9IM_Face
| RNG_NodingNG
| RNG_OverlayNGSnap
| RNG_Shewchuk
| RNG_Hobby
| RNG_Priest
| RNG_JordanUncond
| RNG_SQLMMCathedral
| RNG_DCEL
| RNG_GeomSubclass
| RNG_Leftover522n.

Definition relateng_kind : RelateNGKind := RNG_DE9IM_Face.

Lemma relateng_is_de9im_face : relateng_kind = RNG_DE9IM_Face.
Proof.
  reflexivity.
Qed.

Lemma relateng_not_nodingng : relateng_kind <> RNG_NodingNG.
Proof.
  discriminate.
Qed.

Lemma relateng_not_overlayng : relateng_kind <> RNG_OverlayNGSnap.
Proof.
  discriminate.
Qed.

Lemma relateng_not_shewchuk : relateng_kind <> RNG_Shewchuk.
Proof.
  discriminate.
Qed.

Lemma relateng_not_hobby : relateng_kind <> RNG_Hobby.
Proof.
  discriminate.
Qed.

Lemma relateng_not_priest : relateng_kind <> RNG_Priest.
Proof.
  discriminate.
Qed.

Lemma relateng_not_jordan_uncond : relateng_kind <> RNG_JordanUncond.
Proof.
  discriminate.
Qed.

Lemma relateng_not_sqlmm_cathedral : relateng_kind <> RNG_SQLMMCathedral.
Proof.
  discriminate.
Qed.

Lemma relateng_not_dcel : relateng_kind <> RNG_DCEL.
Proof.
  discriminate.
Qed.

Lemma relateng_not_geom_subclass : relateng_kind <> RNG_GeomSubclass.
Proof.
  discriminate.
Qed.

Lemma relateng_not_522n : relateng_kind <> RNG_Leftover522n.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named QEX parks. Missing constructors, not bools. Do not fake Discharge.   *)
(* -------------------------------------------------------------------------- *)

Inductive RelateNGParkCtor : Type :=
| RelateNGCompleteClassifier
| RelateNGTjunctionTouchesFill
| RelateNGJordanTrueRegion
| RelateNGMultiGeomComplete
| RelateNGIsoQuestionMark.

Definition relateng_park_inhabits (c : RelateNGParkCtor) : Prop :=
  match c with
  | RelateNGCompleteClassifier => False
  | RelateNGTjunctionTouchesFill => False
  | RelateNGJordanTrueRegion => False
  | RelateNGMultiGeomComplete => False
  | RelateNGIsoQuestionMark => False
  end.

Lemma relateng_complete_missing :
  ~ relateng_park_inhabits RelateNGCompleteClassifier.
Proof.
  intro H. exact H.
Qed.

Lemma relateng_tjunction_touches_missing :
  ~ relateng_park_inhabits RelateNGTjunctionTouchesFill.
Proof.
  intro H. exact H.
Qed.

Lemma relateng_jordan_true_region_missing :
  ~ relateng_park_inhabits RelateNGJordanTrueRegion.
Proof.
  intro H. exact H.
Qed.

Lemma relateng_multi_geom_missing :
  ~ relateng_park_inhabits RelateNGMultiGeomComplete.
Proof.
  intro H. exact H.
Qed.

Lemma relateng_iso_question_missing :
  ~ relateng_park_inhabits RelateNGIsoQuestionMark.
Proof.
  intro H. exact H.
Qed.

Inductive RelateNGLetterStatus : Type :=
| RelateNGFaceLanded
| RelateNGCompleteDischarged
| RelateNGJordanDischarged.

Definition relateng_letter_status : RelateNGLetterStatus :=
  RelateNGFaceLanded.

Lemma relateng_letter_is_landed :
  relateng_letter_status = RelateNGFaceLanded /\
  relateng_letter_status <> RelateNGCompleteDischarged /\
  relateng_letter_status <> RelateNGJordanDischarged /\
  ~ relateng_park_inhabits RelateNGCompleteClassifier /\
  ~ relateng_park_inhabits RelateNGJordanTrueRegion.
Proof.
  split; [reflexivity|].
  split; [discriminate|].
  split; [discriminate|].
  split; [exact relateng_complete_missing|].
  exact relateng_jordan_true_region_missing.
Qed.

(* Named QED package: matrix/witness + honesty + 67-c pin + NodingNG. *)
Lemma relateng_face_inhabits :
  (forall r : RelatePredicate, ~ predicate_holds r im_unsupported) /\
  (forall r : RelatePredicate, ~ predicate_holds r (relate [] [])) /\
  line_cell_ok_pinned_ext (Some 1%nat) LSInt LSExt
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
  line_cell_ok_pinned_ext (Some 2%nat) LSExt LSExt
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
  ck_egg (nng_c1 nodingng_disjoint_pair) = MkChord hor_bot /\
  ce_p0 hor_bot = ext_pin_A /\
  nodingng_empty_no_mint nodingng_disjoint_pair /\
  noded_sheet nodingng_disjoint_noded = default_sheet /\
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge /\
  relateng_kind = RNG_DE9IM_Face /\
  relateng_kind <> RNG_NodingNG /\
  relateng_kind <> RNG_OverlayNGSnap /\
  relateng_kind <> RNG_Shewchuk /\
  relateng_kind <> RNG_DCEL.
Proof.
  split; [exact im_unsupported_no_predicate|].
  split; [exact relate_unsupported_no_predicate|].
  destruct parallel_unit_segments_exterior_row_pinned
    as [Hie [Hei [Hbe [Heb Hee]]]].
  split; [exact Hie|].
  split; [exact Hee|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact nodingng_disjoint_empty_no_mint|].
  split; [reflexivity|].
  split; [exact classified_touch_pair|].
  split; [exact relateng_is_de9im_face|].
  split; [exact relateng_not_nodingng|].
  split; [exact relateng_not_overlayng|].
  split; [exact relateng_not_shewchuk|].
  exact relateng_not_dcel.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-relateng-face","topic":"relate","lemma":"ticket_0007_relateng_face_qed_or_qex","title":"RelateNG face packages DE-9IM matrix/witness, honesty decline, and the 67-c line-line exterior-row pin on NodingNG-noded chords (QED) or the honesty decline supports a predicate (QEX); discharged QED; not NodingNG / OverlayNG snap / Shewchuk / DCEL","file":"theories/RelateNGFace.v","witness":"0007-relateng-face","board":"ADR-0007"} *)
Theorem ticket_0007_relateng_face_qed_or_qex :
  ((forall r : RelatePredicate, ~ predicate_holds r im_unsupported) /\
   (forall r : RelatePredicate, ~ predicate_holds r (relate [] [])) /\
   line_cell_ok_pinned_ext (Some 1%nat) LSInt LSExt
     ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
   line_cell_ok_pinned_ext (Some 2%nat) LSExt LSExt
     ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
   ck_egg (nng_c1 nodingng_disjoint_pair) = MkChord hor_bot /\
   ce_p0 hor_bot = ext_pin_A /\
   nodingng_empty_no_mint nodingng_disjoint_pair /\
   noded_sheet nodingng_disjoint_noded = default_sheet /\
   triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge /\
   relateng_kind = RNG_DE9IM_Face /\
   relateng_kind <> RNG_NodingNG /\
   relateng_kind <> RNG_OverlayNGSnap /\
   relateng_kind <> RNG_Shewchuk /\
   relateng_kind <> RNG_DCEL)
  \/
  exists r : RelatePredicate, predicate_holds r (relate [] []).
Proof.
  left.
  exact relateng_face_inhabits.
Qed.

(* Completeness is false; T-junction fill stays unsupported. Do not
   remint leftover I to a Touches fill. Do not mint 522-n. *)
(* WITNESS {"claimId":"0007-relateng-face","topic":"relate","lemma":"ticket_0007_relateng_complete_qed_or_qex","title":"RelateNG face discharges CCW classifier completeness and T-junction Touches fill (QED) or parks completeness-false and T-junction unsupported (QEX); discharged QEX; unnamed CCW pair declines; leftover I fill is im_unsupported","file":"theories/RelateNGFace.v","witness":"0007-relateng-face","board":"ADR-0007"} *)
Theorem ticket_0007_relateng_complete_qed_or_qex :
  (relateng_letter_status = RelateNGCompleteDischarged /\
   relateng_park_inhabits RelateNGCompleteClassifier /\
   relateng_park_inhabits RelateNGTjunctionTouchesFill)
  \/
  (relateng_letter_status = RelateNGFaceLanded /\
   ~ relateng_park_inhabits RelateNGCompleteClassifier /\
   ~ relateng_park_inhabits RelateNGTjunctionTouchesFill /\
   (exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
      0 < gdbl ax ay bx by_ cx cy /\
      0 < gdbl dx dy ex ey fx fy /\
      triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
        = TPR_Unsupported) /\
   (forall r : RelatePredicate,
      ~ predicate_holds r (relate (triangle_geometry 0 0 2 0 0 1)
                                  (triangle_geometry 1 0 3 0 2 1))) /\
   relateng_kind <> RNG_Leftover522n).
Proof.
  right.
  split; [reflexivity|].
  split; [exact relateng_complete_missing|].
  split; [exact relateng_tjunction_touches_missing|].
  split; [exact triangle_pair_regime_ccw_incomplete|].
  split; [exact relate_tjunction_pair_no_predicate|].
  exact relateng_not_522n.
Qed.

(* Full Jordan true-region, S15l+ multi-geom, and ticket 523 ISO `?`.
   cell_none_iff_empty is Qed (emptiness is None); do not fake 523 closed. *)
(* WITNESS {"claimId":"0007-relateng-face","topic":"relate","lemma":"ticket_0007_relateng_parks_qed_or_qex","title":"RelateNG face discharges full Jordan true-region, multi-geom completeness, and ISO result-alphabet (QED) or parks them as named missing constructors (QEX); discharged QEX; cell_none_iff_empty stays Coq emptiness; ticket 523 ? is not ISO","file":"theories/RelateNGFace.v","witness":"0007-relateng-face","board":"ADR-0007"} *)
Theorem ticket_0007_relateng_parks_qed_or_qex :
  (relateng_letter_status = RelateNGJordanDischarged /\
   relateng_park_inhabits RelateNGJordanTrueRegion /\
   relateng_park_inhabits RelateNGMultiGeomComplete /\
   (forall c : CurveRelateResult, iso_result_cell c))
  \/
  (relateng_letter_status = RelateNGFaceLanded /\
   ~ relateng_park_inhabits RelateNGJordanTrueRegion /\
   ~ relateng_park_inhabits RelateNGMultiGeomComplete /\
   ~ relateng_park_inhabits RelateNGIsoQuestionMark /\
   ~ iso_result_cell CRR_Unknown /\
   (forall d, dim_to_result d <> Some CRR_Unknown) /\
   relateng_kind = RNG_DE9IM_Face /\
   relateng_kind <> RNG_JordanUncond /\
   relateng_kind <> RNG_SQLMMCathedral).
Proof.
  right.
  split; [reflexivity|].
  split; [exact relateng_jordan_true_region_missing|].
  split; [exact relateng_multi_geom_missing|].
  split; [exact relateng_iso_question_missing|].
  split; [exact question_mark_not_iso_result|].
  split; [exact dim_to_result_never_unknown|].
  split; [exact relateng_is_de9im_face|].
  split; [exact relateng_not_jordan_uncond|].
  exact relateng_not_sqlmm_cathedral.
Qed.

Print Assumptions relateng_matrix_witness_surface.
Print Assumptions relateng_honesty_decline.
Print Assumptions relateng_locked_line_line_pin.
Print Assumptions relateng_consumes_nodingng.
Print Assumptions relateng_67c_same_chords_as_nodingng_disjoint.
Print Assumptions relateng_locked_triangle_touch.
Print Assumptions relateng_prepared_cache.
Print Assumptions relateng_cell_none_iff_empty.
Print Assumptions relateng_face_inhabits.
Print Assumptions ticket_0007_relateng_face_qed_or_qex.
Print Assumptions ticket_0007_relateng_complete_qed_or_qex.
Print Assumptions ticket_0007_relateng_parks_qed_or_qex.
