(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixAreaLine
   ----------------------------------------------------------------------------
   Issue #67 session 9 (S9): area×line regime→witness — rectangle + segment.

   Regime-indexed `area_line_fill` that SELECTS (does not compute from
   geometry) one of the S5 witness matrices from `RelateAreaLine.v` per
   `AreaLineRegime`.

   Delivers:

     - `AreaLineRegime` + `area_line_fill` (regime → witness matrix)
     - `classify_area_line` recording which S5 geometry guard names each regime
     - Fill = witness equalities
     - `*_fill_witness`: the selected witness satisfies the regime's predicate
       (constant facts; the regime hypothesis is NOT consumed)
     - Mutual-exclusion lemmas (genuine geometry, via coordinate projections +
       `lra`) for disjoint vs interior / pierce / touch

   Honest scoping: axis-aligned rectangle, no holes; oracle `RELATE_MATRIX`
   driver mode is vocabulary-seeded only (`oracle/relate_matrix_fill_vocabulary.txt`).
   Arc/clothoid carriers and full RelateNG noding are S10+.  Proving a witness
   is a configuration's true DE-9IM is the deferred RelateNG step.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance RelateAreaLine.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Regime enum + matrix fill.                                                 *)
(* -------------------------------------------------------------------------- *)

Inductive AreaLineRegime : Type :=
| ALR_Interior
| ALR_Pierce
| ALR_Disjoint
| ALR_BoundaryTouch.

Definition area_line_fill (r : AreaLineRegime) : IntersectionMatrix :=
  match r with
  | ALR_Interior      => al_matrix_segment_interior
  | ALR_Pierce        => al_matrix_segment_crosses
  | ALR_Disjoint      => al_matrix_disjoint
  | ALR_BoundaryTouch => al_matrix_boundary_touch
  end.

Lemma area_line_fill_interior_eq :
  area_line_fill ALR_Interior = al_matrix_segment_interior.
Proof. reflexivity. Qed.

Lemma area_line_fill_pierce_eq :
  area_line_fill ALR_Pierce = al_matrix_segment_crosses.
Proof. reflexivity. Qed.

Lemma area_line_fill_disjoint_eq :
  area_line_fill ALR_Disjoint = al_matrix_disjoint.
Proof. reflexivity. Qed.

Lemma area_line_fill_boundary_touch_eq :
  area_line_fill ALR_BoundaryTouch = al_matrix_boundary_touch.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Classifier — mirrors S5 guards.                                            *)
(* -------------------------------------------------------------------------- *)

Definition classify_area_line (x0 y0 x1 y1 : R) (A B : Point)
    (r : AreaLineRegime) : Prop :=
  match r with
  | ALR_Interior      => segment_strictly_inside_open_rect x0 y0 x1 y1 A B
  | ALR_Pierce        => segment_pierces_rect_horiz x0 y0 x1 y1 A B
  | ALR_Disjoint      => segment_above_rect x0 y0 x1 y1 A B
  | ALR_BoundaryTouch => segment_left_boundary_endpoint_outside x0 y0 x1 y1 A B
  end.

Lemma interior_py_lt_y1 :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_strictly_inside_open_rect x0 y0 x1 y1 A B ->
    py A < y1 /\ py B < y1.
Proof.
  intros x0 y0 x1 y1 A B H.
  unfold segment_strictly_inside_open_rect in H.
  tauto.
Qed.

Lemma pierce_py_in_open_band :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_pierces_rect_horiz x0 y0 x1 y1 A B ->
    y0 < py A /\ py A < y1.
Proof.
  intros x0 y0 x1 y1 A B H.
  unfold segment_pierces_rect_horiz in H.
  tauto.
Qed.

Lemma touch_py_in_open_band :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_left_boundary_endpoint_outside x0 y0 x1 y1 A B ->
    y0 < py A /\ py A < y1.
Proof.
  intros x0 y0 x1 y1 A B H.
  unfold segment_left_boundary_endpoint_outside in H.
  tauto.
Qed.

Lemma interior_px_gt_x0 :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_strictly_inside_open_rect x0 y0 x1 y1 A B ->
    x0 < px A.
Proof.
  intros x0 y0 x1 y1 A B H.
  unfold segment_strictly_inside_open_rect in H.
  tauto.
Qed.

Lemma pierce_pxA_lt_x0 :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_pierces_rect_horiz x0 y0 x1 y1 A B ->
    px A < x0.
Proof.
  intros x0 y0 x1 y1 A B H.
  unfold segment_pierces_rect_horiz in H.
  tauto.
Qed.

Lemma touch_pxA_eq_x0 :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_left_boundary_endpoint_outside x0 y0 x1 y1 A B ->
    px A = x0.
Proof.
  intros x0 y0 x1 y1 A B H.
  unfold segment_left_boundary_endpoint_outside in H.
  tauto.
Qed.

Lemma pierce_pxB_gt_x1 :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_pierces_rect_horiz x0 y0 x1 y1 A B ->
    px B > x1.
Proof.
  intros x0 y0 x1 y1 A B H.
  unfold segment_pierces_rect_horiz in H.
  tauto.
Qed.

Lemma touch_pxB_lt_x0 :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_left_boundary_endpoint_outside x0 y0 x1 y1 A B ->
    px B < x0.
Proof.
  intros x0 y0 x1 y1 A B H.
  unfold segment_left_boundary_endpoint_outside in H.
  tauto.
Qed.

Lemma interior_not_disjoint :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_strictly_inside_open_rect x0 y0 x1 y1 A B ->
    ~ segment_above_rect x0 y0 x1 y1 A B.
Proof.
  intros x0 y0 x1 y1 A B Hinside Habove.
  pose proof (interior_py_lt_y1 x0 y0 x1 y1 A B Hinside) as [Halt _].
  unfold segment_above_rect in Habove.
  destruct Habove as [_ [Hagt _]].
  lra.
Qed.

Lemma pierce_not_disjoint :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_pierces_rect_horiz x0 y0 x1 y1 A B ->
    ~ segment_above_rect x0 y0 x1 y1 A B.
Proof.
  intros x0 y0 x1 y1 A B Hpierce Habove.
  pose proof (pierce_py_in_open_band x0 y0 x1 y1 A B Hpierce) as [Hlo Hhi].
  unfold segment_above_rect in Habove.
  destruct Habove as [_ [Hagt _]].
  lra.
Qed.

Lemma touch_not_disjoint :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_left_boundary_endpoint_outside x0 y0 x1 y1 A B ->
    ~ segment_above_rect x0 y0 x1 y1 A B.
Proof.
  intros x0 y0 x1 y1 A B Htouch Habove.
  pose proof (touch_py_in_open_band x0 y0 x1 y1 A B Htouch) as [Hlo Hhi].
  unfold segment_above_rect in Habove.
  destruct Habove as [_ [Hagt _]].
  lra.
Qed.

Lemma interior_not_pierce :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_strictly_inside_open_rect x0 y0 x1 y1 A B ->
    ~ segment_pierces_rect_horiz x0 y0 x1 y1 A B.
Proof.
  intros x0 y0 x1 y1 A B Hinside Hpierce.
  pose proof (interior_px_gt_x0 x0 y0 x1 y1 A B Hinside) as Hgt.
  pose proof (pierce_pxA_lt_x0 x0 y0 x1 y1 A B Hpierce) as Hlt.
  lra.
Qed.

Lemma interior_not_touch :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_strictly_inside_open_rect x0 y0 x1 y1 A B ->
    ~ segment_left_boundary_endpoint_outside x0 y0 x1 y1 A B.
Proof.
  intros x0 y0 x1 y1 A B Hinside Htouch.
  pose proof (interior_px_gt_x0 x0 y0 x1 y1 A B Hinside) as Hgt.
  pose proof (touch_pxA_eq_x0 x0 y0 x1 y1 A B Htouch) as Heq.
  rewrite Heq in Hgt. lra.
Qed.

Lemma pierce_not_interior :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_pierces_rect_horiz x0 y0 x1 y1 A B ->
    ~ segment_strictly_inside_open_rect x0 y0 x1 y1 A B.
Proof.
  intros x0 y0 x1 y1 A B Hpierce Hinside.
  exact (interior_not_pierce x0 y0 x1 y1 A B Hinside Hpierce).
Qed.

Lemma pierce_not_touch :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    x0 < x1 ->
    segment_pierces_rect_horiz x0 y0 x1 y1 A B ->
    ~ segment_left_boundary_endpoint_outside x0 y0 x1 y1 A B.
Proof.
  intros x0 y0 x1 y1 A B Hx01 Hpierce Htouch.
  pose proof (pierce_pxB_gt_x1 x0 y0 x1 y1 A B Hpierce) as Hbgt.
  pose proof (touch_pxB_lt_x0 x0 y0 x1 y1 A B Htouch) as Hblt.
  lra.
Qed.

Lemma touch_not_pierce :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_left_boundary_endpoint_outside x0 y0 x1 y1 A B ->
    ~ segment_pierces_rect_horiz x0 y0 x1 y1 A B.
Proof.
  intros x0 y0 x1 y1 A B Htouch Hpierce.
  pose proof (touch_pxA_eq_x0 x0 y0 x1 y1 A B Htouch) as Heq.
  pose proof (pierce_pxA_lt_x0 x0 y0 x1 y1 A B Hpierce) as Hlt.
  rewrite Heq in Hlt. lra.
Qed.

Lemma touch_not_interior :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_left_boundary_endpoint_outside x0 y0 x1 y1 A B ->
    ~ segment_strictly_inside_open_rect x0 y0 x1 y1 A B.
Proof.
  intros x0 y0 x1 y1 A B Htouch Hinside.
  exact (interior_not_touch x0 y0 x1 y1 A B Hinside Htouch).
Qed.

(* -------------------------------------------------------------------------- *)
(* Witness facts: the selected witness satisfies the regime's predicate.      *)
(*                                                                            *)
(* Constant facts about `area_line_fill`; no geometry hypothesis, no          *)
(* geometry→matrix claim.  The genuine geometry lives in the mutual-exclusion  *)
(* / projection lemmas above and in `RelateAreaLine.segment_pierces_rect_      *)
(* share`.                                                                     *)
(* -------------------------------------------------------------------------- *)

Theorem area_line_fill_interior_witness :
  im_intersects (area_line_fill ALR_Interior).
Proof.
  rewrite area_line_fill_interior_eq. exact al_matrix_segment_interior_intersects.
Qed.

Theorem area_line_fill_pierce_witness :
  im_crosses (area_line_fill ALR_Pierce) /\
  im_intersects (area_line_fill ALR_Pierce).
Proof.
  rewrite area_line_fill_pierce_eq.
  split; [exact al_matrix_segment_crosses_witness | exact al_matrix_segment_crosses_intersects].
Qed.

Theorem area_line_fill_disjoint_witness :
  im_disjoint (area_line_fill ALR_Disjoint).
Proof.
  rewrite area_line_fill_disjoint_eq. exact al_matrix_disjoint_witness.
Qed.

Theorem area_line_fill_boundary_touch_witness :
  im_touches (area_line_fill ALR_BoundaryTouch).
Proof.
  rewrite area_line_fill_boundary_touch_eq. exact al_matrix_boundary_touch_witness.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions area_line_fill_interior_witness.
Print Assumptions area_line_fill_pierce_witness.
Print Assumptions area_line_fill_disjoint_witness.
Print Assumptions area_line_fill_boundary_touch_witness.