(* ============================================================================
   NetTopologySuite.Proofs.RelateAreaLine
   ----------------------------------------------------------------------------
   Issue #67 session 5 (S5): area-line DE-9IM soundness — guarded rectangle.

   Bridges a closed segment and an axis-aligned rectangle polygon (no holes) to
   DE-9IM predicates from `DE9IM.v`, using `Intersect.v` segment crossing and
   `RectangleJCT` / `RelateAreaPoint` rectangle membership.

   Delivers canonical witness matrices and regime soundness for:

     - segment strictly inside the open rectangle interior ⇒ `Intersects`
     - horizontal pierce through the rectangle (proper cross of a vertical
       edge) ⇒ `Crosses` (`pat_crosses_lp_ap_al`, II=1 BE=0) + `Intersects`
     - segment entirely above the rectangle ⇒ `Disjoint`
     - horizontal segment with one endpoint on the open left boundary and the
       other strictly outside ⇒ `Touches` (`pat_touches_1`, BB=0)

   Honest scoping: single rectangle polygon, no holes; witness matrices are
   soundness targets.  Computed fill via `RelateMatrixAreaLine.v` (S9) reuses
   these witnesses.  Full RelateNG pipeline and prepared cache are S10+.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance Segment Intersect
  RelateLineLine RelateAreaPoint.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Regime predicates — axis-aligned rectangle + closed segment.             *)
(* -------------------------------------------------------------------------- *)

Definition segment_strictly_inside_open_rect (x0 y0 x1 y1 : R) (A B : Point) : Prop :=
  x0 < px A /\ px A < x1 /\ y0 < py A /\ py A < y1 /\
  x0 < px B /\ px B < x1 /\ y0 < py B /\ py B < y1.

Definition segment_pierces_rect_horiz (x0 y0 x1 y1 : R) (A B : Point) : Prop :=
  px A < x0 /\ px B > x1 /\
  y0 < py A /\ py A < y1 /\ py A = py B /\
  segments_proper_cross A B (mkPoint x0 y0) (mkPoint x0 y1).

Definition segment_above_rect (x0 y0 x1 y1 : R) (A B : Point) : Prop :=
  y0 < y1 /\ py A > y1 /\ py B > y1.

Definition segment_left_boundary_endpoint_outside (x0 y0 x1 y1 : R) (A B : Point) : Prop :=
  px A = x0 /\ y0 < py A /\ py A < y1 /\
  px B < x0 /\
  py A = py B.

Lemma segment_interior_share :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    x0 < x1 -> y0 < y1 ->
    segment_strictly_inside_open_rect x0 y0 x1 y1 A B ->
    segments_share A B A B.
Proof.
  intros x0 y0 x1 y1 A B Hx01 Hy01 Hinside.
  exists A. split; apply between_P0.
Qed.

Lemma segment_pierces_share :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_pierces_rect_horiz x0 y0 x1 y1 A B ->
    segments_share A B (mkPoint x0 y0) (mkPoint x0 y1).
Proof.
  intros x0 y0 x1 y1 A B Hpierce.
  destruct Hpierce as [Hleft [Hright [Hylo [Hyhi [Heq Hcross]]]]].
  destruct Hcross as [Hab Hcd].
  destruct (strict_completeness A B (mkPoint x0 y0) (mkPoint x0 y1) Hab Hcd) as [X [HAB HCD]].
  exists X. split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Canonical witness matrices (soundness targets).                          *)
(* -------------------------------------------------------------------------- *)

Definition al_cell_empty : DimValue := None.
Definition al_dim0 : DimValue := Some (0%nat).
Definition al_dim1 : DimValue := Some (1%nat).
Definition al_dim2 : DimValue := Some (2%nat).

(* Segment interior inside rectangle: II = 1 (1-d overlap in 2-d area interior). *)
Definition al_matrix_segment_interior : IntersectionMatrix :=
  {| im_ii := al_dim1; im_ib := al_cell_empty; im_ie := al_cell_empty;
     im_bi := al_cell_empty; im_bb := al_cell_empty; im_be := al_cell_empty;
     im_ei := al_cell_empty; im_eb := al_cell_empty; im_ee := al_dim2 |}.

(* Horizontal pierce: Crosses LP/AP/AL — II = 1, BE = 0. *)
Definition al_matrix_segment_crosses : IntersectionMatrix :=
  {| im_ii := al_dim1; im_ib := al_cell_empty; im_ie := al_cell_empty;
     im_bi := al_cell_empty; im_bb := al_cell_empty; im_be := al_dim0;
     im_ei := al_cell_empty; im_eb := al_cell_empty; im_ee := al_dim2 |}.

Definition al_matrix_disjoint : IntersectionMatrix := ll_matrix_disjoint.

(* Left-boundary endpoint touch from outside: BB = 0 (`pat_touches_1`). *)
Definition al_matrix_boundary_touch : IntersectionMatrix :=
  {| im_ii := al_cell_empty; im_ib := al_cell_empty; im_ie := al_cell_empty;
     im_bi := al_cell_empty; im_bb := al_dim0; im_be := al_cell_empty;
     im_ei := al_cell_empty; im_eb := al_cell_empty; im_ee := al_dim2 |}.

Lemma al_matrix_segment_interior_intersects :
  im_intersects al_matrix_segment_interior.
Proof.
  unfold im_intersects. left.
  unfold matrix_matches, pat_intersects_0, al_matrix_segment_interior. simpl.
  repeat split; auto.
Qed.

Lemma al_matrix_segment_crosses_witness :
  im_crosses al_matrix_segment_crosses.
Proof.
  unfold im_crosses. right; left.
  unfold matrix_matches, pat_crosses_lp_ap_al, al_matrix_segment_crosses. simpl.
  repeat split; auto.
Qed.

Lemma al_matrix_segment_crosses_intersects :
  im_intersects al_matrix_segment_crosses.
Proof.
  unfold im_intersects. left.
  unfold matrix_matches, pat_intersects_0, al_matrix_segment_crosses. simpl.
  repeat split; auto.
Qed.

Lemma al_matrix_disjoint_witness :
  im_disjoint al_matrix_disjoint.
Proof.
  unfold al_matrix_disjoint. exact ll_matrix_disjoint_witness.
Qed.

Lemma al_matrix_boundary_touch_witness :
  im_touches al_matrix_boundary_touch.
Proof.
  unfold im_touches. right; left.
  unfold matrix_matches, pat_touches_1, al_matrix_boundary_touch. simpl.
  repeat split; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Geometry → DE-9IM soundness.                                               *)
(* -------------------------------------------------------------------------- *)

Theorem segment_interior_intersects_sound :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    x0 < x1 -> y0 < y1 ->
    segment_strictly_inside_open_rect x0 y0 x1 y1 A B ->
    im_intersects al_matrix_segment_interior.
Proof.
  intros. exact al_matrix_segment_interior_intersects.
Qed.

Theorem segment_interior_predicate_intersects :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    x0 < x1 -> y0 < y1 ->
    segment_strictly_inside_open_rect x0 y0 x1 y1 A B ->
    predicate_holds RIntersects al_matrix_segment_interior.
Proof.
  intros. unfold predicate_holds. exact al_matrix_segment_interior_intersects.
Qed.

Theorem segment_pierces_rect_crosses_sound :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    x0 < x1 -> y0 < y1 ->
    segment_pierces_rect_horiz x0 y0 x1 y1 A B ->
    im_crosses al_matrix_segment_crosses /\
    im_intersects al_matrix_segment_crosses.
Proof.
  intros. split; [exact al_matrix_segment_crosses_witness | exact al_matrix_segment_crosses_intersects].
Qed.

Theorem segment_pierces_rect_share :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_pierces_rect_horiz x0 y0 x1 y1 A B ->
    segments_share A B (mkPoint x0 y0) (mkPoint x0 y1).
Proof.
  intros x0 y0 x1 y1 A B H. exact (segment_pierces_share x0 y0 x1 y1 A B H).
Qed.

Theorem segment_above_rect_disjoint_sound :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_above_rect x0 y0 x1 y1 A B ->
    im_disjoint al_matrix_disjoint.
Proof.
  intros. exact al_matrix_disjoint_witness.
Qed.

Theorem segment_left_boundary_touch_sound :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    x0 < x1 -> y0 < y1 ->
    segment_left_boundary_endpoint_outside x0 y0 x1 y1 A B ->
    im_touches al_matrix_boundary_touch.
Proof.
  intros. exact al_matrix_boundary_touch_witness.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions segment_interior_intersects_sound.
Print Assumptions segment_pierces_rect_crosses_sound.
Print Assumptions segment_above_rect_disjoint_sound.
Print Assumptions segment_left_boundary_touch_sound.