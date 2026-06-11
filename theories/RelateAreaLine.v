(* ============================================================================
   NetTopologySuite.Proofs.RelateAreaLine
   ----------------------------------------------------------------------------
   Issue #67 session 5 (S5): area-line DE-9IM witness matrices — rectangle.

   For a closed segment and an axis-aligned rectangle polygon (no holes),
   defines one hand-specified DE-9IM witness matrix per regime and proves each
   satisfies the named predicate from `DE9IM.v`:

     - segment strictly inside the open rectangle interior → `Intersects`
     - horizontal pierce through the rectangle (proper cross of a vertical
       edge) → `Crosses` (`pat_crosses_lp_ap_al`, II=1 BE=0) + `Intersects`
     - segment entirely above the rectangle → `Disjoint`
     - horizontal segment with one endpoint on the open left boundary and the
       other strictly outside → `Touches` (`pat_touches_1`, BB=0)

   The witnesses are constant facts; the regime predicates name the intended
   geometry but are not consumed.  One genuine geometric consequence is proved
   (`segment_pierces_rect_share`: a pierce shares a point with the crossed
   edge, via `Intersect.v`).  Honest scoping: single rectangle polygon, no
   holes.  Regime→witness selection via `RelateMatrixAreaLine.v` (S9); proving
   a witness is a configuration's true DE-9IM is the deferred RelateNG step.

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
(* Hand-specified witness matrices (regime targets, not derived from geometry).*)
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
(* Genuine geometry lemma: a pierce produces a shared point with an edge.     *)
(*                                                                            *)
(* The constant `al_matrix_*` lemmas above prove each hand-specified witness   *)
(* satisfies its predicate (Intersects / Crosses / Disjoint / Touches).  The   *)
(* lemma below is the genuine geometric consequence of the pierce regime: the  *)
(* segment shares a point with the crossed vertical edge.  The two layers are  *)
(* not bridged — which witness a configuration's true DE-9IM equals is the     *)
(* deferred RelateNG step.                                                     *)
(* -------------------------------------------------------------------------- *)

Theorem segment_pierces_rect_share :
  forall (x0 y0 x1 y1 : R) (A B : Point),
    segment_pierces_rect_horiz x0 y0 x1 y1 A B ->
    segments_share A B (mkPoint x0 y0) (mkPoint x0 y1).
Proof.
  intros x0 y0 x1 y1 A B H. exact (segment_pierces_share x0 y0 x1 y1 A B H).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions segment_pierces_rect_share.
Print Assumptions al_matrix_segment_interior_intersects.
Print Assumptions al_matrix_segment_crosses_witness.
Print Assumptions al_matrix_boundary_touch_witness.