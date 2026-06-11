(* ============================================================================
   NetTopologySuite.Proofs.RelateAreaPoint
   ----------------------------------------------------------------------------
   Issue #67 session 4 (S4): area-point — rectangle membership + Contains
   witness.

   Relates an axis-aligned rectangle polygon (no holes) and a query point,
   in two honest, independent layers:
     - Geometry: a strict-interior point lies in the rectangle (membership),
       via the unconditional ray-parity characterisation
       `RectangleJCT.point_in_ring_rect_iff`; a left-boundary point lies in
       the polygon but not in the strict interior.
     - Witness: the hand-specified Contains / Touches matrices satisfy the
       `im_contains` / `im_touches` predicates from `DE9IM.v`.
   It does NOT derive a DE-9IM matrix from the geometry (no `point` → matrix
   bridge); that is the deferred RelateNG matrix-fill step.

   Honest scoping: single rectangle polygon, no holes.  S4 covers strict-
   interior membership + the Contains witness; S4b (same file) the left-
   boundary membership + the Touches witness.  Area-line, area-area, RelateNG
   pipeline, and prepared cache are S5+ follow-up.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import DE9IM Distance Overlay RectangleJCT.
(* S4b boundary Touches uses DE-9IM patterns only — no RelateBoundary import
   (decoupled slice; area-point boundary witnesses are self-contained). *)
Import ListNotations.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Minimal area-point carrier: axis-aligned rectangle polygon + query point.  *)
(* -------------------------------------------------------------------------- *)

Definition rect_polygon (x0 y0 x1 y1 : R) : Polygon :=
  {| outer_ring := rect_ring x0 y0 x1 y1; hole_rings := [] |}.

Definition rect_geometry (x0 y0 x1 y1 : R) : Geometry :=
  [ rect_polygon x0 y0 x1 y1 ].

Definition point_strictly_in_open_rect (x0 y0 x1 y1 : R) (p : Point) : Prop :=
  x0 < px p < x1 /\ y0 < py p < y1.

Definition point_in_rect_polygon (x0 y0 x1 y1 : R) (p : Point) : Prop :=
  point_in_polygon p (rect_polygon x0 y0 x1 y1).

Definition point_in_rect_geometry (x0 y0 x1 y1 : R) (p : Point) : Prop :=
  point_set (rect_geometry x0 y0 x1 y1) p.

(* -------------------------------------------------------------------------- *)
(* Hand-specified witness matrix (regime target, not derived from geometry).  *)
(* -------------------------------------------------------------------------- *)

Definition ap_cell_empty : DimValue := None.
Definition ap_dim0 : DimValue := Some (0%nat).
Definition ap_dim2 : DimValue := Some (2%nat).

(* Polygon Contains Point: II = 0 (0-dim interior intersection), EI/EB empty. *)
Definition ap_matrix_rect_contains_point : IntersectionMatrix :=
  {| im_ii := ap_dim0; im_ib := ap_cell_empty; im_ie := ap_cell_empty;
     im_bi := ap_cell_empty; im_bb := ap_cell_empty; im_be := ap_cell_empty;
     im_ei := ap_cell_empty; im_eb := ap_cell_empty; im_ee := ap_dim0 |}.

Lemma ap_matrix_rect_contains_point_witness :
  im_contains ap_matrix_rect_contains_point.
Proof.
  unfold im_contains, pat_contains, matrix_matches, ap_matrix_rect_contains_point.
  simpl. repeat split; auto.
Qed.

Lemma ap_matrix_rect_contains_point_predicate :
  predicate_holds RContains ap_matrix_rect_contains_point.
Proof.
  unfold predicate_holds. exact ap_matrix_rect_contains_point_witness.
Qed.

Lemma ap_matrix_rect_contains_point_intersects :
  im_intersects ap_matrix_rect_contains_point.
Proof.
  unfold im_intersects. left.
  unfold matrix_matches, pat_intersects_0, ap_matrix_rect_contains_point. simpl.
  repeat split; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Rectangle membership lemmas (guarded by well-formed box + strict interior). *)
(* -------------------------------------------------------------------------- *)

Lemma rect_polygon_no_holes :
  forall x0 y0 x1 y1 p,
    point_in_rect_polygon x0 y0 x1 y1 p <->
    point_in_ring p (rect_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 p.
  unfold point_in_rect_polygon, rect_polygon, point_in_polygon. simpl.
  split.
  - intros H. destruct H as [Hp _]. exact Hp.
  - intros Hp. split; [ exact Hp | ].
    intros h Hin. inversion Hin.
Qed.

Lemma strict_interior_point_in_ring :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    point_strictly_in_open_rect x0 y0 x1 y1 p ->
    point_in_ring p (rect_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 [Hx Hyp].
  apply point_in_ring_rect_iff; auto.
  split; [ exact Hyp | split; lra ].
Qed.

Lemma strict_interior_in_rect_polygon :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    point_strictly_in_open_rect x0 y0 x1 y1 p ->
    point_in_rect_polygon x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hstrict.
  rewrite rect_polygon_no_holes.
  exact (strict_interior_point_in_ring x0 y0 x1 y1 p Hx01 Hy01 Hstrict).
Qed.

Lemma strict_interior_in_rect_geometry :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    point_strictly_in_open_rect x0 y0 x1 y1 p ->
    point_in_rect_geometry x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hstrict.
  unfold point_in_rect_geometry, point_set, rect_geometry.
  exists (rect_polygon x0 y0 x1 y1). split; [ cbn [In]; auto | ].
  exact (strict_interior_in_rect_polygon x0 y0 x1 y1 p Hx01 Hy01 Hstrict).
Qed.

(* -------------------------------------------------------------------------- *)
(* Area-point Contains: the two honest layers, kept separate.                 *)
(*                                                                            *)
(* Geometry layer (above): a strict-interior point lies in the rectangle      *)
(* polygon / geometry (`strict_interior_in_rect_polygon`,                      *)
(* `strict_interior_in_rect_geometry`).  Witness layer (above): the           *)
(* hand-specified Contains matrix satisfies `im_contains`                      *)
(* (`ap_matrix_rect_contains_point_witness`).  These are deliberately NOT      *)
(* bridged: proving the strict-interior configuration's true DE-9IM equals     *)
(* the Contains witness is the deferred RelateNG step (S13+).                  *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* S4b — area-point boundary (Touches, not Contains).                         *)
(* -------------------------------------------------------------------------- *)

Definition point_on_rect_left_boundary (x0 y0 x1 y1 : R) (p : Point) : Prop :=
  px p = x0 /\ y0 < py p < y1.

Definition ap_matrix_rect_touches_boundary : IntersectionMatrix :=
  {| im_ii := ap_cell_empty; im_ib := ap_cell_empty; im_ie := ap_cell_empty;
     im_bi := ap_cell_empty; im_bb := ap_cell_empty; im_be := ap_cell_empty;
     im_ei := ap_cell_empty; im_eb := ap_dim0; im_ee := ap_cell_empty |}.

Lemma ap_matrix_rect_touches_boundary_witness :
  im_touches ap_matrix_rect_touches_boundary.
Proof.
  unfold im_touches. right; right.
  unfold matrix_matches, pat_touches_3, ap_matrix_rect_touches_boundary. simpl.
  repeat split; auto.
Qed.

Lemma left_boundary_in_rect_polygon :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    point_on_rect_left_boundary x0 y0 x1 y1 p ->
    point_in_rect_polygon x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 [Hx Hyp].
  rewrite rect_polygon_no_holes.
  apply point_in_ring_rect_iff; auto.
  split; [exact Hyp | split; [rewrite Hx; lra | lra]].
Qed.

Lemma left_boundary_not_strict_interior :
  forall x0 y0 x1 y1 p,
    point_on_rect_left_boundary x0 y0 x1 y1 p ->
    ~ point_strictly_in_open_rect x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p [Hx _] Hopen.
  destruct Hopen as [Hxp _].
  lra.
Qed.

Lemma left_boundary_in_polygon_not_strict :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    point_on_rect_left_boundary x0 y0 x1 y1 p ->
    point_in_rect_polygon x0 y0 x1 y1 p /\
    ~ point_strictly_in_open_rect x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hbnd.
  split.
  - exact (left_boundary_in_rect_polygon x0 y0 x1 y1 p Hx01 Hy01 Hbnd).
  - exact (left_boundary_not_strict_interior x0 y0 x1 y1 p Hbnd).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions strict_interior_in_rect_polygon.
Print Assumptions ap_matrix_rect_contains_point_witness.
Print Assumptions left_boundary_in_polygon_not_strict.
Print Assumptions ap_matrix_rect_touches_boundary_witness.