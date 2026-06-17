(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveRectDisjoint
   ----------------------------------------------------------------------------
   Issue #67 (curve→matrix soundness): a concrete end-to-end relate decision —
   the bounding-box-separation Disjoint fast-path for chord-rectangle curve
   geometries.

   The set-predicate transfers (`RelateCurveInscribedGeometry`) reduce curve
   relate to the Phase-3 inscribed image, and the chord-rectangle membership
   characterisation (`RelateCurveAreaPointSound.point_in_rect_curve_geometry_
   characterisation`) pins membership to the half-open box
   `y0 < py < y1 ∧ x0 <= px < x1`.  Composing them DECIDES `geom_disjoint` for a
   real pair: two axis-aligned chord-rectangle curve geometries whose bounding
   boxes do not overlap (separated along x or y, either way) share no point.

   This is the JTS rectangle/AABB pre-filter, mechanically discharged: a single
   `geom_disjoint` conclusion from the four-way box-separation disjunction, each
   case a one-line `lra` contradiction against the box bounds.

   `Qed` at the standard classical-reals footprint; no new
   `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Overlay CurveGeometry
  RelateCurveAreaPoint RelateCurveAreaPointSound RelateCurveInscribedGeometry.
Local Open Scope R_scope.

(* Two chord-rectangle curve geometries with non-overlapping bounding boxes are
   Disjoint.  The separation disjunct is the standard AABB test: one rectangle
   lies entirely to a side of the other along x, or along y. *)
Theorem rect_curve_geometry_bbox_separated_disjoint :
  forall (x0 y0 x1 y1 x0' y0' x1' y1' : R) (n : nat),
    x0 < x1 -> y0 < y1 -> x0' < x1' -> y0' < y1' ->
    (x1 <= x0' \/ x1' <= x0 \/ y1 <= y0' \/ y1' <= y0) ->
    geom_disjoint (to_geometry (rect_curve_geometry x0 y0 x1 y1) n)
                  (to_geometry (rect_curve_geometry x0' y0' x1' y1') n).
Proof.
  intros x0 y0 x1 y1 x0' y0' x1' y1' n Hx Hy Hx' Hy' Hsep.
  unfold geom_disjoint. intros p [HA HB].
  (* membership in each chord-rectangle curve geometry = half-open box membership *)
  apply (proj1 (point_in_rect_curve_geometry_characterisation x0 y0 x1 y1 n p Hx Hy))
    in HA.
  apply (proj1 (point_in_rect_curve_geometry_characterisation x0' y0' x1' y1' n p Hx' Hy'))
    in HB.
  destruct HA as [[HyA1 HyA2] [HxA1 HxA2]].
  destruct HB as [[HyB1 HyB2] [HxB1 HxB2]].
  destruct Hsep as [H | [H | [H | H]]]; lra.
Qed.

(* Symmetric corollary form: the AABB pre-filter as a reusable Disjoint witness. *)
Corollary rect_curve_geometry_x_left_disjoint :
  forall (x0 y0 x1 y1 x0' y0' x1' y1' : R) (n : nat),
    x0 < x1 -> y0 < y1 -> x0' < x1' -> y0' < y1' ->
    x1 <= x0' ->
    geom_disjoint (to_geometry (rect_curve_geometry x0 y0 x1 y1) n)
                  (to_geometry (rect_curve_geometry x0' y0' x1' y1') n).
Proof.
  intros. apply rect_curve_geometry_bbox_separated_disjoint; auto.
Qed.

Print Assumptions rect_curve_geometry_bbox_separated_disjoint.
