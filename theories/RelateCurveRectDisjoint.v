(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveRectDisjoint
   ----------------------------------------------------------------------------
   Issue #67 (curve→matrix soundness): concrete end-to-end relate decisions —
   the bounding-box (AABB) relate fast-paths for chord-rectangle curve
   geometries: Disjoint when the boxes are separated, Intersects when they
   overlap.

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

(* --------------------------------------------------------------------------- *)
(* The converse fast-path: OVERLAPPING boxes intersect.  A 1-D overlap witness  *)
(* (the midpoint of the two intervals' intersection) lifts to a point strictly  *)
(* inside both boxes.                                                           *)
(* --------------------------------------------------------------------------- *)

(* Two overlapping real intervals share an interior point. *)
Lemma interval_overlap_witness_open :
  forall a b c d : R,
    a < b -> c < d -> a < d -> c < b ->
    exists t, (a < t < b) /\ (c < t < d).
Proof.
  intros a b c d Hab Hcd Had Hcb.
  exists ((Rmax a c + Rmin b d) / 2).
  unfold Rmax, Rmin.
  destruct (Rle_dec a c); destruct (Rle_dec b d); repeat split; lra.
Qed.

(* Two chord-rectangle curve geometries with OVERLAPPING bounding boxes share a
   point — the converse of the separation fast-path.  Overlap is the negation of
   separation: each interval's start precedes the other's end on both axes. *)
Theorem rect_curve_geometry_bbox_overlap_intersects :
  forall (x0 y0 x1 y1 x0' y0' x1' y1' : R) (n : nat),
    x0 < x1 -> y0 < y1 -> x0' < x1' -> y0' < y1' ->
    x0 < x1' -> x0' < x1 -> y0 < y1' -> y0' < y1 ->
    geom_intersects (to_geometry (rect_curve_geometry x0 y0 x1 y1) n)
                    (to_geometry (rect_curve_geometry x0' y0' x1' y1') n).
Proof.
  intros x0 y0 x1 y1 x0' y0' x1' y1' n Hx Hy Hx' Hy' Hox1 Hox2 Hoy1 Hoy2.
  destruct (interval_overlap_witness_open x0 x1 x0' x1' Hx Hx' Hox1 Hox2)
    as [wx [[Hwx_a Hwx_b] [Hwx_c Hwx_d]]].
  destruct (interval_overlap_witness_open y0 y1 y0' y1' Hy Hy' Hoy1 Hoy2)
    as [wy [[Hwy_a Hwy_b] [Hwy_c Hwy_d]]].
  unfold geom_intersects. exists (mkPoint wx wy). split.
  - apply (proj2 (point_in_rect_curve_geometry_characterisation
                    x0 y0 x1 y1 n (mkPoint wx wy) Hx Hy)).
    cbn [px py]. repeat split; lra.
  - apply (proj2 (point_in_rect_curve_geometry_characterisation
                    x0' y0' x1' y1' n (mkPoint wx wy) Hx' Hy')).
    cbn [px py]. repeat split; lra.
Qed.

Print Assumptions rect_curve_geometry_bbox_separated_disjoint.
Print Assumptions rect_curve_geometry_bbox_overlap_intersects.
