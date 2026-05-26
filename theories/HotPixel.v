(* ============================================================================
   NetTopologySuite.Proofs.HotPixel
   ----------------------------------------------------------------------------
   Foundational definitions for hot pixels in snap-rounding.

   A "hot pixel" is the half-open square of side 1/scale centered on a
   grid point at the given scale.  Half-open means each pixel includes
   its lower-left corner and excludes its upper-right corner on each
   axis, so adjacent pixels tile R^2 exactly once -- no overlap, no gap.

   In a snap-rounding noder (JTS/NTS), every input vertex and every
   intersection point becomes the center of a hot pixel; the noder then
   enforces that every segment passing through a hot pixel's interior
   gets a new vertex at that pixel's center.

   This file is the R-side geometric scaffold for Phase 2.  It establishes:

     - hot_pixel_radius   : half-extent of a pixel at a given scale.
     - in_hot_pixel       : a point lies within a pixel.
     - segment_touches_hot_pixel
                          : a segment endpoint is inside a pixel, or the
                            segment crosses through it.
     - on_grid            : a point lies on the integer grid at the
                            given positive scale (its coordinates are
                            integer multiples of 1/scale).

   Plus a handful of foundational lemmas (center-in-own-pixel,
   bounding-box extraction, endpoint-touches).  No algorithm yet -- the
   full snap-rounding rewriter (replacing intersection points with their
   hot-pixel centers, then re-noding) is deferred until the Phase 1
   coordinate story is complete; the rewriter needs actual intersection
   coordinates as input.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.

From NTS.Proofs Require Import Distance.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Half-extent of a hot pixel at a given grid scale.                          *)
(*                                                                            *)
(* When `scale > 0`, the grid spacing is `1 / scale`, and each pixel is a    *)
(* square of side `1 / scale`.  Half the side is `1 / (2 * scale)`.          *)
(* This is the natural arithmetic form; we don't simplify it eagerly so the  *)
(* binary64 mirror can compute the corresponding b64 quantity by the same    *)
(* `1 / (2 * scale)` recipe.                                                 *)
(* -------------------------------------------------------------------------- *)

Definition hot_pixel_radius (scale : R) : R := / (2 * scale).

(* Naming note: we use `radius` (the established term in NTS docs) for the   *)
(* half-extent of a square pixel.  Strictly it's the half-side, not a       *)
(* circular radius, but the term is conventional for grid-cell tolerances.  *)

(* -------------------------------------------------------------------------- *)
(* `in_hot_pixel P C scale`: the point P lies inside the hot pixel centered  *)
(* at C with the given scale.                                                 *)
(*                                                                            *)
(* The pixel is half-open in the JTS sense: it includes the lower bound on   *)
(* each axis and excludes the upper bound.  This avoids double-counting at   *)
(* shared boundaries between adjacent pixels.  Half-open ranges compose      *)
(* cleanly: the union over all grid centers covers R^2 exactly once, with   *)
(* no overlap and no gap.                                                    *)
(* -------------------------------------------------------------------------- *)

Definition in_hot_pixel (P C : Point) (scale : R) : Prop :=
  px C - hot_pixel_radius scale <= px P < px C + hot_pixel_radius scale /\
  py C - hot_pixel_radius scale <= py P < py C + hot_pixel_radius scale.

(* -------------------------------------------------------------------------- *)
(* `on_grid C scale`: C's coordinates are integer multiples of `1 / scale`   *)
(* at a positive scale.                                                       *)
(*                                                                            *)
(* This is the relational form: we don't compute the snapped center via a   *)
(* rounding function (the b64 mirror does that).  Here we only state what   *)
(* it means for a center to lie on the grid.  Positivity of `scale` is      *)
(* folded into the predicate so callers don't need a separate hypothesis.   *)
(* -------------------------------------------------------------------------- *)

Definition on_grid (C : Point) (scale : R) : Prop :=
  0 < scale /\
  exists i j : Z, px C = IZR i / scale /\ py C = IZR j / scale.

(* -------------------------------------------------------------------------- *)
(* `segment_touches_hot_pixel P0 P1 C scale`: the closed segment [P0, P1]   *)
(* shares at least one point with the hot pixel centered at C.              *)
(*                                                                            *)
(* Formulated as a parametric witness: there exists `t ∈ [0, 1]` such that  *)
(* the point `(1-t)·P0 + t·P1` lies in the pixel.  Endpoint-in-pixel is the  *)
(* special case `t = 0` or `t = 1`; segment-through-pixel-interior is any   *)
(* intermediate `t`.                                                         *)
(*                                                                            *)
(* This single existential form is easier to reason about than a three-way  *)
(* disjunction and corresponds directly to the geometric intuition.         *)
(* -------------------------------------------------------------------------- *)

Definition segment_point (P0 P1 : Point) (t : R) : Point :=
  mkPoint ((1 - t) * px P0 + t * px P1)
          ((1 - t) * py P0 + t * py P1).

Definition segment_touches_hot_pixel
  (P0 P1 C : Point) (scale : R) : Prop :=
  exists t : R, 0 <= t <= 1 /\ in_hot_pixel (segment_point P0 P1 t) C scale.

(* -------------------------------------------------------------------------- *)
(* Foundational lemmas.                                                       *)
(* -------------------------------------------------------------------------- *)

Lemma hot_pixel_radius_pos :
  forall scale : R, 0 < scale -> 0 < hot_pixel_radius scale.
Proof.
  intros scale Hs. unfold hot_pixel_radius.
  apply Rinv_0_lt_compat. lra.
Qed.

(* The center of a hot pixel is always inside its own pixel (when the scale  *)
(* is positive).  This is the geometric reflexivity property.                *)
Lemma in_hot_pixel_center :
  forall (C : Point) (scale : R),
    0 < scale -> in_hot_pixel C C scale.
Proof.
  intros C scale Hs.
  pose proof (hot_pixel_radius_pos scale Hs) as Hh.
  unfold in_hot_pixel. split; split; lra.
Qed.

(* Bounding-box extraction: in_hot_pixel gives Rabs bounds on the coordinate *)
(* differences.  Bound is non-strict because the pixel is half-open: the    *)
(* lower-left corner is included (px C - half = px P is admissible), giving *)
(* equality in Rabs on that side.  The strict upper bound on the other side *)
(* dominates only when the difference is positive.                          *)
Lemma in_hot_pixel_abs_bound :
  forall (P C : Point) (scale : R),
    in_hot_pixel P C scale ->
    Rabs (px P - px C) <= hot_pixel_radius scale /\
    Rabs (py P - py C) <= hot_pixel_radius scale.
Proof.
  intros P C scale [[HxL HxR] [HyL HyR]]; split; apply Rabs_le; lra.
Qed.

(* Endpoint-inside is a special case of segment-touches (taking t = 0).      *)
Lemma segment_touches_hot_pixel_l :
  forall (P0 P1 C : Point) (scale : R),
    in_hot_pixel P0 C scale ->
    segment_touches_hot_pixel P0 P1 C scale.
Proof.
  intros P0 P1 C scale H.
  exists 0. split; [lra|].
  unfold segment_point, in_hot_pixel in *.
  destruct P0 as [x0 y0], P1 as [x1 y1].
  simpl in *.
  replace ((1 - 0) * x0 + 0 * x1) with x0 by lra.
  replace ((1 - 0) * y0 + 0 * y1) with y0 by lra.
  exact H.
Qed.

(* Endpoint-inside at t = 1 is symmetric.                                    *)
Lemma segment_touches_hot_pixel_r :
  forall (P0 P1 C : Point) (scale : R),
    in_hot_pixel P1 C scale ->
    segment_touches_hot_pixel P0 P1 C scale.
Proof.
  intros P0 P1 C scale H.
  exists 1. split; [lra|].
  unfold segment_point, in_hot_pixel in *.
  destruct P0 as [x0 y0], P1 as [x1 y1].
  simpl in *.
  replace ((1 - 1) * x0 + 1 * x1) with x1 by lra.
  replace ((1 - 1) * y0 + 1 * y1) with y1 by lra.
  exact H.
Qed.

(* A degenerate segment (P0 = P1) touches a pixel iff its single endpoint   *)
(* lies in the pixel.  Useful for reasoning about vertex-as-degenerate-edge. *)
Lemma segment_touches_hot_pixel_degenerate :
  forall (P C : Point) (scale : R),
    segment_touches_hot_pixel P P C scale <-> in_hot_pixel P C scale.
Proof.
  intros P C scale; split.
  - intros [t [_ Ht]].
    unfold segment_point in Ht.
    destruct P as [x y]; simpl in *.
    replace ((1 - t) * x + t * x) with x in Ht by lra.
    replace ((1 - t) * y + t * y) with y in Ht by lra.
    exact Ht.
  - intros H. apply segment_touches_hot_pixel_l. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Counterexample: bounding-box overlap does NOT imply segment_touches.       *)
(*                                                                            *)
(* This certifies the design observation that motivates the layered          *)
(* form-(a)/form-(b) structure in the binary64 mirror.  A noder filter       *)
(* defined as pure BB-overlap would have false positives -- it would         *)
(* claim "segment touches pixel" when in fact the segment passes outside.   *)
(* Hence a sound form-(b) filter must include an actual edge-crossing test, *)
(* not just BB-overlap.                                                       *)
(*                                                                            *)
(* Witness: P0 = (0, 1), P1 = (3/2, -1), C = (3/2, 1/2), scale = 1.          *)
(*   Pixel-at-C with radius 1/2 covers [1, 2) x [0, 1).                      *)
(*   Segment x-range: [0, 3/2], y-range: [-1, 1].                            *)
(*   BBs overlap in [1, 3/2] x [0, 1) -- non-empty.                          *)
(*   But the segment's parametrization is (3t/2, 1 - 2t):                    *)
(*     - x in [1, 2): requires t >= 2/3.                                     *)
(*     - y in [0, 1):  requires 0 < t <= 1/2.                                *)
(*   These ranges are disjoint, so no t produces a point in the pixel.       *)
(*                                                                            *)
(* The lemma certifies both halves: BB-overlap holds, and                    *)
(* segment_touches_hot_pixel does not.                                        *)
(* -------------------------------------------------------------------------- *)

(* Load-bearing claim: the segment defined by the witness coordinates does
   not touch the half-open pixel.  The BB-overlap of the witness is
   trivial and is recorded as separate lemmas below. *)
Lemma bb_overlap_witness_segment_does_not_touch :
  ~ segment_touches_hot_pixel
      (mkPoint 0 1) (mkPoint (3 / 2) (- (1))) (mkPoint (3 / 2) (1 / 2)) 1.
Proof.
  intros [t [[Ht0 Ht1] Hin]].
  unfold in_hot_pixel, hot_pixel_radius, segment_point, px, py in Hin.
  simpl in Hin.
  destruct Hin as [[Hxlo Hxhi] [Hylo Hyhi]].
  (* Hxlo : 3/2 - / (2 * 1) <= (1 - t) * 0 + t * (3/2)
     Hxhi : (1 - t) * 0 + t * (3/2) < 3/2 + / (2 * 1)
     Hylo : 1/2 - / (2 * 1) <= (1 - t) * 1 + t * (- (1))
     Hyhi : (1 - t) * 1 + t * (- (1)) < 1/2 + / (2 * 1)
     Hxlo forces t >= 2/3; Hyhi forces t <= 1/2; contradiction. *)
  lra.
Qed.

(* BB-overlap facts for the witness, recorded explicitly so the
   counterexample's premises are auditable. *)
Lemma bb_overlap_witness_x_overlap :
  Rmin (px (mkPoint 0 1)) (px (mkPoint (3 / 2) (- (1))))
    <= px (mkPoint (3 / 2) (1 / 2)) + hot_pixel_radius 1
  /\
  px (mkPoint (3 / 2) (1 / 2)) - hot_pixel_radius 1
    <= Rmax (px (mkPoint 0 1)) (px (mkPoint (3 / 2) (- (1)))).
Proof.
  unfold hot_pixel_radius, px. simpl.
  split.
  - apply (Rle_trans _ 0); [apply Rmin_l|]. lra.
  - apply (Rle_trans _ (3 / 2)); [|apply Rmax_r]. lra.
Qed.

Lemma bb_overlap_witness_y_overlap :
  Rmin (py (mkPoint 0 1)) (py (mkPoint (3 / 2) (- (1))))
    <= py (mkPoint (3 / 2) (1 / 2)) + hot_pixel_radius 1
  /\
  py (mkPoint (3 / 2) (1 / 2)) - hot_pixel_radius 1
    <= Rmax (py (mkPoint 0 1)) (py (mkPoint (3 / 2) (- (1)))).
Proof.
  unfold hot_pixel_radius, py. simpl.
  split.
  - apply (Rle_trans _ (- (1))); [apply Rmin_r|]. lra.
  - apply (Rle_trans _ 1); [|apply Rmax_l]. lra.
Qed.

(* Headline: certifies that BB-overlap is not sufficient for touch. *)
Theorem bb_overlap_not_sufficient_for_touches :
  exists P0 P1 C : Point,
    (* BB-overlap on both axes *)
    Rmin (px P0) (px P1) <= px C + hot_pixel_radius 1 /\
    px C - hot_pixel_radius 1 <= Rmax (px P0) (px P1) /\
    Rmin (py P0) (py P1) <= py C + hot_pixel_radius 1 /\
    py C - hot_pixel_radius 1 <= Rmax (py P0) (py P1) /\
    (* But the segment does not touch the half-open pixel *)
    ~ segment_touches_hot_pixel P0 P1 C 1.
Proof.
  exists (mkPoint 0 1), (mkPoint (3 / 2) (- (1))), (mkPoint (3 / 2) (1 / 2)).
  pose proof bb_overlap_witness_x_overlap as [Hx1 Hx2].
  pose proof bb_overlap_witness_y_overlap as [Hy1 Hy2].
  pose proof bb_overlap_witness_segment_does_not_touch as Hntouch.
  repeat split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions bb_overlap_witness_segment_does_not_touch.
Print Assumptions bb_overlap_witness_x_overlap.
Print Assumptions bb_overlap_witness_y_overlap.
Print Assumptions bb_overlap_not_sufficient_for_touches.

(* -------------------------------------------------------------------------- *)
(* Deferred: full snap-rounding rewriter.                                     *)
(*                                                                            *)
(* The snap-rounding noder (JTS HotPixelIndex + MCIndexSnapRounder) does     *)
(* three things this file does NOT yet model:                                *)
(*                                                                            *)
(*   1. Computes a hot pixel center for every input vertex and every         *)
(*      computed intersection point.  Needs the Phase 1 coordinate story    *)
(*      (`b64_intersect_point` + forward-error bound) to land first, so we  *)
(*      have a real R-valued intersection coordinate to snap.                *)
(*                                                                            *)
(*   2. Walks each segment against an index of hot pixels and inserts a     *)
(*      new vertex at the center of every pixel the segment passes through. *)
(*      Needs `segment_touches_hot_pixel` (above) plus an enumeration of    *)
(*      pixels along a segment -- a future slice.                           *)
(*                                                                            *)
(*   3. Iterates to fixpoint: each new vertex may introduce new pixels      *)
(*      that other segments pass through.  Termination + idempotence are    *)
(*      the headline theorems of Phase 2 proper.                             *)
(*                                                                            *)
(* The full snap-rounding algorithm and its termination proof are deferred  *)
(* until the Phase 1 coordinate story (`b64_intersect_point` forward-error  *)
(* + safety) is complete.  A decidable bounding-box variant of              *)
(* `segment_touches_hot_pixel` (for the b64 noder's filter step) will be    *)
(* added on the binary64 side, where computation makes sense.               *)
(* -------------------------------------------------------------------------- *)
