(* ============================================================================
   NetTopologySuite.Proofs.HoleInsideOuterRect
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, analytic seam -- Stage B (rectangle
   beachhead, UNCONDITIONAL): `hole_inside_outer` for any rectangular outer ring
   (docs/extract-rings-proof-structure.md §4; docs/hole-inside-outer-plan.md
   Stage B).

   The concrete witness (`HoleInsideOuterExample.v`) fixed a single 4x4 square.
   This slice generalises it to ALL axis-aligned rectangles, with no JCT
   hypothesis: `RectangleJCT.point_in_ring_rect_iff` already characterises
   `point_in_ring` for a rectangle as box-membership (a Qed parity computation),
   and `hole_inside_outer` is *defined* via `point_in_ring`.  So a hole with any
   vertex inside the box lies inside the rectangle, unconditionally.

     - `point_in_ring_rect`     : box-membership -> `point_in_ring p (rect_ring ..)`;
     - `hole_inside_outer_rect` : a hole vertex in the box -> `hole_inside_outer`
       of the rectangle outer (the first NON-TOY discharge of the seam);
     - `hole_inside_outer_rect_strict` : the convenient strict-interior form.

   This closes the analytic seam for the rectangular-outer case outright.  Convex
   and triangular outers (Stages C/D, on `ConvexField.convex_separation` and the
   triangle separation engines) and the general simple-polygon JCT (Stage E, the
   registered residual) remain.

   Pure `R`; no `Admitted` / `Axiom` / `Parameter`.  Standard three-axiom
   classical-reals base, introduces none of its own.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra.
From NTS.Proofs Require Import Distance Overlay RectangleJCT.

Import ListNotations.
Open Scope R_scope.

(* `point_in_ring` for a rectangle reduces to box-membership (the <- direction of
   `RectangleJCT.point_in_ring_rect_iff`). *)
Lemma point_in_ring_rect : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  y0 < py p < y1 -> x0 <= px p < x1 ->
  point_in_ring p (rect_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hpy Hpx.
  apply point_in_ring_rect_iff; [ exact Hx01 | exact Hy01 | split; assumption ].
Qed.

(* UNCONDITIONAL: a hole with a vertex inside the box lies inside a rectangular
   outer ring.  Generalises the fixed-4x4 witness to every rectangle. *)
Theorem hole_inside_outer_rect : forall x0 y0 x1 y1 (hole : Ring) p,
  x0 < x1 -> y0 < y1 ->
  In p hole ->
  y0 < py p < y1 -> x0 <= px p < x1 ->
  hole_inside_outer (rect_ring x0 y0 x1 y1) hole.
Proof.
  intros x0 y0 x1 y1 hole p Hx01 Hy01 Hin Hpy Hpx.
  exists p. split; [ exact Hin | apply point_in_ring_rect; assumption ].
Qed.

(* Convenient strict-interior form: a hole vertex strictly inside the open box. *)
Corollary hole_inside_outer_rect_strict : forall x0 y0 x1 y1 (hole : Ring) p,
  x0 < x1 -> y0 < y1 ->
  In p hole ->
  x0 < px p < x1 -> y0 < py p < y1 ->
  hole_inside_outer (rect_ring x0 y0 x1 y1) hole.
Proof.
  intros x0 y0 x1 y1 hole p Hx01 Hy01 Hin Hpx Hpy.
  apply (hole_inside_outer_rect x0 y0 x1 y1 hole p);
    [ exact Hx01 | exact Hy01 | exact Hin | exact Hpy | ].
  destruct Hpx as [Hl Hr]. split; lra.
Qed.

(* Sanity: the merged 4x4-square witness is now an instance. *)
Example hole_inside_outer_4x4_via_rect :
  hole_inside_outer (rect_ring 0 0 4 4) [mkPoint 2 2; mkPoint 3 2].
Proof.
  apply (hole_inside_outer_rect_strict 0 0 4 4 _ (mkPoint 2 2));
    [ lra | lra | left; reflexivity | cbn; lra | cbn; lra ].
Qed.
