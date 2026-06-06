(* ============================================================================
   NetTopologySuite.Proofs.HoleInsideOuterConvexExample
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, analytic seam -- Stage C opened
   (convex beachhead, concrete non-axis-aligned instance)
   (docs/extract-rings-proof-structure.md §4; docs/hole-inside-outer-plan.md
   Stage C).

   HONEST SCOPE.  Stage B closed `hole_inside_outer` UNCONDITIONALLY for all
   axis-aligned rectangles, because `RectangleJCT` already provides the parity
   characterisation `point_in_ring_rect_iff`.  `ConvexField` provides the
   separation engine (`conv_min`, `convex_separation`) but NO parity
   characterisation for convex rings -- the general convex
   `point_in_ring p (convex_ring ..)` (a ray-crossing count over an arbitrary CCW
   convex polygon, i.e. convex-chain monotonicity) is substantial geometric work
   and is deliberately NOT attempted here.

   This file lands the bounded, honest step: the FIRST convex instance BEYOND
   rectangles -- a diamond (rotated square) whose four edges are SLANTED, so the
   ray-crossing test exercises real x-intercept arithmetic (not the rectangle's
   degenerate vertical/horizontal edges).  It shows the parity route extends to
   non-axis-aligned convex shapes, and is a regression anchor for the eventual
   general convex theorem.

     - `diamond`                       : the CCW diamond (2,0)-(4,2)-(2,4)-(0,2);
     - `diamond_interior_point_in_ring`: `point_in_ring (2,1) diamond` (one
       slanted edge crossed -> odd), via the `ray_parity_odd` constructors + lra;
     - `hole_inside_outer_diamond`     : a hole vertex at (2,1) lies inside.

   Pure `R`; no `Admitted` / `Axiom` / `Parameter`.  Standard three-axiom
   classical-reals base.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra.
From NTS.Proofs Require Import Distance Overlay.

Import ListNotations.
Open Scope R_scope.

(* A diamond (axis-aligned square rotated 45 degrees), CCW, centred at (2,2). *)
Definition d_e : Point := mkPoint 4 2.   (* east  *)
Definition d_n : Point := mkPoint 2 4.   (* north *)
Definition d_w : Point := mkPoint 0 2.   (* west  *)
Definition d_s : Point := mkPoint 2 0.   (* south *)
Definition diamond : Ring := [d_s; d_e; d_n; d_w; d_s].

(* An interior point off all vertex heights (y in {0,2,4}), so the rightward ray
   grazes no vertex. *)
Definition dctr : Point := mkPoint 2 1.

(* The rightward ray from (2,1) crosses exactly the south-east edge (2,0)-(4,2)
   -- a SLANTED edge whose x-intercept at y=1 is x=3 > 2 -- and no other.  Odd
   parity, hence `point_in_ring`. *)
Lemma diamond_interior_point_in_ring : point_in_ring dctr diamond.
Proof.
  unfold point_in_ring, diamond, dctr. cbn [ring_edges].
  (* SE edge (2,0)-(4,2): crossed *)
  apply rpo_cross.
  { unfold edge_crosses_ray, d_s, d_e. cbn [px py]. left. split.
    - lra.
    - lra. }   (* 2 < 2 + (4-2)*(1-0)/(2-0) = 3 *)
  (* NE edge (4,2)-(2,4): not crossed (y=1 below both) *)
  apply rpe_skip.
  { unfold edge_crosses_ray, d_e, d_n. cbn [px py]. intros [[H _] | [H _]]; lra. }
  (* NW edge (2,4)-(0,2): not crossed *)
  apply rpe_skip.
  { unfold edge_crosses_ray, d_n, d_w. cbn [px py]. intros [[H _] | [H _]]; lra. }
  (* SW edge (0,2)-(2,0): y-range hits, but x-intercept x=1 < 2, so ray (going
     right) does not cross *)
  apply rpe_skip.
  { unfold edge_crosses_ray, d_w, d_s. cbn [px py]. intros [[H _] | [_ Hx]].
    - lra.
    - revert Hx. lra. }   (* 2 < 2 + (0-2)*(1-0)/(2-0) = 1 is false *)
  apply rpe_nil.
Qed.

(* A small hole sharing the interior point (2,1) as a vertex. *)
Definition hole_diamond : Ring :=
  [mkPoint 2 1; mkPoint 2 (3/2); mkPoint (5/2) 1].

Theorem hole_inside_outer_diamond : hole_inside_outer diamond hole_diamond.
Proof.
  exists dctr. split.
  - unfold hole_diamond, dctr. cbn [In]. left. reflexivity.
  - exact diamond_interior_point_in_ring.
Qed.
