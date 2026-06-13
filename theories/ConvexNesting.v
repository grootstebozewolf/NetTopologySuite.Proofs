(* ============================================================================
   NetTopologySuite.Proofs.ConvexNesting
   ----------------------------------------------------------------------------
   General convex `hole_inside_outer`, guarded by the one named residual.

   Rectangle, triangle, diamond, and (HexagonNesting.v) a convex hexagon all
   close `hole_inside_outer` UNCONDITIONALLY by an explicit parity proof.  The
   GENERAL convex-n-gon case hinges on a single missing fact -- the
   "convex-chain monotonicity": a rightward ray from a strictly-interior point
   (positive in every edge half-plane, `0 < conv_min hps`) crosses an odd
   number of the n edges, i.e. `point_in_ring`.  This is exactly the interior
   parity obligation that `ConvexOffringSeam.convex_parity_seam_offring_of`
   leaves as a hypothesis.

   This file packages that residual as a named predicate
   `convex_interior_parity` and gives the general convex `hole_inside_outer`
   GUARDED by it: a hole with a vertex strictly inside a convex outer nests
   inside, modulo the one monotonicity fact.  Concrete convex shapes discharge
   `convex_interior_parity` per family (rectangle/triangle do; the general n-gon
   is the open lemma); until then this is the honest conditional headline.

   Pure-R; three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra.
From NTS.Proofs Require Import Distance Overlay ConvexField PointInRingCorrect.

Import ListNotations.
Local Open Scope R_scope.

(* The convex-chain monotonicity residual: every strictly-interior point (in
   general position) has odd ray-parity.  This is the SOLE open fact for a
   general convex outer; it is what `convex_parity_seam_offring_of` carries as
   its interior-parity obligation. *)
Definition convex_interior_parity (outer : Ring) (hps : list (R * R * R)) : Prop :=
  forall q : Point,
    0 < conv_min hps q ->
    ray_avoids_vertices q outer ->
    no_horizontal_edge_at q outer ->
    point_in_ring q outer.

(* Guarded general convex hole_inside_outer: a hole with a vertex strictly
   inside the convex outer (positive in every half-plane, in general position)
   nests inside -- conditional only on `convex_interior_parity`. *)
Theorem hole_inside_outer_convex_guarded :
  forall (outer hole : Ring) (hps : list (R * R * R)) (p : Point),
    convex_interior_parity outer hps ->
    In p hole ->
    0 < conv_min hps p ->
    ray_avoids_vertices p outer ->
    no_horizontal_edge_at p outer ->
    hole_inside_outer outer hole.
Proof.
  intros outer hole hps p Hpar Hin Hpos Hrav Hnh.
  exists p. split; [ exact Hin | exact (Hpar p Hpos Hrav Hnh) ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hole_inside_outer_convex_guarded.
