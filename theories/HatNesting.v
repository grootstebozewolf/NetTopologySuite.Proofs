(* ============================================================================
   NetTopologySuite.Proofs.HatNesting
   ----------------------------------------------------------------------------
   The "hat" aperiodic einstein monotile (Smith-Myers-Kaplan-Goodman-Strauss
   2023) as a NESTING witness for the rectangle hole-inside-outer machinery.

   `HatMonotile.v` gives `hat_ring` (a non-convex 13-gon on the triangular
   lattice, with exact `sqrt 3` coordinates), proven `ring_closed`,
   `ring_has_minimum_points`, and genuinely non-convex; `HatMonotileInterior.v`
   gives `hat_point_in_ring` / `hat_hole_inside_outer` (the hat as an OUTER ring
   nesting a small square hole, by ray parity).

   This file adds the complementary witness wiring the einstein tile into the
   Stage-B rectangle machinery (`HoleInsideOuterRect.hole_inside_outer_rect`):
   the hat nests inside a bounding rectangle -- `hole_inside_outer (rect_ring …)
   hat_ring` -- via a hat vertex that the rightward-parity test places strictly
   inside the box.  No JCT, no `ring_simple`.

   HONESTY / SCOPE.  A FULL `valid_polygon` witness for the hat (the einstein
   tile as a simple polygon, or as a hole in `JCTNesting.valid_polygon_rect_outer`)
   needs `ring_simple hat_ring` -- the ~78 edge-pair, non-convex, sqrt-3
   case-analysis the corpus deliberately defers for both the Spectre and the hat
   (see `SpectreExample.v`'s header).  Empirically a uniform `nra` discharges
   most edge pairs but not all (adjacent / near-collinear pairs need bespoke
   handling, even under the rational vertical-scale embedding), so it is a
   dedicated effort, not a one-tactic slice; it remains the single missing
   structural fact for the hat's full polygon validity.

   Pure-R; three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay RectangleJCT HoleInsideOuterRect
                               HatMonotile.

Import ListNotations.
Local Open Scope R_scope.

(* sqrt 3 lies strictly between 0 and 2 (since 0 < 3 < 4). *)
Lemma sqrt3_bounds : 0 < sqrt 3 < 2.
Proof.
  assert (Hlo : 0 < sqrt 3) by (apply sqrt_lt_R0; lra).
  assert (Hsq : sqrt 3 * sqrt 3 = 3) by (apply sqrt_sqrt; lra).
  split; [ exact Hlo | nra ].
Qed.

(* -------------------------------------------------------------------------- *)
(* The hat nests inside its bounding rectangle.                                *)
(*                                                                            *)
(* The hat vertex `hexPt 3 1 = (7/2, sqrt 3 / 2)` lies strictly inside the box *)
(* [0,7) x (0,3): its x is the rational 7/2, its y is sqrt 3 / 2 in (0, 3) by  *)
(* `sqrt3_bounds`.  `hole_inside_outer_rect` then delivers the nesting.        *)
(* -------------------------------------------------------------------------- *)

Theorem hat_inside_bounding_box :
  hole_inside_outer (rect_ring 0 0 7 3) hat_ring.
Proof.
  pose proof sqrt3_bounds as [Hlo Hhi].
  apply (hole_inside_outer_rect 0 0 7 3 hat_ring (hexPt 3 1)).
  - lra.
  - lra.
  - (* In (hexPt 3 1) hat_ring -- third vertex *)
    unfold hat_ring; cbn [In]; right; right; left; reflexivity.
  - (* 0 < py (hexPt 3 1) = sqrt 3 / 2 < 3 *)
    unfold hexPt; cbn [py]; lra.
  - (* 0 <= px (hexPt 3 1) = 7/2 < 7 *)
    unfold hexPt; cbn [px]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hat_inside_bounding_box.
