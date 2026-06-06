(* ============================================================================
   NetTopologySuite.Proofs.SpectreExample
   ----------------------------------------------------------------------------
   A point-in-ring regression anchor on the SPECTRE aperiodic monotile -- a
   complex NON-CONVEX 14-gon -- exercising the `Overlay.ray_parity_odd` machinery
   on a hard shape (docs/spectre-example.md).

   SCOPE / HONESTY.  This is a regression anchor / stress test for the parity
   predicate, NOT part of the `extract_rings_valid` pipeline (a monotile is not a
   pipeline face).  What is proved, unconditionally and `Qed`:
     - `spectre_ring_closed`     : `ring_closed`  (structural);
     - `spectre_min_points`      : `ring_has_minimum_points` (14 >= 4 vertices);
     - `spectre_point_in_ring`   : `point_in_ring` for a verified interior point,
       by walking the `ray_parity_odd` constructors over all 13 edges (the
       rightward ray crosses exactly one edge -> odd parity);
     - `hole_inside_outer_spectre`: a hole vertex at that point lies inside.

   What is NOT claimed: `ring_simple` for this non-convex 14-gon (no two
   non-adjacent edges properly cross) is ~70 edge-pair checks and is a separate,
   larger effort -- deliberately omitted, not hand-waved.

   COORDINATES.  The Spectre lives on a hex grid; the metric-exact equilateral
   embedding maps hex `(x,y)` to `(x + y/2, y * (sqrt 3 / 2))`.  We use the
   RATIONAL embedding `(x + y/2, y)` -- the same combinatorial polygon, differing
   only by a uniform VERTICAL SCALE (`* sqrt 3 / 2`).  A vertical scale maps
   horizontal rays to horizontal rays and preserves left/right order at any
   fixed height, so the rightward-ray CROSSING PARITY (hence `point_in_ring`) is
   identical to the equilateral version -- while keeping all arithmetic rational
   so `lra` discharges each `edge_crosses_ray` exactly.  The hex vertex
   coordinates are exactly the canonical Spectre's.

   Pure `R`; no `Admitted` / `Axiom` / `Parameter`.  Standard three-axiom
   classical-reals base.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia.
From NTS.Proofs Require Import Distance Overlay HexXScaleBridge.

Import ListNotations.
Open Scope R_scope.

(* Rational hex->cartesian embedding (height = hex y; see header). *)
Definition hpt (x y : R) : Point := mkPoint (x + y / 2) y.

(* The canonical Spectre 14-gon (hex coordinates exactly as the monotile). *)
Definition spectre_ring : Ring :=
  [ hpt 0    0
  ; hpt 2    0
  ; hpt 3    1
  ; hpt 4    0
  ; hpt 6    0
  ; hpt 7    1
  ; hpt 6    2
  ; hpt 4    2
  ; hpt 3    3
  ; hpt 2    2
  ; hpt 0    2
  ; hpt 0    1
  ; hpt (-1) 1
  ; hpt 0    0 ].

(* An interior point: height 1/2 (between hex levels 0 and 1, so the rightward
   ray grazes no vertex), x = 5 (between the two "feet"). *)
Definition spec_pt : Point := mkPoint 5 (1/2).

(* -------------------------------------------------------------------------- *)
(* §1  Structural facts (coordinate-agnostic).                                 *)
(* -------------------------------------------------------------------------- *)

Lemma spectre_ring_closed : ring_closed spectre_ring.
Proof.
  exists (hpt 0 0),
    [ hpt 2 0; hpt 3 1; hpt 4 0; hpt 6 0; hpt 7 1; hpt 6 2; hpt 4 2;
      hpt 3 3; hpt 2 2; hpt 0 2; hpt 0 1; hpt (-1) 1 ].
  reflexivity.
Qed.

Lemma spectre_min_points : ring_has_minimum_points spectre_ring.
Proof. unfold ring_has_minimum_points, spectre_ring. cbn [length]. lia. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  point_in_ring for the interior point.                                   *)
(* -------------------------------------------------------------------------- *)

(* Discharge a NOT-crossed edge: in each disjunct either the y-range or the
   x-intercept inequality is contradictory (all rational, so `lra`). *)
Ltac edge_not_crossed :=
  unfold edge_crosses_ray, hpt, spec_pt; cbn [px py];
  intros [[[Ha Hb] Hx] | [[Ha Hb] Hx]]; lra.

Lemma spectre_point_in_ring : point_in_ring spec_pt spectre_ring.
Proof.
  unfold point_in_ring, spectre_ring. cbn [ring_edges].
  apply rpo_skip; [ edge_not_crossed | ].   (* E1  (0,0)-(2,0)   horizontal *)
  apply rpo_skip; [ edge_not_crossed | ].   (* E2  (2,0)-(3.5,1) intercept 2.75 < 5 *)
  apply rpo_skip; [ edge_not_crossed | ].   (* E3  (3.5,1)-(4,0) intercept 3.75 < 5 *)
  apply rpo_skip; [ edge_not_crossed | ].   (* E4  (4,0)-(6,0)   horizontal *)
  apply rpo_cross.                          (* E5  (6,0)-(7.5,1) intercept 6.75 > 5: CROSSED *)
  { unfold edge_crosses_ray, hpt, spec_pt; cbn [px py]. left. split; lra. }
  apply rpe_skip; [ edge_not_crossed | ].   (* E6  (7.5,1)-(7,2)  above *)
  apply rpe_skip; [ edge_not_crossed | ].   (* E7  (7,2)-(5,2)    horizontal *)
  apply rpe_skip; [ edge_not_crossed | ].   (* E8  (5,2)-(4.5,3)  above *)
  apply rpe_skip; [ edge_not_crossed | ].   (* E9  (4.5,3)-(3,2)  above *)
  apply rpe_skip; [ edge_not_crossed | ].   (* E10 (3,2)-(1,2)    horizontal *)
  apply rpe_skip; [ edge_not_crossed | ].   (* E11 (1,2)-(0.5,1)  above *)
  apply rpe_skip; [ edge_not_crossed | ].   (* E12 (0.5,1)-(-0.5,1) horizontal *)
  apply rpe_skip; [ edge_not_crossed | ].   (* E13 (-0.5,1)-(0,0) intercept -0.25 < 5 *)
  apply rpe_nil.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  hole_inside_outer on the Spectre.                                       *)
(* -------------------------------------------------------------------------- *)

Definition hole_spectre : Ring :=
  [ mkPoint 5 (1/2); mkPoint 5 (3/4); mkPoint (11/2) (1/2) ].

Theorem hole_inside_outer_spectre : hole_inside_outer spectre_ring hole_spectre.
Proof.
  exists spec_pt. split.
  - unfold hole_spectre, spec_pt. cbn [In]. left. reflexivity.
  - exact spectre_point_in_ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Lift to true equilateral R-geometry via the x-scale bridge.             *)
(*     (2-line follow-up after the HexXScaleBridge.)                         *)
(* -------------------------------------------------------------------------- *)

Theorem spectre_point_in_ring_R :
  point_in_ring (xscale (sqrt 3 / 2) spec_pt)
                (ring_edges (map (xscale (sqrt 3 / 2)) spectre_ring)).
Proof.
  apply (ray_parity_odd_xscale (sqrt 3 / 2) spec_pt (ring_edges spectre_ring)
                               sqrt3_2_pos spectre_point_in_ring).
Qed.
