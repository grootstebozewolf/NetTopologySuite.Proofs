(* ============================================================================
   NetTopologySuite.Proofs.HatMonotileInterior
   ----------------------------------------------------------------------------
   Using the "hat" einstein: the corpus's ray-parity point-in-polygon test
   applied to the actual aperiodic monotile.

   `HatMonotile.v` formalises the hat as a NON-CONVEX 13-gon `Ring` and notes
   that its *geometric/topological* interior theorem is out of reach of the
   convex separation engine (it needs the full polygonal JCT).  But the
   COMBINATORIAL membership predicate `Overlay.point_in_ring` -- the rightward
   ray-parity (crossing-number) test -- is purely discrete and works for ANY
   simple polygon, convex or not.  Here we exercise it on the hat directly.

   Witness point: `p = (17/4, 5*sqrt 3/4)`, inside the hat's top "bump" (the
   triangular peak over vertices `(4,2),(3,3),(2,2)` in hex coordinates, whose
   apex `(3,3)` is the only vertex above height `2*(sqrt 3/2) = sqrt 3`).  At
   `p`'s height `5*sqrt 3/4 in (sqrt 3, 3*sqrt 3/2)`, only the two bump edges
   span the ray's level; of those exactly the right one (`(4,2)->(3,3)`) lies to
   `p`'s right and is crossed, the left one (`(3,3)->(2,2)`) is not -- so the
   crossing number is 1 (odd) and `p` is `point_in_ring`.  All other 11 edges
   sit at or below height `sqrt 3 < py p`, so they cannot span the ray.

   `hat_hole_inside_outer` then nests a (small square) hole carrying `p` as a
   vertex inside the hat -- `hole_inside_outer` for the einstein, by ray parity.

   SCOPE.  This is the ray-parity (crossing-number) interior, the same predicate
   the noder/overlay pipeline uses; it is NOT a claim about the topological
   interior (that equivalence is the polygonal-JCT residual, cf.
   `HatMonotile.v`'s note and `extract-rings-proof-structure.md`).

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay GeneralTriangleParity HatMonotile.
Import ListNotations.

Local Open Scope R_scope.

(* The interior witness, in the hat's top bump. *)
Definition hat_pt : Point := mkPoint (17 / 4) (5 * sqrt 3 / 4).

(* Tactics for the per-edge ray-crossing facts, via the division-free
   `edge_cross_sign` (crossing <-> height-bracket + slack sign). *)
Ltac hat_no_cross :=
  rewrite edge_cross_sign; cbn [px py];
  intros [[[H1 H2] H3] | [[H1 H2] H3]]; nra.

Ltac hat_yes_cross :=
  rewrite edge_cross_sign; cbn [px py]; left; repeat split; nra.

(* The crossing-number / ray-parity membership: the hat CONTAINS hat_pt. *)
Theorem hat_point_in_ring : point_in_ring hat_pt hat_ring.
Proof.
  pose proof (sqrt_lt_R0 3 ltac:(lra)) as Hs3.
  unfold point_in_ring, hat_ring, hat_pt.
  cbn [ring_edges]. unfold hexPt.
  (* edges e1..e7 sit at height <= sqrt 3 < py p : no crossing *)
  apply rpo_skip; [ hat_no_cross | ].   (* e1  (0,0)-(2,0)   *)
  apply rpo_skip; [ hat_no_cross | ].   (* e2  (2,0)-(3,1)   *)
  apply rpo_skip; [ hat_no_cross | ].   (* e3  (3,1)-(4,0)   *)
  apply rpo_skip; [ hat_no_cross | ].   (* e4  (4,0)-(6,0)   *)
  apply rpo_skip; [ hat_no_cross | ].   (* e5  (6,0)-(7,1)   *)
  apply rpo_skip; [ hat_no_cross | ].   (* e6  (7,1)-(6,2)   *)
  apply rpo_skip; [ hat_no_cross | ].   (* e7  (6,2)-(4,2)   *)
  (* e8  (4,2)-(3,3): the right bump edge, crossed once *)
  apply rpo_cross; [ hat_yes_cross | ].
  (* e9..e13 : the left bump edge (not crossed) then height <= sqrt 3 edges *)
  apply rpe_skip; [ hat_no_cross | ].   (* e9  (3,3)-(2,2)   *)
  apply rpe_skip; [ hat_no_cross | ].   (* e10 (2,2)-(0,2)   *)
  apply rpe_skip; [ hat_no_cross | ].   (* e11 (0,2)-(0,1)   *)
  apply rpe_skip; [ hat_no_cross | ].   (* e12 (0,1)-(-1,1)  *)
  apply rpe_skip; [ hat_no_cross | ].   (* e13 (-1,1)-(0,0)  *)
  apply rpe_nil.
Qed.

(* Nesting: a hole carrying hat_pt as a vertex is inside the hat. *)
Theorem hat_hole_inside_outer :
  hole_inside_outer hat_ring
    [ hat_pt
    ; mkPoint (17 / 4 + 1 / 10) (5 * sqrt 3 / 4)
    ; mkPoint (17 / 4 + 1 / 10) (5 * sqrt 3 / 4 + 1 / 10)
    ; mkPoint (17 / 4) (5 * sqrt 3 / 4 + 1 / 10)
    ; hat_pt ].
Proof.
  exists hat_pt. split; [ cbn [In]; auto | apply hat_point_in_ring ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hat_point_in_ring.
Print Assumptions hat_hole_inside_outer.
