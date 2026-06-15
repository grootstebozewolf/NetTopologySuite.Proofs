(* ============================================================================
   NetTopologySuite.Proofs.HatMonotileExterior
   ----------------------------------------------------------------------------
   The einstein "hat" monotile: the crossing-number point-in-polygon test
   correctly EXCLUDES a point in a concave pocket.

   `HatMonotileInterior.v` exhibits the interior witness `hat_point_in_ring`
   (a point in the hat's top bump, crossing number 1 = odd = inside).  This file
   supplies the dual -- and the more distinctly NON-CONVEX -- witness: a point in
   one of the hat's REFLEX POCKETS, i.e. inside the convex hull but outside the
   tile, which the rightward ray-parity test classifies as OUTSIDE (crossing
   number 2 = even).  No convex polygon can exhibit such a point, so this is the
   corpus's first genuinely concave point-in-polygon classification.

   The pocket.  The hat's bottom boundary has a reflex notch: the hex edges
   `(2,0)->(3,1)->(4,0)` map (via `hexPt x y = (x + y/2, y*sqrt 3/2)`) to the
   plane spike `(2,0) -> (3.5, sqrt 3/2) -> (4,0)`, whose apex `(3,1)` is the
   reflex vertex witnessed by `HatMonotile.hat_reflex_turn` (`cross < 0`).  The
   test point `p = (7/2, sqrt 3/4)` sits inside that spike triangle -- inside the
   convex hull, but in the notch, hence exterior to the hat.  Its height
   `sqrt 3/4 in (0, sqrt 3/2)` is met by exactly two edges to its right:
   the down-edge `(3,1)->(4,0)` and the up-edge `(6,0)->(7,1)`.  Two crossings
   (even) => `~ point_in_ring`.  All other edges sit at height `0`, `sqrt 3/2`,
   `sqrt 3` or `3*sqrt 3/2`, or have their x-intercept to `p`'s left.

   Choosing `py p = sqrt 3/4` (a rational multiple of `sqrt 3`) keeps every
   height/slack comparison homogeneous in `sqrt 3`, so each per-edge `nra`
   closes from `0 < sqrt 3` alone -- the same regime as the interior witness.

   SCOPE.  As in `HatMonotileInterior.v`, this is the discrete ray-parity
   (crossing-number) membership the noder/overlay pipeline uses, NOT a claim about
   the topological interior (that equivalence is the polygonal-JCT residual, and
   the hat is out of reach of the convex separation engine, cf. `HatMonotile.v`).
   It rides only the convexity-INDEPENDENT ray-parity layer.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay GeneralTriangleParity
                               HatMonotile HatMonotileInterior.
Import ListNotations.

Local Open Scope R_scope.

(* The exterior witness, in the hat's bottom reflex pocket (inside the hull). *)
Definition hat_pocket_pt : Point := mkPoint (7 / 2) (sqrt 3 / 4).

(* Per-edge ray-crossing facts via the division-free `edge_cross_sign`
   (crossing <-> height-bracket + slack sign).  `hat_no_cross` refutes a
   crossing; `hat_yes_cross_up`/`_dn` prove one for an up-/down-edge (the
   crossing disjunct is the first/second respectively). *)
Ltac hat_no_cross :=
  rewrite edge_cross_sign; cbn [px py];
  intros [[[H1 H2] H3] | [[H1 H2] H3]]; nra.

Ltac hat_yes_cross_up :=
  rewrite edge_cross_sign; cbn [px py]; left; repeat split; nra.

Ltac hat_yes_cross_dn :=
  rewrite edge_cross_sign; cbn [px py]; right; repeat split; nra.

(* Even-excludes-odd for the mutually-inductive ray parity (the corpus keeps
   this as a per-file local lemma; structural induction inverting both
   derivations -- identical to `JCT_Counterexample.ray_parity_even_not_odd`). *)
Lemma ray_parity_even_not_odd :
  forall (p : Point) (es : list Edge),
    ray_parity_even p es -> ~ ray_parity_odd p es.
Proof.
  intros p es; induction es as [|e es' IH]; intros Heven Hodd.
  - inversion Hodd.
  - inversion Heven; subst; inversion Hodd; subst;
      try (eapply IH; eassumption);
      try contradiction.
Qed.

(* The crossing-number / ray-parity membership: the hat EXCLUDES the pocket
   point.  Crossing number 2 (edges (3,1)->(4,0) and (6,0)->(7,1)) is even. *)
Theorem hat_pocket_not_in_ring : ~ point_in_ring hat_pocket_pt hat_ring.
Proof.
  pose proof (sqrt_lt_R0 3 ltac:(lra)) as Hs3.
  unfold point_in_ring, hat_ring, hat_pocket_pt.
  cbn [ring_edges]. unfold hexPt.
  apply ray_parity_even_not_odd.
  apply rpe_skip;  [ hat_no_cross | ].      (* e1  (0,0)-(2,0)   *)
  apply rpe_skip;  [ hat_no_cross | ].      (* e2  (2,0)-(3,1)   *)
  apply rpe_cross; [ hat_yes_cross_dn | ].  (* e3  (3,1)-(4,0)  HIT *)
  apply rpo_skip;  [ hat_no_cross | ].      (* e4  (4,0)-(6,0)   *)
  apply rpo_cross; [ hat_yes_cross_up | ].  (* e5  (6,0)-(7,1)  HIT *)
  apply rpe_skip;  [ hat_no_cross | ].      (* e6  (7,1)-(6,2)   *)
  apply rpe_skip;  [ hat_no_cross | ].      (* e7  (6,2)-(4,2)   *)
  apply rpe_skip;  [ hat_no_cross | ].      (* e8  (4,2)-(3,3)   *)
  apply rpe_skip;  [ hat_no_cross | ].      (* e9  (3,3)-(2,2)   *)
  apply rpe_skip;  [ hat_no_cross | ].      (* e10 (2,2)-(0,2)   *)
  apply rpe_skip;  [ hat_no_cross | ].      (* e11 (0,2)-(0,1)   *)
  apply rpe_skip;  [ hat_no_cross | ].      (* e12 (0,1)-(-1,1)  *)
  apply rpe_skip;  [ hat_no_cross | ].      (* e13 (-1,1)-(0,0)  *)
  apply rpe_nil.
Qed.

(* The einstein's first in/out ray-parity classification pair: the top-bump
   point is inside (odd), the bottom-pocket point is outside (even).  The pocket
   point lies in a reflex notch -- inside the convex hull, outside the tile --
   a configuration no convex polygon can present. *)
Theorem hat_parity_classification :
  point_in_ring hat_pt hat_ring /\ ~ point_in_ring hat_pocket_pt hat_ring.
Proof.
  split; [ apply hat_point_in_ring | apply hat_pocket_not_in_ring ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hat_pocket_not_in_ring.
Print Assumptions hat_parity_classification.
