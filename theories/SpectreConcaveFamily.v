(* ============================================================================
   NetTopologySuite.Proofs.SpectreConcaveFamily
   ----------------------------------------------------------------------------
   The Spectre aperiodic monotile as the corpus's SECOND fully-mechanized
   concave family -- reaching parity with the hat einstein.

   `SpectreExample.v` lands the Spectre as a non-convex 14-gon `spectre_ring`
   (rational hex embedding `hpt x y = (x + y/2, y)`), proves it closed, of
   minimum points, and an INTERIOR ray-parity witness `spectre_point_in_ring`
   at `(5, 1/2)` (crossing-number 1 = odd = inside), but DELIBERATELY DEFERS
   `ring_simple` (the ~70 edge-pair non-self-intersection bash) and supplies no
   exterior witness.  This file closes both, mirroring `HatValidPolygon.v`
   (`ring_simple` + `valid_polygon`) and `HatMonotileExterior.v` (the concave
   pocket exterior witness):

     - `spectre_ring_simple`     : no two distinct edges cross properly;
     - `valid_polygon_spectre`   : the Spectre alone is a `valid_polygon`;
     - `spectre_non_convex`      : a reflex turn and a convex turn (`cross`);
     - `spectre_pocket_not_in_ring`     : a point in the bottom reflex notch
       (inside the convex hull, outside the tile) has crossing-number 2 = even
       => `~ point_in_ring` -- a hull-interior exterior point no convex polygon
       can present;
     - `spectre_parity_classification`  : the Spectre's in/out pair.

   Because the embedding is RATIONAL (vs the hat's `sqrt 3`), every goal closes
   by `lra`/`nra` with no `sqrt 3` machinery.  No new general theorem -- only
   instantiations of existing predicates.

   The pocket.  As for the hat, the bottom boundary has a reflex notch: the
   edges `(2,0)->(3.5,1)->(4,0)` form an upward spike whose apex `(3,1)` is the
   reflex vertex (`spectre_non_convex`).  The point `(7/2, 1/2)` sits inside the
   spike triangle.  At height `1/2 in (0,1)` the rightward ray meets exactly the
   down-edge `(3.5,1)->(4,0)` (intercept 3.75) and the up-edge `(6,0)->(7.5,1)`
   (intercept 6.75); two crossings (even) => outside.

   SCOPE.  Convexity-INDEPENDENT ray-parity (crossing-number) membership, the
   same the noder/overlay pipeline uses; NOT the JCT topological-interior
   equivalence (out of reach of the convex separation engine for a non-convex
   ring).

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Overlay Orientation
                               RingSimple FacePolygonHoles
                               SpectreExample.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The Spectre ring is simple (the deferred ~70 edge-pair bash).           *)
(*                                                                            *)
(* No two distinct edges of the 14-gon cross at an interior point.  Each       *)
(* edge-pair crossing system `(1-t)P0 + tP1 = (1-s)Q0 + sQ1` is linear in      *)
(* (t,s); all coordinates rational, so a single `nra` refutes every off-       *)
(* diagonal pair (the diagonal `e <> e` cases close by `Hne`).                 *)
(* -------------------------------------------------------------------------- *)

Theorem spectre_ring_simple : ring_simple spectre_ring.
Proof.
  unfold ring_simple.
  intros e1 e2 H1 H2 Hne.
  unfold spectre_ring in H1, H2. cbn [ring_edges] in H1, H2. cbn [In] in H1, H2.
  destruct H1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
  destruct H2 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
    try (exfalso; apply Hne; reflexivity);
    intros (t & s & Ht & Hs & Hx & Hy);
    unfold hpt in Hx, Hy; cbn [fst snd px py] in Hx, Hy; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The Spectre is a valid polygon.                                         *)
(* -------------------------------------------------------------------------- *)

Theorem valid_polygon_spectre : valid_polygon (mkPolygon spectre_ring []).
Proof.
  apply polygon_valid_of_rings.
  - apply spectre_ring_closed.
  - apply spectre_ring_simple.
  - apply spectre_min_points.
  - intros h [].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Non-convexity: the boundary turns both ways (`cross` = signed area).     *)
(* -------------------------------------------------------------------------- *)

(* A reflex (clockwise) turn at the spike apex (3,1). *)
Lemma spectre_reflex_turn : cross (hpt 2 0) (hpt 3 1) (hpt 4 0) < 0.
Proof. unfold cross, hpt; cbn [px py]; lra. Qed.

(* A convex (counter-clockwise) turn at (2,0). *)
Lemma spectre_convex_turn : 0 < cross (hpt 0 0) (hpt 2 0) (hpt 3 1).
Proof. unfold cross, hpt; cbn [px py]; lra. Qed.

Theorem spectre_non_convex :
  cross (hpt 2 0) (hpt 3 1) (hpt 4 0) < 0
  /\ 0 < cross (hpt 0 0) (hpt 2 0) (hpt 3 1).
Proof. split; [ apply spectre_reflex_turn | apply spectre_convex_turn ]. Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The concave-pocket exterior witness.                                    *)
(* -------------------------------------------------------------------------- *)

(* The exterior witness, in the bottom reflex pocket (inside the hull). *)
Definition spectre_pocket_pt : Point := mkPoint (7 / 2) (1 / 2).

(* Discharge a NOT-crossed edge (each disjunct contradictory; all rational). *)
Ltac spec_no_cross :=
  unfold edge_crosses_ray, hpt, spectre_pocket_pt; cbn [px py];
  intros [[[Ha Hb] Hx] | [[Ha Hb] Hx]]; lra.

(* Even-excludes-odd for the mutually-inductive ray parity (a per-file local
   lemma, as in `JCT_Counterexample.v` / `HatMonotileExterior.v`). *)
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

(* The pocket point is OUTSIDE: crossing-number 2 (edges (3.5,1)->(4,0) and
   (6,0)->(7.5,1)) is even. *)
Theorem spectre_pocket_not_in_ring : ~ point_in_ring spectre_pocket_pt spectre_ring.
Proof.
  unfold point_in_ring, spectre_ring. cbn [ring_edges].
  apply ray_parity_even_not_odd.
  apply rpe_skip; [ spec_no_cross | ].   (* E1  (0,0)-(2,0)     horizontal *)
  apply rpe_skip; [ spec_no_cross | ].   (* E2  (2,0)-(3.5,1)   intercept 2.75 < 3.5 *)
  apply rpe_cross.                        (* E3  (3.5,1)-(4,0)   down, intercept 3.75: HIT *)
  { unfold edge_crosses_ray, hpt, spectre_pocket_pt; cbn [px py]. right. split; lra. }
  apply rpo_skip; [ spec_no_cross | ].   (* E4  (4,0)-(6,0)     horizontal *)
  apply rpo_cross.                        (* E5  (6,0)-(7.5,1)   up, intercept 6.75: HIT *)
  { unfold edge_crosses_ray, hpt, spectre_pocket_pt; cbn [px py]. left. split; lra. }
  apply rpe_skip; [ spec_no_cross | ].   (* E6  (7.5,1)-(7,2)   above *)
  apply rpe_skip; [ spec_no_cross | ].   (* E7  (7,2)-(5,2)     horizontal *)
  apply rpe_skip; [ spec_no_cross | ].   (* E8  (5,2)-(4.5,3)   above *)
  apply rpe_skip; [ spec_no_cross | ].   (* E9  (4.5,3)-(3,2)   above *)
  apply rpe_skip; [ spec_no_cross | ].   (* E10 (3,2)-(1,2)     horizontal *)
  apply rpe_skip; [ spec_no_cross | ].   (* E11 (1,2)-(0.5,1)   above *)
  apply rpe_skip; [ spec_no_cross | ].   (* E12 (0.5,1)-(-0.5,1) horizontal *)
  apply rpe_skip; [ spec_no_cross | ].   (* E13 (-0.5,1)-(0,0)  intercept -0.25 < 3.5 *)
  apply rpe_nil.
Qed.

(* The Spectre's first in/out ray-parity classification pair: the foot-gap
   point is inside (odd; `SpectreExample`), the bottom reflex-notch point is
   outside (even) -- a hull-interior exterior point no convex polygon presents. *)
Theorem spectre_parity_classification :
  point_in_ring spec_pt spectre_ring
  /\ ~ point_in_ring spectre_pocket_pt spectre_ring.
Proof.
  split; [ apply spectre_point_in_ring | apply spectre_pocket_not_in_ring ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions spectre_ring_simple.
Print Assumptions valid_polygon_spectre.
Print Assumptions spectre_pocket_not_in_ring.
Print Assumptions spectre_parity_classification.
