(* ============================================================================
   NetTopologySuite.Proofs.HexagonNesting
   ----------------------------------------------------------------------------
   Stage C of the hole_inside_outer programme: a second concrete convex
   instance beyond the diamond -- a convex HEXAGON.

   Rectangle (Stage B), triangle (Stage D), and the diamond
   (HoleInsideOuterConvexExample.v) are already Qed.  The GENERAL convex-n-gon
   parity needs the "convex-chain monotonicity" lemma (a rightward ray from an
   interior point crosses exactly one of n arbitrary slanted edges) which is
   substantial and deliberately not attempted.  This file closes a concrete
   convex 6-gon UNCONDITIONALLY, exactly the diamond's route: `point_in_ring`
   by direct ray-parity edge enumeration, then `hole_inside_outer`, then a
   `valid_polygon` capstone via `polygon_valid_of_rings`.

   Integer coordinates (a *regular* hexagon has sqrt-3 coordinates that fight
   `lra`; convexity with rational vertices is all that is needed).  The vertex
   cycle starts at the single ray-crossed edge, so the parity proof is
   `rpo_cross` then `rpe_skip` x5 -- the diamond's shape.

   Pure `R`; three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia.
From NTS.Proofs Require Import Distance Overlay FacePolygonHoles.

Import ListNotations.
Open Scope R_scope.

(* A CCW convex hexagon, integer coordinates, vertex heights {0,2,4}.  The
   cycle starts at (3,0) so the single edge crossed by the rightward ray from
   (2,1) -- namely (3,0)-(4,2) -- is FIRST. *)
Definition hex_ring : Ring :=
  [ mkPoint 3 0 ; mkPoint 4 2 ; mkPoint 3 4 ; mkPoint 1 4
  ; mkPoint 0 2 ; mkPoint 1 0 ; mkPoint 3 0 ].

(* Interior point; y = 1 avoids every vertex height. *)
Definition hex_ctr : Point := mkPoint 2 1.

(* -------------------------------------------------------------------------- *)
(* §1  point_in_ring by ray-parity enumeration (one edge crossed -> odd).      *)
(* -------------------------------------------------------------------------- *)

Lemma hex_point_in_ring : point_in_ring hex_ctr hex_ring.
Proof.
  unfold point_in_ring, hex_ring, hex_ctr. cbn [ring_edges].
  (* edge (3,0)-(4,2): crossed; x-intercept at y=1 is 3.5 > 2 *)
  apply rpo_cross.
  { unfold edge_crosses_ray. cbn [px py]. left. split; lra. }
  (* edge (4,2)-(3,4): y=1 below both -> not crossed *)
  apply rpe_skip.
  { unfold edge_crosses_ray. cbn [px py]. intros [[H _] | [H _]]; lra. }
  (* edge (3,4)-(1,4): horizontal at y=4 -> not crossed *)
  apply rpe_skip.
  { unfold edge_crosses_ray. cbn [px py]. intros [[H _] | [H _]]; lra. }
  (* edge (1,4)-(0,2): y=1 below -> not crossed *)
  apply rpe_skip.
  { unfold edge_crosses_ray. cbn [px py]. intros [[H _] | [H _]]; lra. }
  (* edge (0,2)-(1,0): y-band hits but x-intercept 0.5 < 2 -> not crossed *)
  apply rpe_skip.
  { unfold edge_crosses_ray. cbn [px py]. intros [[H _] | [_ Hx]].
    - lra.
    - revert Hx. lra. }
  (* edge (1,0)-(3,0): horizontal at y=0 -> not crossed *)
  apply rpe_skip.
  { unfold edge_crosses_ray. cbn [px py]. intros [[H _] | [H _]]; lra. }
  apply rpe_nil.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Structural facts: closed, >= 4 vertices, simple.                        *)
(* -------------------------------------------------------------------------- *)

Lemma hex_ring_closed : ring_closed hex_ring.
Proof.
  exists (mkPoint 3 0),
    [ mkPoint 4 2 ; mkPoint 3 4 ; mkPoint 1 4 ; mkPoint 0 2 ; mkPoint 1 0 ].
  reflexivity.
Qed.

Lemma hex_ring_min_points : ring_has_minimum_points hex_ring.
Proof. unfold ring_has_minimum_points, hex_ring; cbn [length]; lia. Qed.

Lemma hex_ring_simple : ring_simple hex_ring.
Proof.
  unfold ring_simple, hex_ring. cbn [ring_edges].
  intros e1 e2 H1 H2 Hne. cbn [In] in H1, H2.
  destruct H1 as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
  destruct H2 as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    first
      [ exfalso; apply Hne; reflexivity
      | intros (t & s & Ht & Hs & Hx & Hy); cbn [fst snd px py] in *; nra ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  hole_inside_outer + the valid_polygon capstone.                         *)
(* -------------------------------------------------------------------------- *)

(* A small closed triangular hole carrying the interior point (2,1) as a
   vertex (all three vertices sit inside the hexagon). *)
Definition hole_hex : Ring :=
  [ mkPoint 2 1 ; mkPoint 2 (3/2) ; mkPoint (5/2) 1 ; mkPoint 2 1 ].

Theorem hole_inside_outer_hexagon : hole_inside_outer hex_ring hole_hex.
Proof.
  exists hex_ctr. split.
  - unfold hole_hex, hex_ctr. cbn [In]. left. reflexivity.
  - exact hex_point_in_ring.
Qed.

Lemma hole_hex_closed : ring_closed hole_hex.
Proof.
  exists (mkPoint 2 1), [ mkPoint 2 (3/2) ; mkPoint (5/2) 1 ]. reflexivity.
Qed.

Lemma hole_hex_min_points : ring_has_minimum_points hole_hex.
Proof. unfold ring_has_minimum_points, hole_hex; cbn [length]; lia. Qed.

Lemma hole_hex_simple : ring_simple hole_hex.
Proof.
  unfold ring_simple, hole_hex. cbn [ring_edges].
  intros e1 e2 H1 H2 Hne. cbn [In] in H1, H2.
  destruct H1 as [<- | [<- | [<- | []]]];
  destruct H2 as [<- | [<- | [<- | []]]];
    first
      [ exfalso; apply Hne; reflexivity
      | intros (t & s & Ht & Hs & Hx & Hy); cbn [fst snd px py] in *; nra ].
Qed.

Theorem valid_polygon_hexagon_with_hole :
  valid_polygon (mkPolygon hex_ring [hole_hex]).
Proof.
  apply polygon_valid_of_rings.
  - apply hex_ring_closed.
  - apply hex_ring_simple.
  - apply hex_ring_min_points.
  - intros h Hh. cbn [In] in Hh. destruct Hh as [<- | []].
    split; [ apply hole_hex_closed | ].
    split; [ apply hole_hex_simple | ].
    split; [ apply hole_hex_min_points | ].
    exact hole_inside_outer_hexagon.
Qed.

(* Named constant for downstream reuse (e.g. `In h (hole_rings hexagon_with_hole_example)`). *)
Definition hexagon_with_hole_example : Polygon := mkPolygon hex_ring [hole_hex].

Theorem hexagon_with_hole_example_valid :
  valid_polygon hexagon_with_hole_example.
Proof. exact valid_polygon_hexagon_with_hole. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hex_point_in_ring.
Print Assumptions hex_ring_simple.
Print Assumptions hole_inside_outer_hexagon.
Print Assumptions valid_polygon_hexagon_with_hole.
