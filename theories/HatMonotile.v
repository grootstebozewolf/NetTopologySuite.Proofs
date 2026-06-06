(* ============================================================================
   NetTopologySuite.Proofs.HatMonotile
   ----------------------------------------------------------------------------
   The "hat" aperiodic monotile (Smith, Myers, Kaplan, Goodman-Strauss, 2023)
   as a concrete ring in the corpus's geometry -- a showcase that the polygon
   machinery built up here can hold famous shapes.

   The hat is a 13-edge non-convex polykite.  Its vertices live on the
   triangular ("hex") lattice; we map lattice coordinates to the plane with the
   standard shear `hexPt x y = (x + y/2, y * sqrt 3 / 2)` (the same convention as
   the discovery paper / hatviz), so the coordinates are EXACT (using `sqrt 3`),
   not approximate.

   The given hex-coordinate vertex list was independently checked (offline) to be
   a genuine SIMPLE, NON-CONVEX, counter-clockwise 13-gon (no self-intersections;
   4 reflex vertices; edge-length multiset {1, sqrt 3, 2}).  Here we prove the
   structural facts the corpus's `Ring` API supports directly:
     - it is `ring_closed` and has `>= 4` vertices (13 edges);
     - it is genuinely NON-CONVEX: the boundary turn is clockwise at one vertex
       and counter-clockwise at another (witnessed by `Orientation.cross`).

   NOTE on scope.  This formalises the hat as a *shape* (a `Ring` value) and its
   combinatorial/orientation structure.  Its *interior theorem* is NOT in reach
   of the convex separation engine (the hat is non-convex) -- that needs the full
   polygonal JCT (`parity_characterises_interior_cont`).  And aperiodicity is a
   tiling-theoretic property entirely outside this corpus.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Overlay Orientation.
Import ListNotations.

Local Open Scope R_scope.
(* Part of the special-case JCT programme (issue #65): rectangle -> right
   triangle -> arbitrary triangle, plus the hat & Spectre monotile showcases. *)

(* Triangular-lattice point -> plane (the standard hat/hatviz shear). *)
Definition hexPt (x y : R) : Point := mkPoint (x + y / 2) (y * (sqrt 3 / 2)).

(* The hat, as the canonical hex-coordinate vertex cycle (closed). *)
Definition hat_ring : Ring :=
  [ hexPt 0 0
  ; hexPt 2 0
  ; hexPt 3 1
  ; hexPt 4 0
  ; hexPt 6 0
  ; hexPt 7 1
  ; hexPt 6 2
  ; hexPt 4 2
  ; hexPt 3 3
  ; hexPt 2 2
  ; hexPt 0 2
  ; hexPt 0 1
  ; hexPt (-1) 1
  ; hexPt 0 0 ].

(* -------------------------------------------------------------------------- *)
(* Structural facts.                                                          *)
(* -------------------------------------------------------------------------- *)

Lemma hat_ring_has_13_edges : length (ring_edges hat_ring) = 13%nat.
Proof. reflexivity. Qed.

Lemma hat_ring_closed : ring_closed hat_ring.
Proof.
  exists (hexPt 0 0),
    [ hexPt 2 0 ; hexPt 3 1 ; hexPt 4 0 ; hexPt 6 0 ; hexPt 7 1 ; hexPt 6 2
    ; hexPt 4 2 ; hexPt 3 3 ; hexPt 2 2 ; hexPt 0 2 ; hexPt 0 1 ; hexPt (-1) 1 ].
  reflexivity.
Qed.

Lemma hat_ring_min_points : ring_has_minimum_points hat_ring.
Proof. unfold ring_has_minimum_points, hat_ring; cbn [length]; lia. Qed.

(* -------------------------------------------------------------------------- *)
(* Non-convexity: the boundary turns both ways.                                *)
(* `cross A B C` is the signed area of (A,B,C); its sign is the turn direction. *)
(* -------------------------------------------------------------------------- *)

(* A reflex (clockwise) turn at vertex (3,1): cross = -sqrt 3 < 0. *)
Lemma hat_reflex_turn :
  cross (hexPt 2 0) (hexPt 3 1) (hexPt 4 0) < 0.
Proof.
  pose proof (sqrt_lt_R0 3 ltac:(lra)) as Hs3.
  unfold cross, hexPt; cbn [px py]; nra.
Qed.

(* A convex (counter-clockwise) turn at vertex (2,0): cross = +sqrt 3 > 0. *)
Lemma hat_convex_turn :
  0 < cross (hexPt 0 0) (hexPt 2 0) (hexPt 3 1).
Proof.
  pose proof (sqrt_lt_R0 3 ltac:(lra)) as Hs3.
  unfold cross, hexPt; cbn [px py]; nra.
Qed.

(* Hence the hat is genuinely non-convex: the boundary makes both a clockwise
   and a counter-clockwise turn, so no single half-plane orientation contains
   it -- it is not the boundary of a convex region. *)
Theorem hat_non_convex :
  cross (hexPt 2 0) (hexPt 3 1) (hexPt 4 0) < 0
  /\ 0 < cross (hexPt 0 0) (hexPt 2 0) (hexPt 3 1).
Proof. split; [ apply hat_reflex_turn | apply hat_convex_turn ]. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hat_ring_closed.
Print Assumptions hat_non_convex.
