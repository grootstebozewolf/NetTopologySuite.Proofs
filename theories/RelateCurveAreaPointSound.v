(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveAreaPointSound
   ----------------------------------------------------------------------------
   Issue #67 (curve→matrix soundness seed): the chord-rectangle curve geometry
   CONTAINS every strictly-interior point — the first genuine curve-polygon×point
   soundness claim, transporting S4's rectangle Contains fact onto the linearised
   curve geometry.

   Two steps, built on the ray-parity foundation (`RayParityDegenerate.v`) and
   the S12b point-set bridge (`RelateCurveAreaPoint.v`):

     1. `point_in_ring_chord_rect_iff` — the linearised chord ring
        `chord_approx_ring (rect_curve_ring x0 y0 x1 y1) n` has the SAME
        point-in-ring as the Phase-3 rectangle `rect_ring x0 y0 x1 y1`.  The
        chord ring carries three degenerate `(v,v)` join edges; each is
        parity-neutral (`ray_parity_zero_edge_irrelevant`), so the two rings
        agree.  n-independent (every segment is a chord).

     2. `strict_interior_in_rect_curve_{polygon,geometry}` — compose with S4's
        `strict_interior_point_in_ring` and the S12b bridge to land Contains on
        the curve polygon and (via `point_set`) the curve geometry.

   Honest scope: axis-aligned chord rectangle, no holes, no arcs in the outer
   ring (the n-independent case).  Arc outer rings and the matrix-fill side
   remain S13+.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Setoid.
From NTS.Proofs Require Import Distance Overlay CurveGeometry RectangleJCT
  RelateAreaPoint RelateCurveAreaPoint RayParityDegenerate.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Edge list of the linearised chord rectangle (n-independent).           *)
(*                                                                            *)
(* Four chords, each linearising to [start; end], so the ring is the 8-vertex *)
(* list with a duplicate at every join; `ring_edges` gives four real edges    *)
(* interleaved with three degenerate `(v,v)` join edges.                      *)
(* -------------------------------------------------------------------------- *)

Lemma ring_edges_chord_rect :
  forall x0 y0 x1 y1 n,
    ring_edges (chord_approx_ring (rect_curve_ring x0 y0 x1 y1) n)
    = [ (mkPoint x0 y0, mkPoint x1 y0)
      ; (mkPoint x1 y0, mkPoint x1 y0)
      ; (mkPoint x1 y0, mkPoint x1 y1)
      ; (mkPoint x1 y1, mkPoint x1 y1)
      ; (mkPoint x1 y1, mkPoint x0 y1)
      ; (mkPoint x0 y1, mkPoint x0 y1)
      ; (mkPoint x0 y1, mkPoint x0 y0) ].
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The chord ring and the Phase-3 rectangle ring agree on point-in-ring.  *)
(*                                                                            *)
(* Strip the three `(v,v)` join edges one at a time; each is parity-neutral.  *)
(* -------------------------------------------------------------------------- *)

Lemma point_in_ring_chord_rect_iff :
  forall x0 y0 x1 y1 n p,
    point_in_ring p (chord_approx_ring (rect_curve_ring x0 y0 x1 y1) n)
    <-> point_in_ring p (rect_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 n p. unfold point_in_ring.
  rewrite ring_edges_chord_rect, ring_edges_rect.
  (* remove (x1 y0, x1 y0) *)
  transitivity (ray_parity_odd p
    [ (mkPoint x0 y0, mkPoint x1 y0)
    ; (mkPoint x1 y0, mkPoint x1 y1)
    ; (mkPoint x1 y1, mkPoint x1 y1)
    ; (mkPoint x1 y1, mkPoint x0 y1)
    ; (mkPoint x0 y1, mkPoint x0 y1)
    ; (mkPoint x0 y1, mkPoint x0 y0) ]).
  { exact (proj1 (ray_parity_zero_edge_irrelevant p (mkPoint x1 y0)
            [ (mkPoint x0 y0, mkPoint x1 y0) ]
            [ (mkPoint x1 y0, mkPoint x1 y1)
            ; (mkPoint x1 y1, mkPoint x1 y1)
            ; (mkPoint x1 y1, mkPoint x0 y1)
            ; (mkPoint x0 y1, mkPoint x0 y1)
            ; (mkPoint x0 y1, mkPoint x0 y0) ])). }
  (* remove (x1 y1, x1 y1) *)
  transitivity (ray_parity_odd p
    [ (mkPoint x0 y0, mkPoint x1 y0)
    ; (mkPoint x1 y0, mkPoint x1 y1)
    ; (mkPoint x1 y1, mkPoint x0 y1)
    ; (mkPoint x0 y1, mkPoint x0 y1)
    ; (mkPoint x0 y1, mkPoint x0 y0) ]).
  { exact (proj1 (ray_parity_zero_edge_irrelevant p (mkPoint x1 y1)
            [ (mkPoint x0 y0, mkPoint x1 y0)
            ; (mkPoint x1 y0, mkPoint x1 y1) ]
            [ (mkPoint x1 y1, mkPoint x0 y1)
            ; (mkPoint x0 y1, mkPoint x0 y1)
            ; (mkPoint x0 y1, mkPoint x0 y0) ])). }
  (* remove (x0 y1, x0 y1) *)
  exact (proj1 (ray_parity_zero_edge_irrelevant p (mkPoint x0 y1)
            [ (mkPoint x0 y0, mkPoint x1 y0)
            ; (mkPoint x1 y0, mkPoint x1 y1)
            ; (mkPoint x1 y1, mkPoint x0 y1) ]
            [ (mkPoint x0 y1, mkPoint x0 y0) ])).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Contains soundness: strict interior ⇒ in the curve polygon / geometry.  *)
(* -------------------------------------------------------------------------- *)

Lemma strict_interior_in_rect_curve_polygon :
  forall x0 y0 x1 y1 n p,
    x0 < x1 -> y0 < y1 ->
    point_strictly_in_open_rect x0 y0 x1 y1 p ->
    point_in_rect_curve_polygon x0 y0 x1 y1 n p.
Proof.
  intros x0 y0 x1 y1 n p Hx Hy Hstrict.
  unfold point_in_rect_curve_polygon, point_in_polygon. simpl.
  split.
  - apply (proj2 (point_in_ring_chord_rect_iff x0 y0 x1 y1 n p)).
    exact (strict_interior_point_in_ring x0 y0 x1 y1 p Hx Hy Hstrict).
  - intros h Hin. destruct Hin.
Qed.

Lemma strict_interior_in_rect_curve_geometry :
  forall x0 y0 x1 y1 n p,
    x0 < x1 -> y0 < y1 ->
    point_strictly_in_open_rect x0 y0 x1 y1 p ->
    point_in_rect_curve_geometry x0 y0 x1 y1 n p.
Proof.
  intros x0 y0 x1 y1 n p Hx Hy Hstrict.
  apply (proj2 (point_in_rect_curve_geometry_iff_polygon x0 y0 x1 y1 n p)).
  exact (strict_interior_in_rect_curve_polygon x0 y0 x1 y1 n p Hx Hy Hstrict).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions point_in_ring_chord_rect_iff.
Print Assumptions strict_interior_in_rect_curve_polygon.
Print Assumptions strict_interior_in_rect_curve_geometry.
