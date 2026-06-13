(* ============================================================================
   NetTopologySuite.Proofs.HatValidPolygon
   ----------------------------------------------------------------------------
   The "hat" aperiodic einstein monotile is a `valid_polygon`.

   `HatMonotile.v` left `ring_simple hat_ring` open -- the ~78 edge-pair,
   non-convex, sqrt-3 case-analysis (the same effort deferred for the Spectre).
   This file closes it: the crossing system for each edge pair is LINEAR in the
   two segment parameters once the coordinates are constants, so after reducing
   `fst`/`snd`/`px`/`py` and supplying `sqrt 3 * sqrt 3 = 3`, a single `nra`
   discharges every one of the off-diagonal pairs (whole proof ~2 s).

   With simplicity in hand, the einstein tile assembles into a `valid_polygon`
   two ways:
     - `valid_polygon_hat` : the hat alone (no holes) is a valid polygon;
     - `valid_polygon_box_with_hat_hole` : a rectangle with the hat punched out
       as a hole is valid -- exercising `JCTNesting.valid_polygon_rect_outer`
       with the einstein monotile as the hole.

   Pure-R; three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Overlay RingSimple FacePolygonHoles
                               RectangleJCT JCTNesting
                               HatMonotile HatNesting.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The hat ring is simple.                                                 *)
(*                                                                            *)
(* No two distinct edges of the 13-gon cross at an interior point.  Each       *)
(* edge-pair crossing system `(1-t)P0 + tP1 = (1-s)Q0 + sQ1` is linear in      *)
(* (t,s); with `sqrt 3 * sqrt 3 = 3` available, `nra` refutes every            *)
(* off-diagonal pair (the diagonal `e <> e` cases close by `Hne`).             *)
(* -------------------------------------------------------------------------- *)

Theorem hat_ring_simple : ring_simple hat_ring.
Proof.
  unfold ring_simple.
  assert (Hr3 : 0 < sqrt 3) by (apply sqrt_lt_R0; lra).
  assert (Hsq : sqrt 3 * sqrt 3 = 3) by (apply sqrt_sqrt; lra).
  intros e1 e2 H1 H2 Hne.
  unfold hat_ring in H1, H2. cbn [ring_edges] in H1, H2. cbn [In] in H1, H2.
  destruct H1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
  destruct H2 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
    try (exfalso; apply Hne; reflexivity);
    intros (t & s & Ht & Hs & Hx & Hy);
    unfold hexPt in Hx, Hy; cbn [fst snd px py] in Hx, Hy; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The hat is a valid polygon.                                             *)
(* -------------------------------------------------------------------------- *)

Theorem valid_polygon_hat : valid_polygon (mkPolygon hat_ring []).
Proof.
  apply polygon_valid_of_rings.
  - apply hat_ring_closed.
  - apply hat_ring_simple.
  - apply hat_ring_min_points.
  - intros h [].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  A rectangle with the einstein monotile punched out as a hole is valid.  *)
(* Showcases JCTNesting.valid_polygon_rect_outer with the hat as the hole      *)
(* (the bounding box (-1,-1)-(8,3) contains the whole hat).                    *)
(* -------------------------------------------------------------------------- *)

Theorem valid_polygon_box_with_hat_hole :
  valid_polygon (mkPolygon (rect_ring (-1) (-1) 8 3) [hat_ring]).
Proof.
  pose proof sqrt3_bounds as [Hlo Hhi].
  apply valid_polygon_rect_outer; [ lra | lra | ].
  intros h Hh. cbn [In] in Hh. destruct Hh as [<- | []].
  split; [ apply hat_ring_closed | ].
  split; [ apply hat_ring_simple | ].
  split; [ apply hat_ring_min_points | ].
  exists (hexPt 3 1).
  split.
  - unfold hat_ring; cbn [In]; right; right; left; reflexivity.
  - unfold hexPt; cbn [px py]; split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hat_ring_simple.
Print Assumptions valid_polygon_hat.
Print Assumptions valid_polygon_box_with_hat_hole.
