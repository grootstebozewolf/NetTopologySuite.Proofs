(* ============================================================================
   NetTopologySuite.Proofs.JCTNesting
   ----------------------------------------------------------------------------
   Make `hole_inside_outer` usable with the conditional extract_rings_valid.

   The conditional `extract_rings_valid` / `extract_rings_valid_holes`
   (theories-flocq/OverlayBridge.v) carry `hole_inside_outer` as the per-hole
   nesting obligation, and the corpus has UNCONDITIONAL `hole_inside_outer`
   witnesses for recognized outer shapes (Stage B rectangle, Stage D triangle).
   This file wires the rectangle witness into the general polygon-with-holes
   assembler so that a polygon with a RECTANGULAR outer and holes (each with an
   interior vertex) is provably `valid_polygon` -- the practical box-overlay
   case -- with NO JCT hypothesis.

   The enabler is `FacePolygonHoles.polygon_valid_of_rings`, which accepts an
   ARBITRARY outer ring plus per-hole `hole_inside_outer`; composing it with
   `HoleInsideOuterRect.hole_inside_outer_rect` needs no face-ring-equals-rect
   detour.  Supporting lemma `rect_ring_simple` (axis-aligned box is a simple
   ring) was missing and is proved here.

   The general arbitrary-simple-ring parity theorem
   (`parity_characterises_interior_cont` for `ring_simple`) remains the
   thesis-scale gap; see #188 and EdgeConnectivity.v §5 for the remaining
   named fact.

   Pure R + list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay RingSimple RingExtract
                               RectangleJCT HoleInsideOuterRect FacePolygonHoles.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  An axis-aligned rectangle ring is simple.                               *)
(*                                                                            *)
(* The four edges (bottom, right, top, left) pairwise do not properly cross:   *)
(* adjacent edges meet only at a shared corner (a boundary point, not an       *)
(* interior crossing), and opposite edges are parallel and separated.  Each    *)
(* of the off-diagonal pairs refutes the interior-interior crossing equations  *)
(* by `nra` from x0 < x1, y0 < y1.                                            *)
(* -------------------------------------------------------------------------- *)

Lemma rect_ring_simple : forall x0 y0 x1 y1,
  x0 < x1 -> y0 < y1 -> ring_simple (rect_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 Hx01 Hy01.
  unfold ring_simple. rewrite ring_edges_rect.
  intros e1 e2 H1 H2 Hne.
  cbn [In] in H1, H2.
  destruct H1 as [<- | [<- | [<- | [<- | []]]]];
  destruct H2 as [<- | [<- | [<- | [<- | []]]]];
    first
      [ exfalso; apply Hne; reflexivity
      | intros (t & s & Ht & Hs & Hx & Hy);
        cbn [fst snd px py] in *; nra ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Usability headline: a rectangular-outer polygon with nested holes is    *)
(* a valid_polygon, unconditionally.                                          *)
(*                                                                            *)
(* Each hole must be a well-formed ring (closed / simple / min-points) with at *)
(* least one vertex inside the open-on-the-right box -- exactly the           *)
(* hypothesis `hole_inside_outer_rect` consumes.  This discharges the          *)
(* `hole_inside_outer` nesting obligation that the conditional extractor       *)
(* carries, for the box-outer case, with no JCT seam.                          *)
(* -------------------------------------------------------------------------- *)

Theorem valid_polygon_rect_outer :
  forall (x0 y0 x1 y1 : R) (holes : list Ring),
    x0 < x1 -> y0 < y1 ->
    (forall h, In h holes ->
       ring_closed h /\ ring_simple h /\ ring_has_minimum_points h /\
       (exists p, In p h /\ y0 < py p < y1 /\ x0 <= px p < x1)) ->
    valid_polygon (mkPolygon (rect_ring x0 y0 x1 y1) holes).
Proof.
  intros x0 y0 x1 y1 holes Hx01 Hy01 Hholes.
  apply polygon_valid_of_rings.
  - apply rect_ring_closed.
  - apply rect_ring_simple; assumption.
  - apply rect_ring_min_points.
  - intros h Hh.
    destruct (Hholes h Hh) as (Hc & Hs & Hm & p & Hin & Hpy & Hpx).
    split; [ exact Hc | ]. split; [ exact Hs | ]. split; [ exact Hm | ].
    apply (hole_inside_outer_rect x0 y0 x1 y1 h p Hx01 Hy01 Hin Hpy Hpx).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure R + list combinatorics; allowlist axioms only.           *)
(* (A concrete valid box-with-hole instance is exercised by                    *)
(*  theories/TriangleValidPolygon.v's worked polygon-with-hole.)               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions rect_ring_simple.
Print Assumptions valid_polygon_rect_outer.
