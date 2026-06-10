(* ============================================================================
   NetTopologySuite.Proofs.JCTCornerBox
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-4: THE CORNER BOXES.  Rung 4b-3's per-edge
   dispatch `corner_edge_clear` quantifies over the WHOLE abscissa interval
   [px v - 2*delta, px v - delta/2] -- not just the drop line -- so its
   fold yields a skeleton-free RECTANGLE beside the corner:

       [px v - 2*delta, px v - delta/2] x [py v - eps, py v + eps].

   Inside a free rectangle, any two points connect by one vertical and one
   horizontal segment (`box_connected_of_clear`, generic).  The corner
   boxes therefore absorb at once all the glue the traversal's corner
   composites need: the corner drop, the rejoin jogs onto the next edge's
   corridor, and the transfer between passage destinations and tip
   crossings -- every such move happens inside a box or along the under-
   tip band, both already free.

   The mirror kit then turns the single west-bottom box into all four:

     corner_box_clear          west of a BOTTOM vertex   (rung 4b-3 fold)
     corner_box_east_clear     east of a bottom vertex   (xmir)
     corner_box_top_clear      west of a TOP vertex      (ymir)
     corner_box_east_top_clear east of a top vertex      (xmir o ymir)

   Hypotheses are rung 4b-3's: tautness plus the horizontal-incident
   direction at the corner (horizontal edges at the vertex extend away
   from the box side); under the traversal's global no-horizontal-edges
   simplification these are vacuous.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport.
From NTS.Proofs Require Import JCTHalfOpenParity JCTGenericStability JCTLevelJump.
From NTS.Proofs Require Import JCTTrappedHalf JCTSeamAssembly JCTEscapeDescent.
From NTS.Proofs Require Import JCTEastApproach JCTCorridor JCTWalkKit JCTWalkStep.
From NTS.Proofs Require Import JCTTautClearance JCTWallClear JCTCornerSector.
From NTS.Proofs Require Import JCTCornerClear JCTMirrorKit JCTTopPassage.
From NTS.Proofs Require Import JCTPassageKit JCTTipCrossing.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  Generic: a skeleton-free rectangle is path-connected.
   --------------------------------------------------------------------------- *)

Lemma box_connected_of_clear : forall (r : Ring) (xlo xhi ylo yhi : R),
  (forall x y, xlo <= x <= xhi -> ylo <= y <= yhi ->
     ~ ring_image r (mkPoint x y)) ->
  forall x1 y1 x2 y2,
    xlo <= x1 <= xhi -> ylo <= y1 <= yhi ->
    xlo <= x2 <= xhi -> ylo <= y2 <= yhi ->
    connected_in_complement_cont r (mkPoint x1 y1) (mkPoint x2 y2).
Proof.
  intros r xlo xhi ylo yhi Hfree x1 y1 x2 y2 Hx1 Hy1 Hx2 Hy2.
  assert (Hv : connected_in_complement_cont r
                 (mkPoint x1 y1) (mkPoint x1 y2)).
  { apply vertical_connected.
    intros y Hy.
    assert (Hlo : ylo <= Rmin y1 y2) by (apply Rmin_glb; lra).
    assert (Hhi : Rmax y1 y2 <= yhi) by (apply Rmax_lub; lra).
    apply Hfree; lra. }
  assert (Hh : connected_in_complement_cont r
                 (mkPoint x1 y2) (mkPoint x2 y2)).
  { apply horizontal_connected.
    intros x Hx.
    assert (Hlo : xlo <= Rmin x1 x2) by (apply Rmin_glb; lra).
    assert (Hhi : Rmax x1 x2 <= xhi) by (apply Rmax_lub; lra).
    apply Hfree; lra. }
  exact (connected_in_complement_cont_trans r
           (mkPoint x1 y1) (mkPoint x1 y2) (mkPoint x2 y2) Hv Hh).
Qed.

(* ---------------------------------------------------------------------------
   §1  The base box: west of a bottom vertex (rung 4b-3's fold, re-exposed).
   --------------------------------------------------------------------------- *)

Theorem corner_box_clear : forall (r : Ring) (e1 : Edge) (v w : Point),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  (forall g, In g (ring_edges r) ->
     py (fst g) = py (snd g) -> fst g = v \/ snd g = v ->
     px v <= px (fst g) /\ px v <= px (snd g)) ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    forall x y,
      px v - 2 * delta <= x <= px v - delta / 2 ->
      py v - eps <= y <= py v + eps ->
      ~ ring_image r (mkPoint x y).
Proof.
  intros r e1 v w Htaut Hin1 Hor Hvw Hez.
  destruct (corner_fold
              (fun g delta eps =>
                 forall xd y,
                   px v - 2 * delta <= xd <= px v - delta / 2 ->
                   py v - eps <= y <= py v + eps ->
                   ~ (exists s : R, 0 <= s <= 1 /\
                        xd = (1 - s) * px (fst g) + s * px (snd g) /\
                        y = (1 - s) * py (fst g) + s * py (snd g)))
              (ring_edges r)) as [d0 [Hd0 Hstage]].
  { intros g Hing.
    exact (corner_edge_clear r e1 g v w Htaut Hin1 Hing Hor Hvw
             (Hez g Hing)). }
  exists d0. split; [ exact Hd0 | ].
  intros delta Hd.
  destruct (Hstage delta Hd) as [e0 [He0 Hball]].
  exists e0. split; [ exact He0 | ].
  intros eps He x y Hx Hy Himg.
  destruct Himg as [g [s [Hing [Hs [Hxs Hys]]]]].
  cbn [px py] in Hxs, Hys.
  apply (Hball eps ltac:(lra) g Hing x y Hx Hy).
  exists s. repeat split; try assumption; lra.
Qed.

(* ---------------------------------------------------------------------------
   §2  The three mirrored boxes.
   --------------------------------------------------------------------------- *)

(* East of a bottom vertex (x-flip): horizontal incidents extend WEST. *)
Theorem corner_box_east_clear : forall (r : Ring) (e1 : Edge) (v w : Point),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  (forall g, In g (ring_edges r) ->
     py (fst g) = py (snd g) -> fst g = v \/ snd g = v ->
     px (fst g) <= px v /\ px (snd g) <= px v) ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    forall x y,
      px v + delta / 2 <= x <= px v + 2 * delta ->
      py v - eps <= y <= py v + eps ->
      ~ ring_image r (mkPoint x y).
Proof.
  intros r e1 v w Htaut Hin Hor Hvw Hez.
  destruct e1 as [ea eb].
  set (r' := map xmir r).
  set (e1' := (xmir ea, xmir eb)).
  assert (Htaut' : ring_taut r') by (apply ring_taut_xmir; exact Htaut).
  assert (Hin' : In e1' (ring_edges r')).
  { unfold r'. rewrite ring_edges_map.
    exact (in_map (fun e => (xmir (fst e), xmir (snd e)))
             (ring_edges r) (ea, eb) Hin). }
  assert (Hor' : e1' = (xmir v, xmir w) \/ e1' = (xmir w, xmir v)).
  { destruct Hor as [He | He]; inversion He; subst; [ left | right ];
      reflexivity. }
  assert (Hez' : forall g', In g' (ring_edges r') ->
            py (fst g') = py (snd g') -> fst g' = xmir v \/ snd g' = xmir v ->
            px (xmir v) <= px (fst g') /\ px (xmir v) <= px (snd g')).
  { intros g' Hing' Hflat' Hinc'.
    unfold r' in Hing'. rewrite ring_edges_map in Hing'.
    apply in_map_iff in Hing'. destruct Hing' as [g [Hgeq Hing]].
    subst g'. cbn [fst snd] in *.
    assert (Hinc : fst g = v \/ snd g = v).
    { destruct Hinc' as [H | H]; [ left | right ]; apply xmir_inj; exact H. }
    assert (Hflat : py (fst g) = py (snd g))
      by (unfold xmir in Hflat'; cbn [py] in Hflat'; lra).
    destruct (Hez g Hing Hflat Hinc) as [HA HB].
    unfold xmir; cbn [px]. lra. }
  destruct (corner_box_clear r' e1' (xmir v) (xmir w) Htaut' Hin' Hor'
              ltac:(unfold xmir; cbn [py]; lra) Hez')
    as [delta0 [Hd0 Hstage]].
  exists delta0. split; [ exact Hd0 | ].
  intros delta Hd.
  destruct (Hstage delta Hd) as [eps0 [He0 Hfree]].
  exists eps0. split; [ exact He0 | ].
  intros eps He x y Hx Hy Himg.
  apply (Hfree eps He (- x) y).
  - unfold xmir; cbn [px]. lra.
  - unfold xmir; cbn [py]. lra.
  - change (mkPoint (- x) y) with (xmir (mkPoint x y)).
    apply (ring_image_xmir r (mkPoint x y)). exact Himg.
Qed.

(* West of a TOP vertex (y-flip): horizontal incidents extend EAST. *)
Theorem corner_box_top_clear : forall (r : Ring) (e1 : Edge) (v u : Point),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, u) \/ e1 = (u, v) ->
  py v < py u ->
  (forall g, In g (ring_edges r) ->
     py (fst g) = py (snd g) -> fst g = u \/ snd g = u ->
     px u <= px (fst g) /\ px u <= px (snd g)) ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    forall x y,
      px u - 2 * delta <= x <= px u - delta / 2 ->
      py u - eps <= y <= py u + eps ->
      ~ ring_image r (mkPoint x y).
Proof.
  intros r e1 v u Htaut Hin Hor Hvu Hez.
  destruct e1 as [ea eb].
  set (r' := map ymir r).
  set (e1' := (ymir ea, ymir eb)).
  assert (Htaut' : ring_taut r') by (apply ring_taut_ymir; exact Htaut).
  assert (Hin' : In e1' (ring_edges r')).
  { unfold r'. rewrite ring_edges_map.
    exact (in_map (fun e => (ymir (fst e), ymir (snd e)))
             (ring_edges r) (ea, eb) Hin). }
  assert (Hor' : e1' = (ymir u, ymir v) \/ e1' = (ymir v, ymir u)).
  { destruct Hor as [He | He]; inversion He; subst; [ right | left ];
      reflexivity. }
  assert (Hez' : forall g', In g' (ring_edges r') ->
            py (fst g') = py (snd g') -> fst g' = ymir u \/ snd g' = ymir u ->
            px (ymir u) <= px (fst g') /\ px (ymir u) <= px (snd g')).
  { intros g' Hing' Hflat' Hinc'.
    unfold r' in Hing'. rewrite ring_edges_map in Hing'.
    apply in_map_iff in Hing'. destruct Hing' as [g [Hgeq Hing]].
    subst g'. cbn [fst snd] in *.
    assert (Hinc : fst g = u \/ snd g = u).
    { destruct Hinc' as [H | H]; [ left | right ]; apply ymir_inj; exact H. }
    assert (Hflat : py (fst g) = py (snd g))
      by (unfold ymir in Hflat'; cbn [py] in Hflat'; lra).
    destruct (Hez g Hing Hflat Hinc) as [HA HB].
    unfold ymir; cbn [px]. lra. }
  destruct (corner_box_clear r' e1' (ymir u) (ymir v) Htaut' Hin' Hor'
              ltac:(unfold ymir; cbn [py]; lra) Hez')
    as [delta0 [Hd0 Hstage]].
  exists delta0. split; [ exact Hd0 | ].
  intros delta Hd.
  destruct (Hstage delta Hd) as [eps0 [He0 Hfree]].
  exists eps0. split; [ exact He0 | ].
  intros eps He x y Hx Hy Himg.
  apply (Hfree eps He x (- y)).
  - unfold ymir; cbn [px]. lra.
  - unfold ymir; cbn [py]. lra.
  - change (mkPoint x (- y)) with (ymir (mkPoint x y)).
    apply (ring_image_ymir r (mkPoint x y)). exact Himg.
Qed.

(* East of a TOP vertex (both flips): horizontal incidents extend WEST. *)
Theorem corner_box_east_top_clear : forall (r : Ring) (e1 : Edge)
                                           (v u : Point),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, u) \/ e1 = (u, v) ->
  py v < py u ->
  (forall g, In g (ring_edges r) ->
     py (fst g) = py (snd g) -> fst g = u \/ snd g = u ->
     px (fst g) <= px u /\ px (snd g) <= px u) ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    forall x y,
      px u + delta / 2 <= x <= px u + 2 * delta ->
      py u - eps <= y <= py u + eps ->
      ~ ring_image r (mkPoint x y).
Proof.
  intros r e1 v u Htaut Hin Hor Hvu Hez.
  destruct e1 as [ea eb].
  set (r' := map xmir r).
  set (e1' := (xmir ea, xmir eb)).
  assert (Htaut' : ring_taut r') by (apply ring_taut_xmir; exact Htaut).
  assert (Hin' : In e1' (ring_edges r')).
  { unfold r'. rewrite ring_edges_map.
    exact (in_map (fun e => (xmir (fst e), xmir (snd e)))
             (ring_edges r) (ea, eb) Hin). }
  assert (Hor' : e1' = (xmir v, xmir u) \/ e1' = (xmir u, xmir v)).
  { destruct Hor as [He | He]; inversion He; subst; [ left | right ];
      reflexivity. }
  assert (Hez' : forall g', In g' (ring_edges r') ->
            py (fst g') = py (snd g') -> fst g' = xmir u \/ snd g' = xmir u ->
            px (xmir u) <= px (fst g') /\ px (xmir u) <= px (snd g')).
  { intros g' Hing' Hflat' Hinc'.
    unfold r' in Hing'. rewrite ring_edges_map in Hing'.
    apply in_map_iff in Hing'. destruct Hing' as [g [Hgeq Hing]].
    subst g'. cbn [fst snd] in *.
    assert (Hinc : fst g = u \/ snd g = u).
    { destruct Hinc' as [H | H]; [ left | right ]; apply xmir_inj; exact H. }
    assert (Hflat : py (fst g) = py (snd g))
      by (unfold xmir in Hflat'; cbn [py] in Hflat'; lra).
    destruct (Hez g Hing Hflat Hinc) as [HA HB].
    unfold xmir; cbn [px]. lra. }
  destruct (corner_box_top_clear r' e1' (xmir v) (xmir u) Htaut' Hin' Hor'
              ltac:(unfold xmir; cbn [py]; lra) Hez')
    as [delta0 [Hd0 Hstage]].
  exists delta0. split; [ exact Hd0 | ].
  intros delta Hd.
  destruct (Hstage delta Hd) as [eps0 [He0 Hfree]].
  exists eps0. split; [ exact He0 | ].
  intros eps He x y Hx Hy Himg.
  apply (Hfree eps He (- x) y).
  - unfold xmir; cbn [px]. lra.
  - unfold xmir; cbn [py]. lra.
  - change (mkPoint (- x) y) with (xmir (mkPoint x y)).
    apply (ring_image_xmir r (mkPoint x y)). exact Himg.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions box_connected_of_clear.
Print Assumptions corner_box_clear.
Print Assumptions corner_box_east_clear.
Print Assumptions corner_box_east_top_clear.
