(* ============================================================================
   NetTopologySuite.Proofs.JCTPassageKit
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-2: THE FOUR-ORIENTATION PASSAGE KIT.

   The boundary-hugging walk rounds corners in four orientations: west of
   the wall under the bottom vertex (rung 5a's `corner_passage`), west over
   the top (rung 5c-1's `corner_passage_top`), and the two EAST-side
   passages delivered here through the x-flip.

   The x-flip reverses the eastward ray, so it does NOT transport the ray
   guard -- but it does not need to: the passage destinations are parked at
   LEVEL-FRESH heights (inside a `depth_gap`, no ring vertex at that level
   at all), and a level-fresh point is guarded in every direction
   (`ray_guard_of_fresh`).  So this file first re-assembles the passage
   with the freshness exposed (`corner_passage_fresh` -- same proof as
   rung 5a's composition, with the parking margin `depth_gap` folded into
   eps0 explicitly), then pulls it through the mirrors:

     corner_passage_fresh        west side, under the bottom vertex
     corner_passage_top_fresh    west side, over the top   (ymir)
     corner_passage_east         east side, under the bottom (xmir)
     corner_passage_east_top     east side, over the top   (xmir o ymir)

   Each concludes: one complement path from the side-corridor at any
   span-interior height, around the corner, to an off-ring point strictly
   past the corner level, plus LEVEL FRESHNESS of the destination height --
   from which the eastward ray guard follows uniformly.  The corner
   conditions read in original coordinates: `corner_opens_east`(/`_top`)
   for the west-side moves, `corner_opens_west`(/`_top`) -- incident edges
   on the relevant vertical side staying weakly WEST of the carrier -- for
   the east-side moves.

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
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  Level freshness: the direction-free guard.
   --------------------------------------------------------------------------- *)

Lemma fresh_below_level : forall (r : Ring) (y0 eps : R),
  0 < eps < depth_gap y0 r ->
  forall vt, In vt r -> py vt <> y0 - eps.
Proof.
  intros r y0 eps He vt Hin Heq.
  destruct (depth_gap_spec y0 r vt Hin) as [H | H]; lra.
Qed.

Lemma ray_guard_of_fresh : forall (r : Ring) (q : Point),
  (forall vt, In vt r -> py vt <> py q) ->
  ray_avoids_vertices q r.
Proof.
  intros r q Hf v Hin [Heq _]. exact (Hf v Hin Heq).
Qed.

(* ---------------------------------------------------------------------------
   §1  The base move with freshness exposed: rung 5a's composition, with
       the depth_gap parking margin folded into eps0 explicitly.
   --------------------------------------------------------------------------- *)

Theorem corner_passage_fresh : forall (r : Ring) (e1 : Edge) (v w : Point)
                                      (yhi : R),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  py v < yhi ->
  yhi < py w ->
  corner_opens_east r e1 v ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    connected_in_complement_cont r
      (corridor e1 delta yhi)
      (mkPoint (edge_x_at e1 (py v + eps) - delta) (py v - eps)) /\
    ring_complement r (corridor e1 delta yhi) /\
    ring_complement r
      (mkPoint (edge_x_at e1 (py v + eps) - delta) (py v - eps)) /\
    (forall vt, In vt r -> py vt <> py v - eps).
Proof.
  intros r e1 v w yhi Htaut Hin1 Hor Hvw Hlo Hhi Hopen.
  assert (Hnh : py (fst e1) <> py (snd e1))
    by (destruct Hor; subst e1; cbn; lra).
  destruct (wall_corridor_clear_corner r e1 v w yhi Htaut Hin1 Hor Hvw
              ltac:(lra) Hhi Hopen) as [dA [HdA HfreeA]].
  destruct (corner_sector_guarded r e1 v w Htaut Hin1 Hor Hvw
              (opens_east_horizontal r e1 v w Hor Hvw Hopen))
    as [dB [HdB HstageB]].
  exists (Rmin dA dB). split; [ apply Rmin_glb_lt; lra | ].
  intros delta Hd.
  pose proof (Rmin_l dA dB). pose proof (Rmin_r dA dB).
  destruct (HstageB delta ltac:(lra)) as [eB [HeB HsectB]].
  pose proof (depth_gap_pos (py v) r) as Hgp.
  exists (Rmin (Rmin eB (yhi - py v)) (depth_gap (py v) r)).
  split; [ apply Rmin_glb_lt; [ apply Rmin_glb_lt | ]; lra | ].
  intros eps He.
  pose proof (Rmin_l (Rmin eB (yhi - py v)) (depth_gap (py v) r)).
  pose proof (Rmin_r (Rmin eB (yhi - py v)) (depth_gap (py v) r)).
  pose proof (Rmin_l eB (yhi - py v)). pose proof (Rmin_r eB (yhi - py v)).
  destruct (HsectB eps ltac:(lra)) as [Hsect [Hcompl _]].
  assert (Hride : connected_in_complement_cont r
            (corridor e1 delta yhi) (corridor e1 delta (py v + eps))).
  { apply (corridor_connected r e1 (py v + eps) yhi delta Hnh ltac:(lra)).
    intros y Hy. apply (HfreeA delta ltac:(lra)). lra. }
  split; [ | split; [ | split ] ].
  - exact (connected_in_complement_cont_trans r
             (corridor e1 delta yhi)
             (corridor e1 delta (py v + eps))
             (mkPoint (edge_x_at e1 (py v + eps) - delta) (py v - eps))
             Hride Hsect).
  - intro Himg. exact (HfreeA delta ltac:(lra) yhi ltac:(lra) Himg).
  - exact Hcompl.
  - apply (fresh_below_level r (py v) eps). lra.
Qed.

(* ---------------------------------------------------------------------------
   §2  West side, over the top: the y-flip of the fresh move.
   --------------------------------------------------------------------------- *)

Theorem corner_passage_top_fresh : forall (r : Ring) (e1 : Edge)
                                          (v u : Point) (ylo : R),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, u) \/ e1 = (u, v) ->
  py v < py u ->
  py v < ylo ->
  ylo < py u ->
  corner_opens_east_top r e1 u ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    connected_in_complement_cont r
      (corridor e1 delta ylo)
      (mkPoint (edge_x_at e1 (py u - eps) - delta) (py u + eps)) /\
    ring_complement r (corridor e1 delta ylo) /\
    ring_complement r
      (mkPoint (edge_x_at e1 (py u - eps) - delta) (py u + eps)) /\
    (forall vt, In vt r -> py vt <> py u + eps).
Proof.
  intros r e1 v u ylo Htaut Hin Hor Hvu Hlo Hhi Hopen.
  destruct e1 as [ea eb].
  assert (Hnh : py ea <> py eb)
    by (destruct Hor as [He | He]; inversion He; subst; cbn; lra).
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
  assert (Hopen' : corner_opens_east r' e1' (ymir u)).
  { intros g' Hing' Hinc'.
    unfold r' in Hing'. rewrite ring_edges_map in Hing'.
    apply in_map_iff in Hing'. destruct Hing' as [g [Hgeq Hing]].
    subst g'. cbn [fst snd] in *.
    assert (Hinc : fst g = u \/ snd g = u).
    { destruct Hinc' as [H | H]; [ left | right ]; apply ymir_inj; exact H. }
    destruct (Hopen g Hing Hinc) as [HA HB].
    split.
    - intro Hyy.
      assert (Hyy' : py (fst g) <= py u)
        by (unfold ymir in Hyy; cbn [py] in Hyy; lra).
      specialize (HA Hyy').
      unfold e1'.
      replace (py (ymir (fst g))) with (- py (fst g))
        by (unfold ymir; cbn [py]; reflexivity).
      rewrite (edge_x_at_ymir ea eb (py (fst g)) Hnh).
      replace (px (ymir (fst g))) with (px (fst g))
        by (unfold ymir; cbn [px]; reflexivity).
      exact HA.
    - intro Hyy.
      assert (Hyy' : py (snd g) <= py u)
        by (unfold ymir in Hyy; cbn [py] in Hyy; lra).
      specialize (HB Hyy').
      unfold e1'.
      replace (py (ymir (snd g))) with (- py (snd g))
        by (unfold ymir; cbn [py]; reflexivity).
      rewrite (edge_x_at_ymir ea eb (py (snd g)) Hnh).
      replace (px (ymir (snd g))) with (px (snd g))
        by (unfold ymir; cbn [px]; reflexivity).
      exact HB. }
  destruct (corner_passage_fresh r' e1' (ymir u) (ymir v) (- ylo)
              Htaut' Hin' Hor'
              ltac:(unfold ymir; cbn [py]; lra)
              ltac:(unfold ymir; cbn [py]; lra)
              ltac:(unfold ymir; cbn [py]; lra)
              Hopen') as [delta0 [Hd0 Hstage]].
  exists delta0. split; [ exact Hd0 | ]. intros delta Hd.
  destruct (Hstage delta Hd) as [eps0 [He0 Hpass]].
  exists eps0. split; [ exact He0 | ]. intros eps He.
  destruct (Hpass eps He) as [Hconn' [HcA' [HcB' Hfr']]].
  assert (HtopEq : corridor e1' delta (- ylo)
                     = ymir (corridor (ea, eb) delta ylo)).
  { unfold e1', corridor.
    rewrite (edge_x_at_ymir ea eb ylo Hnh).
    unfold ymir; cbn [px py]. reflexivity. }
  assert (HbotEq : mkPoint (edge_x_at e1' (py (ymir u) + eps) - delta)
                           (py (ymir u) - eps)
                 = ymir (mkPoint (edge_x_at (ea, eb) (py u - eps) - delta)
                                 (py u + eps))).
  { unfold e1'.
    replace (py (ymir u) + eps) with (- (py u - eps))
      by (unfold ymir; cbn [py]; ring).
    rewrite (edge_x_at_ymir ea eb (py u - eps) Hnh).
    unfold ymir; cbn [px py]. f_equal. ring. }
  rewrite HtopEq in Hconn', HcA'.
  rewrite HbotEq in Hconn', HcB'.
  split; [ | split; [ | split ] ].
  - exact (connected_ymir_rev r _ _ Hconn').
  - exact (proj1 (ring_complement_ymir r _) HcA').
  - exact (proj1 (ring_complement_ymir r _) HcB').
  - intros vt Hinvt Heq.
    apply (Hfr' (ymir vt)).
    + unfold r'. apply in_map. exact Hinvt.
    + unfold ymir; cbn [py]. lra.
Qed.

(* ---------------------------------------------------------------------------
   §3  East side, under the bottom: the x-flip of the fresh move.
   --------------------------------------------------------------------------- *)

(* The corner condition for an EAST-side descent at the bottom vertex v:
   incident edges reaching weakly above v's level stay weakly WEST of the
   wall's carrier. *)
Definition corner_opens_west (r : Ring) (e1 : Edge) (v : Point) : Prop :=
  forall g, In g (ring_edges r) ->
    fst g = v \/ snd g = v ->
    (py v <= py (fst g) -> px (fst g) <= edge_x_at e1 (py (fst g))) /\
    (py v <= py (snd g) -> px (snd g) <= edge_x_at e1 (py (snd g))).

Theorem corner_passage_east : forall (r : Ring) (e1 : Edge) (v w : Point)
                                     (yhi : R),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  py v < yhi ->
  yhi < py w ->
  corner_opens_west r e1 v ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    connected_in_complement_cont r
      (mkPoint (edge_x_at e1 yhi + delta) yhi)
      (mkPoint (edge_x_at e1 (py v + eps) + delta) (py v - eps)) /\
    ring_complement r (mkPoint (edge_x_at e1 yhi + delta) yhi) /\
    ring_complement r
      (mkPoint (edge_x_at e1 (py v + eps) + delta) (py v - eps)) /\
    (forall vt, In vt r -> py vt <> py v - eps).
Proof.
  intros r e1 v w yhi Htaut Hin Hor Hvw Hlo Hhi Hopen.
  destruct e1 as [ea eb].
  assert (Hnh : py ea <> py eb)
    by (destruct Hor as [He | He]; inversion He; subst; cbn; lra).
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
  assert (Hopen' : corner_opens_east r' e1' (xmir v)).
  { intros g' Hing' Hinc'.
    unfold r' in Hing'. rewrite ring_edges_map in Hing'.
    apply in_map_iff in Hing'. destruct Hing' as [g [Hgeq Hing]].
    subst g'. cbn [fst snd] in *.
    assert (Hinc : fst g = v \/ snd g = v).
    { destruct Hinc' as [H | H]; [ left | right ]; apply xmir_inj; exact H. }
    destruct (Hopen g Hing Hinc) as [HA HB].
    split.
    - intro Hyy.
      assert (Hyy' : py v <= py (fst g))
        by (unfold xmir in Hyy; cbn [py] in Hyy; lra).
      specialize (HA Hyy').
      unfold e1'.
      replace (py (xmir (fst g))) with (py (fst g))
        by (unfold xmir; cbn [py]; reflexivity).
      rewrite (edge_x_at_xmir ea eb (py (fst g)) Hnh).
      replace (px (xmir (fst g))) with (- px (fst g))
        by (unfold xmir; cbn [px]; reflexivity).
      lra.
    - intro Hyy.
      assert (Hyy' : py v <= py (snd g))
        by (unfold xmir in Hyy; cbn [py] in Hyy; lra).
      specialize (HB Hyy').
      unfold e1'.
      replace (py (xmir (snd g))) with (py (snd g))
        by (unfold xmir; cbn [py]; reflexivity).
      rewrite (edge_x_at_xmir ea eb (py (snd g)) Hnh).
      replace (px (xmir (snd g))) with (- px (snd g))
        by (unfold xmir; cbn [px]; reflexivity).
      lra. }
  destruct (corner_passage_fresh r' e1' (xmir v) (xmir w) yhi
              Htaut' Hin' Hor'
              ltac:(unfold xmir; cbn [py]; lra)
              ltac:(unfold xmir; cbn [py]; lra)
              ltac:(unfold xmir; cbn [py]; lra)
              Hopen') as [delta0 [Hd0 Hstage]].
  exists delta0. split; [ exact Hd0 | ]. intros delta Hd.
  destruct (Hstage delta Hd) as [eps0 [He0 Hpass]].
  exists eps0. split; [ exact He0 | ]. intros eps He.
  destruct (Hpass eps He) as [Hconn' [HcA' [HcB' Hfr']]].
  assert (HtopEq : corridor e1' delta yhi
                     = xmir (mkPoint (edge_x_at (ea, eb) yhi + delta) yhi)).
  { unfold e1', corridor.
    rewrite (edge_x_at_xmir ea eb yhi Hnh).
    unfold xmir; cbn [px py]. f_equal. ring. }
  assert (HbotEq : mkPoint (edge_x_at e1' (py (xmir v) + eps) - delta)
                           (py (xmir v) - eps)
                 = xmir (mkPoint (edge_x_at (ea, eb) (py v + eps) + delta)
                                 (py v - eps))).
  { unfold e1'.
    replace (py (xmir v) + eps) with (py v + eps)
      by (unfold xmir; cbn [py]; ring).
    rewrite (edge_x_at_xmir ea eb (py v + eps) Hnh).
    unfold xmir; cbn [px py]. f_equal; ring. }
  rewrite HtopEq in Hconn', HcA'.
  rewrite HbotEq in Hconn', HcB'.
  split; [ | split; [ | split ] ].
  - exact (connected_xmir_rev r _ _ Hconn').
  - exact (proj1 (ring_complement_xmir r _) HcA').
  - exact (proj1 (ring_complement_xmir r _) HcB').
  - intros vt Hinvt Heq.
    apply (Hfr' (xmir vt)).
    + unfold r'. apply in_map. exact Hinvt.
    + unfold xmir; cbn [py]. lra.
Qed.

(* ---------------------------------------------------------------------------
   §4  East side, over the top: the x-flip of the y-flipped fresh move.
   --------------------------------------------------------------------------- *)

Definition corner_opens_west_top (r : Ring) (e1 : Edge) (u : Point) : Prop :=
  forall g, In g (ring_edges r) ->
    fst g = u \/ snd g = u ->
    (py (fst g) <= py u -> px (fst g) <= edge_x_at e1 (py (fst g))) /\
    (py (snd g) <= py u -> px (snd g) <= edge_x_at e1 (py (snd g))).

Theorem corner_passage_east_top : forall (r : Ring) (e1 : Edge)
                                         (v u : Point) (ylo : R),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, u) \/ e1 = (u, v) ->
  py v < py u ->
  py v < ylo ->
  ylo < py u ->
  corner_opens_west_top r e1 u ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    connected_in_complement_cont r
      (mkPoint (edge_x_at e1 ylo + delta) ylo)
      (mkPoint (edge_x_at e1 (py u - eps) + delta) (py u + eps)) /\
    ring_complement r (mkPoint (edge_x_at e1 ylo + delta) ylo) /\
    ring_complement r
      (mkPoint (edge_x_at e1 (py u - eps) + delta) (py u + eps)) /\
    (forall vt, In vt r -> py vt <> py u + eps).
Proof.
  intros r e1 v u ylo Htaut Hin Hor Hvu Hlo Hhi Hopen.
  destruct e1 as [ea eb].
  assert (Hnh : py ea <> py eb)
    by (destruct Hor as [He | He]; inversion He; subst; cbn; lra).
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
  assert (Hopen' : corner_opens_east_top r' e1' (xmir u)).
  { intros g' Hing' Hinc'.
    unfold r' in Hing'. rewrite ring_edges_map in Hing'.
    apply in_map_iff in Hing'. destruct Hing' as [g [Hgeq Hing]].
    subst g'. cbn [fst snd] in *.
    assert (Hinc : fst g = u \/ snd g = u).
    { destruct Hinc' as [H | H]; [ left | right ]; apply xmir_inj; exact H. }
    destruct (Hopen g Hing Hinc) as [HA HB].
    split.
    - intro Hyy.
      assert (Hyy' : py (fst g) <= py u)
        by (unfold xmir in Hyy; cbn [py] in Hyy; lra).
      specialize (HA Hyy').
      unfold e1'.
      replace (py (xmir (fst g))) with (py (fst g))
        by (unfold xmir; cbn [py]; reflexivity).
      rewrite (edge_x_at_xmir ea eb (py (fst g)) Hnh).
      replace (px (xmir (fst g))) with (- px (fst g))
        by (unfold xmir; cbn [px]; reflexivity).
      lra.
    - intro Hyy.
      assert (Hyy' : py (snd g) <= py u)
        by (unfold xmir in Hyy; cbn [py] in Hyy; lra).
      specialize (HB Hyy').
      unfold e1'.
      replace (py (xmir (snd g))) with (py (snd g))
        by (unfold xmir; cbn [py]; reflexivity).
      rewrite (edge_x_at_xmir ea eb (py (snd g)) Hnh).
      replace (px (xmir (snd g))) with (- px (snd g))
        by (unfold xmir; cbn [px]; reflexivity).
      lra. }
  destruct (corner_passage_top_fresh r' e1' (xmir v) (xmir u) ylo
              Htaut' Hin' Hor'
              ltac:(unfold xmir; cbn [py]; lra)
              ltac:(unfold xmir; cbn [py]; lra)
              ltac:(unfold xmir; cbn [py]; lra)
              Hopen') as [delta0 [Hd0 Hstage]].
  exists delta0. split; [ exact Hd0 | ]. intros delta Hd.
  destruct (Hstage delta Hd) as [eps0 [He0 Hpass]].
  exists eps0. split; [ exact He0 | ]. intros eps He.
  destruct (Hpass eps He) as [Hconn' [HcA' [HcB' Hfr']]].
  assert (HtopEq : corridor e1' delta ylo
                     = xmir (mkPoint (edge_x_at (ea, eb) ylo + delta) ylo)).
  { unfold e1', corridor.
    rewrite (edge_x_at_xmir ea eb ylo Hnh).
    unfold xmir; cbn [px py]. f_equal. ring. }
  assert (HbotEq : mkPoint (edge_x_at e1' (py (xmir u) - eps) - delta)
                           (py (xmir u) + eps)
                 = xmir (mkPoint (edge_x_at (ea, eb) (py u - eps) + delta)
                                 (py u + eps))).
  { unfold e1'.
    replace (py (xmir u) - eps) with (py u - eps)
      by (unfold xmir; cbn [py]; ring).
    rewrite (edge_x_at_xmir ea eb (py u - eps) Hnh).
    unfold xmir; cbn [px py]. f_equal; ring. }
  rewrite HtopEq in Hconn', HcA'.
  rewrite HbotEq in Hconn', HcB'.
  split; [ | split; [ | split ] ].
  - exact (connected_xmir_rev r _ _ Hconn').
  - exact (proj1 (ring_complement_xmir r _) HcA').
  - exact (proj1 (ring_complement_xmir r _) HcB').
  - intros vt Hinvt Heq.
    apply (Hfr' (xmir vt)).
    + unfold r'. apply in_map. exact Hinvt.
    + unfold xmir; cbn [py]. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions corner_passage_fresh.
Print Assumptions corner_passage_top_fresh.
Print Assumptions corner_passage_east.
Print Assumptions corner_passage_east_top.
