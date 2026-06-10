(* ============================================================================
   NetTopologySuite.Proofs.JCTTopPassage
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-1: THE TOP PASSAGE and the TERMINAL COUNT.

   First consumer of the mirror kit (rung 5b): `corner_passage` (rung 5a,
   the under-the-bottom corner move) pulled back through the y-flip gives
   `corner_passage_top` -- from the wall's west corridor at any height
   strictly inside the span, over the wall's TOP vertex, to an off-ring,
   ray-guarded point strictly ABOVE the top level.  This is the move that
   backs the walk out of a wedge: when the bottom corner is sealed
   (`corner_opens_east` fails below), the walk exits upward over the top.
   The mirrored hypothesis `corner_opens_east_top` reads in original
   coordinates: every edge incident at the top vertex u reaching weakly
   BELOW u's level stays weakly east of the wall's carrier.

   Because the y-flip is exact for the guard and the crossing data
   (rung 5b), the destination's ray guard pulls back directly --
   no re-derivation needed.  The x-flip versions (east-side passages)
   transport freedom/connectivity the same way and are assembled when the
   traversal needs them; `edge_x_at_xmir` is provided here.

   Also here: the traversal's terminal payoff.  `xsup` is the ring's
   east-most vertex abscissa (an explicit Rmax fold); at or east of it no
   edge crosses the eastward ray (`ho_cross_east_none`: the crossing
   abscissa is a convex combination of endpoint abscissae), so
   `ho_count_zero_east`: any point at or east of `xsup` has crossing count
   ZERO -- strictly below the walker's even positive count, and exactly
   what `escape_east_of_zero_count` consumes.

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
From NTS.Proofs Require Import JCTCornerClear JCTMirrorKit.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  Mirror micro-kit: injectivity and the carrier across the flips.
   --------------------------------------------------------------------------- *)

Lemma ymir_inj : forall p q : Point, ymir p = ymir q -> p = q.
Proof.
  intros p q H.
  rewrite <- (ymir_invol p), <- (ymir_invol q), H. reflexivity.
Qed.

Lemma xmir_inj : forall p q : Point, xmir p = xmir q -> p = q.
Proof.
  intros p q H.
  rewrite <- (xmir_invol p), <- (xmir_invol q), H. reflexivity.
Qed.

Lemma edge_x_at_ymir : forall (a b : Point) (y : R),
  py a <> py b ->
  edge_x_at (ymir a, ymir b) (- y) = edge_x_at (a, b) y.
Proof.
  intros a b y Hnh. unfold edge_x_at, ymir; cbn [px py]. field. lra.
Qed.

Lemma edge_x_at_xmir : forall (a b : Point) (y : R),
  py a <> py b ->
  edge_x_at (xmir a, xmir b) y = - edge_x_at (a, b) y.
Proof.
  intros a b y Hnh. unfold edge_x_at, xmir; cbn [px py]. field. lra.
Qed.

(* ---------------------------------------------------------------------------
   §1  The top passage: corner_passage through the y-flip.
   --------------------------------------------------------------------------- *)

(* The corner condition at the wall's TOP vertex u: every incident edge
   reaching weakly BELOW u's level stays weakly east of the wall's carrier.
   This is exactly `corner_opens_east` of the y-mirrored ring at ymir u. *)
Definition corner_opens_east_top (r : Ring) (e1 : Edge) (u : Point) : Prop :=
  forall g, In g (ring_edges r) ->
    fst g = u \/ snd g = u ->
    (py (fst g) <= py u -> edge_x_at e1 (py (fst g)) <= px (fst g)) /\
    (py (snd g) <= py u -> edge_x_at e1 (py (snd g)) <= px (snd g)).

(* THE RUNG THEOREM: over the top.  From the west corridor at any height
   strictly inside the wall's span, around the TOP vertex u, to an
   off-ring, ray-guarded point strictly ABOVE the top level. *)
Theorem corner_passage_top : forall (r : Ring) (e1 : Edge) (v u : Point)
                                    (ylo : R),
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
    ray_avoids_vertices
      (mkPoint (edge_x_at e1 (py u - eps) - delta) (py u + eps)) r.
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
  destruct (corner_passage r' e1' (ymir u) (ymir v) (- ylo) Htaut' Hin' Hor'
              ltac:(unfold ymir; cbn [py]; lra)
              ltac:(unfold ymir; cbn [py]; lra)
              ltac:(unfold ymir; cbn [py]; lra)
              Hopen') as [delta0 [Hd0 Hstage]].
  exists delta0. split; [ exact Hd0 | ]. intros delta Hd.
  destruct (Hstage delta Hd) as [eps0 [He0 Hpass]].
  exists eps0. split; [ exact He0 | ]. intros eps He.
  destruct (Hpass eps He) as [Hconn' [HcA' [HcB' Hg']]].
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
  rewrite HbotEq in Hconn', HcB', Hg'.
  split; [ | split; [ | split ] ].
  - exact (connected_ymir_rev r _ _ Hconn').
  - exact (proj1 (ring_complement_ymir r _) HcA').
  - exact (proj1 (ring_complement_ymir r _) HcB').
  - exact (guard_ymir_rev r _ Hg').
Qed.

(* ---------------------------------------------------------------------------
   §2  The terminal count: east of every vertex, the count is zero.
   --------------------------------------------------------------------------- *)

(* The ring's east-most vertex abscissa, as an explicit Rmax fold. *)
Fixpoint xsup (l : list Point) : R :=
  match l with
  | [] => 0
  | v :: l' => Rmax (px v) (xsup l')
  end.

Lemma xsup_ub : forall (l : list Point) (v : Point),
  In v l -> px v <= xsup l.
Proof.
  induction l as [| w l' IH]; intros v Hin; [ contradiction | ].
  cbn [xsup]. destruct Hin as [He | Hin].
  - subst w. apply Rmax_l.
  - pose proof (IH v Hin). pose proof (Rmax_r (px w) (xsup l')). lra.
Qed.

(* No edge crosses the eastward ray of a point at or east of xsup: the
   crossing abscissa is a convex combination of the endpoint abscissae. *)
Lemma ho_cross_east_none : forall (r : Ring) (q : Point) (a b : Point),
  In (a, b) (ring_edges r) ->
  xsup r <= px q ->
  ~ edge_crosses_ray_ho q (a, b).
Proof.
  intros r q a b Hin Hxs Hc.
  destruct (ring_edges_endpoints_in r _ Hin) as [Ha Hb];
    cbn [fst snd] in Ha, Hb.
  pose proof (xsup_ub r a Ha) as Hxa.
  pose proof (xsup_ub r b Hb) as Hxb.
  destruct Hc as [[Hband Hx] | [Hband Hx]].
  - set (t := (py q - py a) / (py b - py a)).
    assert (Ht1 : t * (py b - py a) = py q - py a)
      by (unfold t; field; lra).
    assert (Htb : 0 <= t <= 1) by nra.
    assert (Hterm : px a + (px b - px a) * (py q - py a) / (py b - py a)
                      = (1 - t) * px a + t * px b)
      by (unfold t; field; lra).
    rewrite Hterm in Hx. nra.
  - set (t := (py q - py b) / (py a - py b)).
    assert (Ht1 : t * (py a - py b) = py q - py b)
      by (unfold t; field; lra).
    assert (Htb : 0 <= t <= 1) by nra.
    assert (Hterm : px b + (px a - px b) * (py q - py b) / (py a - py b)
                      = (1 - t) * px b + t * px a)
      by (unfold t; field; lra).
    rewrite Hterm in Hx. nra.
Qed.

(* THE TERMINAL COUNT: at or east of the east-most vertex abscissa, the
   crossing count is ZERO -- strictly below any positive count, and the
   precondition of escape_east_of_zero_count. *)
Lemma ho_count_zero_east : forall (r : Ring) (q : Point),
  xsup r <= px q ->
  ho_count q (ring_edges r) = 0%nat.
Proof.
  intros r q Hxs.
  assert (Hsub : forall l, (forall e, In e l -> In e (ring_edges r)) ->
            ho_count q l = 0%nat).
  { induction l as [| e l' IH]; intros Hsubl; [ reflexivity | ].
    cbn [ho_count].
    rewrite IH; [ | intros e' He'; apply Hsubl; right; exact He' ].
    destruct (edge_crosses_ray_ho_dec q e) as [Hc | Hn]; [ | reflexivity ].
    exfalso. destruct e as [a b].
    exact (ho_cross_east_none r q a b
             (Hsubl (a, b) (or_introl eq_refl)) Hxs Hc). }
  apply Hsub. intros e He. exact He.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions corner_passage_top.
Print Assumptions ho_cross_east_none.
Print Assumptions ho_count_zero_east.
