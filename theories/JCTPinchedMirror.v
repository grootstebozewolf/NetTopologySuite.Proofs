(* ============================================================================
   NetTopologySuite.Proofs.JCTPinchedMirror
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-12: THE MIRRORED PINCHED TURNAROUNDS and the
   CARRIER-SIDE BRIDGE.

   The pinched composite (rung 5c-11) transports through the reflections
   exactly as the open one did (rung 5c-9):

     hug_step_min_pinched_ew   (xmir)         min, east in, west out,
                                              wedge on the east;
     hug_step_max_pinched_we   (ymir)         local MAX, west in, east out;
     hug_step_max_pinched_ew   (xmir o ymir)  max, east in, west out.

   `hugs_east_ymir` (the east state's y-flip transport) is factored out
   here -- it was inlined in rung 5c-9's max_open_we.

   THE BRIDGE (`carrier_side_equiv`): at an extremum corner the two
   carrier-side conditions -- the departing edge's far endpoint against
   the arriving carrier, and the arriving edge's far endpoint against the
   departing carrier -- are EQUIVALENT, both expressing one slope
   comparison through the shared corner ((KE - KF) has one sign).  So the
   per-corner total step decides open vs pinched with a single `Rle_dec`
   and derives the other condition from the bridge; the strict negations
   feed the pinched steps.  Stated for minima and maxima at once (the
   far-endpoint heights lie on the same side of the corner level).

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
From NTS.Proofs Require Import JCTPassageKit JCTTipCrossing JCTCornerBox.
From NTS.Proofs Require Import JCTRingCycle JCTHugStep JCTHugMirror.
From NTS.Proofs Require Import JCTMinOpenStep JCTMinOpenMirror JCTCornerDisk.
From NTS.Proofs Require Import JCTPinchedStep.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  The east state's y-flip transport (factored out of rung 5c-9).
   --------------------------------------------------------------------------- *)

Lemma hugs_east_ymir : forall (r : Ring) (a b : Point) (q : Point),
  py a <> py b ->
  hugs_east r (a, b) q ->
  hugs_east (map ymir r) (ymir a, ymir b) (ymir q).
Proof.
  intros r a b q Hnh [Hq [delta [Hd [Hfree Hconn]]]].
  split.
  { apply (ring_complement_ymir r q). exact Hq. }
  exists delta. split; [ exact Hd | ].
  assert (Hpt : forall d',
            mkPoint (edge_x_at (ymir a, ymir b) (mid (ymir a, ymir b)) + d')
                    (mid (ymir a, ymir b))
            = ymir (mkPoint (edge_x_at (a, b) (mid (a, b)) + d')
                            (mid (a, b)))).
  { intro d'.
    rewrite mid_ymir.
    replace (- mid (a, b)) with (- (mid (a, b))) by ring.
    rewrite (edge_x_at_ymir a b (mid (a, b)) Hnh).
    unfold ymir; cbn [px py]. reflexivity. }
  split.
  - intros d' Hd' Himg.
    rewrite Hpt in Himg.
    apply (Hfree d' Hd').
    apply (ring_image_ymir r _). exact Himg.
  - rewrite Hpt.
    exact (connected_ymir r q _ Hconn).
Qed.

(* ---------------------------------------------------------------------------
   §1  The mirrored pinched turnarounds.
   --------------------------------------------------------------------------- *)

(* Local minimum, east in, west out: the wedge opens to the east. *)
Theorem hug_step_min_pinched_ew : forall (r : Ring) (e f : Edge)
                                         (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py c < py w_e -> py c < py w_f ->
  edge_x_at e (py w_f) < px w_f ->
  px w_e < edge_x_at f (py w_e) ->
  hugs_east r e q ->
  hugs_west r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hnef Hine Hinf HorE HorF
    Hwe Hwf Hpin1 Hpin2 Hhug.
  destruct e as [ea eb]. destruct f as [fa fb].
  assert (HnhE : py ea <> py eb)
    by (destruct HorE as [HE | HE]; inversion HE; subst; cbn; lra).
  assert (HnhF : py fa <> py fb)
    by (destruct HorF as [HF | HF]; inversion HF; subst; cbn; lra).
  set (r' := map xmir r).
  assert (Hine' : In (xmir ea, xmir eb) (ring_edges r')).
  { unfold r'. rewrite ring_edges_map.
    exact (in_map (fun e0 => (xmir (fst e0), xmir (snd e0)))
             (ring_edges r) (ea, eb) Hine). }
  assert (Hinf' : In (xmir fa, xmir fb) (ring_edges r')).
  { unfold r'. rewrite ring_edges_map.
    exact (in_map (fun e0 => (xmir (fst e0), xmir (snd e0)))
             (ring_edges r) (fa, fb) Hinf). }
  assert (HorE' : (xmir ea, xmir eb) = (xmir w_e, xmir c) \/
                  (xmir ea, xmir eb) = (xmir c, xmir w_e)).
  { destruct HorE as [HE | HE]; inversion HE; subst; [ left | right ];
      reflexivity. }
  assert (HorF' : (xmir fa, xmir fb) = (xmir c, xmir w_f) \/
                  (xmir fa, xmir fb) = (xmir w_f, xmir c)).
  { destruct HorF as [HF | HF]; inversion HF; subst; [ left | right ];
      reflexivity. }
  assert (Hpin1' : px (xmir w_f)
                     < edge_x_at (xmir ea, xmir eb) (py (xmir w_f))).
  { replace (py (xmir w_f)) with (py w_f)
      by (unfold xmir; cbn [py]; reflexivity).
    rewrite (edge_x_at_xmir ea eb (py w_f) HnhE).
    replace (px (xmir w_f)) with (- px w_f)
      by (unfold xmir; cbn [px]; reflexivity).
    lra. }
  assert (Hpin2' : edge_x_at (xmir fa, xmir fb) (py (xmir w_e))
                     < px (xmir w_e)).
  { replace (py (xmir w_e)) with (py w_e)
      by (unfold xmir; cbn [py]; reflexivity).
    rewrite (edge_x_at_xmir fa fb (py w_e) HnhF).
    replace (px (xmir w_e)) with (- px w_e)
      by (unfold xmir; cbn [px]; reflexivity).
    lra. }
  pose proof (hug_step_min_pinched_we r' (xmir ea, xmir eb)
                (xmir fa, xmir fb) (xmir c) (xmir w_e) (xmir w_f) (xmir q)
                (ring_taut_xmir r Htaut)
                (ring_core_nodup_xmir r Hnd)
                (no_horizontal_xmir r Hnoh)
                (xmir_edge_neq ea eb fa fb Hnef)
                Hine' Hinf' HorE' HorF'
                ltac:(unfold xmir; cbn [py]; lra)
                ltac:(unfold xmir; cbn [py]; lra)
                Hpin1' Hpin2'
                (hugs_east_to_west_xmir r ea eb q HnhE Hhug)) as Hstep.
  assert (HnhF' : py (xmir fa) <> py (xmir fb))
    by (unfold xmir; cbn [py]; lra).
  pose proof (hugs_east_to_west_xmir r' (xmir fa) (xmir fb) (xmir q)
                HnhF' Hstep) as Hback.
  unfold r' in Hback.
  rewrite map_xmir_invol, !xmir_invol in Hback.
  exact Hback.
Qed.

(* Local maximum, west in, east out. *)
Theorem hug_step_max_pinched_we : forall (r : Ring) (e f : Edge)
                                         (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_e < py c -> py w_f < py c ->
  px w_f < edge_x_at e (py w_f) ->
  edge_x_at f (py w_e) < px w_e ->
  hugs_west r e q ->
  hugs_east r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hnef Hine Hinf HorE HorF
    Hwe Hwf Hpin1 Hpin2 Hhug.
  destruct e as [ea eb]. destruct f as [fa fb].
  assert (HnhE : py ea <> py eb)
    by (destruct HorE as [HE | HE]; inversion HE; subst; cbn; lra).
  assert (HnhF : py fa <> py fb)
    by (destruct HorF as [HF | HF]; inversion HF; subst; cbn; lra).
  set (r' := map ymir r).
  assert (Hine' : In (ymir ea, ymir eb) (ring_edges r')).
  { unfold r'. rewrite ring_edges_map.
    exact (in_map (fun e0 => (ymir (fst e0), ymir (snd e0)))
             (ring_edges r) (ea, eb) Hine). }
  assert (Hinf' : In (ymir fa, ymir fb) (ring_edges r')).
  { unfold r'. rewrite ring_edges_map.
    exact (in_map (fun e0 => (ymir (fst e0), ymir (snd e0)))
             (ring_edges r) (fa, fb) Hinf). }
  assert (HorE' : (ymir ea, ymir eb) = (ymir w_e, ymir c) \/
                  (ymir ea, ymir eb) = (ymir c, ymir w_e)).
  { destruct HorE as [HE | HE]; inversion HE; subst; [ left | right ];
      reflexivity. }
  assert (HorF' : (ymir fa, ymir fb) = (ymir c, ymir w_f) \/
                  (ymir fa, ymir fb) = (ymir w_f, ymir c)).
  { destruct HorF as [HF | HF]; inversion HF; subst; [ left | right ];
      reflexivity. }
  assert (Hpin1' : px (ymir w_f)
                     < edge_x_at (ymir ea, ymir eb) (py (ymir w_f))).
  { replace (py (ymir w_f)) with (- py w_f)
      by (unfold ymir; cbn [py]; reflexivity).
    rewrite (edge_x_at_ymir ea eb (py w_f) HnhE).
    replace (px (ymir w_f)) with (px w_f)
      by (unfold ymir; cbn [px]; reflexivity).
    exact Hpin1. }
  assert (Hpin2' : edge_x_at (ymir fa, ymir fb) (py (ymir w_e))
                     < px (ymir w_e)).
  { replace (py (ymir w_e)) with (- py w_e)
      by (unfold ymir; cbn [py]; reflexivity).
    rewrite (edge_x_at_ymir fa fb (py w_e) HnhF).
    replace (px (ymir w_e)) with (px w_e)
      by (unfold ymir; cbn [px]; reflexivity).
    exact Hpin2. }
  pose proof (hug_step_min_pinched_we r' (ymir ea, ymir eb)
                (ymir fa, ymir fb) (ymir c) (ymir w_e) (ymir w_f) (ymir q)
                (ring_taut_ymir r Htaut)
                (ring_core_nodup_ymir r Hnd)
                (no_horizontal_ymir r Hnoh)
                (ymir_edge_neq ea eb fa fb Hnef)
                Hine' Hinf' HorE' HorF'
                ltac:(unfold ymir; cbn [py]; lra)
                ltac:(unfold ymir; cbn [py]; lra)
                Hpin1' Hpin2'
                (hugs_west_ymir r ea eb q HnhE Hhug)) as Hstep.
  assert (HnhF' : py (ymir fa) <> py (ymir fb))
    by (unfold ymir; cbn [py]; lra).
  pose proof (hugs_east_ymir r' (ymir fa) (ymir fb) (ymir q)
                HnhF' Hstep) as Hback.
  unfold r' in Hback.
  rewrite map_ymir_invol, !ymir_invol in Hback.
  exact Hback.
Qed.

(* Local maximum, east in, west out. *)
Theorem hug_step_max_pinched_ew : forall (r : Ring) (e f : Edge)
                                         (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_e < py c -> py w_f < py c ->
  edge_x_at e (py w_f) < px w_f ->
  px w_e < edge_x_at f (py w_e) ->
  hugs_east r e q ->
  hugs_west r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hnef Hine Hinf HorE HorF
    Hwe Hwf Hpin1 Hpin2 Hhug.
  destruct e as [ea eb]. destruct f as [fa fb].
  assert (HnhE : py ea <> py eb)
    by (destruct HorE as [HE | HE]; inversion HE; subst; cbn; lra).
  assert (HnhF : py fa <> py fb)
    by (destruct HorF as [HF | HF]; inversion HF; subst; cbn; lra).
  set (r' := map xmir r).
  assert (Hine' : In (xmir ea, xmir eb) (ring_edges r')).
  { unfold r'. rewrite ring_edges_map.
    exact (in_map (fun e0 => (xmir (fst e0), xmir (snd e0)))
             (ring_edges r) (ea, eb) Hine). }
  assert (Hinf' : In (xmir fa, xmir fb) (ring_edges r')).
  { unfold r'. rewrite ring_edges_map.
    exact (in_map (fun e0 => (xmir (fst e0), xmir (snd e0)))
             (ring_edges r) (fa, fb) Hinf). }
  assert (HorE' : (xmir ea, xmir eb) = (xmir w_e, xmir c) \/
                  (xmir ea, xmir eb) = (xmir c, xmir w_e)).
  { destruct HorE as [HE | HE]; inversion HE; subst; [ left | right ];
      reflexivity. }
  assert (HorF' : (xmir fa, xmir fb) = (xmir c, xmir w_f) \/
                  (xmir fa, xmir fb) = (xmir w_f, xmir c)).
  { destruct HorF as [HF | HF]; inversion HF; subst; [ left | right ];
      reflexivity. }
  assert (Hpin1' : px (xmir w_f)
                     < edge_x_at (xmir ea, xmir eb) (py (xmir w_f))).
  { replace (py (xmir w_f)) with (py w_f)
      by (unfold xmir; cbn [py]; reflexivity).
    rewrite (edge_x_at_xmir ea eb (py w_f) HnhE).
    replace (px (xmir w_f)) with (- px w_f)
      by (unfold xmir; cbn [px]; reflexivity).
    lra. }
  assert (Hpin2' : edge_x_at (xmir fa, xmir fb) (py (xmir w_e))
                     < px (xmir w_e)).
  { replace (py (xmir w_e)) with (py w_e)
      by (unfold xmir; cbn [py]; reflexivity).
    rewrite (edge_x_at_xmir fa fb (py w_e) HnhF).
    replace (px (xmir w_e)) with (- px w_e)
      by (unfold xmir; cbn [px]; reflexivity).
    lra. }
  pose proof (hug_step_max_pinched_we r' (xmir ea, xmir eb)
                (xmir fa, xmir fb) (xmir c) (xmir w_e) (xmir w_f) (xmir q)
                (ring_taut_xmir r Htaut)
                (ring_core_nodup_xmir r Hnd)
                (no_horizontal_xmir r Hnoh)
                (xmir_edge_neq ea eb fa fb Hnef)
                Hine' Hinf' HorE' HorF'
                ltac:(unfold xmir; cbn [py]; lra)
                ltac:(unfold xmir; cbn [py]; lra)
                Hpin1' Hpin2'
                (hugs_east_to_west_xmir r ea eb q HnhE Hhug)) as Hstep.
  assert (HnhF' : py (xmir fa) <> py (xmir fb))
    by (unfold xmir; cbn [py]; lra).
  pose proof (hugs_east_to_west_xmir r' (xmir fa) (xmir fb) (xmir q)
                HnhF' Hstep) as Hback.
  unfold r' in Hback.
  rewrite map_xmir_invol, !xmir_invol in Hback.
  exact Hback.
Qed.

(* ---------------------------------------------------------------------------
   §2  THE CARRIER-SIDE BRIDGE: the two extremum conditions are one slope
       comparison through the shared corner.
   --------------------------------------------------------------------------- *)

Lemma carrier_lin : forall (e : Edge) (c w : Point),
  e = (c, w) \/ e = (w, c) ->
  py w <> py c ->
  forall y, edge_x_at e y
              = px c + (px w - px c) / (py w - py c) * (y - py c).
Proof.
  intros e c w Hor Hnh y.
  destruct Hor as [He | He]; subst e; unfold edge_x_at; cbn [fst snd];
    field; lra.
Qed.

Lemma carrier_side_equiv : forall (e f : Edge) (c w_e w_f : Point),
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_e <> py c -> py w_f <> py c ->
  (py w_e - py c) * (py w_f - py c) > 0 ->
  (edge_x_at e (py w_f) <= px w_f <-> px w_e <= edge_x_at f (py w_e)) /\
  (px w_f <= edge_x_at e (py w_f) <-> edge_x_at f (py w_e) <= px w_e).
Proof.
  intros e f c w_e w_f HorE HorF HnhE HnhF Hsame.
  assert (HorE' : e = (c, w_e) \/ e = (w_e, c)) by tauto.
  assert (HorF' : f = (c, w_f) \/ f = (w_f, c)) by tauto.
  set (KE := (px w_e - px c) / (py w_e - py c)).
  set (KF := (px w_f - px c) / (py w_f - py c)).
  assert (HKE1 : KE * (py w_e - py c) = px w_e - px c)
    by (unfold KE; field; lra).
  assert (HKF1 : KF * (py w_f - py c) = px w_f - px c)
    by (unfold KF; field; lra).
  assert (HlinE : edge_x_at e (py w_f)
                    = px c + KE * (py w_f - py c))
    by (rewrite (carrier_lin e c w_e HorE' HnhE (py w_f)); unfold KE;
        reflexivity).
  assert (HlinF : edge_x_at f (py w_e)
                    = px c + KF * (py w_e - py c))
    by (rewrite (carrier_lin f c w_f HorF' HnhF (py w_e)); unfold KF;
        reflexivity).
  set (A := py w_e - py c) in *. set (B := py w_f - py c) in *.
  assert (HB2 : 0 < B * B) by nra.
  assert (HA2 : 0 < A * A) by nra.
  split; split; intro H.
  - (* (KE - KF) * B <= 0  ->  (KE - KF) * A <= 0 *)
    assert (H1 : (KE - KF) * B <= 0) by nra.
    assert (T2 : (KE - KF) * A * (B * B) <= 0) by nra.
    nra.
  - assert (H1 : (KE - KF) * A <= 0) by nra.
    assert (T2 : (KE - KF) * B * (A * A) <= 0) by nra.
    nra.
  - assert (H1 : 0 <= (KE - KF) * B) by nra.
    assert (T2 : 0 <= (KE - KF) * A * (B * B)) by nra.
    nra.
  - assert (H1 : 0 <= (KE - KF) * A) by nra.
    assert (T2 : 0 <= (KE - KF) * B * (A * A)) by nra.
    nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hug_step_min_pinched_ew.
Print Assumptions hug_step_max_pinched_we.
Print Assumptions hug_step_max_pinched_ew.
Print Assumptions carrier_side_equiv.
