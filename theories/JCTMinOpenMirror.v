(* ============================================================================
   NetTopologySuite.Proofs.JCTMinOpenMirror
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-9: THE MIRRORED OPEN-SIDE TURNAROUNDS.  Rung
   5c-8's open-side local-minimum composite transports through the
   reflections exactly like the pass-through steps did (rung 5c-7):

     hug_step_min_open_ew   (xmir)        local min, east in, west out,
                                          departing edge weakly WEST;
     hug_step_max_open_we   (ymir)        local MAX, west in, east out;
     hug_step_max_open_ew   (xmir o ymir) local max, east in, west out.

   The x-flip swaps the hug sides AND the carrier-side conditions; the
   y-flip turns minima into maxima while keeping sides and conditions.
   Together with rungs 5c-6..8 this completes the OPEN-side corner
   inventory: all four pass-throughs and all four open extremum
   turnarounds.  Only the pinched-side turnaround (the wedge jog) remains
   before the cycle recursion.

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
From NTS.Proofs Require Import JCTMinOpenStep.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  Edge-pair injectivity of the flips.
   --------------------------------------------------------------------------- *)

Lemma xmir_edge_neq : forall (ea eb fa fb : Point),
  (ea, eb) <> (fa, fb) ->
  (xmir ea, xmir eb) <> (xmir fa, xmir fb).
Proof.
  intros ea eb fa fb Hne He.
  assert (H1 : xmir ea = xmir fa) by congruence.
  assert (H2 : xmir eb = xmir fb) by congruence.
  apply xmir_inj in H1. apply xmir_inj in H2.
  subst. exact (Hne eq_refl).
Qed.

Lemma ymir_edge_neq : forall (ea eb fa fb : Point),
  (ea, eb) <> (fa, fb) ->
  (ymir ea, ymir eb) <> (ymir fa, ymir fb).
Proof.
  intros ea eb fa fb Hne He.
  assert (H1 : ymir ea = ymir fa) by congruence.
  assert (H2 : ymir eb = ymir fb) by congruence.
  apply ymir_inj in H1. apply ymir_inj in H2.
  subst. exact (Hne eq_refl).
Qed.

(* ---------------------------------------------------------------------------
   §1  Local minimum, east in, west out (x-flip).
   --------------------------------------------------------------------------- *)

Theorem hug_step_min_open_ew : forall (r : Ring) (e f : Edge)
                                      (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py c < py w_e -> py c < py w_f ->
  px w_f <= edge_x_at e (py w_f) ->
  edge_x_at f (py w_e) <= px w_e ->
  hugs_east r e q ->
  hugs_west r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hnef Hine Hinf HorE HorF
    Hwe Hwf HopE HopW Hhug.
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
  assert (HopE' : edge_x_at (xmir ea, xmir eb) (py (xmir w_f))
                    <= px (xmir w_f)).
  { replace (py (xmir w_f)) with (py w_f)
      by (unfold xmir; cbn [py]; reflexivity).
    rewrite (edge_x_at_xmir ea eb (py w_f) HnhE).
    replace (px (xmir w_f)) with (- px w_f)
      by (unfold xmir; cbn [px]; reflexivity).
    lra. }
  assert (HopW' : px (xmir w_e)
                    <= edge_x_at (xmir fa, xmir fb) (py (xmir w_e))).
  { replace (py (xmir w_e)) with (py w_e)
      by (unfold xmir; cbn [py]; reflexivity).
    rewrite (edge_x_at_xmir fa fb (py w_e) HnhF).
    replace (px (xmir w_e)) with (- px w_e)
      by (unfold xmir; cbn [px]; reflexivity).
    lra. }
  pose proof (hug_step_min_open_we r' (xmir ea, xmir eb) (xmir fa, xmir fb)
                (xmir c) (xmir w_e) (xmir w_f) (xmir q)
                (ring_taut_xmir r Htaut)
                (ring_core_nodup_xmir r Hnd)
                (no_horizontal_xmir r Hnoh)
                (xmir_edge_neq ea eb fa fb Hnef)
                Hine' Hinf' HorE' HorF'
                ltac:(unfold xmir; cbn [py]; lra)
                ltac:(unfold xmir; cbn [py]; lra)
                HopE' HopW'
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
   §2  Local maximum, west in, east out (y-flip).
   --------------------------------------------------------------------------- *)

Theorem hug_step_max_open_we : forall (r : Ring) (e f : Edge)
                                      (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_e < py c -> py w_f < py c ->
  edge_x_at e (py w_f) <= px w_f ->
  px w_e <= edge_x_at f (py w_e) ->
  hugs_west r e q ->
  hugs_east r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hnef Hine Hinf HorE HorF
    Hwe Hwf HopE HopW Hhug.
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
  assert (HopE' : edge_x_at (ymir ea, ymir eb) (py (ymir w_f))
                    <= px (ymir w_f)).
  { replace (py (ymir w_f)) with (- py w_f)
      by (unfold ymir; cbn [py]; reflexivity).
    rewrite (edge_x_at_ymir ea eb (py w_f) HnhE).
    replace (px (ymir w_f)) with (px w_f)
      by (unfold ymir; cbn [px]; reflexivity).
    exact HopE. }
  assert (HopW' : px (ymir w_e)
                    <= edge_x_at (ymir fa, ymir fb) (py (ymir w_e))).
  { replace (py (ymir w_e)) with (- py w_e)
      by (unfold ymir; cbn [py]; reflexivity).
    rewrite (edge_x_at_ymir fa fb (py w_e) HnhF).
    replace (px (ymir w_e)) with (px w_e)
      by (unfold ymir; cbn [px]; reflexivity).
    exact HopW. }
  pose proof (hug_step_min_open_we r' (ymir ea, ymir eb) (ymir fa, ymir fb)
                (ymir c) (ymir w_e) (ymir w_f) (ymir q)
                (ring_taut_ymir r Htaut)
                (ring_core_nodup_ymir r Hnd)
                (no_horizontal_ymir r Hnoh)
                (ymir_edge_neq ea eb fa fb Hnef)
                Hine' Hinf' HorE' HorF'
                ltac:(unfold ymir; cbn [py]; lra)
                ltac:(unfold ymir; cbn [py]; lra)
                HopE' HopW'
                (hugs_west_ymir r ea eb q HnhE Hhug)) as Hstep.
  (* pull hugs_east of the y-mirror back: east stays east under ymir *)
  destruct Hstep as [Hq' [delta [Hd [Hfree Hconn]]]].
  split.
  { pose proof (proj1 (ring_complement_ymir r q)) as Hpb.
    apply Hpb. exact Hq'. }
  exists delta. split; [ exact Hd | ].
  assert (Hpt : forall d',
            mkPoint (edge_x_at (ymir fa, ymir fb) (mid (ymir fa, ymir fb))
                       + d')
                    (mid (ymir fa, ymir fb))
            = ymir (mkPoint (edge_x_at (fa, fb) (mid (fa, fb)) + d')
                            (mid (fa, fb)))).
  { intro d'.
    rewrite mid_ymir.
    replace (- mid (fa, fb)) with (- (mid (fa, fb))) by ring.
    rewrite (edge_x_at_ymir fa fb (mid (fa, fb)) HnhF).
    unfold ymir; cbn [px py]. reflexivity. }
  split.
  - intros d' Hd' Himg.
    apply (Hfree d' Hd').
    rewrite Hpt.
    apply (ring_image_ymir r _). exact Himg.
  - rewrite Hpt in Hconn.
    pose proof (connected_ymir r' (ymir q)
                  (ymir (mkPoint (edge_x_at (fa, fb) (mid (fa, fb)) + delta)
                                 (mid (fa, fb)))) Hconn) as Hc2.
    unfold r' in Hc2.
    rewrite map_ymir_invol, !ymir_invol in Hc2.
    exact Hc2.
Qed.

(* ---------------------------------------------------------------------------
   §3  Local maximum, east in, west out (both flips).
   --------------------------------------------------------------------------- *)

Theorem hug_step_max_open_ew : forall (r : Ring) (e f : Edge)
                                      (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_e < py c -> py w_f < py c ->
  px w_f <= edge_x_at e (py w_f) ->
  edge_x_at f (py w_e) <= px w_e ->
  hugs_east r e q ->
  hugs_west r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hnef Hine Hinf HorE HorF
    Hwe Hwf HopE HopW Hhug.
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
  assert (HopE' : edge_x_at (xmir ea, xmir eb) (py (xmir w_f))
                    <= px (xmir w_f)).
  { replace (py (xmir w_f)) with (py w_f)
      by (unfold xmir; cbn [py]; reflexivity).
    rewrite (edge_x_at_xmir ea eb (py w_f) HnhE).
    replace (px (xmir w_f)) with (- px w_f)
      by (unfold xmir; cbn [px]; reflexivity).
    lra. }
  assert (HopW' : px (xmir w_e)
                    <= edge_x_at (xmir fa, xmir fb) (py (xmir w_e))).
  { replace (py (xmir w_e)) with (py w_e)
      by (unfold xmir; cbn [py]; reflexivity).
    rewrite (edge_x_at_xmir fa fb (py w_e) HnhF).
    replace (px (xmir w_e)) with (- px w_e)
      by (unfold xmir; cbn [px]; reflexivity).
    lra. }
  pose proof (hug_step_max_open_we r' (xmir ea, xmir eb) (xmir fa, xmir fb)
                (xmir c) (xmir w_e) (xmir w_f) (xmir q)
                (ring_taut_xmir r Htaut)
                (ring_core_nodup_xmir r Hnd)
                (no_horizontal_xmir r Hnoh)
                (xmir_edge_neq ea eb fa fb Hnef)
                Hine' Hinf' HorE' HorF'
                ltac:(unfold xmir; cbn [py]; lra)
                ltac:(unfold xmir; cbn [py]; lra)
                HopE' HopW'
                (hugs_east_to_west_xmir r ea eb q HnhE Hhug)) as Hstep.
  assert (HnhF' : py (xmir fa) <> py (xmir fb))
    by (unfold xmir; cbn [py]; lra).
  pose proof (hugs_east_to_west_xmir r' (xmir fa) (xmir fb) (xmir q)
                HnhF' Hstep) as Hback.
  unfold r' in Hback.
  rewrite map_xmir_invol, !xmir_invol in Hback.
  exact Hback.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hug_step_min_open_ew.
Print Assumptions hug_step_max_open_we.
Print Assumptions hug_step_max_open_ew.
