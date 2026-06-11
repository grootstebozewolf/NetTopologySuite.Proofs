(* ============================================================================
   NetTopologySuite.Proofs.JCTPayoffRides
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-16b: THE PAYOFF RIDES.  At the eastmost vertex
   vS, each hug configuration yields a connected, off-ring, ray-guarded
   point with crossing count 0 or 1:

     payoff_east_ride     east hug of an ascending incident: ride the
                          east corridor to the corner band; the point is
                          strictly EAST of every vertex: count 0;
     payoff_west_ride_pt  west hug at a pass-through corner: ride the
                          west corridor to the band; exactly the ridden
                          edge crosses: count 1;
     payoff_passage_min   west hug at an open local minimum: the corner
                          passage lands BELOW the minimum, where no
                          incident spans and non-incidents are excluded
                          by the disk: count 0;
     payoff_wedge_min     west hug inside a pinched minimum: descend the
                          fixed window to the wedge band; the ridden
                          (east-wall) edge alone crosses: count 1.

   Counts come from rung 5c-16a's kernels: `noncross_far` (non-incidents),
   the incident span/carrier kernels, `ho_count_zero_of_no_cross`,
   `ho_count_one_in`/`_out`; guards from level freshness.  The final
   dispatch (next rung) selects the ride from the hug disjunction and the
   corner type, mirrors the maxima, and closes H1.

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
From NTS.Proofs Require Import JCTPinchedStep JCTPinchedMirror.
From NTS.Proofs Require Import JCTCornerDispatch JCTHugCycle JCTEdgeCount.
From NTS.Proofs Require Import JCTPayoffKit.
Import ListNotations.

Local Open Scope R_scope.

(* The uniform conclusion: a connected, off-ring, guarded point whose
   crossing count is at most one. *)
Definition payoff (r : Ring) (p : Point) : Prop :=
  exists z : Point,
    connected_in_complement_cont r p z /\
    ring_complement r z /\
    ray_avoids_vertices z r /\
    (ho_count z (ring_edges r) = 0%nat \/
     ho_count z (ring_edges r) = 1%nat).

(* ---------------------------------------------------------------------------
   §1  The east ride: count zero, east of everything.
   --------------------------------------------------------------------------- *)

Lemma payoff_east_ride : forall (r : Ring) (E : Edge) (vS w : Point)
                                (p : Point),
  ring_taut r ->
  In E (ring_edges r) ->
  E = (w, vS) \/ E = (vS, w) ->
  py vS < py w ->
  (forall q, In q r -> px q <= px vS) ->
  corner_opens_west r E vS ->
  hugs_east r E p ->
  payoff r p.
Proof.
  intros r E vS w p Htaut HinE HorE Hvw Hub Hopen Hhug.
  destruct Hhug as [Hp [dS [HdS [HfreeS HconnS]]]].
  assert (HorE' : E = (vS, w) \/ E = (w, vS)) by tauto.
  assert (HnhE : py (fst E) <> py (snd E))
    by (destruct HorE as [HE | HE]; subst E; cbn; lra).
  set (yE := mid E).
  assert (HyE : py vS < yE < py w)
    by (unfold yE, mid; destruct HorE as [HE | HE]; subst E; cbn; lra).
  destruct (wall_corridor_clear_corner_east r E vS w yE Htaut HinE HorE'
              ltac:(lra) ltac:(lra) ltac:(lra) Hopen)
    as [dC [HdC HfreeC]].
  set (del := Rmin dS dC / 2).
  assert (Hdel : 0 < del /\ del < dS /\ del < dC).
  { unfold del.
    pose proof (Rmin_l dS dC). pose proof (Rmin_r dS dC).
    assert (0 < Rmin dS dC) by (apply Rmin_glb_lt; lra).
    repeat split; lra. }
  destruct Hdel as [Hdel0 [HdelS HdelC]].
  pose proof (Rabs_pos (px w - px vS)) as HAw.
  pose proof (level_gap_pos (py vS) r) as Hlg.
  set (capE := del * (py w - py vS) / (2 * (Rabs (px w - px vS) + 1))).
  assert (HcapE : 0 < capE)
    by (unfold capE; apply Rdiv_lt_0_compat; nra).
  set (eps := Rmin (Rmin capE (yE - py vS)) (level_gap (py vS) r) / 2).
  assert (Heps : 0 < eps /\ eps < capE /\ eps < yE - py vS /\
                 eps < level_gap (py vS) r).
  { unfold eps.
    pose proof (Rmin_l capE (yE - py vS)).
    pose proof (Rmin_r capE (yE - py vS)).
    pose proof (Rmin_l (Rmin capE (yE - py vS)) (level_gap (py vS) r)).
    pose proof (Rmin_r (Rmin capE (yE - py vS)) (level_gap (py vS) r)).
    assert (0 < Rmin (Rmin capE (yE - py vS)) (level_gap (py vS) r)).
    { apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | lra ]. }
    repeat split; lra. }
  destruct Heps as [Heps0 [HepsE [HepsY HepsG]]].
  assert (HprodE : 2 * eps * (Rabs (px w - px vS) + 1)
                     < del * (py w - py vS)).
  { apply (cap_mult eps _ (2 * (Rabs (px w - px vS) + 1))
             ltac:(nra)) in HepsE.
    unfold capE in HepsE. lra. }
  assert (HbndE : px vS - del / 2 <= edge_x_at E (py vS + eps)
                    <= px vS + del / 2).
  { destruct HorE' as [HE | HE]; subst E.
    - exact (foot_abscissa_bound vS w del eps Hvw ltac:(lra) ltac:(lra)
               HprodE).
    - rewrite <- (edge_x_at_swap vS w (py vS + eps) ltac:(lra)).
      exact (foot_abscissa_bound vS w del eps Hvw ltac:(lra) ltac:(lra)
               HprodE). }
  set (z := mkPoint (edge_x_at E (py vS + eps) + del) (py vS + eps)).
  assert (Hjog : connected_in_complement_cont r
            (mkPoint (edge_x_at E (mid E) + dS) (mid E))
            (mkPoint (edge_x_at E (mid E) + del) (mid E))).
  { apply horizontal_connected.
    intros x Hx.
    assert (Hb : edge_x_at E (mid E) + del <= x
                   <= edge_x_at E (mid E) + dS).
    { assert (Hlo : edge_x_at E (mid E) + del
                      <= Rmin (edge_x_at E (mid E) + dS)
                              (edge_x_at E (mid E) + del))
        by (apply Rmin_glb; lra).
      assert (Hhi : Rmax (edge_x_at E (mid E) + dS)
                         (edge_x_at E (mid E) + del)
                      <= edge_x_at E (mid E) + dS)
        by (apply Rmax_lub; lra).
      lra. }
    replace x with (edge_x_at E (mid E) + (x - edge_x_at E (mid E)))
      by ring.
    apply HfreeS. lra. }
  assert (Hride : connected_in_complement_cont r
            (mkPoint (edge_x_at E yE + del) yE) z).
  { unfold z.
    apply (corridor_connected_east r E (py vS + eps) yE del HnhE
             ltac:(lra)).
    intros y Hy. apply (HfreeC del ltac:(lra)). lra. }
  assert (Hchain : connected_in_complement_cont r p z).
  { apply (connected_in_complement_cont_trans r p
             (mkPoint (edge_x_at E (mid E) + del) (mid E))).
    - apply (connected_in_complement_cont_trans r p
               (mkPoint (edge_x_at E (mid E) + dS) (mid E)));
        [ exact HconnS | exact Hjog ].
    - exact Hride. }
  exists z. split; [ exact Hchain | ]. split; [ | split ].
  - intro Himg.
    apply (HfreeC del ltac:(lra) (py vS + eps) ltac:(lra)).
    exact Himg.
  - apply (guard_of_fresh_level r z (py vS)); unfold z; cbn [py]; lra.
  - left.
    apply ho_count_zero_east_ub.
    intros vt Hvt.
    pose proof (Hub vt Hvt).
    unfold z; cbn [px]. lra.
Qed.

(* ---------------------------------------------------------------------------
   §2  The west ride at a pass-through corner: count one.
   --------------------------------------------------------------------------- *)

Lemma payoff_west_ride_pt : forall (r : Ring) (E E' : Edge)
                                   (vS w w' : Point) (p : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  In E (ring_edges r) -> In E' (ring_edges r) ->
  E = (w, vS) \/ E = (vS, w) ->
  E' = (vS, w') \/ E' = (w', vS) ->
  py vS < py w -> py w' < py vS ->
  (forall q, In q r -> px q <= px vS) ->
  corner_opens_east r E vS ->
  hugs_west r E p ->
  payoff r p.
Proof.
  intros r E E' vS w w' p Htaut Hnd Hnoh HinE HinE' HorE HorE'
    Hvw Hvw' Hub Hopen Hhug.
  destruct Hhug as [Hp [dS [HdS [HfreeS HconnS]]]].
  assert (HorEn : E = (vS, w) \/ E = (w, vS)) by tauto.
  assert (HnhE : py (fst E) <> py (snd E))
    by (destruct HorE as [HE | HE]; subst E; cbn; lra).
  set (yE := mid E).
  assert (HyE : py vS < yE < py w)
    by (unfold yE, mid; destruct HorE as [HE | HE]; subst E; cbn; lra).
  destruct (wall_corridor_clear_corner r E vS w yE Htaut HinE HorEn
              ltac:(lra) ltac:(lra) ltac:(lra) Hopen)
    as [dC [HdC HfreeC]].
  destruct (corner_disk_clear r E vS w Htaut HinE HorEn Hnoh)
    as [rad0 [Hrad0 Hdisk]].
  set (rad := rad0 / 2).
  assert (Hrad : 0 < rad < rad0) by (unfold rad; lra).
  set (del := Rmin (Rmin dS dC) (rad / 2) / 2).
  assert (Hdel : 0 < del /\ del < dS /\ del < dC /\ 2 * del < rad).
  { unfold del.
    pose proof (Rmin_l dS dC). pose proof (Rmin_r dS dC).
    pose proof (Rmin_l (Rmin dS dC) (rad / 2)).
    pose proof (Rmin_r (Rmin dS dC) (rad / 2)).
    assert (0 < Rmin (Rmin dS dC) (rad / 2)).
    { apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | lra ]. }
    repeat split; lra. }
  destruct Hdel as [Hdel0 [HdelS [HdelC Hdelrad]]].
  pose proof (Rabs_pos (px w - px vS)) as HAw.
  pose proof (level_gap_pos (py vS) r) as Hlg.
  set (capE := del * (py w - py vS) / (2 * (Rabs (px w - px vS) + 1))).
  assert (HcapE : 0 < capE)
    by (unfold capE; apply Rdiv_lt_0_compat; nra).
  set (eps := Rmin (Rmin capE (yE - py vS))
                (Rmin (level_gap (py vS) r) rad) / 2).
  assert (Heps : 0 < eps /\ eps < capE /\ eps < yE - py vS /\
                 eps < level_gap (py vS) r /\ eps < rad).
  { unfold eps.
    pose proof (Rmin_l capE (yE - py vS)).
    pose proof (Rmin_r capE (yE - py vS)).
    pose proof (Rmin_l (level_gap (py vS) r) rad).
    pose proof (Rmin_r (level_gap (py vS) r) rad).
    pose proof (Rmin_l (Rmin capE (yE - py vS))
                  (Rmin (level_gap (py vS) r) rad)).
    pose proof (Rmin_r (Rmin capE (yE - py vS))
                  (Rmin (level_gap (py vS) r) rad)).
    assert (0 < Rmin (Rmin capE (yE - py vS))
                  (Rmin (level_gap (py vS) r) rad)).
    { apply Rmin_glb_lt; apply Rmin_glb_lt; lra. }
    repeat split; lra. }
  destruct Heps as [Heps0 [HepsE [HepsY [HepsG Hepsrad]]]].
  assert (HprodE : 2 * eps * (Rabs (px w - px vS) + 1)
                     < del * (py w - py vS)).
  { apply (cap_mult eps _ (2 * (Rabs (px w - px vS) + 1))
             ltac:(nra)) in HepsE.
    unfold capE in HepsE. lra. }
  assert (HbndE : px vS - 2 * del <= edge_x_at E (py vS + eps) - del
                    <= px vS - del / 2).
  { destruct HorEn as [HE | HE]; subst E.
    - exact (drop_abscissa_bound vS w del eps Hvw ltac:(lra) ltac:(lra)
               HprodE).
    - rewrite <- (edge_x_at_swap vS w (py vS + eps) ltac:(lra)).
      exact (drop_abscissa_bound vS w del eps Hvw ltac:(lra) ltac:(lra)
               HprodE). }
  set (z := mkPoint (edge_x_at E (py vS + eps) - del) (py vS + eps)).
  assert (Hjog : connected_in_complement_cont r
            (corridor E del (mid E)) (corridor E dS (mid E))).
  { apply (corridor_offset_jog r E (mid E) del dS ltac:(lra)).
    intros d' Hd'. apply HfreeS. lra. }
  assert (Hride : connected_in_complement_cont r
            (corridor E del yE) (corridor E del (py vS + eps))).
  { apply (corridor_connected r E (py vS + eps) yE del HnhE ltac:(lra)).
    intros y Hy. apply (HfreeC del ltac:(lra)). lra. }
  assert (Hchain : connected_in_complement_cont r p z).
  { apply (connected_in_complement_cont_trans r p
             (corridor E del (mid E))).
    - apply (connected_in_complement_cont_trans r p
               (corridor E dS (mid E))); [ exact HconnS | ].
      apply connected_in_complement_cont_sym. exact Hjog.
    - exact Hride. }
  assert (Hiff : forall g, In g (ring_edges r) ->
            (edge_crosses_ray_ho z g <-> g = E)).
  { intros g Hing. split.
    - intro Hc.
      destruct (coord_point_dec (fst g) vS) as [Hfv | Hfv].
      { destruct (incident_pair r E E' vS w w' Hnd HinE HinE' HorE HorE'
                    Hvw' Hvw g Hing (or_introl Hfv)) as [Hg | Hg];
          [ exact Hg | exfalso; subst g ].
        apply (incident_below_nocross z E'); [ | | exact Hc ];
          destruct HorE' as [HE' | HE']; subst E'; cbn [fst snd];
          unfold z; cbn [py]; lra. }
      destruct (coord_point_dec (snd g) vS) as [Hsv | Hsv].
      { destruct (incident_pair r E E' vS w w' Hnd HinE HinE' HorE HorE'
                    Hvw' Hvw g Hing (or_intror Hsv)) as [Hg | Hg];
          [ exact Hg | exfalso; subst g ].
        apply (incident_below_nocross z E'); [ | | exact Hc ];
          destruct HorE' as [HE' | HE']; subst E'; cbn [fst snd];
          unfold z; cbn [py]; lra. }
      exfalso.
      apply (noncross_far r g vS z rad Hing Hub
               (fun x y Hx Hy => Hdisk rad Hrad g Hing Hfv Hsv x y Hx Hy)
               ltac:(unfold z; cbn [py]; lra)
               ltac:(unfold z; cbn [px]; lra)
               Hc).
    - intro Hg. subst g.
      apply carrier_east_cross.
      + destruct HorE as [HE | HE]; subst E; cbn [fst snd];
          unfold z; cbn [py]; [ right | left ]; lra.
      + unfold z; cbn [px py]. lra.
  }
  exists z. split; [ exact Hchain | ]. split; [ | split ].
  - intro Himg.
    apply (HfreeC del ltac:(lra) (py vS + eps) ltac:(lra)).
    exact Himg.
  - apply (guard_of_fresh_level r z (py vS)); unfold z; cbn [py]; lra.
  - right.
    destruct HorE as [HE | HE]; subst E.
    + exact (ho_count_one_in r z w vS Hnd HinE Hiff).
    + exact (ho_count_one_out r z vS w Hnd HinE Hiff).
Qed.

(* ---------------------------------------------------------------------------
   §3  The passage below an open minimum: count zero.
   --------------------------------------------------------------------------- *)

Lemma payoff_passage_min : forall (r : Ring) (E E' : Edge)
                                  (vS w w' : Point) (p : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  E <> E' ->
  In E (ring_edges r) -> In E' (ring_edges r) ->
  E = (w, vS) \/ E = (vS, w) ->
  E' = (vS, w') \/ E' = (w', vS) ->
  py vS < py w -> py vS < py w' ->
  (forall q, In q r -> px q <= px vS) ->
  corner_opens_east r E vS ->
  hugs_west r E p ->
  payoff r p.
Proof.
  intros r E E' vS w w' p Htaut Hnd Hnoh Hne HinE HinE' HorE HorE'
    Hvw Hvw' Hub Hopen Hhug.
  destruct Hhug as [Hp [dS [HdS [HfreeS HconnS]]]].
  assert (HorEn : E = (vS, w) \/ E = (w, vS)) by tauto.
  set (yE := mid E).
  assert (HyE : py vS < yE < py w)
    by (unfold yE, mid; destruct HorE as [HE | HE]; subst E; cbn; lra).
  destruct (corner_passage_fresh r E vS w yE Htaut HinE HorEn
              ltac:(lra) ltac:(lra) ltac:(lra) Hopen)
    as [dP [HdP HstageP]].
  destruct (corner_disk_clear r E vS w Htaut HinE HorEn Hnoh)
    as [rad0 [Hrad0 Hdisk]].
  set (rad := rad0 / 2).
  assert (Hrad : 0 < rad < rad0) by (unfold rad; lra).
  set (del := Rmin (Rmin dS dP) (rad / 2) / 2).
  assert (Hdel : 0 < del /\ del < dS /\ del < dP /\ 2 * del < rad).
  { unfold del.
    pose proof (Rmin_l dS dP). pose proof (Rmin_r dS dP).
    pose proof (Rmin_l (Rmin dS dP) (rad / 2)).
    pose proof (Rmin_r (Rmin dS dP) (rad / 2)).
    assert (0 < Rmin (Rmin dS dP) (rad / 2)).
    { apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | lra ]. }
    repeat split; lra. }
  destruct Hdel as [Hdel0 [HdelS [HdelP Hdelrad]]].
  destruct (HstageP del ltac:(lra)) as [eP [HeP HpassP]].
  pose proof (Rabs_pos (px w - px vS)) as HAw.
  set (capE := del * (py w - py vS) / (2 * (Rabs (px w - px vS) + 1))).
  assert (HcapE : 0 < capE)
    by (unfold capE; apply Rdiv_lt_0_compat; nra).
  set (eps := Rmin (Rmin eP capE) rad / 2).
  assert (Heps : 0 < eps /\ eps < eP /\ eps < capE /\ eps < rad).
  { unfold eps.
    pose proof (Rmin_l eP capE). pose proof (Rmin_r eP capE).
    pose proof (Rmin_l (Rmin eP capE) rad).
    pose proof (Rmin_r (Rmin eP capE) rad).
    assert (0 < Rmin (Rmin eP capE) rad).
    { apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | lra ]. }
    repeat split; lra. }
  destruct Heps as [Heps0 [HepsP [HepsE Hepsrad]]].
  assert (HprodE : 2 * eps * (Rabs (px w - px vS) + 1)
                     < del * (py w - py vS)).
  { apply (cap_mult eps _ (2 * (Rabs (px w - px vS) + 1))
             ltac:(nra)) in HepsE.
    unfold capE in HepsE. lra. }
  assert (HbndE : px vS - 2 * del <= edge_x_at E (py vS + eps) - del
                    <= px vS - del / 2).
  { destruct HorEn as [HE | HE]; subst E.
    - exact (drop_abscissa_bound vS w del eps Hvw ltac:(lra) ltac:(lra)
               HprodE).
    - rewrite <- (edge_x_at_swap vS w (py vS + eps) ltac:(lra)).
      exact (drop_abscissa_bound vS w del eps Hvw ltac:(lra) ltac:(lra)
               HprodE). }
  destruct (HpassP eps ltac:(lra)) as [HconnP [_ [HcomplZ Hfresh]]].
  set (z := mkPoint (edge_x_at E (py vS + eps) - del) (py vS - eps)).
  assert (Hjog : connected_in_complement_cont r
            (corridor E del (mid E)) (corridor E dS (mid E))).
  { apply (corridor_offset_jog r E (mid E) del dS ltac:(lra)).
    intros d' Hd'. apply HfreeS. lra. }
  assert (Hchain : connected_in_complement_cont r p z).
  { apply (connected_in_complement_cont_trans r p
             (corridor E del (mid E))).
    - apply (connected_in_complement_cont_trans r p
               (corridor E dS (mid E))); [ exact HconnS | ].
      apply connected_in_complement_cont_sym. exact Hjog.
    - exact HconnP. }
  exists z. split; [ exact Hchain | ]. split; [ exact HcomplZ | ]. split.
  - apply ray_guard_of_fresh.
    intros vt Hvt.
    unfold z; cbn [py]. exact (Hfresh vt Hvt).
  - left.
    apply ho_count_zero_of_no_cross.
    intros g Hing Hc.
    destruct (coord_point_dec (fst g) vS) as [Hfv | Hfv].
    { destruct (incident_pair_min r E E' vS w w' Hnd Hne HinE HinE'
                  HorE HorE' Hvw Hvw' g Hing (or_introl Hfv)) as [Hg | Hg];
        subst g.
      - apply (incident_above_nocross z E); [ | | exact Hc ];
          destruct HorE as [HE | HE]; subst E; cbn [fst snd];
          unfold z; cbn [py]; lra.
      - apply (incident_above_nocross z E'); [ | | exact Hc ];
          destruct HorE' as [HE' | HE']; subst E'; cbn [fst snd];
          unfold z; cbn [py]; lra. }
    destruct (coord_point_dec (snd g) vS) as [Hsv | Hsv].
    { destruct (incident_pair_min r E E' vS w w' Hnd Hne HinE HinE'
                  HorE HorE' Hvw Hvw' g Hing (or_intror Hsv)) as [Hg | Hg];
        subst g.
      - apply (incident_above_nocross z E); [ | | exact Hc ];
          destruct HorE as [HE | HE]; subst E; cbn [fst snd];
          unfold z; cbn [py]; lra.
      - apply (incident_above_nocross z E'); [ | | exact Hc ];
          destruct HorE' as [HE' | HE']; subst E'; cbn [fst snd];
          unfold z; cbn [py]; lra. }
    apply (noncross_far r g vS z rad Hing Hub
             (fun x y Hx Hy => Hdisk rad Hrad g Hing Hfv Hsv x y Hx Hy)
             ltac:(unfold z; cbn [py]; lra)
             ltac:(unfold z; cbn [px]; lra)
             Hc).
Qed.

(* ---------------------------------------------------------------------------
   §4  The wedge probe inside a pinched minimum: count one.
   --------------------------------------------------------------------------- *)

Lemma payoff_wedge_min : forall (r : Ring) (E E' : Edge)
                                (vS w w' : Point) (p : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  E <> E' ->
  In E (ring_edges r) -> In E' (ring_edges r) ->
  E = (w, vS) \/ E = (vS, w) ->
  E' = (vS, w') \/ E' = (w', vS) ->
  py vS < py w -> py vS < py w' ->
  (forall q, In q r -> px q <= px vS) ->
  px w' < edge_x_at E (py w') ->
  hugs_west r E p ->
  payoff r p.
Proof.
  intros r E E' vS w w' p Htaut Hnd Hnoh Hne HinE HinE' HorE HorE'
    Hvw Hvw' Hub Hpin Hhug.
  destruct Hhug as [Hp [dS [HdS [HfreeS HconnS]]]].
  assert (HorEn : E = (vS, w) \/ E = (w, vS)) by tauto.
  assert (HorE'n : E' = (vS, w') \/ E' = (w', vS)) by tauto.
  assert (HnhE : py (fst E) <> py (snd E))
    by (destruct HorE as [HE | HE]; subst E; cbn; lra).
  assert (HnhE' : py (fst E') <> py (snd E'))
    by (destruct HorE' as [HE' | HE']; subst E'; cbn; lra).
  set (yE := mid E).
  assert (HyE : py vS < yE < py w)
    by (unfold yE, mid; destruct HorE as [HE | HE]; subst E; cbn; lra).
  (* linearized carriers through the corner *)
  set (KE := (px w - px vS) / (py w - py vS)).
  set (KF := (px w' - px vS) / (py w' - py vS)).
  assert (HlinE : forall y, edge_x_at E y = px vS + KE * (y - py vS)).
  { intro y. destruct HorEn as [HE | HE]; subst E;
      unfold edge_x_at, KE; cbn [fst snd]; field; lra. }
  assert (HlinF : forall y, edge_x_at E' y = px vS + KF * (y - py vS)).
  { intro y. destruct HorE'n as [HE' | HE']; subst E';
      unfold edge_x_at, KF; cbn [fst snd]; field; lra. }
  assert (HKlt : KF < KE).
  { apply Rmult_lt_reg_r with (py w' - py vS); [ lra | ].
    assert (HKF1 : KF * (py w' - py vS) = px w' - px vS)
      by (unfold KF; field; lra).
    rewrite (HlinE (py w')) in Hpin. nra. }
  pose proof (Rle_abs KE) as HKEa. pose proof (Rabs_pos KE) as HKEp.
  pose proof (Rle_abs KF) as HKFa. pose proof (Rabs_pos KF) as HKFp.
  assert (HKEa' : - Rabs KE <= KE)
    by (pose proof (Rle_abs (- KE)); rewrite Rabs_Ropp in *; lra).
  (* the disk and the fixed band height *)
  destruct (corner_disk_clear r E vS w Htaut HinE HorEn Hnoh)
    as [rad0 [Hrad0 Hdisk]].
  set (rad := rad0 / 2).
  assert (Hrad : 0 < rad < rad0) by (unfold rad; lra).
  pose proof (level_gap_pos (py vS) r) as Hlg.
  set (eps0 := Rmin (Rmin (rad / (2 * (Rabs KE + 1)))
                       (level_gap (py vS) r / 2))
                 (Rmin ((yE - py vS) / 2) ((py w' - py vS) / 2))).
  assert (Heps0 : 0 < eps0 /\ eps0 <= rad / (2 * (Rabs KE + 1)) /\
                  eps0 < level_gap (py vS) r /\
                  eps0 <= (yE - py vS) / 2 /\
                  eps0 <= (py w' - py vS) / 2).
  { unfold eps0.
    pose proof (Rmin_l (rad / (2 * (Rabs KE + 1)))
                  (level_gap (py vS) r / 2)).
    pose proof (Rmin_r (rad / (2 * (Rabs KE + 1)))
                  (level_gap (py vS) r / 2)).
    pose proof (Rmin_l ((yE - py vS) / 2) ((py w' - py vS) / 2)).
    pose proof (Rmin_r ((yE - py vS) / 2) ((py w' - py vS) / 2)).
    pose proof (Rmin_l (Rmin (rad / (2 * (Rabs KE + 1)))
                          (level_gap (py vS) r / 2))
                  (Rmin ((yE - py vS) / 2) ((py w' - py vS) / 2))).
    pose proof (Rmin_r (Rmin (rad / (2 * (Rabs KE + 1)))
                          (level_gap (py vS) r / 2))
                  (Rmin ((yE - py vS) / 2) ((py w' - py vS) / 2))).
    assert (0 < rad / (2 * (Rabs KE + 1)))
      by (apply Rdiv_lt_0_compat; nra).
    assert (0 < Rmin (Rmin (rad / (2 * (Rabs KE + 1)))
                        (level_gap (py vS) r / 2))
                  (Rmin ((yE - py vS) / 2) ((py w' - py vS) / 2))).
    { apply Rmin_glb_lt; apply Rmin_glb_lt; lra. }
    repeat split; lra. }
  destruct Heps0 as [Heps0p [Heps0r [Heps0G [Heps0E Heps0F]]]].
  set (ystar := py vS + eps0).
  (* eps0 stays under half the disk radius *)
  assert (Heps0rad : eps0 <= rad / 2).
  { assert (rad / (2 * (Rabs KE + 1)) <= rad / 2).
    { apply Rmult_le_reg_r with (2 * (Rabs KE + 1)); [ nra | ].
      replace (rad / (2 * (Rabs KE + 1)) * (2 * (Rabs KE + 1))) with rad
        by (field; nra).
      nra. }
    lra. }
  assert (HKeps : Rabs KE * eps0 <= rad / 2).
  { assert (HS2 : eps0 * (2 * (Rabs KE + 1)) <= rad).
    { replace rad with (rad / (2 * (Rabs KE + 1)) * (2 * (Rabs KE + 1)))
        by (field; nra).
      apply Rmult_le_compat_r; nra. }
    nra. }
  (* the fixed-window descent clearance *)
  assert (HspanE : (py (fst E) < ystar /\ yE < py (snd E)) \/
                   (py (snd E) < ystar /\ yE < py (fst E)))
    by (unfold ystar; destruct HorEn as [HE | HE]; subst E; cbn in *;
        [ left | right ]; lra).
  destruct (wall_corridor_clear r E ystar yE Htaut HinE HspanE
              ltac:(unfold ystar; lra))
    as [dA [HdA HfreeA]].
  set (capW := (KE - KF) * eps0 / 3).
  assert (HcapW : 0 < capW) by (unfold capW; nra).
  set (del := Rmin (Rmin dS dA) (Rmin capW (rad / 4)) / 2).
  assert (Hdel : 0 < del /\ del < dS /\ del < dA /\ del < capW /\
                 del < rad / 4).
  { unfold del.
    pose proof (Rmin_l dS dA). pose proof (Rmin_r dS dA).
    pose proof (Rmin_l capW (rad / 4)). pose proof (Rmin_r capW (rad / 4)).
    pose proof (Rmin_l (Rmin dS dA) (Rmin capW (rad / 4))).
    pose proof (Rmin_r (Rmin dS dA) (Rmin capW (rad / 4))).
    assert (0 < Rmin (Rmin dS dA) (Rmin capW (rad / 4))).
    { apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra
                         | apply Rmin_glb_lt; lra ]. }
    repeat split; lra. }
  destruct Hdel as [Hdel0 [HdelS [HdelA [HdelW Hdelrad]]]].
  set (z := corridor E del ystar).
  assert (Hzx : px z = px vS + KE * eps0 - del)
    by (unfold z, corridor; cbn [px]; rewrite (HlinE ystar);
        unfold ystar; ring).
  assert (HzxF : edge_x_at E' ystar = px vS + KF * eps0)
    by (rewrite (HlinF ystar); unfold ystar; ring).
  (* the moves *)
  assert (Hjog : connected_in_complement_cont r
            (corridor E del (mid E)) (corridor E dS (mid E))).
  { apply (corridor_offset_jog r E (mid E) del dS ltac:(lra)).
    intros d' Hd'. apply HfreeS. lra. }
  assert (Hride : connected_in_complement_cont r
            (corridor E del yE) z).
  { unfold z.
    apply (corridor_connected r E ystar yE del HnhE
             ltac:(unfold ystar; lra)).
    intros y Hy. apply (HfreeA del ltac:(lra)). lra. }
  assert (Hchain : connected_in_complement_cont r p z).
  { apply (connected_in_complement_cont_trans r p
             (corridor E del (mid E))).
    - apply (connected_in_complement_cont_trans r p
               (corridor E dS (mid E))); [ exact HconnS | ].
      apply connected_in_complement_cont_sym. exact Hjog.
    - exact Hride. }
  (* the count *)
  assert (Hiff : forall g, In g (ring_edges r) ->
            (edge_crosses_ray_ho z g <-> g = E)).
  { intros g Hing. split.
    - intro Hc.
      destruct (coord_point_dec (fst g) vS) as [Hfv | Hfv].
      { destruct (incident_pair_min r E E' vS w w' Hnd Hne HinE HinE'
                    HorE HorE' Hvw Hvw' g Hing (or_introl Hfv))
          as [Hg | Hg]; [ exact Hg | exfalso; subst g ].
        apply (carrier_west_nocross z E' HnhE'); [ | exact Hc ].
        unfold z, corridor; cbn [px py].
        rewrite HzxF, (HlinE ystar). unfold ystar, capW in *. nra. }
      destruct (coord_point_dec (snd g) vS) as [Hsv | Hsv].
      { destruct (incident_pair_min r E E' vS w w' Hnd Hne HinE HinE'
                    HorE HorE' Hvw Hvw' g Hing (or_intror Hsv))
          as [Hg | Hg]; [ exact Hg | exfalso; subst g ].
        apply (carrier_west_nocross z E' HnhE'); [ | exact Hc ].
        unfold z, corridor; cbn [px py].
        rewrite HzxF, (HlinE ystar). unfold ystar, capW in *. nra. }
      exfalso.
      assert (HzxLo : px vS - rad < px z).
      { rewrite Hzx.
        assert (T1 : - (rad / 2) <= KE * eps0) by nra.
        lra. }
      apply (noncross_far r g vS z rad Hing Hub
               (fun x y Hx Hy => Hdisk rad Hrad g Hing Hfv Hsv x y Hx Hy)
               ltac:(unfold z, corridor; cbn [py]; unfold ystar; lra)
               HzxLo
               Hc).
    - intro Hg. subst g.
      apply carrier_east_cross.
      + destruct HorEn as [HE | HE]; subst E; cbn [fst snd];
          unfold z, corridor; cbn [py]; unfold ystar;
          [ left | right ]; lra.
      + unfold z, corridor; cbn [px py]. lra.
  }
  exists z. split; [ exact Hchain | ]. split; [ | split ].
  - intro Himg.
    apply (HfreeA del ltac:(lra) ystar ltac:(unfold ystar; lra)).
    exact Himg.
  - apply (guard_of_fresh_level r z (py vS));
      unfold z, corridor; cbn [py]; unfold ystar; lra.
  - right.
    destruct HorE as [HE | HE]; subst E.
    + exact (ho_count_one_in r z w vS Hnd HinE Hiff).
    + exact (ho_count_one_out r z vS w Hnd HinE Hiff).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions payoff_east_ride.
Print Assumptions payoff_west_ride_pt.
Print Assumptions payoff_passage_min.
Print Assumptions payoff_wedge_min.
