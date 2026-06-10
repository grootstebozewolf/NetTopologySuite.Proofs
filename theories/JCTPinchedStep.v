(* ============================================================================
   NetTopologySuite.Proofs.JCTPinchedStep
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-11: THE PINCHED TURNAROUND.  At a local minimum
   c whose departing edge f climbs strictly WEST of the arriving edge e,
   the west-side walker is inside the closing wedge: the boundary turns
   around and so must the walk.  The composite:

     jog (shrink delta) . descend west-of-e to the fixed band height
     py c + eps0 (rung 4b-2 on the FIXED window [py c + eps0, mid e] --
     f's clip margins are strictly positive there since the carriers only
     meet at c) . jog ACROSS the wedge interior at that height (incident
     edges clear POINTWISE by the carrier identity `on_carrier_x`; all
     other edges by the corner disk, rung 5c-10) . ascend east-of-f
     (x-flipped rung 4b-2) to mid f.

   The hug side flips (`hugs_west e -> hugs_east f`) exactly as in the
   open turnaround -- but the walker never leaves the wedge.  The wedge
   width is affine with root at c (`width(y) = (KE - KF)(y - py c)`, the
   slopes KE > KF from the strict pinch hypotheses), so the band height
   eps0 is fixed BEFORE delta and the jog has room for delta below
   (KE - KF) * eps0 / 3: no quantifier circularity.

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
Import ListNotations.

Local Open Scope R_scope.

Theorem hug_step_min_pinched_we : forall (r : Ring) (e f : Edge)
                                         (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py c < py w_e -> py c < py w_f ->
  px w_f < edge_x_at e (py w_f) ->
  edge_x_at f (py w_e) < px w_e ->
  hugs_west r e q ->
  hugs_east r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hnef Hine Hinf HorE HorF
    Hwe Hwf Hpin1 Hpin2 Hhug.
  destruct Hhug as [Hq [dS [HdS [HfreeS HconnS]]]].
  assert (HorE' : e = (c, w_e) \/ e = (w_e, c)) by tauto.
  assert (HorF' : f = (c, w_f) \/ f = (w_f, c)) by tauto.
  assert (HnhE : py (fst e) <> py (snd e))
    by (destruct HorE as [HE | HE]; subst e; cbn; lra).
  assert (HnhF : py (fst f) <> py (snd f))
    by (destruct HorF as [HF | HF]; subst f; cbn; lra).
  set (yE := mid e). set (yF := mid f).
  assert (HyE : py c < yE < py w_e)
    by (unfold yE, mid; destruct HorE as [HE | HE]; subst e; cbn; lra).
  assert (HyF : py c < yF < py w_f)
    by (unfold yF, mid; destruct HorF as [HF | HF]; subst f; cbn; lra).
  (* the linearized carriers through the corner *)
  set (KE := (px w_e - px c) / (py w_e - py c)).
  set (KF := (px w_f - px c) / (py w_f - py c)).
  assert (HlinE : forall y, edge_x_at e y = px c + KE * (y - py c)).
  { intro y. destruct HorE' as [HE | HE]; subst e;
      unfold edge_x_at, KE; cbn [fst snd]; field; lra. }
  assert (HlinF : forall y, edge_x_at f y = px c + KF * (y - py c)).
  { intro y. destruct HorF' as [HF | HF]; subst f;
      unfold edge_x_at, KF; cbn [fst snd]; field; lra. }
  assert (HKF1 : KF * (py w_f - py c) = px w_f - px c)
    by (unfold KF; field; lra).
  assert (HKE1 : KE * (py w_e - py c) = px w_e - px c)
    by (unfold KE; field; lra).
  assert (HKlt : KF < KE).
  { apply Rmult_lt_reg_r with (py w_f - py c); [ lra | ].
    rewrite (HlinE (py w_f)) in Hpin1. nra. }
  pose proof (Rle_abs KE) as HKEa. pose proof (Rabs_pos KE) as HKEp.
  pose proof (Rle_abs KF) as HKFa. pose proof (Rabs_pos KF) as HKFp.
  assert (HKEa' : - Rabs KE <= KE)
    by (pose proof (Rle_abs (- KE)); rewrite Rabs_Ropp in *; lra).
  assert (HKFa' : - Rabs KF <= KF)
    by (pose proof (Rle_abs (- KF)); rewrite Rabs_Ropp in *; lra).
  (* the corner disk and the fixed band height *)
  destruct (corner_disk_clear r e c w_e Htaut Hine HorE' Hnoh)
    as [rad0 [Hrad0 Hdisk]].
  set (rad := rad0 / 2).
  assert (Hrad : 0 < rad < rad0) by (unfold rad; lra).
  set (eps0 := Rmin (rad / (2 * (Rabs KE + Rabs KF + 1)))
                 (Rmin ((yE - py c) / 2) ((yF - py c) / 2))).
  assert (Heps0 : 0 < eps0 /\ eps0 <= rad / (2 * (Rabs KE + Rabs KF + 1)) /\
                  eps0 <= (yE - py c) / 2 /\ eps0 <= (yF - py c) / 2).
  { unfold eps0.
    pose proof (Rmin_l (rad / (2 * (Rabs KE + Rabs KF + 1)))
                  (Rmin ((yE - py c) / 2) ((yF - py c) / 2))).
    pose proof (Rmin_r (rad / (2 * (Rabs KE + Rabs KF + 1)))
                  (Rmin ((yE - py c) / 2) ((yF - py c) / 2))).
    pose proof (Rmin_l ((yE - py c) / 2) ((yF - py c) / 2)).
    pose proof (Rmin_r ((yE - py c) / 2) ((yF - py c) / 2)).
    assert (0 < rad / (2 * (Rabs KE + Rabs KF + 1)))
      by (apply Rdiv_lt_0_compat; nra).
    assert (0 < Rmin (rad / (2 * (Rabs KE + Rabs KF + 1)))
                  (Rmin ((yE - py c) / 2) ((yF - py c) / 2))).
    { apply Rmin_glb_lt; [ lra | apply Rmin_glb_lt; lra ]. }
    repeat split; lra. }
  destruct Heps0 as [Heps0p [Heps0r [Heps0E Heps0F]]].
  assert (Heps0rad : eps0 <= rad / 2).
  { assert (rad / (2 * (Rabs KE + Rabs KF + 1)) <= rad / 2).
    { apply Rmult_le_reg_r with (2 * (Rabs KE + Rabs KF + 1)); [ nra | ].
      replace (rad / (2 * (Rabs KE + Rabs KF + 1))
                 * (2 * (Rabs KE + Rabs KF + 1))) with rad
        by (field; nra).
      nra. }
    lra. }
  set (ystar := py c + eps0).
  (* fixed-window clearances *)
  assert (HspanE : (py (fst e) < ystar /\ yE < py (snd e)) \/
                   (py (snd e) < ystar /\ yE < py (fst e)))
    by (unfold ystar; destruct HorE' as [HE | HE]; subst e; cbn in *;
        [ left | right ]; lra).
  destruct (wall_corridor_clear r e ystar yE Htaut Hine HspanE
              ltac:(unfold ystar; lra))
    as [dA [HdA HfreeA]].
  assert (HspanF : (py (fst f) < ystar /\ yF < py (snd f)) \/
                   (py (snd f) < ystar /\ yF < py (fst f)))
    by (unfold ystar; destruct HorF' as [HF | HF]; subst f; cbn in *;
        [ left | right ]; lra).
  destruct (wall_corridor_clear_east r f ystar yF Htaut Hinf HspanF
              ltac:(unfold ystar; lra))
    as [dA' [HdA' HfreeA']].
  assert (HspanFm : (py (fst f) < yF /\ yF < py (snd f)) \/
                    (py (snd f) < yF /\ yF < py (fst f)))
    by (destruct HorF' as [HF | HF]; subst f; cbn in *;
        [ left | right ]; lra).
  destruct (wall_corridor_clear_east r f yF yF Htaut Hinf HspanFm
              ltac:(lra))
    as [dM [HdM HfreeM]].
  set (capW := (KE - KF) * eps0 / 3).
  assert (HcapW : 0 < capW) by (unfold capW; nra).
  set (del := Rmin (Rmin dS dA) (Rmin (Rmin dA' dM) capW) / 2).
  assert (Hdel : 0 < del /\ del < dS /\ del < dA /\ del < dA' /\
                 del < dM /\ del < capW).
  { unfold del.
    pose proof (Rmin_l dS dA). pose proof (Rmin_r dS dA).
    pose proof (Rmin_l dA' dM). pose proof (Rmin_r dA' dM).
    pose proof (Rmin_l (Rmin dA' dM) capW).
    pose proof (Rmin_r (Rmin dA' dM) capW).
    pose proof (Rmin_l (Rmin dS dA) (Rmin (Rmin dA' dM) capW)).
    pose proof (Rmin_r (Rmin dS dA) (Rmin (Rmin dA' dM) capW)).
    assert (0 < Rmin (Rmin dS dA) (Rmin (Rmin dA' dM) capW)).
    { apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | ].
      apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | lra ]. }
    repeat split; lra. }
  destruct Hdel as [Hdel0 [HdelS [HdelA [HdelA' [HdelM HdelW]]]]].
  (* wedge width at the band height *)
  assert (Hwidth : edge_x_at e ystar - edge_x_at f ystar
                     = (KE - KF) * eps0).
  { rewrite (HlinE ystar), (HlinF ystar). unfold ystar. ring. }
  assert (Hroom : edge_x_at f ystar + del <= edge_x_at e ystar - del)
    by (unfold capW in HdelW; lra).
  (* the moves *)
  assert (Hjog : connected_in_complement_cont r
            (corridor e del (mid e)) (corridor e dS (mid e))).
  { apply (corridor_offset_jog r e (mid e) del dS ltac:(lra)).
    intros d' Hd'. apply HfreeS. lra. }
  assert (Hdescend : connected_in_complement_cont r
            (corridor e del yE) (corridor e del ystar)).
  { apply (corridor_connected r e ystar yE del HnhE
             ltac:(unfold ystar; lra)).
    intros y Hy. apply (HfreeA del ltac:(lra)). lra. }
  (* the cross-wedge jog *)
  assert (Hcross : connected_in_complement_cont r
            (mkPoint (edge_x_at e ystar - del) ystar)
            (mkPoint (edge_x_at f ystar + del) ystar)).
  { apply horizontal_connected.
    intros x Hx.
    assert (Hx1 : edge_x_at f ystar + del <= x <= edge_x_at e ystar - del).
    { assert (Hlo : edge_x_at f ystar + del
                      <= Rmin (edge_x_at e ystar - del)
                              (edge_x_at f ystar + del))
        by (apply Rmin_glb; lra).
      assert (Hhi : Rmax (edge_x_at e ystar - del)
                         (edge_x_at f ystar + del)
                      <= edge_x_at e ystar - del)
        by (apply Rmax_lub; lra).
      lra. }
    (* disk-square membership *)
    assert (HxE : edge_x_at e ystar = px c + KE * eps0)
      by (rewrite (HlinE ystar); unfold ystar; ring).
    assert (HxF : edge_x_at f ystar = px c + KF * eps0)
      by (rewrite (HlinF ystar); unfold ystar; ring).
    assert (HS2 : eps0 * (2 * (Rabs KE + Rabs KF + 1)) <= rad).
    { replace rad with (rad / (2 * (Rabs KE + Rabs KF + 1))
                          * (2 * (Rabs KE + Rabs KF + 1)))
        by (field; nra).
      apply Rmult_le_compat_r; nra. }
    assert (HbF : Rabs KF * eps0 <= rad / 2) by nra.
    assert (HbE : Rabs KE * eps0 <= rad / 2) by nra.
    assert (HFlo : - (rad / 2) <= KF * eps0) by nra.
    assert (HEhi : KE * eps0 <= rad / 2) by nra.
    assert (Hxdisk : px c - rad <= x <= px c + rad) by lra.
    intro Himg.
    destruct Himg as [g [s [Hing [Hs [Hxs Hys]]]]].
    cbn [px py] in Hxs, Hys.
    destruct (coord_point_dec (fst g) c) as [Hfc | Hfc].
    { (* incident: g = e or g = f, both cleared pointwise *)
      destruct (incident_pair_min r e f c w_e w_f Hnd Hnef Hine Hinf
                  HorE HorF Hwe Hwf g Hing (or_introl Hfc)) as [Hg | Hg];
        subst g.
      - rewrite <- (on_carrier_x e s HnhE) in Hxs.
        rewrite <- Hys in Hxs. lra.
      - rewrite <- (on_carrier_x f s HnhF) in Hxs.
        rewrite <- Hys in Hxs. lra. }
    destruct (coord_point_dec (snd g) c) as [Hsc | Hsc].
    { destruct (incident_pair_min r e f c w_e w_f Hnd Hnef Hine Hinf
                  HorE HorF Hwe Hwf g Hing (or_intror Hsc)) as [Hg | Hg];
        subst g.
      - rewrite <- (on_carrier_x e s HnhE) in Hxs.
        rewrite <- Hys in Hxs. lra.
      - rewrite <- (on_carrier_x f s HnhF) in Hxs.
        rewrite <- Hys in Hxs. lra. }
    apply (Hdisk rad Hrad g Hing Hfc Hsc x ystar Hxdisk
             ltac:(unfold ystar; lra)).
    exists s. repeat split; try assumption; lra. }
  (* the ascent east of f *)
  assert (Hascend : connected_in_complement_cont r
            (mkPoint (edge_x_at f yF + del) yF)
            (mkPoint (edge_x_at f ystar + del) ystar)).
  { apply (corridor_connected_east r f ystar yF del HnhF
             ltac:(unfold ystar; lra)).
    intros y Hy. apply (HfreeA' del ltac:(lra)). lra. }
  (* assemble *)
  assert (Hchain : connected_in_complement_cont r q
            (mkPoint (edge_x_at f yF + del) yF)).
  { apply (connected_in_complement_cont_trans r q
             (corridor e del (mid e))).
    - apply (connected_in_complement_cont_trans r q
               (corridor e dS (mid e))); [ exact HconnS | ].
      apply connected_in_complement_cont_sym. exact Hjog.
    - apply (connected_in_complement_cont_trans r _
               (corridor e del ystar)).
      + exact Hdescend.
      + apply (connected_in_complement_cont_trans r _
                 (mkPoint (edge_x_at f ystar + del) ystar)).
        * exact Hcross.
        * apply connected_in_complement_cont_sym. exact Hascend. }
  split; [ exact Hq | ].
  exists del. split; [ exact Hdel0 | ]. split.
  - intros d' Hd'. apply (HfreeM d' ltac:(lra) yF). lra.
  - exact Hchain.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hug_step_min_pinched_we.
