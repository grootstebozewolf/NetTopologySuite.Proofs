(* ============================================================================
   NetTopologySuite.Proofs.JCTEscapeDescentHolds
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-17: THE CLOSING RUNG.

     escape_descent_holds : ring_taut r -> ring_core_nodup r ->
                            no_horizontal_edges r -> escape_descent r

   and with it, through `parity_seam_offring_of_descent`, the corrected
   polygonal Jordan seam H1 for taut, proper, horizontal-free rings:

     parity_seam_offring_taut :
       parity_characterises_interior_cont_offring p r.

   The proof of the descent: the walker (even, guarded, positive count)
   enters the boundary hug at its first wall (`hug_entry`, rung 1 +
   5c-14), propagates around the whole ring (`hugs_everywhere`), and at
   the EASTMOST vertex the dispatch below selects a payoff ride (rungs
   5c-16a/b): pass-through corners ride directly; minima ride the
   passage/east-ride on the open side or probe the wedge on the pinched
   side; maxima are the y-flip of minima (`payoff_ymir` -- the y-flip is
   exact for counts and guards, rung 5b).  The harvested point has
   crossing count 0 or 1.  Count 0 is the descent's q (even, and less
   than any positive count).  Count 1 is ODD: by parity transport along
   the connecting path (`parity_constant_on_components`) the even walker
   would be in-ring -- contradiction, so the case is absurd.

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
From NTS.Proofs Require Import JCTPayoffKit JCTPayoffRides JCTSeparation.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  Two small gap-fillers.
   --------------------------------------------------------------------------- *)

(* The west mirror of opens_east_pass_down. *)
Lemma opens_west_pass_down : forall (r : Ring) (e f : Edge)
                                    (c w_e w_f : Point),
  ring_core_nodup r ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_f < py c -> py c < py w_e ->
  corner_opens_west r e c.
Proof.
  intros r e f c w_e w_f Hnd Hine Hinf HorE HorF Hwf Hwe g Hing Hinc.
  assert (HorE' : e = (c, w_e) \/ e = (w_e, c)) by tauto.
  assert (Hcc : edge_x_at e (py c) = px c)
    by (exact (carrier_at_corner e c w_e HorE' Hwe)).
  assert (Hcw : edge_x_at e (py w_e) = px w_e)
    by (exact (carrier_at_far e c w_e HorE' Hwe)).
  destruct (incident_pair r e f c w_e w_f Hnd Hine Hinf HorE HorF Hwf Hwe
              g Hing Hinc) as [Hg | Hg]; subst g.
  - destruct HorE as [HE | HE]; subst e; cbn [fst snd] in *;
      split; intro Hyy; lra.
  - destruct HorF as [HF | HF]; subst f; cbn [fst snd] in *;
      split; intro Hyy; lra.
Qed.

(* The eastmost vertex has an outgoing edge. *)
Lemma vertex_out_edge : forall (r : Ring) (v : Point),
  ring_core_nodup r ->
  no_horizontal_edges r ->
  In v r ->
  exists bb, In (v, bb) (ring_edges r).
Proof.
  intros r v Hnd Hnoh HIn.
  pose proof Hnd as [p0 [ps [Hr Hndps]]].
  destruct (in_split v r HIn) as [l1 [l2 Hs]].
  destruct l2 as [| w l2'].
  - (* v is the closing vertex: v = p0, the first edge starts at it *)
    assert (Hvp : v = p0).
    { assert (H1 : last r p0 = v)
        by (rewrite Hs; apply last_snoc).
      assert (H2 : last r p0 = p0).
      { rewrite Hr. cbn [last].
        destruct (ps ++ [p0]) eqn:Hl; [ destruct ps; discriminate | ].
        rewrite <- Hl. apply last_snoc. }
      congruence. }
    subst v.
    destruct ps as [| q0 ps'].
    + exfalso.
      assert (Hin' : In (p0, p0) (ring_edges r))
        by (rewrite Hr; cbn; auto).
      pose proof (Hnoh (p0, p0) Hin'). cbn in *. lra.
    + exists q0.
      apply ring_edges_in_split. exists [], (ps' ++ [p0]).
      rewrite Hr. reflexivity.
  - exists w.
    apply ring_edges_in_split. exists l1, l2'. exact Hs.
Qed.

(* The payoff pulls back through the y-flip (counts and guards are
   y-exact, rung 5b). *)
Lemma payoff_ymir : forall (r : Ring) (p : Point),
  payoff (map ymir r) (ymir p) -> payoff r p.
Proof.
  intros r p [z' [Hconn [Hcompl [Hguard Hcount]]]].
  set (z := ymir z').
  assert (Hz' : z' = ymir z)
    by (unfold z; rewrite ymir_invol; reflexivity).
  rewrite Hz' in Hconn, Hcompl, Hguard, Hcount.
  assert (Hguardz : ray_avoids_vertices z r)
    by (exact (guard_ymir_rev r z Hguard)).
  exists z. split; [ | split; [ | split ] ].
  - exact (connected_ymir_rev r p z Hconn).
  - exact (proj1 (ring_complement_ymir r z) Hcompl).
  - exact Hguardz.
  - rewrite (ho_count_ymir r z Hguardz) in Hcount. exact Hcount.
Qed.

(* ---------------------------------------------------------------------------
   §1  The east-hug wedge probe at a pinched minimum.
   --------------------------------------------------------------------------- *)

Lemma payoff_wedge_min_east : forall (r : Ring) (E E' : Edge)
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
  edge_x_at E (py w') < px w' ->
  hugs_east r E p ->
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
  set (KE := (px w - px vS) / (py w - py vS)).
  set (KF := (px w' - px vS) / (py w' - py vS)).
  assert (HlinE : forall y, edge_x_at E y = px vS + KE * (y - py vS)).
  { intro y. destruct HorEn as [HE | HE]; subst E;
      unfold edge_x_at, KE; cbn [fst snd]; field; lra. }
  assert (HlinF : forall y, edge_x_at E' y = px vS + KF * (y - py vS)).
  { intro y. destruct HorE'n as [HE' | HE']; subst E';
      unfold edge_x_at, KF; cbn [fst snd]; field; lra. }
  assert (HKlt : KE < KF).
  { apply Rmult_lt_reg_r with (py w' - py vS); [ lra | ].
    assert (HKF1 : KF * (py w' - py vS) = px w' - px vS)
      by (unfold KF; field; lra).
    rewrite (HlinE (py w')) in Hpin. nra. }
  pose proof (Rle_abs KE) as HKEa. pose proof (Rabs_pos KE) as HKEp.
  assert (HKEa' : - Rabs KE <= KE)
    by (pose proof (Rle_abs (- KE)); rewrite Rabs_Ropp in *; lra).
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
  assert (HKeps : Rabs KE * eps0 <= rad / 2).
  { assert (HS2 : eps0 * (2 * (Rabs KE + 1)) <= rad).
    { replace rad with (rad / (2 * (Rabs KE + 1)) * (2 * (Rabs KE + 1)))
        by (field; nra).
      apply Rmult_le_compat_r; nra. }
    nra. }
  assert (Heps0rad : eps0 <= rad / 2).
  { assert (rad / (2 * (Rabs KE + 1)) <= rad / 2).
    { apply Rmult_le_reg_r with (2 * (Rabs KE + 1)); [ nra | ].
      replace (rad / (2 * (Rabs KE + 1)) * (2 * (Rabs KE + 1))) with rad
        by (field; nra).
      nra. }
    lra. }
  assert (HspanE : (py (fst E) < ystar /\ yE < py (snd E)) \/
                   (py (snd E) < ystar /\ yE < py (fst E)))
    by (unfold ystar; destruct HorEn as [HE | HE]; subst E; cbn in *;
        [ left | right ]; lra).
  destruct (wall_corridor_clear_east r E ystar yE Htaut HinE HspanE
              ltac:(unfold ystar; lra))
    as [dA [HdA HfreeA]].
  set (capW := (KF - KE) * eps0 / 3).
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
  set (z := mkPoint (edge_x_at E ystar + del) ystar).
  assert (Hzx : px z = px vS + KE * eps0 + del)
    by (unfold z; cbn [px]; rewrite (HlinE ystar); unfold ystar; ring).
  assert (HzxF : edge_x_at E' ystar = px vS + KF * eps0)
    by (rewrite (HlinF ystar); unfold ystar; ring).
  (* the moves *)
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
    apply (corridor_connected_east r E ystar yE del HnhE
             ltac:(unfold ystar; lra)).
    intros y Hy. apply (HfreeA del ltac:(lra)). lra. }
  assert (Hchain : connected_in_complement_cont r p z).
  { apply (connected_in_complement_cont_trans r p
             (mkPoint (edge_x_at E (mid E) + del) (mid E))).
    - apply (connected_in_complement_cont_trans r p
               (mkPoint (edge_x_at E (mid E) + dS) (mid E)));
        [ exact HconnS | exact Hjog ].
    - exact Hride. }
  (* the count: exactly the EAST wall E' crosses *)
  assert (Hiff : forall g, In g (ring_edges r) ->
            (edge_crosses_ray_ho z g <-> g = E')).
  { intros g Hing. split.
    - intro Hc.
      destruct (coord_point_dec (fst g) vS) as [Hfv | Hfv].
      { destruct (incident_pair_min r E E' vS w w' Hnd Hne HinE HinE'
                    HorE HorE' Hvw Hvw' g Hing (or_introl Hfv))
          as [Hg | Hg]; [ exfalso; subst g | exact Hg ].
        apply (carrier_west_nocross z E HnhE); [ | exact Hc ].
        unfold z; cbn [px py].
        lra. }
      destruct (coord_point_dec (snd g) vS) as [Hsv | Hsv].
      { destruct (incident_pair_min r E E' vS w w' Hnd Hne HinE HinE'
                    HorE HorE' Hvw Hvw' g Hing (or_intror Hsv))
          as [Hg | Hg]; [ exfalso; subst g | exact Hg ].
        apply (carrier_west_nocross z E HnhE); [ | exact Hc ].
        unfold z; cbn [px py].
        lra. }
      exfalso.
      assert (HzxLo : px vS - rad < px z).
      { rewrite Hzx.
        assert (T1 : - (rad / 2) <= KE * eps0) by nra.
        lra. }
      apply (noncross_far r g vS z rad Hing Hub
               (fun x y Hx Hy => Hdisk rad Hrad g Hing Hfv Hsv x y Hx Hy)
               ltac:(unfold z; cbn [py]; unfold ystar; lra)
               HzxLo
               Hc).
    - intro Hg. subst g.
      apply carrier_east_cross.
      + destruct HorE' as [HE' | HE']; subst E'; cbn [fst snd];
          unfold z; cbn [py]; unfold ystar;
          [ left | right ]; lra.
      + unfold z; cbn [px py].
        rewrite HzxF, (HlinE ystar). unfold ystar, capW in *. nra.
  }
  exists z. split; [ exact Hchain | ]. split; [ | split ].
  - intro Himg.
    apply (HfreeA del ltac:(lra) ystar ltac:(unfold ystar; lra)).
    exact Himg.
  - apply (guard_of_fresh_level r z (py vS));
      unfold z; cbn [py]; unfold ystar; lra.
  - right.
    destruct HorE' as [HE' | HE']; subst E'.
    + exact (ho_count_one_out r z vS w' Hnd HinE' Hiff).
    + exact (ho_count_one_in r z w' vS Hnd HinE' Hiff).
Qed.

(* ---------------------------------------------------------------------------
   §2  The dispatches.
   --------------------------------------------------------------------------- *)

(* A pass-through corner: ride the ascending edge on whichever side. *)
Lemma payoff_pt_dispatch : forall (r : Ring) (EU ED : Edge)
                                  (vS u d : Point) (p : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  In EU (ring_edges r) -> In ED (ring_edges r) ->
  EU = (u, vS) \/ EU = (vS, u) ->
  ED = (vS, d) \/ ED = (d, vS) ->
  py vS < py u -> py d < py vS ->
  (forall q, In q r -> px q <= px vS) ->
  hugs r EU p ->
  payoff r p.
Proof.
  intros r EU ED vS u d p Htaut Hnd Hnoh HinU HinD HorU HorD Hu Hd Hub
    Hhug.
  destruct Hhug as [Hw | He].
  - exact (payoff_west_ride_pt r EU ED vS u d p Htaut Hnd Hnoh HinU HinD
             HorU HorD Hu Hd Hub
             (opens_east_pass_down r EU ED vS u d Hnd HinU HinD HorU HorD
                Hd Hu) Hw).
  - exact (payoff_east_ride r EU vS u p Htaut HinU HorU Hu Hub
             (opens_west_pass_down r EU ED vS u d Hnd HinU HinD HorU HorD
                Hd Hu) He).
Qed.

(* A local minimum: open side rides, pinched side probes the wedge. *)
Lemma payoff_min_dispatch : forall (r : Ring) (a b vS : Point) (p : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  In (a, vS) (ring_edges r) -> In (vS, b) (ring_edges r) ->
  py vS < py a -> py vS < py b ->
  (forall q, In q r -> px q <= px vS) ->
  hugs r (a, vS) p ->
  payoff r p.
Proof.
  intros r a b vS p Htaut Hnd Hnoh HinI HinO Ha Hb Hub Hhug.
  assert (Hne : (a, vS) <> (vS, b)).
  { intro He. injection He as H1 H2.
    pose proof (Hnoh (vS, b) HinO) as Hh. cbn in Hh.
    apply Hh. rewrite H2. reflexivity. }
  assert (Hsame : (py a - py vS) * (py b - py vS) > 0) by nra.
  pose proof (corner_slopes_distinct r (a, vS) (vS, b) vS a b Htaut Hne
                HinI HinO (or_introl eq_refl) (or_introl eq_refl)
                ltac:(cbn; lra) ltac:(cbn; lra) Hsame) as Hneq.
  destruct (Rle_dec (edge_x_at (a, vS) (py b)) (px b)) as [Hside | Hside].
  - (* the out-edge is weakly (hence strictly) east of the in-carrier *)
    destruct Hhug as [Hw | He].
    + exact (payoff_passage_min r (a, vS) (vS, b) vS a b p Htaut Hnd Hnoh
               Hne HinI HinO (or_introl eq_refl) (or_introl eq_refl)
               Ha Hb Hub
               (opens_east_min r (a, vS) (vS, b) vS a b Hnd Hne HinI HinO
                  (or_introl eq_refl) (or_introl eq_refl) Ha Hb Hside)
               Hw).
    + apply (payoff_wedge_min_east r (a, vS) (vS, b) vS a b p Htaut Hnd
               Hnoh Hne HinI HinO (or_introl eq_refl) (or_introl eq_refl)
               Ha Hb Hub ltac:(lra) He).
  - (* the out-edge is strictly west of the in-carrier *)
    destruct Hhug as [Hw | He].
    + apply (payoff_wedge_min r (a, vS) (vS, b) vS a b p Htaut Hnd Hnoh
               Hne HinI HinO (or_introl eq_refl) (or_introl eq_refl)
               Ha Hb Hub ltac:(lra) Hw).
    + apply (payoff_east_ride r (a, vS) vS a p Htaut HinI
               (or_introl eq_refl) Ha Hub).
      * apply (opens_west_min r (vS, b) (a, vS) vS b a Hnd
                 ltac:(intro Hc; apply Hne; symmetry; exact Hc)
                 HinO HinI (or_intror eq_refl) (or_intror eq_refl)
                 Hb Ha ltac:(lra)).
      * exact He.
Qed.

(* THE EASTMOST DISPATCH: hugging both incidents of the eastmost vertex
   always pays off. *)
Lemma eastmost_payoff : forall (r : Ring) (a b vS : Point) (p : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  In (a, vS) (ring_edges r) -> In (vS, b) (ring_edges r) ->
  (forall q, In q r -> px q <= px vS) ->
  hugs r (a, vS) p -> hugs r (vS, b) p ->
  payoff r p.
Proof.
  intros r a b vS p Htaut Hnd Hnoh HinI HinO Hub HhugI HhugO.
  assert (Hna : py a <> py vS)
    by (pose proof (Hnoh (a, vS) HinI); cbn in *; lra).
  assert (Hnb : py b <> py vS)
    by (pose proof (Hnoh (vS, b) HinO); cbn in *; lra).
  destruct (Rlt_le_dec (py vS) (py a)) as [HaU | HaD];
  destruct (Rlt_le_dec (py vS) (py b)) as [HbU | HbD].
  - (* local minimum *)
    exact (payoff_min_dispatch r a b vS p Htaut Hnd Hnoh HinI HinO
             HaU HbU Hub HhugI).
  - (* pass-through down: the in-edge ascends *)
    exact (payoff_pt_dispatch r (a, vS) (vS, b) vS a b p Htaut Hnd Hnoh
             HinI HinO (or_introl eq_refl) (or_introl eq_refl)
             HaU ltac:(lra) Hub HhugI).
  - (* pass-through up: the out-edge ascends *)
    exact (payoff_pt_dispatch r (vS, b) (a, vS) vS b a p Htaut Hnd Hnoh
             HinO HinI (or_intror eq_refl) (or_intror eq_refl)
             HbU ltac:(lra) Hub HhugO).
  - (* local maximum: the y-flip of a minimum *)
    apply payoff_ymir.
    assert (HinI' : In (ymir a, ymir vS) (ring_edges (map ymir r))).
    { rewrite ring_edges_map.
      exact (in_map (fun e0 => (ymir (fst e0), ymir (snd e0)))
               (ring_edges r) (a, vS) HinI). }
    assert (HinO' : In (ymir vS, ymir b) (ring_edges (map ymir r))).
    { rewrite ring_edges_map.
      exact (in_map (fun e0 => (ymir (fst e0), ymir (snd e0)))
               (ring_edges r) (vS, b) HinO). }
    apply (payoff_min_dispatch (map ymir r) (ymir a) (ymir b) (ymir vS)
             (ymir p)
             (ring_taut_ymir r Htaut)
             (ring_core_nodup_ymir r Hnd)
             (no_horizontal_ymir r Hnoh)
             HinI' HinO'
             ltac:(unfold ymir; cbn [py]; lra)
             ltac:(unfold ymir; cbn [py]; lra)).
    + intros q' Hq'.
      apply in_map_iff in Hq'. destruct Hq' as [q [Hq HInq]].
      subst q'. unfold ymir; cbn [px]. exact (Hub q HInq).
    + destruct HhugI as [Hw | He].
      * left. exact (hugs_west_ymir r a vS p ltac:(cbn; lra) Hw).
      * right. exact (hugs_east_ymir r a vS p ltac:(cbn; lra) He).
Qed.

(* ---------------------------------------------------------------------------
   §3  THE DESCENT, and H1.
   --------------------------------------------------------------------------- *)

Theorem escape_descent_holds : forall (r : Ring),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  escape_descent r.
Proof.
  intros r Htaut Hnd Hnoh p Hcompl Hrav Heven Hpos.
  (* the first wall and the entry hug *)
  destruct (ho_count_pos_ex p (ring_edges r) Hpos) as [e0 [Hine0 Hc0]].
  destruct (min_cross_x_some_of_cross p (ring_edges r) e0 Hine0 Hc0)
    as [X1 Hmin].
  destruct (min_cross_x_achieved p (ring_edges r) X1 Hmin)
    as [e1 [Hine1 [Hc1 HX1]]].
  pose proof (hug_entry r p e1 X1 Htaut Hcompl Hrav Hmin Hine1 Hc1 HX1)
    as Hentry.
  (* the eastmost corner pair *)
  assert (Hrne : r <> []).
  { destruct Hnd as [p0 [ps [Hr _]]]. rewrite Hr. discriminate. }
  destruct (vertex_xmax_achieved r Hrne) as [vS [HinvS Hub]].
  destruct (vertex_out_edge r vS Hnd Hnoh HinvS) as [b HinO].
  destruct (cyclic_prev r (vS, b) (ring_core_nodup_closed r Hnd) HinO)
    as [f [Hinf Hsndf]].
  cbn [fst] in Hsndf.
  assert (HinI : In (fst f, vS) (ring_edges r))
    by (rewrite <- Hsndf, <- surjective_pairing; exact Hinf).
  set (a := fst f).
  (* propagate the hug to both incidents *)
  assert (HhugI : hugs r (a, vS) p).
  { apply (hugs_everywhere r p e1 (a, vS) Htaut Hnd Hnoh Hine1 HinI).
    left. exact Hentry. }
  assert (HhugO : hugs r (vS, b) p).
  { apply (hugs_everywhere r p e1 (vS, b) Htaut Hnd Hnoh Hine1 HinO).
    left. exact Hentry. }
  (* the payoff *)
  destruct (eastmost_payoff r a b vS p Htaut Hnd Hnoh HinI HinO Hub
              HhugI HhugO) as [z [Hconn [Hcomplz [Hguardz Hcount]]]].
  destruct Hcount as [Hz0 | Hz1].
  - (* count zero: the descent's q *)
    exists z. split; [ exact Hconn | ]. split; [ exact Hguardz | ]. split.
    + destruct (ho_count_parity z (ring_edges r)) as [HEv _].
      apply HEv. rewrite Hz0. exists 0%nat. lia.
    + lia.
  - (* count one: odd -- the even walker cannot reach it *)
    exfalso.
    assert (Hoddz : ho_parity_odd z (ring_edges r)).
    { destruct (ho_count_parity z (ring_edges r)) as [_ HOd].
      apply HOd. rewrite Hz1. exists 0%nat. lia. }
    assert (Hpirz : point_in_ring z r)
      by (apply (point_in_ring_ho_agrees z r Hguardz); exact Hoddz).
    assert (Hpirp : point_in_ring p r).
    { apply (parity_constant_on_components r p z
               (ring_core_nodup_closed r Hnd) Hrav Hguardz Hconn).
      exact Hpirz. }
    apply (proj2 (point_in_ring_ho_agrees p r Hrav)) in Hpirp.
    exact (ho_parity_excl p (ring_edges r) Hpirp Heven).
Qed.

(* ============================================================================
   H1, CLOSED: the corrected polygonal Jordan seam holds outright for
   taut, proper, horizontal-free rings -- every premise a theorem, no
   stub, no named hypothesis, three axioms.
   ========================================================================== *)

Theorem parity_seam_offring_taut : forall (r : Ring) (p : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  parity_characterises_interior_cont_offring p r.
Proof.
  intros r p Htaut Hnd Hnoh.
  apply parity_seam_offring_of_descent.
  exact (escape_descent_holds r Htaut Hnd Hnoh).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions escape_descent_holds.
Print Assumptions parity_seam_offring_taut.
