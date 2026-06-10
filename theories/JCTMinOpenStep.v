(* ============================================================================
   NetTopologySuite.Proofs.JCTMinOpenStep
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-8: THE OPEN-SIDE LOCAL-MINIMUM COMPOSITE.  At a
   local minimum c (both cycle edges climb out of c), the boundary turns
   around; the walker on the OPEN side -- west of the arriving edge e with
   the departing edge f weakly east of e's carrier -- rounds the tip:

     jog . corner_passage_fresh (down e's west side, into the west band)
     . under_tip_crossing (across the corner, beneath the tip)
     . east corner box (up through the band east of the corner)
     . east corner-abutting rise (up f's EAST side to mid f).

   The hug side flips, as it must: right-of-travel is west on a descent
   and east on an ascent (`hugs_west e -> hugs_east f`).  The open-side
   conditions are two carrier-line comparisons -- f's far endpoint weakly
   east of e's carrier (so the west passage clears) and e's far endpoint
   weakly west of f's carrier (so the east rise clears); at a genuine
   local minimum exactly one of open/pinched holds per side, and the
   traversal will decide it by `Rle_dec`.

   Degree-2 housekeeping: `incident_pair_min` (both edges climb, so two
   in-edges or two out-edges at c would coincide -- excluded by e <> f).
   East-side gap-fillers (x-flip pullbacks): `wall_corridor_clear_east`
   (rung 4b-2), `wall_corridor_clear_corner_east` (rung 5a),
   `corridor_connected_east` (rung 2), and `foot_abscissa_bound` (the
   two-sided abscissa pin at a corner's foot).

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
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  East-side gap-fillers (x-flip pullbacks).
   --------------------------------------------------------------------------- *)

(* The x-flip of rung 4b-2's wall theorem: uniform delta0 for the EAST
   corridor on a span-interior window. *)
Theorem wall_corridor_clear_east : forall (r : Ring) (e1 : Edge)
                                          (ylo yhi : R),
  ring_taut r ->
  In e1 (ring_edges r) ->
  ((py (fst e1) < ylo /\ yhi < py (snd e1)) \/
   (py (snd e1) < ylo /\ yhi < py (fst e1))) ->
  ylo <= yhi ->
  exists delta0, 0 < delta0 /\
    forall delta, 0 < delta < delta0 ->
      forall y, ylo <= y <= yhi ->
        ~ ring_image r (mkPoint (edge_x_at e1 y + delta) y).
Proof.
  intros r e1 ylo yhi Htaut Hin Hspan Hle.
  destruct e1 as [ea eb].
  assert (Hnh : py ea <> py eb) by (cbn in Hspan; lra).
  set (r' := map xmir r).
  set (e1' := (xmir ea, xmir eb)).
  assert (Htaut' : ring_taut r') by (apply ring_taut_xmir; exact Htaut).
  assert (Hin' : In e1' (ring_edges r')).
  { unfold r'. rewrite ring_edges_map.
    exact (in_map (fun e0 => (xmir (fst e0), xmir (snd e0)))
             (ring_edges r) (ea, eb) Hin). }
  assert (Hspan' : (py (fst e1') < ylo /\ yhi < py (snd e1')) \/
                   (py (snd e1') < ylo /\ yhi < py (fst e1'))).
  { unfold e1', xmir; cbn [fst snd py] in *. exact Hspan. }
  destruct (wall_corridor_clear r' e1' ylo yhi Htaut' Hin' Hspan' Hle)
    as [delta0 [Hd0 Hfree]].
  exists delta0. split; [ exact Hd0 | ].
  intros delta Hd y Hy Himg.
  apply (Hfree delta Hd y Hy).
  unfold e1'.
  rewrite (corridor_xmir ea eb delta y Hnh).
  apply (ring_image_xmir r _). exact Himg.
Qed.

(* The x-flip of rung 5a's corner-abutting clearance: uniform delta0 for
   the EAST corridor on a window abutting the bottom vertex. *)
Theorem wall_corridor_clear_corner_east : forall (r : Ring) (e1 : Edge)
                                                 (v w : Point) (yhi : R),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  py v <= yhi ->
  yhi < py w ->
  corner_opens_west r e1 v ->
  exists delta0, 0 < delta0 /\
    forall delta, 0 < delta < delta0 ->
      forall y, py v < y <= yhi ->
        ~ ring_image r (mkPoint (edge_x_at e1 y + delta) y).
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
    exact (in_map (fun e0 => (xmir (fst e0), xmir (snd e0)))
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
  destruct (wall_corridor_clear_corner r' e1' (xmir v) (xmir w) yhi
              Htaut' Hin' Hor'
              ltac:(unfold xmir; cbn [py]; lra)
              ltac:(unfold xmir; cbn [py]; lra)
              ltac:(unfold xmir; cbn [py]; lra)
              Hopen') as [delta0 [Hd0 Hfree]].
  exists delta0. split; [ exact Hd0 | ].
  intros delta Hd y Hy Himg.
  apply (Hfree delta Hd y ltac:(unfold xmir; cbn [py]; lra)).
  unfold e1'.
  rewrite (corridor_xmir ea eb delta y Hnh).
  apply (ring_image_xmir r _). exact Himg.
Qed.

(* The x-flip of the rung-2 corridor path: the EAST corridor is connected
   under pointwise freedom. *)
Lemma corridor_connected_east : forall (r : Ring) (e1 : Edge)
                                       (ylo yhi delta : R),
  py (fst e1) <> py (snd e1) ->
  ylo <= yhi ->
  (forall y, ylo <= y <= yhi ->
     ~ ring_image r (mkPoint (edge_x_at e1 y + delta) y)) ->
  connected_in_complement_cont r
    (mkPoint (edge_x_at e1 yhi + delta) yhi)
    (mkPoint (edge_x_at e1 ylo + delta) ylo).
Proof.
  intros r e1 ylo yhi delta Hnh Hle Hfree.
  destruct e1 as [ea eb]. cbn [fst snd] in Hnh.
  set (r' := map xmir r).
  assert (Hfree' : forall y, ylo <= y <= yhi ->
            ~ ring_image r' (corridor (xmir ea, xmir eb) delta y)).
  { intros y Hy Himg.
    apply (Hfree y Hy).
    rewrite (corridor_xmir ea eb delta y Hnh) in Himg.
    apply (ring_image_xmir r _). exact Himg. }
  pose proof (corridor_connected r' (xmir ea, xmir eb) ylo yhi delta
                ltac:(unfold xmir; cbn [fst snd py]; exact Hnh)
                Hle Hfree') as Hconn.
  rewrite (corridor_xmir ea eb delta yhi Hnh) in Hconn.
  rewrite (corridor_xmir ea eb delta ylo Hnh) in Hconn.
  exact (connected_xmir_rev r _ _ Hconn).
Qed.

(* The two-sided abscissa pin at a corner's foot. *)
Lemma foot_abscissa_bound : forall (v w : Point) (delta eps : R),
  py v < py w -> 0 < delta -> 0 < eps ->
  2 * eps * (Rabs (px w - px v) + 1) < delta * (py w - py v) ->
  px v - delta / 2 <= edge_x_at (v, w) (py v + eps) <= px v + delta / 2.
Proof.
  intros v w delta eps Hvw Hd He Hcap.
  unfold edge_x_at.
  set (qq := (px w - px v) * (py v + eps - py v) / (py w - py v)).
  assert (Hq : qq * (py w - py v) = (px w - px v) * eps)
    by (unfold qq; field; lra).
  destruct (Rcase_abs (px w - px v)) as [Hc | Hc].
  - rewrite (Rabs_left (px w - px v) Hc) in Hcap.
    assert (Hb1 : - (delta / 2) * (py w - py v) <= qq * (py w - py v))
      by nra.
    assert (Hb2 : qq * (py w - py v) <= 0) by nra.
    split; nra.
  - rewrite (Rabs_right (px w - px v) Hc) in Hcap.
    assert (Hb1 : 0 <= qq * (py w - py v)) by nra.
    assert (Hb2 : qq * (py w - py v) <= (delta / 2) * (py w - py v))
      by nra.
    split; nra.
Qed.

(* ---------------------------------------------------------------------------
   §1  Degree-2 housekeeping at a local minimum.
   --------------------------------------------------------------------------- *)

Lemma incident_pair_min : forall (r : Ring) (e f : Edge) (c w_e w_f : Point),
  ring_core_nodup r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py c < py w_e -> py c < py w_f ->
  forall g, In g (ring_edges r) -> fst g = c \/ snd g = c ->
  g = e \/ g = f.
Proof.
  intros r e f c w_e w_f Hnd Hne Hine Hinf HorE HorF Hwe Hwf g Hing Hinc.
  destruct HorE as [HE | HE]; destruct HorF as [HF | HF]; subst e f.
  - exact (incident_two r (w_e, c) (c, w_f) g c Hnd Hine eq_refl
             Hinf eq_refl Hing Hinc).
  - exfalso.
    pose proof (in_edge_unique r w_e w_f c Hnd Hine Hinf). subst w_f.
    exact (Hne eq_refl).
  - exfalso.
    pose proof (out_edge_unique r w_e w_f c Hnd Hine Hinf). subst w_f.
    exact (Hne eq_refl).
  - destruct (incident_two r (w_f, c) (c, w_e) g c Hnd Hinf eq_refl
                Hine eq_refl Hing Hinc) as [H | H]; [ right | left ];
      exact H.
Qed.

Lemma opens_east_min : forall (r : Ring) (e f : Edge) (c w_e w_f : Point),
  ring_core_nodup r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py c < py w_e -> py c < py w_f ->
  edge_x_at e (py w_f) <= px w_f ->
  corner_opens_east r e c.
Proof.
  intros r e f c w_e w_f Hnd Hne Hine Hinf HorE HorF Hwe Hwf Hop
    g Hing Hinc.
  assert (HorE' : e = (c, w_e) \/ e = (w_e, c)) by tauto.
  assert (Hcc : edge_x_at e (py c) = px c)
    by (exact (carrier_at_corner e c w_e HorE' Hwe)).
  assert (Hcw : edge_x_at e (py w_e) = px w_e)
    by (exact (carrier_at_far e c w_e HorE' Hwe)).
  destruct (incident_pair_min r e f c w_e w_f Hnd Hne Hine Hinf HorE HorF
              Hwe Hwf g Hing Hinc) as [Hg | Hg]; subst g.
  - destruct HorE as [HE | HE]; subst e; cbn [fst snd] in *;
      split; intro Hyy; lra.
  - destruct HorF as [HF | HF]; subst f; cbn [fst snd] in *;
      split; intro Hyy; lra.
Qed.

Lemma opens_west_min : forall (r : Ring) (e f : Edge) (c w_e w_f : Point),
  ring_core_nodup r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py c < py w_e -> py c < py w_f ->
  px w_e <= edge_x_at f (py w_e) ->
  corner_opens_west r f c.
Proof.
  intros r e f c w_e w_f Hnd Hne Hine Hinf HorE HorF Hwe Hwf Hop
    g Hing Hinc.
  assert (HorF' : f = (c, w_f) \/ f = (w_f, c)) by tauto.
  assert (Hcc : edge_x_at f (py c) = px c)
    by (exact (carrier_at_corner f c w_f HorF' Hwf)).
  assert (Hcw : edge_x_at f (py w_f) = px w_f)
    by (exact (carrier_at_far f c w_f HorF' Hwf)).
  destruct (incident_pair_min r e f c w_e w_f Hnd Hne Hine Hinf HorE HorF
              Hwe Hwf g Hing Hinc) as [Hg | Hg]; subst g.
  - destruct HorE as [HE | HE]; subst e; cbn [fst snd] in *;
      split; intro Hyy; lra.
  - destruct HorF as [HF | HF]; subst f; cbn [fst snd] in *;
      split; intro Hyy; lra.
Qed.

(* ---------------------------------------------------------------------------
   §2  THE COMPOSITE: the open-side local minimum, west in, east out.
   --------------------------------------------------------------------------- *)

Theorem hug_step_min_open_we : forall (r : Ring) (e f : Edge)
                                      (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py c < py w_e -> py c < py w_f ->
  edge_x_at e (py w_f) <= px w_f ->
  px w_e <= edge_x_at f (py w_e) ->
  hugs_west r e q ->
  hugs_east r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hnef Hine Hinf HorE HorF
    Hwe Hwf HopE HopW Hhug.
  destruct Hhug as [Hq [dS [HdS [HfreeS HconnS]]]].
  assert (HorE' : e = (c, w_e) \/ e = (w_e, c)) by tauto.
  assert (HnhE : py (fst e) <> py (snd e))
    by (destruct HorE as [HE | HE]; subst e; cbn; lra).
  assert (HnhF : py (fst f) <> py (snd f))
    by (destruct HorF as [HF | HF]; subst f; cbn; lra).
  assert (HopenE : corner_opens_east r e c)
    by (exact (opens_east_min r e f c w_e w_f Hnd Hnef Hine Hinf
                 HorE HorF Hwe Hwf HopE)).
  assert (HopenW : corner_opens_west r f c)
    by (exact (opens_west_min r e f c w_e w_f Hnd Hnef Hine Hinf
                 HorE HorF Hwe Hwf HopW)).
  assert (Hmin : forall g, In g (ring_edges r) ->
            fst g = c \/ snd g = c ->
            py c <= py (fst g) /\ py c <= py (snd g)).
  { intros g Hing Hinc.
    destruct (incident_pair_min r e f c w_e w_f Hnd Hnef Hine Hinf
                HorE HorF Hwe Hwf g Hing Hinc) as [Hg | Hg]; subst g.
    - destruct HorE as [HE | HE]; subst e; cbn [fst snd]; lra.
    - destruct HorF as [HF | HF]; subst f; cbn [fst snd]; lra. }
  assert (HezE : forall g, In g (ring_edges r) ->
            py (fst g) = py (snd g) -> fst g = c \/ snd g = c ->
            px (fst g) <= px c /\ px (snd g) <= px c)
    by (intros g Hing Hflat _; exfalso; exact (Hnoh g Hing Hflat)).
  set (yE := mid e). set (yF := mid f).
  assert (HyE : py c < yE < py w_e)
    by (unfold yE, mid; destruct HorE as [HE | HE]; subst e; cbn; lra).
  assert (HyF : py c < yF < py w_f)
    by (unfold yF, mid; destruct HorF as [HF | HF]; subst f; cbn; lra).
  (* stage-1 thresholds *)
  destruct (corner_passage_fresh r e c w_e yE Htaut Hine HorE'
              ltac:(lra) ltac:(lra) ltac:(lra) HopenE)
    as [dP [HdP HstageP]].
  destruct (under_tip_crossing r e c w_e Htaut Hine HorE' Hmin)
    as [dU [HdU HstageU]].
  destruct (corner_box_east_clear r f c w_f Htaut Hinf HorF
              ltac:(lra) HezE)
    as [dBe [HdBe HstageBe]].
  destruct (wall_corridor_clear_corner_east r f c w_f yF Htaut Hinf HorF
              ltac:(lra) ltac:(lra) ltac:(lra) HopenW)
    as [dE [HdE HfreeE]].
  assert (HspanF : (py (fst f) < yF /\ yF < py (snd f)) \/
                   (py (snd f) < yF /\ yF < py (fst f)))
    by (destruct HorF as [HF | HF]; subst f; cbn in *; [ left | right ]; lra).
  destruct (wall_corridor_clear_east r f yF yF Htaut Hinf HspanF
              ltac:(lra))
    as [dM [HdM HfreeM]].
  set (del := Rmin (Rmin dS dP) (Rmin (Rmin dU dBe) (Rmin dE dM)) / 2).
  assert (Hdel : 0 < del /\ del < dS /\ del < dP /\ del < dU /\
                 del < dBe /\ del < dE /\ del < dM).
  { unfold del.
    pose proof (Rmin_l dS dP). pose proof (Rmin_r dS dP).
    pose proof (Rmin_l dU dBe). pose proof (Rmin_r dU dBe).
    pose proof (Rmin_l dE dM). pose proof (Rmin_r dE dM).
    pose proof (Rmin_l (Rmin dU dBe) (Rmin dE dM)).
    pose proof (Rmin_r (Rmin dU dBe) (Rmin dE dM)).
    pose proof (Rmin_l (Rmin dS dP) (Rmin (Rmin dU dBe) (Rmin dE dM))).
    pose proof (Rmin_r (Rmin dS dP) (Rmin (Rmin dU dBe) (Rmin dE dM))).
    assert (0 < Rmin (Rmin dS dP) (Rmin (Rmin dU dBe) (Rmin dE dM))).
    { apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | ].
      apply Rmin_glb_lt; apply Rmin_glb_lt; lra. }
    repeat split; lra. }
  destruct Hdel as [Hdel0 [HdelS [HdelP [HdelU [HdelBe [HdelE HdelM]]]]]].
  (* stage-2 thresholds *)
  destruct (HstageP del ltac:(lra)) as [eP [HeP HpassP]].
  destruct (HstageU del ltac:(lra)) as [eU [HeU HcrossU]].
  destruct (HstageBe del ltac:(lra)) as [eBe [HeBe HboxBe]].
  pose proof (Rabs_pos (px w_e - px c)) as HAe.
  pose proof (Rabs_pos (px w_f - px c)) as HAf.
  set (capE := del * (py w_e - py c) / (2 * (Rabs (px w_e - px c) + 1))).
  set (capF := del * (py w_f - py c) / (2 * (Rabs (px w_f - px c) + 1))).
  assert (HcapE : 0 < capE)
    by (unfold capE; apply Rdiv_lt_0_compat; nra).
  assert (HcapF : 0 < capF)
    by (unfold capF; apply Rdiv_lt_0_compat; nra).
  set (eps := Rmin (Rmin eP eU) (Rmin (Rmin eBe capE) (Rmin capF (yF - py c)))
                / 2).
  assert (Heps : 0 < eps /\ eps < eP /\ eps < eU /\ eps < eBe /\
                 eps < capE /\ eps < capF /\ eps < yF - py c).
  { unfold eps.
    pose proof (Rmin_l eP eU). pose proof (Rmin_r eP eU).
    pose proof (Rmin_l eBe capE). pose proof (Rmin_r eBe capE).
    pose proof (Rmin_l capF (yF - py c)). pose proof (Rmin_r capF (yF - py c)).
    pose proof (Rmin_l (Rmin eBe capE) (Rmin capF (yF - py c))).
    pose proof (Rmin_r (Rmin eBe capE) (Rmin capF (yF - py c))).
    pose proof (Rmin_l (Rmin eP eU)
                  (Rmin (Rmin eBe capE) (Rmin capF (yF - py c)))).
    pose proof (Rmin_r (Rmin eP eU)
                  (Rmin (Rmin eBe capE) (Rmin capF (yF - py c)))).
    assert (0 < Rmin (Rmin eP eU)
                  (Rmin (Rmin eBe capE) (Rmin capF (yF - py c)))).
    { apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | ].
      apply Rmin_glb_lt; apply Rmin_glb_lt; lra. }
    repeat split; lra. }
  destruct Heps as [Heps0 [HepsP [HepsU [HepsBe [HepsE [HepsF HepsYF]]]]]].
  (* abscissa products and pins *)
  assert (HprodE : 2 * eps * (Rabs (px w_e - px c) + 1)
                     < del * (py w_e - py c)).
  { apply (cap_mult eps _ (2 * (Rabs (px w_e - px c) + 1))
             ltac:(nra)) in HepsE.
    unfold capE in HepsE. lra. }
  assert (HprodF : 2 * eps * (Rabs (px w_f - px c) + 1)
                     < del * (py w_f - py c)).
  { apply (cap_mult eps _ (2 * (Rabs (px w_f - px c) + 1))
             ltac:(nra)) in HepsF.
    unfold capF in HepsF. lra. }
  assert (HbndE : px c - 2 * del <= edge_x_at e (py c + eps) - del
                    <= px c - del / 2).
  { destruct HorE' as [HE | HE]; subst e.
    - exact (drop_abscissa_bound c w_e del eps Hwe ltac:(lra) ltac:(lra)
               HprodE).
    - rewrite <- (edge_x_at_swap c w_e (py c + eps) ltac:(lra)).
      exact (drop_abscissa_bound c w_e del eps Hwe ltac:(lra) ltac:(lra)
               HprodE). }
  assert (HbndF : px c - del / 2 <= edge_x_at f (py c + eps)
                    <= px c + del / 2).
  { destruct HorF as [HF | HF]; subst f.
    - exact (foot_abscissa_bound c w_f del eps Hwf ltac:(lra) ltac:(lra)
               HprodF).
    - rewrite <- (edge_x_at_swap c w_f (py c + eps) ltac:(lra)).
      exact (foot_abscissa_bound c w_f del eps Hwf ltac:(lra) ltac:(lra)
               HprodF). }
  (* the moves *)
  destruct (HpassP eps ltac:(lra)) as [HconnP [_ [HcomplP1 _]]].
  assert (Hjog : connected_in_complement_cont r
            (corridor e del (mid e)) (corridor e dS (mid e))).
  { apply (corridor_offset_jog r e (mid e) del dS ltac:(lra)).
    intros d' Hd'. apply HfreeS. lra. }
  destruct (HcrossU eps ltac:(lra)
              (edge_x_at e (py c + eps) - del)
              (edge_x_at f (py c + eps) + del)
              ltac:(lra) ltac:(lra)) as [Htip _].
  assert (HboxConn : connected_in_complement_cont r
            (mkPoint (edge_x_at f (py c + eps) + del) (py c - eps))
            (mkPoint (edge_x_at f (py c + eps) + del) (py c + eps))).
  { apply (box_connected_of_clear r (px c + del / 2) (px c + 2 * del)
             (py c - eps) (py c + eps)
             ltac:(intros x y Hx Hy;
                   exact (HboxBe eps ltac:(lra) x y Hx Hy)));
      split; lra. }
  assert (HriseF : connected_in_complement_cont r
            (mkPoint (edge_x_at f yF + del) yF)
            (mkPoint (edge_x_at f (py c + eps) + del) (py c + eps))).
  { apply (corridor_connected_east r f (py c + eps) yF del HnhF
             ltac:(lra)).
    intros y Hy. apply (HfreeE del ltac:(lra)). lra. }
  assert (Hchain : connected_in_complement_cont r q
            (mkPoint (edge_x_at f yF + del) yF)).
  { apply (connected_in_complement_cont_trans r q
             (corridor e del (mid e))).
    - apply (connected_in_complement_cont_trans r q
               (corridor e dS (mid e))); [ exact HconnS | ].
      apply connected_in_complement_cont_sym. exact Hjog.
    - apply (connected_in_complement_cont_trans r _
               (mkPoint (edge_x_at e (py c + eps) - del) (py c - eps))).
      + exact HconnP.
      + apply (connected_in_complement_cont_trans r _
                 (mkPoint (edge_x_at f (py c + eps) + del) (py c - eps))).
        * exact Htip.
        * apply (connected_in_complement_cont_trans r _
                   (mkPoint (edge_x_at f (py c + eps) + del) (py c + eps))).
          { exact HboxConn. }
          { apply connected_in_complement_cont_sym. exact HriseF. } }
  split; [ exact Hq | ].
  exists del. split; [ exact Hdel0 | ]. split.
  - intros d' Hd'. apply (HfreeM d' ltac:(lra) yF). lra.
  - exact Hchain.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions wall_corridor_clear_corner_east.
Print Assumptions corridor_connected_east.
Print Assumptions incident_pair_min.
Print Assumptions hug_step_min_open_we.
