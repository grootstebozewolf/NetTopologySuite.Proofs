(* ============================================================================
   NetTopologySuite.Proofs.JCTHugStep
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-6: THE HUG STATE and the first CORNER COMPOSITE.

   The traversal's state: `hugs_west r e q` -- the anchor point q is
   off-ring and complement-connected to a west-corridor point of e at the
   edge's SPAN MIDPOINT `mid e`, with freedom at ALL smaller offsets
   there.  The midpoint is the delta-free canonical height that kills the
   parameter-threading circularity (window before delta before eps before
   window); the all-offsets clause is what `corridor_offset_jog` consumes
   to shrink delta below any corner's threshold.  Steps never move q: they
   EXTEND its connectivity to the next edge's midpoint corridor.

   `hug_step_pass_down_west` is the first composite: at a downward
   pass-through corner c (e arrives from above, f continues below, walker
   on the west), the chain is

     jog (shrink delta) . corner_passage_fresh (down e, past c)
     . corner box (transfer to f's corridor entry, both abscissae pinned
       inside the box by drop/apex_abscissa_bound)
     . top-abutting ride (down f to mid f).

   The corner conditions are DISCHARGED, not assumed: at a degree-2
   pass-through corner, `corner_opens_east` for e and
   `corner_opens_east_top` for f hold by `incident_two` -- the only
   incident edges are e (own carrier, equalities) and f (its far endpoint
   is below the corner level, so the east condition is vacuous), and
   symmetrically.  Only tautness, the proper-ring structure, and the
   global no-horizontal-edges simplification remain as inputs.

   Also here: `wall_corridor_clear_corner_top` (the y-flip of rung 5a's
   corner-abutting clearance -- uniform delta0 for the corridor on a
   window abutting the wall's TOP vertex) and `apex_abscissa_bound` (the
   y-flip of the drop abscissa bound).

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
From NTS.Proofs Require Import JCTRingCycle.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  The state.
   --------------------------------------------------------------------------- *)

Definition mid (e : Edge) : R := (py (fst e) + py (snd e)) / 2.

(* q is off-ring and connected to e's west midpoint corridor, with freedom
   at all smaller offsets there. *)
Definition hugs_west (r : Ring) (e : Edge) (q : Point) : Prop :=
  ring_complement r q /\
  exists delta,
    0 < delta /\
    (forall d', 0 < d' <= delta -> ~ ring_image r (corridor e d' (mid e))) /\
    connected_in_complement_cont r q (corridor e delta (mid e)).

(* The global general-position simplification for the traversal. *)
Definition no_horizontal_edges (r : Ring) : Prop :=
  forall g, In g (ring_edges r) -> py (fst g) <> py (snd g).

(* ---------------------------------------------------------------------------
   §1  Mirror gap-fillers: the top-abutting clearance and the apex bound.
   --------------------------------------------------------------------------- *)

(* The y-flip of rung 5a's corner-abutting wall clearance: ONE uniform
   delta0 for the corridor on a window abutting the wall's TOP vertex. *)
Theorem wall_corridor_clear_corner_top : forall (r : Ring) (e1 : Edge)
                                                (v u : Point) (ylo : R),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, u) \/ e1 = (u, v) ->
  py v < py u ->
  py v < ylo ->
  ylo <= py u ->
  corner_opens_east_top r e1 u ->
  exists delta0, 0 < delta0 /\
    forall delta, 0 < delta < delta0 ->
      forall y, ylo <= y < py u ->
        ~ ring_image r (corridor e1 delta y).
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
  destruct (wall_corridor_clear_corner r' e1' (ymir u) (ymir v) (- ylo)
              Htaut' Hin' Hor'
              ltac:(unfold ymir; cbn [py]; lra)
              ltac:(unfold ymir; cbn [py]; lra)
              ltac:(unfold ymir; cbn [py]; lra)
              Hopen') as [delta0 [Hd0 Hfree]].
  exists delta0. split; [ exact Hd0 | ].
  intros delta Hd y Hy Himg.
  apply (Hfree delta Hd (- y)).
  - unfold ymir; cbn [py]. lra.
  - assert (HcorEq : corridor e1' delta (- y)
                       = ymir (corridor (ea, eb) delta y)).
    { unfold e1', corridor.
      rewrite (edge_x_at_ymir ea eb y Hnh).
      unfold ymir; cbn [px py]. reflexivity. }
    rewrite HcorEq.
    apply (ring_image_ymir r (corridor (ea, eb) delta y)). exact Himg.
Qed.

(* The y-flip of drop_abscissa_bound: near the TOP vertex v of a
   descending edge (v, w), the corridor abscissa is pinned in the box. *)
Lemma apex_abscissa_bound : forall (v w : Point) (delta eps : R),
  py w < py v -> 0 < delta -> 0 < eps ->
  2 * eps * (Rabs (px w - px v) + 1) < delta * (py v - py w) ->
  px v - 2 * delta <= edge_x_at (v, w) (py v - eps) - delta
    <= px v - delta / 2.
Proof.
  intros v w delta eps Hvw Hd He Hcap.
  assert (Hnh : py v <> py w) by lra.
  assert (Heq : edge_x_at (v, w) (py v - eps)
                  = edge_x_at (ymir v, ymir w) (py (ymir v) + eps)).
  { replace (py (ymir v) + eps) with (- (py v - eps))
      by (unfold ymir; cbn [py]; ring).
    rewrite (edge_x_at_ymir v w (py v - eps) Hnh). reflexivity. }
  rewrite Heq.
  pose proof (drop_abscissa_bound (ymir v) (ymir w) delta eps
                ltac:(unfold ymir; cbn [py]; lra) Hd He
                ltac:(unfold ymir; cbn [px py];
                      replace (- py w - - py v) with (py v - py w) by ring;
                      lra)) as Hb.
  unfold ymir in Hb; cbn [px py] in Hb.
  exact Hb.
Qed.

(* ---------------------------------------------------------------------------
   §2  Discharging the corner conditions at a degree-2 pass-through corner.
   --------------------------------------------------------------------------- *)

(* The wall's carrier passes through its own top vertex. *)
Lemma carrier_at_far : forall (e1 : Edge) (v w : Point),
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  edge_x_at e1 (py w) = px w.
Proof.
  intros e1 v w Hor Hvw.
  destruct Hor as [He | He]; subst e1.
  - apply (edge_x_at_endpoint_b (v, w)); cbn; lra.
  - apply (edge_x_at_endpoint_a (w, v)); cbn; lra.
Qed.

(* At a degree-2 corner, every incident edge is e or f. *)
Lemma incident_pair : forall (r : Ring) (e f : Edge) (c w_e w_f : Point),
  ring_core_nodup r ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_f < py c -> py c < py w_e ->
  forall g, In g (ring_edges r) -> fst g = c \/ snd g = c ->
  g = e \/ g = f.
Proof.
  intros r e f c w_e w_f Hnd Hine Hinf HorE HorF Hwf Hwe g Hing Hinc.
  destruct HorE as [HE | HE]; destruct HorF as [HF | HF]; subst e f.
  - exact (incident_two r (w_e, c) (c, w_f) g c Hnd Hine eq_refl
             Hinf eq_refl Hing Hinc).
  - exfalso.
    pose proof (in_edge_unique r w_e w_f c Hnd Hine Hinf). subst w_f. lra.
  - exfalso.
    pose proof (out_edge_unique r w_e w_f c Hnd Hine Hinf). subst w_f. lra.
  - destruct (incident_two r (w_f, c) (c, w_e) g c Hnd Hinf eq_refl
                Hine eq_refl Hing Hinc) as [H | H]; [ right | left ];
      exact H.
Qed.

(* corner_opens_east for the arriving wall e at a downward pass-through. *)
Lemma opens_east_pass_down : forall (r : Ring) (e f : Edge)
                                    (c w_e w_f : Point),
  ring_core_nodup r ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_f < py c -> py c < py w_e ->
  corner_opens_east r e c.
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

(* corner_opens_east_top for the departing wall f at the same corner. *)
Lemma opens_east_top_pass_down : forall (r : Ring) (e f : Edge)
                                        (c w_e w_f : Point),
  ring_core_nodup r ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_f < py c -> py c < py w_e ->
  corner_opens_east_top r f c.
Proof.
  intros r e f c w_e w_f Hnd Hine Hinf HorE HorF Hwf Hwe g Hing Hinc.
  assert (HorF' : f = (w_f, c) \/ f = (c, w_f)) by tauto.
  assert (Hcc : edge_x_at f (py c) = px c)
    by (exact (carrier_at_far f w_f c HorF' Hwf)).
  assert (Hcw : edge_x_at f (py w_f) = px w_f)
    by (exact (carrier_at_corner f w_f c HorF' Hwf)).
  destruct (incident_pair r e f c w_e w_f Hnd Hine Hinf HorE HorF Hwf Hwe
              g Hing Hinc) as [Hg | Hg]; subst g.
  - destruct HorE as [HE | HE]; subst e; cbn [fst snd] in *;
      split; intro Hyy; lra.
  - destruct HorF as [HF | HF]; subst f; cbn [fst snd] in *;
      split; intro Hyy; lra.
Qed.

(* ---------------------------------------------------------------------------
   §3  THE COMPOSITE: the downward pass-through corner, west side.
   --------------------------------------------------------------------------- *)

Theorem hug_step_pass_down_west : forall (r : Ring) (e f : Edge)
                                         (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_f < py c -> py c < py w_e ->
  hugs_west r e q ->
  hugs_west r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hine Hinf HorE HorF Hwf Hwe Hhug.
  destruct Hhug as [Hq [dS [HdS [HfreeS HconnS]]]].
  assert (HorE' : e = (c, w_e) \/ e = (w_e, c)) by tauto.
  assert (HorF' : f = (w_f, c) \/ f = (c, w_f)) by tauto.
  assert (HnhE : py (fst e) <> py (snd e))
    by (destruct HorE as [HE | HE]; subst e; cbn; lra).
  assert (HnhF : py (fst f) <> py (snd f))
    by (destruct HorF as [HF | HF]; subst f; cbn; lra).
  assert (HopenE : corner_opens_east r e c)
    by (exact (opens_east_pass_down r e f c w_e w_f Hnd Hine Hinf
                 HorE HorF Hwf Hwe)).
  assert (HopenF : corner_opens_east_top r f c)
    by (exact (opens_east_top_pass_down r e f c w_e w_f Hnd Hine Hinf
                 HorE HorF Hwf Hwe)).
  set (yE := mid e). set (yF := mid f).
  assert (HyE : py c < yE < py w_e)
    by (unfold yE, mid; destruct HorE as [HE | HE]; subst e; cbn; lra).
  assert (HyF : py w_f < yF < py c)
    by (unfold yF, mid; destruct HorF as [HF | HF]; subst f; cbn; lra).
  assert (Hez : forall g, In g (ring_edges r) ->
            py (fst g) = py (snd g) -> fst g = c \/ snd g = c ->
            px c <= px (fst g) /\ px c <= px (snd g))
    by (intros g Hing Hflat _; exfalso; exact (Hnoh g Hing Hflat)).
  (* stage-1 thresholds *)
  destruct (corner_passage_fresh r e c w_e yE Htaut Hine HorE'
              ltac:(lra) ltac:(lra) ltac:(lra) HopenE)
    as [dP [HdP HstageP]].
  destruct (corner_box_clear r e c w_e Htaut Hine HorE' ltac:(lra) Hez)
    as [dB [HdB HstageB]].
  destruct (wall_corridor_clear_corner_top r f w_f c yF Htaut Hinf HorF'
              ltac:(lra) ltac:(lra) ltac:(lra) HopenF)
    as [dT [HdT HfreeT]].
  assert (HspanF : (py (fst f) < yF /\ yF < py (snd f)) \/
                   (py (snd f) < yF /\ yF < py (fst f)))
    by (destruct HorF as [HF | HF]; subst f; cbn in *; [ right | left ]; lra).
  destruct (wall_corridor_clear r f yF yF Htaut Hinf HspanF ltac:(lra))
    as [dM [HdM HfreeM]].
  set (del := Rmin (Rmin dS dP) (Rmin dB (Rmin dT dM)) / 2).
  assert (Hdel : 0 < del /\ del < dS /\ del < dP /\ del < dB /\
                 del < dT /\ del < dM).
  { unfold del.
    pose proof (Rmin_l dS dP). pose proof (Rmin_r dS dP).
    pose proof (Rmin_l dB (Rmin dT dM)). pose proof (Rmin_r dB (Rmin dT dM)).
    pose proof (Rmin_l dT dM). pose proof (Rmin_r dT dM).
    pose proof (Rmin_l (Rmin dS dP) (Rmin dB (Rmin dT dM))).
    pose proof (Rmin_r (Rmin dS dP) (Rmin dB (Rmin dT dM))).
    assert (0 < Rmin (Rmin dS dP) (Rmin dB (Rmin dT dM))).
    { apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | ].
      apply Rmin_glb_lt; [ lra | apply Rmin_glb_lt; lra ]. }
    repeat split; lra. }
  destruct Hdel as [Hdel0 [HdelS [HdelP [HdelB [HdelT HdelM]]]]].
  (* stage-2 thresholds *)
  destruct (HstageP del ltac:(lra)) as [eP [HeP HpassP]].
  destruct (HstageB del ltac:(lra)) as [eB [HeB HboxB]].
  pose proof (Rabs_pos (px w_e - px c)) as HAe.
  pose proof (Rabs_pos (px w_f - px c)) as HAf.
  set (capE := del * (py w_e - py c) / (2 * (Rabs (px w_e - px c) + 1))).
  set (capF := del * (py c - py w_f) / (2 * (Rabs (px w_f - px c) + 1))).
  assert (HcapE : 0 < capE)
    by (unfold capE; apply Rdiv_lt_0_compat; nra).
  assert (HcapF : 0 < capF)
    by (unfold capF; apply Rdiv_lt_0_compat; nra).
  set (eps := Rmin (Rmin eP eB) (Rmin (Rmin capE capF) (py c - yF)) / 2).
  assert (Heps : 0 < eps /\ eps < eP /\ eps < eB /\ eps < capE /\
                 eps < capF /\ eps < py c - yF).
  { unfold eps.
    pose proof (Rmin_l eP eB). pose proof (Rmin_r eP eB).
    pose proof (Rmin_l capE capF). pose proof (Rmin_r capE capF).
    pose proof (Rmin_l (Rmin capE capF) (py c - yF)).
    pose proof (Rmin_r (Rmin capE capF) (py c - yF)).
    pose proof (Rmin_l (Rmin eP eB) (Rmin (Rmin capE capF) (py c - yF))).
    pose proof (Rmin_r (Rmin eP eB) (Rmin (Rmin capE capF) (py c - yF))).
    assert (0 < Rmin (Rmin eP eB) (Rmin (Rmin capE capF) (py c - yF))).
    { apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | ].
      apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | lra ]. }
    repeat split; lra. }
  destruct Heps as [Heps0 [HepsP [HepsB [HepsE [HepsF HepsYF]]]]].
  (* abscissa caps in product form *)
  assert (HprodE : 2 * eps * (Rabs (px w_e - px c) + 1)
                     < del * (py w_e - py c)).
  { apply (cap_mult eps _ (2 * (Rabs (px w_e - px c) + 1))
             ltac:(nra)) in HepsE.
    unfold capE in HepsE. lra. }
  assert (HprodF : 2 * eps * (Rabs (px w_f - px c) + 1)
                     < del * (py c - py w_f)).
  { apply (cap_mult eps _ (2 * (Rabs (px w_f - px c) + 1))
             ltac:(nra)) in HepsF.
    unfold capF in HepsF. lra. }
  (* abscissa bounds: both transfer points sit in the corner box *)
  assert (HbndE : px c - 2 * del <= edge_x_at e (py c + eps) - del
                    <= px c - del / 2).
  { destruct HorE' as [HE | HE]; subst e.
    - exact (drop_abscissa_bound c w_e del eps Hwe ltac:(lra) ltac:(lra)
               HprodE).
    - rewrite <- (edge_x_at_swap c w_e (py c + eps) ltac:(lra)).
      exact (drop_abscissa_bound c w_e del eps Hwe ltac:(lra) ltac:(lra)
               HprodE). }
  assert (HbndF : px c - 2 * del <= edge_x_at f (py c - eps) - del
                    <= px c - del / 2).
  { destruct HorF' as [HF | HF]; subst f.
    - rewrite (edge_x_at_swap w_f c (py c - eps) ltac:(lra)).
      exact (apex_abscissa_bound c w_f del eps Hwf ltac:(lra) ltac:(lra)
               HprodF).
    - exact (apex_abscissa_bound c w_f del eps Hwf ltac:(lra) ltac:(lra)
               HprodF). }
  (* the moves *)
  destruct (HpassP eps ltac:(lra)) as [HconnP [_ [HcomplP1 _]]].
  assert (Hjog : connected_in_complement_cont r
            (corridor e del (mid e)) (corridor e dS (mid e))).
  { apply (corridor_offset_jog r e (mid e) del dS ltac:(lra)).
    intros d' Hd'. apply HfreeS. lra. }
  assert (HboxConn : connected_in_complement_cont r
            (mkPoint (edge_x_at e (py c + eps) - del) (py c - eps))
            (mkPoint (edge_x_at f (py c - eps) - del) (py c - eps))).
  { apply (box_connected_of_clear r (px c - 2 * del) (px c - del / 2)
             (py c - eps) (py c + eps)
             ltac:(intros x y Hx Hy;
                   exact (HboxB eps ltac:(lra) x y Hx Hy)));
      split; lra. }
  assert (HrideF : connected_in_complement_cont r
            (corridor f del (py c - eps)) (corridor f del yF)).
  { apply (corridor_connected r f yF (py c - eps) del HnhF ltac:(lra)).
    intros y Hy. apply (HfreeT del ltac:(lra)). lra. }
  assert (Hchain : connected_in_complement_cont r q (corridor f del yF)).
  { apply (connected_in_complement_cont_trans r q
             (corridor e del (mid e))).
    - apply (connected_in_complement_cont_trans r q
               (corridor e dS (mid e))); [ exact HconnS | ].
      apply connected_in_complement_cont_sym. exact Hjog.
    - apply (connected_in_complement_cont_trans r _
               (mkPoint (edge_x_at e (py c + eps) - del) (py c - eps))).
      + exact HconnP.
      + apply (connected_in_complement_cont_trans r _
                 (mkPoint (edge_x_at f (py c - eps) - del) (py c - eps))).
        * exact HboxConn.
        * exact HrideF. }
  split; [ exact Hq | ].
  exists del. split; [ exact Hdel0 | ]. split.
  - intros d' Hd'. apply (HfreeM d' ltac:(lra) yF). lra.
  - exact Hchain.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions wall_corridor_clear_corner_top.
Print Assumptions apex_abscissa_bound.
Print Assumptions incident_pair.
Print Assumptions hug_step_pass_down_west.
