(* ============================================================================
   NetTopologySuite.Proofs.JCTCornerDispatch
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-13: THE PER-CORNER TOTAL STEP.  The walker's
   combined state `hugs := hugs_west \/ hugs_east` advances through ANY
   degree-2 corner of a taut, proper, horizontal-free ring:

     hug_step_corner : hugs r e q -> hugs r f q

   for cycle-adjacent edges e (other end w_e) and f (other end w_f) at
   the shared corner c.  The dispatch:

     - corner type by the height signs of w_e, w_f against c
       (pass-through down/up, local min, local max);
     - pass-throughs keep the hug side (rungs 5c-6/7);
     - extrema flip it, deciding open vs pinched by ONE `Rle_dec` on the
       carrier comparison: the bridge (`carrier_side_equiv`, rung 5c-12)
       supplies the partner condition, and `corner_slopes_distinct`
       strictifies the negative branch -- under tautness two distinct
       edges through one corner cannot be collinear (they would meet at
       a parameter-interior point, `interior_param`), so the slope
       comparison is never an equality on the pinched side.

   This is the traversal's engine: the cycle recursion (next rung) just
   iterates it along `cyclic_next`.

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
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  Interior parameters and the distinct-slopes fact.
   --------------------------------------------------------------------------- *)

(* A height strictly between an edge's endpoint levels is hit at a
   parameter strictly inside (0,1). *)
Lemma interior_param : forall (g : Edge) (c w : Point) (ym : R),
  g = (c, w) \/ g = (w, c) ->
  (ym - py c) * (py w - ym) > 0 ->
  exists t, 0 < t < 1 /\
    (1 - t) * py (fst g) + t * py (snd g) = ym.
Proof.
  intros g c w ym Hor Hbet.
  assert (Hnh : py c <> py w).
  { intro He. rewrite He in Hbet.
    pose proof (Rle_0_sqr (ym - py w)) as Hsq. unfold Rsqr in Hsq. nra. }
  destruct Hor as [Hg | Hg]; subst g; cbn [fst snd].
  - assert (HD : py w - py c <> 0) by lra.
    pose proof (Rsqr_pos_lt (py w - py c) HD) as HD2. unfold Rsqr in HD2.
    pose proof (Rle_0_sqr (ym - py c)) as HN2. unfold Rsqr in HN2.
    pose proof (Rle_0_sqr (py w - ym)) as HM2. unfold Rsqr in HM2.
    exists ((ym - py c) / (py w - py c)).
    assert (Ht1 : (ym - py c) / (py w - py c) * (py w - py c) = ym - py c)
      by (field; lra).
    pose proof (Rmult_eq_compat_r (py w - py c) _ _ Ht1) as Ht2.
    assert (TND : (ym - py c) * (py w - py c) > 0) by nra.
    assert (TDD : (py w - ym) * (py w - py c) > 0) by nra.
    split; [ split; nra | nra ].
  - assert (HD : py c - py w <> 0) by lra.
    pose proof (Rsqr_pos_lt (py c - py w) HD) as HD2. unfold Rsqr in HD2.
    pose proof (Rle_0_sqr (ym - py w)) as HN2. unfold Rsqr in HN2.
    pose proof (Rle_0_sqr (py c - ym)) as HM2. unfold Rsqr in HM2.
    exists ((ym - py w) / (py c - py w)).
    assert (Ht1 : (ym - py w) / (py c - py w) * (py c - py w) = ym - py w)
      by (field; lra).
    pose proof (Rmult_eq_compat_r (py c - py w) _ _ Ht1) as Ht2.
    assert (TND : (ym - py w) * (py c - py w) > 0) by nra.
    assert (TDD : (py c - ym) * (py c - py w) > 0) by nra.
    split; [ split; nra | nra ].
Qed.

(* Under tautness, two distinct edges through a shared corner are never
   collinear: the far endpoint of one never sits exactly on the other's
   carrier (same-side version, covering minima and maxima). *)
Lemma corner_slopes_distinct : forall (r : Ring) (e f : Edge)
                                      (c w_e w_f : Point),
  ring_taut r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_e <> py c -> py w_f <> py c ->
  (py w_e - py c) * (py w_f - py c) > 0 ->
  edge_x_at e (py w_f) <> px w_f.
Proof.
  intros r e f c w_e w_f Htaut Hnef Hine Hinf HorE HorF HnhE HnhF Hsame Heq.
  assert (HorE' : e = (c, w_e) \/ e = (w_e, c)) by tauto.
  assert (HorF' : f = (c, w_f) \/ f = (w_f, c)) by tauto.
  assert (HnhE' : py (fst e) <> py (snd e))
    by (destruct HorE as [HE | HE]; subst e; cbn; lra).
  assert (HnhF' : py (fst f) <> py (snd f))
    by (destruct HorF as [HF | HF]; subst f; cbn; lra).
  set (KE := (px w_e - px c) / (py w_e - py c)).
  set (KF := (px w_f - px c) / (py w_f - py c)).
  assert (HlinE : forall y, edge_x_at e y = px c + KE * (y - py c))
    by (intro y; rewrite (carrier_lin e c w_e HorE' HnhE y); unfold KE;
        reflexivity).
  assert (HlinF : forall y, edge_x_at f y = px c + KF * (y - py c))
    by (intro y; rewrite (carrier_lin f c w_f HorF' HnhF y); unfold KF;
        reflexivity).
  assert (HKF1 : KF * (py w_f - py c) = px w_f - px c)
    by (unfold KF; field; lra).
  assert (HKeq : KE = KF).
  { rewrite (HlinE (py w_f)) in Heq.
    assert ((KE - KF) * (py w_f - py c) = 0) by lra.
    assert (py w_f - py c <> 0) by lra.
    nra. }
  (* a common interior height *)
  set (A := py w_e - py c). set (B := py w_f - py c).
  assert (Hcase : (0 < A /\ 0 < B) \/ (A < 0 /\ B < 0))
    by (unfold A, B in *; nra).
  assert (Hym : exists ym, (ym - py c) * (py w_e - ym) > 0 /\
                           (ym - py c) * (py w_f - ym) > 0).
  { destruct Hcase as [[HA HB] | [HA HB]].
    - exists (py c + Rmin A B / 2).
      pose proof (Rmin_l A B). pose proof (Rmin_r A B).
      assert (0 < Rmin A B) by (apply Rmin_glb_lt; lra).
      unfold A, B in *. split; nra.
    - exists (py c + Rmax A B / 2).
      pose proof (Rmax_l A B). pose proof (Rmax_r A B).
      assert (Rmax A B < 0) by (apply Rmax_lub_lt; lra).
      unfold A, B in *. split; nra. }
  destruct Hym as [ym [HbetE HbetF]].
  destruct (interior_param e c w_e ym ltac:(tauto) HbetE)
    as [t [Htb Hty]].
  destruct (interior_param f c w_f ym ltac:(tauto) HbetF)
    as [s [Hsb Hsy]].
  (* the meeting equations at height ym *)
  assert (Htx : (1 - t) * px (fst e) + t * px (snd e) = edge_x_at e ym)
    by (rewrite <- (on_carrier_x e t HnhE'), Hty; reflexivity).
  assert (Hsx : (1 - s) * px (fst f) + s * px (snd f) = edge_x_at f ym)
    by (rewrite <- (on_carrier_x f s HnhF'), Hsy; reflexivity).
  assert (Hcar : edge_x_at e ym = edge_x_at f ym)
    by (rewrite (HlinE ym), (HlinF ym), HKeq; reflexivity).
  destruct (Htaut e f Hine Hinf t s ltac:(lra) ltac:(lra)
              ltac:(rewrite Htx, Hsx, Hcar; reflexivity)
              ltac:(rewrite Hty, Hsy; reflexivity))
    as [[Ht0 | Ht1] | [Hff Hss]].
  - lra.
  - lra.
  - apply Hnef.
    rewrite (surjective_pairing e), (surjective_pairing f), Hff, Hss.
    reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   §1  The combined state and THE TOTAL CORNER STEP.
   --------------------------------------------------------------------------- *)

Definition hugs (r : Ring) (e : Edge) (q : Point) : Prop :=
  hugs_west r e q \/ hugs_east r e q.

Theorem hug_step_corner : forall (r : Ring) (e f : Edge)
                                 (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  e <> f ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_e <> py c -> py w_f <> py c ->
  hugs r e q ->
  hugs r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hnef Hine Hinf HorE HorF
    HhE HhF Hhug.
  destruct (Rlt_le_dec (py c) (py w_e)) as [HweU | HweD];
  destruct (Rlt_le_dec (py c) (py w_f)) as [HwfU | HwfD].
  - (* local MIN: both climb *)
    assert (Hsame : (py w_e - py c) * (py w_f - py c) > 0) by nra.
    destruct (carrier_side_equiv e f c w_e w_f HorE HorF HhE HhF Hsame)
      as [Hbr1 Hbr2].
    pose proof (corner_slopes_distinct r e f c w_e w_f Htaut Hnef
                  Hine Hinf HorE HorF HhE HhF Hsame) as Hneq.
    destruct (Rle_dec (edge_x_at e (py w_f)) (px w_f)) as [Hside | Hside].
    + (* f weakly (hence strictly) east of e's carrier *)
      destruct Hhug as [Hw | He].
      * right.
        exact (hug_step_min_open_we r e f c w_e w_f q Htaut Hnd Hnoh
                 Hnef Hine Hinf HorE HorF HweU HwfU Hside
                 (proj1 Hbr1 Hside) Hw).
      * left.
        assert (Hs1 : edge_x_at e (py w_f) < px w_f) by lra.
        assert (Hs2 : px w_e < edge_x_at f (py w_e)).
        { destruct (Rle_dec (edge_x_at f (py w_e)) (px w_e)) as [Hc | Hc];
            [ | lra ].
          pose proof (proj2 Hbr2 Hc). lra. }
        exact (hug_step_min_pinched_ew r e f c w_e w_f q Htaut Hnd Hnoh
                 Hnef Hine Hinf HorE HorF HweU HwfU Hs1 Hs2 He).
    + (* f strictly west of e's carrier *)
      assert (Hs1 : px w_f < edge_x_at e (py w_f)) by lra.
      destruct Hhug as [Hw | He].
      * right.
        assert (Hs2 : edge_x_at f (py w_e) < px w_e).
        { destruct (Rle_dec (px w_e) (edge_x_at f (py w_e))) as [Hc | Hc];
            [ | lra ].
          pose proof (proj2 Hbr1 Hc). lra. }
        exact (hug_step_min_pinched_we r e f c w_e w_f q Htaut Hnd Hnoh
                 Hnef Hine Hinf HorE HorF HweU HwfU Hs1 Hs2 Hw).
      * left.
        exact (hug_step_min_open_ew r e f c w_e w_f q Htaut Hnd Hnoh
                 Hnef Hine Hinf HorE HorF HweU HwfU ltac:(lra)
                 (proj1 Hbr2 ltac:(lra)) He).
  - (* downward pass-through *)
    destruct Hhug as [Hw | He].
    + left.
      exact (hug_step_pass_down_west r e f c w_e w_f q Htaut Hnd Hnoh
               Hine Hinf HorE HorF ltac:(lra) HweU Hw).
    + right.
      exact (hug_step_pass_down_east r e f c w_e w_f q Htaut Hnd Hnoh
               Hine Hinf HorE HorF ltac:(lra) HweU He).
  - (* upward pass-through *)
    destruct Hhug as [Hw | He].
    + left.
      exact (hug_step_pass_up_west r e f c w_e w_f q Htaut Hnd Hnoh
               Hine Hinf HorE HorF HwfU ltac:(lra) Hw).
    + right.
      exact (hug_step_pass_up_east r e f c w_e w_f q Htaut Hnd Hnoh
               Hine Hinf HorE HorF HwfU ltac:(lra) He).
  - (* local MAX: both descend *)
    assert (Hsame : (py w_e - py c) * (py w_f - py c) > 0) by nra.
    destruct (carrier_side_equiv e f c w_e w_f HorE HorF HhE HhF Hsame)
      as [Hbr1 Hbr2].
    pose proof (corner_slopes_distinct r e f c w_e w_f Htaut Hnef
                  Hine Hinf HorE HorF HhE HhF Hsame) as Hneq.
    destruct (Rle_dec (edge_x_at e (py w_f)) (px w_f)) as [Hside | Hside].
    + destruct Hhug as [Hw | He].
      * right.
        exact (hug_step_max_open_we r e f c w_e w_f q Htaut Hnd Hnoh
                 Hnef Hine Hinf HorE HorF ltac:(lra) ltac:(lra) Hside
                 (proj1 Hbr1 Hside) Hw).
      * left.
        assert (Hs1 : edge_x_at e (py w_f) < px w_f) by lra.
        assert (Hs2 : px w_e < edge_x_at f (py w_e)).
        { destruct (Rle_dec (edge_x_at f (py w_e)) (px w_e)) as [Hc | Hc];
            [ | lra ].
          pose proof (proj2 Hbr2 Hc). lra. }
        exact (hug_step_max_pinched_ew r e f c w_e w_f q Htaut Hnd Hnoh
                 Hnef Hine Hinf HorE HorF ltac:(lra) ltac:(lra)
                 Hs1 Hs2 He).
    + assert (Hs1 : px w_f < edge_x_at e (py w_f)) by lra.
      destruct Hhug as [Hw | He].
      * right.
        assert (Hs2 : edge_x_at f (py w_e) < px w_e).
        { destruct (Rle_dec (px w_e) (edge_x_at f (py w_e))) as [Hc | Hc];
            [ | lra ].
          pose proof (proj2 Hbr1 Hc). lra. }
        exact (hug_step_max_pinched_we r e f c w_e w_f q Htaut Hnd Hnoh
                 Hnef Hine Hinf HorE HorF ltac:(lra) ltac:(lra)
                 Hs1 Hs2 Hw).
      * left.
        exact (hug_step_max_open_ew r e f c w_e w_f q Htaut Hnd Hnoh
                 Hnef Hine Hinf HorE HorF ltac:(lra) ltac:(lra) ltac:(lra)
                 (proj1 Hbr2 ltac:(lra)) He).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions interior_param.
Print Assumptions corner_slopes_distinct.
Print Assumptions hug_step_corner.
