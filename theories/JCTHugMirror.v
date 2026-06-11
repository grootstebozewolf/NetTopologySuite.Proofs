(* ============================================================================
   NetTopologySuite.Proofs.JCTHugMirror
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-7: THE MIRRORED HUG STEPS.  The hug state
   transports through the coordinate reflections -- the west midpoint
   corridor of a y-mirrored edge IS the y-mirror of the west midpoint
   corridor (`corridor_ymir`, `mid_ymir`), and the x-mirror swaps west
   corridors into EAST corridors (`corridor_xmir`), turning `hugs_west`
   of the mirror into `hugs_east` of the original.  With the ring-side
   hypotheses transported as well (tautness, the proper-ring structure
   via injective maps, no-horizontal-edges), the three remaining
   pass-through composites follow from rung 5c-6's
   `hug_step_pass_down_west` by transport rather than re-proof:

     hug_step_pass_up_west     (ymir)          west side, ascending
     hug_step_pass_down_east   (xmir)          east side, descending
     hug_step_pass_up_east     (xmir o ymir)   east side, ascending

   Each carries the walker's anchor through a degree-2 pass-through
   corner on its side, with all corner conditions discharged inside the
   mirrored application.

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
From NTS.Proofs Require Import JCTRingCycle JCTHugStep.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  The east-side state, and the corridor/midpoint mirror laws.
   --------------------------------------------------------------------------- *)

(* q is off-ring and connected to e's EAST midpoint corridor, with freedom
   at all smaller offsets there. *)
Definition hugs_east (r : Ring) (e : Edge) (q : Point) : Prop :=
  ring_complement r q /\
  exists delta,
    0 < delta /\
    (forall d', 0 < d' <= delta ->
       ~ ring_image r (mkPoint (edge_x_at e (mid e) + d') (mid e))) /\
    connected_in_complement_cont r q
      (mkPoint (edge_x_at e (mid e) + delta) (mid e)).

Lemma mid_ymir : forall (a b : Point),
  mid (ymir a, ymir b) = - mid (a, b).
Proof.
  intros a b. unfold mid, ymir; cbn [fst snd px py]. lra.
Qed.

Lemma mid_xmir : forall (a b : Point),
  mid (xmir a, xmir b) = mid (a, b).
Proof.
  intros a b. unfold mid, xmir; cbn [fst snd px py]. lra.
Qed.

Lemma corridor_ymir : forall (a b : Point) (delta y : R),
  py a <> py b ->
  corridor (ymir a, ymir b) delta (- y) = ymir (corridor (a, b) delta y).
Proof.
  intros a b delta y Hnh.
  unfold corridor.
  rewrite (edge_x_at_ymir a b y Hnh).
  unfold ymir; cbn [px py]. reflexivity.
Qed.

Lemma corridor_xmir : forall (a b : Point) (delta y : R),
  py a <> py b ->
  corridor (xmir a, xmir b) delta y
    = xmir (mkPoint (edge_x_at (a, b) y + delta) y).
Proof.
  intros a b delta y Hnh.
  unfold corridor.
  rewrite (edge_x_at_xmir a b y Hnh).
  unfold xmir; cbn [px py]. f_equal. ring.
Qed.

(* ---------------------------------------------------------------------------
   §1  Ring-side hypothesis transport.
   --------------------------------------------------------------------------- *)

Lemma nodup_map_inj : forall (m : Point -> Point),
  (forall p q : Point, m p = m q -> p = q) ->
  forall l : list Point, NoDup l -> NoDup (map m l).
Proof.
  intros m Hinj l Hnd.
  induction Hnd as [| x l Hnin Hnd IH]; cbn [map].
  - constructor.
  - constructor; [ | exact IH ].
    intro HIn. apply in_map_iff in HIn.
    destruct HIn as [y [Hy HIny]].
    apply Hinj in Hy. subst y. exact (Hnin HIny).
Qed.

Lemma ring_core_nodup_ymir : forall (r : Ring),
  ring_core_nodup r -> ring_core_nodup (map ymir r).
Proof.
  intros r [p [ps [Hr Hnd]]].
  exists (ymir p), (map ymir ps). split.
  - rewrite Hr. cbn [map]. rewrite map_app. reflexivity.
  - change (ymir p :: map ymir ps) with (map ymir (p :: ps)).
    exact (nodup_map_inj ymir ymir_inj (p :: ps) Hnd).
Qed.

Lemma ring_core_nodup_xmir : forall (r : Ring),
  ring_core_nodup r -> ring_core_nodup (map xmir r).
Proof.
  intros r [p [ps [Hr Hnd]]].
  exists (xmir p), (map xmir ps). split.
  - rewrite Hr. cbn [map]. rewrite map_app. reflexivity.
  - change (xmir p :: map xmir ps) with (map xmir (p :: ps)).
    exact (nodup_map_inj xmir xmir_inj (p :: ps) Hnd).
Qed.

Lemma no_horizontal_ymir : forall (r : Ring),
  no_horizontal_edges r -> no_horizontal_edges (map ymir r).
Proof.
  intros r Hnoh g' Hing'.
  rewrite ring_edges_map in Hing'.
  apply in_map_iff in Hing'. destruct Hing' as [g [Hg Hing]].
  subst g'. cbn [fst snd].
  pose proof (Hnoh g Hing).
  unfold ymir; cbn [py]. lra.
Qed.

Lemma no_horizontal_xmir : forall (r : Ring),
  no_horizontal_edges r -> no_horizontal_edges (map xmir r).
Proof.
  intros r Hnoh g' Hing'.
  rewrite ring_edges_map in Hing'.
  apply in_map_iff in Hing'. destruct Hing' as [g [Hg Hing]].
  subst g'. cbn [fst snd].
  pose proof (Hnoh g Hing).
  unfold xmir; cbn [py]. lra.
Qed.

(* ---------------------------------------------------------------------------
   §2  State transport.
   --------------------------------------------------------------------------- *)

Lemma hugs_west_ymir : forall (r : Ring) (a b : Point) (q : Point),
  py a <> py b ->
  hugs_west r (a, b) q ->
  hugs_west (map ymir r) (ymir a, ymir b) (ymir q).
Proof.
  intros r a b q Hnh [Hq [delta [Hd [Hfree Hconn]]]].
  split.
  { apply (ring_complement_ymir r q). exact Hq. }
  exists delta. split; [ exact Hd | ]. split.
  - intros d' Hd' Himg.
    rewrite mid_ymir in Himg.
    rewrite (corridor_ymir a b d' (mid (a, b)) Hnh) in Himg.
    apply (Hfree d' Hd').
    apply (ring_image_ymir r (corridor (a, b) d' (mid (a, b)))).
    exact Himg.
  - rewrite mid_ymir.
    rewrite (corridor_ymir a b delta (mid (a, b)) Hnh).
    exact (connected_ymir r q (corridor (a, b) delta (mid (a, b))) Hconn).
Qed.

Lemma hugs_west_to_east_xmir : forall (r : Ring) (a b : Point) (q : Point),
  py a <> py b ->
  hugs_west r (a, b) q ->
  hugs_east (map xmir r) (xmir a, xmir b) (xmir q).
Proof.
  intros r a b q Hnh [Hq [delta [Hd [Hfree Hconn]]]].
  split.
  { apply (ring_complement_xmir r q). exact Hq. }
  exists delta. split; [ exact Hd | ].
  assert (HnhM : py (xmir a) <> py (xmir b))
    by (unfold xmir; cbn [py]; exact Hnh).
  assert (Hpt : forall d',
            mkPoint (edge_x_at (xmir a, xmir b) (mid (xmir a, xmir b)) + d')
                    (mid (xmir a, xmir b))
            = xmir (corridor (a, b) d' (mid (a, b)))).
  { intro d'.
    rewrite mid_xmir.
    rewrite (edge_x_at_xmir a b (mid (a, b)) Hnh).
    unfold corridor, xmir; cbn [px py]. f_equal. ring. }
  split.
  - intros d' Hd' Himg.
    rewrite Hpt in Himg.
    apply (Hfree d' Hd').
    apply (ring_image_xmir r (corridor (a, b) d' (mid (a, b)))).
    exact Himg.
  - rewrite Hpt.
    exact (connected_xmir r q (corridor (a, b) delta (mid (a, b))) Hconn).
Qed.

Lemma hugs_east_to_west_xmir : forall (r : Ring) (a b : Point) (q : Point),
  py a <> py b ->
  hugs_east r (a, b) q ->
  hugs_west (map xmir r) (xmir a, xmir b) (xmir q).
Proof.
  intros r a b q Hnh [Hq [delta [Hd [Hfree Hconn]]]].
  split.
  { apply (ring_complement_xmir r q). exact Hq. }
  exists delta. split; [ exact Hd | ].
  assert (Hpt : forall d',
            corridor (xmir a, xmir b) d' (mid (xmir a, xmir b))
            = xmir (mkPoint (edge_x_at (a, b) (mid (a, b)) + d')
                            (mid (a, b)))).
  { intro d'.
    rewrite mid_xmir.
    exact (corridor_xmir a b d' (mid (a, b)) Hnh). }
  split.
  - intros d' Hd' Himg.
    rewrite Hpt in Himg.
    apply (Hfree d' Hd').
    apply (ring_image_xmir r _).
    exact Himg.
  - rewrite Hpt.
    exact (connected_xmir r q _ Hconn).
Qed.

(* ---------------------------------------------------------------------------
   §3  The three mirrored pass-through steps.
   --------------------------------------------------------------------------- *)

(* West side, ascending: e arrives from below at its TOP corner c, f
   continues upward. *)
Theorem hug_step_pass_up_west : forall (r : Ring) (e f : Edge)
                                       (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py c < py w_f -> py w_e < py c ->
  hugs_west r e q ->
  hugs_west r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hine Hinf HorE HorF Hwf Hwe Hhug.
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
  pose proof (hug_step_pass_down_west r' (ymir ea, ymir eb)
                (ymir fa, ymir fb) (ymir c) (ymir w_e) (ymir w_f) (ymir q)
                (ring_taut_ymir r Htaut)
                (ring_core_nodup_ymir r Hnd)
                (no_horizontal_ymir r Hnoh)
                Hine' Hinf' HorE' HorF'
                ltac:(unfold ymir; cbn [py]; lra)
                ltac:(unfold ymir; cbn [py]; lra)
                (hugs_west_ymir r ea eb q HnhE Hhug)) as Hstep.
  assert (HnhF' : py (ymir fa) <> py (ymir fb))
    by (unfold ymir; cbn [py]; lra).
  pose proof (hugs_west_ymir r' (ymir fa) (ymir fb) (ymir q) HnhF' Hstep)
    as Hback.
  unfold r' in Hback.
  rewrite map_ymir_invol, !ymir_invol in Hback.
  exact Hback.
Qed.

(* East side, descending: e arrives from above at its BOTTOM corner c, f
   continues downward, walker east. *)
Theorem hug_step_pass_down_east : forall (r : Ring) (e f : Edge)
                                         (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py w_f < py c -> py c < py w_e ->
  hugs_east r e q ->
  hugs_east r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hine Hinf HorE HorF Hwf Hwe Hhug.
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
  pose proof (hug_step_pass_down_west r' (xmir ea, xmir eb)
                (xmir fa, xmir fb) (xmir c) (xmir w_e) (xmir w_f) (xmir q)
                (ring_taut_xmir r Htaut)
                (ring_core_nodup_xmir r Hnd)
                (no_horizontal_xmir r Hnoh)
                Hine' Hinf' HorE' HorF'
                ltac:(unfold xmir; cbn [py]; lra)
                ltac:(unfold xmir; cbn [py]; lra)
                (hugs_east_to_west_xmir r ea eb q HnhE Hhug)) as Hstep.
  assert (HnhF' : py (xmir fa) <> py (xmir fb))
    by (unfold xmir; cbn [py]; lra).
  pose proof (hugs_west_to_east_xmir r' (xmir fa) (xmir fb) (xmir q)
                HnhF' Hstep) as Hback.
  unfold r' in Hback.
  rewrite map_xmir_invol, !xmir_invol in Hback.
  exact Hback.
Qed.

(* East side, ascending: both flips. *)
Theorem hug_step_pass_up_east : forall (r : Ring) (e f : Edge)
                                       (c w_e w_f : Point) (q : Point),
  ring_taut r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  In e (ring_edges r) -> In f (ring_edges r) ->
  e = (w_e, c) \/ e = (c, w_e) ->
  f = (c, w_f) \/ f = (w_f, c) ->
  py c < py w_f -> py w_e < py c ->
  hugs_east r e q ->
  hugs_east r f q.
Proof.
  intros r e f c w_e w_f q Htaut Hnd Hnoh Hine Hinf HorE HorF Hwf Hwe Hhug.
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
  pose proof (hug_step_pass_up_west r' (xmir ea, xmir eb)
                (xmir fa, xmir fb) (xmir c) (xmir w_e) (xmir w_f) (xmir q)
                (ring_taut_xmir r Htaut)
                (ring_core_nodup_xmir r Hnd)
                (no_horizontal_xmir r Hnoh)
                Hine' Hinf' HorE' HorF'
                ltac:(unfold xmir; cbn [py]; lra)
                ltac:(unfold xmir; cbn [py]; lra)
                (hugs_east_to_west_xmir r ea eb q HnhE Hhug)) as Hstep.
  assert (HnhF' : py (xmir fa) <> py (xmir fb))
    by (unfold xmir; cbn [py]; lra).
  pose proof (hugs_west_to_east_xmir r' (xmir fa) (xmir fb) (xmir q)
                HnhF' Hstep) as Hback.
  unfold r' in Hback.
  rewrite map_xmir_invol, !xmir_invol in Hback.
  exact Hback.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hugs_west_ymir.
Print Assumptions hug_step_pass_up_west.
Print Assumptions hug_step_pass_down_east.
Print Assumptions hug_step_pass_up_east.
