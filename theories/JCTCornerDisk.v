(* ============================================================================
   NetTopologySuite.Proofs.JCTCornerDisk
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-10: THE CORNER DISK.  Every edge NOT incident
   at a vertex v misses a fixed square neighbourhood of v: the pinched
   turnaround's last missing clearance.

   At a pinched corner the walker must turn around INSIDE the wedge
   between the two incident edges, jogging across the wedge interior near
   the tip.  Away from the corner the wedge interior may contain other
   parts of the ring (nested spiral arms!), so the jog must happen inside
   the taut margins around v -- and there the two incident edges clear
   POINTWISE (the wedge width exceeds the offsets), while every other
   edge clears by this disk:

     - edges whose span misses v's level: explicit height margins;
     - edges crossing v's level: they cross at abscissa X with
       |X - px v| = m > 0 (an edge through v would be incident, by
       `taut_vertex_endpoint`), and the square of radius below m/8 stays
       clear via `hprobe_avoid_level_crossing` (rung 5c-3's rectangle
       probe, reused with delta = eps = the radius).

   Under the traversal's global no-horizontal-edges simplification the
   horizontal cases vanish; the radii fold by `clear_fold` into one
   uniform disk radius (`corner_disk_clear`).

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
From NTS.Proofs Require Import JCTMinOpenStep JCTMinOpenMirror.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  Per-edge disk clearance for a non-incident edge.
   --------------------------------------------------------------------------- *)

Lemma disk_edge_clear : forall (r : Ring) (e1 g : Edge) (v w : Point),
  ring_taut r ->
  In e1 (ring_edges r) -> In g (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py (fst g) <> py (snd g) ->
  fst g <> v -> snd g <> v ->
  exists rg, 0 < rg /\ forall rad, 0 < rad < rg ->
    forall x y,
      px v - rad <= x <= px v + rad ->
      py v - rad <= y <= py v + rad ->
      ~ (exists s : R, 0 <= s <= 1 /\
           x = (1 - s) * px (fst g) + s * px (snd g) /\
           y = (1 - s) * py (fst g) + s * py (snd g)).
Proof.
  intros r e1 g v w Htaut Hin1 Hing Hor Hnh Hav Hbv.
  destruct g as [a b]; cbn [fst snd] in *.
  assert (Hnotong : forall u : R, 0 <= u <= 1 ->
            ~ ((1 - u) * px a + u * px b = px v /\
               (1 - u) * py a + u * py b = py v)).
  { intros u Hu [Hxu Hyu].
    destruct (taut_vertex_endpoint r e1 (a, b) v w Htaut Hin1 Hing Hor
                u Hu ltac:(cbn [fst snd]; exact Hxu)
                ltac:(cbn [fst snd]; exact Hyu)) as [Hfa | Hfb];
      cbn [fst snd] in *; [ exact (Hav Hfa) | exact (Hbv Hfb) ]. }
  destruct (Rlt_le_dec (py v) (py a)) as [Haab | Hale];
  destruct (Rlt_le_dec (py v) (py b)) as [Hbab | Hble].
  - (* both strictly above the level *)
    exists (Rmin (py a - py v) (py b - py v)).
    split; [ apply Rmin_glb_lt; lra | ].
    intros rad Hr x y Hx Hy [s [Hs [Hxs Hys]]].
    pose proof (Rmin_l (py a - py v) (py b - py v)).
    pose proof (Rmin_r (py a - py v) (py b - py v)).
    assert (T1 : 0 <= (1 - s) * (py a - (py v + rad))) by nra.
    assert (T2 : 0 <= s * (py b - (py v + rad))) by nra.
    nra.
  - (* a above, b at-or-below: the carrier crosses the level *)
    set (X := edge_x_at (a, b) (py v)).
    assert (HX : (X - px a) * (py b - py a) = (py v - py a) * (px b - px a))
      by (unfold X, edge_x_at; field; lra).
    assert (Hm : X <> px v).
    { intro Heq.
      set (u := (py a - py v) / (py a - py b)).
      assert (Hu1 : u * (py a - py b) = py a - py v)
        by (unfold u; field; lra).
      assert (Hub : 0 <= u <= 1) by nra.
      apply (Hnotong u Hub).
      split.
      - unfold u. unfold X, edge_x_at in Heq. rewrite <- Heq. field. lra.
      - nra. }
    pose proof (Rabs_pos_lt (X - px v) ltac:(lra)) as Hmpos.
    pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
    pose proof (Rabs_pos (px b - px a)) as HDx.
    exists (Rmin (Rabs (X - px v) / 8)
              (Rabs (X - px v) * Rabs (py b - py a)
                 / (8 * (Rabs (px b - px a) + 1)))).
    split.
    { apply Rmin_glb_lt; [ lra | apply Rdiv_lt_0_compat; nra ]. }
    intros rad Hr x y Hx Hy.
    pose proof (Rmin_l (Rabs (X - px v) / 8)
                  (Rabs (X - px v) * Rabs (py b - py a)
                     / (8 * (Rabs (px b - px a) + 1)))).
    pose proof (Rmin_r (Rabs (X - px v) / 8)
                  (Rabs (X - px v) * Rabs (py b - py a)
                     / (8 * (Rabs (px b - px a) + 1)))).
    assert (Hcap : 4 * rad * (Rabs (px b - px a) + 1)
                     < Rabs (X - px v) * Rabs (py b - py a)).
    { assert (Hr2 : rad < Rabs (X - px v) * Rabs (py b - py a)
                            / (8 * (Rabs (px b - px a) + 1))) by lra.
      apply (cap_mult rad _ (8 * (Rabs (px b - px a) + 1))
               ltac:(nra)) in Hr2.
      nra. }
    apply (hprobe_avoid_level_crossing a b v rad rad x y X Hnh HX
             ltac:(lra) ltac:(lra) ltac:(lra) Hcap
             ltac:(lra) ltac:(lra)).
  - (* a at-or-below, b above: mirror *)
    set (X := edge_x_at (a, b) (py v)).
    assert (HX : (X - px a) * (py b - py a) = (py v - py a) * (px b - px a))
      by (unfold X, edge_x_at; field; lra).
    assert (Hm : X <> px v).
    { intro Heq.
      set (u := (py v - py a) / (py b - py a)).
      assert (Hu1 : u * (py b - py a) = py v - py a)
        by (unfold u; field; lra).
      assert (Hub : 0 <= u <= 1) by nra.
      apply (Hnotong u Hub).
      split.
      - unfold u. unfold X, edge_x_at in Heq. rewrite <- Heq. field. lra.
      - nra. }
    pose proof (Rabs_pos_lt (X - px v) ltac:(lra)) as Hmpos.
    pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
    pose proof (Rabs_pos (px b - px a)) as HDx.
    exists (Rmin (Rabs (X - px v) / 8)
              (Rabs (X - px v) * Rabs (py b - py a)
                 / (8 * (Rabs (px b - px a) + 1)))).
    split.
    { apply Rmin_glb_lt; [ lra | apply Rdiv_lt_0_compat; nra ]. }
    intros rad Hr x y Hx Hy.
    pose proof (Rmin_l (Rabs (X - px v) / 8)
                  (Rabs (X - px v) * Rabs (py b - py a)
                     / (8 * (Rabs (px b - px a) + 1)))).
    pose proof (Rmin_r (Rabs (X - px v) / 8)
                  (Rabs (X - px v) * Rabs (py b - py a)
                     / (8 * (Rabs (px b - px a) + 1)))).
    assert (Hcap : 4 * rad * (Rabs (px b - px a) + 1)
                     < Rabs (X - px v) * Rabs (py b - py a)).
    { assert (Hr2 : rad < Rabs (X - px v) * Rabs (py b - py a)
                            / (8 * (Rabs (px b - px a) + 1))) by lra.
      apply (cap_mult rad _ (8 * (Rabs (px b - px a) + 1))
               ltac:(nra)) in Hr2.
      nra. }
    apply (hprobe_avoid_level_crossing a b v rad rad x y X Hnh HX
             ltac:(lra) ltac:(lra) ltac:(lra) Hcap
             ltac:(lra) ltac:(lra)).
  - (* both at-or-below the level *)
    destruct (Req_EM_T (py a) (py v)) as [Hae | Hae].
    + (* a exactly at the level: carrier crosses at X = px a <> px v *)
      assert (Hnh' : py a <> py b) by lra.
      set (X := edge_x_at (a, b) (py v)).
      assert (HX : (X - px a) * (py b - py a)
                     = (py v - py a) * (px b - px a))
        by (unfold X, edge_x_at; field; lra).
      assert (Hm : X <> px v).
      { intro Heq.
        apply (Hnotong 0 ltac:(lra)).
        assert (HX0 : X = px a) by nra.
        split; lra. }
      pose proof (Rabs_pos_lt (X - px v) ltac:(lra)) as Hmpos.
      pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
      pose proof (Rabs_pos (px b - px a)) as HDx.
      exists (Rmin (Rabs (X - px v) / 8)
                (Rabs (X - px v) * Rabs (py b - py a)
                   / (8 * (Rabs (px b - px a) + 1)))).
      split.
      { apply Rmin_glb_lt; [ lra | apply Rdiv_lt_0_compat; nra ]. }
      intros rad Hr x y Hx Hy.
      pose proof (Rmin_l (Rabs (X - px v) / 8)
                    (Rabs (X - px v) * Rabs (py b - py a)
                       / (8 * (Rabs (px b - px a) + 1)))).
      pose proof (Rmin_r (Rabs (X - px v) / 8)
                    (Rabs (X - px v) * Rabs (py b - py a)
                       / (8 * (Rabs (px b - px a) + 1)))).
      assert (Hcap : 4 * rad * (Rabs (px b - px a) + 1)
                       < Rabs (X - px v) * Rabs (py b - py a)).
      { assert (Hr2 : rad < Rabs (X - px v) * Rabs (py b - py a)
                              / (8 * (Rabs (px b - px a) + 1))) by lra.
        apply (cap_mult rad _ (8 * (Rabs (px b - px a) + 1))
                 ltac:(nra)) in Hr2.
        nra. }
      apply (hprobe_avoid_level_crossing a b v rad rad x y X Hnh' HX
               ltac:(lra) ltac:(lra) ltac:(lra) Hcap
               ltac:(lra) ltac:(lra)).
    + destruct (Req_EM_T (py b) (py v)) as [Hbe | Hbe].
      * (* b exactly at the level: X = px b <> px v *)
        assert (Hnh' : py a <> py b) by lra.
        set (X := edge_x_at (a, b) (py v)).
        assert (HX : (X - px a) * (py b - py a)
                       = (py v - py a) * (px b - px a))
          by (unfold X, edge_x_at; field; lra).
        assert (Hm : X <> px v).
        { intro Heq.
          apply (Hnotong 1 ltac:(lra)).
          assert (HX1 : X = px b) by nra.
          split; lra. }
        pose proof (Rabs_pos_lt (X - px v) ltac:(lra)) as Hmpos.
        pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
        pose proof (Rabs_pos (px b - px a)) as HDx.
        exists (Rmin (Rabs (X - px v) / 8)
                  (Rabs (X - px v) * Rabs (py b - py a)
                     / (8 * (Rabs (px b - px a) + 1)))).
        split.
        { apply Rmin_glb_lt; [ lra | apply Rdiv_lt_0_compat; nra ]. }
        intros rad Hr x y Hx Hy.
        pose proof (Rmin_l (Rabs (X - px v) / 8)
                      (Rabs (X - px v) * Rabs (py b - py a)
                         / (8 * (Rabs (px b - px a) + 1)))).
        pose proof (Rmin_r (Rabs (X - px v) / 8)
                      (Rabs (X - px v) * Rabs (py b - py a)
                         / (8 * (Rabs (px b - px a) + 1)))).
        assert (Hcap : 4 * rad * (Rabs (px b - px a) + 1)
                         < Rabs (X - px v) * Rabs (py b - py a)).
        { assert (Hr2 : rad < Rabs (X - px v) * Rabs (py b - py a)
                                / (8 * (Rabs (px b - px a) + 1))) by lra.
          apply (cap_mult rad _ (8 * (Rabs (px b - px a) + 1))
                   ltac:(nra)) in Hr2.
          nra. }
        apply (hprobe_avoid_level_crossing a b v rad rad x y X Hnh' HX
                 ltac:(lra) ltac:(lra) ltac:(lra) Hcap
                 ltac:(lra) ltac:(lra)).
      * (* both strictly below *)
        exists (Rmin (py v - py a) (py v - py b)).
        split; [ apply Rmin_glb_lt; lra | ].
        intros rad Hr x y Hx Hy [s [Hs [Hxs Hys]]].
        pose proof (Rmin_l (py v - py a) (py v - py b)).
        pose proof (Rmin_r (py v - py a) (py v - py b)).
        assert (T1 : (1 - s) * (py a - (py v - rad)) <= 0) by nra.
        assert (T2 : s * (py b - (py v - rad)) <= 0) by nra.
        nra.
Qed.

(* ---------------------------------------------------------------------------
   §2  THE CORNER DISK: one uniform radius for all non-incident edges.
   --------------------------------------------------------------------------- *)

Theorem corner_disk_clear : forall (r : Ring) (e1 : Edge) (v w : Point),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  no_horizontal_edges r ->
  exists rad0, 0 < rad0 /\
    forall rad, 0 < rad < rad0 ->
      forall g, In g (ring_edges r) -> fst g <> v -> snd g <> v ->
        forall x y,
          px v - rad <= x <= px v + rad ->
          py v - rad <= y <= py v + rad ->
          ~ (exists s : R, 0 <= s <= 1 /\
               x = (1 - s) * px (fst g) + s * px (snd g) /\
               y = (1 - s) * py (fst g) + s * py (snd g)).
Proof.
  intros r e1 v w Htaut Hin1 Hor Hnoh.
  destruct (clear_fold
              (fun g rad =>
                 fst g <> v -> snd g <> v ->
                 forall x y,
                   px v - rad <= x <= px v + rad ->
                   py v - rad <= y <= py v + rad ->
                   ~ (exists s : R, 0 <= s <= 1 /\
                        x = (1 - s) * px (fst g) + s * px (snd g) /\
                        y = (1 - s) * py (fst g) + s * py (snd g)))
              (ring_edges r)) as [rad0 [Hr0 Hball]].
  { intros g Hing.
    destruct (coord_point_dec (fst g) v) as [Hfv | Hfv].
    { exists 1. split; [ lra | ].
      intros rad Hr Hf. exfalso. exact (Hf Hfv). }
    destruct (coord_point_dec (snd g) v) as [Hsv | Hsv].
    { exists 1. split; [ lra | ].
      intros rad Hr _ Hs. exfalso. exact (Hs Hsv). }
    destruct (disk_edge_clear r e1 g v w Htaut Hin1 Hing Hor
                (Hnoh g Hing) Hfv Hsv) as [rg [Hrg Hclear]].
    exists rg. split; [ exact Hrg | ].
    intros rad Hr _ _. exact (Hclear rad Hr). }
  exists rad0. split; [ exact Hr0 | ].
  intros rad Hr g Hing Hfv Hsv x y Hx Hy.
  exact (Hball rad Hr g Hing Hfv Hsv x y Hx Hy).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions disk_edge_clear.
Print Assumptions corner_disk_clear.
