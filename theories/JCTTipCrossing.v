(* ============================================================================
   NetTopologySuite.Proofs.JCTTipCrossing
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-3: THE UNDER-TIP CROSSING.  At a LOCAL-MINIMUM
   corner -- every ring edge incident at the vertex v reaches weakly upward
   -- the horizontal band just below v is skeleton-free across the whole
   corner: the walk can pass from the west side of the corner to the east
   side underneath the tip.  This is the side-switch move: it connects the
   west-side passage destinations (rungs 5a/5c-2, which land in exactly
   this band) to the east-side corridors, and by the mirror kit its y-flip
   crosses OVER a local-maximum tip.

   Why it is free: incident edges live entirely at-or-above v's level
   (their points are convex combinations of endpoints at-or-above), so the
   strictly-below probe never meets them -- no slope bounds needed.
   Non-incident edges get explicit margins exactly as in the corner drop
   (rung 4b-3): an edge crossing v's level does so at abscissa X with
   |X - px v| = m > 0 (tautness: an edge through v would be incident,
   `taut_vertex_endpoint`), and for 8*delta < m and a thin band the probe
   segment [px v - 2*delta, px v + 2*delta] stays m/2 short of it
   (`hprobe_avoid_level_crossing`, the horizontal twin of
   `drop_avoid_level_crossing`); edges clear of the level are cleared by
   height margins.  The two-stage fold (rung 4b-3's `corner_fold`) gives
   the uniform delta0, then eps0(delta).

   `under_tip_crossing` packages the move: any two points of the band
   connect through the complement, off-ring, at a level chosen below v.
   The caller parks the level fresh via depth_gap when it needs the guard.

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
From NTS.Proofs Require Import JCTPassageKit.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  The horizontal-probe clearance against a level-crossing edge.
   --------------------------------------------------------------------------- *)

(* Horizontal twin of drop_avoid_level_crossing: the probe segment
   [px v - 2*delta, px v + 2*delta] at a height within eps of v's level
   misses an edge whose carrier crosses that level at abscissa X with
   |X - px v| = m > 0, for 8*delta < m and a thin band. *)
Lemma hprobe_avoid_level_crossing : forall (a b v : Point)
                                           (delta eps x y X : R),
  py a <> py b ->
  (X - px a) * (py b - py a) = (py v - py a) * (px b - px a) ->
  0 < delta -> 0 < eps ->
  8 * delta < Rabs (X - px v) ->
  4 * eps * (Rabs (px b - px a) + 1)
    < Rabs (X - px v) * Rabs (py b - py a) ->
  px v - 2 * delta <= x <= px v + 2 * delta ->
  py v - eps <= y <= py v + eps ->
  ~ (exists s : R, 0 <= s <= 1 /\
       x = (1 - s) * px a + s * px b /\
       y = (1 - s) * py a + s * py b).
Proof.
  intros a b v delta eps x y X Hnh HX Hd He Hdcap Hecap Hx Hband
    [s [Hs [Hxs Hys]]].
  assert (Hx2 : x - px a = s * (px b - px a)) by nra.
  assert (Hy2 : y - py a = s * (py b - py a)) by nra.
  apply (Rmult_eq_compat_r (py b - py a)) in Hx2.
  apply (Rmult_eq_compat_r (px b - px a)) in Hy2.
  assert (Hkey : (x - X) * (py b - py a) = (y - py v) * (px b - px a)) by nra.
  assert (Habs1 : Rabs (X - px v) / 2 <= Rabs (x - X)).
  { destruct (Rcase_abs (X - px v)) as [Hc | Hc].
    - rewrite (Rabs_left (X - px v) Hc) in *.
      rewrite (Rabs_right (x - X) ltac:(lra)). lra.
    - rewrite (Rabs_right (X - px v) Hc) in *.
      rewrite (Rabs_left (x - X) ltac:(lra)). lra. }
  assert (Hay : Rabs (y - py v) <= eps)
    by (unfold Rabs; destruct (Rcase_abs (y - py v)); lra).
  assert (Hprod : Rabs (x - X) * Rabs (py b - py a)
                    = Rabs (y - py v) * Rabs (px b - px a))
    by (rewrite <- !Rabs_mult; rewrite Hkey; reflexivity).
  pose proof (Rabs_pos (px b - px a)) as HDx.
  pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
  pose proof (Rabs_pos (x - X)) as HxX.
  assert (T1 : (Rabs (X - px v) / 2) * Rabs (py b - py a)
                 <= Rabs (x - X) * Rabs (py b - py a)) by nra.
  assert (T2 : Rabs (y - py v) * Rabs (px b - px a)
                 <= eps * Rabs (px b - px a)) by nra.
  nra.
Qed.

(* ---------------------------------------------------------------------------
   §2  Per-edge clearance of the under-tip band.
   --------------------------------------------------------------------------- *)

Lemma under_tip_edge_clear : forall (r : Ring) (e1 g : Edge) (v w : Point),
  ring_taut r ->
  In e1 (ring_edges r) -> In g (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  (forall g', In g' (ring_edges r) -> fst g' = v \/ snd g' = v ->
     py v <= py (fst g') /\ py v <= py (snd g')) ->
  exists dg, 0 < dg /\ forall delta, 0 < delta < dg ->
  exists eg, 0 < eg /\ forall eps, 0 < eps < eg ->
    forall x y,
      px v - 2 * delta <= x <= px v + 2 * delta ->
      py v - eps <= y < py v ->
      ~ (exists s : R, 0 <= s <= 1 /\
           x = (1 - s) * px (fst g) + s * px (snd g) /\
           y = (1 - s) * py (fst g) + s * py (snd g)).
Proof.
  intros r e1 g v w Htaut Hin1 Hing Hor Hmin.
  destruct g as [a b]; cbn [fst snd] in *.
  (* INCIDENT edges: entirely at-or-above the level, probe strictly below *)
  destruct (coord_point_dec a v) as [Hav | Hav].
  { destruct (Hmin (a, b) Hing ltac:(left; cbn; exact Hav)) as [HA HB];
      cbn [fst snd] in HA, HB.
    exists 1. split; [ lra | ]. intros delta Hd.
    exists 1. split; [ lra | ]. intros eps He x y Hx Hy
      [s [Hs [Hxs Hys]]].
    assert (T1 : 0 <= (1 - s) * (py a - py v)) by nra.
    assert (T2 : 0 <= s * (py b - py v)) by nra.
    nra. }
  destruct (coord_point_dec b v) as [Hbv | Hbv].
  { destruct (Hmin (a, b) Hing ltac:(right; cbn; exact Hbv)) as [HA HB];
      cbn [fst snd] in HA, HB.
    exists 1. split; [ lra | ]. intros delta Hd.
    exists 1. split; [ lra | ]. intros eps He x y Hx Hy
      [s [Hs [Hxs Hys]]].
    assert (T1 : 0 <= (1 - s) * (py a - py v)) by nra.
    assert (T2 : 0 <= s * (py b - py v)) by nra.
    nra. }
  (* NON-INCIDENT: any contact with v contradicts tautness *)
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
  - (* both strictly above the level: probe below the level *)
    exists 1. split; [ lra | ]. intros delta Hd.
    exists 1. split; [ lra | ]. intros eps He x y Hx Hy
      [s [Hs [Hxs Hys]]].
    assert (T1 : 0 <= (1 - s) * (py a - py v)) by nra.
    assert (T2 : 0 <= s * (py b - py v)) by nra.
    nra.
  - (* a above, b at-or-below: the carrier crosses the level *)
    assert (Hnh : py a <> py b) by lra.
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
    exists (Rabs (X - px v) / 8). split; [ lra | ]. intros delta Hd.
    pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
    pose proof (Rabs_pos (px b - px a)) as HDx.
    exists (Rabs (X - px v) * Rabs (py b - py a)
              / (4 * (Rabs (px b - px a) + 1))).
    split; [ apply Rdiv_lt_0_compat; nra | ].
    intros eps He x y Hx Hy.
    assert (Hcap : 4 * eps * (Rabs (px b - px a) + 1)
                     < Rabs (X - px v) * Rabs (py b - py a)).
    { destruct He as [He1 He2].
      apply (cap_mult eps _ (4 * (Rabs (px b - px a) + 1))
               ltac:(nra)) in He2.
      lra. }
    apply (hprobe_avoid_level_crossing a b v delta eps x y X Hnh HX
             ltac:(lra) ltac:(lra) ltac:(lra) Hcap Hx ltac:(lra)).
  - (* a at-or-below, b above: mirror *)
    assert (Hnh : py a <> py b) by lra.
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
    exists (Rabs (X - px v) / 8). split; [ lra | ]. intros delta Hd.
    pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
    pose proof (Rabs_pos (px b - px a)) as HDx.
    exists (Rabs (X - px v) * Rabs (py b - py a)
              / (4 * (Rabs (px b - px a) + 1))).
    split; [ apply Rdiv_lt_0_compat; nra | ].
    intros eps He x y Hx Hy.
    assert (Hcap : 4 * eps * (Rabs (px b - px a) + 1)
                     < Rabs (X - px v) * Rabs (py b - py a)).
    { destruct He as [He1 He2].
      apply (cap_mult eps _ (4 * (Rabs (px b - px a) + 1))
               ltac:(nra)) in He2.
      lra. }
    apply (hprobe_avoid_level_crossing a b v delta eps x y X Hnh HX
             ltac:(lra) ltac:(lra) ltac:(lra) Hcap Hx ltac:(lra)).
  - (* both at-or-below the level *)
    destruct (Req_EM_T (py a) (py v)) as [Hae | Hae];
    destruct (Req_EM_T (py b) (py v)) as [Hbe | Hbe].
    + (* horizontal AT the level: probe strictly below it *)
      exists 1. split; [ lra | ]. intros delta Hd.
      exists 1. split; [ lra | ]. intros eps He x y Hx Hy
        [s [Hs [Hxs Hys]]].
      nra.
    + (* a at the level, b strictly below: carrier crosses; X = px a <> px v *)
      assert (Hnh : py a <> py b) by lra.
      set (X := edge_x_at (a, b) (py v)).
      assert (HX : (X - px a) * (py b - py a) = (py v - py a) * (px b - px a))
        by (unfold X, edge_x_at; field; lra).
      assert (Hm : X <> px v).
      { intro Heq.
        apply (Hnotong 0 ltac:(lra)).
        assert (HX0 : X = px a) by nra.
        split; lra. }
      pose proof (Rabs_pos_lt (X - px v) ltac:(lra)) as Hmpos.
      exists (Rabs (X - px v) / 8). split; [ lra | ]. intros delta Hd.
      pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
      pose proof (Rabs_pos (px b - px a)) as HDx.
      exists (Rabs (X - px v) * Rabs (py b - py a)
                / (4 * (Rabs (px b - px a) + 1))).
      split; [ apply Rdiv_lt_0_compat; nra | ].
      intros eps He x y Hx Hy.
      assert (Hcap : 4 * eps * (Rabs (px b - px a) + 1)
                       < Rabs (X - px v) * Rabs (py b - py a)).
      { destruct He as [He1 He2].
        apply (cap_mult eps _ (4 * (Rabs (px b - px a) + 1))
                 ltac:(nra)) in He2.
        lra. }
      apply (hprobe_avoid_level_crossing a b v delta eps x y X Hnh HX
               ltac:(lra) ltac:(lra) ltac:(lra) Hcap Hx ltac:(lra)).
    + (* b at the level, a strictly below: X = px b <> px v *)
      assert (Hnh : py a <> py b) by lra.
      set (X := edge_x_at (a, b) (py v)).
      assert (HX : (X - px a) * (py b - py a) = (py v - py a) * (px b - px a))
        by (unfold X, edge_x_at; field; lra).
      assert (Hm : X <> px v).
      { intro Heq.
        apply (Hnotong 1 ltac:(lra)).
        assert (HX1 : X = px b) by nra.
        split; lra. }
      pose proof (Rabs_pos_lt (X - px v) ltac:(lra)) as Hmpos.
      exists (Rabs (X - px v) / 8). split; [ lra | ]. intros delta Hd.
      pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
      pose proof (Rabs_pos (px b - px a)) as HDx.
      exists (Rabs (X - px v) * Rabs (py b - py a)
                / (4 * (Rabs (px b - px a) + 1))).
      split; [ apply Rdiv_lt_0_compat; nra | ].
      intros eps He x y Hx Hy.
      assert (Hcap : 4 * eps * (Rabs (px b - px a) + 1)
                       < Rabs (X - px v) * Rabs (py b - py a)).
      { destruct He as [He1 He2].
        apply (cap_mult eps _ (4 * (Rabs (px b - px a) + 1))
                 ltac:(nra)) in He2.
        lra. }
      apply (hprobe_avoid_level_crossing a b v delta eps x y X Hnh HX
               ltac:(lra) ltac:(lra) ltac:(lra) Hcap Hx ltac:(lra)).
    + (* both strictly below: probe above them for a thin band *)
      exists 1. split; [ lra | ]. intros delta Hd.
      exists (Rmin (py v - py a) (py v - py b)).
      split; [ apply Rmin_glb_lt; lra | ].
      intros eps He x y Hx Hy [s [Hs [Hxs Hys]]].
      pose proof (Rmin_l (py v - py a) (py v - py b)).
      pose proof (Rmin_r (py v - py a) (py v - py b)).
      assert (T1 : (1 - s) * (py a - (py v - eps)) <= 0) by nra.
      assert (T2 : s * (py b - (py v - eps)) <= 0) by nra.
      nra.
Qed.

(* ---------------------------------------------------------------------------
   §3  THE UNDER-TIP CROSSING: the band below a local-minimum corner is
       skeleton-free, and any two of its points connect.
   --------------------------------------------------------------------------- *)

Theorem under_tip_clear : forall (r : Ring) (e1 : Edge) (v w : Point),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  (forall g, In g (ring_edges r) -> fst g = v \/ snd g = v ->
     py v <= py (fst g) /\ py v <= py (snd g)) ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    forall x y,
      px v - 2 * delta <= x <= px v + 2 * delta ->
      py v - eps <= y < py v ->
      ~ ring_image r (mkPoint x y).
Proof.
  intros r e1 v w Htaut Hin1 Hor Hmin.
  destruct (corner_fold
              (fun g delta eps =>
                 forall x y,
                   px v - 2 * delta <= x <= px v + 2 * delta ->
                   py v - eps <= y < py v ->
                   ~ (exists s : R, 0 <= s <= 1 /\
                        x = (1 - s) * px (fst g) + s * px (snd g) /\
                        y = (1 - s) * py (fst g) + s * py (snd g)))
              (ring_edges r)) as [d0 [Hd0 Hstage]].
  { intros g Hing.
    exact (under_tip_edge_clear r e1 g v w Htaut Hin1 Hing Hor Hmin). }
  exists d0. split; [ exact Hd0 | ].
  intros delta Hd.
  destruct (Hstage delta Hd) as [e0 [He0 Hball]].
  exists e0. split; [ exact He0 | ].
  intros eps He x y Hx Hy Himg.
  destruct Himg as [g [s [Hing [Hs [Hxs Hys]]]]].
  cbn [px py] in Hxs, Hys.
  apply (Hball eps ltac:(lra) g Hing x y Hx Hy).
  exists s. repeat split; try assumption; lra.
Qed.

Theorem under_tip_crossing : forall (r : Ring) (e1 : Edge) (v w : Point),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  (forall g, In g (ring_edges r) -> fst g = v \/ snd g = v ->
     py v <= py (fst g) /\ py v <= py (snd g)) ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    forall x1 x2,
      px v - 2 * delta <= x1 <= px v + 2 * delta ->
      px v - 2 * delta <= x2 <= px v + 2 * delta ->
      connected_in_complement_cont r
        (mkPoint x1 (py v - eps)) (mkPoint x2 (py v - eps)) /\
      ring_complement r (mkPoint x1 (py v - eps)).
Proof.
  intros r e1 v w Htaut Hin1 Hor Hmin.
  destruct (under_tip_clear r e1 v w Htaut Hin1 Hor Hmin)
    as [delta0 [Hd0 Hstage]].
  exists delta0. split; [ exact Hd0 | ].
  intros delta Hd.
  destruct (Hstage delta Hd) as [eps0 [He0 Hfree]].
  exists eps0. split; [ exact He0 | ].
  intros eps He x1 x2 Hx1 Hx2.
  assert (Hfree' : forall x, Rmin x1 x2 <= x <= Rmax x1 x2 ->
            ~ ring_image r (mkPoint x (py v - eps))).
  { intros x Hx.
    assert (Hlo : px v - 2 * delta <= Rmin x1 x2) by (apply Rmin_glb; lra).
    assert (Hhi : Rmax x1 x2 <= px v + 2 * delta) by (apply Rmax_lub; lra).
    apply (Hfree eps ltac:(lra) x (py v - eps)); lra. }
  split.
  - exact (horizontal_connected r (py v - eps) x1 x2 Hfree').
  - apply (Hfree eps ltac:(lra) x1 (py v - eps)); lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hprobe_avoid_level_crossing.
Print Assumptions under_tip_edge_clear.
Print Assumptions under_tip_crossing.
