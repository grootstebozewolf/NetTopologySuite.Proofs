(* ============================================================================
   NetTopologySuite.Proofs.JCTWalkKit
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 3: the walk kit -- window-clipped clearances and the
   jog connectors that chain corridor pieces.

   Rung 2 cleared edges that are globally west/east of the carrier or
   globally outside the height window.  The remaining generic case is the
   MIXED edge: only part of it overlaps the corridor's height window.  The
   key identity is the THREE-POINT AFFINE LAW: for the affine clearance
   function F(s) = edge_x_at e (y_f s) - x_f s along f,

       (s1 - s0) * F s = (s1 - s) * F s0 + (s - s0) * F s1,

   a pure `ring` fact.  So if the window-overlapping parameters are clipped
   into [s0, s1] and F clears delta at BOTH clip points, it clears delta on
   the whole overlap (`corridor_avoid_clipped_west`), and likewise for the
   east side (`corridor_avoid_clipped_east`).  `clip_params_asc`/`_desc`
   compute the clip points explicitly for non-horizontal edges (affine
   inversion, clamped by Rmax/Rmin).

   The jog connectors finish the kit: `horizontal_connected` and
   `vertical_connected` carry a point between two abscissae (resp. heights)
   along a skeleton-free axis segment -- the glue between consecutive
   corridors of rung 4's boundary walk.

   With rungs 1-3 the generic geometry is complete: every edge that does
   not TOUCH the carrier inside the window is clearable by an explicit
   margin, and all path pieces (east run-up, corridors, jogs) connect.
   What remains for rung 4 is per-polygon: touch-freedom from `ring_simple`
   (the `crossings_distinct` style), corner sectors at shared vertices, and
   the bounded recursion around the boundary.

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
From NTS.Proofs Require Import JCTEastApproach JCTCorridor.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  Window-clipped clearances via the three-point affine law.
   --------------------------------------------------------------------------- *)

Lemma corridor_avoid_clipped_west :
  forall (e f : Edge) (delta ylo yhi s0 s1 : R),
  py (fst e) <> py (snd e) ->
  (forall s, 0 <= s <= 1 ->
     ylo <= (1 - s) * py (fst f) + s * py (snd f) <= yhi ->
     s0 <= s <= s1) ->
  (1 - s0) * px (fst f) + s0 * px (snd f) + delta
    < edge_x_at e ((1 - s0) * py (fst f) + s0 * py (snd f)) ->
  (1 - s1) * px (fst f) + s1 * px (snd f) + delta
    < edge_x_at e ((1 - s1) * py (fst f) + s1 * py (snd f)) ->
  forall y, ylo <= y <= yhi ->
  ~ (exists s : R, 0 <= s <= 1 /\
       edge_x_at e y - delta = (1 - s) * px (fst f) + s * px (snd f) /\
       y = (1 - s) * py (fst f) + s * py (snd f)).
Proof.
  intros e f delta ylo yhi s0 s1 Hnh Hclip H0 H1 y Hw [s [Hs [Hx Hy]]].
  assert (Hwin : ylo <= (1 - s) * py (fst f) + s * py (snd f) <= yhi)
    by (rewrite <- Hy; exact Hw).
  pose proof (Hclip s Hs Hwin) as Hs01.
  destruct e as [a b]; cbn [fst snd] in *.
  unfold edge_x_at in *.
  set (al := (px b - px a) / (py b - py a)) in *.
  assert (Hlin : forall z : R,
            px a + (px b - px a) * (z - py a) / (py b - py a)
              = al * z + (px a - al * py a))
    by (intro z; unfold al; field; lra).
  rewrite Hlin in Hx, H0, H1.
  rewrite Hy in Hx.
  set (F := fun s' : R =>
        al * ((1 - s') * py (fst f) + s' * py (snd f))
          + (px a - al * py a)
          - ((1 - s') * px (fst f) + s' * px (snd f))).
  assert (HF0 : delta < F s0) by (unfold F; lra).
  assert (HF1 : delta < F s1) by (unfold F; lra).
  assert (HFs : F s = delta) by (unfold F; lra).
  assert (Hkey : (s1 - s0) * F s = (s1 - s) * F s0 + (s - s0) * F s1)
    by (unfold F; ring).
  destruct (Rle_or_lt s1 s0) as [Hdeg | Hord].
  - assert (Hss0 : s = s0) by lra.
    rewrite Hss0 in HFs. lra.
  - destruct (Rle_or_lt s s0) as [Hss0 | Hgt].
    + assert (Hss0' : s = s0) by lra.
      rewrite Hss0' in HFs. lra.
    + assert (T1 : 0 < (s - s0) * (F s1 - delta)) by nra.
      assert (T2 : 0 <= (s1 - s) * (F s0 - delta)) by nra.
      nra.
Qed.

Lemma corridor_avoid_clipped_east :
  forall (e f : Edge) (delta ylo yhi s0 s1 : R),
  py (fst e) <> py (snd e) ->
  0 < delta ->
  (forall s, 0 <= s <= 1 ->
     ylo <= (1 - s) * py (fst f) + s * py (snd f) <= yhi ->
     s0 <= s <= s1) ->
  edge_x_at e ((1 - s0) * py (fst f) + s0 * py (snd f))
    < (1 - s0) * px (fst f) + s0 * px (snd f) ->
  edge_x_at e ((1 - s1) * py (fst f) + s1 * py (snd f))
    < (1 - s1) * px (fst f) + s1 * px (snd f) ->
  forall y, ylo <= y <= yhi ->
  ~ (exists s : R, 0 <= s <= 1 /\
       edge_x_at e y - delta = (1 - s) * px (fst f) + s * px (snd f) /\
       y = (1 - s) * py (fst f) + s * py (snd f)).
Proof.
  intros e f delta ylo yhi s0 s1 Hnh Hd Hclip H0 H1 y Hw [s [Hs [Hx Hy]]].
  assert (Hwin : ylo <= (1 - s) * py (fst f) + s * py (snd f) <= yhi)
    by (rewrite <- Hy; exact Hw).
  pose proof (Hclip s Hs Hwin) as Hs01.
  destruct e as [a b]; cbn [fst snd] in *.
  unfold edge_x_at in *.
  set (al := (px b - px a) / (py b - py a)) in *.
  assert (Hlin : forall z : R,
            px a + (px b - px a) * (z - py a) / (py b - py a)
              = al * z + (px a - al * py a))
    by (intro z; unfold al; field; lra).
  rewrite Hlin in Hx, H0, H1.
  rewrite Hy in Hx.
  set (F := fun s' : R =>
        al * ((1 - s') * py (fst f) + s' * py (snd f))
          + (px a - al * py a)
          - ((1 - s') * px (fst f) + s' * px (snd f))).
  assert (HF0 : F s0 < 0) by (unfold F; lra).
  assert (HF1 : F s1 < 0) by (unfold F; lra).
  assert (HFs : F s = delta) by (unfold F; lra).
  assert (Hkey : (s1 - s0) * F s = (s1 - s) * F s0 + (s - s0) * F s1)
    by (unfold F; ring).
  destruct (Rle_or_lt s1 s0) as [Hdeg | Hord].
  - assert (Hss0 : s = s0) by lra.
    rewrite Hss0 in HFs. lra.
  - assert (T1 : (s - s0) * F s1 <= 0) by nra.
    assert (T2 : (s1 - s) * F s0 <= 0) by nra.
    nra.
Qed.

(* ---------------------------------------------------------------------------
   §2  Explicit clip points for non-horizontal edges (affine inversion).
   --------------------------------------------------------------------------- *)

Lemma clip_params_asc : forall (f : Edge) (ylo yhi s : R),
  py (fst f) < py (snd f) ->
  0 <= s <= 1 ->
  ylo <= (1 - s) * py (fst f) + s * py (snd f) <= yhi ->
  Rmax 0 ((ylo - py (fst f)) / (py (snd f) - py (fst f))) <= s /\
  s <= Rmin 1 ((yhi - py (fst f)) / (py (snd f) - py (fst f))).
Proof.
  intros f ylo yhi s Hasc Hs Hw.
  set (d := py (snd f) - py (fst f)).
  assert (Hd : 0 < d) by (unfold d; lra).
  split.
  - apply Rmax_lub; [ lra | ].
    apply Rmult_le_reg_r with d; [ exact Hd | ].
    replace ((ylo - py (fst f)) / d * d) with (ylo - py (fst f))
      by (field; lra).
    unfold d. nra.
  - apply Rmin_glb; [ lra | ].
    apply Rmult_le_reg_r with d; [ exact Hd | ].
    replace ((yhi - py (fst f)) / d * d) with (yhi - py (fst f))
      by (field; lra).
    unfold d. nra.
Qed.

Lemma clip_params_desc : forall (f : Edge) (ylo yhi s : R),
  py (snd f) < py (fst f) ->
  0 <= s <= 1 ->
  ylo <= (1 - s) * py (fst f) + s * py (snd f) <= yhi ->
  Rmax 0 ((py (fst f) - yhi) / (py (fst f) - py (snd f))) <= s /\
  s <= Rmin 1 ((py (fst f) - ylo) / (py (fst f) - py (snd f))).
Proof.
  intros f ylo yhi s Hdesc Hs Hw.
  set (d := py (fst f) - py (snd f)).
  assert (Hd : 0 < d) by (unfold d; lra).
  split.
  - apply Rmax_lub; [ lra | ].
    apply Rmult_le_reg_r with d; [ exact Hd | ].
    replace ((py (fst f) - yhi) / d * d) with (py (fst f) - yhi)
      by (field; lra).
    unfold d. nra.
  - apply Rmin_glb; [ lra | ].
    apply Rmult_le_reg_r with d; [ exact Hd | ].
    replace ((py (fst f) - ylo) / d * d) with (py (fst f) - ylo)
      by (field; lra).
    unfold d. nra.
Qed.

(* ---------------------------------------------------------------------------
   §3  Jog connectors: axis-aligned glue between corridor pieces.
   --------------------------------------------------------------------------- *)

Lemma horizontal_connected : forall (r : Ring) (y x1 x2 : R),
  (forall x, Rmin x1 x2 <= x <= Rmax x1 x2 ->
     ~ ring_image r (mkPoint x y)) ->
  connected_in_complement_cont r (mkPoint x1 y) (mkPoint x2 y).
Proof.
  intros r y x1 x2 Hfree.
  exists (fun t => mkPoint ((1 - t) * x1 + t * x2) ((1 - t) * y + t * y)).
  split; [ apply straight_path_continuous | ]. split; [ | split ].
  - cbn [px py]; f_equal; lra.
  - cbn [px py]; f_equal; lra.
  - intros t Ht Himg.
    assert (Hco : (1 - t) * y + t * y = y) by ring.
    rewrite Hco in Himg.
    refine (Hfree ((1 - t) * x1 + t * x2) _ Himg).
    pose proof (Rmin_l x1 x2). pose proof (Rmin_r x1 x2).
    pose proof (Rmax_l x1 x2). pose proof (Rmax_r x1 x2).
    split; nra.
Qed.

Lemma vertical_connected : forall (r : Ring) (x y1 y2 : R),
  (forall y, Rmin y1 y2 <= y <= Rmax y1 y2 ->
     ~ ring_image r (mkPoint x y)) ->
  connected_in_complement_cont r (mkPoint x y1) (mkPoint x y2).
Proof.
  intros r x y1 y2 Hfree.
  exists (fun t => mkPoint ((1 - t) * x + t * x) ((1 - t) * y1 + t * y2)).
  split; [ apply straight_path_continuous | ]. split; [ | split ].
  - cbn [px py]; f_equal; lra.
  - cbn [px py]; f_equal; lra.
  - intros t Ht Himg.
    assert (Hco : (1 - t) * x + t * x = x) by ring.
    rewrite Hco in Himg.
    refine (Hfree ((1 - t) * y1 + t * y2) _ Himg).
    pose proof (Rmin_l y1 y2). pose proof (Rmin_r y1 y2).
    pose proof (Rmax_l y1 y2). pose proof (Rmax_r y1 y2).
    split; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions corridor_avoid_clipped_west.
Print Assumptions corridor_avoid_clipped_east.
Print Assumptions clip_params_asc.
Print Assumptions horizontal_connected.
