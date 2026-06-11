(* ============================================================================
   NetTopologySuite.Proofs.JCTWallClear
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 4b-2: the per-edge clearance case tree and the
   uniform offset -- for a TAUT ring, the wall's corridor is skeleton-free
   for every sufficiently small positive offset (`wall_corridor_clear`).

   The unifying device is `touch_clearance`: if any edge meets the
   carrier's line at a window height (a "touch witness"), then by
   `taut_no_line_touch` that edge IS the carrier pointwise, and the carrier
   is missed by every positive offset (`corridor_avoid_carrier`).  So every
   branch of the case tree either produces an explicit positive margin or a
   touch witness:

     - edges entirely below/above the window: margin 1 (rung-2 helpers);
     - horizontal edges at a window height: the carrier abscissa at that
       height either lies outside the edge's x-range (west: explicit
       endpoint margin; east: margin 1) or inside it (touch witness by
       affine inversion of the x-interpolation);
     - sloped edges overlapping the window: clip (rung 4b-1), evaluate the
       clearance at the two clip points, and decide -- both positive: the
       clipped-west margin (rung 3); both negative: clipped-east, margin 1;
       a zero or a sign change: an `affine_root` zero inside the clip
       range, i.e. a touch witness.

   `clear_fold` Rmin-folds the per-edge margins over the edge list, and
   `wall_corridor_clear` plugs the result into `corridor_free_of_edges`.
   Together with `walk_step_guarded` this discharges every hypothesis of
   the walk step for taut rings except the choice of the window itself --
   rung 4b-3's corner-and-recursion business.

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
From NTS.Proofs Require Import JCTTautClearance.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  A touch witness clears the edge outright (it IS the carrier).
   --------------------------------------------------------------------------- *)

Lemma touch_clearance : forall (r : Ring) (e1 f : Edge) (ylo yhi : R),
  ring_taut r ->
  In e1 (ring_edges r) -> In f (ring_edges r) ->
  py (fst e1) <> py (snd e1) ->
  ((py (fst e1) < ylo /\ yhi < py (snd e1)) \/
   (py (snd e1) < ylo /\ yhi < py (fst e1))) ->
  (exists s y : R, 0 <= s <= 1 /\ ylo <= y <= yhi /\
     y = (1 - s) * py (fst f) + s * py (snd f) /\
     edge_x_at e1 y = (1 - s) * px (fst f) + s * px (snd f)) ->
  forall (delta y' : R), 0 < delta ->
    ~ (exists s : R, 0 <= s <= 1 /\
         edge_x_at e1 y' - delta = (1 - s) * px (fst f) + s * px (snd f) /\
         y' = (1 - s) * py (fst f) + s * py (snd f)).
Proof.
  intros r e1 f ylo yhi Htaut Hin1 Hinf Hnh Hspan
         [s [y [Hs [Hw [Hy Hx]]]]] delta y' Hd.
  destruct (taut_no_line_touch r e1 f ylo yhi Htaut Hin1 Hinf Hnh Hspan
              s y Hs Hw Hy Hx) as [Hf1 Hf2].
  rewrite <- Hf1, <- Hf2.
  apply corridor_avoid_carrier; assumption.
Qed.

(* ---------------------------------------------------------------------------
   §2  The per-edge clearance.
   --------------------------------------------------------------------------- *)

Lemma per_edge_clear : forall (r : Ring) (e1 f : Edge) (ylo yhi : R),
  ring_taut r ->
  In e1 (ring_edges r) -> In f (ring_edges r) ->
  ((py (fst e1) < ylo /\ yhi < py (snd e1)) \/
   (py (snd e1) < ylo /\ yhi < py (fst e1))) ->
  ylo <= yhi ->
  exists df, 0 < df /\
    forall delta, 0 < delta < df ->
      forall y, ylo <= y <= yhi ->
        ~ (exists s : R, 0 <= s <= 1 /\
             edge_x_at e1 y - delta = (1 - s) * px (fst f) + s * px (snd f) /\
             y = (1 - s) * py (fst f) + s * py (snd f)).
Proof.
  intros r e1 f ylo yhi Htaut Hin1 Hinf Hspan Hle.
  assert (Hnh : py (fst e1) <> py (snd e1)) by (destruct Hspan; lra).
  (* shorthand for invoking the touch route *)
  assert (Htouch : (exists s y : R, 0 <= s <= 1 /\ ylo <= y <= yhi /\
            y = (1 - s) * py (fst f) + s * py (snd f) /\
            edge_x_at e1 y = (1 - s) * px (fst f) + s * px (snd f)) ->
          exists df, 0 < df /\
            forall delta, 0 < delta < df ->
              forall y, ylo <= y <= yhi ->
                ~ (exists s : R, 0 <= s <= 1 /\
                     edge_x_at e1 y - delta
                       = (1 - s) * px (fst f) + s * px (snd f) /\
                     y = (1 - s) * py (fst f) + s * py (snd f))).
  { intro Hex. exists 1. split; [ lra | ].
    intros delta Hd y Hw.
    exact (touch_clearance r e1 f ylo yhi Htaut Hin1 Hinf Hnh Hspan
             Hex delta y ltac:(lra)). }
  destruct (Rtotal_order (py (fst f)) (py (snd f))) as [Hasc | [Hflat | Hdesc]].
  - (* ascending f *)
    destruct (Rle_or_lt ylo (py (snd f))) as [Hov1 | Hbelow];
      [ | (* entirely below *) exists 1; split; [ lra | ];
          intros delta Hd y Hw;
          apply (corridor_avoid_below e1 f delta ylo yhi y Hw); lra ].
    destruct (Rle_or_lt (py (fst f)) yhi) as [Hov2 | Habove];
      [ | (* entirely above *) exists 1; split; [ lra | ];
          intros delta Hd y Hw;
          apply (corridor_avoid_above e1 f delta ylo yhi y Hw); lra ].
    (* overlapping: clip and decide signs *)
    pose proof (clip_ordered_asc f ylo yhi Hasc Hle Hov2 Hov1) as CL.
    cbv zeta in CL.
    set (s0 := Rmax 0 ((ylo - py (fst f)) / (py (snd f) - py (fst f)))) in *.
    set (s1 := Rmin 1 ((yhi - py (fst f)) / (py (snd f) - py (fst f)))) in *.
    destruct CL as [Hs00 [Hs01 [Hs11 [Hc0lo [Hc0hi [Hc1lo Hc1hi]]]]]].
    set (G0 := edge_x_at e1 ((1 - s0) * py (fst f) + s0 * py (snd f))
                 - ((1 - s0) * px (fst f) + s0 * px (snd f))).
    set (G1 := edge_x_at e1 ((1 - s1) * py (fst f) + s1 * py (snd f))
                 - ((1 - s1) * px (fst f) + s1 * px (snd f))).
    assert (Hclip : forall s, 0 <= s <= 1 ->
              ylo <= (1 - s) * py (fst f) + s * py (snd f) <= yhi ->
              s0 <= s <= s1)
      by (intros s Hs Hw; exact (clip_params_asc f ylo yhi s Hasc Hs Hw)).
    destruct (Rtotal_order 0 G0) as [HG0p | [HG0z | HG0n]].
    + destruct (Rtotal_order 0 G1) as [HG1p | [HG1z | HG1n]].
      * (* both west: clipped-west margin *)
        exists (Rmin G0 G1). split; [ apply Rmin_glb_lt; lra | ].
        intros delta Hd y Hw.
        pose proof (Rmin_l G0 G1). pose proof (Rmin_r G0 G1).
        apply (corridor_avoid_clipped_west e1 f delta ylo yhi s0 s1 Hnh Hclip);
          try assumption; unfold G0, G1 in *; lra.
      * (* zero at s1: touch at the clip *)
        apply Htouch. exists s1, ((1 - s1) * py (fst f) + s1 * py (snd f)).
        repeat split; try lra. unfold G1 in HG1z. lra.
      * (* sign change: an affine root inside the clip range *)
        (* linearise the carrier and extract the affine form of G *)
        destruct e1 as [a1 b1]; cbn [fst snd] in *.
        set (al := (px b1 - px a1) / (py b1 - py a1)).
        assert (Hlin : forall z : R,
                  edge_x_at (a1, b1) z = al * z + (px a1 - al * py a1)).
        { intro z. unfold edge_x_at, al. cbn [fst snd]. field. lra. }
        set (A := al * (py (snd f) - py (fst f))
                    - (px (snd f) - px (fst f))).
        set (B := al * py (fst f) + (px a1 - al * py a1) - px (fst f)).
        assert (HGA : forall s : R,
                  edge_x_at (a1, b1) ((1 - s) * py (fst f) + s * py (snd f))
                    - ((1 - s) * px (fst f) + s * px (snd f))
                  = A * s + B)
          by (intro s; rewrite Hlin; unfold A, B; ring).
        assert (Hprod : (A * s0 + B) * (A * s1 + B) <= 0).
        { rewrite <- (HGA s0), <- (HGA s1). unfold G0, G1 in *. nra. }
        destruct (affine_root A B s0 s1 Hs01 Hprod) as [sr [Hsr Hzero]].
        apply Htouch.
        exists sr, ((1 - sr) * py (fst f) + sr * py (snd f)).
        assert (Hmono : forall u v : R, u <= v ->
                  (1 - u) * py (fst f) + u * py (snd f)
                    <= (1 - v) * py (fst f) + v * py (snd f))
          by (intros u v Huv; nra).
        pose proof (Hmono s0 sr ltac:(lra)).
        pose proof (Hmono sr s1 ltac:(lra)).
        repeat split; try lra.
        rewrite <- (HGA sr) in Hzero. lra.
    + (* zero at s0: touch at the clip *)
      apply Htouch. exists s0, ((1 - s0) * py (fst f) + s0 * py (snd f)).
      repeat split; try lra. unfold G0 in HG0z. lra.
    + destruct (Rtotal_order 0 G1) as [HG1p | [HG1z | HG1n]].
      * (* sign change, mirrored *)
        destruct e1 as [a1 b1]; cbn [fst snd] in *.
        set (al := (px b1 - px a1) / (py b1 - py a1)).
        assert (Hlin : forall z : R,
                  edge_x_at (a1, b1) z = al * z + (px a1 - al * py a1)).
        { intro z. unfold edge_x_at, al. cbn [fst snd]. field. lra. }
        set (A := al * (py (snd f) - py (fst f))
                    - (px (snd f) - px (fst f))).
        set (B := al * py (fst f) + (px a1 - al * py a1) - px (fst f)).
        assert (HGA : forall s : R,
                  edge_x_at (a1, b1) ((1 - s) * py (fst f) + s * py (snd f))
                    - ((1 - s) * px (fst f) + s * px (snd f))
                  = A * s + B)
          by (intro s; rewrite Hlin; unfold A, B; ring).
        assert (Hprod : (A * s0 + B) * (A * s1 + B) <= 0).
        { rewrite <- (HGA s0), <- (HGA s1). unfold G0, G1 in *. nra. }
        destruct (affine_root A B s0 s1 Hs01 Hprod) as [sr [Hsr Hzero]].
        apply Htouch.
        exists sr, ((1 - sr) * py (fst f) + sr * py (snd f)).
        assert (Hmono : forall u v : R, u <= v ->
                  (1 - u) * py (fst f) + u * py (snd f)
                    <= (1 - v) * py (fst f) + v * py (snd f))
          by (intros u v Huv; nra).
        pose proof (Hmono s0 sr ltac:(lra)).
        pose proof (Hmono sr s1 ltac:(lra)).
        repeat split; try lra.
        rewrite <- (HGA sr) in Hzero. lra.
      * apply Htouch. exists s1, ((1 - s1) * py (fst f) + s1 * py (snd f)).
        repeat split; try lra. unfold G1 in HG1z. lra.
      * (* both east *)
        exists 1. split; [ lra | ].
        intros delta Hd y Hw.
        apply (corridor_avoid_clipped_east e1 f delta ylo yhi s0 s1 Hnh
                 ltac:(lra) Hclip); try assumption;
          unfold G0, G1 in *; lra.
  - (* horizontal f *)
    destruct (Rle_or_lt ylo (py (fst f))) as [Hov1 | Hbelow];
      [ | exists 1; split; [ lra | ];
          intros delta Hd y Hw;
          apply (corridor_avoid_below e1 f delta ylo yhi y Hw); lra ].
    destruct (Rle_or_lt (py (fst f)) yhi) as [Hov2 | Habove];
      [ | exists 1; split; [ lra | ];
          intros delta Hd y Hw;
          apply (corridor_avoid_above e1 f delta ylo yhi y Hw); lra ].
    set (cs := edge_x_at e1 (py (fst f))).
    assert (Hcs2 : edge_x_at e1 (py (snd f)) = cs)
      by (unfold cs; rewrite Hflat; reflexivity).
    destruct (Rtotal_order (px (fst f)) cs) as [Hp1 | [Hp1 | Hp1]];
    destruct (Rtotal_order (px (snd f)) cs) as [Hp2 | [Hp2 | Hp2]].
    + (* both west *)
      exists (Rmin (cs - px (fst f)) (cs - px (snd f))).
      split; [ apply Rmin_glb_lt; lra | ].
      intros delta Hd y Hw.
      pose proof (Rmin_l (cs - px (fst f)) (cs - px (snd f))).
      pose proof (Rmin_r (cs - px (fst f)) (cs - px (snd f))).
      apply (corridor_avoid_west e1 f delta y Hnh); unfold cs in *; lra.
    + (* snd at the carrier: touch at s = 1 *)
      apply Htouch. exists 1, (py (snd f)).
      repeat split; try lra.
    + (* straddles the carrier: interior touch by affine inversion *)
      apply Htouch.
      assert (Hne : px (snd f) - px (fst f) <> 0) by lra.
      set (sr := (cs - px (fst f)) / (px (snd f) - px (fst f))).
      assert (Hsr : 0 <= sr <= 1).
      { unfold sr. split.
        - apply Rmult_le_reg_r with (px (snd f) - px (fst f)); [ lra | ].
          replace ((cs - px (fst f)) / (px (snd f) - px (fst f))
                     * (px (snd f) - px (fst f)))
            with (cs - px (fst f)) by (field; lra). lra.
        - apply Rmult_le_reg_r with (px (snd f) - px (fst f)); [ lra | ].
          replace ((cs - px (fst f)) / (px (snd f) - px (fst f))
                     * (px (snd f) - px (fst f)))
            with (cs - px (fst f)) by (field; lra). lra. }
      exists sr, (py (fst f)).
      repeat split; try lra.
      * rewrite Hflat. ring_simplify. rewrite <- Hflat. ring_simplify. lra.
      * replace ((1 - sr) * px (fst f) + sr * px (snd f))
          with (px (fst f) + sr * (px (snd f) - px (fst f))) by ring.
        unfold sr. unfold cs.
        replace ((edge_x_at e1 (py (fst f)) - px (fst f))
                   / (px (snd f) - px (fst f)) * (px (snd f) - px (fst f)))
          with (edge_x_at e1 (py (fst f)) - px (fst f)) by (field; lra).
        lra.
    + (* fst at the carrier: touch at s = 0 *)
      apply Htouch. exists 0, (py (fst f)).
      unfold cs in Hp1.
      repeat split; try lra.
    + (* both at the carrier: touch at s = 0 *)
      apply Htouch. exists 0, (py (fst f)).
      unfold cs in Hp1.
      repeat split; try lra.
    + (* fst at the carrier: touch at s = 0 *)
      apply Htouch. exists 0, (py (fst f)).
      unfold cs in Hp1.
      repeat split; try lra.
    + (* straddles, mirrored: interior touch *)
      apply Htouch.
      assert (Hne : px (snd f) - px (fst f) <> 0) by lra.
      set (sr := (cs - px (fst f)) / (px (snd f) - px (fst f))).
      assert (Hsr : 0 <= sr <= 1).
      { unfold sr. split.
        - apply Rmult_le_reg_r with (px (fst f) - px (snd f)); [ lra | ].
          replace ((cs - px (fst f)) / (px (snd f) - px (fst f))
                     * (px (fst f) - px (snd f)))
            with (px (fst f) - cs) by (field; lra). lra.
        - apply Rmult_le_reg_r with (px (fst f) - px (snd f)); [ lra | ].
          replace ((cs - px (fst f)) / (px (snd f) - px (fst f))
                     * (px (fst f) - px (snd f)))
            with (px (fst f) - cs) by (field; lra). lra. }
      exists sr, (py (fst f)).
      repeat split; try lra.
      * rewrite Hflat. ring_simplify. rewrite <- Hflat. ring_simplify. lra.
      * replace ((1 - sr) * px (fst f) + sr * px (snd f))
          with (px (fst f) + sr * (px (snd f) - px (fst f))) by ring.
        unfold sr. unfold cs.
        replace ((edge_x_at e1 (py (fst f)) - px (fst f))
                   / (px (snd f) - px (fst f)) * (px (snd f) - px (fst f)))
          with (edge_x_at e1 (py (fst f)) - px (fst f)) by (field; lra).
        lra.
    + (* snd at the carrier: touch at s = 1 *)
      apply Htouch. exists 1, (py (snd f)).
      repeat split; try lra.
    + (* both east *)
      exists 1. split; [ lra | ].
      intros delta Hd y Hw.
      apply (corridor_avoid_east e1 f delta y Hnh ltac:(lra));
        unfold cs in *; lra.
  - (* descending f: mirror of the ascending case *)
    destruct (Rle_or_lt ylo (py (fst f))) as [Hov1 | Hbelow];
      [ | exists 1; split; [ lra | ];
          intros delta Hd y Hw;
          apply (corridor_avoid_below e1 f delta ylo yhi y Hw); lra ].
    destruct (Rle_or_lt (py (snd f)) yhi) as [Hov2 | Habove];
      [ | exists 1; split; [ lra | ];
          intros delta Hd y Hw;
          apply (corridor_avoid_above e1 f delta ylo yhi y Hw); lra ].
    pose proof (clip_ordered_desc f ylo yhi Hdesc Hle Hov2 Hov1) as CL.
    cbv zeta in CL.
    set (s0 := Rmax 0 ((py (fst f) - yhi) / (py (fst f) - py (snd f)))) in *.
    set (s1 := Rmin 1 ((py (fst f) - ylo) / (py (fst f) - py (snd f)))) in *.
    destruct CL as [Hs00 [Hs01 [Hs11 [Hc0lo [Hc0hi [Hc1lo Hc1hi]]]]]].
    set (G0 := edge_x_at e1 ((1 - s0) * py (fst f) + s0 * py (snd f))
                 - ((1 - s0) * px (fst f) + s0 * px (snd f))).
    set (G1 := edge_x_at e1 ((1 - s1) * py (fst f) + s1 * py (snd f))
                 - ((1 - s1) * px (fst f) + s1 * px (snd f))).
    assert (Hclip : forall s, 0 <= s <= 1 ->
              ylo <= (1 - s) * py (fst f) + s * py (snd f) <= yhi ->
              s0 <= s <= s1)
      by (intros s Hs Hw; exact (clip_params_desc f ylo yhi s Hdesc Hs Hw)).
    destruct (Rtotal_order 0 G0) as [HG0p | [HG0z | HG0n]].
    + destruct (Rtotal_order 0 G1) as [HG1p | [HG1z | HG1n]].
      * exists (Rmin G0 G1). split; [ apply Rmin_glb_lt; lra | ].
        intros delta Hd y Hw.
        pose proof (Rmin_l G0 G1). pose proof (Rmin_r G0 G1).
        apply (corridor_avoid_clipped_west e1 f delta ylo yhi s0 s1 Hnh Hclip);
          try assumption; unfold G0, G1 in *; lra.
      * apply Htouch. exists s1, ((1 - s1) * py (fst f) + s1 * py (snd f)).
        repeat split; try lra. unfold G1 in HG1z. lra.
      * destruct e1 as [a1 b1]; cbn [fst snd] in *.
        set (al := (px b1 - px a1) / (py b1 - py a1)).
        assert (Hlin : forall z : R,
                  edge_x_at (a1, b1) z = al * z + (px a1 - al * py a1)).
        { intro z. unfold edge_x_at, al. cbn [fst snd]. field. lra. }
        set (A := al * (py (snd f) - py (fst f))
                    - (px (snd f) - px (fst f))).
        set (B := al * py (fst f) + (px a1 - al * py a1) - px (fst f)).
        assert (HGA : forall s : R,
                  edge_x_at (a1, b1) ((1 - s) * py (fst f) + s * py (snd f))
                    - ((1 - s) * px (fst f) + s * px (snd f))
                  = A * s + B)
          by (intro s; rewrite Hlin; unfold A, B; ring).
        assert (Hprod : (A * s0 + B) * (A * s1 + B) <= 0).
        { rewrite <- (HGA s0), <- (HGA s1). unfold G0, G1 in *. nra. }
        destruct (affine_root A B s0 s1 Hs01 Hprod) as [sr [Hsr Hzero]].
        apply Htouch.
        exists sr, ((1 - sr) * py (fst f) + sr * py (snd f)).
        assert (Hmono : forall u v : R, u <= v ->
                  (1 - v) * py (fst f) + v * py (snd f)
                    <= (1 - u) * py (fst f) + u * py (snd f))
          by (intros u v Huv; nra).
        pose proof (Hmono s0 sr ltac:(lra)).
        pose proof (Hmono sr s1 ltac:(lra)).
        repeat split; try lra.
        rewrite <- (HGA sr) in Hzero. lra.
    + apply Htouch. exists s0, ((1 - s0) * py (fst f) + s0 * py (snd f)).
      repeat split; try lra. unfold G0 in HG0z. lra.
    + destruct (Rtotal_order 0 G1) as [HG1p | [HG1z | HG1n]].
      * destruct e1 as [a1 b1]; cbn [fst snd] in *.
        set (al := (px b1 - px a1) / (py b1 - py a1)).
        assert (Hlin : forall z : R,
                  edge_x_at (a1, b1) z = al * z + (px a1 - al * py a1)).
        { intro z. unfold edge_x_at, al. cbn [fst snd]. field. lra. }
        set (A := al * (py (snd f) - py (fst f))
                    - (px (snd f) - px (fst f))).
        set (B := al * py (fst f) + (px a1 - al * py a1) - px (fst f)).
        assert (HGA : forall s : R,
                  edge_x_at (a1, b1) ((1 - s) * py (fst f) + s * py (snd f))
                    - ((1 - s) * px (fst f) + s * px (snd f))
                  = A * s + B)
          by (intro s; rewrite Hlin; unfold A, B; ring).
        assert (Hprod : (A * s0 + B) * (A * s1 + B) <= 0).
        { rewrite <- (HGA s0), <- (HGA s1). unfold G0, G1 in *. nra. }
        destruct (affine_root A B s0 s1 Hs01 Hprod) as [sr [Hsr Hzero]].
        apply Htouch.
        exists sr, ((1 - sr) * py (fst f) + sr * py (snd f)).
        assert (Hmono : forall u v : R, u <= v ->
                  (1 - v) * py (fst f) + v * py (snd f)
                    <= (1 - u) * py (fst f) + u * py (snd f))
          by (intros u v Huv; nra).
        pose proof (Hmono s0 sr ltac:(lra)).
        pose proof (Hmono sr s1 ltac:(lra)).
        repeat split; try lra.
        rewrite <- (HGA sr) in Hzero. lra.
      * apply Htouch. exists s1, ((1 - s1) * py (fst f) + s1 * py (snd f)).
        repeat split; try lra. unfold G1 in HG1z. lra.
      * exists 1. split; [ lra | ].
        intros delta Hd y Hw.
        apply (corridor_avoid_clipped_east e1 f delta ylo yhi s0 s1 Hnh
                 ltac:(lra) Hclip); try assumption;
          unfold G0, G1 in *; lra.
Qed.

(* ---------------------------------------------------------------------------
   §3  The fold and the wall theorem.
   --------------------------------------------------------------------------- *)

Lemma clear_fold : forall (P : Edge -> R -> Prop) (es : list Edge),
  (forall f, In f es ->
     exists df, 0 < df /\ forall delta, 0 < delta < df -> P f delta) ->
  exists d0, 0 < d0 /\
    forall delta, 0 < delta < d0 -> forall f, In f es -> P f delta.
Proof.
  intros P; induction es as [| e es' IH]; intros Hall.
  - exists 1. split; [ lra | ]. intros delta Hd f [].
  - destruct (Hall e (or_introl eq_refl)) as [d1 [Hd1 Hb1]].
    destruct (IH (fun f Hf => Hall f (or_intror Hf))) as [d2 [Hd2 Hb2]].
    exists (Rmin d1 d2). split; [ apply Rmin_glb_lt; lra | ].
    intros delta Hd f Hin.
    pose proof (Rmin_l d1 d2). pose proof (Rmin_r d1 d2).
    destruct Hin as [He | Hin].
    + subst e. apply Hb1. lra.
    + apply Hb2; [ lra | exact Hin ].
Qed.

(* THE WALL THEOREM: for a taut ring, the corridor along the wall is
   skeleton-free for every sufficiently small positive offset. *)
Theorem wall_corridor_clear : forall (r : Ring) (e1 : Edge) (ylo yhi : R),
  ring_taut r ->
  In e1 (ring_edges r) ->
  ((py (fst e1) < ylo /\ yhi < py (snd e1)) \/
   (py (snd e1) < ylo /\ yhi < py (fst e1))) ->
  ylo <= yhi ->
  exists delta0, 0 < delta0 /\
    forall delta, 0 < delta < delta0 ->
      forall y, ylo <= y <= yhi ->
        ~ ring_image r (corridor e1 delta y).
Proof.
  intros r e1 ylo yhi Htaut Hin1 Hspan Hle.
  destruct (clear_fold
              (fun f delta => forall y, ylo <= y <= yhi ->
                 ~ (exists s : R, 0 <= s <= 1 /\
                      edge_x_at e1 y - delta
                        = (1 - s) * px (fst f) + s * px (snd f) /\
                      y = (1 - s) * py (fst f) + s * py (snd f)))
              (ring_edges r)) as [d0 [Hd0 Hball]].
  { intros f Hinf.
    exact (per_edge_clear r e1 f ylo yhi Htaut Hin1 Hinf Hspan Hle). }
  exists d0. split; [ exact Hd0 | ].
  intros delta Hd y Hw.
  apply (corridor_free_of_edges r e1 ylo yhi delta); [ | exact Hw ].
  intros f Hinf y' Hw'.
  exact (Hball delta Hd f Hinf y' Hw').
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions touch_clearance.
Print Assumptions per_edge_clear.
Print Assumptions wall_corridor_clear.
