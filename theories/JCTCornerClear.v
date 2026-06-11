(* ============================================================================
   NetTopologySuite.Proofs.JCTCornerClear
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5a: the CORNER-ABUTTING WALL CLEARANCE, dissolving
   the quantifier deadlock between the wall theorem and the corner drop.

   The deadlock: `wall_corridor_clear` (rung 4b-2) fixes the height window
   BEFORE delta, while the corner drop (rung 4b-3) needs eps << delta.  A
   corridor window reaching down to py v + eps therefore needs its delta0
   to be UNIFORM as eps -> 0 -- which is false in general: when the
   companion edge at the wall's bottom vertex v ascends WEST of the wall's
   carrier (a wedge seen from inside), its clearance at the bottom clip
   point vanishes linearly, and no uniform delta0 exists.  This is not a
   defect: it is exactly where walkers INSIDE the ring get stuck, as they
   must (`odd_parity_trapped`).

   The resolution is the hypothesis `corner_opens_east`: every ring edge
   incident at v whose other endpoint reaches (weakly) above v's level
   stays weakly EAST of the wall's carrier line.  Then:

     - incident edges reaching above: weakly east at both endpoints, so
       ANY positive offset clears them (`corridor_avoid_east_weak` -- the
       weak-inequality twin of rung 2's east clearance: the corridor is
       strictly west of the carrier, the obstacle weakly east);
     - incident edges descending from v: entirely at-or-below the corner
       level, cleared per-height (the window is OPEN at py v);
     - non-incident edges NEVER touch the carrier on [py v, yhi]: a touch
       at the corner level is a touch at v itself (`taut_vertex_endpoint`
       makes the toucher incident -- contradiction), a touch strictly
       above is span-interior (`taut_no_line_touch` makes the toucher
       pointwise equal to the wall, hence incident -- contradiction).  So
       their clip clearances are STRICTLY signed on the CLOSED window
       [py v, yhi], and the rung 4b-2 case tree runs with the touch
       branches replaced by contradictions, yielding eps-FREE margins.

   `wall_corridor_clear_corner` folds these into one uniform delta0 with
   the corridor free on ALL of (py v, yhi].  `corner_passage` then
   composes corridor ride + corner drop into the full descent move: from
   the corridor point at height yhi, around the corner, to an off-ring,
   ray-guarded point strictly BELOW the corner level.  Note
   `corner_opens_east` subsumes rung 4b-3's no-west-horizontal residual
   (a horizontal edge at v has its far endpoint at v's level, where the
   carrier abscissa is px v).

   What remains for the descent recursion (rung 5b): choosing the wall so
   that `corner_opens_east` holds at its bottom vertex -- the wall-switch
   argument -- and the strictly-decreasing height measure down to a
   count-free point.

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
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  The weak-east clearance and the corner-opens-east hypothesis.
   --------------------------------------------------------------------------- *)

(* Weak twin of corridor_avoid_east: an obstacle WEAKLY east of the carrier
   line at both endpoints is missed by every strictly positive offset. *)
Lemma corridor_avoid_east_weak : forall (e f : Edge) (delta : R) (y : R),
  py (fst e) <> py (snd e) ->
  0 < delta ->
  edge_x_at e (py (fst f)) <= px (fst f) ->
  edge_x_at e (py (snd f)) <= px (snd f) ->
  ~ (exists s : R, 0 <= s <= 1 /\
       edge_x_at e y - delta = (1 - s) * px (fst f) + s * px (snd f) /\
       y = (1 - s) * py (fst f) + s * py (snd f)).
Proof.
  intros e f delta y Hnh Hd Hea Heb [s [Hs [Hx Hy]]].
  destruct e as [a b]; cbn [fst snd] in *.
  unfold edge_x_at in *.
  set (al := (px b - px a) / (py b - py a)) in *.
  assert (Hlin : forall z : R,
            px a + (px b - px a) * (z - py a) / (py b - py a)
              = al * z + (px a - al * py a))
    by (intro z; unfold al; field; lra).
  rewrite Hlin in Hx, Hea, Heb.
  rewrite Hy in Hx.
  assert (H1 : (1 - s) * (al * py (fst f) + (px a - al * py a))
                 <= (1 - s) * px (fst f)) by nra.
  assert (H2 : s * (al * py (snd f) + (px a - al * py a))
                 <= s * px (snd f)) by nra.
  nra.
Qed.

(* The corner-opens-east condition at the wall's bottom vertex v: every
   edge incident at v keeps any endpoint reaching (weakly) above v's level
   weakly east of the wall's carrier line. *)
Definition corner_opens_east (r : Ring) (e1 : Edge) (v : Point) : Prop :=
  forall g, In g (ring_edges r) ->
    fst g = v \/ snd g = v ->
    (py v <= py (fst g) -> edge_x_at e1 (py (fst g)) <= px (fst g)) /\
    (py v <= py (snd g) -> edge_x_at e1 (py (snd g)) <= px (snd g)).

(* The wall's carrier passes through its own bottom vertex. *)
Lemma carrier_at_corner : forall (e1 : Edge) (v w : Point),
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  edge_x_at e1 (py v) = px v.
Proof.
  intros e1 v w Hor Hvw.
  destruct Hor as [He | He]; subst e1.
  - apply (edge_x_at_endpoint_a (v, w)); cbn; lra.
  - apply (edge_x_at_endpoint_b (w, v)); cbn; lra.
Qed.

(* ---------------------------------------------------------------------------
   §2  The per-edge clearance on the corner-abutting window.
   --------------------------------------------------------------------------- *)

Lemma per_edge_clear_corner : forall (r : Ring) (e1 g : Edge)
                                     (v w : Point) (yhi : R),
  ring_taut r ->
  In e1 (ring_edges r) -> In g (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  py v <= yhi ->
  yhi < py w ->
  corner_opens_east r e1 v ->
  exists df, 0 < df /\
    forall delta, 0 < delta < df ->
      forall y, py v < y <= yhi ->
        ~ (exists s : R, 0 <= s <= 1 /\
             edge_x_at e1 y - delta = (1 - s) * px (fst g) + s * px (snd g) /\
             y = (1 - s) * py (fst g) + s * py (snd g)).
Proof.
  intros r e1 g v w yhi Htaut Hin1 Hing Hor Hvw Hle Hhi Hopen.
  assert (Hnh : py (fst e1) <> py (snd e1))
    by (destruct Hor; subst e1; cbn; lra).
  assert (He1v : edge_x_at e1 (py v) = px v)
    by (exact (carrier_at_corner e1 v w Hor Hvw)).
  (* INCIDENT edges: weak-east when reaching above, below-window otherwise *)
  destruct (coord_point_dec (fst g) v) as [Hfv | Hfv].
  { destruct (Rle_or_lt (py v) (py (snd g))) as [Hup | Hdown].
    - destruct (Hopen g Hing (or_introl Hfv)) as [_ HoB].
      exists 1. split; [ lra | ]. intros delta Hd y Hy.
      apply (corridor_avoid_east_weak e1 g delta y Hnh ltac:(lra));
        [ rewrite Hfv; lra | exact (HoB Hup) ].
    - exists 1. split; [ lra | ]. intros delta Hd y Hy.
      apply (corridor_avoid_below e1 g delta y y y ltac:(lra));
        [ rewrite Hfv; lra | lra ]. }
  destruct (coord_point_dec (snd g) v) as [Hsv | Hsv].
  { destruct (Rle_or_lt (py v) (py (fst g))) as [Hup | Hdown].
    - destruct (Hopen g Hing (or_intror Hsv)) as [HoA _].
      exists 1. split; [ lra | ]. intros delta Hd y Hy.
      apply (corridor_avoid_east_weak e1 g delta y Hnh ltac:(lra));
        [ exact (HoA Hup) | rewrite Hsv; lra ].
    - exists 1. split; [ lra | ]. intros delta Hd y Hy.
      apply (corridor_avoid_below e1 g delta y y y ltac:(lra));
        [ lra | rewrite Hsv; lra ]. }
  (* NON-INCIDENT edges never touch the carrier on [py v, yhi]. *)
  assert (Hnotouch : ~ (exists s y0 : R, 0 <= s <= 1 /\
            py v <= y0 <= yhi /\
            y0 = (1 - s) * py (fst g) + s * py (snd g) /\
            edge_x_at e1 y0 = (1 - s) * px (fst g) + s * px (snd g))).
  { intros [s [y0 [Hs [Hw0 [Hy0 Hx0]]]]].
    destruct (Req_EM_T y0 (py v)) as [Hy0v | Hy0v].
    - (* touch at the corner level IS a touch at v *)
      rewrite Hy0v in Hx0, Hy0.
      rewrite He1v in Hx0.
      destruct (taut_vertex_endpoint r e1 g v w Htaut Hin1 Hing Hor s Hs
                  (eq_sym Hx0) (eq_sym Hy0)) as [H | H];
        [ exact (Hfv H) | exact (Hsv H) ].
    - (* touch strictly above the corner: span-interior, hence pointwise
         the wall itself, hence incident -- contradiction *)
      assert (Hy0gt : py v < y0) by lra.
      assert (Hspan : (py (fst e1) < y0 /\ y0 < py (snd e1)) \/
                      (py (snd e1) < y0 /\ y0 < py (fst e1)))
        by (destruct Hor; subst e1; cbn; [ left | right ]; split; lra).
      destruct (taut_no_line_touch r e1 g y0 y0 Htaut Hin1 Hing Hnh
                  ltac:(destruct Hspan as [[A B] | [A B]]; [ left | right ];
                        split; lra)
                  s y0 Hs ltac:(lra) Hy0 Hx0) as [Hf1 Hf2].
      destruct Hor; subst e1; cbn in Hf1, Hf2.
      + exact (Hfv (eq_sym Hf1)).
      + exact (Hsv (eq_sym Hf2)). }
  (* the clip tree on the CLOSED window [py v, yhi]; touch -> contradiction *)
  destruct (Rtotal_order (py (fst g)) (py (snd g))) as [Hasc | [Hflat | Hdesc]].
  - (* ascending g *)
    destruct (Rle_or_lt (py v) (py (snd g))) as [Hov1 | Hbelow];
      [ | exists 1; split; [ lra | ];
          intros delta Hd y Hy;
          apply (corridor_avoid_below e1 g delta y y y ltac:(lra)); lra ].
    destruct (Rle_or_lt (py (fst g)) yhi) as [Hov2 | Habove];
      [ | exists 1; split; [ lra | ];
          intros delta Hd y Hy;
          apply (corridor_avoid_above e1 g delta y y y ltac:(lra)); lra ].
    pose proof (clip_ordered_asc g (py v) yhi Hasc Hle Hov2 Hov1) as CL.
    cbv zeta in CL.
    set (s0 := Rmax 0 ((py v - py (fst g)) / (py (snd g) - py (fst g)))) in *.
    set (s1 := Rmin 1 ((yhi - py (fst g)) / (py (snd g) - py (fst g)))) in *.
    destruct CL as [Hs00 [Hs01 [Hs11 [Hc0lo [Hc0hi [Hc1lo Hc1hi]]]]]].
    set (G0 := edge_x_at e1 ((1 - s0) * py (fst g) + s0 * py (snd g))
                 - ((1 - s0) * px (fst g) + s0 * px (snd g))).
    set (G1 := edge_x_at e1 ((1 - s1) * py (fst g) + s1 * py (snd g))
                 - ((1 - s1) * px (fst g) + s1 * px (snd g))).
    assert (Hclip : forall s, 0 <= s <= 1 ->
              py v <= (1 - s) * py (fst g) + s * py (snd g) <= yhi ->
              s0 <= s <= s1)
      by (intros s Hs Hw; exact (clip_params_asc g (py v) yhi s Hasc Hs Hw)).
    destruct (Rtotal_order 0 G0) as [HG0p | [HG0z | HG0n]].
    + destruct (Rtotal_order 0 G1) as [HG1p | [HG1z | HG1n]].
      * (* both west: clipped-west margin *)
        exists (Rmin G0 G1). split; [ apply Rmin_glb_lt; lra | ].
        intros delta Hd y Hy.
        pose proof (Rmin_l G0 G1). pose proof (Rmin_r G0 G1).
        apply (corridor_avoid_clipped_west e1 g delta (py v) yhi s0 s1
                 Hnh Hclip); try (unfold G0, G1 in *; lra).
      * (* zero at the clip: a touch -- impossible here *)
        exfalso. apply Hnotouch.
        exists s1, ((1 - s1) * py (fst g) + s1 * py (snd g)).
        repeat split; try lra. unfold G1 in HG1z. lra.
      * (* sign change: an affine root inside the clip range -- a touch *)
        exfalso.
        destruct e1 as [a1 b1]; cbn [fst snd] in *.
        set (al := (px b1 - px a1) / (py b1 - py a1)).
        assert (Hlin : forall z : R,
                  edge_x_at (a1, b1) z = al * z + (px a1 - al * py a1)).
        { intro z. unfold edge_x_at, al. cbn [fst snd]. field. lra. }
        set (A := al * (py (snd g) - py (fst g))
                    - (px (snd g) - px (fst g))).
        set (B := al * py (fst g) + (px a1 - al * py a1) - px (fst g)).
        assert (HGA : forall s : R,
                  edge_x_at (a1, b1) ((1 - s) * py (fst g) + s * py (snd g))
                    - ((1 - s) * px (fst g) + s * px (snd g))
                  = A * s + B)
          by (intro s; rewrite Hlin; unfold A, B; ring).
        assert (Hprod : (A * s0 + B) * (A * s1 + B) <= 0).
        { rewrite <- (HGA s0), <- (HGA s1). unfold G0, G1 in *. nra. }
        destruct (affine_root A B s0 s1 Hs01 Hprod) as [sr [Hsr Hzero]].
        apply Hnotouch.
        exists sr, ((1 - sr) * py (fst g) + sr * py (snd g)).
        assert (Hmono : forall u v' : R, u <= v' ->
                  (1 - u) * py (fst g) + u * py (snd g)
                    <= (1 - v') * py (fst g) + v' * py (snd g))
          by (intros u v' Huv; nra).
        pose proof (Hmono s0 sr ltac:(lra)).
        pose proof (Hmono sr s1 ltac:(lra)).
        repeat split; try lra.
        rewrite <- (HGA sr) in Hzero. lra.
    + (* zero at the lower clip: a touch -- impossible *)
      exfalso. apply Hnotouch.
      exists s0, ((1 - s0) * py (fst g) + s0 * py (snd g)).
      repeat split; try lra. unfold G0 in HG0z. lra.
    + destruct (Rtotal_order 0 G1) as [HG1p | [HG1z | HG1n]].
      * (* sign change, mirrored: a touch -- impossible *)
        exfalso.
        destruct e1 as [a1 b1]; cbn [fst snd] in *.
        set (al := (px b1 - px a1) / (py b1 - py a1)).
        assert (Hlin : forall z : R,
                  edge_x_at (a1, b1) z = al * z + (px a1 - al * py a1)).
        { intro z. unfold edge_x_at, al. cbn [fst snd]. field. lra. }
        set (A := al * (py (snd g) - py (fst g))
                    - (px (snd g) - px (fst g))).
        set (B := al * py (fst g) + (px a1 - al * py a1) - px (fst g)).
        assert (HGA : forall s : R,
                  edge_x_at (a1, b1) ((1 - s) * py (fst g) + s * py (snd g))
                    - ((1 - s) * px (fst g) + s * px (snd g))
                  = A * s + B)
          by (intro s; rewrite Hlin; unfold A, B; ring).
        assert (Hprod : (A * s0 + B) * (A * s1 + B) <= 0).
        { rewrite <- (HGA s0), <- (HGA s1). unfold G0, G1 in *. nra. }
        destruct (affine_root A B s0 s1 Hs01 Hprod) as [sr [Hsr Hzero]].
        apply Hnotouch.
        exists sr, ((1 - sr) * py (fst g) + sr * py (snd g)).
        assert (Hmono : forall u v' : R, u <= v' ->
                  (1 - u) * py (fst g) + u * py (snd g)
                    <= (1 - v') * py (fst g) + v' * py (snd g))
          by (intros u v' Huv; nra).
        pose proof (Hmono s0 sr ltac:(lra)).
        pose proof (Hmono sr s1 ltac:(lra)).
        repeat split; try lra.
        rewrite <- (HGA sr) in Hzero. lra.
      * exfalso. apply Hnotouch.
        exists s1, ((1 - s1) * py (fst g) + s1 * py (snd g)).
        repeat split; try lra. unfold G1 in HG1z. lra.
      * (* both east *)
        exists 1. split; [ lra | ].
        intros delta Hd y Hy.
        apply (corridor_avoid_clipped_east e1 g delta (py v) yhi s0 s1 Hnh
                 ltac:(lra) Hclip); try (unfold G0, G1 in *; lra).
  - (* horizontal g *)
    destruct (Rle_or_lt (py (fst g)) (py v)) as [HLlo | HLhi];
      [ exists 1; split; [ lra | ];
        intros delta Hd y Hy;
        apply (corridor_avoid_below e1 g delta y y y ltac:(lra)); lra | ].
    destruct (Rle_or_lt (py (fst g)) yhi) as [HLin | HLout];
      [ | exists 1; split; [ lra | ];
          intros delta Hd y Hy;
          apply (corridor_avoid_above e1 g delta y y y ltac:(lra)); lra ].
    (* horizontal at a window level strictly above the corner *)
    set (cs := edge_x_at e1 (py (fst g))).
    assert (Hcs2 : edge_x_at e1 (py (snd g)) = cs)
      by (unfold cs; rewrite Hflat; reflexivity).
    (* a touch witness at this level is impossible *)
    assert (Hnt : forall s, 0 <= s <= 1 ->
              cs <> (1 - s) * px (fst g) + s * px (snd g)).
    { intros s Hs Heq. apply Hnotouch.
      exists s, (py (fst g)).
      repeat split; try lra.
      - rewrite <- Hflat. ring.
      - unfold cs in Heq. lra. }
    destruct (Rtotal_order (px (fst g)) cs) as [Hp1 | [Hp1 | Hp1]];
    destruct (Rtotal_order (px (snd g)) cs) as [Hp2 | [Hp2 | Hp2]].
    + (* both west *)
      exists (Rmin (cs - px (fst g)) (cs - px (snd g))).
      split; [ apply Rmin_glb_lt; lra | ].
      intros delta Hd y Hy.
      pose proof (Rmin_l (cs - px (fst g)) (cs - px (snd g))).
      pose proof (Rmin_r (cs - px (fst g)) (cs - px (snd g))).
      apply (corridor_avoid_west e1 g delta y Hnh); unfold cs in *; lra.
    + (* snd at the carrier: a touch at s = 1 -- impossible *)
      exfalso. apply (Hnt 1 ltac:(lra)). ring_simplify. lra.
    + (* straddles the carrier: an interior touch -- impossible *)
      exfalso.
      assert (Hne : px (snd g) - px (fst g) <> 0) by lra.
      set (sr := (cs - px (fst g)) / (px (snd g) - px (fst g))).
      assert (Hu1 : sr * (px (snd g) - px (fst g)) = cs - px (fst g))
        by (unfold sr; field; lra).
      assert (Hsr : 0 <= sr <= 1) by nra.
      apply (Hnt sr Hsr). nra.
    + (* fst at the carrier: a touch at s = 0 -- impossible *)
      exfalso. apply (Hnt 0 ltac:(lra)). ring_simplify. lra.
    + exfalso. apply (Hnt 0 ltac:(lra)). ring_simplify. lra.
    + exfalso. apply (Hnt 0 ltac:(lra)). ring_simplify. lra.
    + (* straddles, mirrored -- impossible *)
      exfalso.
      assert (Hne : px (snd g) - px (fst g) <> 0) by lra.
      set (sr := (cs - px (fst g)) / (px (snd g) - px (fst g))).
      assert (Hu1 : sr * (px (snd g) - px (fst g)) = cs - px (fst g))
        by (unfold sr; field; lra).
      assert (Hsr : 0 <= sr <= 1) by nra.
      apply (Hnt sr Hsr). nra.
    + (* snd at the carrier -- impossible *)
      exfalso. apply (Hnt 1 ltac:(lra)). ring_simplify. lra.
    + (* both east *)
      exists 1. split; [ lra | ].
      intros delta Hd y Hy.
      apply (corridor_avoid_east e1 g delta y Hnh ltac:(lra));
        unfold cs in *; lra.
  - (* descending g: mirror of the ascending case *)
    destruct (Rle_or_lt (py v) (py (fst g))) as [Hov1 | Hbelow];
      [ | exists 1; split; [ lra | ];
          intros delta Hd y Hy;
          apply (corridor_avoid_below e1 g delta y y y ltac:(lra)); lra ].
    destruct (Rle_or_lt (py (snd g)) yhi) as [Hov2 | Habove];
      [ | exists 1; split; [ lra | ];
          intros delta Hd y Hy;
          apply (corridor_avoid_above e1 g delta y y y ltac:(lra)); lra ].
    pose proof (clip_ordered_desc g (py v) yhi Hdesc Hle Hov2 Hov1) as CL.
    cbv zeta in CL.
    set (s0 := Rmax 0 ((py (fst g) - yhi) / (py (fst g) - py (snd g)))) in *.
    set (s1 := Rmin 1 ((py (fst g) - py v) / (py (fst g) - py (snd g)))) in *.
    destruct CL as [Hs00 [Hs01 [Hs11 [Hc0lo [Hc0hi [Hc1lo Hc1hi]]]]]].
    set (G0 := edge_x_at e1 ((1 - s0) * py (fst g) + s0 * py (snd g))
                 - ((1 - s0) * px (fst g) + s0 * px (snd g))).
    set (G1 := edge_x_at e1 ((1 - s1) * py (fst g) + s1 * py (snd g))
                 - ((1 - s1) * px (fst g) + s1 * px (snd g))).
    assert (Hclip : forall s, 0 <= s <= 1 ->
              py v <= (1 - s) * py (fst g) + s * py (snd g) <= yhi ->
              s0 <= s <= s1)
      by (intros s Hs Hw; exact (clip_params_desc g (py v) yhi s Hdesc Hs Hw)).
    destruct (Rtotal_order 0 G0) as [HG0p | [HG0z | HG0n]].
    + destruct (Rtotal_order 0 G1) as [HG1p | [HG1z | HG1n]].
      * exists (Rmin G0 G1). split; [ apply Rmin_glb_lt; lra | ].
        intros delta Hd y Hy.
        pose proof (Rmin_l G0 G1). pose proof (Rmin_r G0 G1).
        apply (corridor_avoid_clipped_west e1 g delta (py v) yhi s0 s1
                 Hnh Hclip); try (unfold G0, G1 in *; lra).
      * exfalso. apply Hnotouch.
        exists s1, ((1 - s1) * py (fst g) + s1 * py (snd g)).
        repeat split; try lra. unfold G1 in HG1z. lra.
      * exfalso.
        destruct e1 as [a1 b1]; cbn [fst snd] in *.
        set (al := (px b1 - px a1) / (py b1 - py a1)).
        assert (Hlin : forall z : R,
                  edge_x_at (a1, b1) z = al * z + (px a1 - al * py a1)).
        { intro z. unfold edge_x_at, al. cbn [fst snd]. field. lra. }
        set (A := al * (py (snd g) - py (fst g))
                    - (px (snd g) - px (fst g))).
        set (B := al * py (fst g) + (px a1 - al * py a1) - px (fst g)).
        assert (HGA : forall s : R,
                  edge_x_at (a1, b1) ((1 - s) * py (fst g) + s * py (snd g))
                    - ((1 - s) * px (fst g) + s * px (snd g))
                  = A * s + B)
          by (intro s; rewrite Hlin; unfold A, B; ring).
        assert (Hprod : (A * s0 + B) * (A * s1 + B) <= 0).
        { rewrite <- (HGA s0), <- (HGA s1). unfold G0, G1 in *. nra. }
        destruct (affine_root A B s0 s1 Hs01 Hprod) as [sr [Hsr Hzero]].
        apply Hnotouch.
        exists sr, ((1 - sr) * py (fst g) + sr * py (snd g)).
        assert (Hmono : forall u v' : R, u <= v' ->
                  (1 - v') * py (fst g) + v' * py (snd g)
                    <= (1 - u) * py (fst g) + u * py (snd g))
          by (intros u v' Huv; nra).
        pose proof (Hmono s0 sr ltac:(lra)).
        pose proof (Hmono sr s1 ltac:(lra)).
        repeat split; try lra.
        rewrite <- (HGA sr) in Hzero. lra.
    + exfalso. apply Hnotouch.
      exists s0, ((1 - s0) * py (fst g) + s0 * py (snd g)).
      repeat split; try lra. unfold G0 in HG0z. lra.
    + destruct (Rtotal_order 0 G1) as [HG1p | [HG1z | HG1n]].
      * exfalso.
        destruct e1 as [a1 b1]; cbn [fst snd] in *.
        set (al := (px b1 - px a1) / (py b1 - py a1)).
        assert (Hlin : forall z : R,
                  edge_x_at (a1, b1) z = al * z + (px a1 - al * py a1)).
        { intro z. unfold edge_x_at, al. cbn [fst snd]. field. lra. }
        set (A := al * (py (snd g) - py (fst g))
                    - (px (snd g) - px (fst g))).
        set (B := al * py (fst g) + (px a1 - al * py a1) - px (fst g)).
        assert (HGA : forall s : R,
                  edge_x_at (a1, b1) ((1 - s) * py (fst g) + s * py (snd g))
                    - ((1 - s) * px (fst g) + s * px (snd g))
                  = A * s + B)
          by (intro s; rewrite Hlin; unfold A, B; ring).
        assert (Hprod : (A * s0 + B) * (A * s1 + B) <= 0).
        { rewrite <- (HGA s0), <- (HGA s1). unfold G0, G1 in *. nra. }
        destruct (affine_root A B s0 s1 Hs01 Hprod) as [sr [Hsr Hzero]].
        apply Hnotouch.
        exists sr, ((1 - sr) * py (fst g) + sr * py (snd g)).
        assert (Hmono : forall u v' : R, u <= v' ->
                  (1 - v') * py (fst g) + v' * py (snd g)
                    <= (1 - u) * py (fst g) + u * py (snd g))
          by (intros u v' Huv; nra).
        pose proof (Hmono s0 sr ltac:(lra)).
        pose proof (Hmono sr s1 ltac:(lra)).
        repeat split; try lra.
        rewrite <- (HGA sr) in Hzero. lra.
      * exfalso. apply Hnotouch.
        exists s1, ((1 - s1) * py (fst g) + s1 * py (snd g)).
        repeat split; try lra. unfold G1 in HG1z. lra.
      * exists 1. split; [ lra | ].
        intros delta Hd y Hy.
        apply (corridor_avoid_clipped_east e1 g delta (py v) yhi s0 s1 Hnh
                 ltac:(lra) Hclip); try (unfold G0, G1 in *; lra).
Qed.

(* ---------------------------------------------------------------------------
   §3  The corner-abutting wall theorem: ONE uniform delta0, the corridor
       free on the whole half-open window down to the corner level.
   --------------------------------------------------------------------------- *)

Theorem wall_corridor_clear_corner : forall (r : Ring) (e1 : Edge)
                                            (v w : Point) (yhi : R),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  py v <= yhi ->
  yhi < py w ->
  corner_opens_east r e1 v ->
  exists delta0, 0 < delta0 /\
    forall delta, 0 < delta < delta0 ->
      forall y, py v < y <= yhi ->
        ~ ring_image r (corridor e1 delta y).
Proof.
  intros r e1 v w yhi Htaut Hin1 Hor Hvw Hle Hhi Hopen.
  destruct (clear_fold
              (fun g delta => forall y, py v < y <= yhi ->
                 ~ (exists s : R, 0 <= s <= 1 /\
                      edge_x_at e1 y - delta
                        = (1 - s) * px (fst g) + s * px (snd g) /\
                      y = (1 - s) * py (fst g) + s * py (snd g)))
              (ring_edges r)) as [d0 [Hd0 Hball]].
  { intros g Hing.
    exact (per_edge_clear_corner r e1 g v w yhi Htaut Hin1 Hing Hor Hvw
             Hle Hhi Hopen). }
  exists d0. split; [ exact Hd0 | ].
  intros delta Hd y Hy.
  apply (corridor_free_of_edges r e1 y y delta); [ | lra ].
  intros g Hing y' Hy'.
  apply (Hball delta Hd g Hing y'). lra.
Qed.

(* ---------------------------------------------------------------------------
   §4  The full corner passage: corridor ride + corner drop, composed.
   --------------------------------------------------------------------------- *)

(* corner_opens_east subsumes rung 4b-3's horizontal-east residual. *)
Lemma opens_east_horizontal : forall (r : Ring) (e1 : Edge) (v w : Point),
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  corner_opens_east r e1 v ->
  forall g, In g (ring_edges r) ->
    py (fst g) = py (snd g) -> fst g = v \/ snd g = v ->
    px v <= px (fst g) /\ px v <= px (snd g).
Proof.
  intros r e1 v w Hor Hvw Hopen g Hing Hflat Hinc.
  assert (He1v : edge_x_at e1 (py v) = px v)
    by (exact (carrier_at_corner e1 v w Hor Hvw)).
  destruct (Hopen g Hing Hinc) as [HoA HoB].
  assert (Hlv : py (fst g) = py v /\ py (snd g) = py v).
  { destruct Hinc as [H | H]; rewrite H in Hflat; split; congruence. }
  destruct Hlv as [HA HB].
  split.
  - specialize (HoA ltac:(lra)). rewrite HA, He1v in HoA. exact HoA.
  - specialize (HoB ltac:(lra)). rewrite HB, He1v in HoB. exact HoB.
Qed.

(* THE RUNG THEOREM: from the wall's corridor at any height in the window,
   ride down to the corner band and drop past the bottom vertex -- one
   complement path to an off-ring, ray-guarded point strictly below the
   corner level.  delta0 uniform; eps chosen after delta. *)
Theorem corner_passage : forall (r : Ring) (e1 : Edge) (v w : Point)
                                (yhi : R),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  py v < yhi ->
  yhi < py w ->
  corner_opens_east r e1 v ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    connected_in_complement_cont r
      (corridor e1 delta yhi)
      (mkPoint (edge_x_at e1 (py v + eps) - delta) (py v - eps)) /\
    ring_complement r (corridor e1 delta yhi) /\
    ring_complement r
      (mkPoint (edge_x_at e1 (py v + eps) - delta) (py v - eps)) /\
    ray_avoids_vertices
      (mkPoint (edge_x_at e1 (py v + eps) - delta) (py v - eps)) r.
Proof.
  intros r e1 v w yhi Htaut Hin1 Hor Hvw Hlo Hhi Hopen.
  assert (Hnh : py (fst e1) <> py (snd e1))
    by (destruct Hor; subst e1; cbn; lra).
  destruct (wall_corridor_clear_corner r e1 v w yhi Htaut Hin1 Hor Hvw
              ltac:(lra) Hhi Hopen) as [dA [HdA HfreeA]].
  destruct (corner_sector_guarded r e1 v w Htaut Hin1 Hor Hvw
              (opens_east_horizontal r e1 v w Hor Hvw Hopen))
    as [dB [HdB HstageB]].
  exists (Rmin dA dB). split; [ apply Rmin_glb_lt; lra | ].
  intros delta Hd.
  pose proof (Rmin_l dA dB). pose proof (Rmin_r dA dB).
  destruct (HstageB delta ltac:(lra)) as [eB [HeB HsectB]].
  exists (Rmin eB (yhi - py v)). split; [ apply Rmin_glb_lt; lra | ].
  intros eps He.
  pose proof (Rmin_l eB (yhi - py v)). pose proof (Rmin_r eB (yhi - py v)).
  destruct (HsectB eps ltac:(lra)) as [Hsect [Hcompl Hguard]].
  assert (Hride : connected_in_complement_cont r
            (corridor e1 delta yhi) (corridor e1 delta (py v + eps))).
  { apply (corridor_connected r e1 (py v + eps) yhi delta Hnh ltac:(lra)).
    intros y Hy. apply (HfreeA delta ltac:(lra)). lra. }
  split; [ | split; [ | split ] ].
  - exact (connected_in_complement_cont_trans r
             (corridor e1 delta yhi)
             (corridor e1 delta (py v + eps))
             (mkPoint (edge_x_at e1 (py v + eps) - delta) (py v - eps))
             Hride Hsect).
  - intro Himg. exact (HfreeA delta ltac:(lra) yhi ltac:(lra) Himg).
  - exact Hcompl.
  - exact Hguard.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions corridor_avoid_east_weak.
Print Assumptions per_edge_clear_corner.
Print Assumptions wall_corridor_clear_corner.
Print Assumptions corner_passage.
