(* ============================================================================
   NetTopologySuite.Proofs.HotPixelConvexRing
   ----------------------------------------------------------------------------
   The hot pixel as a convex ring: bridging Phase-2 snap-rounding to the
   JCT / convex-chain crossing-number campaign.

   A "hot pixel" (Phase 2, `theories/HotPixel.v`) is the half-open axis-aligned
   square  [cx - r, cx + r) x [cy - r, cy + r)  with r = hot_pixel_radius scale
   = / (2 * scale).  A hot pixel is therefore a convex 4-gon, and this file
   presents it as a `Ring` and connects the half-open membership predicate
   `in_hot_pixel` to the crossing-number predicate `point_in_ring` (the
   rightward-ray parity test).

   The axis-aligned square has HORIZONTAL top/bottom edges, so it is NOT a
   strict `bimonotone_split` (the chain predicates `edge_up`/`edge_dn` are
   strict).  But a horizontal edge never crosses a rightward ray (the crossing
   predicate demands a strict y-straddle), so only the two VERTICAL edges can
   cross.  This gives, by the same count argument as the convex campaign's
   `convex_ray_crosses_le_two` / `convex_in_ring_iff_one_crossing` (reproved
   here directly against the flat-edged square):

     §1  `pixel_ring`            — the CCW square ring (BL, BR, TR, TL).
     §2  per-edge crossing facts — horizontals never cross; each vertical
         crosses iff the ray height straddles the pixel and the ray origin is
         left of that edge's x.
     §3  `pixel_ray_crosses_le_two` — the ring is crossed at most twice.
     §4  `pixel_in_ring_iff_one_crossing` / `pixel_point_in_ring_iff_box` —
         inside iff crossed exactly once iff a HALF-OPEN-x / OPEN-y box.
     §5  the bridge to `in_hot_pixel`: `point_in_ring` is a subset of the
         half-open pixel (total), the converse holds OFF the bottom edge, and
         a concrete grazing witness on the included bottom edge is `in_hot_pixel`
         yet not `point_in_ring` — the hot-pixel incarnation of the corpus's
         vertex-grazing caveat (`JCT_VertexGrazingCounterexample`).
     §6  validation on the unit pixel (scale = 1, centre at the origin).

   Pure-R + three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia.
From NTS.Proofs Require Import Distance Overlay MonotoneChainParity HotPixel.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The hot pixel as a CCW square ring.                                     *)
(* -------------------------------------------------------------------------- *)

(* CCW square: BL (cx-r, cy-r) -> BR (cx+r, cy-r) -> TR (cx+r, cy+r)
   -> TL (cx-r, cy+r) -> BL.  Same closed-ring convention as `diamond_ring`. *)
Definition pixel_ring (C : Point) (scale : R) : Ring :=
  [ mkPoint (px C - hot_pixel_radius scale) (py C - hot_pixel_radius scale) ;
    mkPoint (px C + hot_pixel_radius scale) (py C - hot_pixel_radius scale) ;
    mkPoint (px C + hot_pixel_radius scale) (py C + hot_pixel_radius scale) ;
    mkPoint (px C - hot_pixel_radius scale) (py C + hot_pixel_radius scale) ;
    mkPoint (px C - hot_pixel_radius scale) (py C - hot_pixel_radius scale) ].

(* The four edges, in CCW order: bottom, right, top, left. *)
Lemma pixel_ring_edges : forall C scale,
  ring_edges (pixel_ring C scale) =
    [ (mkPoint (px C - hot_pixel_radius scale) (py C - hot_pixel_radius scale),
       mkPoint (px C + hot_pixel_radius scale) (py C - hot_pixel_radius scale)) ;
      (mkPoint (px C + hot_pixel_radius scale) (py C - hot_pixel_radius scale),
       mkPoint (px C + hot_pixel_radius scale) (py C + hot_pixel_radius scale)) ;
      (mkPoint (px C + hot_pixel_radius scale) (py C + hot_pixel_radius scale),
       mkPoint (px C - hot_pixel_radius scale) (py C + hot_pixel_radius scale)) ;
      (mkPoint (px C - hot_pixel_radius scale) (py C + hot_pixel_radius scale),
       mkPoint (px C - hot_pixel_radius scale) (py C - hot_pixel_radius scale)) ].
Proof. intros C scale. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Per-edge crossing facts.                                                *)
(* -------------------------------------------------------------------------- *)

(* `0 / x = 0` -- isolates the vertical-edge x-intercept simplification so we
   do not depend on the exact stdlib lemma name. *)
Lemma Rdiv_zero_num : forall x : R, 0 / x = 0.
Proof. intro x. unfold Rdiv. apply Rmult_0_l. Qed.

(* The bottom edge is horizontal, so the ray never crosses it: no strict
   y-straddle is possible.  No positivity of `scale` needed. *)
Lemma pixel_bottom_no_cross : forall C scale P,
  ~ edge_crosses_ray P
      (mkPoint (px C - hot_pixel_radius scale) (py C - hot_pixel_radius scale),
       mkPoint (px C + hot_pixel_radius scale) (py C - hot_pixel_radius scale)).
Proof.
  intros C scale P. unfold edge_crosses_ray. cbn [fst snd px py].
  intros [[H _] | [H _]]; lra.
Qed.

(* The top edge is horizontal: same argument. *)
Lemma pixel_top_no_cross : forall C scale P,
  ~ edge_crosses_ray P
      (mkPoint (px C + hot_pixel_radius scale) (py C + hot_pixel_radius scale),
       mkPoint (px C - hot_pixel_radius scale) (py C + hot_pixel_radius scale)).
Proof.
  intros C scale P. unfold edge_crosses_ray. cbn [fst snd px py].
  intros [[H _] | [H _]]; lra.
Qed.

(* The right edge (a vertical up-edge at x = cx + r) crosses iff the ray height
   strictly straddles the pixel and the ray origin is left of cx + r. *)
Lemma pixel_right_crosses_iff : forall C scale P, 0 < scale ->
  (edge_crosses_ray P
     (mkPoint (px C + hot_pixel_radius scale) (py C - hot_pixel_radius scale),
      mkPoint (px C + hot_pixel_radius scale) (py C + hot_pixel_radius scale))
   <-> (py C - hot_pixel_radius scale < py P < py C + hot_pixel_radius scale
        /\ px P < px C + hot_pixel_radius scale)).
Proof.
  intros C scale P Hs.
  pose proof (hot_pixel_radius_pos scale Hs) as Hr.
  set (r := hot_pixel_radius scale) in *.
  unfold edge_crosses_ray. cbn [fst snd px py]. split.
  - intros [[Hy Hx] | [Hy _]].
    + split; [ exact Hy | ].
      replace (px C + r - (px C + r)) with 0 in Hx by lra.
      rewrite Rmult_0_l, Rdiv_zero_num, Rplus_0_r in Hx. exact Hx.
    + lra.
  - intros [Hy Hx]. left. split; [ exact Hy | ].
    replace (px C + r - (px C + r)) with 0 by lra.
    rewrite Rmult_0_l, Rdiv_zero_num, Rplus_0_r. exact Hx.
Qed.

(* The left edge (a vertical down-edge at x = cx - r) crosses iff the ray height
   strictly straddles the pixel and the ray origin is left of cx - r. *)
Lemma pixel_left_crosses_iff : forall C scale P, 0 < scale ->
  (edge_crosses_ray P
     (mkPoint (px C - hot_pixel_radius scale) (py C + hot_pixel_radius scale),
      mkPoint (px C - hot_pixel_radius scale) (py C - hot_pixel_radius scale))
   <-> (py C - hot_pixel_radius scale < py P < py C + hot_pixel_radius scale
        /\ px P < px C - hot_pixel_radius scale)).
Proof.
  intros C scale P Hs.
  pose proof (hot_pixel_radius_pos scale Hs) as Hr.
  set (r := hot_pixel_radius scale) in *.
  unfold edge_crosses_ray. cbn [fst snd px py]. split.
  - intros [[Hy _] | [Hy Hx]].
    + lra.
    + split; [ lra | ].
      replace (px C - r - (px C - r)) with 0 in Hx by lra.
      rewrite Rmult_0_l, Rdiv_zero_num, Rplus_0_r in Hx. exact Hx.
  - intros [Hy Hx]. right. split; [ lra | ].
    replace (px C - r - (px C - r)) with 0 by lra.
    rewrite Rmult_0_l, Rdiv_zero_num, Rplus_0_r. exact Hx.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The crossing bound: a hot pixel is crossed at most twice.               *)
(* -------------------------------------------------------------------------- *)

Lemma cross_count_nil : forall P, cross_count P [] = 0%nat.
Proof. intro P. reflexivity. Qed.

Lemma cross_count_single : forall P e, (cross_count P [e] <= 1)%nat.
Proof.
  intros P e. unfold cross_count. cbn [filter].
  destruct (crosses_b P e); cbn [length]; lia.
Qed.

Theorem pixel_ray_crosses_le_two : forall C scale P,
  (cross_count P (ring_edges (pixel_ring C scale)) <= 2)%nat.
Proof.
  intros C scale P. rewrite pixel_ring_edges.
  rewrite (cross_count_cons_nocross P _ _ (pixel_bottom_no_cross C scale P)).
  set (eR := (mkPoint (px C + hot_pixel_radius scale) (py C - hot_pixel_radius scale),
              mkPoint (px C + hot_pixel_radius scale) (py C + hot_pixel_radius scale))).
  set (eL := (mkPoint (px C - hot_pixel_radius scale) (py C + hot_pixel_radius scale),
              mkPoint (px C - hot_pixel_radius scale) (py C - hot_pixel_radius scale))).
  destruct (edge_crosses_ray_dec P eR) as [HR | HR];
    [ rewrite (cross_count_cons_cross P _ _ HR)
    | rewrite (cross_count_cons_nocross P _ _ HR) ];
    rewrite (cross_count_cons_nocross P _ _ (pixel_top_no_cross C scale P));
    (destruct (edge_crosses_ray_dec P eL) as [HL | HL];
       [ rewrite (cross_count_cons_cross P _ _ HL)
       | rewrite (cross_count_cons_nocross P _ _ HL) ];
       rewrite cross_count_nil; lia).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Crossing count = 1 iff a half-open-x / open-y box; inside iff one cross.*)
(* -------------------------------------------------------------------------- *)

Theorem pixel_cross_count_one_iff : forall C scale P, 0 < scale ->
  (cross_count P (ring_edges (pixel_ring C scale)) = 1%nat
   <-> (px C - hot_pixel_radius scale <= px P < px C + hot_pixel_radius scale
        /\ py C - hot_pixel_radius scale < py P < py C + hot_pixel_radius scale)).
Proof.
  intros C scale P Hs.
  pose proof (hot_pixel_radius_pos scale Hs) as Hr.
  pose proof (pixel_right_crosses_iff C scale P Hs) as HRiff.
  pose proof (pixel_left_crosses_iff  C scale P Hs) as HLiff.
  set (r := hot_pixel_radius scale) in *.
  rewrite pixel_ring_edges.
  rewrite (cross_count_cons_nocross P _ _ (pixel_bottom_no_cross C scale P)).
  destruct (edge_crosses_ray_dec P
              (mkPoint (px C + r) (py C - r), mkPoint (px C + r) (py C + r)))
    as [HR | HR].
  - rewrite (cross_count_cons_cross P _ _ HR).
    rewrite (cross_count_cons_nocross P _ _ (pixel_top_no_cross C scale P)).
    apply HRiff in HR. destruct HR as [HRy HRx].
    destruct (edge_crosses_ray_dec P
                (mkPoint (px C - r) (py C + r), mkPoint (px C - r) (py C - r)))
      as [HL | HL].
    + (* both verticals cross: count = 2, and px < cx - r refutes the box *)
      rewrite (cross_count_cons_cross P _ _ HL), cross_count_nil.
      apply HLiff in HL. destruct HL as [_ HLx].
      split; [ intro Hcontra; lia | intros [[Hxl _] _]; lra ].
    + (* only the right vertical crosses: count = 1, box holds *)
      rewrite (cross_count_cons_nocross P _ _ HL), cross_count_nil.
      assert (HnLx : ~ (px P < px C - r))
        by (intro Hlt; apply HL, HLiff; split; [ exact HRy | exact Hlt ]).
      split; [ intros _; split; [ split; lra | exact HRy ] | intros _; reflexivity ].
  - rewrite (cross_count_cons_nocross P _ _ HR).
    rewrite (cross_count_cons_nocross P _ _ (pixel_top_no_cross C scale P)).
    destruct (edge_crosses_ray_dec P
                (mkPoint (px C - r) (py C + r), mkPoint (px C - r) (py C - r)))
      as [HL | HL].
    + (* left crosses but right does not: impossible (cx - r < cx + r) *)
      exfalso. apply HR, HRiff. apply HLiff in HL. destruct HL as [HLy HLx].
      split; [ exact HLy | lra ].
    + (* neither vertical crosses: count = 0, box fails *)
      rewrite (cross_count_cons_nocross P _ _ HL), cross_count_nil.
      split.
      * intro Hcontra; lia.
      * intros [[Hxl Hxr] [Hyl Hyr]]. exfalso.
        apply HR, HRiff. split; [ split; lra | lra ].
Qed.

Theorem pixel_in_ring_iff_one_crossing : forall C scale P, 0 < scale ->
  (point_in_ring P (pixel_ring C scale)
   <-> cross_count P (ring_edges (pixel_ring C scale)) = 1%nat).
Proof.
  intros C scale P Hs.
  pose proof (pixel_ray_crosses_le_two C scale P) as Hle.
  unfold point_in_ring.
  destruct (ray_parity_count P (ring_edges (pixel_ring C scale))) as [Hodd _].
  split.
  - intro Hpir. apply Hodd in Hpir.
    destruct (cross_count P (ring_edges (pixel_ring C scale))) as [| [| [| n]]];
      cbn in Hpir; solve [ discriminate | reflexivity | lia ].
  - intro Hcc. apply Hodd. rewrite Hcc. reflexivity.
Qed.

(* HEADLINE: a point is inside the pixel ring iff it lies in the half-open-x,
   open-y box.  Note the y-interval is OPEN on both ends (the ray test grazes
   both horizontal edges' heights), whereas `in_hot_pixel` is closed-bottom. *)
Theorem pixel_point_in_ring_iff_box : forall C scale P, 0 < scale ->
  (point_in_ring P (pixel_ring C scale)
   <-> (px C - hot_pixel_radius scale <= px P < px C + hot_pixel_radius scale
        /\ py C - hot_pixel_radius scale < py P < py C + hot_pixel_radius scale)).
Proof.
  intros C scale P Hs.
  rewrite (pixel_in_ring_iff_one_crossing C scale P Hs).
  exact (pixel_cross_count_one_iff C scale P Hs).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The bridge to `in_hot_pixel`.                                           *)
(* -------------------------------------------------------------------------- *)

(* Total inclusion: the ray-parity interior is a subset of the half-open pixel
   (the box's open-bottom `cy - r < py` implies the pixel's closed-bottom). *)
Theorem pixel_point_in_ring_implies_in_hot_pixel : forall C scale P, 0 < scale ->
  point_in_ring P (pixel_ring C scale) -> in_hot_pixel P C scale.
Proof.
  intros C scale P Hs Hpir.
  apply (pixel_point_in_ring_iff_box C scale P Hs) in Hpir.
  destruct Hpir as [[Hxl Hxr] [Hyl Hyr]].
  unfold in_hot_pixel. split; split; lra.
Qed.

(* Converse OFF the included bottom edge: above the bottom edge the two
   predicates coincide. *)
Theorem in_hot_pixel_off_bottom_implies_point_in_ring : forall C scale P, 0 < scale ->
  py C - hot_pixel_radius scale < py P ->
  in_hot_pixel P C scale -> point_in_ring P (pixel_ring C scale).
Proof.
  intros C scale P Hs Hbot Hin.
  apply (pixel_point_in_ring_iff_box C scale P Hs).
  unfold in_hot_pixel in Hin. destruct Hin as [[Hxl Hxr] [Hyl Hyr]].
  split; split; lra.
Qed.

(* The genuine divergence: a point on the INCLUDED bottom edge is `in_hot_pixel`
   yet its rightward ray grazes the bottom vertices, so it is NOT
   `point_in_ring`.  The hot-pixel incarnation of the corpus's vertex-grazing
   caveat (`JCT_VertexGrazingCounterexample`). *)
Theorem pixel_grazing_bottom_edge :
  in_hot_pixel (mkPoint 0 (- (1/2))) (mkPoint 0 0) 1
  /\ ~ point_in_ring (mkPoint 0 (- (1/2))) (pixel_ring (mkPoint 0 0) 1).
Proof.
  assert (Hr : hot_pixel_radius 1 = 1/2)
    by (unfold hot_pixel_radius; lra).
  split.
  - unfold in_hot_pixel. rewrite Hr. cbn [px py]. split; split; lra.
  - intro Hpir.
    apply (pixel_point_in_ring_iff_box (mkPoint 0 0) 1 (mkPoint 0 (- (1/2)))) in Hpir;
      [ | lra ].
    rewrite Hr in Hpir. cbn [px py] in Hpir.
    destruct Hpir as [_ [Hyl _]]. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Validation: the unit pixel (scale = 1, centred at the origin).          *)
(* -------------------------------------------------------------------------- *)

(* The strict-interior centre is inside the unit pixel ring. *)
Corollary unit_pixel_centre_in_ring :
  point_in_ring (mkPoint 0 0) (pixel_ring (mkPoint 0 0) 1).
Proof.
  apply (pixel_point_in_ring_iff_box (mkPoint 0 0) 1 (mkPoint 0 0)); [ lra | ].
  assert (Hr : hot_pixel_radius 1 = 1/2) by (unfold hot_pixel_radius; lra).
  rewrite Hr. cbn [px py]. split; split; lra.
Qed.

(* And it is crossed exactly once. *)
Corollary unit_pixel_centre_one_crossing :
  cross_count (mkPoint 0 0) (ring_edges (pixel_ring (mkPoint 0 0) 1)) = 1%nat.
Proof.
  apply (pixel_in_ring_iff_one_crossing (mkPoint 0 0) 1 (mkPoint 0 0)); [ lra | ].
  exact unit_pixel_centre_in_ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions pixel_ray_crosses_le_two.
Print Assumptions pixel_point_in_ring_iff_box.
Print Assumptions pixel_point_in_ring_implies_in_hot_pixel.
Print Assumptions in_hot_pixel_off_bottom_implies_point_in_ring.
Print Assumptions pixel_grazing_bottom_edge.
