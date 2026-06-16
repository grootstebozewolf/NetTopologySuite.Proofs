(* ============================================================================
   NetTopologySuite.Proofs.ConvexSlice
   ----------------------------------------------------------------------------
   The convex SLICE FACT: a point inward of both straddling chain edges at its
   height lies in EVERY edge half-plane (`conv_min >= 0`).

   This is the geometric keystone the convex-JCT campaign isolated as a residual
   (the convexity "horizontal slice = inter-chain interval" content behind both
   `ConvexYUnimodal.convex_no_interior_ymin` and
   `ConvexExteriorEven.convex_exterior_balanced`).  It is proved here WITHOUT any
   cross-product monotonicity / supporting-line induction, via two observations:

     (1) the point `m` on a straddling edge at height `py p` is a `ring_image`
         point, so `ConvexOffringSeam.image_slack_nonneg` puts it in EVERY
         half-plane the ring's vertices satisfy; and

     (2) `hp_slack (a,b,c) q = c - a*px q - b*py q` is AFFINE in `x` with slope
         `-a`, and for `edge_inward_hp e` the x-coefficient `a` is exactly the
         edge's y-direction `py (snd e) - py (fst e)`.

   So a point bounded on the left by the on-edge image point of the straddling
   UP edge and on the right by that of the straddling DOWN edge satisfies each
   half-plane by a one-line `nra`, split on the sign of the half-plane's
   x-coefficient.

   What remains open (a strictly smaller, separate residual): straddle
   EXTRACTION — locating the straddling `e_i`/`e_d` for an arbitrary query point —
   which for exterior points needs vertex-height avoidance unavailable from
   `ray_avoids_vertices` alone.  Given the straddling edges, exterior-even is now
   a theorem (`exterior_slice_contra`).

   Pure-R + three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra.
From NTS.Proofs Require Import Distance Overlay MonotoneChainParity
                               MonotoneChainCoverage ConvexField ConvexChainSplit
                               PointInRingTangents ConvexOffringSeam
                               DiamondOffringSeam.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  hp_slack is affine in x at a fixed height (slope = - x-coefficient).     *)
(* -------------------------------------------------------------------------- *)

Lemma hp_slack_sub_x : forall (hp : R * R * R) (q1 q2 : Point),
  py q1 = py q2 ->
  hp_slack hp q1 - hp_slack hp q2 = - (fst (fst hp)) * (px q1 - px q2).
Proof.
  intros [[a b] c] q1 q2 Hy. unfold hp_slack. cbn [fst]. rewrite Hy. ring.
Qed.

(* The x-coefficient of an inward half-plane is the edge's y-direction. *)
Lemma edge_inward_hp_xcoef : forall e : Edge,
  fst (fst (edge_inward_hp e)) = py (snd e) - py (fst e).
Proof. intros [[ax ay] [bx by_]]. cbn [edge_inward_hp fst snd py]. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The point on a straddling edge at height `py p` is a ring-image point.   *)
(* -------------------------------------------------------------------------- *)

Lemma straddle_point_ring_image : forall (r : Ring) (e : Edge) (p : Point),
  In e (ring_edges r) ->
  straddles p e ->
  exists m : Point,
    ring_image r m /\ py m = py p /\ hp_slack (edge_inward_hp e) m = 0.
Proof.
  intros r e p Hin Hstr.
  destruct e as [[vx vy] [wx wy]].
  unfold straddles in Hstr. cbn [fst snd px py] in Hstr.
  set (t := (py p - vy) / (wy - vy)).
  assert (Hden : wy - vy <> 0) by lra.
  assert (Ht0 : 0 <= t).
  { subst t. destruct Hstr as [[H1 H2] | [H1 H2]].
    - unfold Rdiv. apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ].
    - replace ((py p - vy) / (wy - vy)) with ((vy - py p) / (vy - wy))
        by (field; lra).
      unfold Rdiv. apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ]. }
  assert (Ht1 : t <= 1).
  { assert (H1t : 1 - t = (wy - py p) / (wy - vy)) by (subst t; field; lra).
    assert (Hnn : 0 <= 1 - t).
    { rewrite H1t. destruct Hstr as [[H1 H2] | [H1 H2]].
      - unfold Rdiv. apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ].
      - replace ((wy - py p) / (wy - vy)) with ((py p - wy) / (vy - wy))
          by (field; lra).
        unfold Rdiv. apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ]. }
    lra. }
  exists (mkPoint ((1 - t) * vx + t * wx) ((1 - t) * vy + t * wy)).
  assert (Hty : (1 - t) * vy + t * wy = py p).
  { subst t. field. exact Hden. }
  split; [ | split ].
  - (* ring_image *)
    exists (mkPoint vx vy, mkPoint wx wy), t.
    cbn [fst snd px py].
    refine (conj Hin (conj (conj Ht0 Ht1) (conj _ _))); reflexivity.
  - (* py m = py p *) cbn [py]. exact Hty.
  - (* slack of e at m is 0 (m is on e's line) *)
    rewrite hp_slack_edge_inward_cross_product. cbn [px py]. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  THE SLICE FACT: inward of both straddling chain edges ⟹ in all hps.      *)
(* -------------------------------------------------------------------------- *)

Theorem convex_slice_all_halfplanes :
  forall (r : Ring) (hps : list (R * R * R)) (p : Point) (e_i e_d : Edge),
    Forall (vertices_in_halfplane r) hps ->
    In e_i (ring_edges r) -> In e_d (ring_edges r) ->
    py (fst e_i) < py (snd e_i) ->          (* e_i is an UP edge   *)
    py (snd e_d) < py (fst e_d) ->          (* e_d is a DOWN edge  *)
    straddles p e_i -> straddles p e_d ->
    0 < hp_slack (edge_inward_hp e_i) p ->
    0 <= hp_slack (edge_inward_hp e_d) p ->
    Forall (fun hp => 0 <= hp_slack hp p) hps.
Proof.
  intros r hps p e_i e_d Hverts Hii Hid Hup Hdn Hstri Hstrd Hsi Hsd.
  (* The two on-edge image points at height py p. *)
  destruct (straddle_point_ring_image r e_i p Hii Hstri) as [mi [Hmi_img [Hmi_y Hmi_0]]].
  destruct (straddle_point_ring_image r e_d p Hid Hstrd) as [md [Hmd_img [Hmd_y Hmd_0]]].
  (* px p < px mi (p left of the up edge e_i). *)
  assert (Hxi : px p < px mi).
  { pose proof (hp_slack_sub_x (edge_inward_hp e_i) p mi (eq_sym Hmi_y)) as Hsub.
    rewrite Hmi_0, (edge_inward_hp_xcoef e_i) in Hsub. nra. }
  (* px md <= px p (p right of the down edge e_d). *)
  assert (Hxd : px md <= px p).
  { pose proof (hp_slack_sub_x (edge_inward_hp e_d) p md (eq_sym Hmd_y)) as Hsub.
    rewrite Hmd_0, (edge_inward_hp_xcoef e_d) in Hsub. nra. }
  (* Per-half-plane: bound p's slack below by mi's (a>=0) or md's (a<0). *)
  rewrite Forall_forall in Hverts |- *.
  intros hp Hhp.
  pose proof (image_slack_nonneg r hp mi (Hverts hp Hhp) Hmi_img) as Hmi_s.
  pose proof (image_slack_nonneg r hp md (Hverts hp Hhp) Hmd_img) as Hmd_s.
  pose proof (hp_slack_sub_x hp p mi (eq_sym Hmi_y)) as Hsub_i.
  pose proof (hp_slack_sub_x hp p md (eq_sym Hmd_y)) as Hsub_d.
  destruct hp as [[a b] c]. cbn [fst] in Hsub_i, Hsub_d.
  destruct (Rle_or_lt 0 a) as [Ha | Ha].
  - (* a >= 0: hp_slack decreasing in x; px p < px mi *) nra.
  - (* a < 0: hp_slack increasing in x; px md <= px p *) nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Corollaries: conv_min >= 0, and the exterior contradiction.             *)
(* -------------------------------------------------------------------------- *)

(* All slacks nonnegative ⟹ conv_min nonnegative (local, self-contained). *)
Lemma conv_min_nonneg_local : forall hps pt,
  Forall (fun hp => 0 <= hp_slack hp pt) hps -> 0 <= conv_min hps pt.
Proof.
  induction hps as [| h rest IH]; intros pt H; cbn [conv_min]; [ lra | ].
  inversion H as [| ? ? Hh Hrest]; subst.
  pose proof (IH pt Hrest) as Hr.
  unfold Rmin; destruct (Rle_dec (hp_slack h pt) (conv_min rest pt)); lra.
Qed.

(* The slice fact, packaged as `0 <= conv_min`. *)
Corollary conv_min_nonneg_of_slice :
  forall (r : Ring) (hps : list (R * R * R)) (p : Point) (e_i e_d : Edge),
    Forall (vertices_in_halfplane r) hps ->
    In e_i (ring_edges r) -> In e_d (ring_edges r) ->
    py (fst e_i) < py (snd e_i) ->
    py (snd e_d) < py (fst e_d) ->
    straddles p e_i -> straddles p e_d ->
    0 < hp_slack (edge_inward_hp e_i) p ->
    0 <= hp_slack (edge_inward_hp e_d) p ->
    0 <= conv_min hps p.
Proof.
  intros r hps p e_i e_d Hv Hii Hid Hup Hdn Hsi Hsd Hpi Hpd.
  apply conv_min_nonneg_local.
  apply (convex_slice_all_halfplanes r hps p e_i e_d); assumption.
Qed.

(* With the straddling edges in hand, an exterior point is impossible: the
   inc-crossed/dec-not contradiction of `convex_exterior_balanced`, now a
   theorem.  (Only the straddle EXTRACTION remains open.) *)
Corollary exterior_slice_contra :
  forall (r : Ring) (hps : list (R * R * R)) (p : Point) (e_i e_d : Edge),
    Forall (vertices_in_halfplane r) hps ->
    In e_i (ring_edges r) -> In e_d (ring_edges r) ->
    py (fst e_i) < py (snd e_i) ->
    py (snd e_d) < py (fst e_d) ->
    straddles p e_i -> straddles p e_d ->
    0 < hp_slack (edge_inward_hp e_i) p ->
    0 <= hp_slack (edge_inward_hp e_d) p ->
    conv_min hps p < 0 -> False.
Proof.
  intros r hps p e_i e_d Hv Hii Hid Hup Hdn Hsi Hsd Hpi Hpd Hneg.
  pose proof (conv_min_nonneg_of_slice r hps p e_i e_d Hv Hii Hid Hup Hdn Hsi Hsd Hpi Hpd).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Validation: the diamond's interior point (0, 1/2).                      *)
(* -------------------------------------------------------------------------- *)

(* p = (0, 1/2) sits inward of the straddling up edge (2,0)->(0,2) and the
   straddling down edge (0,2)->(-2,0); the slice fact concludes it satisfies all
   four diamond half-planes. *)
Lemma diamond_slice_validation :
  Forall (fun hp => 0 <= hp_slack hp (mkPoint 0 (1/2))) diamond_hps.
Proof.
  apply (convex_slice_all_halfplanes diamond_ring diamond_hps (mkPoint 0 (1/2))
           (mkPoint 2 0, mkPoint 0 2) (mkPoint 0 2, mkPoint (-2) 0)).
  - exact diamond_vertices_in_hps.
  - rewrite ring_edges_diamond. right; left; reflexivity.
  - rewrite ring_edges_diamond. right; right; left; reflexivity.
  - cbn [fst snd py]; lra.
  - cbn [fst snd py]; lra.
  - unfold straddles; cbn [fst snd py]; left; lra.
  - unfold straddles; cbn [fst snd py]; right; lra.
  - unfold hp_slack, edge_inward_hp; cbn [fst snd px py]; lra.
  - unfold hp_slack, edge_inward_hp; cbn [fst snd px py]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions straddle_point_ring_image.
Print Assumptions convex_slice_all_halfplanes.
Print Assumptions conv_min_nonneg_of_slice.
Print Assumptions exterior_slice_contra.
Print Assumptions diamond_slice_validation.
