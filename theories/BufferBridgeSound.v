(* ============================================================================
   NetTopologySuite.Proofs.BufferBridgeSound
   ----------------------------------------------------------------------------
   Seam map: docs/buffer-noder-pipeline.md §6 (the H_bridge residual; soundness
   side) and §2.5 (Stage 5).
   The SOUNDNESS half of H_bridge, at the buffer-boundary distance level.

   `BufferBridge.v` decomposed the buffer headline's `H_bridge` into
   `buffer_extract_sound` ("the extracted result is within d of the input")
   and `buffer_extract_complete`, carried as named hypotheses because the
   exact equality `point_set (extract) = buffer_spec` holds only for the
   idealised round buffer with exact arcs.  Two construction-level facts make
   that precise; both are proven here, Qed, bridgeheaded on the closed
   `BufferOffset` / `BufferMiter` / `BufferBevel` lemmas.

   (1) SOUNDNESS SKELETON (the within-d direction holds for offset walls and
       bevel/round joins).  Every offset endpoint is at distance exactly |d|
       from its source endpoint (`offset_point_dist`); every bevel-join chord
       point is within d of the corner vertex (closed disk is convex, and the
       chord endpoints sit on the radius-d circle).  So the bevel-buffer
       boundary near a corner never escapes the d-ball of that corner.

   (2) THE MITER OBSTRUCTION (why soundness needs a non-miter join / the miter
       limit).  The miter apex lies strictly OUTSIDE the d-ball of the corner
       vertex: for the unit right-angle corner, `dist_sq V apex = 2 d^2 > d^2`
       (via the closed `miter_length_sq`).  Replacing a bevel/round join by an
       uncapped miter join therefore pushes the boundary out of the corner's
       d-ball -- the precise geometric reason the soundness direction of
       H_bridge cannot hold for the mitered buffer, complementing the
       chord-undershoot residual on the completeness side.

   Scope note (honesty).  These statements are about the d-ball of the corner
   VERTEX.  Full soundness against the input's d-neighbourhood (distance to
   the edge SEGMENTS, where a long edge can keep even the miter apex within d,
   and a short edge cannot) remains the analytic residual carried by
   `buffer_extract_sound`; JTS caps it with the miter limit
   (`BufferMiter.miter_within_limit_iff`).

   Pure-R; no atan / Flocq / snap_round.  Three-axiom footprint.
   No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Vec Distance Direction HotPixel
                               BufferOffset BufferMiter BufferBevel.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The within-d soundness skeleton.                                       *)
(* -------------------------------------------------------------------------- *)

(* Each offset endpoint is within d of its source endpoint (d >= 0). *)
Lemma offset_point_within_d :
  forall A B P : Point, forall d : R,
    A <> B -> 0 <= d -> dist P (offset_point A B P d) <= d.
Proof.
  intros A B P d Hne Hd.
  rewrite (offset_point_dist A B P d Hne), Rabs_right by lra. lra.
Qed.

(* The bevel-join endpoint sits on the radius-|d| circle about the corner. *)
Lemma bevel_point_dist :
  forall (V : Point) (ein : Vec) (d : R),
    ein <> vzero -> dist V (bevel_point V ein d) = Rabs d.
Proof.
  intros V ein d Hne. unfold dist, bevel_point.
  rewrite dist_sq_translate.
  replace ((d * vx (unit_perp ein)) * (d * vx (unit_perp ein)) +
           (d * vy (unit_perp ein)) * (d * vy (unit_perp ein)))
    with (d * d * vmag_sq (unit_perp ein)) by (unfold vmag_sq, vdot; ring).
  rewrite (vmag_sq_unit_perp ein Hne), Rmult_1_r.
  replace (d * d) with (Rsqr d) by (unfold Rsqr; ring).
  apply sqrt_Rsqr_abs.
Qed.

(* The closed d-ball is convex: a point on the segment between two points
   each within d of V is itself within d of V. *)
Lemma ball_convex :
  forall (V X Y : Point) (d t : R),
    0 <= d -> 0 <= t <= 1 ->
    dist V X <= d -> dist V Y <= d ->
    dist V (segment_point X Y t) <= d.
Proof.
  intros V X Y d t Hd Ht HX HY.
  apply (proj2 (dist_le_iff_dist_sq_le _ _ d Hd)).
  apply (proj1 (dist_le_iff_dist_sq_le _ _ d Hd)) in HX.
  apply (proj1 (dist_le_iff_dist_sq_le _ _ d Hd)) in HY.
  unfold dist_sq, segment_point in *. simpl in *.
  assert (Hid :
    (px V - ((1 - t) * px X + t * px Y)) * (px V - ((1 - t) * px X + t * px Y)) +
    (py V - ((1 - t) * py X + t * py Y)) * (py V - ((1 - t) * py X + t * py Y))
    = (1 - t) * ((px V - px X) * (px V - px X) + (py V - py X) * (py V - py X))
      + t * ((px V - px Y) * (px V - px Y) + (py V - py Y) * (py V - py Y))
      - t * (1 - t) * ((px X - px Y) * (px X - px Y) + (py X - py Y) * (py X - py Y)))
    by ring.
  assert (Hpos :
    0 <= t * (1 - t) * ((px X - px Y) * (px X - px Y) + (py X - py Y) * (py X - py Y))).
  { apply Rmult_le_pos.
    - apply Rmult_le_pos; lra.
    - apply Rplus_le_le_0_compat;
        [ pose proof (Rle_0_sqr (px X - px Y)) as Hq
        | pose proof (Rle_0_sqr (py X - py Y)) as Hq ];
        unfold Rsqr in Hq; exact Hq. }
  rewrite Hid.
  (* Abstract the squared distances to atoms so nra works over {A,B,Cc,t,d}. *)
  set (A := (px V - px X) * (px V - px X) + (py V - py X) * (py V - py X)) in *.
  set (B := (px V - px Y) * (px V - px Y) + (py V - py Y) * (py V - py Y)) in *.
  set (Cc := (px X - px Y) * (px X - px Y) + (py X - py Y) * (py X - py Y)) in *.
  nra.
Qed.

(* Every point of the bevel-join chord is within d of the corner vertex:
   the bevel join keeps the buffer boundary inside the corner's d-ball. *)
Lemma bevel_chord_within_d :
  forall (V : Point) (ein eout : Vec) (d t : R),
    ein <> vzero -> eout <> vzero -> 0 <= d -> 0 <= t <= 1 ->
    dist V (segment_point (bevel_point V ein d) (bevel_point V eout d) t) <= d.
Proof.
  intros V ein eout d t Hin Hout Hd Ht.
  apply ball_convex; try assumption.
  - rewrite bevel_point_dist by assumption. rewrite Rabs_right; lra.
  - rewrite bevel_point_dist by assumption. rewrite Rabs_right; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The miter obstruction.                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma vmag_unit_x : vmag (mkVec 1 0) = 1.
Proof.
  unfold vmag, vmag_sq, vdot. simpl.
  replace (1 * 1 + 0 * 0) with 1 by ring. apply sqrt_1.
Qed.

Lemma vmag_unit_y : vmag (mkVec 0 1) = 1.
Proof.
  unfold vmag, vmag_sq, vdot. simpl.
  replace (0 * 0 + 1 * 1) with 1 by ring. apply sqrt_1.
Qed.

(* The miter apex of the unit right-angle corner is at squared distance 2 d^2
   from the vertex (closed `miter_length_sq` with det = 1). *)
Lemma miter_apex_dist_sq_90 :
  forall d : R,
    dist_sq (mkPoint 0 0)
            (miter_apex (mkPoint 0 0) (mkVec 1 0) (mkVec 0 1) d)
    = 2 * (d * d).
Proof.
  intros d.
  assert (Hdet : miter_det (mkVec 1 0) (mkVec 0 1) <> 0)
    by (unfold miter_det; simpl; lra).
  pose proof (miter_length_sq (mkPoint 0 0) (mkVec 1 0) (mkVec 0 1) d Hdet) as Hlen.
  rewrite vmag_unit_x, vmag_unit_y in Hlen.
  unfold miter_det in Hlen. simpl in Hlen. nra.
Qed.

(* Hence the miter apex lies strictly outside the corner's d-ball -- the
   buffer boundary it produces is NOT within d of the corner vertex. *)
Theorem miter_apex_overshoots_vertex :
  forall d : R,
    0 < d ->
    d * d < dist_sq (mkPoint 0 0)
                    (miter_apex (mkPoint 0 0) (mkVec 1 0) (mkVec 0 1) d).
Proof.
  intros d Hd. rewrite miter_apex_dist_sq_90. nra.
Qed.

(* In Euclidean distance: the unit right-angle miter apex is sqrt 2 * d from
   the vertex, strictly beyond d. *)
Corollary miter_apex_dist_gt_d :
  forall d : R,
    0 < d ->
    d < dist (mkPoint 0 0)
             (miter_apex (mkPoint 0 0) (mkVec 1 0) (mkVec 0 1) d).
Proof.
  intros d Hd.
  apply Rnot_le_lt. intro Hle.
  apply (proj1 (dist_le_iff_dist_sq_le _ _ d (Rlt_le _ _ Hd))) in Hle.
  pose proof (miter_apex_overshoots_vertex d Hd). lra.
Qed.

Print Assumptions bevel_chord_within_d.
Print Assumptions miter_apex_overshoots_vertex.
