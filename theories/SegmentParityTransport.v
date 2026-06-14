(* ==========================================================================
   SegmentParityTransport.v

   Phase B brick of the H_bridge geometric/JCT route (Rung 3b-iv).

   Discrete parity transport: if the straight segment from `u` to `v` stays in
   the complement of a closed ring `r`, then `u` and `v` have the same
   point-in-ring (crossing-number) parity.  This is the combinatorial workhorse
   that replaces the continuous-path `parity_constant_on_components` at the
   single-segment granularity used by the bridge argument: a polyline that
   avoids the ring transports parity unchanged across each of its segments.

   It is a direct corollary of the proven `parity_constant_on_components`
   (theories/JCTSeparation.v): the affine path `(1-t)·u + t·v` is continuous
   (`straight_path_continuous`) and, by hypothesis, lands in the ring
   complement for every `t ∈ [0,1]`, so its endpoints share a component.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents
                               PointInRingCorrect JordanCurveSeam JCTSeparation.

Import ListNotations.
Open Scope R_scope.

(* The straight segment from `u` to `v`, as an affine path on [0,1]. *)
Definition seg_path (u v : Point) : R -> Point :=
  fun t => mkPoint ((1 - t) * px u + t * px v) ((1 - t) * py u + t * py v).

Lemma seg_path_0 : forall u v, seg_path u v 0 = u.
Proof. intros [xu yu] [xv yv]. unfold seg_path; cbn [px py]. f_equal; lra. Qed.

Lemma seg_path_1 : forall u v, seg_path u v 1 = v.
Proof. intros [xu yu] [xv yv]. unfold seg_path; cbn [px py]. f_equal; lra. Qed.

(* Discrete parity transport across a segment that avoids the ring. *)
Lemma parity_eq_of_clear_segment :
  forall (r : Ring) (u v : Point),
    ring_closed r ->
    ray_avoids_vertices u r ->
    ray_avoids_vertices v r ->
    (forall t : R, 0 <= t <= 1 -> ring_complement r (seg_path u v t)) ->
    (point_in_ring u r <-> point_in_ring v r).
Proof.
  intros r u v Hclosed Hru Hrv Hclear.
  apply (parity_constant_on_components r u v Hclosed Hru Hrv).
  exists (seg_path u v).
  split; [ apply straight_path_continuous | ].
  split; [ apply seg_path_0 | ].
  split; [ apply seg_path_1 | ].
  exact Hclear.
Qed.
