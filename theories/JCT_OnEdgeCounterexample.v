(* ============================================================================
   NetTopologySuite.Proofs.JCT_OnEdgeCounterexample
   ----------------------------------------------------------------------------
   RED for the H1 seam AS STATED: `JCT.parity_characterises_interior_cont_strict`
   is FALSE for ON-EDGE points -- the two generic-position guards
   (`no_horizontal_edge_at`, `ray_avoids_vertices`) do NOT exclude the ring
   skeleton, and the ray-parity test is HALF-OPEN there (the boundary
   phenomenon of GeneralTriangleParityRED.v, one level up).

   Witness.  The CCW triangle A=(0,0), B=(4,1), C=(1,3) -- NO horizontal edge
   (edge heights (0,1), (1,3), (3,0)) -- and the point p = (1/2, 3/2), the
   MIDPOINT of edge C--A.  Then:

     - `point_in_ring p` is TRUE: the rightward ray at height 3/2 crosses edge
       B--C once (at x = 13/4 > 1/2); edge A--B lies below (heights 0..1); and
       the edge C--A that p LIES ON does not count (p is not strictly to its
       left -- the signed area is exactly 0).  Parity odd.
     - `geometric_interior_cont p` is FALSE: p is in the ring IMAGE (parameter
       t = 1/2 on edge C--A), hence not in `ring_complement`.
     - ALL FIVE premises of the strict seam hold: the triangle is ring_simple
       (adjacent edges never cross properly -- six `nra` cases), ring_closed,
       has >= 4 points, has no horizontal edge, and p's height 3/2 avoids all
       vertex heights {0, 1, 3} -- so `ray_avoids_vertices` holds too.

   Hence the seam's biconditional fails (TRUE -> FALSE), refuting the Prop at
   (p, r).  CONSEQUENCE: any eventual discharge of H1 must carry an OFF-RING
   premise.  The corrected seam `parity_characterises_interior_cont_offring`
   below adds `ring_complement r p` to the strict guard set, and the headline
   `point_in_ring_correct_jct_cont_offring` re-wires
   `JCT.point_in_ring_correct_jct_cont` against it.  Note the three closed
   families (rectangle / right triangle / arbitrary triangle) are unaffected:
   their headlines are scoped to STRICT-INTERIOR points, which are off-ring by
   construction (`gtri_interior_complement` and friends).

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT.
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity.
Import ListNotations.

Local Open Scope R_scope.

(* The witness ring and point: triangle (0,0),(4,1),(1,3), midpoint of C--A. *)
Definition oe_ring : Ring := gtri_ring 0 0 4 1 1 3.
Definition oe_pt : Point := mkPoint (1 / 2) (3 / 2).

(* p lies ON the ring: parameter 1/2 along edge (C,A). *)
Lemma oe_pt_on_ring : ring_image oe_ring oe_pt.
Proof.
  unfold oe_ring, oe_pt.
  exists (mkPoint 1 3, mkPoint 0 0), (1 / 2).
  rewrite (ring_edges_gtri 0 0 4 1 1 3).
  repeat split; cbn [In px py fst snd];
    [ right; right; left; reflexivity | lra | lra | lra | lra ].
Qed.

(* Yet the half-open ray-parity test counts p INSIDE: B--C crosses once. *)
Lemma oe_pt_in_ring : point_in_ring oe_pt oe_ring.
Proof.
  unfold point_in_ring, oe_ring, oe_pt. rewrite (ring_edges_gtri 0 0 4 1 1 3).
  apply rpo_skip.
  - (* A--B (heights 0..1) is below the ray *)
    rewrite (edge_cross_sign 0 0 4 1 (mkPoint (1 / 2) (3 / 2))); cbn [px py].
    intros [[Hy _] | [Hy _]]; lra.
  - apply rpo_cross.
    + (* B--C crosses: heights 1..3 straddle 3/2, p strictly left *)
      rewrite (edge_cross_sign 4 1 1 3 (mkPoint (1 / 2) (3 / 2))); cbn [px py].
      left; repeat split; nra.
    + apply rpe_skip; [ | apply rpe_nil ].
      (* C--A: p lies on it; the signed area is exactly 0, not < 0 *)
      rewrite (edge_cross_sign 1 3 0 0 (mkPoint (1 / 2) (3 / 2))); cbn [px py].
      intros [[Hy _] | [_ Hs]]; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* All five premises of the strict seam hold at the witness.                   *)
(* -------------------------------------------------------------------------- *)

Lemma oe_ring_closed : ring_closed oe_ring.
Proof.
  exists (mkPoint 0 0), [mkPoint 4 1; mkPoint 1 3]. reflexivity.
Qed.

Lemma oe_ring_min_points : ring_has_minimum_points oe_ring.
Proof. unfold ring_has_minimum_points, oe_ring; cbn; lia. Qed.

Lemma oe_no_horizontal : no_horizontal_edge_at oe_pt oe_ring.
Proof.
  unfold no_horizontal_edge_at, oe_ring.
  rewrite (ring_edges_gtri 0 0 4 1 1 3).
  repeat constructor; cbn [px py fst snd]; lra.
Qed.

Lemma oe_ray_avoids : ray_avoids_vertices oe_pt oe_ring.
Proof.
  intros v Hv [Heq _].
  unfold oe_ring, gtri_ring in Hv; cbn in Hv.
  unfold oe_pt in Heq.
  destruct Hv as [Hv | [Hv | [Hv | [Hv | []]]]]; subst v;
    cbn [py] in Heq; lra.
Qed.

(* The triangle is simple: no two distinct edges cross at interior points.
   All pairs are adjacent (3 edges); a shared endpoint is not a PROPER
   intersection, and the six ordered off-diagonal cases close by `nra`. *)
Lemma oe_ring_simple : ring_simple oe_ring.
Proof.
  intros e1 e2 H1 H2 Hne.
  unfold oe_ring in H1, H2; rewrite (ring_edges_gtri 0 0 4 1 1 3) in H1, H2.
  cbn [In] in H1, H2.
  intros [t [s [Ht [Hs [Hx Hy]]]]].
  destruct H1 as [He1 | [He1 | [He1 | []]]];
  destruct H2 as [He2 | [He2 | [He2 | []]]];
    subst e1; subst e2;
    try (exfalso; apply Hne; reflexivity);
    cbn [px py fst snd] in Hx, Hy; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The RED: the strict H1 seam is FALSE at an on-edge, fully-guarded point.    *)
(* -------------------------------------------------------------------------- *)

Theorem parity_seam_strict_refuted_on_edge :
  ~ parity_characterises_interior_cont_strict oe_pt oe_ring.
Proof.
  unfold parity_characterises_interior_cont_strict. intro H.
  specialize (H oe_ring_simple oe_ring_closed oe_ring_min_points
                oe_no_horizontal oe_ray_avoids).
  destruct H as [_ Hback].
  destruct (Hback oe_pt_in_ring) as [Hcompl _].
  exact (Hcompl oe_pt_on_ring).
Qed.

(* The un-strengthened seam falls with it (its premises are a subset). *)
Corollary parity_seam_refuted_on_edge :
  ~ parity_characterises_interior_cont oe_pt oe_ring.
Proof.
  unfold parity_characterises_interior_cont. intro H.
  specialize (H oe_ring_simple oe_ring_closed oe_ring_min_points
                oe_no_horizontal).
  destruct H as [_ Hback].
  destruct (Hback oe_pt_in_ring) as [Hcompl _].
  exact (Hcompl oe_pt_on_ring).
Qed.

(* -------------------------------------------------------------------------- *)
(* The re-scoped seam: add the OFF-RING premise.  This is the corrected H1     *)
(* target -- the minimal repair the witness above shows is necessary.          *)
(* -------------------------------------------------------------------------- *)

Definition parity_characterises_interior_cont_offring (p : Point) (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  ring_complement r p ->
  no_horizontal_edge_at p r ->
  ray_avoids_vertices p r ->
  (geometric_interior_cont p r <-> point_in_ring p r).

(* The witness no longer applies: it fails the off-ring premise outright. *)
Remark oe_pt_excluded_by_offring_premise : ~ ring_complement oe_ring oe_pt.
Proof. intro Hc. exact (Hc oe_pt_on_ring). Qed.

(* The headline, re-wired against the corrected seam (the honest analogue of
   JCT.point_in_ring_correct_jct_cont). *)
Theorem point_in_ring_correct_jct_cont_offring :
  forall (p : Point) (r : Ring),
    ring_simple r ->
    ring_closed r ->
    ring_has_minimum_points r ->
    ring_complement r p ->
    no_horizontal_edge_at p r ->
    ray_avoids_vertices p r ->
    parity_characterises_interior_cont_offring p r ->
    point_in_ring p r <-> geometric_interior_cont p r.
Proof.
  intros p r Hs Hc Hm Hcompl Hnh Hrav Hjct.
  split; intro H; apply (Hjct Hs Hc Hm Hcompl Hnh Hrav); exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions parity_seam_strict_refuted_on_edge.
Print Assumptions parity_seam_refuted_on_edge.
Print Assumptions point_in_ring_correct_jct_cont_offring.
