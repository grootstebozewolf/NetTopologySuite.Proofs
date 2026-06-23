(* ============================================================================
   NetTopologySuite.Proofs.ArcArcDistance
   ----------------------------------------------------------------------------
   Issue #64 / JTS #1195 §7 D-AA: ARC-TO-ARC (circle-to-circle) DISTANCE, the
   analytic core / proof companion of the oracle ARC_ARC_DISTANCE mode.  The
   arc-to-arc follow-up explicitly deferred by theories/ArcDistance.v (D-PT).

   For two circles (centres O1, O2, radii r1, r2) that are EXTERNALLY separated
   (r1 + r2 <= d, d = dist O1 O2), the minimum distance between them is the
   radial gap d - r1 - r2, realised by the two feet on the segment O1 O2:

     - LOWER BOUND (`two_circles_dist_lower`): every pair (X1 on circle 1,
       X2 on circle 2) is at least d - r1 - r2 apart -- two triangle
       inequalities through O1 and O2 (the reverse triangle inequality, one
       dimension up from `ArcDistance.point_circle_dist_lower`).  This holds
       UNCONDITIONALLY (it is just vacuous/negative when the circles overlap).
     - ATTAINMENT (`circle_feet_dist`): the radial feet
       F1 = O1 + (r1/d)(O2-O1)  and  F2 = O2 + (r2/d)(O1-O2)
       (`ArcDistance.radial_foot O1 O2 r1` / `radial_foot O2 O1 r2`) lie on
       their circles and are exactly d - r1 - r2 apart -- F2 - F1 collapses to
       (O2-O1)(d - r1 - r2)/d, a `field` identity.

   Composed (`two_circles_dist_radial`): for externally separated circles the
   radial feet realise the infimum, so the circle-to-circle distance IS
   d - r1 - r2.  This is the value ARC_ARC_DISTANCE emits for its both-feet-
   on-arc case; the arc-level corollary `arc_arc_dist_external` restates it for
   two valid arcs' circumcircles.

   Pure metric algebra (`Distance` + `Linearise.dist_triangle`), reusing the
   D-PT `radial_foot` lemmas.  THREE-AXIOM (the classical-reals trio -- no
   trig / atan2 / sin_lt_x), so no `docs/audit-exceptions.txt` entry.  No
   `Admitted`/`Axiom`/`Parameter`.

   DEFERRED (honest scope, mirroring D-PT): the on-arc-sector clamping (feet
   off-sweep -> nearest endpoint-pair, matching the oracle's atan2 sector
   test); the INTERNAL (d <= |r1 - r2|, distance |r1 - r2| - d) and OVERLAPPING
   (distance 0) regimes; arc-segment distance; and a binary64 layer.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Linearise ArcDistance CurveGeometry
  ArcChordApprox ArcOffsetThreePoint ArcIntersect.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Lower bound: two circles are at least d - r1 - r2 apart.                *)
(*                                                                            *)
(* Reverse triangle inequality through BOTH centres: chain O1 -> X1 -> X2 ->   *)
(* O2 by `dist_triangle` twice.  Holds for every X1 on circle 1, X2 on circle  *)
(* 2 -- no separation hypothesis (the bound is just trivial when negative).    *)
(* -------------------------------------------------------------------------- *)

Theorem two_circles_dist_lower :
  forall (O1 O2 X1 X2 : Point) (r1 r2 : R),
    dist O1 X1 = r1 ->
    dist O2 X2 = r2 ->
    dist O1 O2 - r1 - r2 <= dist X1 X2.
Proof.
  intros O1 O2 X1 X2 r1 r2 H1 H2.
  pose proof (dist_triangle O1 X1 O2) as T1.   (* dist O1 O2 <= dist O1 X1 + dist X1 O2 *)
  pose proof (dist_triangle X1 X2 O2) as T2.   (* dist X1 O2 <= dist X1 X2 + dist X2 O2 *)
  rewrite (dist_sym X2 O2) in T2.              (* dist X2 O2 = dist O2 X2 = r2 *)
  rewrite H1 in T1. rewrite H2 in T2.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Attainment: the two radial feet are exactly d - r1 - r2 apart.          *)
(* -------------------------------------------------------------------------- *)

(* F2 - F1 = (O2 - O1) * (d - r1 - r2)/d, so |F1 F2|^2 = (d - r1 - r2)^2.       *)
Lemma circle_feet_dist :
  forall (O1 O2 : Point) (r1 r2 : R),
    0 < dist O1 O2 ->
    r1 + r2 <= dist O1 O2 ->
    dist (radial_foot O1 O2 r1) (radial_foot O2 O1 r2)
      = dist O1 O2 - r1 - r2.
Proof.
  intros O1 O2 r1 r2 Hd Hext.
  assert (Hd2 : dist O1 O2 * dist O1 O2 = dist_sq O1 O2) by apply dist_mul_self.
  (* squared-distance of the two feet factors as ((d-r1-r2)/d)^2 * dist_sq O1 O2 *)
  assert (HF : dist_sq (radial_foot O1 O2 r1) (radial_foot O2 O1 r2)
               = (dist O1 O2 - r1 - r2) / dist O1 O2
                 * ((dist O1 O2 - r1 - r2) / dist O1 O2)
                 * dist_sq O1 O2).
  { unfold dist_sq, radial_foot. simpl.
    rewrite (dist_sym O2 O1). field. lra. }
  (* bind the gap as an opaque g so `unfold dist` cannot expand dist O1 O2
     on the RHS into sqrt(dist_sq O1 O2) (which lra could not relate to Hext) *)
  set (g := dist O1 O2 - r1 - r2).
  assert (Hsq : dist_sq (radial_foot O1 O2 r1) (radial_foot O2 O1 r2) = g * g).
  { unfold g. rewrite HF, <- Hd2. field. lra. }
  unfold dist. rewrite Hsq.
  replace (g * g) with (Rsqr g) by (unfold Rsqr; ring).
  apply sqrt_Rsqr. unfold g. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The circle-to-circle distance is d - r1 - r2 (infimum, attained).       *)
(* -------------------------------------------------------------------------- *)

Theorem two_circles_dist_radial :
  forall (O1 O2 : Point) (r1 r2 : R),
    0 < dist O1 O2 -> 0 <= r1 -> 0 <= r2 ->
    r1 + r2 <= dist O1 O2 ->
    (* the two radial feet are on their circles ... *)
    dist O1 (radial_foot O1 O2 r1) = r1
    /\ dist O2 (radial_foot O2 O1 r2) = r2
    (* ... exactly d - r1 - r2 apart ... *)
    /\ dist (radial_foot O1 O2 r1) (radial_foot O2 O1 r2)
         = dist O1 O2 - r1 - r2
    (* ... and no cross-circle pair is closer. *)
    /\ (forall X1 X2, dist O1 X1 = r1 -> dist O2 X2 = r2 ->
          dist O1 O2 - r1 - r2 <= dist X1 X2).
Proof.
  intros O1 O2 r1 r2 Hd Hr1 Hr2 Hext.
  split; [ apply radial_foot_on_circle; assumption | ].
  split; [ apply radial_foot_on_circle; [ rewrite (dist_sym O2 O1); exact Hd | exact Hr2 ] | ].
  split; [ apply circle_feet_dist; assumption | ].
  intros X1 X2 H1 H2. apply (two_circles_dist_lower O1 O2 X1 X2 r1 r2 H1 H2).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Arc-level corollary: externally separated circumcircles.               *)
(*                                                                            *)
(* Restates §3 for two valid arcs (positive circumradii), the D-AA-relevant   *)
(* shape.  DEFERRED: on-arc-sector membership of the feet (atan2 / oracle      *)
(* float layer) -- this certifies the unconditional circle-to-circle core.    *)
(* -------------------------------------------------------------------------- *)

Theorem arc_arc_dist_external :
  forall (a1 a2 : CircularArc),
    valid_arc a1 -> valid_arc a2 ->
    arc_radius a1 + arc_radius a2 <= dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1)
         (radial_foot (arc_center a1) (arc_center a2) (arc_radius a1)) = arc_radius a1
    /\ dist (arc_center a2)
            (radial_foot (arc_center a2) (arc_center a1) (arc_radius a2)) = arc_radius a2
    /\ dist (radial_foot (arc_center a1) (arc_center a2) (arc_radius a1))
            (radial_foot (arc_center a2) (arc_center a1) (arc_radius a2))
         = dist (arc_center a1) (arc_center a2) - arc_radius a1 - arc_radius a2
    /\ (forall X1 X2,
          dist (arc_center a1) X1 = arc_radius a1 ->
          dist (arc_center a2) X2 = arc_radius a2 ->
          dist (arc_center a1) (arc_center a2) - arc_radius a1 - arc_radius a2
            <= dist X1 X2).
Proof.
  intros a1 a2 Hva1 Hva2 Hext.
  assert (Hr1 : 0 < arc_radius a1) by (apply arc_radius_pos; exact Hva1).
  assert (Hr2 : 0 < arc_radius a2) by (apply arc_radius_pos; exact Hva2).
  assert (Hd : 0 < dist (arc_center a1) (arc_center a2)) by lra.
  apply two_circles_dist_radial; lra.
Qed.

(* Sweep-clamp tightness wrapper for the external case.
   When the caller has determined (via its atan2 sector test, mirrored here
   by arc_span_contains) that both radial feet lie in their arc sweeps, the
   external gap value computed by arc_arc_dist_external is the correct one
   to use.  The lower-bound direction already holds unconditionally over the
   circumcircles (two_circles_dist_lower); the span hyps simply justify
   selecting the radial candidate instead of an endpoint pair. *)
Lemma arc_arc_external_feet_on_arcs_tight :
  forall (a1 a2 : CircularArc),
    valid_arc a1 -> valid_arc a2 ->
    let O1 := arc_center a1 in
    let O2 := arc_center a2 in
    let r1 := arc_radius a1 in
    let r2 := arc_radius a2 in
    let d := dist O1 O2 in
    0 < d ->
    r1 + r2 <= d ->
    let f1 := radial_foot O1 O2 r1 in
    let f2 := radial_foot O2 O1 r2 in
    arc_span_contains a1 f1 ->
    arc_span_contains a2 f2 ->
    (* The gap value from the external core is attained at the feet and is a
       lower bound for any pair on the circumcircles (hence for arc points). *)
    dist f1 f2 = d - r1 - r2 /\
    (forall X1 X2,
       dist O1 X1 = r1 ->
       dist O2 X2 = r2 ->
       d - r1 - r2 <= dist X1 X2).
Proof.
  intros a1 a2 Hva1 Hva2 O1 O2 r1 r2 d Hd Hext f1 f2 Hspan1 Hspan2.
  pose proof (arc_arc_dist_external a1 a2 Hva1 Hva2 Hext) as
    [_ [_ [Hgap Hlower]]].
  split.
  - exact Hgap.
  - exact Hlower.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions two_circles_dist_lower.
Print Assumptions circle_feet_dist.
Print Assumptions two_circles_dist_radial.
Print Assumptions arc_arc_dist_external.
