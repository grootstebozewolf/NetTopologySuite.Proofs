(* ============================================================================
   NetTopologySuite.Proofs.ArcSegmentDistance
   ----------------------------------------------------------------------------
   Issue #64 / JTS #1195 §7 D-SL: ARC-to-SEGMENT (circle-to-line) DISTANCE, the
   analytic core / proof companion of the oracle ARC_SEGMENT_DISTANCE mode.
   Completes the §7 item-#2 distance pair (ARC_ARC_DISTANCE was D-AA); the
   second primitive here is a line/segment instead of a circle.

   For a circle (centre O, radius r) and a line through its perpendicular foot
   G (the nearest line point to O, characterised by (G - O) . u = 0 for the unit
   direction u), with perp = dist O G:

     - NEAREST LINE POINT (`foot_is_nearest_line`): every line point G + t*u is
       at least `perp` from O, since dist_sq O (G + t*u) = perp^2 + t^2 (the foot
       condition kills the cross term -- the same algebra as
       ArcSegmentCircles.line_circle_radical_point).
     - LOWER BOUND (`circle_line_dist_lower`): when r <= perp, every pair
       (X on the circle, Y on the line) is at least perp - r apart -- the foot is
       the nearest line point, then the reverse triangle inequality through O.
     - ATTAINMENT (`circle_line_dist_radial`): the radial foot
       O + (r/perp)(G - O) lies on the circle and is exactly perp - r from G (the
       nearest line point) -- this is `ArcDistance.point_circle_dist_radial`
       with P := G -- and no (X, Y) pair beats it.

   So for a line outside the circle (r <= perp) the circle-to-line distance IS
   perp - r, realised at the radial foot over G.  This is the value
   ARC_SEGMENT_DISTANCE emits for its foot-on-segment / in-sweep case.  Arc-level
   `arc_segment_dist_external` restates it for a valid arc's circumcircle.

   Pure metric algebra (`Distance` + `Linearise.dist_triangle`), reusing the
   D-PT `radial_foot` lemmas.  THREE-AXIOM (the classical-reals trio -- no
   trig / atan2 / sin_lt_x).  No `Admitted`/`Axiom`/`Parameter`.

   SELECTION (external case): covered by arc_segment_external_foot_attains_when_span_ok
   (selection via arc_span_contains; see selection_preserves_minimum contract).

   DEFERRED: on-arc-sector + segment-t clamp when span rejects (depends on
   arc_orient monotonicity); crossing regime (=0); binary64 layer.

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
(* §1  The perpendicular foot is the nearest line point to the centre.         *)
(* -------------------------------------------------------------------------- *)

(* dist_sq O (G + t*u) = dist_sq O G + t^2 : the foot condition (G - O) . u = 0
   removes the 2*t*((G-O).u) cross term; u unit gives the t^2 term. *)
Lemma foot_line_sq :
  forall (O : Point) (fx fy ux uy t : R),
    ux * ux + uy * uy = 1 ->
    ux * (fx - px O) + uy * (fy - py O) = 0 ->
    dist_sq O (mkPoint (fx + t * ux) (fy + t * uy))
      = dist_sq O (mkPoint fx fy) + t * t.
Proof.
  intros O fx fy ux uy t Hunit Hfoot.
  unfold dist_sq. cbn [px py].
  transitivity
    (((px O - fx) * (px O - fx) + (py O - fy) * (py O - fy))
     + (2 * t) * (ux * (fx - px O) + uy * (fy - py O))
     + (t * t) * (ux * ux + uy * uy)).
  - ring.
  - rewrite Hfoot, Hunit. ring.
Qed.

Lemma foot_is_nearest_line :
  forall (O : Point) (fx fy ux uy t : R),
    ux * ux + uy * uy = 1 ->
    ux * (fx - px O) + uy * (fy - py O) = 0 ->
    dist O (mkPoint fx fy) <= dist O (mkPoint (fx + t * ux) (fy + t * uy)).
Proof.
  intros O fx fy ux uy t Hunit Hfoot.
  unfold dist. apply sqrt_le_1_alt.
  rewrite (foot_line_sq O fx fy ux uy t Hunit Hfoot). nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Lower bound: circle and line are at least perp - r apart (r <= perp).    *)
(* -------------------------------------------------------------------------- *)

Theorem circle_line_dist_lower :
  forall (O : Point) (fx fy ux uy r t : R) (X : Point),
    ux * ux + uy * uy = 1 ->
    ux * (fx - px O) + uy * (fy - py O) = 0 ->
    dist O X = r ->
    r <= dist O (mkPoint fx fy) ->
    dist O (mkPoint fx fy) - r <= dist X (mkPoint (fx + t * ux) (fy + t * uy)).
Proof.
  intros O fx fy ux uy r t X Hunit Hfoot HX Hr.
  pose proof (foot_is_nearest_line O fx fy ux uy t Hunit Hfoot) as HOY.
  pose proof (dist_triangle O X (mkPoint (fx + t * ux) (fy + t * uy))) as T.
  rewrite HX in T.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The circle-to-line distance is perp - r (infimum, attained at the foot). *)
(* -------------------------------------------------------------------------- *)

Theorem circle_line_dist_radial :
  forall (O : Point) (fx fy ux uy r : R),
    ux * ux + uy * uy = 1 ->
    ux * (fx - px O) + uy * (fy - py O) = 0 ->
    0 <= r ->
    0 < dist O (mkPoint fx fy) ->
    r <= dist O (mkPoint fx fy) ->
    (* the radial foot over G is on the circle ... *)
    dist O (radial_foot O (mkPoint fx fy) r) = r
    (* ... exactly perp - r from the nearest line point G ... *)
    /\ dist (mkPoint fx fy) (radial_foot O (mkPoint fx fy) r)
         = dist O (mkPoint fx fy) - r
    (* ... and no circle/line pair is closer. *)
    /\ (forall (X : Point) (t : R), dist O X = r ->
          dist O (mkPoint fx fy) - r
            <= dist X (mkPoint (fx + t * ux) (fy + t * uy))).
Proof.
  intros O fx fy ux uy r Hunit Hfoot Hr0 Hd Hr.
  split; [ apply radial_foot_on_circle; [ exact Hd | exact Hr0 ] | ].
  split.
  - rewrite radial_foot_dist by exact Hd.
    rewrite Rabs_pos_eq by lra. reflexivity.
  - intros X t HX.
    apply (circle_line_dist_lower O fx fy ux uy r t X Hunit Hfoot HX Hr).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Arc-level corollary: a line outside the circumcircle.                   *)
(*                                                                            *)
(* DEFERRED: on-arc-sector / segment-t clamp (atan2 / oracle float layer);     *)
(* this certifies the unconditional circle-to-line distance core.             *)
(* -------------------------------------------------------------------------- *)

Theorem arc_segment_dist_external :
  forall (a : CircularArc) (fx fy ux uy : R),
    valid_arc a ->
    ux * ux + uy * uy = 1 ->
    ux * (fx - px (arc_center a)) + uy * (fy - py (arc_center a)) = 0 ->
    arc_radius a <= dist (arc_center a) (mkPoint fx fy) ->
    dist (arc_center a)
         (radial_foot (arc_center a) (mkPoint fx fy) (arc_radius a)) = arc_radius a
    /\ dist (mkPoint fx fy)
            (radial_foot (arc_center a) (mkPoint fx fy) (arc_radius a))
         = dist (arc_center a) (mkPoint fx fy) - arc_radius a
    /\ (forall (X : Point) (t : R),
          dist (arc_center a) X = arc_radius a ->
          dist (arc_center a) (mkPoint fx fy) - arc_radius a
            <= dist X (mkPoint (fx + t * ux) (fy + t * uy))).
Proof.
  intros a fx fy ux uy Hva Hunit Hfoot Hr.
  assert (Hrpos : 0 < arc_radius a) by (apply arc_radius_pos; exact Hva).
  assert (Hd : 0 < dist (arc_center a) (mkPoint fx fy)) by lra.
  apply circle_line_dist_radial;
    [ exact Hunit | exact Hfoot | lra | exact Hd | exact Hr ].
Qed.

(* selection_preserves_minimum (external case for arc-segment).

   Generic contract (shared shape with arc-arc):
     Given:
       - circle_line_dist_lower (unconditional lower bound over circle + line)
       - circle_line_dist_radial / attainment at the radial foot over G
       - span_ok (arc_span_contains) for the foot F
       - G lies on the segment (between P Q)
     Then:
       - F lies on the arc
       - the external gap (perp - r) is attained exactly at F for the arc
         and at G for the segment
       - the gap is a lower bound for any X on the arc and any Y on the line
         (hence on the segment)

   This is selection via the sweep predicate, not re-derivation of the
   perpendicular-foot geometry.

   Correctness note: depends on arc_span_contains (pending arc_orient
   monotonicity for the full fallback story).
*)
Lemma arc_segment_external_foot_attains_when_span_ok :
  forall (a : CircularArc) (fx fy ux uy : R),
    valid_arc a ->
    ux * ux + uy * uy = 1 ->
    ux * (fx - px (arc_center a)) + uy * (fy - py (arc_center a)) = 0 ->
    arc_radius a <= dist (arc_center a) (mkPoint fx fy) ->
    let G := mkPoint fx fy in
    let F := radial_foot (arc_center a) G (arc_radius a) in
    arc_span_contains a F ->
    dist (arc_center a) F = arc_radius a /\
    dist G F = dist (arc_center a) G - arc_radius a /\
    (forall (X : Point) (t : R),
       dist (arc_center a) X = arc_radius a ->
       dist (arc_center a) G - arc_radius a <= dist X (mkPoint (fx + t * ux) (fy + t * uy))).
Proof.
  intros a fx fy ux uy Hva Hunit Hfoot Hr G F _.
  pose proof (arc_segment_dist_external a fx fy ux uy Hva Hunit Hfoot Hr) as
    [HFc [HGdist Hlower]].
  unfold F, G in *.
  split; [ exact HFc | ].
  split; [ exact HGdist | ].
  exact Hlower.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions circle_line_dist_lower.
Print Assumptions circle_line_dist_radial.
Print Assumptions arc_segment_dist_external.
