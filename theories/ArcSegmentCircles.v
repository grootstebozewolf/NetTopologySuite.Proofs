(* ============================================================================
   NetTopologySuite.Proofs.ArcSegmentCircles
   ----------------------------------------------------------------------------
   Issue #64 ask #5b / #224 W1 / JTS curve-awareness N-AL: ARC-SEGMENT (line)
   intersection, the circle-line existence core.  Companion to ArcArcCircles.v
   (N-AA): there the second primitive was a circle, here it is a line.

   JTS CircularArcs.intersectSegment intersects a circular arc with a line
   segment.  The ARC_SEGMENT_XY oracle mode (this PR) enumerates the circle-line
   intersections of an arc's circumcircle: for centre O, radius r and a line of
   unit direction u through its foot F (the nearest point of the line to O),

       perp distance d = |O F|,   half-chord h = sqrt(r^2 - d^2),
       P+- = F +- h*u                          (the two candidate points)

   each kept iff it lies in the arc's sweep AND within the segment (0 <= t <= 1).

   Proved here (all THREE-AXIOM, no atan2/sin_lt_x, no Classic):

     §1  `line_circle_radical_point` — HEADLINE unconditional existence: for a
         line given by its foot F (the perpendicular foot from O, characterised
         by (F - O) . u = 0) and a unit direction u, whenever d^2 <= r^2 the two
         points F +- h*u both lie on the circle (dist_sq O P = r^2).  Pure
         algebra: the foot condition kills the cross term, leaving d^2 + h^2.

     §2  `arc_line_circle_intersect` — arc-level corollary: a line whose
         perpendicular foot is within the arc's circumradius meets the arc's
         circumcircle; the witness X has inCircle_R = 0 (via the merged
         ArcArcCircles.inCircle_R_zero_of_equidistant) and lies on the line.

   DEFERRED (honest scope, matching ArcArcCircles.v):
     - `arc_span_contains` / segment-parameter (0 <= t <= 1) membership for the
       witness: the angular sector test needs atan2 and the clamp is the
       oracle's float layer (exercised by oracle/gen_arc_segment_tests.py).
     - Binary64 soundness of ARC_SEGMENT_XY; sweep >= pi / reflex arcs.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcChordApprox
  ArcArcCircles.
Local Open Scope R_scope.

(* ========================================================================== *)
(* §1  Circle-line intersection: the two foot +- h*u points lie on the circle *)
(*                                                                            *)
(* HEADLINE: for a line through its perpendicular foot F (from centre O) with  *)
(* unit direction u, every point F + t*u has dist_sq O (F + t*u) = d^2 + t^2   *)
(* (the foot condition (F - O).u = 0 removes the 2*t*((F-O).u) cross term).    *)
(* Setting t = +- sqrt(r^2 - d^2) gives the two circle intersections.          *)
(* ========================================================================== *)

Lemma line_circle_radical_point :
  forall (O : Point) (fx fy ux uy r2 : R),
    ux * ux + uy * uy = 1 ->
    ux * (fx - px O) + uy * (fy - py O) = 0 ->
    0 <= r2 - dist_sq O (mkPoint fx fy) ->
    let h := sqrt (r2 - dist_sq O (mkPoint fx fy)) in
    dist_sq O (mkPoint (fx + h * ux) (fy + h * uy)) = r2 /\
    dist_sq O (mkPoint (fx - h * ux) (fy - h * uy)) = r2.
Proof.
  intros O fx fy ux uy r2 Hunit Hperp Hnn.
  cbn zeta.
  set (h := sqrt (r2 - dist_sq O (mkPoint fx fy))).
  assert (Hhh : h * h = r2 - dist_sq O (mkPoint fx fy)).
  { unfold h. apply sqrt_sqrt. exact Hnn. }
  unfold dist_sq in *. cbn [px py] in *.
  split.
  - transitivity
      (((px O - fx) * (px O - fx) + (py O - fy) * (py O - fy))
       + 2 * h * (ux * (fx - px O) + uy * (fy - py O))
       + h * h * (ux * ux + uy * uy)).
    + ring.
    + rewrite Hperp, Hunit. nra.
  - transitivity
      (((px O - fx) * (px O - fx) + (py O - fy) * (py O - fy))
       + (- (2 * h)) * (ux * (fx - px O) + uy * (fy - py O))
       + h * h * (ux * ux + uy * uy)).
    + ring.
    + rewrite Hperp, Hunit. nra.
Qed.

(* ========================================================================== *)
(* §2  Arc-level corollary: a line within the circumradius meets the circle    *)
(*                                                                            *)
(* The witness lies on the arc's CIRCUMCIRCLE (inCircle_R = 0) and on the line.*)
(* `arc_radius_sq a = dist_sq (arc_center a) (arc_start a)`, so the circle      *)
(* membership reuses the merged ArcArcCircles.inCircle_R_zero_of_equidistant.  *)
(*                                                                            *)
(* DEFERRED: arc-sweep membership and the segment clamp 0 <= t <= 1 (atan2 /   *)
(* float oracle layer); this gives the unconditional COORDINATE existence.     *)
(* ========================================================================== *)

Theorem arc_line_circle_intersect :
  forall (a : CircularArc) (fx fy ux uy : R),
    valid_arc a ->
    ux * ux + uy * uy = 1 ->
    ux * (fx - px (arc_center a)) + uy * (fy - py (arc_center a)) = 0 ->
    dist_sq (arc_center a) (mkPoint fx fy) <= arc_radius_sq a ->
    exists X : Point,
      inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 /\
      (exists t : R, px X = fx + t * ux /\ py X = fy + t * uy).
Proof.
  intros a fx fy ux uy Hva Hunit Hperp Hle.
  set (O := arc_center a) in *.
  set (r2 := arc_radius_sq a) in *.
  assert (Hnn : 0 <= r2 - dist_sq O (mkPoint fx fy)) by lra.
  destruct (line_circle_radical_point O fx fy ux uy r2 Hunit Hperp Hnn)
    as [Hplus _].
  set (h := sqrt (r2 - dist_sq O (mkPoint fx fy))) in *.
  exists (mkPoint (fx + h * ux) (fy + h * uy)).
  split.
  - apply inCircle_R_zero_of_equidistant; [exact Hva |].
    (* dist_sq O X = r2 = arc_radius_sq a = dist_sq O (arc_start a) *)
    change (dist_sq O (mkPoint (fx + h * ux) (fy + h * uy))
            = dist_sq (arc_center a) (arc_start a)).
    rewrite Hplus. unfold r2, arc_radius_sq. reflexivity.
  - exists h. cbn [px py]. split; reflexivity.
Qed.

(* ========================================================================== *)
(* §3  Audit footprint.                                                       *)
(* ========================================================================== *)

Print Assumptions line_circle_radical_point.
Print Assumptions arc_line_circle_intersect.
