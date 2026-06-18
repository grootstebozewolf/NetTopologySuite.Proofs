(* ============================================================================
   NetTopologySuite.Proofs.CurveRingSimple
   ----------------------------------------------------------------------------
   Issue #64 / JTS #1195 §7 V-CS / V-CP: SIMPLE curve rings -- the proof
   companion of the oracle RING_SIMPLE mode.  A `CurveRing` (CurveGeometry.v) is
   a closed list of CurveSegments (chords / circular arcs).  Structural validity
   (`valid_curve_ring`: arcs valid + adjacent + closed) is already proven; this
   file adds the SIMPLICITY layer: no two non-adjacent segments share a point
   (consecutive segments are allowed to meet at their shared connecting vertex,
   the `curve_ring_adjacent` configuration).

   Proved here (all THREE-AXIOM, no atan2/sin_lt_x):

     §1  Membership: `on_curve_segment s X` (X on a chord = `between`; X on an
         arc = on the circumcircle AND in the sweep, `arc_span_contains`).
         `curve_segments_meet s1 s2` := some X lies on both.

     §2  `curve_ring_simple r` : no two non-adjacent ring positions' segments
         meet (positions are adjacent iff consecutive or the closing pair).

     §3  `curve_ring_not_simple_of_witness` (SOUNDNESS, the property the oracle
         relies on): a shared point of two non-adjacent segments witnesses
         ~ curve_ring_simple.  This certifies every NOT_SIMPLE verdict the
         oracle reports from a detected crossing.

     §4  `arc_arc_circle_meet_of_span` : two valid arcs whose circumcircles
         properly intersect (the merged `ArcArcCircles.arc_arc_circles_intersect`
         existence) meet as curve segments, given the honest span bridge (the
         radical point is in both sweeps -- the deferred atan2 fact, named as a
         hypothesis exactly as `ArcArcSound` does).  `adjacent_arcs_meet_at_vertex`
         records the PERMITTED shared-vertex meeting (consecutive arcs).

   DEFERRED (honest scope, as in ArcArcSound/ArcChordSound): the UNCONDITIONAL
   span membership of the radical point (needs atan2 for sweep >= pi); the
   completeness direction (no crossing => simple) is the oracle's all-pairs
   computation, not a theorem here; holes-in-shell / holes-disjoint for full
   CurvePolygon validity (V-CP) is a follow-up.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Segment CurveGeometry ArcOrient
  ArcIntersect ArcArcCircles ArcChordApprox.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Point-on-segment membership and the "two segments meet" relation.       *)
(* -------------------------------------------------------------------------- *)

(* X lies on a circular arc: on its circumcircle (inCircle_R = 0) and in the
   directed sweep (arc_span_contains). *)
Definition on_arc (a : CircularArc) (X : Point) : Prop :=
  inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 /\ arc_span_contains a X.

Definition on_curve_segment (s : CurveSegment) (X : Point) : Prop :=
  match s with
  | CSChord p q => between p q X
  | CSArc a     => on_arc a X
  end.

Definition curve_segments_meet (s1 s2 : CurveSegment) : Prop :=
  exists X : Point, on_curve_segment s1 X /\ on_curve_segment s2 X.

Lemma curve_segments_meet_sym :
  forall s1 s2, curve_segments_meet s1 s2 -> curve_segments_meet s2 s1.
Proof. intros s1 s2 [X [H1 H2]]. exists X. split; assumption. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Simplicity: no two NON-ADJACENT segments meet.                          *)
(*                                                                            *)
(* Positions i, j in a length-n ring are adjacent iff consecutive (S i = j or  *)
(* S j = i) or the closing pair ({i,j} = {0, n-1}).  Consecutive segments      *)
(* legitimately share their connecting vertex (curve_ring_adjacent), so only   *)
(* NON-adjacent pairs must stay disjoint.                                      *)
(* -------------------------------------------------------------------------- *)

Definition ring_adjacent_positions (n i j : nat) : Prop :=
  S i = j \/ S j = i \/ (i = 0%nat /\ j = (n - 1)%nat) \/ (j = 0%nat /\ i = (n - 1)%nat).

Definition curve_ring_simple (r : CurveRing) : Prop :=
  forall (i j : nat) (s1 s2 : CurveSegment),
    nth_error r i = Some s1 ->
    nth_error r j = Some s2 ->
    i <> j ->
    ~ ring_adjacent_positions (length r) i j ->
    ~ curve_segments_meet s1 s2.

(* -------------------------------------------------------------------------- *)
(* §3  Soundness: a non-adjacent crossing witness refutes simplicity.          *)
(*                                                                            *)
(* This is exactly what the oracle's NOT_SIMPLE verdict means: it found two    *)
(* non-adjacent segments sharing a point X.                                    *)
(* -------------------------------------------------------------------------- *)

Theorem curve_ring_not_simple_of_witness :
  forall (r : CurveRing) (i j : nat) (s1 s2 : CurveSegment) (X : Point),
    nth_error r i = Some s1 ->
    nth_error r j = Some s2 ->
    i <> j ->
    ~ ring_adjacent_positions (length r) i j ->
    on_curve_segment s1 X ->
    on_curve_segment s2 X ->
    ~ curve_ring_simple r.
Proof.
  intros r i j s1 s2 X H1 H2 Hij Hnadj Hon1 Hon2 Hsimple.
  apply (Hsimple i j s1 s2 H1 H2 Hij Hnadj).
  exists X. split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Arc-arc crossings: tie to the merged radical-line existence.            *)
(* -------------------------------------------------------------------------- *)

(* Two valid arcs whose circumcircles PROPERLY intersect meet as curve
   segments, GIVEN the honest span bridge (the radical point lies in both
   sweeps).  Composes ArcArcCircles.arc_arc_circles_intersect (the unconditional
   both-circles coordinate existence) with the deferred atan2 sweep fact, named
   as a hypothesis -- the same conditional shape as ArcArcSound. *)
Theorem arc_arc_circle_meet_of_span :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    (forall X : Point,
       inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 ->
       inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0 ->
       arc_span_contains a1 X /\ arc_span_contains a2 X) ->
    curve_segments_meet (CSArc a1) (CSArc a2).
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt Hspan.
  destruct (arc_arc_circles_intersect a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt)
    as [X [HX1 HX2]].
  destruct (Hspan X HX1 HX2) as [Hs1 Hs2].
  exists X. split; unfold on_curve_segment, on_arc; split; assumption.
Qed.

(* The PERMITTED meeting: consecutive arcs sharing a connecting vertex meet
   there (and `ring_adjacent_positions` exempts that pair from simplicity). *)
Theorem adjacent_arcs_meet_at_vertex :
  forall a1 a2 : CircularArc,
    arc_end a1 = arc_start a2 ->
    curve_segments_meet (CSArc a1) (CSArc a2).
Proof.
  intros a1 a2 Hshare.
  exists (arc_end a1). split; unfold on_curve_segment, on_arc.
  - split; [ apply inCircle_R_at_C | right; right; reflexivity ].
  - rewrite Hshare. split; [ apply inCircle_R_at_A | right; left; reflexivity ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions curve_ring_not_simple_of_witness.
Print Assumptions arc_arc_circle_meet_of_span.
Print Assumptions adjacent_arcs_meet_at_vertex.
