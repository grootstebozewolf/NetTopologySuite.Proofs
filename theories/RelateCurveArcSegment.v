(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveArcSegment
   ----------------------------------------------------------------------------
   Issue #67 (curve→matrix soundness): the FIRST arc-bearing outer ring.

   `RelateCurveAreaPointSound.v` closed the curve→matrix membership story for
   the all-chord axis-aligned rectangle and flagged "arc (non-chord) outer
   rings" as the next open frontier.  This file opens it with the simplest
   genuinely-curved closed outer ring — a SQL/MM circular SEGMENT (a "lens"):
   one `CSArc` followed by the closing `CSChord` back to its start.

     arc_seg_curve_ring a := [ CSArc a ; CSChord (arc_end a) (arc_start a) ].

   The key structural fact that makes this tractable WITHOUT the (quarantined)
   unconditional arc-span soundness: `chord_approx_arc a n = [arc_start a;
   arc_mid a; arc_end a]` for every `n` (CurveLinearise.chord_approx_segment_shape),
   so the whole linearised ring is the fixed 5-point polyline

     [arc_start a; arc_mid a; arc_end a; arc_end a; arc_start a],

   carrying exactly one degenerate `(arc_end, arc_end)` join edge.  Stripping it
   with `RayParityDegenerate.ray_parity_zero_edge_irrelevant` — the same
   technique `point_in_ring_chord_rect_iff` used for the rectangle's three join
   edges — reduces the arc-segment ring's point-in-ring to that of the explicit
   Phase-3 CONTROL TRIANGLE `[arc_start a; arc_mid a; arc_end a; arc_start a]`.
   This is the arc analogue of `point_in_ring_chord_rect_iff`, and is likewise
   n-independent (the SQL/MM three-point chord approximation is start–mid–end).

   Deliverables (all `Qed`, three-axiom, no `Admitted`/`Axiom`/`Parameter`):

     1. `valid_arc_seg_curve_ring` — the lens is a `valid_curve_ring` whenever
        the arc is non-degenerate (`valid_arc`).
     2. `arc_seg_linearised_ring_closed` — its chord approximation is a
        `ring_closed` Phase-3 ring (the `valid_polygon` prerequisite).
     3. `point_in_ring_arc_seg_iff` — the headline reduction: the linearised
        arc-segment ring ≡ the control triangle on point-in-ring.
     4. `point_in_arc_seg_curve_{polygon,geometry}_iff_triangle` — transported
        through the S12b-style point-set bridge to the curve polygon and the
        curve geometry's point set, unchanged.

   Honest scope: a single arc + closing chord, no holes.  The membership of the
   control triangle itself (Contains/Touches/Disjoint via the triangle JCT
   family) and arc rings of more than one arc remain downstream; this file
   lands the arc-ring→inscribed-polygon REDUCTION those build on.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay CurveGeometry CurveLinearise
  RelateCurveAreaPoint RayParityDegenerate.
From NTS.Proofs Require Import CurveRingOffset BufferOffset ArcOffsetThreePoint.
From NTS.Proofs Require Import PointInRingCorrect JordanCurveSeam
  GeneralTriangleSeparation GeneralTriangleJCT.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The circular-segment ("lens") curve ring: one arc + its closing chord. *)
(* -------------------------------------------------------------------------- *)

Definition arc_seg_curve_ring (a : CircularArc) : CurveRing :=
  [ CSArc a ; CSChord (arc_end a) (arc_start a) ].

Definition arc_seg_curve_polygon (a : CircularArc) : CurvePolygon :=
  {| curve_outer := arc_seg_curve_ring a; curve_holes := [] |}.

Definition arc_seg_curve_geometry (a : CircularArc) : CurveGeometry :=
  [ arc_seg_curve_polygon a ].

(* -------------------------------------------------------------------------- *)
(* §2  Structural validity (conditional on the arc being non-degenerate).      *)
(*                                                                            *)
(* Adjacency and closedness are definitional for the two-segment lens; the     *)
(* only genuine content is the per-arc `valid_arc` hypothesis.                 *)
(* -------------------------------------------------------------------------- *)

Lemma arc_seg_curve_ring_arcs_valid :
  forall a, valid_arc a -> curve_ring_arcs_valid (arc_seg_curve_ring a).
Proof.
  intros a Ha. unfold curve_ring_arcs_valid, arc_seg_curve_ring.
  repeat constructor. exact Ha.
Qed.

Lemma arc_seg_curve_ring_adjacent :
  forall a, curve_ring_adjacent (arc_seg_curve_ring a).
Proof.
  intros a. unfold curve_ring_adjacent, arc_seg_curve_ring,
    curve_segment_end, curve_segment_start. split; reflexivity.
Qed.

Lemma arc_seg_curve_ring_closed :
  forall a, curve_ring_closed (arc_seg_curve_ring a).
Proof.
  intros a. unfold curve_ring_closed, arc_seg_curve_ring,
    curve_segment_end, curve_segment_start. reflexivity.
Qed.

Lemma valid_arc_seg_curve_ring :
  forall a, valid_arc a -> valid_curve_ring (arc_seg_curve_ring a).
Proof.
  intros a Ha. unfold valid_curve_ring.
  split; [ exact (arc_seg_curve_ring_arcs_valid a Ha) | ].
  split; [ exact (arc_seg_curve_ring_adjacent a)
         | exact (arc_seg_curve_ring_closed a) ].
Qed.

(* The linearised lens is a closed Phase-3 ring (the `valid_polygon`
   prerequisite for plugging it into the overlay / relate machinery). *)
Lemma arc_seg_linearised_ring_closed :
  forall a n,
    ring_closed (chord_approx_ring (arc_seg_curve_ring a) n).
Proof.
  intros a n. apply chord_approx_ring_closed.
  exact (arc_seg_curve_ring_closed a).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The reduction: arc-segment ring ≡ control triangle on point-in-ring.    *)
(*                                                                            *)
(* The chord approximation is the fixed 5-point polyline                       *)
(*   [start; mid; end; end; start]                                            *)
(* (the SQL/MM start–mid–end arc approximation followed by the closing chord). *)
(* Its `ring_edges` carry one degenerate `(end,end)` join edge; strip it.      *)
(* -------------------------------------------------------------------------- *)

(* `ring_edges` of the linearised lens, computed (n-independent). *)
Lemma ring_edges_arc_seg :
  forall a n,
    ring_edges (chord_approx_ring (arc_seg_curve_ring a) n)
    = [ (arc_start a, arc_mid a)
      ; (arc_mid a,   arc_end a)
      ; (arc_end a,   arc_end a)
      ; (arc_end a,   arc_start a) ].
Proof. reflexivity. Qed.

(* `ring_edges` of the explicit control triangle. *)
Lemma ring_edges_control_triangle :
  forall a,
    ring_edges [arc_start a; arc_mid a; arc_end a; arc_start a]
    = [ (arc_start a, arc_mid a)
      ; (arc_mid a,   arc_end a)
      ; (arc_end a,   arc_start a) ].
Proof. reflexivity. Qed.

Theorem point_in_ring_arc_seg_iff :
  forall a n p,
    point_in_ring p (chord_approx_ring (arc_seg_curve_ring a) n)
    <-> point_in_ring p [arc_start a; arc_mid a; arc_end a; arc_start a].
Proof.
  intros a n p. unfold point_in_ring.
  rewrite (ring_edges_arc_seg a n), (ring_edges_control_triangle a).
  (* strip the single degenerate (arc_end, arc_end) join edge *)
  exact (proj1 (ray_parity_zero_edge_irrelevant p (arc_end a)
            [ (arc_start a, arc_mid a); (arc_mid a, arc_end a) ]
            [ (arc_end a, arc_start a) ])).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Transport to the curve polygon and the curve geometry's point set.      *)
(* -------------------------------------------------------------------------- *)

Definition point_in_arc_seg_curve_polygon (a : CircularArc) (n : nat) (p : Point) : Prop :=
  point_in_polygon p
    (mkPolygon (chord_approx_ring (arc_seg_curve_ring a) n) []).

Definition point_in_arc_seg_curve_geometry (a : CircularArc) (n : nat) (p : Point) : Prop :=
  point_set (to_geometry (arc_seg_curve_geometry a) n) p.

Theorem point_in_arc_seg_curve_polygon_iff_triangle :
  forall a n p,
    point_in_arc_seg_curve_polygon a n p
    <-> point_in_ring p [arc_start a; arc_mid a; arc_end a; arc_start a].
Proof.
  intros a n p.
  unfold point_in_arc_seg_curve_polygon, point_in_polygon. simpl.
  rewrite (point_in_ring_arc_seg_iff a n p).
  split.
  - intros [H _]. exact H.
  - intro H. split; [ exact H | intros h Hin; destruct Hin ].
Qed.

(* S12b-style point-set bridge: the curve geometry is the singleton linearised
   polygon, so `point_set` over it is `point_in_polygon` on that sole element. *)
Lemma point_in_arc_seg_curve_geometry_iff_polygon :
  forall a n p,
    point_in_arc_seg_curve_geometry a n p
    <-> point_in_arc_seg_curve_polygon a n p.
Proof.
  intros a n p.
  unfold point_in_arc_seg_curve_geometry, point_in_arc_seg_curve_polygon,
         point_set, to_geometry, arc_seg_curve_geometry, arc_seg_curve_polygon.
  cbn [map curve_outer curve_holes].
  split.
  - intros [poly [Hin Hpip]]. cbn [In] in Hin.
    destruct Hin as [Heq | Hfalse]; [ subst poly; exact Hpip | contradiction ].
  - intros Hpip.
    exists (mkPolygon (chord_approx_ring (arc_seg_curve_ring a) n) []).
    cbn [In]. split; [ left; reflexivity | exact Hpip ].
Qed.

Theorem point_in_arc_seg_curve_geometry_iff_triangle :
  forall a n p,
    point_in_arc_seg_curve_geometry a n p
    <-> point_in_ring p [arc_start a; arc_mid a; arc_end a; arc_start a].
Proof.
  intros a n p.
  rewrite (point_in_arc_seg_curve_geometry_iff_polygon a n p).
  exact (point_in_arc_seg_curve_polygon_iff_triangle a n p).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Contains: a guarded control-triangle interior point is in the lens.     *)
(*                                                                            *)
(* The control triangle of §3 is exactly `GeneralTriangleSeparation.gtri_ring` *)
(* on the arc's three control points, so the general-triangle JCT layer        *)
(* (`GeneralTriangleJCT`) applies verbatim.  `gtri_interior_in_ring` needs NO   *)
(* orientation hypothesis — `0 < gtri p` itself forces CCW — and the rightward- *)
(* ray genericity guard `ray_avoids_vertices` rules out the middle-vertex graze *)
(* (JCT_VertexGrazingCounterexample).  Composing it with the §4 transport lands *)
(* the first genuine Contains direction for an arc-bearing curve geometry.      *)
(* -------------------------------------------------------------------------- *)

(* The §3 control triangle IS `gtri_ring` on the arc control points. *)
Lemma gtri_ring_arc_control :
  forall a,
    gtri_ring (px (arc_start a)) (py (arc_start a))
              (px (arc_mid a))   (py (arc_mid a))
              (px (arc_end a))   (py (arc_end a))
    = [arc_start a; arc_mid a; arc_end a; arc_start a].
Proof.
  intros a. unfold gtri_ring.
  destruct (arc_start a), (arc_mid a), (arc_end a). reflexivity.
Qed.

(* Contains: an interior-side (`0 < gtri`) point of the control triangle, under
   the ray-genericity guard, lies in the arc-segment curve geometry. *)
Theorem arc_seg_control_interior_in_curve_geometry :
  forall a n p,
    0 < gtri (px (arc_start a)) (py (arc_start a))
             (px (arc_mid a))   (py (arc_mid a))
             (px (arc_end a))   (py (arc_end a)) p ->
    ray_avoids_vertices p
      (gtri_ring (px (arc_start a)) (py (arc_start a))
                 (px (arc_mid a))   (py (arc_mid a))
                 (px (arc_end a))   (py (arc_end a))) ->
    point_in_arc_seg_curve_geometry a n p.
Proof.
  intros a n p Hpos Hrav.
  apply (proj2 (point_in_arc_seg_curve_geometry_iff_triangle a n p)).
  rewrite <- (gtri_ring_arc_control a).
  apply gtri_interior_in_ring; [ exact Hpos | exact Hrav ].
Qed.

(* The full parity ↔ continuous-interior characterisation transported to the
   lens: for guarded control-triangle interior points, membership in the curve
   geometry IS the continuous geometric interior of the control triangle — the
   arc analogue of the rectangle/right-triangle H1 instances. *)
Theorem point_in_arc_seg_curve_geometry_iff_control_interior :
  forall a n p,
    0 < gtri (px (arc_start a)) (py (arc_start a))
             (px (arc_mid a))   (py (arc_mid a))
             (px (arc_end a))   (py (arc_end a)) p ->
    ray_avoids_vertices p
      (gtri_ring (px (arc_start a)) (py (arc_start a))
                 (px (arc_mid a))   (py (arc_mid a))
                 (px (arc_end a))   (py (arc_end a))) ->
    (point_in_arc_seg_curve_geometry a n p
     <-> geometric_interior_cont p
           (gtri_ring (px (arc_start a)) (py (arc_start a))
                      (px (arc_mid a))   (py (arc_mid a))
                      (px (arc_end a))   (py (arc_end a)))).
Proof.
  intros a n p Hpos Hrav.
  rewrite (point_in_arc_seg_curve_geometry_iff_triangle a n p).
  rewrite <- (gtri_ring_arc_control a).
  exact (general_triangle_parity_characterises_interior
           _ _ _ _ _ _ p Hpos Hrav).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions valid_arc_seg_curve_ring.
Print Assumptions arc_seg_linearised_ring_closed.
Print Assumptions point_in_ring_arc_seg_iff.
Print Assumptions point_in_arc_seg_curve_polygon_iff_triangle.
Print Assumptions point_in_arc_seg_curve_geometry_iff_triangle.
Print Assumptions arc_seg_control_interior_in_curve_geometry.
Print Assumptions point_in_arc_seg_curve_geometry_iff_control_interior.

(* -------------------------------------------------------------------------- *)
(* ARC_BUFFER_SIMPLE: single arc (as arc+chord lens) → CurvePolygon or degen. *)
(*                                                                            *)
(* BUF-1 cheap lane exercised by the oracle via BUFFER_REGION on the 2-seg    *)
(* "degenerate ring" [CSArc a; CSChord end start].  For d=0 recovers the lens; *)
(* outward yields expanded CurvePolygon (offset arc + round/connector pieces); *)
(* inward may hit DEGENERATE (partial collapse) or EMPTY (r+d <= 0).           *)
(* -------------------------------------------------------------------------- *)

Definition arc_buffer_simple (a : CircularArc) (d : R) : CurvePolygon :=
  {| curve_outer := curve_ring_offset (arc_seg_curve_ring a) d;
     curve_holes := [] |}.

Lemma arc_buffer_simple_first_segment_is_offset :
  forall a d,
    hd_error (curve_ring_offset (arc_seg_curve_ring a) d)
    = Some (CSArc (arc_offset_arc a d)).
Proof.
  intros a d.
  unfold arc_seg_curve_ring, curve_ring_offset.
  reflexivity.
Qed.

Lemma arc_buffer_simple_d0_is_identity :
  forall a : CircularArc,
    arc_buffer_simple a 0 = arc_seg_curve_polygon a.
Proof.
  intros a.
  unfold arc_buffer_simple, arc_seg_curve_polygon.
  f_equal.
  unfold curve_ring_offset, arc_seg_curve_ring.
  simpl.
  (* chord parts at d=0 are identity *)
  assert (Hch1 : offset_point (arc_end a) (arc_start a) (arc_end a) 0 = arc_end a).
  { unfold offset_point, pt_translate, offset_normal, seg_vec.
    simpl. ring. }
  assert (Hch2 : offset_point (arc_end a) (arc_start a) (arc_start a) 0 = arc_start a).
  { unfold offset_point, pt_translate, offset_normal, seg_vec.
    simpl. ring. }
  rewrite Hch1, Hch2.
  (* arc at d=0 is identity: k=1, homothety C 1 P = P *)
  assert (Har : arc_offset_arc a 0 = a).
  { unfold arc_offset_arc, radial_offset, homothety.
    unfold arc_start, arc_mid, arc_end, mkCircularArc.
    (* (r+0)/r = 1 , so C + 1*(P-C) = P for each control *)
    destruct a as [s m e]; simpl.
    unfold pt_translate; simpl.
    f_equal; ring. }
  rewrite Har.
  reflexivity.
Qed.

Lemma arc_offset_arc_radius :
  forall a d,
    valid_arc a ->
    arc_radius (arc_offset_arc a d) = Rabs (arc_radius a + d).
Proof.
  intros a d Hva.
  pose proof (arc_radius_pos a Hva) as Hr.
  pose proof (arc_center_equidistant_offset a d Hva) as Heq.
  unfold arc_radius, dist, arc_offset_arc in *.
  simpl.
  assert (Hdist : dist (arc_center a) (arc_start (arc_offset_arc a d)) = Rabs (arc_radius a + d)).
  { apply radial_offset_center_dist.
    - exact Hr.
    - apply arc_center_equidistant; assumption.
  }
  rewrite Hdist.
  reflexivity.
Qed.

Lemma arc_buffer_simple_unsafe_radius :
  forall a d,
    valid_arc a ->
    arc_radius a + d <= 0 ->
    arc_radius (arc_offset_arc a d) = - (arc_radius a + d).
Proof.
  intros a d Hva Hle.
  rewrite arc_offset_arc_radius by assumption.
  apply Rabs_left1.
  lra.
Qed.

Lemma arc_buffer_simple_valid_when_safe :
  forall a d,
    valid_arc a ->
    ring_offset_safe (arc_seg_curve_ring a) d ->
    valid_curve_polygon (arc_buffer_simple a d).
Proof.
  intros a d Hva Hsafe.
  unfold arc_buffer_simple, valid_curve_polygon; simpl.
  split.
  - apply curve_ring_offset_valid.
    + apply valid_arc_seg_curve_ring; exact Hva.
    + exact (valid_arc_seg_curve_ring a Hva).
    + exact Hsafe.
  - constructor.
Qed.

(* When the per-arc safety fails (r + d <= 0 for the lens arc), construction   *)
(* yields a "polygon" whose arc has non-positive radius; oracle treats as      *)
(* EMPTY / DEGENERATE depending on exact collapse.  We record the radius fact. *)
(* Note: degen/EMPTY decision is by the caller using ring_offset_safe (or the   *)
(* per-arc r+d <=0 test); the polygon is always built; unsafe cases produce    *)
(* polygons containing invalid (radius <=0) arcs, which higher layers treat as *)
(* degenerate/empty rather than emitting.  The area companion (CurveBufferArea) *)
(* already records the per-arc safety + growth.                                 *)

Print Assumptions arc_buffer_simple_valid_when_safe.
Print Assumptions arc_buffer_simple_first_segment_is_offset.
