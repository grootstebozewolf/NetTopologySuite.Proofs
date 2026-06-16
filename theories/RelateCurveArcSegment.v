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
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions valid_arc_seg_curve_ring.
Print Assumptions arc_seg_linearised_ring_closed.
Print Assumptions point_in_ring_arc_seg_iff.
Print Assumptions point_in_arc_seg_curve_polygon_iff_triangle.
Print Assumptions point_in_arc_seg_curve_geometry_iff_triangle.
