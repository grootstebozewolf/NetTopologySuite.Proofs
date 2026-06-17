(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveVesica
   ----------------------------------------------------------------------------
   Issue #67 (curve→matrix soundness): the ALL-ARC outer ring (a CIRCULARSTRING).

   `RelateCurveArcSegment.v` opened the arc-bearing-outer-ring frontier with a
   single arc closed by a straight chord (a circular segment / "lens").  This
   file takes the next rung — a closed outer ring made of TWO arcs and NO chords
   at all: a SQL/MM CIRCULARSTRING, the "vesica" bounded by two circular arcs
   sharing both endpoints.

     vesica_curve_ring a b := [ CSArc a ; CSArc b ]
       with  arc_end a = arc_start b   (adjacency)
       and   arc_end b = arc_start a   (closure).

   The same n-independent linearisation (`chord_approx_arc a n =
   [arc_start a; arc_mid a; arc_end a]`) flattens the ring to the 6-point
   polyline

     [arc_start a; arc_mid a; arc_end a; arc_start b; arc_mid b; arc_end b],

   which — after substituting the adjacency/closure identities — carries exactly
   one degenerate `(arc_end a, arc_end a)` join edge.  Stripping it with
   `RayParityDegenerate.ray_parity_zero_edge_irrelevant` (the same technique as
   the rectangle and the lens) reduces the vesica ring's point-in-ring to that
   of the explicit CONTROL QUADRILATERAL

     [arc_start a; arc_mid a; arc_end a; arc_mid b; arc_start a].

   Deliverables (all `Qed`, no `Admitted`/`Axiom`/`Parameter`; the reduction is
   ZERO-axiom — only `RayParityDegenerate` + list computation):

     1. `valid_vesica_curve_ring`     — a `valid_curve_ring` under the two arc
        validities and the adjacency/closure identities.
     2. `vesica_linearised_ring_closed` — its chord approximation is a
        `ring_closed` Phase-3 ring.
     3. `point_in_ring_vesica_iff`    — the headline reduction: the linearised
        vesica ring ≡ the control quadrilateral on point-in-ring.
     4. `point_in_vesica_curve_{polygon,geometry}_iff_quad` — transported
        through the S12b-style point-set bridge to the curve polygon and the
        curve geometry's point set, unchanged.

   This carries the curve→matrix reduction technique from the one-arc lens to
   the all-arc CIRCULARSTRING (and, with one more join strip per extra segment,
   to any compound ring).  Membership of the control quadrilateral itself
   (convex-quad JCT) is downstream.

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
(* §1  The vesica curve ring: two arcs, no chords (a CIRCULARSTRING).          *)
(* -------------------------------------------------------------------------- *)

Definition vesica_curve_ring (a b : CircularArc) : CurveRing :=
  [ CSArc a ; CSArc b ].

Definition vesica_curve_polygon (a b : CircularArc) : CurvePolygon :=
  {| curve_outer := vesica_curve_ring a b; curve_holes := [] |}.

Definition vesica_curve_geometry (a b : CircularArc) : CurveGeometry :=
  [ vesica_curve_polygon a b ].

(* -------------------------------------------------------------------------- *)
(* §2  Structural validity.                                                    *)
(* -------------------------------------------------------------------------- *)

Lemma vesica_curve_ring_arcs_valid :
  forall a b, valid_arc a -> valid_arc b ->
    curve_ring_arcs_valid (vesica_curve_ring a b).
Proof.
  intros a b Ha Hb. unfold curve_ring_arcs_valid, vesica_curve_ring.
  apply Forall_cons; [ exact Ha | ].
  apply Forall_cons; [ exact Hb | ].
  apply Forall_nil.
Qed.

Lemma vesica_curve_ring_adjacent :
  forall a b, arc_end a = arc_start b ->
    curve_ring_adjacent (vesica_curve_ring a b).
Proof.
  intros a b Hadj. unfold curve_ring_adjacent, vesica_curve_ring,
    curve_segment_end, curve_segment_start. split; [ exact Hadj | exact I ].
Qed.

Lemma vesica_curve_ring_closed :
  forall a b, arc_end b = arc_start a ->
    curve_ring_closed (vesica_curve_ring a b).
Proof.
  intros a b Hcl. unfold curve_ring_closed, vesica_curve_ring,
    curve_segment_end, curve_segment_start. exact Hcl.
Qed.

Lemma valid_vesica_curve_ring :
  forall a b,
    valid_arc a -> valid_arc b ->
    arc_end a = arc_start b -> arc_end b = arc_start a ->
    valid_curve_ring (vesica_curve_ring a b).
Proof.
  intros a b Ha Hb Hadj Hcl. unfold valid_curve_ring.
  split; [ exact (vesica_curve_ring_arcs_valid a b Ha Hb) | ].
  split; [ exact (vesica_curve_ring_adjacent a b Hadj)
         | exact (vesica_curve_ring_closed a b Hcl) ].
Qed.

Lemma vesica_linearised_ring_closed :
  forall a b n,
    arc_end b = arc_start a ->
    ring_closed (chord_approx_ring (vesica_curve_ring a b) n).
Proof.
  intros a b n Hcl. apply chord_approx_ring_closed.
  exact (vesica_curve_ring_closed a b Hcl).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The reduction: vesica ring ≡ control quadrilateral on point-in-ring.    *)
(*                                                                            *)
(* The linearisation is the fixed 6-point polyline                             *)
(*   [start_a; mid_a; end_a; start_b; mid_b; end_b];                          *)
(* substituting `end_a = start_b` (adjacency) makes the middle join a          *)
(* degenerate `(end_a, end_a)` edge, and `end_b = start_a` (closure) closes    *)
(* the polyline.  Strip the one degenerate edge.                               *)
(* -------------------------------------------------------------------------- *)

Theorem point_in_ring_vesica_iff :
  forall a b n p,
    arc_end a = arc_start b ->
    arc_end b = arc_start a ->
    point_in_ring p (chord_approx_ring (vesica_curve_ring a b) n)
    <-> point_in_ring p [arc_start a; arc_mid a; arc_end a; arc_mid b; arc_start a].
Proof.
  intros a b n p Hadj Hcl. unfold point_in_ring.
  (* compute ring_edges of the 6-point linearisation *)
  replace (ring_edges (chord_approx_ring (vesica_curve_ring a b) n))
    with [ (arc_start a, arc_mid a)
         ; (arc_mid a,   arc_end a)
         ; (arc_end a,   arc_start b)
         ; (arc_start b, arc_mid b)
         ; (arc_mid b,   arc_end b) ] by reflexivity.
  rewrite <- Hadj.   (* arc_start b -> arc_end a *)
  rewrite Hcl.       (* arc_end b   -> arc_start a *)
  (* ring_edges of the explicit control quadrilateral *)
  replace (ring_edges [arc_start a; arc_mid a; arc_end a; arc_mid b; arc_start a])
    with [ (arc_start a, arc_mid a)
         ; (arc_mid a,   arc_end a)
         ; (arc_end a,   arc_mid b)
         ; (arc_mid b,   arc_start a) ] by reflexivity.
  (* strip the single degenerate (arc_end a, arc_end a) join edge *)
  exact (proj1 (ray_parity_zero_edge_irrelevant p (arc_end a)
            [ (arc_start a, arc_mid a); (arc_mid a, arc_end a) ]
            [ (arc_end a, arc_mid b); (arc_mid b, arc_start a) ])).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Transport to the curve polygon and the curve geometry's point set.      *)
(* -------------------------------------------------------------------------- *)

Definition point_in_vesica_curve_polygon (a b : CircularArc) (n : nat) (p : Point) : Prop :=
  point_in_polygon p
    (mkPolygon (chord_approx_ring (vesica_curve_ring a b) n) []).

Definition point_in_vesica_curve_geometry (a b : CircularArc) (n : nat) (p : Point) : Prop :=
  point_set (to_geometry (vesica_curve_geometry a b) n) p.

Theorem point_in_vesica_curve_polygon_iff_quad :
  forall a b n p,
    arc_end a = arc_start b ->
    arc_end b = arc_start a ->
    point_in_vesica_curve_polygon a b n p
    <-> point_in_ring p [arc_start a; arc_mid a; arc_end a; arc_mid b; arc_start a].
Proof.
  intros a b n p Hadj Hcl.
  unfold point_in_vesica_curve_polygon, point_in_polygon. simpl.
  rewrite (point_in_ring_vesica_iff a b n p Hadj Hcl).
  split.
  - intros [H _]. exact H.
  - intro H. split; [ exact H | intros h Hin; destruct Hin ].
Qed.

(* S12b-style point-set bridge: singleton linearised polygon, no holes. *)
Lemma point_in_vesica_curve_geometry_iff_polygon :
  forall a b n p,
    point_in_vesica_curve_geometry a b n p
    <-> point_in_vesica_curve_polygon a b n p.
Proof.
  intros a b n p.
  unfold point_in_vesica_curve_geometry, point_in_vesica_curve_polygon,
         point_set, to_geometry, vesica_curve_geometry, vesica_curve_polygon.
  cbn [map curve_outer curve_holes].
  split.
  - intros [poly [Hin Hpip]]. cbn [In] in Hin.
    destruct Hin as [Heq | Hfalse]; [ subst poly; exact Hpip | contradiction ].
  - intros Hpip.
    exists (mkPolygon (chord_approx_ring (vesica_curve_ring a b) n) []).
    cbn [In]. split; [ left; reflexivity | exact Hpip ].
Qed.

Theorem point_in_vesica_curve_geometry_iff_quad :
  forall a b n p,
    arc_end a = arc_start b ->
    arc_end b = arc_start a ->
    point_in_vesica_curve_geometry a b n p
    <-> point_in_ring p [arc_start a; arc_mid a; arc_end a; arc_mid b; arc_start a].
Proof.
  intros a b n p Hadj Hcl.
  rewrite (point_in_vesica_curve_geometry_iff_polygon a b n p).
  exact (point_in_vesica_curve_polygon_iff_quad a b n p Hadj Hcl).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions valid_vesica_curve_ring.
Print Assumptions vesica_linearised_ring_closed.
Print Assumptions point_in_ring_vesica_iff.
Print Assumptions point_in_vesica_curve_geometry_iff_quad.
