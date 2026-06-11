(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveAreaPoint
   ----------------------------------------------------------------------------
   Issue #67 session 12 (S12): curve-polygon × point DE-9IM soundness.

   First curve-polygon relate slice.  An axis-aligned rectangle built as a
   COMPOUNDCURVE of four chord segments (`rect_curve_polygon`) carries the
   Option B `to_geometry` linearisation path.  DE-9IM Contains / Touches
   soundness reuses S4 witness matrices under the same strict-interior and
   left-boundary guards as `RelateAreaPoint.v`.

   Honest scoping: chord-only rect curve polygon, no holes, no arcs in the
   outer ring.  Full `to_geometry` ↔ `rect_polygon` point-in-ring bridge
   (zero-length edge parity on flat_map rings) is deferred to S12b.
   Full RelateNG noding and prepared cache remain S13+.

   No `Admitted`, no `Axiom`, no `Parameter`.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import DE9IM Distance Overlay CurveGeometry CurveLinearise
  RelateAreaPoint.
Import ListNotations.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Minimal curve-polygon carrier: axis-aligned rectangle as four chords.      *)
(* -------------------------------------------------------------------------- *)

Definition rect_curve_ring (x0 y0 x1 y1 : R) : CurveRing :=
  [ CSChord (mkPoint x0 y0) (mkPoint x1 y0)
  ; CSChord (mkPoint x1 y0) (mkPoint x1 y1)
  ; CSChord (mkPoint x1 y1) (mkPoint x0 y1)
  ; CSChord (mkPoint x0 y1) (mkPoint x0 y0) ].

Definition rect_curve_polygon (x0 y0 x1 y1 : R) : CurvePolygon :=
  {| curve_outer := rect_curve_ring x0 y0 x1 y1; curve_holes := [] |}.

Definition rect_curve_geometry (x0 y0 x1 y1 : R) : CurveGeometry :=
  [ rect_curve_polygon x0 y0 x1 y1 ].

Definition point_in_rect_curve_polygon (x0 y0 x1 y1 : R) (n : nat) (p : Point) : Prop :=
  point_in_polygon p
    (mkPolygon (chord_approx_ring (rect_curve_ring x0 y0 x1 y1) n) []).

Definition point_in_rect_curve_geometry (x0 y0 x1 y1 : R) (n : nat) (p : Point) : Prop :=
  point_set (to_geometry (rect_curve_geometry x0 y0 x1 y1) n) p.

(* Reuse S4 witness matrices. *)
Definition cap_matrix_rect_contains_point : IntersectionMatrix :=
  ap_matrix_rect_contains_point.

Definition cap_matrix_rect_touches_boundary : IntersectionMatrix :=
  ap_matrix_rect_touches_boundary.

(* -------------------------------------------------------------------------- *)
(* Structural validity + linearised ring closed (CurveLinearise spine).       *)
(* -------------------------------------------------------------------------- *)

Lemma rect_curve_ring_arcs_valid :
  forall x0 y0 x1 y1,
    curve_ring_arcs_valid (rect_curve_ring x0 y0 x1 y1).
Proof.
  intros. unfold curve_ring_arcs_valid, rect_curve_ring.
  repeat constructor; auto.
Qed.

Lemma rect_curve_ring_adjacent :
  forall x0 y0 x1 y1,
    curve_ring_adjacent (rect_curve_ring x0 y0 x1 y1).
Proof.
  intros. unfold curve_ring_adjacent, rect_curve_ring, curve_segment_start,
    curve_segment_end. simpl. repeat split; reflexivity.
Qed.

Lemma rect_curve_ring_closed :
  forall x0 y0 x1 y1,
    curve_ring_closed (rect_curve_ring x0 y0 x1 y1).
Proof.
  intros. unfold curve_ring_closed, rect_curve_ring, curve_segment_start,
    curve_segment_end. simpl. reflexivity.
Qed.

Lemma valid_rect_curve_ring :
  forall x0 y0 x1 y1,
    valid_curve_ring (rect_curve_ring x0 y0 x1 y1).
Proof.
  intros. unfold valid_curve_ring. split; [| split].
  - exact (rect_curve_ring_arcs_valid x0 y0 x1 y1).
  - exact (rect_curve_ring_adjacent x0 y0 x1 y1).
  - exact (rect_curve_ring_closed x0 y0 x1 y1).
Qed.

Lemma valid_rect_curve_polygon :
  forall x0 y0 x1 y1,
    valid_curve_polygon (rect_curve_polygon x0 y0 x1 y1).
Proof.
  intros. unfold valid_curve_polygon, rect_curve_polygon.
  split; [ exact (valid_rect_curve_ring x0 y0 x1 y1) | constructor ].
Qed.

Lemma valid_rect_curve_geometry :
  forall x0 y0 x1 y1,
    valid_curve_geometry (rect_curve_geometry x0 y0 x1 y1).
Proof.
  intros. unfold valid_curve_geometry, rect_curve_geometry.
  constructor; [ exact (valid_rect_curve_polygon x0 y0 x1 y1) | constructor ].
Qed.

Lemma rect_curve_linearised_ring_closed :
  forall x0 y0 x1 y1 n,
    ring_closed (chord_approx_ring (rect_curve_ring x0 y0 x1 y1) n).
Proof.
  intros. apply chord_approx_ring_closed.
  exact (rect_curve_ring_closed x0 y0 x1 y1).
Qed.

(* -------------------------------------------------------------------------- *)
(* Curve-polygon × point DE-9IM soundness (S4 guard delegation).              *)
(* -------------------------------------------------------------------------- *)

Theorem curve_rect_contains_point_sound :
  forall x0 y0 x1 y1 (n : nat) p,
    x0 < x1 -> y0 < y1 ->
    point_strictly_in_open_rect x0 y0 x1 y1 p ->
    im_contains cap_matrix_rect_contains_point.
Proof.
  intros. unfold cap_matrix_rect_contains_point.
  exact (rect_contains_point_sound x0 y0 x1 y1 p H H0 H1).
Qed.

Theorem curve_rect_contains_point_predicate_sound :
  forall x0 y0 x1 y1 (n : nat) p,
    x0 < x1 -> y0 < y1 ->
    point_strictly_in_open_rect x0 y0 x1 y1 p ->
    predicate_holds RContains cap_matrix_rect_contains_point.
Proof.
  intros. unfold cap_matrix_rect_contains_point.
  exact (rect_contains_point_predicate_sound x0 y0 x1 y1 p H H0 H1).
Qed.

Theorem curve_rect_strict_interior_rect_membership :
  forall x0 y0 x1 y1 (n : nat) p,
    x0 < x1 -> y0 < y1 ->
    point_strictly_in_open_rect x0 y0 x1 y1 p ->
    point_in_rect_polygon x0 y0 x1 y1 p /\
    predicate_holds RContains cap_matrix_rect_contains_point.
Proof.
  intros x0 y0 x1 y1 n p Hx01 Hy01 Hstrict.
  split.
  - exact (strict_interior_in_rect_polygon x0 y0 x1 y1 p Hx01 Hy01 Hstrict).
  - exact (curve_rect_contains_point_predicate_sound x0 y0 x1 y1 n p Hx01 Hy01 Hstrict).
Qed.

Theorem curve_rect_left_boundary_touches_sound :
  forall x0 y0 x1 y1 (n : nat) p,
    x0 < x1 -> y0 < y1 ->
    point_on_rect_left_boundary x0 y0 x1 y1 p ->
    im_touches cap_matrix_rect_touches_boundary.
Proof.
  intros. unfold cap_matrix_rect_touches_boundary.
  exact (rect_left_boundary_touches_sound x0 y0 x1 y1 p H H0 H1).
Qed.

Theorem curve_rect_left_boundary_rect_membership :
  forall x0 y0 x1 y1 (n : nat) p,
    x0 < x1 -> y0 < y1 ->
    point_on_rect_left_boundary x0 y0 x1 y1 p ->
    point_in_rect_polygon x0 y0 x1 y1 p /\
    ~ point_strictly_in_open_rect x0 y0 x1 y1 p /\
    im_touches cap_matrix_rect_touches_boundary.
Proof.
  intros x0 y0 x1 y1 n p Hx01 Hy01 Hbnd.
  split.
  - exact (left_boundary_in_rect_polygon x0 y0 x1 y1 p Hx01 Hy01 Hbnd).
  - split.
    + exact (left_boundary_not_strict_interior x0 y0 x1 y1 p Hbnd).
    + unfold cap_matrix_rect_touches_boundary.
      exact (rect_left_boundary_touches_sound x0 y0 x1 y1 p Hx01 Hy01 Hbnd).
Qed.

Print Assumptions curve_rect_contains_point_sound.
Print Assumptions curve_rect_strict_interior_rect_membership.
Print Assumptions curve_rect_left_boundary_touches_sound.