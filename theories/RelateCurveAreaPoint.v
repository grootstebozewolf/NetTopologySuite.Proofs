(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveAreaPoint
   ----------------------------------------------------------------------------
   Issue #67 session 12 (S12): curve-polygon × point — validity + S4 witnesses.

   First curve-polygon relate slice.  An axis-aligned rectangle built as a
   COMPOUNDCURVE of four chord segments (`rect_curve_polygon`) carries the
   Option B `to_geometry` linearisation path.  The curve-specific content is
   the structural-validity spine (the chord rectangle is a valid curve polygon
   with a closed linearised ring).  The Contains / Touches witnesses are S4's,
   reused as constant facts.

   Honest scoping: chord-only rect curve polygon, no holes, no arcs in the
   outer ring.  This file does NOT bridge the curve geometry's point set to
   `rect_polygon`, so it makes no curve→matrix soundness claim: the
   `to_geometry` ↔ `rect_polygon` point-in-ring bridge (zero-length edge
   parity on flat_map rings) is deferred to S12b.  Full RelateNG noding and
   prepared cache remain S13+.

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

(* Constant witness facts: the reused S4 matrices satisfy their predicates.
   (No geometry hypothesis; no curve→matrix bridge — see the section comment
   below.) *)
Lemma cap_matrix_rect_contains_point_witness :
  im_contains cap_matrix_rect_contains_point.
Proof.
  unfold cap_matrix_rect_contains_point. exact ap_matrix_rect_contains_point_witness.
Qed.

Lemma cap_matrix_rect_touches_boundary_witness :
  im_touches cap_matrix_rect_touches_boundary.
Proof.
  unfold cap_matrix_rect_touches_boundary. exact ap_matrix_rect_touches_boundary_witness.
Qed.

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
(* Curve-polygon × point: what is and is not established here.                 *)
(*                                                                            *)
(* This file's genuine, curve-specific content is the structural-validity      *)
(* spine above (`valid_rect_curve_*`, `rect_curve_linearised_ring_closed`):    *)
(* the chord-built rectangle is a valid curve polygon whose linearised ring    *)
(* is closed.  The DE-9IM point membership and the Contains/Touches witnesses  *)
(* are exactly S4's (`RelateAreaPoint.v`: `strict_interior_in_rect_polygon`,   *)
(* `left_boundary_in_polygon_not_strict`, and the `cap_matrix_*_witness`       *)
(* facts above).  The missing bridge — that the *curve* geometry's point set   *)
(* (`to_geometry` linearisation) coincides with `rect_polygon`, and hence that *)
(* a witness matrix is the curve-polygon×point true DE-9IM — is deferred to    *)
(* S12b/S13+ and is NOT claimed here.                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions valid_rect_curve_geometry.
Print Assumptions rect_curve_linearised_ring_closed.
Print Assumptions cap_matrix_rect_contains_point_witness.
Print Assumptions cap_matrix_rect_touches_boundary_witness.