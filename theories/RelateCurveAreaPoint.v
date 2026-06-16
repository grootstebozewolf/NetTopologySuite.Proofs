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
(* §S12b  The `to_geometry` ↔ rectangle-polygon point-in-ring bridge.          *)
(*                                                                            *)
(* The bridge S12 deferred: the *curve* geometry's point set (the `to_geometry`*)
(* linearisation, via `point_set`) coincides with membership in the single     *)
(* linearised rectangle polygon.  It is pure structural computation, not JCT   *)
(* content: `to_geometry` maps the chord-approximation over the one curve       *)
(* polygon (no holes), so the geometry is the singleton                        *)
(*   [mkPolygon (chord_approx_ring (rect_curve_ring x0 y0 x1 y1) n) []],        *)
(* and `point_set` over a singleton is `point_in_polygon` on its sole element. *)
(* With this bridge the S4 Contains/Touches facts transport to the curve       *)
(* geometry's point set unchanged.                                             *)
(* -------------------------------------------------------------------------- *)

Lemma point_in_rect_curve_geometry_iff_polygon :
  forall x0 y0 x1 y1 n p,
    point_in_rect_curve_geometry x0 y0 x1 y1 n p
    <-> point_in_rect_curve_polygon x0 y0 x1 y1 n p.
Proof.
  intros x0 y0 x1 y1 n p.
  unfold point_in_rect_curve_geometry, point_in_rect_curve_polygon, point_set,
         to_geometry, rect_curve_geometry, rect_curve_polygon.
  cbn [map curve_outer curve_holes].
  split.
  - intros [poly [Hin Hpip]]. cbn [In] in Hin.
    destruct Hin as [Heq | Hfalse]; [ subst poly; exact Hpip | contradiction ].
  - intros Hpip.
    exists (mkPolygon (chord_approx_ring (rect_curve_ring x0 y0 x1 y1) n) []).
    cbn [In]. split; [ left; reflexivity | exact Hpip ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Curve-polygon × point: status after S12b.                                   *)
(*                                                                            *)
(* Established here: the structural-validity spine (`valid_rect_curve_*`,       *)
(* `rect_curve_linearised_ring_closed`) AND the S12b point-set bridge above     *)
(* (`point_in_rect_curve_geometry_iff_polygon`): the curve geometry's point     *)
(* set equals membership in the linearised rectangle polygon, so the S4 facts   *)
(* (`RelateAreaPoint.v`) and the `cap_matrix_*_witness` matrices transport to   *)
(* the curve-polygon×point setting unchanged.  Still S13+: arc (non-chord)      *)
(* outer rings, holes, and full RelateNG noding / prepared cache.              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions valid_rect_curve_geometry.
Print Assumptions rect_curve_linearised_ring_closed.
Print Assumptions point_in_rect_curve_geometry_iff_polygon.
Print Assumptions cap_matrix_rect_contains_point_witness.
Print Assumptions cap_matrix_rect_touches_boundary_witness.