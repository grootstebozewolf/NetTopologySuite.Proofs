(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixCurveAreaPoint
   ----------------------------------------------------------------------------
   Issue #67 session 12 (S12): curve-polygon × point regime→witness selection.

   `curve_point_fill` SELECTS (does not compute from geometry) the S12 / S4
   witness matrices for the chord rect curve polygon carrier per
   `CurvePointRegime`.  The `*_fill_witness` facts are constant; the regime
   hypothesis is not consumed, and no geometry→matrix claim is made.

   No `Admitted`, no `Axiom`, no `Parameter`.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance RelateAreaPoint RelateCurveAreaPoint.
Open Scope R_scope.

Inductive CurvePointRegime : Type :=
| CPR_StrictInterior
| CPR_LeftBoundaryTouch.

Definition curve_point_fill (r : CurvePointRegime) : IntersectionMatrix :=
  match r with
  | CPR_StrictInterior    => cap_matrix_rect_contains_point
  | CPR_LeftBoundaryTouch => cap_matrix_rect_touches_boundary
  end.

Lemma curve_point_fill_contains_eq :
  curve_point_fill CPR_StrictInterior = cap_matrix_rect_contains_point.
Proof. reflexivity. Qed.

Lemma curve_point_fill_touch_eq :
  curve_point_fill CPR_LeftBoundaryTouch = cap_matrix_rect_touches_boundary.
Proof. reflexivity. Qed.

Definition classify_curve_point (x0 y0 x1 y1 : R) (p : Point) (n : nat)
    (r : CurvePointRegime) : Prop :=
  match r with
  | CPR_StrictInterior =>
      x0 < x1 /\ y0 < y1 /\
      point_strictly_in_open_rect x0 y0 x1 y1 p
  | CPR_LeftBoundaryTouch =>
      x0 < x1 /\ y0 < y1 /\
      point_on_rect_left_boundary x0 y0 x1 y1 p
  end.

(* Constant witness facts: the selected witness satisfies the regime's
   predicate.  No geometry hypothesis; no geometry→matrix claim. *)
Theorem curve_point_fill_contains_witness :
  im_contains (curve_point_fill CPR_StrictInterior) /\
  predicate_holds RContains (curve_point_fill CPR_StrictInterior).
Proof.
  rewrite curve_point_fill_contains_eq.
  split.
  - exact cap_matrix_rect_contains_point_witness.
  - unfold predicate_holds. exact cap_matrix_rect_contains_point_witness.
Qed.

Theorem curve_point_fill_touch_witness :
  im_touches (curve_point_fill CPR_LeftBoundaryTouch).
Proof.
  rewrite curve_point_fill_touch_eq. exact cap_matrix_rect_touches_boundary_witness.
Qed.

Theorem strict_interior_not_left_boundary_touch :
  forall x0 y0 x1 y1 p,
    point_strictly_in_open_rect x0 y0 x1 y1 p ->
    ~ point_on_rect_left_boundary x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p Hopen [Hx _].
  destruct Hopen as [Hxp _]. lra.
Qed.

Print Assumptions curve_point_fill_contains_witness.
Print Assumptions curve_point_fill_touch_witness.
Print Assumptions strict_interior_not_left_boundary_touch.