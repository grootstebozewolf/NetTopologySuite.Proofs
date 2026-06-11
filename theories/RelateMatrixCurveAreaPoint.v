(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixCurveAreaPoint
   ----------------------------------------------------------------------------
   Issue #67 session 12 (S12): curve-polygon × point matrix fill.

   Seventh computed fill API: `curve_point_fill` reusing S12 / S4 witness
   matrices for the chord rect curve polygon carrier.

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

Theorem curve_point_fill_contains_sound :
  forall x0 y0 x1 y1 (n : nat) p,
    point_strictly_in_open_rect x0 y0 x1 y1 p ->
    x0 < x1 -> y0 < y1 ->
    im_contains (curve_point_fill CPR_StrictInterior) /\
    predicate_holds RContains (curve_point_fill CPR_StrictInterior).
Proof.
  intros x0 y0 x1 y1 n p Hstrict Hx01 Hy01.
  rewrite curve_point_fill_contains_eq.
  split.
  - exact (curve_rect_contains_point_sound x0 y0 x1 y1 n p Hx01 Hy01 Hstrict).
  - exact (curve_rect_contains_point_predicate_sound x0 y0 x1 y1 n p Hx01 Hy01 Hstrict).
Qed.

Theorem curve_point_fill_touch_sound :
  forall x0 y0 x1 y1 (n : nat) p,
    point_on_rect_left_boundary x0 y0 x1 y1 p ->
    x0 < x1 -> y0 < y1 ->
    im_touches (curve_point_fill CPR_LeftBoundaryTouch).
Proof.
  intros x0 y0 x1 y1 n p Hbnd Hx01 Hy01.
  rewrite curve_point_fill_touch_eq.
  exact (curve_rect_left_boundary_touches_sound x0 y0 x1 y1 n p Hx01 Hy01 Hbnd).
Qed.

Theorem classify_curve_point_contains_fill_sound :
  forall x0 y0 x1 y1 (n : nat) p,
    classify_curve_point x0 y0 x1 y1 p n CPR_StrictInterior ->
    im_contains (curve_point_fill CPR_StrictInterior) /\
    predicate_holds RContains (curve_point_fill CPR_StrictInterior).
Proof.
  intros x0 y0 x1 y1 n p [Hx01 [Hy01 Hstrict]].
  exact (curve_point_fill_contains_sound x0 y0 x1 y1 n p Hstrict Hx01 Hy01).
Qed.

Theorem classify_curve_point_touch_fill_sound :
  forall x0 y0 x1 y1 (n : nat) p,
    classify_curve_point x0 y0 x1 y1 p n CPR_LeftBoundaryTouch ->
    im_touches (curve_point_fill CPR_LeftBoundaryTouch).
Proof.
  intros x0 y0 x1 y1 n p [Hx01 [Hy01 Hbnd]].
  exact (curve_point_fill_touch_sound x0 y0 x1 y1 n p Hbnd Hx01 Hy01).
Qed.

Theorem strict_interior_not_left_boundary_touch :
  forall x0 y0 x1 y1 p,
    point_strictly_in_open_rect x0 y0 x1 y1 p ->
    ~ point_on_rect_left_boundary x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p Hopen [Hx _].
  destruct Hopen as [Hxp _]. lra.
Qed.

Print Assumptions curve_point_fill_contains_sound.