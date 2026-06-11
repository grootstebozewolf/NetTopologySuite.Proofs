(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixArcAnalytic
   ----------------------------------------------------------------------------
   Issue #67 session 10b (S10b): arc×line matrix fill — Option-A analytic (4-ax).

   Fifth computed fill API: `arc_analytic_fill` for the analytic proper-cross
   regime, reusing S10 witness matrices under `arc_analytic_minor_guard`.

   No `Admitted`, no `Axiom`, no `Parameter`.
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import DE9IM Distance CurveGeometry RelateArcAnalytic
  RelateArcChord.
Open Scope R_scope.

Inductive ArcAnalyticRegime : Type :=
| AAR_AnalyticCross.

Definition arc_analytic_fill (r : ArcAnalyticRegime) : IntersectionMatrix :=
  match r with
  | AAR_AnalyticCross => ac_matrix_point_ii
  end.

Lemma arc_analytic_fill_cross_eq :
  arc_analytic_fill AAR_AnalyticCross = ac_matrix_point_ii.
Proof. reflexivity. Qed.

Definition classify_arc_analytic (a : CircularArc) (P Q : Point)
    (r : ArcAnalyticRegime) : Prop :=
  match r with
  | AAR_AnalyticCross => arc_analytic_proper_cross a P Q
  end.

Theorem arc_analytic_fill_cross_sound :
  forall (a : CircularArc) (P Q : Point),
    arc_analytic_proper_cross a P Q ->
    im_crosses (arc_analytic_fill AAR_AnalyticCross) /\
    im_intersects (arc_analytic_fill AAR_AnalyticCross).
Proof.
  intros a P Q H.
  rewrite arc_analytic_fill_cross_eq.
  exact (arc_analytic_proper_cross_sound a P Q H).
Qed.

Theorem classify_analytic_cross_fill_sound :
  forall (a : CircularArc) (P Q : Point),
    classify_arc_analytic a P Q AAR_AnalyticCross ->
    im_crosses (arc_analytic_fill AAR_AnalyticCross) /\
    im_intersects (arc_analytic_fill AAR_AnalyticCross).
Proof.
  intros a P Q H. unfold classify_arc_analytic in H.
  exact (arc_analytic_fill_cross_sound a P Q H).
Qed.

Print Assumptions arc_analytic_fill_cross_sound.