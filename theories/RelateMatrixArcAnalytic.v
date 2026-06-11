(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixArcAnalytic
   ----------------------------------------------------------------------------
   Issue #67 session 10b (S10b): arc×line regime→witness — Option-A analytic.

   `arc_analytic_fill` SELECTS (does not compute from geometry) the S10 point
   witness for the analytic proper-cross regime.  The witness fact is constant;
   the regime hypothesis is not consumed, and no geometry→matrix claim is made.

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

(* Constant witness fact: the selected witness satisfies the regime's
   predicate.  No geometry hypothesis, no geometry→matrix claim. *)
Theorem arc_analytic_fill_cross_witness :
  im_crosses (arc_analytic_fill AAR_AnalyticCross) /\
  im_intersects (arc_analytic_fill AAR_AnalyticCross).
Proof.
  rewrite arc_analytic_fill_cross_eq.
  split; [exact ac_matrix_point_ii_crosses | exact ac_matrix_point_ii_intersects].
Qed.

Print Assumptions arc_analytic_fill_cross_witness.