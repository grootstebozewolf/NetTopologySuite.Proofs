(* ============================================================================
   NetTopologySuite.Proofs.Segment
   ----------------------------------------------------------------------------
   Finite line segments in the plane, the parametric "between" relation, and
   the bridge to the orientation predicate.

   Every segment-intersection test in NetTopologySuite (`LineIntersector`,
   `RobustLineIntersector`, the overlay machinery) rests on a single
   correspondence: a point Q lies on a segment P0-P1 only if it lies on the
   infinite line through P0 and P1 (i.e., `cross(P0, P1, Q) = 0`).

   This file states the parametric definition of "between" and proves it
   implies collinearity. Once that bridge is established, every downstream
   intersection test that uses `cross` is entitled to "Q lies on segment"
   as a sufficient witness of collinearity without recomputing the line
   equation.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance Orientation.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* A finite line segment is a pair of endpoints.                              *)
(* -------------------------------------------------------------------------- *)

Record Segment : Type := mkSegment { sp0 : Point; sp1 : Point }.

(* -------------------------------------------------------------------------- *)
(* Q lies on the infinite line through P0 and P1.                             *)
(* -------------------------------------------------------------------------- *)

Definition on_line (P0 P1 Q : Point) : Prop := cross P0 P1 Q = 0.

(* -------------------------------------------------------------------------- *)
(* Q lies on the closed segment from P0 to P1.                                *)
(* Parametric form: there exists t in [0, 1] such that                        *)
(*   Q = (1 - t) * P0 + t * P1                                                *)
(* coordinate-wise.                                                           *)
(* -------------------------------------------------------------------------- *)

Definition between (P0 P1 Q : Point) : Prop :=
  exists t : R, 0 <= t /\ t <= 1 /\
    px Q = (1 - t) * px P0 + t * px P1 /\
    py Q = (1 - t) * py P0 + t * py P1.

(* -------------------------------------------------------------------------- *)
(* The endpoints lie on the segment trivially.                                *)
(* -------------------------------------------------------------------------- *)

Lemma between_P0 : forall P0 P1, between P0 P1 P0.
Proof.
  intros P0 P1. exists 0.
  repeat split; try lra; ring.
Qed.

Lemma between_P1 : forall P0 P1, between P0 P1 P1.
Proof.
  intros P0 P1. exists 1.
  repeat split; try lra; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* The segment relation is symmetric in its endpoints: reversing the segment  *)
(* direction does not change which points lie on it.                          *)
(* -------------------------------------------------------------------------- *)

Lemma between_symmetric : forall P0 P1 Q,
  between P0 P1 Q <-> between P1 P0 Q.
Proof.
  assert (Help : forall A B Q, between A B Q -> between B A Q).
  { intros A B Q [t [Ht0 [Ht1 [Hx Hy]]]].
    exists (1 - t).
    split; [lra |].
    split; [lra |].
    split; [rewrite Hx; ring | rewrite Hy; ring]. }
  intros P0 P1 Q. split; apply Help.
Qed.

(* -------------------------------------------------------------------------- *)
(* The headline theorem: a point on the segment is collinear with the         *)
(* endpoints. This is the bridge that lets every cross-product-based          *)
(* intersection test treat "between" as a sufficient witness of collinearity. *)
(* -------------------------------------------------------------------------- *)

Theorem between_implies_on_line : forall P0 P1 Q,
  between P0 P1 Q -> on_line P0 P1 Q.
Proof.
  intros P0 P1 Q [t [Ht0 [Ht1 [Hx Hy]]]].
  unfold on_line, cross.
  rewrite Hx, Hy.
  ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Corollary: a point at strictly positive perpendicular distance from the    *)
(* line P0-P1 cannot lie on the segment. This is the contrapositive of the    *)
(* headline theorem, written as a positive existential closer to the form    *)
(* used by intersection-rejection paths in NTS.                               *)
(*                                                                            *)
(* (We state it in terms of `cross <> 0` rather than perpendicular distance   *)
(* because the cross product is what the implementation actually computes.    *)
(* The two are scalar multiples for fixed P0, P1.)                            *)
(* -------------------------------------------------------------------------- *)

Corollary off_line_not_between : forall P0 P1 Q,
  cross P0 P1 Q <> 0 -> ~ between P0 P1 Q.
Proof.
  intros P0 P1 Q Hne Hbetween.
  apply Hne.
  apply between_implies_on_line in Hbetween.
  unfold on_line in Hbetween.
  exact Hbetween.
Qed.

(* -------------------------------------------------------------------------- *)
(* The "on infinite line" relation is symmetric in the line's endpoints.      *)
(* (Falls out of cross_swap_first_two: swapping flips the sign, but a sign-   *)
(* flipped zero is still zero.)                                               *)
(* -------------------------------------------------------------------------- *)

Lemma on_line_symmetric : forall P0 P1 Q,
  on_line P0 P1 Q <-> on_line P1 P0 Q.
Proof.
  intros P0 P1 Q. unfold on_line.
  rewrite (cross_swap_first_two P0 P1 Q).
  split; intros H.
  - apply Ropp_eq_compat in H. rewrite Ropp_involutive, Ropp_0 in H. exact H.
  - rewrite H. apply Ropp_0.
Qed.

(* -------------------------------------------------------------------------- *)
(* A point on a closed segment has each coordinate within the closed range    *)
(* spanned by the corresponding coordinates of the endpoints.  This is the    *)
(* algebraic basis for envelope/bounding-box rejection tests in NTS.          *)
(* -------------------------------------------------------------------------- *)

Lemma between_in_coord_range : forall P0 P1 Q,
  between P0 P1 Q ->
  Rmin (px P0) (px P1) <= px Q <= Rmax (px P0) (px P1) /\
  Rmin (py P0) (py P1) <= py Q <= Rmax (py P0) (py P1).
Proof.
  intros P0 P1 Q [t [Ht0 [Ht1 [HXx HXy]]]].
  split; split.
  - rewrite HXx. pose proof (Rmin_l (px P0) (px P1)).
    pose proof (Rmin_r (px P0) (px P1)). nra.
  - rewrite HXx. pose proof (Rmax_l (px P0) (px P1)).
    pose proof (Rmax_r (px P0) (px P1)). nra.
  - rewrite HXy. pose proof (Rmin_l (py P0) (py P1)).
    pose proof (Rmin_r (py P0) (py P1)). nra.
  - rewrite HXy. pose proof (Rmax_l (py P0) (py P1)).
    pose proof (Rmax_r (py P0) (py P1)). nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The midpoint of a segment lies on the segment (with parameter t = 1/2).    *)
(* -------------------------------------------------------------------------- *)

Definition midpoint (P0 P1 : Point) : Point :=
  mkPoint ((px P0 + px P1) / 2) ((py P0 + py P1) / 2).

Lemma midpoint_between : forall P0 P1, between P0 P1 (midpoint P0 P1).
Proof.
  intros P0 P1. exists (1/2).
  split; [lra |].
  split; [lra |].
  split; unfold midpoint; cbn; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Endpoint coincidence: when P0 = P1, the "segment" is a single point, and  *)
(* the only point on it is P0 itself.                                         *)
(* -------------------------------------------------------------------------- *)

Lemma between_degenerate : forall P Q,
  between P P Q -> px Q = px P /\ py Q = py P.
Proof.
  intros P Q [t [_ [_ [Hx Hy]]]].
  split.
  - rewrite Hx. ring.
  - rewrite Hy. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Transitivity of the betweenness relation through an interior point.       *)
(* If X is between A and B, and Y is between A and X, then Y is also         *)
(* between A and B.  This is the property polyline-traversal proofs use.    *)
(* -------------------------------------------------------------------------- *)

Lemma between_transitive : forall A B X Y,
  between A B X -> between A X Y -> between A B Y.
Proof.
  intros A B X Y [tx [Htx0 [Htx1 [HXx HXy]]]] [ty [Hty0 [Hty1 [HYx HYy]]]].
  exists (ty * tx).
  split; [nra |].
  split; [nra |].
  split.
  - rewrite HYx, HXx. ring.
  - rewrite HYy, HXy. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* A point is on the closed segment iff it can be written as a convex        *)
(* combination of the endpoints.  This is the parametric definition restated *)
(* as an iff for use as a rewriting principle downstream.                    *)
(* -------------------------------------------------------------------------- *)

Lemma between_iff_convex_combination : forall P0 P1 Q,
  between P0 P1 Q <->
  exists t : R, 0 <= t <= 1 /\
    px Q = (1 - t) * px P0 + t * px P1 /\
    py Q = (1 - t) * py P0 + t * py P1.
Proof.
  intros P0 P1 Q. split.
  - intros [t [Ht0 [Ht1 [Hx Hy]]]]. exists t. split; [lra | split; assumption].
  - intros [t [[Ht0 Ht1] [Hx Hy]]]. exists t. repeat split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Midpoint properties.                                                        *)
(* -------------------------------------------------------------------------- *)

Lemma midpoint_symmetric : forall P Q, midpoint P Q = midpoint Q P.
Proof. intros. unfold midpoint. simpl. f_equal; field. Qed.

Lemma midpoint_self : forall P, midpoint P P = P.
Proof. intros [a b]. unfold midpoint. simpl. f_equal; field. Qed.

Lemma midpoint_x : forall P Q, px (midpoint P Q) = (px P + px Q) / 2.
Proof. intros. reflexivity. Qed.

Lemma midpoint_y : forall P Q, py (midpoint P Q) = (py P + py Q) / 2.
Proof. intros. reflexivity. Qed.

Lemma midpoint_collinear : forall P Q,
  cross P Q (midpoint P Q) = 0.
Proof. intros. unfold cross, midpoint. simpl. field. Qed.

(* -------------------------------------------------------------------------- *)
(* Coordinate-range corollaries.                                              *)
(* -------------------------------------------------------------------------- *)

Lemma between_px_le_max : forall P0 P1 Q,
  between P0 P1 Q -> px Q <= Rmax (px P0) (px P1).
Proof.
  intros. apply (between_in_coord_range P0 P1 Q) in H. tauto.
Qed.

Lemma between_px_ge_min : forall P0 P1 Q,
  between P0 P1 Q -> Rmin (px P0) (px P1) <= px Q.
Proof.
  intros. apply (between_in_coord_range P0 P1 Q) in H. tauto.
Qed.

Lemma between_py_le_max : forall P0 P1 Q,
  between P0 P1 Q -> py Q <= Rmax (py P0) (py P1).
Proof.
  intros. apply (between_in_coord_range P0 P1 Q) in H. tauto.
Qed.

Lemma between_py_ge_min : forall P0 P1 Q,
  between P0 P1 Q -> Rmin (py P0) (py P1) <= py Q.
Proof.
  intros. apply (between_in_coord_range P0 P1 Q) in H. tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* on_line properties (algebraic).                                            *)
(* -------------------------------------------------------------------------- *)

Lemma on_line_swap_args : forall P0 P1 Q,
  on_line P0 P1 Q -> on_line P1 P0 Q.
Proof. intros. apply on_line_symmetric. exact H. Qed.

Lemma on_line_at_P0 : forall P0 P1, on_line P0 P1 P0.
Proof. intros. unfold on_line. apply cross_at_P0_is_collinear. Qed.

Lemma on_line_at_P1 : forall P0 P1, on_line P0 P1 P1.
Proof. intros. unfold on_line. apply cross_at_P1_is_collinear. Qed.

Lemma on_line_degenerate : forall P Q, on_line P P Q.
Proof. intros. unfold on_line. apply cross_degenerate_base. Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit. The proofs above are pure ring + linear arithmetic       *)
(* over real numbers; no axiom is introduced beyond the standard library's    *)
(* classical real arithmetic.                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions between_implies_on_line.
Print Assumptions off_line_not_between.
