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
(* Assumption audit. The proofs above are pure ring + linear arithmetic       *)
(* over real numbers; no axiom is introduced beyond the standard library's    *)
(* classical real arithmetic.                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions between_implies_on_line.
Print Assumptions off_line_not_between.
