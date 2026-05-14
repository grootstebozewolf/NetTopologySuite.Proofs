(* ============================================================================
   NetTopologySuite.Proofs.Orientation
   ----------------------------------------------------------------------------
   Foundational properties of the orientation predicate.

   In NTS (`Algorithm.Orientation.Index`) and JTS, orientation is determined
   by the sign of the cross product

       cross(P0, P1, Q) = (P1.x - P0.x) * (Q.y  - P0.y)
                        - (Q.x  - P0.x) * (P1.y - P0.y)

   which is signed twice the area of triangle P0-P1-Q. The sign distinguishes
   counter-clockwise (positive), clockwise (negative), and collinear (zero).

   The predicate is used throughout the library; everything that decides
   "is this point left/right of this segment" rests on it. The properties
   below are the algebraic invariants any correct implementation must satisfy
   regardless of arithmetic representation.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Signed twice-area of the triangle (P0, P1, Q).                             *)
(* -------------------------------------------------------------------------- *)

Definition cross (P0 P1 Q : Point) : R :=
  (px P1 - px P0) * (py Q  - py P0)
  - (px Q  - px P0) * (py P1 - py P0).

(* -------------------------------------------------------------------------- *)
(* Antisymmetry: swapping the last two arguments flips the sign.              *)
(* This makes "directed orientation" a coherent notion: the function          *)
(* genuinely tells you which side of an oriented segment a point lies on.     *)
(* -------------------------------------------------------------------------- *)

Theorem cross_antisymmetric : forall P0 P1 Q,
  cross P0 P1 Q = - cross P0 Q P1.
Proof.
  intros P0 P1 Q. unfold cross. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Collinearity is preserved under reversal: if Q lies on the line through    *)
(* P0 and P1, then it lies on the line through P0 and P1 in the opposite      *)
(* direction. A direct consequence of antisymmetry.                           *)
(* -------------------------------------------------------------------------- *)

Theorem cross_collinear_sym : forall P0 P1 Q,
  cross P0 P1 Q = 0 <-> cross P0 Q P1 = 0.
Proof.
  intros P0 P1 Q.
  rewrite cross_antisymmetric.
  split; intros H.
  - apply Ropp_eq_0_compat in H. rewrite Ropp_involutive in H. exact H.
  - rewrite H. apply Ropp_0.
Qed.

(* -------------------------------------------------------------------------- *)
(* Endpoint coincidence: a point coincident with either base endpoint is      *)
(* collinear (the triangle degenerates to a segment, zero area).              *)
(* -------------------------------------------------------------------------- *)

Theorem cross_at_P0_is_collinear : forall P0 P1,
  cross P0 P1 P0 = 0.
Proof.
  intros P0 P1. unfold cross. ring.
Qed.

Theorem cross_at_P1_is_collinear : forall P0 P1,
  cross P0 P1 P1 = 0.
Proof.
  intros P0 P1. unfold cross. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Translation invariance: shifting all three points by the same vector       *)
(* leaves the orientation unchanged. This is the property that lets NTS       *)
(* relocate or normalise coordinate frames without changing any topological   *)
(* result.                                                                    *)
(* -------------------------------------------------------------------------- *)

Definition translate (p : Point) (vx vy : R) : Point :=
  mkPoint (px p + vx) (py p + vy).

Theorem cross_translation_invariant : forall P0 P1 Q vx vy,
  cross (translate P0 vx vy) (translate P1 vx vy) (translate Q vx vy)
  = cross P0 P1 Q.
Proof.
  intros P0 P1 Q vx vy. unfold cross, translate. simpl. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Swapping the first two arguments also flips the sign.  Distinct from       *)
(* `cross_antisymmetric` (which swaps the last two): together they generate   *)
(* the full sign action of the symmetric group S_3 on the three arguments.    *)
(* -------------------------------------------------------------------------- *)

Theorem cross_swap_first_two : forall P0 P1 Q,
  cross P0 P1 Q = - cross P1 P0 Q.
Proof.
  intros P0 P1 Q. unfold cross. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cyclic permutation of the three arguments preserves the cross product.    *)
(* An even permutation, so no sign change.                                    *)
(* -------------------------------------------------------------------------- *)

Theorem cross_cyclic : forall A B C,
  cross A B C = cross B C A.
Proof. intros A B C. unfold cross. ring. Qed.

Theorem cross_cyclic_2 : forall A B C,
  cross A B C = cross C A B.
Proof. intros A B C. unfold cross. ring. Qed.

(* -------------------------------------------------------------------------- *)
(* Translating only the third argument: cross becomes cross of the translate. *)
(* More general than `cross_translation_invariant`.                           *)
(* -------------------------------------------------------------------------- *)

Lemma cross_translate_third : forall A B Q vx vy,
  cross A B (translate Q vx vy) = cross A B Q
    + (px B - px A) * vy - vx * (py B - py A).
Proof. intros A B Q vx vy. unfold cross, translate. simpl. ring. Qed.

(* -------------------------------------------------------------------------- *)
(* Coincident base: cross(A, A, Q) = 0 for any Q.  A line through a single   *)
(* point has no defined orientation; the cross product reflects this by      *)
(* vanishing.                                                                 *)
(* -------------------------------------------------------------------------- *)

Theorem cross_degenerate_base : forall A Q,
  cross A A Q = 0.
Proof. intros A Q. unfold cross. ring. Qed.

(* -------------------------------------------------------------------------- *)
(* Scaling all three points by the same factor scales the cross product by    *)
(* the factor squared.  Combined with sign analysis, this gives positive-    *)
(* scaling-preserves-orientation as a corollary.                              *)
(* -------------------------------------------------------------------------- *)

Definition pt_scale_o (c : R) (p : Point) : Point :=
  mkPoint (c * px p) (c * py p).

Theorem cross_scale : forall c A B Q,
  cross (pt_scale_o c A) (pt_scale_o c B) (pt_scale_o c Q)
  = c * c * cross A B Q.
Proof.
  intros c A B Q. unfold cross, pt_scale_o. simpl. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit. All theorems in this file are purely algebraic and       *)
(* depend on `ring`-equivalent reasoning over the real field. No classical    *)
(* axioms (excluded middle, irrelevance, choice) are introduced.              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions cross_antisymmetric.
Print Assumptions cross_translation_invariant.
