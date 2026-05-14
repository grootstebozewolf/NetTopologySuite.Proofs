(* ============================================================================
   NetTopologySuite.Proofs.Triangle
   ----------------------------------------------------------------------------
   Triangles in the plane: the signed-area function (via the cross product),
   degeneracy, the permutation/sign action on vertices, translation and
   scaling invariance.

   NTS uses signed triangle area heavily — `Triangle.signedArea` in JTS, and
   throughout the orientation-based polygonal predicates.  Stating the
   algebraic invariants once means downstream proofs about polygons,
   triangulations, and Voronoi diagrams can cite them as named lemmas.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance Orientation.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* A triangle is an ordered triple of points.                                 *)
(* -------------------------------------------------------------------------- *)

Record Triangle : Type := mkTriangle { tA : Point; tB : Point; tC : Point }.

(* -------------------------------------------------------------------------- *)
(* Signed twice the area, computed via the cross product of two edges.       *)
(* The factor of two is kept implicit; the sign carries the orientation.    *)
(* -------------------------------------------------------------------------- *)

Definition area2 (t : Triangle) : R := cross (tA t) (tB t) (tC t).

Definition is_degenerate (t : Triangle) : Prop := area2 t = 0.

(* -------------------------------------------------------------------------- *)
(* A triangle is degenerate iff its vertices are collinear (third vertex on   *)
(* the line through the first two).  Restatement of the definition in the    *)
(* triangle vocabulary.                                                       *)
(* -------------------------------------------------------------------------- *)

Lemma area2_zero_iff_collinear : forall t,
  is_degenerate t <-> cross (tA t) (tB t) (tC t) = 0.
Proof. intros t. unfold is_degenerate, area2. tauto. Qed.

(* -------------------------------------------------------------------------- *)
(* Vertex swap flips signed area; cyclic permutations preserve it.           *)
(* -------------------------------------------------------------------------- *)

Lemma area2_swap_AB : forall t,
  area2 t = - area2 (mkTriangle (tB t) (tA t) (tC t)).
Proof.
  intros t. unfold area2. simpl. apply cross_swap_first_two.
Qed.

Lemma area2_swap_BC : forall t,
  area2 t = - area2 (mkTriangle (tA t) (tC t) (tB t)).
Proof.
  intros t. unfold area2. simpl. apply cross_antisymmetric.
Qed.

Lemma area2_cyclic_ABC_BCA : forall t,
  area2 t = area2 (mkTriangle (tB t) (tC t) (tA t)).
Proof.
  intros t. unfold area2. simpl. apply cross_cyclic.
Qed.

Lemma area2_cyclic_ABC_CAB : forall t,
  area2 t = area2 (mkTriangle (tC t) (tA t) (tB t)).
Proof.
  intros t. unfold area2. simpl. apply cross_cyclic_2.
Qed.

(* -------------------------------------------------------------------------- *)
(* Degeneracy when two vertices coincide.                                     *)
(* -------------------------------------------------------------------------- *)

Lemma area2_AA_degenerate : forall A C,
  is_degenerate (mkTriangle A A C).
Proof.
  intros A C. unfold is_degenerate, area2. simpl. apply cross_degenerate_base.
Qed.

Lemma area2_AB_at_A_degenerate : forall A B,
  is_degenerate (mkTriangle A B A).
Proof.
  intros A B. unfold is_degenerate, area2. simpl.
  apply cross_at_P0_is_collinear.
Qed.

Lemma area2_AB_at_B_degenerate : forall A B,
  is_degenerate (mkTriangle A B B).
Proof.
  intros A B. unfold is_degenerate, area2. simpl.
  apply cross_at_P1_is_collinear.
Qed.

(* -------------------------------------------------------------------------- *)
(* Affine invariance: translation preserves signed area; scaling all         *)
(* coordinates by c scales signed area by c².                                *)
(* -------------------------------------------------------------------------- *)

Definition tri_translate (t : Triangle) (vx vy : R) : Triangle :=
  mkTriangle (translate (tA t) vx vy)
             (translate (tB t) vx vy)
             (translate (tC t) vx vy).

Lemma area2_translation_invariant : forall t vx vy,
  area2 (tri_translate t vx vy) = area2 t.
Proof.
  intros t vx vy. unfold area2, tri_translate. simpl.
  apply cross_translation_invariant.
Qed.

Definition tri_scale (c : R) (t : Triangle) : Triangle :=
  mkTriangle (pt_scale_o c (tA t))
             (pt_scale_o c (tB t))
             (pt_scale_o c (tC t)).

Lemma area2_scale : forall c t,
  area2 (tri_scale c t) = c * c * area2 t.
Proof.
  intros c t. unfold area2, tri_scale. simpl. apply cross_scale.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions area2_cyclic_ABC_BCA.
Print Assumptions area2_translation_invariant.
