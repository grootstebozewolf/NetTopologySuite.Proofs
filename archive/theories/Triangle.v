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
(* Side-length-squared definitions and basic properties.                       *)
(* -------------------------------------------------------------------------- *)

Definition side_AB_sq (t : Triangle) : R := dist_sq (tA t) (tB t).
Definition side_BC_sq (t : Triangle) : R := dist_sq (tB t) (tC t).
Definition side_CA_sq (t : Triangle) : R := dist_sq (tC t) (tA t).

Lemma side_AB_sq_nonneg : forall t, 0 <= side_AB_sq t.
Proof. intros. unfold side_AB_sq. apply dist_sq_nonneg. Qed.

Lemma side_BC_sq_nonneg : forall t, 0 <= side_BC_sq t.
Proof. intros. unfold side_BC_sq. apply dist_sq_nonneg. Qed.

Lemma side_CA_sq_nonneg : forall t, 0 <= side_CA_sq t.
Proof. intros. unfold side_CA_sq. apply dist_sq_nonneg. Qed.

Lemma side_AB_sq_sym : forall A B C,
  side_AB_sq (mkTriangle A B C) = side_AB_sq (mkTriangle B A C).
Proof. intros. unfold side_AB_sq. simpl. apply dist_sq_sym. Qed.

Lemma side_AB_sq_zero_iff : forall t,
  side_AB_sq t = 0 <-> (px (tA t) = px (tB t) /\ py (tA t) = py (tB t)).
Proof. intros. unfold side_AB_sq. apply dist_sq_zero_iff_eq. Qed.

(* -------------------------------------------------------------------------- *)
(* Two further degeneracy characterisations.                                  *)
(* -------------------------------------------------------------------------- *)

Lemma is_degenerate_iff_area2_zero : forall t,
  is_degenerate t <-> area2 t = 0.
Proof. intros. unfold is_degenerate. tauto. Qed.

Lemma area2_unfold : forall t,
  area2 t = (px (tB t) - px (tA t)) * (py (tC t) - py (tA t))
          - (px (tC t) - px (tA t)) * (py (tB t) - py (tA t)).
Proof. intros. unfold area2, cross. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Vertex-position lemmas.                                                    *)
(* -------------------------------------------------------------------------- *)

Lemma area2_translate_A : forall A B C dx dy,
  area2 (mkTriangle (translate A dx dy) (translate B dx dy) (translate C dx dy))
  = area2 (mkTriangle A B C).
Proof.
  intros. unfold area2. simpl. apply cross_translation_invariant.
Qed.

Lemma area2_AB_aligned : forall A B,
  area2 (mkTriangle A B (mkPoint (px A) (py A))) = 0.
Proof.
  intros A B. unfold area2, cross. simpl. ring.
Qed.

Lemma area2_neg_cancel : forall t,
  area2 t + area2 (mkTriangle (tA t) (tC t) (tB t)) = 0.
Proof.
  intros. unfold area2, cross. simpl. ring.
Qed.

Lemma area2_double_AC : forall A C,
  area2 (mkTriangle A C A) = 0.
Proof. intros. unfold area2. simpl. apply cross_at_P0_is_collinear. Qed.

Lemma area2_double_BC : forall A B,
  area2 (mkTriangle A B B) = 0.
Proof. intros. unfold area2. simpl. apply cross_at_P1_is_collinear. Qed.

Lemma area2_with_AA : forall A C,
  area2 (mkTriangle A A C) = 0.
Proof. intros. unfold area2. simpl. apply cross_degenerate_base. Qed.

Lemma side_AB_sq_at_collapsed : forall A C,
  side_AB_sq (mkTriangle A A C) = 0.
Proof.
  intros. unfold side_AB_sq, dist_sq. simpl. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Perimeter (squared sum) and basic bound.                                   *)
(* -------------------------------------------------------------------------- *)

Definition sum_sides_sq (t : Triangle) : R :=
  side_AB_sq t + side_BC_sq t + side_CA_sq t.

Lemma sum_sides_sq_nonneg : forall t, 0 <= sum_sides_sq t.
Proof.
  intros. unfold sum_sides_sq.
  pose proof (side_AB_sq_nonneg t).
  pose proof (side_BC_sq_nonneg t).
  pose proof (side_CA_sq_nonneg t).
  lra.
Qed.

Lemma sum_sides_sq_zero_implies_all_coincide : forall A B C,
  sum_sides_sq (mkTriangle A B C) = 0 ->
  side_AB_sq (mkTriangle A B C) = 0 /\
  side_BC_sq (mkTriangle A B C) = 0 /\
  side_CA_sq (mkTriangle A B C) = 0.
Proof.
  intros A B C H. unfold sum_sides_sq in H.
  pose proof (side_AB_sq_nonneg (mkTriangle A B C)).
  pose proof (side_BC_sq_nonneg (mkTriangle A B C)).
  pose proof (side_CA_sq_nonneg (mkTriangle A B C)).
  split; [|split]; lra.
Qed.

Lemma sum_sides_sq_translate : forall A B C dx dy,
  sum_sides_sq (mkTriangle (translate A dx dy) (translate B dx dy) (translate C dx dy))
  = sum_sides_sq (mkTriangle A B C).
Proof.
  intros. unfold sum_sides_sq, side_AB_sq, side_BC_sq, side_CA_sq, dist_sq, translate.
  simpl. ring.
Qed.

Lemma area2_swap_AC : forall A B C,
  area2 (mkTriangle A B C) = - area2 (mkTriangle C B A).
Proof.
  intros. unfold area2, cross. simpl. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions area2_cyclic_ABC_BCA.
Print Assumptions area2_translation_invariant.
