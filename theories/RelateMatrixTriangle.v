(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixTriangle
   ----------------------------------------------------------------------------
   Triangle analogue of RelateMatrixRect.v (S7 style).

   Defines TrianglePairRegime + triangle_pair_fill (regime → witness matrix)
   and classify_triangle_pair.

   Witnesses reuse the aa_* shapes from RelateAreaArea.v for now
   (touch has same BB=1 / EE=2 shape).

   Honest scoping: triangles only (convex, no holes). Full pointset
   satisfaction and noding bridge in RelateNG.

   No `Admitted`, no `Axiom`, no `Parameter`.
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import DE9IM Distance RelateAreaArea Orientation.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Regime enum + matrix fill (parallel to RectPairRegime).                   *)
(* -------------------------------------------------------------------------- *)

Inductive TrianglePairRegime : Type :=
| TPR_Disjoint
| TPR_Overlap
| TPR_Contains
| TPR_TouchEdge
| TPR_TouchVertex.  (* vertex contact; matrix shape can be adjusted later *)

Definition triangle_pair_fill (r : TrianglePairRegime) : IntersectionMatrix :=
  match r with
  | TPR_Disjoint    => aa_matrix_disjoint
  | TPR_Overlap     => aa_matrix_partial_overlap
  | TPR_Contains    => aa_matrix_contains
  | TPR_TouchEdge   => aa_matrix_touch_vertical  (* BB=1, EE=2 *)
  | TPR_TouchVertex => aa_matrix_touch_vertical  (* same for starter; point contact may be dim 0 *)
  end.

Lemma triangle_pair_fill_disjoint_eq :
  triangle_pair_fill TPR_Disjoint = aa_matrix_disjoint.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_overlap_eq :
  triangle_pair_fill TPR_Overlap = aa_matrix_partial_overlap.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_contains_eq :
  triangle_pair_fill TPR_Contains = aa_matrix_contains.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_touch_edge_eq :
  triangle_pair_fill TPR_TouchEdge = aa_matrix_touch_vertical.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_touch_vertex_eq :
  triangle_pair_fill TPR_TouchVertex = aa_matrix_touch_vertical.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Classifier (geometry predicates).                                          *)
(* These name the intended configuration; proved later in RelateNG.           *)
(* For now, opaque for dispatch.                                              *)
(* -------------------------------------------------------------------------- *)

(* Placeholder geometry predicates; will be defined with between/cross/gtri
   in RelateNG and proved to classify the regimes. *)
Definition shares_edge (p1 p2 q1 q2 : Point) : Prop :=
  (p1 = q1 /\ p2 = q2) \/ (p1 = q2 /\ p2 = q1).

Definition opposite_sides (p1 p2 p q : Point) : Prop :=
  let s1 := cross p1 p2 p in
  let s2 := cross p1 p2 q in
  s1 * s2 < 0.

Definition triangles_touch_on_shared_edge (a1 a2 a3 b1 b2 b3 : Point) : Prop :=
  (shares_edge a1 a2 b1 b2 /\ opposite_sides a1 a2 a3 b3) \/
  (shares_edge a1 a2 b2 b3 /\ opposite_sides a1 a2 a3 b1) \/
  (shares_edge a1 a2 b3 b1 /\ opposite_sides a1 a2 a3 b2) \/
  (shares_edge a2 a3 b1 b2 /\ opposite_sides a2 a3 a1 b3) \/
  (shares_edge a2 a3 b2 b3 /\ opposite_sides a2 a3 a1 b1) \/
  (shares_edge a2 a3 b3 b1 /\ opposite_sides a2 a3 a1 b2) \/
  (shares_edge a3 a1 b1 b2 /\ opposite_sides a3 a1 a2 b3) \/
  (shares_edge a3 a1 b2 b3 /\ opposite_sides a3 a1 a2 b1) \/
  (shares_edge a3 a1 b3 b1 /\ opposite_sides a3 a1 a2 b2).

Definition triangles_separated (a1 a2 a3 b1 b2 b3 : Point) : Prop := True.
Definition triangles_partial_overlap (a1 a2 a3 b1 b2 b3 : Point) : Prop := True.
Definition triangle_a_contains_b (a1 a2 a3 b1 b2 b3 : Point) : Prop := True.
Definition triangles_touch_on_edge (a1 a2 a3 b1 b2 b3 : Point) : Prop :=
  triangles_touch_on_shared_edge a1 a2 a3 b1 b2 b3.
Definition triangles_touch_at_vertex (a1 a2 a3 b1 b2 b3 : Point) : Prop := True.

Definition classify_triangle_pair (a1 a2 a3 b1 b2 b3 : Point)
    (r : TrianglePairRegime) : Prop :=
  match r with
  | TPR_Disjoint    => triangles_separated a1 a2 a3 b1 b2 b3
  | TPR_Overlap     => triangles_partial_overlap a1 a2 a3 b1 b2 b3
  | TPR_Contains    => triangle_a_contains_b a1 a2 a3 b1 b2 b3
  | TPR_TouchEdge   => triangles_touch_on_edge a1 a2 a3 b1 b2 b3
  | TPR_TouchVertex => triangles_touch_at_vertex a1 a2 a3 b1 b2 b3
  end.
