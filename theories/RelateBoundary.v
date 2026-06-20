(* ============================================================================
   NetTopologySuite.Proofs.RelateBoundary
   ----------------------------------------------------------------------------
   Issue #67 session 4b (S4b): boundary / MOD2 policy — witnesses + geometry.

   Formalises the JTS `BoundaryNodeRule` classification spine (default MOD2)
   and records the `Touches` / `Intersects` witness matrices from `DE9IM.v`
   for endpoint-vs-interior contact regimes on closed segments.

   Delivers:

     - `BoundaryNodeRule` + MOD2 parity classification (degree 1 ⇒ boundary)
     - Endpoint vs interior share predicates on segment pairs
     - Hand-specified `Touches` witness for endpoint-only contact (L-touch),
       with the constant `ll_matrix_touches_endpoint_*` predicate lemmas
     - Genuine geometry lemma: endpoint contact ⇒ the segments share a point
       (`endpoint_contact_share`)
     - JTS#1175 regression class pinned via `ll_matrix_paper_test10`
       (geometrically separated segments need not be DE-9IM `disjoint`)

   Honest scoping: closed segments; witness matrices hand-specified.  Now extended
   with incidence helpers for RelateNG pipeline (MOD2 policy applied to boundary
   cell dims). Multi-component collections and prepared cache remain follow-up.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia PeanoNat.
From NTS.Proofs Require Import DE9IM Distance Segment Intersect RelateLineLine.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* JTS BoundaryNodeRule — MOD2 default.                                       *)
(* -------------------------------------------------------------------------- *)

Inductive BoundaryNodeRule : Type :=
| BNR_Mod2
| BNR_EndPoint
| BNR_MonoValent.

(* Under MOD2, a node is on the boundary iff its incidence count is odd. *)
Definition mod2_is_boundary_node (degree : nat) : Prop :=
  exists k : nat, degree = (2 * k + 1)%nat.

Lemma mod2_endpoint_is_boundary :
  mod2_is_boundary_node 1.
Proof.
  unfold mod2_is_boundary_node. exists 0%nat. lia.
Qed.

Lemma mod2_degree_two_not_boundary :
  ~ mod2_is_boundary_node 2.
Proof.
  unfold mod2_is_boundary_node.
  intros [k H].
  lia.
Qed.

(* A line-string endpoint has incidence 1 under the standard MOD2 rule. *)
Lemma line_endpoint_mod2_boundary :
  mod2_is_boundary_node 1.
Proof. exact mod2_endpoint_is_boundary. Qed.

(* -------------------------------------------------------------------------- *)
(* Endpoint vs interior contact on segment pairs.                             *)
(* -------------------------------------------------------------------------- *)

Definition on_segment_endpoint (P0 P1 Q : Point) : Prop :=
  between P0 P1 Q /\ (Q = P0 \/ Q = P1).

Definition between_strict (P0 P1 Q : Point) : Prop :=
  exists t : R,
    0 < t < 1 /\
    px Q = (1 - t) * px P0 + t * px P1 /\
    py Q = (1 - t) * py P0 + t * py P1.

Definition segments_interior_share (A B C D : Point) : Prop :=
  exists X : Point,
    between_strict A B X /\ between_strict C D X.

Definition segments_endpoint_contact (A B C D : Point) : Prop :=
  exists X : Point,
    between A B X /\ between C D X /\
    on_segment_endpoint A B X /\ on_segment_endpoint C D X.

Definition segments_endpoint_only_contact (A B C D : Point) : Prop :=
  segments_endpoint_contact A B C D /\
  ~ segments_interior_share A B C D /\
  ~ segments_interior_collinear_overlap A B C D.

(* -------------------------------------------------------------------------- *)
(* Canonical Touches witness — endpoint-only line-line contact (IB=0).     *)
(* -------------------------------------------------------------------------- *)

Definition ll_matrix_touches_endpoint : IntersectionMatrix :=
  {| im_ii := ll_cell_empty; im_ib := ll_dim0; im_ie := ll_cell_empty;
     im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_cell_empty;
     im_ei := ll_cell_empty; im_eb := ll_cell_empty; im_ee := ll_dim2 |}.

Lemma ll_matrix_touches_endpoint_witness :
  im_touches ll_matrix_touches_endpoint.
Proof.
  unfold im_touches. left.
  unfold matrix_matches, pat_touches_0, ll_matrix_touches_endpoint. simpl.
  repeat split; auto.
Qed.

Lemma ll_matrix_touches_endpoint_predicate :
  predicate_holds RTouches ll_matrix_touches_endpoint.
Proof.
  unfold predicate_holds. exact ll_matrix_touches_endpoint_witness.
Qed.

Lemma ll_matrix_touches_endpoint_intersects :
  im_intersects ll_matrix_touches_endpoint.
Proof.
  unfold im_intersects. right; left.
  unfold matrix_matches, pat_intersects_1, ll_matrix_touches_endpoint. simpl.
  repeat split; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Genuine geometry lemma: endpoint contact ⇒ the segments share a point.    *)
(*                                                                            *)
(* The matrix-level facts for the endpoint-only Touches witness and the       *)
(* shared-point Intersects witness are the constant `ll_matrix_touches_*` and *)
(* `ll_matrix_point_ii_*` lemmas (here / in `RelateLineLine.v`).  They are    *)
(* not bridged to the geometry here: which witness a configuration's true     *)
(* DE-9IM equals is the deferred RelateNG-noding step.                        *)
(* -------------------------------------------------------------------------- *)

Theorem endpoint_contact_share :
  forall A B C D : Point,
    segments_endpoint_contact A B C D ->
    segments_share A B C D.
Proof.
  intros A B C D [X [HAB [HCD _]]].
  exists X. split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* JTS#1175 regression class — boundary cells visible though separated.       *)
(*                                                                            *)
(* Romanschek test 10 (`FF10F0102`): segments are geometrically separated     *)
(* (no shared point) yet the full matrix is not `disjoint` because BI=0.      *)
(* This is the DE-9IM footprint of the bug class fixed in JTS#1200: boundary   *)
(* endpoints must be accounted for even across disjoint line components.       *)
(* -------------------------------------------------------------------------- *)

Definition jts1175_separated_not_disjoint_matrix : IntersectionMatrix :=
  ll_matrix_paper_test10.

Lemma jts1175_separated_not_disjoint_matrix_holds :
  im_intersects jts1175_separated_not_disjoint_matrix /\
  ~ im_disjoint jts1175_separated_not_disjoint_matrix.
Proof.
  split.
  - exact paper_test10_intersects.
  - exact paper_test10_not_disjoint.
Qed.

Theorem jts1175_boundary_cells_preclude_disjoint :
  predicate_holds RIntersects jts1175_separated_not_disjoint_matrix /\
  ~ predicate_holds RDisjoint jts1175_separated_not_disjoint_matrix.
Proof.
  split.
  - unfold predicate_holds. exact paper_test10_intersects.
  - unfold predicate_holds. exact paper_test10_not_disjoint.
Qed.

(* -------------------------------------------------------------------------- *)
(* Pipeline helpers: MOD2 incidence → boundary cell dimension.                *)
(*                                                                            *)
(* For RelateNG matrix assembly (boundary cells IB/BI/BB/BE/EB). Under MOD2   *)
(* a lone endpoint contact (degree 1, odd) contributes a dim-0 boundary point.*)
(* Positive-length boundary runs (area or collinear line overlap) are handled *)
(* separately by edge tests and yield dim 1.  These helpers make the policy   *)
(* reusable from the pipeline without duplicating the odd-degree rule.        *)
(* -------------------------------------------------------------------------- *)

Definition mod2_boundary_dim (degree : nat) : DimValue :=
  if Nat.odd degree then Some 0%nat else None.

Lemma mod2_boundary_dim_endpoint :
  mod2_boundary_dim 1 = Some 0%nat.
Proof.
  reflexivity.
Qed.

Lemma mod2_boundary_dim_even_none :
  forall k, mod2_boundary_dim (2 * k)%nat = None.
Proof.
  intros k. unfold mod2_boundary_dim. rewrite Nat.odd_even. reflexivity.
Qed.

Lemma mod2_boundary_dim_1 :
  mod2_boundary_dim 1 = Some 0%nat.
Proof. reflexivity. Qed.

Lemma mod2_boundary_dim_3 :
  mod2_boundary_dim 3 = Some 0%nat.
Proof. reflexivity. Qed.

(* Abstract incidence count for pipeline use.  Concrete noding collection
   (walking noded fragments for endpoint hits at a vertex) lives in RelateNG.
   Here we only require the parity link. *)
Definition odd_incidence_is_mod2_boundary (incidences : nat) : Prop :=
  mod2_is_boundary_node incidences.

Lemma odd_incidence_boundary_example :
  odd_incidence_is_mod2_boundary 1.
Proof. apply mod2_endpoint_is_boundary. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ll_matrix_touches_endpoint_witness.
Print Assumptions endpoint_contact_share.
Print Assumptions jts1175_boundary_cells_preclude_disjoint.
Print Assumptions mod2_boundary_dim_endpoint.
Print Assumptions mod2_boundary_dim_1.
Print Assumptions mod2_boundary_dim_3.