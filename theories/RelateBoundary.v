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

   Honest scoping: closed segments; the witness matrices are hand-specified
   targets, not derived from geometry and not a RelateNG matrix-fill
   implementation.  Multi-component line collections, area-line, and prepared
   cache are S5+.

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
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ll_matrix_touches_endpoint_witness.
Print Assumptions endpoint_contact_share.
Print Assumptions jts1175_boundary_cells_preclude_disjoint.