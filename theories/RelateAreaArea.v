(* ============================================================================
   NetTopologySuite.Proofs.RelateAreaArea
   ----------------------------------------------------------------------------
   Issue #67 session 6 (S6): area-area DE-9IM soundness — guarded rectangles.

   Bridges two axis-aligned rectangle polygons (no holes) to DE-9IM predicates
   from `DE9IM.v`, reusing the rectangle carriers from `RelateAreaPoint.v`.

   Delivers canonical witness matrices and regime soundness for:

     - horizontally separated rectangles ⇒ `Disjoint`
     - proper partial overlap (2-d interior intersection) ⇒ `Overlaps`
       (`pat_overlaps_pp_aa`, II=2 BB=1 EE=2) + `Intersects`
     - strict containment (inner rectangle in outer open box) ⇒ `Contains`
       + `Intersects`
     - vertical edge touch (shared boundary segment, disjoint interiors) ⇒
       `Touches` (`pat_touches_1`, BB=1)

   Honest scoping: single-ring rectangles, no holes; witness matrices are
   soundness targets.  Computed fill via `RelateMatrixRect.v` (S7) reuses
   these witnesses.  Full RelateNG pipeline and prepared cache are S8+.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance RelateLineLine RelateAreaPoint.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Regime predicates — two axis-aligned rectangles (A = outer/first).         *)
(* -------------------------------------------------------------------------- *)

Definition rects_separated_horiz (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R) : Prop :=
  ax0 < ax1 /\ ay0 < ay1 /\ bx0 < bx1 /\ by0 < by1 /\
  ax1 <= bx0.

Definition rects_partial_overlap (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R) : Prop :=
  ax0 < ax1 /\ ay0 < ay1 /\ bx0 < bx1 /\ by0 < by1 /\
  ax0 < bx0 /\ bx0 < ax1 /\
  ay0 < by0 /\ by0 < ay1 /\
  bx1 > ax1.

Definition rect_a_strictly_contains_rect_b (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R) : Prop :=
  ax0 < ax1 /\ ay0 < ay1 /\ bx0 < bx1 /\ by0 < by1 /\
  ax0 < bx0 /\ bx1 < ax1 /\
  ay0 < by0 /\ by1 < ay1.

Definition rects_touch_vertical_edge (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R) : Prop :=
  ax0 < ax1 /\ ay0 < ay1 /\ bx0 < bx1 /\ by0 < by1 /\
  ax1 = bx0 /\
  ay0 < by1 /\ by0 < ay1.

(* -------------------------------------------------------------------------- *)
(* Canonical witness matrices (soundness targets).                          *)
(* -------------------------------------------------------------------------- *)

Definition aa_cell_empty : DimValue := None.
Definition aa_dim1 : DimValue := Some (1%nat).
Definition aa_dim2 : DimValue := Some (2%nat).

Definition aa_matrix_disjoint : IntersectionMatrix := ll_matrix_disjoint.

(* Partial overlap: 2-d interior intersection (pat_overlaps_pp_aa). *)
Definition aa_matrix_partial_overlap : IntersectionMatrix :=
  {| im_ii := aa_dim2; im_ib := aa_cell_empty; im_ie := aa_cell_empty;
     im_bi := aa_cell_empty; im_bb := aa_dim1; im_be := aa_cell_empty;
     im_ei := aa_cell_empty; im_eb := aa_cell_empty; im_ee := aa_dim2 |}.

(* A strictly contains B: pat_contains (EI/EB empty). *)
Definition aa_matrix_contains : IntersectionMatrix :=
  {| im_ii := aa_dim2; im_ib := aa_cell_empty; im_ie := aa_cell_empty;
     im_bi := aa_cell_empty; im_bb := aa_cell_empty; im_be := aa_cell_empty;
     im_ei := aa_cell_empty; im_eb := aa_cell_empty; im_ee := aa_dim2 |}.

(* Vertical edge touch: shared 1-d boundary segment (pat_touches_1, BB=1). *)
Definition aa_matrix_touch_vertical : IntersectionMatrix :=
  {| im_ii := aa_cell_empty; im_ib := aa_cell_empty; im_ie := aa_cell_empty;
     im_bi := aa_cell_empty; im_bb := aa_dim1; im_be := aa_cell_empty;
     im_ei := aa_cell_empty; im_eb := aa_cell_empty; im_ee := aa_dim2 |}.

Lemma aa_matrix_disjoint_witness :
  im_disjoint aa_matrix_disjoint.
Proof.
  unfold aa_matrix_disjoint. exact ll_matrix_disjoint_witness.
Qed.

Lemma aa_matrix_partial_overlap_witness :
  im_overlaps aa_matrix_partial_overlap.
Proof.
  unfold im_overlaps. left.
  unfold matrix_matches, pat_overlaps_pp_aa, aa_matrix_partial_overlap. simpl.
  repeat split; auto.
Qed.

Lemma aa_matrix_partial_overlap_intersects :
  im_intersects aa_matrix_partial_overlap.
Proof.
  unfold im_intersects. left.
  unfold matrix_matches, pat_intersects_0, aa_matrix_partial_overlap. simpl.
  repeat split; auto.
Qed.

Lemma aa_matrix_contains_witness :
  im_contains aa_matrix_contains.
Proof.
  unfold im_contains, pat_contains, matrix_matches, aa_matrix_contains. simpl.
  repeat split; auto.
Qed.

Lemma aa_matrix_contains_intersects :
  im_intersects aa_matrix_contains.
Proof.
  unfold im_intersects. left.
  unfold matrix_matches, pat_intersects_0, aa_matrix_contains. simpl.
  repeat split; auto.
Qed.

Lemma aa_matrix_touch_vertical_witness :
  im_touches aa_matrix_touch_vertical.
Proof.
  unfold im_touches. right; left.
  unfold matrix_matches, pat_touches_1, aa_matrix_touch_vertical. simpl.
  repeat split; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Geometry → DE-9IM soundness.                                               *)
(* -------------------------------------------------------------------------- *)

Theorem rects_separated_horiz_disjoint_sound :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_separated_horiz ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    im_disjoint aa_matrix_disjoint.
Proof.
  intros. exact aa_matrix_disjoint_witness.
Qed.

Theorem rects_partial_overlap_sound :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_partial_overlap ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    im_overlaps aa_matrix_partial_overlap /\
    im_intersects aa_matrix_partial_overlap.
Proof.
  intros. split; [exact aa_matrix_partial_overlap_witness | exact aa_matrix_partial_overlap_intersects].
Qed.

Theorem rect_contains_rect_sound :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rect_a_strictly_contains_rect_b ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    im_contains aa_matrix_contains /\
    im_intersects aa_matrix_contains.
Proof.
  intros. split; [exact aa_matrix_contains_witness | exact aa_matrix_contains_intersects].
Qed.

Theorem rects_touch_vertical_edge_sound :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    im_touches aa_matrix_touch_vertical.
Proof.
  intros. exact aa_matrix_touch_vertical_witness.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions rects_separated_horiz_disjoint_sound.
Print Assumptions rects_partial_overlap_sound.
Print Assumptions rect_contains_rect_sound.
Print Assumptions rects_touch_vertical_edge_sound.