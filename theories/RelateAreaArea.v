(* ============================================================================
   NetTopologySuite.Proofs.RelateAreaArea
   ----------------------------------------------------------------------------
   Issue #67 session 6 (S6): area-area DE-9IM witness matrices — rectangles.

   Defines, for two axis-aligned rectangle polygons (no holes), one
   hand-specified DE-9IM witness matrix per regime, and proves each satisfies
   the named predicate from `DE9IM.v`:

     - horizontally separated rectangles → `Disjoint` witness
     - proper partial overlap (2-d interior intersection) → `Overlaps` witness
       (`pat_overlaps_pp_aa`, II=2 BB=1 EE=2) + `Intersects`
     - strict containment (inner rectangle in outer open box) → `Contains`
       witness + `Intersects`
     - vertical edge touch (shared boundary segment) → `Touches` witness
       (`pat_touches_1`, BB=1)

   These are constant witness facts; the regime predicates name the intended
   geometry but are NOT consumed (this file does not derive a matrix from the
   geometry).  Honest scoping: single-ring rectangles, no holes.  The
   regime→witness selection is `RelateMatrixRect.v` (S7); proving a witness is
   S13: cases integrated into RelateNG pipeline (geometry→matrix bridge).

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

(* Symmetric horizontal shared-edge touch (A below B: A's top edge touches B's bottom edge,
   with x-ranges overlapping). This completes the "full rect family" for boundary touch
   (vertical + horizontal). The resulting DE-9IM matrix shape is identical (BB=1, EE=2). *)
Definition rects_touch_horizontal_edge (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R) : Prop :=
  ax0 < ax1 /\ ay0 < ay1 /\ bx0 < bx1 /\ by0 < by1 /\
  ay1 = by0 /\
  ax0 < bx1 /\ bx0 < ax1.

(* -------------------------------------------------------------------------- *)
(* Hand-specified witness matrices (regime targets, not derived from geometry).*)
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
(* The witness facts above (`aa_matrix_*_witness` / `_intersects`) are the     *)
(* honest content: each constant matrix satisfies its DE-9IM predicate.  No    *)
(* `geometry → matrix` theorem is stated, because none is proved — the regime  *)
(* predicates (`rects_separated_horiz`, `rects_partial_overlap`, …) only name  *)
(* which witness `RelateMatrixRect.v` selects.                                 *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions aa_matrix_disjoint_witness.
Print Assumptions aa_matrix_partial_overlap_witness.
Print Assumptions aa_matrix_contains_witness.
Print Assumptions aa_matrix_touch_vertical_witness.