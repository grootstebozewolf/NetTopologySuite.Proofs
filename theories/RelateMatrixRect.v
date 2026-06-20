(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixRect
   ----------------------------------------------------------------------------
   Issue #67 session 7 (S7): rect×rect regime→witness selection.

   A regime-indexed function `rect_pair_fill` that SELECTS (does not compute
   from geometry) one of the S6 witness matrices from `RelateAreaArea.v` per
   `RectPairRegime`.  Deciding a regime from rectangle bounds, and proving the
   selected witness is the configuration's true DE-9IM, is the deferred
   RelateNG step; this file does neither.

   Delivers:

     - `RectPairRegime` + `rect_pair_fill` (regime → witness matrix)
     - `classify_rect_pair` recording which S6 geometry guard names each regime
     - Fill = witness equalities
     - `*_fill_witness`: the selected witness satisfies the regime's predicate
       (constant facts; the regime hypothesis is NOT consumed)
     - Mutual-exclusion lemmas (genuine geometry, via `lra` on the bounds) for
       strict-disjoint vs overlap / touch / contains

   Honest scoping: axis-aligned rectangles, no holes; not full RelateNG noding.
   Area-line selection, oracle `RELATE_MATRIX`, arc/clothoid carriers are S8+.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance RelateAreaArea.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Regime enum + matrix fill.                                                 *)
(* -------------------------------------------------------------------------- *)

Inductive RectPairRegime : Type :=
| RPR_Disjoint
| RPR_Overlap
| RPR_Contains
| RPR_TouchVert
| RPR_TouchHoriz.  (* horizontal shared edge; matrix shape identical to TouchVert *)

Definition rect_pair_fill (r : RectPairRegime) : IntersectionMatrix :=
  match r with
  | RPR_Disjoint    => aa_matrix_disjoint
  | RPR_Overlap     => aa_matrix_partial_overlap
  | RPR_Contains    => aa_matrix_contains
  | RPR_TouchVert   => aa_matrix_touch_vertical
  | RPR_TouchHoriz  => aa_matrix_touch_vertical  (* same BB=1 / EE=2 shape *)
  end.

Lemma rect_pair_fill_disjoint_eq :
  rect_pair_fill RPR_Disjoint = aa_matrix_disjoint.
Proof. reflexivity. Qed.

Lemma rect_pair_fill_overlap_eq :
  rect_pair_fill RPR_Overlap = aa_matrix_partial_overlap.
Proof. reflexivity. Qed.

Lemma rect_pair_fill_contains_eq :
  rect_pair_fill RPR_Contains = aa_matrix_contains.
Proof. reflexivity. Qed.

Lemma rect_pair_fill_touch_eq :
  rect_pair_fill RPR_TouchVert = aa_matrix_touch_vertical.
Proof. reflexivity. Qed.

Lemma rect_pair_fill_touch_horiz_eq :
  rect_pair_fill RPR_TouchHoriz = aa_matrix_touch_vertical.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Classifier — mirrors S6 guards.                                            *)
(* -------------------------------------------------------------------------- *)

Definition classify_rect_pair (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R)
    (r : RectPairRegime) : Prop :=
  match r with
  | RPR_Disjoint    => rects_separated_horiz ax0 ay0 ax1 ay1 bx0 by0 bx1 by1
  | RPR_Overlap     => rects_partial_overlap ax0 ay0 ax1 ay1 bx0 by0 bx1 by1
  | RPR_Contains    => rect_a_strictly_contains_rect_b ax0 ay0 ax1 ay1 bx0 by0 bx1 by1
  | RPR_TouchVert   => rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1
  | RPR_TouchHoriz  => rects_touch_horizontal_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1
  end.

(* Strict horizontal separation (classifier discrimination; S6 disjoint
   allows `ax1 = bx0` for closed-interval bookkeeping). *)
Definition rects_strictly_separated_horiz (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R) : Prop :=
  rects_separated_horiz ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 /\
  ax1 < bx0.

Lemma overlap_bx0_lt_ax1 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_partial_overlap ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    bx0 < ax1.
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hov.
  unfold rects_partial_overlap in Hov.
  tauto.
Qed.

Lemma contains_bx1_lt_ax1 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rect_a_strictly_contains_rect_b ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    bx1 < ax1.
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hcont.
  unfold rect_a_strictly_contains_rect_b in Hcont.
  tauto.
Qed.

Lemma overlap_bx1_gt_ax1 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_partial_overlap ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    ax1 < bx1.
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hov.
  unfold rects_partial_overlap in Hov.
  tauto.
Qed.

Lemma touch_ax1_eq_bx0 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    ax1 = bx0.
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch.
  unfold rects_touch_vertical_edge in Htouch.
  tauto.
Qed.

Lemma contains_bx0_gt_ax0 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rect_a_strictly_contains_rect_b ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    ax0 < bx0.
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hcont.
  unfold rect_a_strictly_contains_rect_b in Hcont.
  tauto.
Qed.

Lemma overlap_not_strictly_separated :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_partial_overlap ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    ~ rects_strictly_separated_horiz ax0 ay0 ax1 ay1 bx0 by0 bx1 by1.
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hov [Hsep Hstrict].
  pose proof (overlap_bx0_lt_ax1 ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hov) as Hbx.
  lra.
Qed.

Lemma contains_not_overlap :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rect_a_strictly_contains_rect_b ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    ~ rects_partial_overlap ax0 ay0 ax1 ay1 bx0 by0 bx1 by1.
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hcont Hov.
  pose proof (contains_bx1_lt_ax1 ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hcont) as Hlt.
  pose proof (overlap_bx1_gt_ax1 ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hov) as Hgt.
  lra.
Qed.

Lemma touch_not_overlap :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    ~ rects_partial_overlap ax0 ay0 ax1 ay1 bx0 by0 bx1 by1.
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch Hov.
  pose proof (touch_ax1_eq_bx0 ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch) as Heq.
  pose proof (overlap_bx0_lt_ax1 ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hov) as Hbx.
  subst bx0. lra.
Qed.

Lemma touch_not_contains :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    ~ rect_a_strictly_contains_rect_b ax0 ay0 ax1 ay1 bx0 by0 bx1 by1.
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch Hcont.
  pose proof (touch_ax1_eq_bx0 ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch) as Heq.
  pose proof (contains_bx1_lt_ax1 ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hcont) as Hb1lt.
  unfold rect_a_strictly_contains_rect_b in Hcont.
  repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end.
  subst bx0. lra.
Qed.

Lemma strict_sep_not_overlap :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_strictly_separated_horiz ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    ~ rects_partial_overlap ax0 ay0 ax1 ay1 bx0 by0 bx1 by1.
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 [_ Hstrict] Hov.
  pose proof (overlap_bx0_lt_ax1 ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Hov) as Hbx.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Witness facts: the selected witness satisfies the regime's predicate.      *)
(*                                                                            *)
(* Constant facts about `rect_pair_fill` (a regime → matrix map); they take no *)
(* geometry hypothesis and make no geometry→matrix claim.  That a rectangle    *)
(* pair actually falls in a regime, and that the selected witness is then its  *)
(* true DE-9IM, is the deferred RelateNG step.                                 *)
(* -------------------------------------------------------------------------- *)

Theorem rect_fill_disjoint_witness :
  im_disjoint (rect_pair_fill RPR_Disjoint).
Proof.
  rewrite rect_pair_fill_disjoint_eq. exact aa_matrix_disjoint_witness.
Qed.

Theorem rect_fill_overlap_witness :
  im_overlaps (rect_pair_fill RPR_Overlap) /\
  im_intersects (rect_pair_fill RPR_Overlap).
Proof.
  rewrite rect_pair_fill_overlap_eq.
  split; [exact aa_matrix_partial_overlap_witness | exact aa_matrix_partial_overlap_intersects].
Qed.

Theorem rect_fill_contains_witness :
  im_contains (rect_pair_fill RPR_Contains) /\
  im_intersects (rect_pair_fill RPR_Contains).
Proof.
  rewrite rect_pair_fill_contains_eq.
  split; [exact aa_matrix_contains_witness | exact aa_matrix_contains_intersects].
Qed.

Theorem rect_fill_touch_witness :
  im_touches (rect_pair_fill RPR_TouchVert).
Proof.
  rewrite rect_pair_fill_touch_eq. exact aa_matrix_touch_vertical_witness.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions rect_fill_disjoint_witness.
Print Assumptions rect_fill_overlap_witness.
Print Assumptions rect_fill_contains_witness.
Print Assumptions rect_fill_touch_witness.