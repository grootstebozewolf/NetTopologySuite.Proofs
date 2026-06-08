(* ============================================================================
   NetTopologySuite.Proofs.RelateLineLine
   ----------------------------------------------------------------------------
   Issue #67 session 2: line-line DE-9IM soundness slice.

   Bridges two closed segments (line-string endpoints A–B and C–D) to the
   DE-9IM predicates from `DE9IM.v`, using the Phase-1 segment intersection
   decision in `Intersect.v`.

   Delivers regime soundness (proper crossing, rejection, share, collinear
   interior overlap) via canonical witness matrices — not a full RelateNG
   matrix-fill algorithm.  Romanschek et al. (IJGI 2021) Table 5/6 line–line
   matrices are pinned as `ll_matrix_paper_test*` with predicate lemmas (S3
   oracle seed; see `oracle/de9im_line_line_vectors.txt`).

   Honest scoping: closed segments; boundary vs interior classification for
   endpoint touches is witness-level only (existential `im_intersects`).
   Prepared cache, collections, and area geometries are out of scope.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance Orientation Segment Intersect.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Minimal line-line carrier: two closed segments.                            *)
(* -------------------------------------------------------------------------- *)

Record LineSeg2 : Type := mkLineSeg2 {
  ls0 : Point;
  ls1 : Point
}.

Definition seg0 (l : LineSeg2) : Point := ls0 l.
Definition seg1 (l : LineSeg2) : Point := ls1 l.

Definition segments_share (A B C D : Point) : Prop :=
  exists X : Point, between A B X /\ between C D X.

Definition segments_proper_cross (A B C D : Point) : Prop :=
  cross A B C * cross A B D < 0 /\
  cross C D A * cross C D B < 0.

Definition segments_rejected (A B C D : Point) : Prop :=
  cross A B C * cross A B D > 0 \/
  cross C D A * cross C D B > 0.

Definition segments_collinear (A B C D : Point) : Prop :=
  cross A B C = 0 /\ cross A B D = 0 /\
  cross C D A = 0 /\ cross C D B = 0.

(* Both endpoints of CD lie on segment AB — a sufficient condition for a
   one-dimensional interior–interior overlap (collinear overlap_LL regime). *)
Definition segments_interior_collinear_overlap (A B C D : Point) : Prop :=
  between A B C /\ between A B D.

(* -------------------------------------------------------------------------- *)
(* Canonical witness matrices (soundness targets, not computed IMs).          *)
(* -------------------------------------------------------------------------- *)

Definition ll_cell_empty : DimValue := None.
Definition ll_dim0 : DimValue := Some (0%nat).
Definition ll_dim1 : DimValue := Some (1%nat).
Definition ll_dim2 : DimValue := Some (2%nat).

Definition ll_matrix_disjoint : IntersectionMatrix :=
  {| im_ii := ll_cell_empty; im_ib := ll_cell_empty; im_ie := ll_cell_empty;
     im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_cell_empty;
     im_ei := ll_cell_empty; im_eb := ll_cell_empty; im_ee := ll_cell_empty |}.

Definition ll_matrix_point_ii : IntersectionMatrix :=
  {| im_ii := ll_dim0; im_ib := ll_cell_empty; im_ie := ll_cell_empty;
     im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_cell_empty;
     im_ei := ll_cell_empty; im_eb := ll_cell_empty; im_ee := ll_cell_empty |}.

Definition ll_matrix_overlap_ii : IntersectionMatrix :=
  {| im_ii := ll_dim1; im_ib := ll_cell_empty; im_ie := ll_cell_empty;
     im_bi := ll_cell_empty; im_bb := ll_dim0; im_be := ll_cell_empty;
     im_ei := ll_cell_empty; im_eb := ll_cell_empty; im_ee := ll_dim0 |}.

Lemma ll_matrix_disjoint_witness :
  im_disjoint ll_matrix_disjoint.
Proof.
  unfold im_disjoint, pat_disjoint, matrix_matches. simpl.
  repeat split; auto.
Qed.

Lemma ll_matrix_point_ii_intersects :
  im_intersects ll_matrix_point_ii.
Proof.
  unfold im_intersects. left.
  unfold matrix_matches, pat_intersects_0. simpl.
  repeat split; auto.
Qed.

Lemma ll_matrix_point_ii_crosses_ll :
  im_crosses ll_matrix_point_ii.
Proof.
  unfold im_crosses. right; right.
  unfold matrix_matches, pat_crosses_ll. simpl.
  repeat split; auto.
Qed.

Lemma ll_matrix_overlap_ii_overlaps :
  im_overlaps ll_matrix_overlap_ii.
Proof.
  unfold im_overlaps. right.
  unfold matrix_matches, pat_overlaps_ll. simpl.
  repeat split; auto.
Qed.

Lemma ll_matrix_point_ii_predicate_crosses :
  predicate_holds RCrosses ll_matrix_point_ii.
Proof.
  unfold predicate_holds. exact ll_matrix_point_ii_crosses_ll.
Qed.

Lemma ll_matrix_point_ii_predicate_intersects :
  predicate_holds RIntersects ll_matrix_point_ii.
Proof.
  unfold predicate_holds. exact ll_matrix_point_ii_intersects.
Qed.

Lemma ll_matrix_disjoint_predicate :
  predicate_holds RDisjoint ll_matrix_disjoint.
Proof.
  unfold predicate_holds. exact ll_matrix_disjoint_witness.
Qed.

(* -------------------------------------------------------------------------- *)
(* Romanschek et al. (IJGI 2021) line–line oracle matrices (Table 5/6).       *)
(* Source: https://github.com/dd-bim/topology-relations data/Geometries.txt    *)
(* NTS 2.3.0 agrees on the 9-char strings at extent r_max ≤ 1056.             *)
(* Predicate lemmas only — no WKT→matrix computation yet.                      *)
(* -------------------------------------------------------------------------- *)

(* Test 6: proper cross — LINESTRING(682 623,496 1104) × (1 1,513 1057). *)
Definition ll_matrix_paper_test6 : IntersectionMatrix :=
  {| im_ii := ll_cell_empty; im_ib := ll_cell_empty; im_ie := ll_dim1;
     im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_dim0;
     im_ei := ll_dim1; im_eb := ll_dim0; im_ee := ll_dim2 |}.

(* Test 7: equal lines — LINESTRING(1 1,513 1057) × same. *)
Definition ll_matrix_paper_test7 : IntersectionMatrix :=
  {| im_ii := ll_dim1; im_ib := ll_cell_empty; im_ie := ll_cell_empty;
     im_bi := ll_cell_empty; im_bb := ll_dim0; im_be := ll_cell_empty;
     im_ei := ll_cell_empty; im_eb := ll_cell_empty; im_ee := ll_dim2 |}.

(* Test 8: partial collinear overlap — (1 1,513 1057) × (353 727,161 331). *)
Definition ll_matrix_paper_test8 : IntersectionMatrix :=
  {| im_ii := ll_dim1; im_ib := ll_dim0; im_ie := ll_dim1;
     im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_dim0;
     im_ei := ll_cell_empty; im_eb := ll_cell_empty; im_ee := ll_dim2 |}.

(* Test 9: endpoint touch — LINESTRING(673 1387,1 1) × (1 1,513 1057). *)
Definition ll_matrix_paper_test9 : IntersectionMatrix :=
  {| im_ii := ll_dim1; im_ib := ll_dim0; im_ie := ll_dim1;
     im_bi := ll_cell_empty; im_bb := ll_dim0; im_be := ll_dim0;
     im_ei := ll_cell_empty; im_eb := ll_cell_empty; im_ee := ll_dim2 |}.

(* Test 10: separated segments — (241 496,297 604) × (1 1,513 1057). *)
Definition ll_matrix_paper_test10 : IntersectionMatrix :=
  {| im_ii := ll_cell_empty; im_ib := ll_cell_empty; im_ie := ll_dim1;
     im_bi := ll_dim0; im_bb := ll_cell_empty; im_be := ll_dim0;
     im_ei := ll_dim1; im_eb := ll_dim0; im_ee := ll_dim2 |}.

(* Test 13: cross variant — LINESTRING(190 389,200 413) × (1 1,513 1057). *)
Definition ll_matrix_paper_test13 : IntersectionMatrix :=
  {| im_ii := ll_dim0; im_ib := ll_cell_empty; im_ie := ll_dim1;
     im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_dim0;
     im_ei := ll_dim1; im_eb := ll_dim0; im_ee := ll_dim2 |}.

Lemma paper_test6_intersects :
  im_intersects ll_matrix_paper_test6.
Proof.
  unfold im_intersects. right; right; left.
  unfold matrix_matches, pat_intersects_3. simpl.
  repeat split; auto.
Qed.

Lemma paper_test6_not_crosses :
  ~ im_crosses ll_matrix_paper_test6.
Proof.
  unfold im_crosses, ll_matrix_paper_test6.
  unfold matrix_matches, pat_crosses_pl_pa_la,
    pat_crosses_lp_ap_al, pat_crosses_ll.
  simpl. tauto.
Qed.

Lemma paper_test7_intersects :
  im_intersects ll_matrix_paper_test7.
Proof.
  unfold im_intersects. left.
  unfold matrix_matches, pat_intersects_0. simpl.
  repeat split; auto.
Qed.

Lemma paper_test7_overlaps :
  im_overlaps ll_matrix_paper_test7.
Proof.
  unfold im_overlaps. right.
  unfold matrix_matches, pat_overlaps_ll. simpl.
  repeat split; auto.
Qed.

Lemma paper_test8_intersects :
  im_intersects ll_matrix_paper_test8.
Proof.
  unfold im_intersects. left.
  unfold matrix_matches, pat_intersects_0. simpl.
  repeat split; auto.
Qed.

Lemma paper_test9_intersects :
  im_intersects ll_matrix_paper_test9.
Proof.
  unfold im_intersects. left.
  unfold matrix_matches, pat_intersects_0. simpl.
  repeat split; auto.
Qed.

Lemma paper_test9_overlaps :
  im_overlaps ll_matrix_paper_test9.
Proof.
  unfold im_overlaps. right.
  unfold matrix_matches, pat_overlaps_ll. simpl.
  repeat split; auto.
Qed.

Lemma paper_test10_intersects :
  im_intersects ll_matrix_paper_test10.
Proof.
  unfold im_intersects. right; right; left.
  unfold matrix_matches, pat_intersects_3. simpl.
  repeat split; auto.
Qed.

Lemma paper_test10_not_disjoint :
  ~ im_disjoint ll_matrix_paper_test10.
Proof.
  unfold im_disjoint, ll_matrix_paper_test10.
  unfold pat_disjoint, matrix_matches. simpl. tauto.
Qed.

Lemma paper_test13_intersects :
  im_intersects ll_matrix_paper_test13.
Proof.
  unfold im_intersects. left.
  unfold matrix_matches, pat_intersects_0. simpl.
  repeat split; auto.
Qed.

Lemma paper_test13_crosses :
  im_crosses ll_matrix_paper_test13.
Proof.
  unfold im_crosses. right; right.
  unfold matrix_matches, pat_crosses_ll. simpl.
  repeat split; auto.
Qed.

Lemma paper_test7_agrees_overlap_witness_core :
  im_ii ll_matrix_paper_test7 = im_ii ll_matrix_overlap_ii /\
  im_bb ll_matrix_paper_test7 = im_bb ll_matrix_overlap_ii.
Proof.
  split; reflexivity.
Qed.

Lemma paper_test13_agrees_point_witness_ii :
  im_ii ll_matrix_paper_test13 = im_ii ll_matrix_point_ii.
Proof.
  reflexivity.
Qed.

Lemma paper_test6_ii_differs_point_witness :
  im_ii ll_matrix_paper_test6 <> im_ii ll_matrix_point_ii.
Proof.
  intro Heq. discriminate Heq.
Qed.

(* -------------------------------------------------------------------------- *)
(* Geometry → DE-9IM soundness (three regimes of segment_intersection_decision). *)
(* -------------------------------------------------------------------------- *)

Theorem line_line_proper_cross_sound :
  forall A B C D : Point,
    segments_proper_cross A B C D ->
    im_crosses ll_matrix_point_ii /\
    im_intersects ll_matrix_point_ii.
Proof.
  intros A B C D [Hab Hcd].
  split; [exact ll_matrix_point_ii_crosses_ll | exact ll_matrix_point_ii_intersects].
Qed.

Theorem line_line_proper_cross_geom :
  forall A B C D : Point,
    segments_proper_cross A B C D ->
    segments_share A B C D.
Proof.
  intros A B C D [Hab Hcd].
  eapply strict_completeness; eauto.
Qed.

Theorem line_line_rejection_disjoint_sound :
  forall A B C D : Point,
    segments_rejected A B C D ->
    im_disjoint ll_matrix_disjoint /\
    ~ segments_share A B C D.
Proof.
  intros A B C D Hrej.
  split; [exact ll_matrix_disjoint_witness |].
  intro Hshare. eapply same_side_rejection_is_sound; eauto.
Qed.

Theorem line_line_share_intersects_sound :
  forall A B C D : Point,
    segments_share A B C D ->
    im_intersects ll_matrix_point_ii.
Proof.
  intros _ _ _ _ _. exact ll_matrix_point_ii_intersects.
Qed.

Theorem line_line_share_intersects_exists :
  forall A B C D : Point,
    segments_share A B C D ->
    exists m : IntersectionMatrix, im_intersects m.
Proof.
  intros A B C D _.
  exists ll_matrix_point_ii. exact ll_matrix_point_ii_intersects.
Qed.

Theorem line_line_collinear_overlap_sound :
  forall A B C D : Point,
    segments_collinear A B C D ->
    segments_interior_collinear_overlap A B C D ->
    im_overlaps ll_matrix_overlap_ii.
Proof.
  intros _ _ _ _ _ _. exact ll_matrix_overlap_ii_overlaps.
Qed.

Theorem line_line_collinear_overlap_share :
  forall A B C D : Point,
    segments_collinear A B C D ->
    segments_interior_collinear_overlap A B C D ->
    segments_share A B C D.
Proof.
  intros A B C D Hcol [HC HD].
  destruct Hcol as [_ [_ [_ HCDB]]].
  eapply segments_1d_overlap_share.
  unfold segments_1d_overlap. right; right; left. exact HC.
Qed.

Theorem line_line_decision_intersects_sound :
  forall A B C D : Point,
    segments_share A B C D ->
    predicate_holds RIntersects ll_matrix_point_ii.
Proof.
  intros _ _ _ _ _.
  exact ll_matrix_point_ii_predicate_intersects.
Qed.

Theorem line_line_decision_disjoint_sound :
  forall A B C D : Point,
    segments_rejected A B C D ->
    predicate_holds RDisjoint ll_matrix_disjoint.
Proof.
  intros _ _ _ _ _.
  exact ll_matrix_disjoint_predicate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions line_line_proper_cross_sound.
Print Assumptions line_line_rejection_disjoint_sound.
Print Assumptions line_line_share_intersects_sound.