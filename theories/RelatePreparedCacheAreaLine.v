(* ============================================================================
   NetTopologySuite.Proofs.RelatePreparedCacheAreaLine
   ----------------------------------------------------------------------------
   Issue #67 session 14 (S14): area-line prepared-cache concrete instance.

   NTS#819 / JTS#1099 prepared area-line mode indexes the polygon boundary
   segments once (`prepare(A)`), then each `evaluate(B)` queries the STRtree
   with the line envelope and tests candidates.  This module instantiates the
   S13 generic refinement for that carrier: rectangle boundary edges as the
   indexed item list and a closed query segment as the envelope source.

   Two layers:
     - CARRIER: `rect_boundary_segments` — the four edges of
       `RelateAreaPoint.rect_polygon`, aligned with `RectangleJCT.ring_edges_rect`.
     - REFINEMENT: `prepared_area_line_intersects_eq_brute` — prepared candidate
       enumeration equals brute force over all boundary edges, for any sound
       segment-intersection test (the LineIntersector hook).
   S14b: polygon-envelope early-exit soundness (`rect_envelope_disjoint_all_edges`)
   — if the rectangle envelope and the query-segment envelope are disjoint, no
   boundary edge can meet the query segment.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Permutation Reals Lra Bool.
From NTS.Proofs Require Import Distance Segment Bbox Overlay RectangleJCT
  RelatePreparedCache.
Import ListNotations.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Rectangle boundary as indexed segments (the prepared-area item list).        *)
(* -------------------------------------------------------------------------- *)

Definition edge_to_segment (e : Edge) : Segment :=
  mkSegment (fst e) (snd e).

Definition rect_boundary_segments (x0 y0 x1 y1 : R) : list Segment :=
  map edge_to_segment (ring_edges (rect_ring x0 y0 x1 y1)).

Lemma rect_boundary_segments_ring_edges :
  forall x0 y0 x1 y1,
    rect_boundary_segments x0 y0 x1 y1 =
      map edge_to_segment (ring_edges (rect_ring x0 y0 x1 y1)).
Proof. reflexivity. Qed.

Lemma rect_boundary_segments_four_edges :
  forall x0 y0 x1 y1,
    rect_boundary_segments x0 y0 x1 y1 =
      [ mkSegment (mkPoint x0 y0) (mkPoint x1 y0)
      ; mkSegment (mkPoint x1 y0) (mkPoint x1 y1)
      ; mkSegment (mkPoint x1 y1) (mkPoint x0 y1)
      ; mkSegment (mkPoint x0 y1) (mkPoint x0 y0) ].
Proof.
  intros x0 y0 x1 y1.
  unfold rect_boundary_segments. rewrite ring_edges_rect. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* S14b — polygon-envelope early-exit soundness.                                *)
(* -------------------------------------------------------------------------- *)

Definition bbox_of_rect (x0 y0 x1 y1 : R) : Bbox :=
  mkBbox x0 x1 y0 y1.

Lemma in_bbox_rect_bottom_edge :
  forall x0 y0 x1 y1 Q,
    x0 < x1 -> y0 < y1 ->
    between (mkPoint x0 y0) (mkPoint x1 y0) Q ->
    in_bbox (bbox_of_rect x0 y0 x1 y1) Q.
Proof.
  intros x0 y0 x1 y1 Q Hx01 Hy01 HQ.
  pose proof (between_in_coord_range (mkPoint x0 y0) (mkPoint x1 y0) Q HQ) as [Hx Hy].
  cbn [px py] in Hx, Hy.
  rewrite Rmin_left in Hx by lra.
  rewrite Rmax_right in Hx by lra.
  rewrite Rmin_left, Rmax_left in Hy by lra.
  unfold in_bbox, bbox_of_rect. simpl. lra.
Qed.

Lemma in_bbox_rect_right_edge :
  forall x0 y0 x1 y1 Q,
    x0 < x1 -> y0 < y1 ->
    between (mkPoint x1 y0) (mkPoint x1 y1) Q ->
    in_bbox (bbox_of_rect x0 y0 x1 y1) Q.
Proof.
  intros x0 y0 x1 y1 Q Hx01 Hy01 HQ.
  pose proof (between_in_coord_range (mkPoint x1 y0) (mkPoint x1 y1) Q HQ) as [Hx Hy].
  cbn [px py] in Hx, Hy.
  rewrite Rmin_right, Rmax_right in Hx by lra.
  rewrite Rmin_left in Hy by lra.
  rewrite Rmax_right in Hy by lra.
  unfold in_bbox, bbox_of_rect. simpl. lra.
Qed.

Lemma in_bbox_rect_top_edge :
  forall x0 y0 x1 y1 Q,
    x0 < x1 -> y0 < y1 ->
    between (mkPoint x1 y1) (mkPoint x0 y1) Q ->
    in_bbox (bbox_of_rect x0 y0 x1 y1) Q.
Proof.
  intros x0 y0 x1 y1 Q Hx01 Hy01 HQ.
  pose proof (between_in_coord_range (mkPoint x1 y1) (mkPoint x0 y1) Q HQ) as [Hx Hy].
  cbn [px py] in Hx, Hy.
  rewrite Rmin_right in Hx by lra.
  rewrite Rmax_left in Hx by lra.
  rewrite Rmin_right, Rmax_right in Hy by lra.
  unfold in_bbox, bbox_of_rect. simpl. lra.
Qed.

Lemma in_bbox_rect_left_edge :
  forall x0 y0 x1 y1 Q,
    x0 < x1 -> y0 < y1 ->
    between (mkPoint x0 y1) (mkPoint x0 y0) Q ->
    in_bbox (bbox_of_rect x0 y0 x1 y1) Q.
Proof.
  intros x0 y0 x1 y1 Q Hx01 Hy01 HQ.
  pose proof (between_in_coord_range (mkPoint x0 y1) (mkPoint x0 y0) Q HQ) as [Hx Hy].
  cbn [px py] in Hx, Hy.
  rewrite Rmin_left, Rmax_left in Hx by lra.
  rewrite Rmin_right in Hy by lra.
  rewrite Rmax_left in Hy by lra.
  unfold in_bbox, bbox_of_rect. simpl. lra.
Qed.

Lemma rect_boundary_point_in_bbox :
  forall x0 y0 x1 y1 s Q,
    x0 < x1 -> y0 < y1 ->
    In s (rect_boundary_segments x0 y0 x1 y1) ->
    between (sp0 s) (sp1 s) Q ->
    in_bbox (bbox_of_rect x0 y0 x1 y1) Q.
Proof.
  intros x0 y0 x1 y1 s Q Hx01 Hy01 Hin HQ.
  rewrite rect_boundary_segments_four_edges in Hin.
  destruct Hin as [Heq | [Heq | [Heq | [Heq | Hin0]]]].
  - subst s. eauto using in_bbox_rect_bottom_edge.
  - subst s. eauto using in_bbox_rect_right_edge.
  - subst s. eauto using in_bbox_rect_top_edge.
  - subst s. eauto using in_bbox_rect_left_edge.
  - exfalso. exact Hin0.
Qed.

Lemma rect_bottom_edge_no_line_cross :
  forall x0 y0 x1 y1 t,
    x0 < x1 -> y0 < y1 ->
    bbox_disjoint (bbox_of_rect x0 y0 x1 y1) (bbox_of_seg t) ->
    ~ exists X, between (mkPoint x0 y0) (mkPoint x1 y0) X /\
                 between (sp0 t) (sp1 t) X.
Proof.
  intros x0 y0 x1 y1 t Hx01 Hy01 Hdisj [X [HX HXt]].
  apply (shared_point_implies_not_disjoint
           (bbox_of_rect x0 y0 x1 y1) (bbox_of_seg t) X).
  - apply in_bbox_rect_bottom_edge; assumption.
  - apply bbox_of_seg_contains_between. exact HXt.
  - exact Hdisj.
Qed.

Lemma rect_right_edge_no_line_cross :
  forall x0 y0 x1 y1 t,
    x0 < x1 -> y0 < y1 ->
    bbox_disjoint (bbox_of_rect x0 y0 x1 y1) (bbox_of_seg t) ->
    ~ exists X, between (mkPoint x1 y0) (mkPoint x1 y1) X /\
                 between (sp0 t) (sp1 t) X.
Proof.
  intros x0 y0 x1 y1 t Hx01 Hy01 Hdisj [X [HX HXt]].
  apply (shared_point_implies_not_disjoint
           (bbox_of_rect x0 y0 x1 y1) (bbox_of_seg t) X).
  - apply in_bbox_rect_right_edge; assumption.
  - apply bbox_of_seg_contains_between. exact HXt.
  - exact Hdisj.
Qed.

Lemma rect_top_edge_no_line_cross :
  forall x0 y0 x1 y1 t,
    x0 < x1 -> y0 < y1 ->
    bbox_disjoint (bbox_of_rect x0 y0 x1 y1) (bbox_of_seg t) ->
    ~ exists X, between (mkPoint x1 y1) (mkPoint x0 y1) X /\
                 between (sp0 t) (sp1 t) X.
Proof.
  intros x0 y0 x1 y1 t Hx01 Hy01 Hdisj [X [HX HXt]].
  apply (shared_point_implies_not_disjoint
           (bbox_of_rect x0 y0 x1 y1) (bbox_of_seg t) X).
  - apply in_bbox_rect_top_edge; assumption.
  - apply bbox_of_seg_contains_between. exact HXt.
  - exact Hdisj.
Qed.

Lemma rect_left_edge_no_line_cross :
  forall x0 y0 x1 y1 t,
    x0 < x1 -> y0 < y1 ->
    bbox_disjoint (bbox_of_rect x0 y0 x1 y1) (bbox_of_seg t) ->
    ~ exists X, between (mkPoint x0 y1) (mkPoint x0 y0) X /\
                 between (sp0 t) (sp1 t) X.
Proof.
  intros x0 y0 x1 y1 t Hx01 Hy01 Hdisj [X [HX HXt]].
  apply (shared_point_implies_not_disjoint
           (bbox_of_rect x0 y0 x1 y1) (bbox_of_seg t) X).
  - apply in_bbox_rect_left_edge; assumption.
  - apply bbox_of_seg_contains_between. exact HXt.
  - exact Hdisj.
Qed.

Theorem rect_envelope_disjoint_all_edges :
  forall x0 y0 x1 y1 t,
    x0 < x1 -> y0 < y1 ->
    bbox_disjoint (bbox_of_rect x0 y0 x1 y1) (bbox_of_seg t) ->
    forall s, In s (rect_boundary_segments x0 y0 x1 y1) ->
    ~ exists X, between (sp0 s) (sp1 s) X /\ between (sp0 t) (sp1 t) X.
Proof.
  intros x0 y0 x1 y1 t Hx01 Hy01 Hdisj s Hin.
  rewrite rect_boundary_segments_four_edges in Hin.
  destruct Hin as [Heq | [Heq | [Heq | [Heq | Hin0]]]].
  - subst s. eauto using rect_bottom_edge_no_line_cross.
  - subst s. eauto using rect_right_edge_no_line_cross.
  - subst s. eauto using rect_top_edge_no_line_cross.
  - subst s. eauto using rect_left_edge_no_line_cross.
  - exfalso. exact Hin0.
Qed.

(* -------------------------------------------------------------------------- *)
(* Area-line prepared intersects refinement (S13 segment instance applied).     *)
(* -------------------------------------------------------------------------- *)

Section AreaLinePrepared.

  Variables (x0 y0 x1 y1 : R).
  Hypothesis Hrect : x0 < x1 /\ y0 < y1.

  Variable intersect_test : Segment -> Segment -> bool.
  Hypothesis intersect_test_sound :
    forall s t, intersect_test s t = true ->
      exists X, between (sp0 s) (sp1 s) X /\ between (sp0 t) (sp1 t) X.

  Variable t : Segment.

  Let a_edges := rect_boundary_segments x0 y0 x1 y1.
  Let qb := bbox_of_seg t.
  Let contrib (s : Segment) : bool := intersect_test s t.

  Definition area_line_intersects_brute : bool :=
    fold_right orb false (map contrib a_edges).

  Definition area_line_intersects_prepared (q : list Segment) : bool :=
    fold_right orb false (map contrib q).

  Lemma area_line_intersects_drop_sound :
    forall s, bbox_overlap_keep qb s = false -> contrib s = false.
  Proof.
    intros s Hk. unfold contrib.
    destruct (intersect_test s t) eqn:Hit; [exfalso | reflexivity].
    apply (disjoint_bboxes_imply_no_shared_point s t).
    - exact (keep_false_disjoint qb s Hk).
    - exact (intersect_test_sound s t Hit).
  Qed.

  Theorem prepared_area_line_intersects_eq_brute :
    forall q,
      Permutation q (filter (bbox_overlap_keep qb) a_edges) ->
      area_line_intersects_prepared q = area_line_intersects_brute.
  Proof.
    intros q Hq. unfold area_line_intersects_prepared, area_line_intersects_brute.
    rewrite <- (fold_filter_drop orb false contrib (bbox_overlap_keep qb)
      orb_false_l area_line_intersects_drop_sound a_edges).
    apply (fold_right_permutation orb false orb_comm); auto using Permutation_map.
    intros x y z. destruct x, y, z; reflexivity.
  Qed.

  Corollary prepared_area_line_intersects_path_independent :
    forall q1 q2,
      Permutation q1 (filter (bbox_overlap_keep qb) a_edges) ->
      Permutation q2 (filter (bbox_overlap_keep qb) a_edges) ->
      area_line_intersects_prepared q1 = area_line_intersects_prepared q2.
  Proof.
    intros q1 q2 H1 H2.
    rewrite (prepared_area_line_intersects_eq_brute q1 H1),
            (prepared_area_line_intersects_eq_brute q2 H2). reflexivity.
  Qed.

  Lemma orb_map_all_false :
    forall (l : list Segment),
      (forall s, In s l -> contrib s = false) ->
      fold_right orb false (map contrib l) = false.
  Proof.
    induction l as [| s l IH]; simpl.
    - intros _. reflexivity.
    - intros Hall.
      assert (Hfs : contrib s = false) by (apply Hall; cbn; auto).
      rewrite Hfs, Bool.orb_false_l. apply IH.
      intros s' Hin'. apply Hall. cbn. auto.
  Qed.

  Theorem prepared_area_line_envelope_early_exit :
    bbox_disjoint (bbox_of_rect x0 y0 x1 y1) qb ->
    area_line_intersects_brute = false.
  Proof.
    intros Henv.
    unfold area_line_intersects_brute.
    apply orb_map_all_false. intros s Hin.
    unfold contrib.
    destruct (intersect_test s t) eqn:Hit; [exfalso | reflexivity].
    apply (intersect_test_sound s t) in Hit.
    destruct Hit as [X [HXs HXt]].
    destruct Hrect as [Hx01' Hy01'].
    apply (rect_envelope_disjoint_all_edges x0 y0 x1 y1 t Hx01' Hy01' Henv s Hin).
    exists X; split; assumption.
  Qed.

End AreaLinePrepared.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions prepared_area_line_intersects_eq_brute.
Print Assumptions rect_envelope_disjoint_all_edges.
Print Assumptions prepared_area_line_envelope_early_exit.