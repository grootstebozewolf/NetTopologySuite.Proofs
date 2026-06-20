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
   Polygon-envelope early-exit soundness (`rect_envelope_disjoint_all_edges`) is
   queued as S14b follow-up.

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

End AreaLinePrepared.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions prepared_area_line_intersects_eq_brute.