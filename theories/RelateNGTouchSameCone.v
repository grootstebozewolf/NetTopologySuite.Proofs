(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchSameCone
   ----------------------------------------------------------------------------
   Leftover Ⅵ: name the leftover-Ⅴ same-sign cone spill.

   Accept as leftover-Ⅵ inhabitance. Reject as a same-cone
   soundness result or an overlap theorem.
   `triangle_pair_regime_samecone` is inhabitance, not soundness.
   `classify_triangle_pair`'s TPR_SameCone arm is True — no
   denotation. There is no TPR_SameCone ⇒ interiors meet.

   Map: docs/scout/map-same-cone-cert.md. Compiled pair
   A = (0,0)(2,0)(0,2), B = (0,0)(3,1)(1,3) is the leftover-Ⅴ
   completeness residue. Shared origin. Cone normal nA = (2,2) puts
   both remaining B vertices strictly positive (side_dot = 8).
   Sibling of leftover Ⅴ (same A; B third vertex (−1,−1) is
   TPR_MixedCone, opposite signs) and of leftover Ⅱ (B third
   vertex (1,−1) is TPR_TouchObtuse, product 0) and of #572
   (B third vertex (0,−2) is TPR_TouchVertex, same-sign opposite
   cone). That taxonomy is real. Detector `same_cone_vertex_b` is
   both-strict-pos plus `negb` of both cones and of
   `mixed_cone_from_v` — not a remint of `cone_separates_b` /
   `touch_vertex_b` / `touch_obtuse_vertex_b` /
   `mixed_cone_vertex_b`. The `negb mixed_cone_from_v` is
   classifier order written twice (`mixed_cone_from_v` is already
   exclusive of `both_strict_pos`). Harmless, not content.
   Constructor `TPR_SameCone` stays on `im_unsupported`
   (load-bearing: do not emit `2FFF1FFF2`; that pin is #570).
   This pair is DE-9IM overlap with a shared vertex and no
   vertex-stab; parking it on a new constructor avoids the fill,
   leftover policy, not a cone theorem. After leftover Ⅴ. False on
   `classified_hard_pairs`, leftover Ⅰ, leftover Ⅱ, leftover Ⅲ,
   leftover Ⅳ, leftover Ⅴ, and the #567 contains pair.
   Completeness stays false on an unnamed lens pair. Leftover `Ⅶ`
   is already written as #642. Relocating
   `triangle_pair_regime_ccw_stop` here does not move #522 closer
   to QED — the #577 disjunction copied into a third file.
   `leftover_vi_qed_or_qex` is classified ∨ declined on the pair
   just classified. `classified_hard_pairs_still_samecone` is
   misnamed: those pairs stay Disjoint / Overlap / TouchVertex /
   TouchEdge. `classify_triangle_pair` arm is `True` — leftover Ⅰ
   honesty, not CONTEXT Bar 1. Nothing that mentions
   `TPR_SameCone` may be proved through `classify_triangle_pair`.
   Do not steal 522-j / 522-m / 522-f / 522-i / leftover Ⅰ /
   leftover Ⅱ / leftover Ⅴ. Do not remint `cone_separates_b` /
   `overlap_b`. Do not mint 522-n. Do not remint aa_matrix_*.

   WITNESS topic: relate · claimId: Ⅵ · witness: Ⅵ-same-cone-cex
   macro: relate
   lane: proofs
   issue: leftover Ⅵ / #522
   ADR-0004: leftover numerals stay off the 522-* board catalog
   (not a partial mint). JSON blob on the headline is the leftover
   tag. Not requesting mutation pins this letter.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

From Stdlib Require Import Reals Lra Bool.
From NTS.Proofs Require Import DE9IM Distance Orientation RelateMatrixTriangle
  GeneralTriangleSeparation
  RelateNGCore RelateNGDisjoint RelateNGTouchVertex RelateNGUnnamedCex
  RelateNGComplete.
Local Open Scope R_scope.

Lemma leftover_I_no_samecone :
  same_cone_vertex_b 0 0 2 0 0 1 1 0 3 0 2 1 = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_II_no_samecone :
  same_cone_vertex_b 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold same_cone_from_v, mixed_cone_from_v, others_fst, others_snd,
         is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold opposite_side_dot_b, closed_cone_separates_b,
         both_closed_pos_b, both_closed_neg_b,
         cone_separates_b, both_strict_pos_b, both_strict_neg_b,
         vec_sum_from, side_dot.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_III_no_samecone :
  same_cone_vertex_b 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1) = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (1/2) (-1) (3/2) (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_IV_no_samecone :
  same_cone_vertex_b 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (5/4) (1/4) (3/4) (1/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_V_no_samecone :
  same_cone_vertex_b 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-1) (-1) 3 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold same_cone_from_v, mixed_cone_from_v, others_fst, others_snd,
         is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold opposite_side_dot_b, closed_cone_separates_b,
         both_closed_pos_b, both_closed_neg_b,
         cone_separates_b, both_strict_pos_b, both_strict_neg_b,
         vec_sum_from, side_dot.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_disjoint_no_samecone :
  same_cone_vertex_b 0 0 1 0 0 1 2 0 3 0 2 1 = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 2 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_overlap_no_samecone :
  same_cone_vertex_b 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
  = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl (1/4) (1/4) (5/4) (1/4) (1/4) (5/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_touchvertex_no_samecone :
  same_cone_vertex_b 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 0 (-2))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold same_cone_from_v, mixed_cone_from_v, others_fst, others_snd,
         is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold opposite_side_dot_b, closed_cone_separates_b,
         both_closed_pos_b, both_closed_neg_b,
         cone_separates_b, both_strict_pos_b, both_strict_neg_b,
         vec_sum_from, side_dot.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_touchedge_no_samecone :
  same_cone_vertex_b 0 0 1 0 0 1 1 0 1 1 0 1 = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 1 1 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_contains_no_samecone :
  same_cone_vertex_b 0 0 1 0 0 1 (1/4) (1/4) (1/2) (1/4) (1/4) (1/2)
  = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl (1/4) (1/4) (1/2) (1/4) (1/4) (1/2))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_VI_samecone_true :
  same_cone_vertex_b 0 0 2 0 0 2 0 0 3 1 1 3 = true.
Proof.
  exact same_cone_vertex_b_true.
Qed.

Lemma classified_hard_pairs_no_samecone :
  same_cone_vertex_b 0 0 1 0 0 1 2 0 3 0 2 1 = false /\
  same_cone_vertex_b 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
  = false /\
  same_cone_vertex_b 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = false /\
  same_cone_vertex_b 0 0 1 0 0 1 1 0 1 1 0 1 = false /\
  same_cone_vertex_b 0 0 1 0 0 1 (1/4) (1/4) (1/2) (1/4) (1/4) (1/2)
  = false.
Proof.
  split; [exact hard_disjoint_no_samecone|].
  split; [exact hard_overlap_no_samecone|].
  split; [exact hard_touchvertex_no_samecone|].
  split; [exact hard_touchedge_no_samecone|].
  exact hard_contains_no_samecone.
Qed.

(* WITNESS {"claimId":"Ⅵ","topic":"relate","lemma":"triangle_pair_regime_samecone","title":"TPR_SameCone inhabitance on the compiled leftover-Ⅵ same-sign spill (not a same-cone denotation)","file":"theories/RelateNGTouchSameCone.v","witness":"Ⅵ-same-cone-cex","board":"leftover-Ⅵ"} *)
Theorem triangle_pair_regime_samecone :
  triangle_pair_regime 0 0 2 0 0 2 0 0 3 1 1 3 = TPR_SameCone.
Proof.
  exact same_cone_pair_samecone.
Qed.

Theorem triangle_pair_regime_samecone_of :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    touch_edge_b (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = false ->
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    touch_partial_edge_b
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = false ->
    touch_onesided_t_b
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = false ->
    touch_obtuse_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    mixed_cone_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    same_cone_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_SameCone.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy He Hc Ho Hs Hv Hp Ho1 Hob Hm Hsc.
  unfold triangle_pair_regime.
  rewrite He, Hc, Ho, Hs, Hv, Hp, Ho1, Hob, Hm, Hsc. reflexivity.
Qed.

Theorem leftover_I_still_partial :
  triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1 = TPR_TouchPartialEdge.
Proof.
  exact tjunction_pair_touch_partial.
Qed.

Theorem leftover_II_still_obtuse :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = TPR_TouchObtuse.
Proof.
  exact obtuse_pair_touch_obtuse.
Qed.

Theorem leftover_III_still_onesided :
  triangle_pair_regime 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1)
    = TPR_TouchOnesided.
Proof.
  exact onesided_t_pair_onesided.
Qed.

Theorem leftover_IV_still_onesided :
  triangle_pair_regime 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4)
    = TPR_TouchOnesided.
Proof.
  exact interior_side_pair_onesided.
Qed.

Theorem leftover_V_still_mixedcone :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = TPR_MixedCone.
Proof.
  exact mixed_cone_pair_mixedcone.
Qed.

(* Misnamed: leftover Ⅰ / #570 / #572 / #567 still Disjoint /
   Overlap / TouchVertex / TouchEdge. Not a TPR_SameCone claim. *)
Theorem classified_hard_pairs_still_samecone :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint /\
  triangle_pair_regime 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
    = TPR_Overlap /\
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = TPR_TouchVertex /\
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  exact classified_hard_pairs.
Qed.

Theorem unnamed_ccw_still_unsupported :
  triangle_pair_regime 0 0 3 0 0 3 2 (-1) 2 2 (-1) 2 = TPR_Unsupported.
Proof.
  exact unnamed_ccw_pair_unsupported.
Qed.

(* Epic #522 / #577 stop: completeness (QED) or a documented CCW
   unsupported pair (QEX). Discharged QEX — unnamed lens. The
   #577 disjunction copied into a third file; does not move #522
   closer to QED. Leftover-Ⅵ inhabitance does not take the left.
   Not a 522-j remint. Leftover `Ⅶ` is already #642. *)
(* WITNESS {"claimId":"Ⅵ","topic":"relate","lemma":"triangle_pair_regime_ccw_stop","title":"Epic #522 stop is completeness (QED) or a documented CCW unsupported pair (QEX); discharged QEX on an unnamed lens","file":"theories/RelateNGTouchSameCone.v","witness":"Ⅵ-same-cone-cex","board":"leftover-Ⅵ"} *)
Theorem triangle_pair_regime_ccw_stop :
  (forall ax ay bx by_ cx cy dx dy ex ey fx fy : R,
     0 < gdbl ax ay bx by_ cx cy ->
     0 < gdbl dx dy ex ey fx fy ->
     triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
       <> TPR_Unsupported)
  \/
  (exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
     0 < gdbl ax ay bx by_ cx cy /\
     0 < gdbl dx dy ex ey fx fy /\
     triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
       = TPR_Unsupported).
Proof.
  right.
  exact triangle_pair_regime_ccw_incomplete.
Qed.

Theorem triangle_pair_regime_ccw_stop_not_tjunction :
  (forall ax ay bx by_ cx cy dx dy ex ey fx fy : R,
     0 < gdbl ax ay bx by_ cx cy ->
     0 < gdbl dx dy ex ey fx fy ->
     ~ tjunction_pair_coords ax ay bx by_ cx cy dx dy ex ey fx fy ->
     triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
       <> TPR_Unsupported)
  \/
  (exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
     0 < gdbl ax ay bx by_ cx cy /\
     0 < gdbl dx dy ex ey fx fy /\
     ~ tjunction_pair_coords ax ay bx by_ cx cy dx dy ex ey fx fy /\
     triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
       = TPR_Unsupported).
Proof.
  right.
  exact triangle_pair_regime_ccw_incomplete_not_tjunction.
Qed.

(* Classified ∨ declined on the pair this letter just classified.
   One more named bucket. Does not move epic #522 closer to QED. *)
Theorem leftover_vi_qed_or_qex :
  triangle_pair_regime 0 0 2 0 0 2 0 0 3 1 1 3 = TPR_SameCone
  \/
  triangle_pair_regime 0 0 2 0 0 2 0 0 3 1 1 3 = TPR_Unsupported.
Proof.
  left.
  exact triangle_pair_regime_samecone.
Qed.

Theorem samecone_fill_still_unsupported :
  triangle_pair_fill TPR_SameCone = im_unsupported.
Proof.
  exact triangle_pair_fill_touch_samecone_eq.
Qed.

Print Assumptions triangle_pair_regime_samecone.
Print Assumptions leftover_I_no_samecone.
Print Assumptions leftover_II_no_samecone.
Print Assumptions leftover_III_no_samecone.
Print Assumptions leftover_IV_no_samecone.
Print Assumptions leftover_V_no_samecone.
Print Assumptions leftover_VI_samecone_true.
Print Assumptions classified_hard_pairs_no_samecone.
Print Assumptions hard_touchvertex_no_samecone.
Print Assumptions hard_contains_no_samecone.
Print Assumptions leftover_I_still_partial.
Print Assumptions leftover_II_still_obtuse.
Print Assumptions leftover_III_still_onesided.
Print Assumptions leftover_IV_still_onesided.
Print Assumptions leftover_V_still_mixedcone.
Print Assumptions unnamed_ccw_still_unsupported.
Print Assumptions triangle_pair_regime_ccw_stop.
Print Assumptions triangle_pair_regime_ccw_stop_not_tjunction.
Print Assumptions leftover_vi_qed_or_qex.
Print Assumptions samecone_fill_still_unsupported.
