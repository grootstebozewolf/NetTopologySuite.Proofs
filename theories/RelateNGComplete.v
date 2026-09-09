(* ============================================================================
   NetTopologySuite.Proofs.RelateNGComplete
   ----------------------------------------------------------------------------
   Issue #577 / #522 claimId 522-j: leftover-decline finding.

   Ticket #577 asked completeness or a documented counterexample.
   Leftover `Ⅰ` classifies the T-junction as `TPR_TouchPartialEdge`.
   Leftover `Ⅱ` classifies obtuse-at-v as `TPR_TouchObtuse`.
   Leftover `Ⅴ` classifies mixed-cone as `TPR_MixedCone`.
   Leftover `Ⅵ` classifies same-cone as `TPR_SameCone`.
   Completeness is still FALSE on an unnamed lens (`TPR_Unsupported`).

   Hard pairs that DO classify are cited, not re-proved. Catalog
   ids: disjoint #571 / 522-c; overlap #570 / 522-b; vertex-touch
   #572 / 522-i; shared-edge is the existing `TPR_TouchEdge` pin.

   Domain boundary: `overlap_b` / `separated_b` / `touch_vertex_b`
   are false when either orientation fails. That is NOT
   "non-CCW ⇒ Unsupported" — `touch_edge_b` has no CCW guard.

   Five names are not a partition. Leftover `Ⅲ`/`Ⅳ` share
   `TPR_TouchOnesided` (fill token). `522-j` is the #577 ticket
   id. `522-m` retries after excluding the T-junction: still
   FALSE (unnamed lens after leftover `Ⅵ`). Not an ADR-0004 remint.

   WITNESS topic: relate · claimId: 522-j · witness: 522-j-sentinel-cex
   WITNESS topic: relate · claimId: 522-m · witness: 522-m-complete-filtered
   WITNESS topic: relate · claimId: Ⅲ · witness: Ⅲ-onesided-t-cex
   WITNESS topic: relate · claimId: Ⅳ · witness: Ⅳ-interior-side-cex
   WITNESS topic: relate · claimId: Ⅱ · witness: Ⅱ-obtuse-cex
   WITNESS topic: relate · claimId: Ⅴ · witness: Ⅴ-mixed-cone-cex
   macro: relate
   lane: proofs
   issue: #577 / #522
   ADR-0004: not a remint. 522-j is the existing #577 ticket id.
   522-m is the filtered-completeness retry (unused letter; not 522-d..l).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

From Stdlib Require Import Reals List Lia Lra Ranalysis Bool Btauto.
From NTS.Proofs Require Import Real.
From NTS.Proofs Require Import DE9IM Distance Overlay Segment RelateBoundary
  RelateLineLine RelateAreaPoint RelateAreaLine RelateAreaArea
  RelateMatrixLineLine RelateMatrixAreaLine RelateMatrixRect RelateMatrixTriangle
  RelateCurveMatrix RectangleJCT Intersect Orientation Convex Lattice Centroid.
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity
  RectangleSeparation.
From NTS.Proofs Require Import GeneralTriangleJCT GeneralTriangleExterior
  TriangleValidPolygon JCTSeamAssembly PointInRingCorrect PointInRingTangents
  JordanCurveSeam TriangleContainmentConvex.
From NTS.Proofs Require Import RelateNGCore RelateNGContains RelateNGOverlap
  RelateNGDisjoint RelateNGTouchVertex RelateNGUnnamedCex RelateNGTouch.

Import ListNotations.
Local Open Scope R_scope.

(* Historical 522-j pair: leftover `Ⅰ` classifies; live cex is unnamed. *)

Lemma tjunction_pair_both_ccw :
  0 < gdbl 0 0 2 0 0 1 /\ 0 < gdbl 1 0 3 0 2 1.
Proof. unfold gdbl; split; lra. Qed.

(** Leftover-Ⅰ classifies as [TPR_TouchPartialEdge]. Live cex is unnamed. *)
Theorem triangle_pair_regime_incomplete_tjunction :
  0 < gdbl 0 0 2 0 0 1 /\
  0 < gdbl 1 0 3 0 2 1 /\
  triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1 = TPR_TouchPartialEdge.
Proof.
  split; [unfold gdbl; lra|].
  split; [unfold gdbl; lra|].
  exact tjunction_pair_touch_partial.
Qed.

(* -------------------------------------------------------------------------- *)
(* Hard-pair family that does classify.  Cite existing, do not re-prove.      *)
(* Catalog: disjoint #571 / 522-c on the #530 sentinel; overlap #570 /        *)
(* 522-b on the #567 pair; vertex-touch #572 / 522-i; shared-edge touch       *)
(* is the pre-#522 `TPR_TouchEdge` pin.                                       *)
(* -------------------------------------------------------------------------- *)

(* #571 / 522-c: the #530 sentinel `(0,0)(1,0)(0,1)` vs `(2,0)(3,0)(2,1)`. *)
Lemma classified_disjoint_pair :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint.
Proof.
  exact (triangle_pair_regime_disjoint 0 0 1 0 0 1 2 0 3 0 2 1
           dispatch_pair_separated_b).
Qed.

(* #570 / 522-b: the #567 overlap pair. *)
Lemma classified_overlap_pair :
  triangle_pair_regime 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
    = TPR_Overlap.
Proof.
  exact (triangle_pair_regime_overlap 0 0 1 0 0 1
           (1/4) (1/4) (5/4) (1/4) (1/4) (5/4) overlap_ex_overlap_b).
Qed.

(* #572 / 522-i: ticket vertex-touch pair. *)
Lemma classified_touchvertex_pair :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = TPR_TouchVertex.
Proof.
  exact (triangle_pair_regime_touchvertex 0 0 2 0 0 2
           0 0 (-2) 0 0 (-2) touchvertex_ex_touch_vertex_b).
Qed.

(* Pre-#522 shared-edge pin, not a #522 subtask. *)
Lemma classified_touch_pair :
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  exact (triangle_pair_regime_touch 0 0 1 0 0 1 1 0 1 1 0 1
           ex_triangles_touch_on_shared_edge).
Qed.

Lemma classified_hard_pairs :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint /\
  triangle_pair_regime 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
    = TPR_Overlap /\
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = TPR_TouchVertex /\
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  split; [exact classified_disjoint_pair|].
  split; [exact classified_overlap_pair|].
  split; [exact classified_touchvertex_pair|].
  exact classified_touch_pair.
Qed.

(* -------------------------------------------------------------------------- *)
(* Domain boundary.  The three both-CCW certificates refuse a non-CCW         *)
(* argument.  This is NOT "non-CCW ⇒ Unsupported": `touch_edge_b` has no      *)
(* orientation guard, and `contains_b` guards only A.                         *)
(* -------------------------------------------------------------------------- *)

Lemma overlap_b_false_of_non_ccw :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    ~ (0 < gdbl ax ay bx by_ cx cy)
    \/ ~ (0 < gdbl dx dy ex ey fx fy) ->
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold overlap_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [| reflexivity ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [| reflexivity ].
  exfalso. destruct H as [Hn | Hn]; apply Hn; assumption.
Qed.

Lemma separated_b_false_of_non_ccw :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    ~ (0 < gdbl ax ay bx by_ cx cy)
    \/ ~ (0 < gdbl dx dy ex ey fx fy) ->
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [| reflexivity ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [| reflexivity ].
  exfalso. destruct H as [Hn | Hn]; apply Hn; assumption.
Qed.

Lemma touch_vertex_b_false_of_non_ccw :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    ~ (0 < gdbl ax ay bx by_ cx cy)
    \/ ~ (0 < gdbl dx dy ex ey fx fy) ->
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold touch_vertex_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [| reflexivity ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [| reflexivity ].
  exfalso. destruct H as [Hn | Hn]; apply Hn; assumption.
Qed.

Lemma non_ccw_pair_no_overlap_disjoint_vertex :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    ~ (0 < gdbl ax ay bx by_ cx cy)
    \/ ~ (0 < gdbl dx dy ex ey fx fy) ->
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = false /\
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = false /\
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  split; [exact (overlap_b_false_of_non_ccw _ _ _ _ _ _ _ _ _ _ _ _ H)|].
  split; [exact (separated_b_false_of_non_ccw _ _ _ _ _ _ _ _ _ _ _ _ H)|].
  exact (touch_vertex_b_false_of_non_ccw _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

(* 522-m: leftover Ⅵ classified same-cone. Live cex is unnamed
   A=(0,0)(3,0)(0,3) vs B=(2,-1)(2,2)(-1,2). Do not mint leftover `Ⅶ`. *)

Definition tjunction_pair_coords
    (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : Prop :=
  ax = 0 /\ ay = 0 /\ bx = 2 /\ by_ = 0 /\ cx = 0 /\ cy = 1 /\
  dx = 1 /\ dy = 0 /\ ex = 3 /\ ey = 0 /\ fx = 2 /\ fy = 1.

Lemma obtuse_pair_both_ccw :
  0 < gdbl 0 0 2 0 0 2 /\ 0 < gdbl 0 0 (-2) 0 1 (-1).
Proof. unfold gdbl; split; lra. Qed.

Lemma obtuse_pair_not_tjunction :
  ~ tjunction_pair_coords 0 0 2 0 0 2 0 0 (-2) 0 1 (-1).
Proof.
  intros [Hax [Hay [Hbx [Hby [Hcx [Hcy _]]]]]].
  lra.
Qed.

Lemma both_strict_neg_b_false_snd : forall v n p q,
  ~ (side_dot v n q < 0) ->
  both_strict_neg_b v n p q = false.
Proof.
  intros v n p q Hn. unfold both_strict_neg_b.
  destruct (Rlt_dec (side_dot v n p) 0) as [_ | _];
    [| reflexivity ].
  destruct (Rlt_dec (side_dot v n q) 0) as [Hlt | _];
    [ contradiction | reflexivity ].
Qed.

Lemma both_strict_pos_b_false_snd : forall v n p q,
  ~ (0 < side_dot v n q) ->
  both_strict_pos_b v n p q = false.
Proof.
  intros v n p q Hn. unfold both_strict_pos_b.
  destruct (Rlt_dec 0 (side_dot v n p)) as [_ | _];
    [| reflexivity ].
  destruct (Rlt_dec 0 (side_dot v n q)) as [Hlt | _];
    [ contradiction | reflexivity ].
Qed.

Lemma obtuse_no_separator :
  some_edge_separates_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1)) = false.
Proof.
  unfold some_edge_separates_b.
  (* A bottom y=0: B's (0,0) is an endpoint. *)
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
             (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* A hypotenuse: B's (0,0) equals A's apex. *)
  rewrite (edge_separates_b_false_l (mkPoint 2 0) (mkPoint 0 2) (mkPoint 0 0)
             (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* A left x=0: B's (0,0) is an endpoint. *)
  rewrite (edge_separates_b_false_l (mkPoint 0 2) (mkPoint 0 0) (mkPoint 2 0)
             (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* B bottom y=0: A's (0,0) is an endpoint. *)
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* B sloped: A's (0,0) equals B's apex. *)
  rewrite (edge_separates_b_false_l (mkPoint (-2) 0) (mkPoint 1 (-1)) (mkPoint 0 0)
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* B last: A's (0,0) is an endpoint (q1). *)
  assert (E6 : edge_separates_b (mkPoint 1 (-1)) (mkPoint 0 0) (mkPoint (-2) 0)
                 (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) = false).
  { unfold edge_separates_b, opposite_sides_b, cross; cbn [px py].
    destruct (Rlt_dec (_ * _) 0) as [Hbad | _];
      [ exfalso; lra | reflexivity ]. }
  rewrite E6. reflexivity.
Qed.

Lemma obtuse_touch_obtuse_true :
  touch_obtuse_vertex_b 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = true.
Proof.
  unfold touch_obtuse_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold touch_obtuse_from_v, others_fst, others_snd, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold closed_cone_separates_b, both_closed_pos_b, both_closed_neg_b,
         cone_separates_b, both_strict_pos_b, both_strict_neg_b,
         vec_sum_from, side_dot.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma obtuse_pair_touch_obtuse :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = TPR_TouchObtuse.
Proof.
  unfold triangle_pair_regime, touch_edge_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold contains_b.
  assert (Hcb : gtri 0 0 2 0 0 2 (mkPoint 0 0) <= 0).
  { unfold gtri.
    assert (H : gsA 0 0 2 0 (mkPoint 0 0) = 0) by (unfold gsA; simpl; ring).
    rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_l_le ]. }
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; lra | ].
  unfold overlap_b, some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 0))) as [H1 | _];
    [ exfalso; lra | ].
  assert (H20 : gtri 0 0 2 0 0 2 (mkPoint (-2) 0) <= 0).
  { unfold gtri.
    assert (H : gsA 0 0 2 0 (mkPoint (-2) 0) = 0) by (unfold gsA; simpl; ring).
    rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_l_le ]. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint (-2) 0))) as [H2 | _];
    [ exfalso; lra | ].
  assert (H1n : gtri 0 0 2 0 0 2 (mkPoint 1 (-1)) < 0).
  { eapply Rle_lt_trans; [ apply (gtri_le_gsA 0 0 2 0 0 2 (mkPoint 1 (-1))) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 1 (-1)))) as [H3 | _];
    [ exfalso; lra | ].
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  rewrite obtuse_no_separator.
  unfold touch_vertex_b, exactly_one_shared_from_a, is_vertex_b, point_eqb.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  assert (HA2 : touch_vertex_from_v
            (mkPoint 2 0)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1)) = false).
  { unfold touch_vertex_from_v.
    rewrite (is_vertex_b_false_of_none
               (mkPoint 2 0)
               (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))).
    - rewrite andb_false_r, andb_false_l. reflexivity.
    - apply mkPoint_neq_px; lra.
    - apply mkPoint_neq_px; lra.
    - apply mkPoint_neq_px; lra. }
  assert (HA3 : touch_vertex_from_v
            (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1)) = false).
  { unfold touch_vertex_from_v.
    rewrite (is_vertex_b_false_of_none
               (mkPoint 0 2)
               (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))).
    - rewrite andb_false_r, andb_false_l. reflexivity.
    - apply mkPoint_neq_py; lra.
    - apply mkPoint_neq_py; lra.
    - apply mkPoint_neq_py; lra. }
  assert (HA1 : touch_vertex_from_v
            (mkPoint 0 0)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1)) = false).
  { unfold touch_vertex_from_v, others_fst, others_snd.
    rewrite (point_eqb_complete (mkPoint 0 0) (mkPoint 0 0) eq_refl).
    rewrite (cone_separates_b_false_of_arms
               (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
               (mkPoint (-2) 0) (mkPoint 1 (-1))).
    - rewrite andb_false_r. reflexivity.
    - apply both_strict_neg_b_false_snd.
      unfold vec_sum_from, side_dot. cbn [px py]. lra.
    - apply both_strict_pos_b_false_snd.
      unfold vec_sum_from, side_dot. cbn [px py]. lra. }
  rewrite HA1, HA2, HA3.
  rewrite !orb_false_r, andb_false_r.
  unfold touch_partial_edge_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  unfold touch_onesided_t_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  rewrite obtuse_touch_obtuse_true.
  reflexivity.
Qed.

(* WITNESS {"claimId":"Ⅱ","topic":"relate","lemma":"obtuse_pair_touch_obtuse","title":"Leftover Ⅱ obtuse-at-v classifies as TPR_TouchObtuse","file":"theories/RelateNGComplete.v","witness":"Ⅱ-obtuse-cex","board":"leftover-Ⅱ"} *)

(* Leftover Ⅴ mixed-cone: A=(0,0)(2,0)(0,2), B=(0,0)(-1,-1)(3,1). *)
Definition mixed_cone_pair_coords
    (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : Prop :=
  ax = 0 /\ ay = 0 /\ bx = 2 /\ by_ = 0 /\ cx = 0 /\ cy = 2 /\
  dx = 0 /\ dy = 0 /\ ex = (-1) /\ ey = (-1) /\ fx = 3 /\ fy = 1.

Lemma mixed_cone_pair_both_ccw :
  0 < gdbl 0 0 2 0 0 2 /\ 0 < gdbl 0 0 (-1) (-1) 3 1.
Proof. unfold gdbl; split; lra. Qed.

Lemma mixed_cone_pair_not_tjunction :
  ~ tjunction_pair_coords 0 0 2 0 0 2 0 0 (-1) (-1) 3 1.
Proof.
  intros [Hax [Hay [Hbx [Hby [Hcx [Hcy _]]]]]].
  lra.
Qed.

Lemma mixed_cone_no_separator :
  some_edge_separates_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1) = false.
Proof.
  unfold some_edge_separates_b.
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
             (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 2 0) (mkPoint 0 2) (mkPoint 0 0)
             (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 0 2) (mkPoint 0 0) (mkPoint 2 0)
             (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1)
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint (-1) (-1)) (mkPoint 3 1) (mkPoint 0 0)
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  assert (E6 : edge_separates_b (mkPoint 3 1) (mkPoint 0 0) (mkPoint (-1) (-1))
                 (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) = false).
  { unfold edge_separates_b, opposite_sides_b, cross; cbn [px py].
    destruct (Rlt_dec (_ * _) 0) as [Hbad | _];
      [ exfalso; lra | reflexivity ]. }
  rewrite E6. reflexivity.
Qed.

Lemma mixed_cone_touch_obtuse_false :
  touch_obtuse_vertex_b 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = false.
Proof.
  unfold touch_obtuse_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-1) (-1) 3 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold touch_obtuse_from_v, others_fst, others_snd, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold closed_cone_separates_b, both_closed_pos_b, both_closed_neg_b,
         cone_separates_b, both_strict_pos_b, both_strict_neg_b,
         vec_sum_from, side_dot.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma mixed_cone_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1) = false.
Proof.
  unfold touch_partial_edge_b.
  rewrite mixed_cone_no_open_A, mixed_cone_no_open_B.
  reflexivity.
Qed.

Lemma mixed_cone_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1) = false.
Proof.
  unfold touch_onesided_t_b.
  rewrite mixed_cone_no_open_A, mixed_cone_no_open_B.
  reflexivity.
Qed.

Lemma mixed_cone_pair_mixedcone :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = TPR_MixedCone.
Proof.
  unfold triangle_pair_regime, touch_edge_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold contains_b.
  assert (Hcb : gtri 0 0 2 0 0 2 (mkPoint 0 0) <= 0).
  { unfold gtri.
    assert (H : gsA 0 0 2 0 (mkPoint 0 0) = 0) by (unfold gsA; simpl; ring).
    rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_l_le ]. }
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; lra | ].
  unfold overlap_b, some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-1) (-1) 3 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 0))) as [H1 | _];
    [ exfalso; lra | ].
  assert (H20 : gtri 0 0 2 0 0 2 (mkPoint (-1) (-1)) < 0).
  { eapply Rle_lt_trans; [ apply (gtri_le_gsA 0 0 2 0 0 2 (mkPoint (-1) (-1))) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint (-1) (-1)))) as [H2 | _];
    [ exfalso; lra | ].
  assert (H1n : gtri 0 0 2 0 0 2 (mkPoint 3 1) < 0).
  { eapply Rle_lt_trans; [ apply (gtri_le_gsB 0 0 2 0 0 2 (mkPoint 3 1)) | ].
    unfold gsB; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 3 1))) as [H3 | _];
    [ exfalso; lra | ].
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-1) (-1) 3 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  rewrite mixed_cone_no_separator.
  unfold touch_vertex_b, exactly_one_shared_from_a, is_vertex_b, point_eqb.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-1) (-1) 3 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  assert (HA2 : touch_vertex_from_v
            (mkPoint 2 0)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1) = false).
  { unfold touch_vertex_from_v.
    rewrite (is_vertex_b_false_of_none
               (mkPoint 2 0)
               (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1)).
    - rewrite andb_false_r, andb_false_l. reflexivity.
    - apply mkPoint_neq_px; lra.
    - apply mkPoint_neq_px; lra.
    - apply mkPoint_neq_px; lra. }
  assert (HA3 : touch_vertex_from_v
            (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1) = false).
  { unfold touch_vertex_from_v.
    rewrite (is_vertex_b_false_of_none
               (mkPoint 0 2)
               (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1)).
    - rewrite andb_false_r, andb_false_l. reflexivity.
    - apply mkPoint_neq_py; lra.
    - apply mkPoint_neq_py; lra.
    - apply mkPoint_neq_py; lra. }
  assert (HA1 : touch_vertex_from_v
            (mkPoint 0 0)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1) = false).
  { unfold touch_vertex_from_v, others_fst, others_snd.
    rewrite (point_eqb_complete (mkPoint 0 0) (mkPoint 0 0) eq_refl).
    rewrite (cone_separates_b_false_of_arms
               (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
               (mkPoint (-1) (-1)) (mkPoint 3 1)).
    - rewrite andb_false_r. reflexivity.
    - apply both_strict_neg_b_false_snd.
      unfold vec_sum_from, side_dot. cbn [px py]. lra.
    - apply both_strict_pos_b_false_fst.
      unfold vec_sum_from, side_dot. cbn [px py]. lra. }
  rewrite HA1, HA2, HA3.
  rewrite !orb_false_r, andb_false_r.
  rewrite mixed_cone_no_partial_edge.
  rewrite mixed_cone_no_onesided.
  rewrite mixed_cone_touch_obtuse_false.
  rewrite mixed_cone_vertex_b_true.
  reflexivity.
Qed.

(* WITNESS {"claimId":"Ⅴ","topic":"relate","lemma":"mixed_cone_pair_mixedcone","title":"Leftover Ⅴ mixed-cone classifies as TPR_MixedCone","file":"theories/RelateNGComplete.v","witness":"Ⅴ-mixed-cone-cex","board":"leftover-Ⅴ"} *)

(* WITNESS {"claimId":"522-j","topic":"relate","lemma":"triangle_pair_regime_ccw_incomplete","title":"Classifier completeness is still false after leftover Ⅵ: an unnamed lens pair emits TPR_Unsupported","file":"theories/RelateNGComplete.v","witness":"522-j-sentinel-cex","board":"#577"} *)
Theorem triangle_pair_regime_ccw_incomplete :
  exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
    0 < gdbl ax ay bx by_ cx cy /\
    0 < gdbl dx dy ex ey fx fy /\
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_Unsupported.
Proof.
  exists 0, 0, 3, 0, 0, 3, 2, (-1), 2, 2, (-1), 2.
  split; [unfold gdbl; lra|].
  split; [unfold gdbl; lra|].
  exact unnamed_ccw_pair_unsupported.
Qed.

(* WITNESS {"claimId":"522-m","topic":"relate","lemma":"triangle_pair_regime_ccw_incomplete_not_tjunction","title":"Filtered CCW-completeness is still false: an unnamed lens declines after leftover Ⅵ classifies same-cone","file":"theories/RelateNGComplete.v","witness":"522-m-complete-filtered","board":"#522"} *)
Theorem triangle_pair_regime_ccw_incomplete_not_tjunction :
  exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
    0 < gdbl ax ay bx by_ cx cy /\
    0 < gdbl dx dy ex ey fx fy /\
    ~ tjunction_pair_coords ax ay bx by_ cx cy dx dy ex ey fx fy /\
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_Unsupported.
Proof.
  exists 0, 0, 3, 0, 0, 3, 2, (-1), 2, 2, (-1), 2.
  split; [unfold gdbl; lra|].
  split; [unfold gdbl; lra|].
  split; [intros [Hax [Hay [Hbx [Hby [Hcx [Hcy [Hdx _]]]]]]]; lra|].
  exact unnamed_ccw_pair_unsupported.
Qed.

Theorem ccw_complete_except_tjunction_false :
  ~ (forall ax ay bx by_ cx cy dx dy ex ey fx fy : R,
       0 < gdbl ax ay bx by_ cx cy ->
       0 < gdbl dx dy ex ey fx fy ->
       ~ tjunction_pair_coords ax ay bx by_ cx cy dx dy ex ey fx fy ->
       triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
         <> TPR_Unsupported).
Proof.
  intros H.
  destruct triangle_pair_regime_ccw_incomplete_not_tjunction
    as [ax [ay [bx [by_ [cx [cy [dx [dy [ex [ey [fx [fy H12]]]]]]]]]]]].
  destruct H12 as [HA [HB [Hn Hreg]]].
  apply (H ax ay bx by_ cx cy dx dy ex ey fx fy HA HB Hn).
  exact Hreg.
Qed.

(* Leftover Ⅲ — exterior-side stem. Completeness is unnamed. *)

Definition onesided_t_pair_coords
    (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : Prop :=
  ax = 0 /\ ay = 0 /\ bx = 2 /\ by_ = 0 /\ cx = 0 /\ cy = 1 /\
  dx = 1 /\ dy = 0 /\ ex = (1/2) /\ ey = (-1) /\ fx = (3/2) /\ fy = (-1).

Lemma onesided_t_pair_both_ccw :
  0 < gdbl 0 0 2 0 0 1 /\ 0 < gdbl 1 0 (1/2) (-1) (3/2) (-1).
Proof. unfold gdbl; split; lra. Qed.

Lemma onesided_t_not_tjunction :
  ~ tjunction_pair_coords 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1).
Proof.
  intros [Hax [Hay [Hbx [Hby [Hcx [Hcy [Hdx [Hdy [Hex _]]]]]]]]].
  lra.
Qed.

Lemma onesided_t_B_gsA_plus_gsC : forall p,
  gsA 1 0 (1/2) (-1) p + gsC 1 0 (3/2) (-1) p = - py p.
Proof. intros p; unfold gsA, gsC; cbn [px py]; lra. Qed.

(* Exterior-side stem: A's interior is y > 0, B's slacks on the two
   apex edges sum to -y, so II is empty. *)
Lemma onesided_t_ii_empty : forall p,
  ~ (0 < gtri 0 0 2 0 0 1 p /\
     0 < gtri 1 0 (1/2) (-1) (3/2) (-1) p).
Proof.
  intros p [HA HB].
  assert (Hy : 0 < py p).
  { pose proof (gtri_le_gsA 0 0 2 0 0 1 p) as Hle.
    unfold gsA in Hle; cbn [px py] in Hle. lra. }
  pose proof (onesided_t_B_gsA_plus_gsC p) as Hsum.
  pose proof (gtri_le_gsA 1 0 (1/2) (-1) (3/2) (-1) p) as HleA.
  pose proof (gtri_le_gsC 1 0 (1/2) (-1) (3/2) (-1) p) as HleC.
  lra.
Qed.

(* Ticket 21 filter: B-vertex (1, 0) sits in the open interior of
   A's base (0,0)--(2,0). *)
Lemma onesided_t_B_on_open_base :
  on_open_seg_b (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 0) = true.
Proof.
  unfold on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

(* One-sided: some B-vertex on an open A-edge, no A-vertex on an
   open B-edge. Mutual leftover Ⅰ stays false. *)
Lemma onesided_t_one_sided :
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = true /\
  some_vertex_on_open_edges
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1))
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1) = false.
Proof.
  split.
  { unfold some_vertex_on_open_edges, vertex_on_open_edges.
    rewrite onesided_t_B_on_open_base.
    reflexivity. }
  { unfold some_vertex_on_open_edges, vertex_on_open_edges,
           on_open_seg_b, cross.
    cbn [px py].
    repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
    repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
    reflexivity. }
Qed.

(* Ticket 21 filter: no shared vertex (also distinguishes leftover Ⅱ). *)
Lemma onesided_t_no_shared_vertex :
  is_vertex_b (mkPoint 0 0)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = false /\
  is_vertex_b (mkPoint 2 0)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = false /\
  is_vertex_b (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = false.
Proof.
  split.
  { apply is_vertex_b_false_of_none;
      (apply mkPoint_neq_px; lra). }
  split.
  { apply is_vertex_b_false_of_none.
    - apply mkPoint_neq_px; lra.
    - apply mkPoint_neq_py; lra.
    - apply mkPoint_neq_py; lra. }
  { apply is_vertex_b_false_of_none;
      (apply mkPoint_neq_py; lra). }
Qed.

Lemma onesided_t_no_separator :
  some_edge_separates_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = false.
Proof.
  unfold some_edge_separates_b.
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
             (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 2 0) (mkPoint 0 1) (mkPoint 0 0)
             (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 0 1) (mkPoint 0 0) (mkPoint 2 0)
             (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* B's (1,0)–(1/2,-1): A's (0,0) is opposite the apex. Pin the
     mid vertex (2,0) so lra never sees a 12-hypothesis Rlt_dec goal. *)
  assert (E4 : edge_separates_b (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1))
                 (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1) = false).
  { unfold edge_separates_b.
    assert (Hprod : cross (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1))
                        * cross (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint 2 0) >= 0).
    { unfold cross; cbn [px py]; lra. }
    assert (Hmid : opposite_sides_b
                     (mkPoint 1 0) (mkPoint (1/2) (-1))
                     (mkPoint (3/2) (-1)) (mkPoint 2 0) = false).
    { apply opposite_sides_b_false_of_nlt. intros Hlt. lra. }
    rewrite Hmid.
    destruct (opposite_sides_b (mkPoint 1 0) (mkPoint (1/2) (-1))
                (mkPoint (3/2) (-1)) (mkPoint 0 0)); reflexivity. }
  rewrite E4.
  rewrite (edge_separates_b_false_l (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) (mkPoint 1 0)
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)).
  2: {
    apply opposite_sides_b_false_of_nlt.
    assert (Hprod : cross (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) (mkPoint 1 0)
                        * cross (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) (mkPoint 0 0) >= 0).
    { unfold cross; cbn [px py]; lra. }
    intros Hlt. lra. }
  rewrite (edge_separates_b_false_l (mkPoint (3/2) (-1)) (mkPoint 1 0) (mkPoint (1/2) (-1))
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)).
  2: {
    apply opposite_sides_b_false_of_nlt.
    assert (Hprod : cross (mkPoint (3/2) (-1)) (mkPoint 1 0) (mkPoint (1/2) (-1))
                        * cross (mkPoint (3/2) (-1)) (mkPoint 1 0) (mkPoint 0 0) >= 0).
    { unfold cross; cbn [px py]; lra. }
    intros Hlt. lra. }
  reflexivity.
Qed.

Lemma onesided_t_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = false.
Proof.
  unfold touch_partial_edge_b.
  destruct onesided_t_one_sided as [HA HB].
  rewrite HA, HB.
  reflexivity.
Qed.

Lemma onesided_t_onesided_true :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = true.
Proof.
  unfold touch_onesided_t_b.
  destruct onesided_t_one_sided as [HA HB].
  rewrite HA, HB.
  reflexivity.
Qed.

Lemma onesided_t_pair_onesided :
  triangle_pair_regime 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1)
    = TPR_TouchOnesided.
Proof.
  unfold triangle_pair_regime, touch_edge_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold contains_b.
  assert (Hcb : gtri 0 0 2 0 0 1 (mkPoint 1 0) <= 0).
  { unfold gtri.
    assert (H : gsA 0 0 2 0 (mkPoint 1 0) = 0) by (unfold gsA; simpl; ring).
    rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_l_le ]. }
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 1 (mkPoint 1 0))) as [Hlt | _];
    [ exfalso; lra | ].
  unfold overlap_b, some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (1/2) (-1) (3/2) (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 1 (mkPoint 1 0))) as [H1 | _];
    [ exfalso; lra | ].
  assert (H20 : gtri 0 0 2 0 0 1 (mkPoint (1/2) (-1)) < 0).
  { eapply Rle_lt_trans; [ apply (gtri_le_gsA 0 0 2 0 0 1 (mkPoint (1/2) (-1))) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 1 (mkPoint (1/2) (-1)))) as [H2 | _];
    [ exfalso; lra | ].
  assert (H3n : gtri 0 0 2 0 0 1 (mkPoint (3/2) (-1)) < 0).
  { eapply Rle_lt_trans; [ apply (gtri_le_gsA 0 0 2 0 0 1 (mkPoint (3/2) (-1))) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 1 (mkPoint (3/2) (-1)))) as [H3 | _];
    [ exfalso; lra | ].
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (1/2) (-1) (3/2) (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  rewrite onesided_t_no_separator.
  unfold touch_vertex_b, exactly_one_shared_from_a, is_vertex_b, point_eqb.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (1/2) (-1) (3/2) (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  rewrite onesided_t_no_partial_edge.
  rewrite onesided_t_onesided_true.
  reflexivity.
Qed.

(* WITNESS {"claimId":"Ⅲ","topic":"relate","lemma":"onesided_t_pair_onesided","title":"Leftover Ⅲ exterior-side stem classifies as TPR_TouchOnesided","file":"theories/RelateNGComplete.v","witness":"Ⅲ-onesided-t-cex","board":"leftover-Ⅲ"} *)
Theorem onesided_t_pair_inhabits :
  onesided_t_pair_coords 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1) /\
  0 < gdbl 0 0 2 0 0 1 /\
  0 < gdbl 1 0 (1/2) (-1) (3/2) (-1) /\
  on_open_seg_b (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 0) = true /\
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = true /\
  some_vertex_on_open_edges
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1))
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1) = false /\
  ~ tjunction_pair_coords 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1) /\
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = false /\
  is_vertex_b (mkPoint 0 0)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = false /\
  is_vertex_b (mkPoint 2 0)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = false /\
  is_vertex_b (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = false /\
  (forall p, ~ (0 < gtri 0 0 2 0 0 1 p /\
                0 < gtri 1 0 (1/2) (-1) (3/2) (-1) p)) /\
  triangle_pair_regime 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1)
    = TPR_TouchOnesided.
Proof.
  split; [repeat split; reflexivity|].
  split; [unfold gdbl; lra|].
  split; [unfold gdbl; lra|].
  split; [exact onesided_t_B_on_open_base|].
  destruct onesided_t_one_sided as [Hone Hrev].
  split; [exact Hone|].
  split; [exact Hrev|].
  split; [exact onesided_t_not_tjunction|].
  split; [exact onesided_t_no_partial_edge|].
  destruct onesided_t_no_shared_vertex as [Hv1 [Hv2 Hv3]].
  split; [exact Hv1|].
  split; [exact Hv2|].
  split; [exact Hv3|].
  split; [exact onesided_t_ii_empty|].
  exact onesided_t_pair_onesided.
Qed.

Print Assumptions triangle_pair_regime_incomplete_tjunction.
Print Assumptions triangle_pair_regime_ccw_incomplete.
Print Assumptions classified_hard_pairs.
Print Assumptions non_ccw_pair_no_overlap_disjoint_vertex.
Print Assumptions triangle_pair_regime_ccw_incomplete_not_tjunction.
Print Assumptions ccw_complete_except_tjunction_false.
Print Assumptions onesided_t_pair_onesided.
Print Assumptions onesided_t_pair_inhabits.
Print Assumptions onesided_t_onesided_true.
Print Assumptions onesided_t_ii_empty.
Print Assumptions onesided_t_B_on_open_base.
Print Assumptions onesided_t_one_sided.
Print Assumptions onesided_t_no_shared_vertex.

(* -------------------------------------------------------------------------- *)
(* Leftover Ⅳ — interior-side one-sided T (ticket 26 residue).               *)
(*                                                                            *)
(* Same A and contact as leftover Ⅲ.  A = (0,0)(2,0)(0,1),                    *)
(* B = (1,0)(5/4,1/4)(3/4,1/4).  Both CCW.  B-vertex (1,0) sits in the        *)
(* open base of A.  Remaining B vertices sit on the same side of y = 0        *)
(* as A's interior (y > 0) and are strictly interior to A, so                 *)
(* overlap_b misses (no exterior B-vertex).  contains_b misses (stem          *)
(* has gtri A = 0).  Not mutual.  No shared vertex.  Not leftover Ⅰ /         *)
(* Ⅱ / Ⅲ.  II nonempty at (1, 1/6).  Classifier emits                         *)
(* TPR_TouchOnesided.  Fill stays im_unsupported.  Do not remint the          *)
(* xor. Completeness is unnamed. Not CONTEXT Bar 1.                           *)
(* -------------------------------------------------------------------------- *)

Definition interior_side_pair_coords
    (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : Prop :=
  ax = 0 /\ ay = 0 /\ bx = 2 /\ by_ = 0 /\ cx = 0 /\ cy = 1 /\
  dx = 1 /\ dy = 0 /\ ex = (5/4) /\ ey = (1/4) /\ fx = (3/4) /\ fy = (1/4).

Lemma interior_side_pair_both_ccw :
  0 < gdbl 0 0 2 0 0 1 /\ 0 < gdbl 1 0 (5/4) (1/4) (3/4) (1/4).
Proof. unfold gdbl; split; lra. Qed.

Lemma interior_side_not_tjunction :
  ~ tjunction_pair_coords 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4).
Proof.
  intros [Hax [Hay [Hbx [Hby [Hcx [Hcy [Hdx [Hdy [Hex _]]]]]]]]].
  lra.
Qed.

Lemma interior_side_not_onesided_iii :
  ~ onesided_t_pair_coords 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4).
Proof.
  intros [Hax [Hay [Hbx [Hby [Hcx [Hcy [Hdx [Hdy [Hex [Hey _]]]]]]]]]].
  lra.
Qed.

(* Remaining B vertices share the supporting-line sign of A's apex. *)
Lemma interior_side_same_side :
  0 < cross (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1) /\
  0 < cross (mkPoint 0 0) (mkPoint 2 0) (mkPoint (5/4) (1/4)) /\
  0 < cross (mkPoint 0 0) (mkPoint 2 0) (mkPoint (3/4) (1/4)).
Proof. unfold cross; cbn [px py]; split; [|split]; lra. Qed.

Lemma interior_side_gtri_A_stem :
  gtri 0 0 2 0 0 1 (mkPoint 1 0) = 0.
Proof.
  unfold gtri.
  assert (HA : gsA 0 0 2 0 (mkPoint 1 0) = 0) by
    (unfold gsA; cbn [px py]; ring).
  rewrite HA.
  assert (HB : 0 <= gsB 2 0 0 1 (mkPoint 1 0)) by
    (unfold gsB; cbn [px py]; lra).
  assert (HC : 0 <= gsC 0 0 0 1 (mkPoint 1 0)) by
    (unfold gsC; cbn [px py]; lra).
  rewrite (Rmin_left _ _ HB).
  rewrite (Rmin_left _ _ HC).
  reflexivity.
Qed.

Lemma interior_side_gtri_A_e :
  0 < gtri 0 0 2 0 0 1 (mkPoint (5/4) (1/4)).
Proof.
  unfold gtri, gsA, gsB, gsC; cbn [px py].
  apply Rmin_pos_iff. split; [apply Rmin_pos_iff; split|]; lra.
Qed.

Lemma interior_side_gtri_A_f :
  0 < gtri 0 0 2 0 0 1 (mkPoint (3/4) (1/4)).
Proof.
  unfold gtri, gsA, gsB, gsC; cbn [px py].
  apply Rmin_pos_iff. split; [apply Rmin_pos_iff; split|]; lra.
Qed.

(* overlap_b needs an exterior B-vertex. Residue: none. *)
Lemma interior_side_overlap_b_false :
  overlap_b 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) = false.
Proof.
  unfold overlap_b, some_vertex_strict_pos, some_vertex_strict_neg,
         gtri_strict_pos_b, gtri_strict_neg_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (5/4) (1/4) (3/4) (1/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  pose proof interior_side_gtri_A_stem as Hs.
  pose proof interior_side_gtri_A_e as He.
  pose proof interior_side_gtri_A_f as Hf.
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 1 (mkPoint 1 0))) as [H1 | _];
    [ exfalso; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 1 (mkPoint (5/4) (1/4)))) as [_ | Hn];
    [ | exfalso; apply Hn; exact He ].
  destruct (Rlt_dec (gtri 0 0 2 0 0 1 (mkPoint 1 0)) 0) as [Hn | _];
    [ exfalso; lra | ].
  destruct (Rlt_dec (gtri 0 0 2 0 0 1 (mkPoint (5/4) (1/4))) 0) as [Hn | _];
    [ exfalso; lra | ].
  destruct (Rlt_dec (gtri 0 0 2 0 0 1 (mkPoint (3/4) (1/4))) 0) as [Hn | _];
    [ exfalso; lra | ].
  reflexivity.
Qed.

Lemma interior_side_contains_b_false :
  contains_b 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) = false.
Proof.
  unfold contains_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  pose proof interior_side_gtri_A_stem as Hs.
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 1 (mkPoint 1 0))) as [Hlt | _];
    [ exfalso; lra | ].
  reflexivity.
Qed.

(* Ticket 26: typically II nonempty. Do not call this areal Touches. *)
Lemma interior_side_ii_nonempty :
  exists p, 0 < gtri 0 0 2 0 0 1 p /\
            0 < gtri 1 0 (5/4) (1/4) (3/4) (1/4) p.
Proof.
  exists (mkPoint 1 (1/6)).
  split.
  { unfold gtri, gsA, gsB, gsC; cbn [px py].
    apply Rmin_pos_iff. split; [apply Rmin_pos_iff; split|]; lra. }
  { unfold gtri, gsA, gsB, gsC; cbn [px py].
    apply Rmin_pos_iff. split; [apply Rmin_pos_iff; split|]; lra. }
Qed.

Lemma interior_side_B_on_open_base :
  on_open_seg_b (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 0) = true.
Proof. exact onesided_t_B_on_open_base. Qed.

Lemma interior_side_one_sided :
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = true /\
  some_vertex_on_open_edges
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4))
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1) = false.
Proof.
  split.
  { unfold some_vertex_on_open_edges, vertex_on_open_edges.
    rewrite interior_side_B_on_open_base.
    reflexivity. }
  { unfold some_vertex_on_open_edges, vertex_on_open_edges,
           on_open_seg_b, cross.
    cbn [px py].
    repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
    repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
    reflexivity. }
Qed.

Lemma interior_side_no_shared_vertex :
  is_vertex_b (mkPoint 0 0)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = false /\
  is_vertex_b (mkPoint 2 0)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = false /\
  is_vertex_b (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = false.
Proof.
  split.
  { apply is_vertex_b_false_of_none;
      (apply mkPoint_neq_px; lra). }
  split.
  { apply is_vertex_b_false_of_none;
      (apply mkPoint_neq_px; lra). }
  { apply is_vertex_b_false_of_none;
      (apply mkPoint_neq_py; lra). }
Qed.

Lemma interior_side_no_separator :
  some_edge_separates_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = false.
Proof.
  unfold some_edge_separates_b.
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
             (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 2 0) (mkPoint 0 1) (mkPoint 0 0)
             (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 0 1) (mkPoint 0 0) (mkPoint 2 0)
             (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4))
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)).
  2: {
    apply opposite_sides_b_false_of_nlt.
    assert (Hprod : cross (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4))
                        * cross (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint 0 0) >= 0).
    { unfold cross; cbn [px py]; lra. }
    intros Hlt. lra. }
  rewrite (edge_separates_b_false_l (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) (mkPoint 1 0)
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)).
  2: {
    apply opposite_sides_b_false_of_nlt.
    assert (Hprod : cross (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) (mkPoint 1 0)
                        * cross (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) (mkPoint 0 0) >= 0).
    { unfold cross; cbn [px py]; lra. }
    intros Hlt. lra. }
  (* B's (3/4,1/4)–(1,0): A's (0,0) is opposite the apex. Pin (2,0)
     so lra never sees a true opposite-sides goal. Vertex order
     stays (0,0)(2,0)(0,1) — do not reorder q1. *)
  assert (E6 : edge_separates_b
                 (mkPoint (3/4) (1/4)) (mkPoint 1 0) (mkPoint (5/4) (1/4))
                 (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1) = false).
  { unfold edge_separates_b.
    assert (Hprod : cross (mkPoint (3/4) (1/4)) (mkPoint 1 0) (mkPoint (5/4) (1/4))
                        * cross (mkPoint (3/4) (1/4)) (mkPoint 1 0) (mkPoint 2 0) >= 0).
    { unfold cross; cbn [px py]; lra. }
    assert (Hmid : opposite_sides_b
                     (mkPoint (3/4) (1/4)) (mkPoint 1 0)
                     (mkPoint (5/4) (1/4)) (mkPoint 2 0) = false).
    { apply opposite_sides_b_false_of_nlt. intros Hlt. lra. }
    rewrite Hmid.
    destruct (opposite_sides_b (mkPoint (3/4) (1/4)) (mkPoint 1 0)
                (mkPoint (5/4) (1/4)) (mkPoint 0 0)); reflexivity. }
  rewrite E6.
  reflexivity.
Qed.

Lemma interior_side_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = false.
Proof.
  unfold touch_partial_edge_b.
  destruct interior_side_one_sided as [HA HB].
  rewrite HA, HB.
  reflexivity.
Qed.

Lemma interior_side_onesided_true :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = true.
Proof.
  unfold touch_onesided_t_b.
  destruct interior_side_one_sided as [HA HB].
  rewrite HA, HB.
  reflexivity.
Qed.

Lemma interior_side_pair_onesided :
  triangle_pair_regime 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4)
    = TPR_TouchOnesided.
Proof.
  unfold triangle_pair_regime, touch_edge_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  rewrite interior_side_contains_b_false.
  rewrite interior_side_overlap_b_false.
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (5/4) (1/4) (3/4) (1/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  rewrite interior_side_no_separator.
  unfold touch_vertex_b, exactly_one_shared_from_a, is_vertex_b, point_eqb.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (5/4) (1/4) (3/4) (1/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  rewrite interior_side_no_partial_edge.
  rewrite interior_side_onesided_true.
  reflexivity.
Qed.

(* WITNESS {"claimId":"Ⅳ","topic":"relate","lemma":"interior_side_pair_onesided","title":"Leftover Ⅳ interior-side stem classifies as TPR_TouchOnesided","file":"theories/RelateNGComplete.v","witness":"Ⅳ-interior-side-cex","board":"leftover-Ⅳ"} *)
Theorem interior_side_pair_inhabits :
  interior_side_pair_coords 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) /\
  0 < gdbl 0 0 2 0 0 1 /\
  0 < gdbl 1 0 (5/4) (1/4) (3/4) (1/4) /\
  on_open_seg_b (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 0) = true /\
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = true /\
  some_vertex_on_open_edges
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4))
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1) = false /\
  ~ tjunction_pair_coords 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) /\
  ~ onesided_t_pair_coords 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) /\
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = false /\
  is_vertex_b (mkPoint 0 0)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = false /\
  is_vertex_b (mkPoint 2 0)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = false /\
  is_vertex_b (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = false /\
  0 < cross (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1) /\
  0 < cross (mkPoint 0 0) (mkPoint 2 0) (mkPoint (5/4) (1/4)) /\
  0 < cross (mkPoint 0 0) (mkPoint 2 0) (mkPoint (3/4) (1/4)) /\
  overlap_b 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) = false /\
  contains_b 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) = false /\
  (exists p, 0 < gtri 0 0 2 0 0 1 p /\
             0 < gtri 1 0 (5/4) (1/4) (3/4) (1/4) p) /\
  triangle_pair_regime 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4)
    = TPR_TouchOnesided.
Proof.
  split; [repeat split; reflexivity|].
  split; [unfold gdbl; lra|].
  split; [unfold gdbl; lra|].
  split; [exact interior_side_B_on_open_base|].
  destruct interior_side_one_sided as [Hone Hrev].
  split; [exact Hone|].
  split; [exact Hrev|].
  split; [exact interior_side_not_tjunction|].
  split; [exact interior_side_not_onesided_iii|].
  split; [exact interior_side_no_partial_edge|].
  destruct interior_side_no_shared_vertex as [Hv1 [Hv2 Hv3]].
  split; [exact Hv1|].
  split; [exact Hv2|].
  split; [exact Hv3|].
  destruct interior_side_same_side as [Hs1 [Hs2 Hs3]].
  split; [exact Hs1|].
  split; [exact Hs2|].
  split; [exact Hs3|].
  split; [exact interior_side_overlap_b_false|].
  split; [exact interior_side_contains_b_false|].
  split; [exact interior_side_ii_nonempty|].
  exact interior_side_pair_onesided.
Qed.

Print Assumptions interior_side_pair_onesided.
Print Assumptions interior_side_pair_inhabits.
Print Assumptions interior_side_onesided_true.
Print Assumptions interior_side_overlap_b_false.
Print Assumptions interior_side_same_side.
Print Assumptions interior_side_ii_nonempty.
Print Assumptions interior_side_B_on_open_base.
Print Assumptions interior_side_one_sided.
Print Assumptions interior_side_no_shared_vertex.
