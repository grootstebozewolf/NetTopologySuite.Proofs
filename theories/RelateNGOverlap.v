(* ============================================================================
   NetTopologySuite.Proofs.RelateNGOverlap
   ----------------------------------------------------------------------------
   Issue #570 / #522 claimId 522-b: TPR_Overlap reachable at relate bar
   level 1.

   `overlap_b` (RelateNGCore) is a sound-but-partial certificate: both
   triangles CCW, a vertex of B strictly interior to A, a vertex of B
   strictly exterior to A, and a vertex of A strictly exterior to B.
   This file derives the earlier classifier branches false (not assumed)
   and lifts the flag to `triangles_partial_overlap` by a convexity
   nudge from the certified B-vertex toward B's centroid.  `gtri` is a
   min of affine slacks, hence concave, so an explicit parameter
   `overlap_nudge_t` keeps the combination interior to A while entering
   B's specified interior.

   Frozen anchors stay untouched: `touch_int_ext_exclusion` and the
   II-guard maximality refutation.  `triangles_touch_on_shared_edge`
   is not referenced.

   WITNESS topic: relate · claimId: 522-b · witness: 522-b-overlap-bar1
   macro: relate
   lane: proofs
   issue: #570 / #522
   ADR-0004: not a remint. 522-b is the existing #570 ticket id.

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
From NTS.Proofs Require Import RelateNGCore RelateNGContains.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Slack arithmetic (section-free; no CCW hypothesis).                        *)
(* -------------------------------------------------------------------------- *)

Lemma gtri_pos_slacks : forall ax ay bx by_ cx cy p,
  0 < gtri ax ay bx by_ cx cy p ->
  0 < gsA ax ay bx by_ p /\
  0 < gsB bx by_ cx cy p /\
  0 < gsC ax ay cx cy p.
Proof.
  intros ax ay bx by_ cx cy p H.
  unfold gtri in H. rewrite !Rmin_pos_iff in H. tauto.
Qed.

Lemma gdbl_eq_slack_sum : forall ax ay bx by_ cx cy p,
  gsA ax ay bx by_ p + gsB bx by_ cx cy p + gsC ax ay cx cy p =
  gdbl ax ay bx by_ cx cy.
Proof. intros; unfold gsA, gsB, gsC, gdbl; ring. Qed.

Lemma gtri_pos_ccw : forall ax ay bx by_ cx cy p,
  0 < gtri ax ay bx by_ cx cy p -> 0 < gdbl ax ay bx by_ cx cy.
Proof.
  intros ax ay bx by_ cx cy p H.
  apply gtri_pos_slacks in H as [HA [HB HC]].
  pose proof (gdbl_eq_slack_sum ax ay bx by_ cx cy p) as Hs.
  lra.
Qed.

Lemma Rmin_lt_or : forall a b, Rmin a b < 0 -> a < 0 \/ b < 0.
Proof.
  intros a b H. unfold Rmin in H. destruct (Rle_dec a b); lra.
Qed.

Lemma gtri_neg_some_slack : forall ax ay bx by_ cx cy p,
  gtri ax ay bx by_ cx cy p < 0 ->
  gsA ax ay bx by_ p < 0 \/
  gsB bx by_ cx cy p < 0 \/
  gsC ax ay cx cy p < 0.
Proof.
  intros ax ay bx by_ cx cy p H.
  unfold gtri in H.
  apply Rmin_lt_or in H as [H1 | H3].
  - apply Rmin_lt_or in H1. tauto.
  - tauto.
Qed.

Lemma gsA_eq_cross : forall ax ay bx by_ p,
  gsA ax ay bx by_ p = cross (mkPoint ax ay) (mkPoint bx by_) p.
Proof. intros; unfold gsA, cross; simpl; ring. Qed.

Lemma gsB_eq_cross : forall bx by_ cx cy p,
  gsB bx by_ cx cy p = cross (mkPoint bx by_) (mkPoint cx cy) p.
Proof. intros; unfold gsB, cross; simpl; ring. Qed.

Lemma gsC_eq_cross : forall ax ay cx cy p,
  gsC ax ay cx cy p = cross (mkPoint cx cy) (mkPoint ax ay) p.
Proof. intros; unfold gsC, cross; simpl; ring. Qed.

Lemma gdbl_eq_cross : forall ax ay bx by_ cx cy,
  gdbl ax ay bx by_ cx cy =
  cross (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy).
Proof. intros; unfold gdbl, cross; simpl; ring. Qed.

Lemma cross_BCA_eq_gdbl : forall ax ay bx by_ cx cy,
  cross (mkPoint bx by_) (mkPoint cx cy) (mkPoint ax ay) =
  gdbl ax ay bx by_ cx cy.
Proof. intros; unfold gdbl, cross; simpl; ring. Qed.

Lemma cross_CAB_eq_gdbl : forall ax ay bx by_ cx cy,
  cross (mkPoint cx cy) (mkPoint ax ay) (mkPoint bx by_) =
  gdbl ax ay bx by_ cx cy.
Proof. intros; unfold gdbl, cross; simpl; ring. Qed.

(* -------------------------------------------------------------------------- *)
(* Affine slacks and concave gtri.                                            *)
(* -------------------------------------------------------------------------- *)

Lemma gsA_affine : forall ax ay bx by_ P Q t,
  gsA ax ay bx by_ (convex_combination P Q t) =
  (1 - t) * gsA ax ay bx by_ P + t * gsA ax ay bx by_ Q.
Proof. intros; unfold gsA, convex_combination; simpl; ring. Qed.

Lemma gsB_affine : forall bx by_ cx cy P Q t,
  gsB bx by_ cx cy (convex_combination P Q t) =
  (1 - t) * gsB bx by_ cx cy P + t * gsB bx by_ cx cy Q.
Proof. intros; unfold gsB, convex_combination; simpl; ring. Qed.

Lemma gsC_affine : forall ax ay cx cy P Q t,
  gsC ax ay cx cy (convex_combination P Q t) =
  (1 - t) * gsC ax ay cx cy P + t * gsC ax ay cx cy Q.
Proof. intros; unfold gsC, convex_combination; simpl; ring. Qed.

Lemma Rmin_ge_both : forall x y z, x <= y -> x <= z -> x <= Rmin y z.
Proof.
  intros x y z Hy Hz. unfold Rmin. destruct (Rle_dec y z); lra.
Qed.

Lemma Rmin_ge_convex : forall a b c d t,
  0 <= t -> t <= 1 ->
  (1 - t) * Rmin a b + t * Rmin c d <=
  Rmin ((1 - t) * a + t * c) ((1 - t) * b + t * d).
Proof.
  intros a b c d t Ht0 Ht1.
  apply Rmin_ge_both.
  - pose proof (Rmin_l a b). pose proof (Rmin_l c d). nra.
  - pose proof (Rmin_r a b). pose proof (Rmin_r c d). nra.
Qed.

Lemma Rmin_le_compat_l : forall x y z, x <= y -> Rmin x z <= Rmin y z.
Proof.
  intros x y z Hxy. unfold Rmin.
  destruct (Rle_dec x z); destruct (Rle_dec y z); lra.
Qed.

Lemma gtri_concave : forall ax ay bx by_ cx cy P Q t,
  0 <= t -> t <= 1 ->
  (1 - t) * gtri ax ay bx by_ cx cy P
  + t * gtri ax ay bx by_ cx cy Q <=
  gtri ax ay bx by_ cx cy (convex_combination P Q t).
Proof.
  intros ax ay bx by_ cx cy P Q t Ht0 Ht1.
  unfold gtri.
  rewrite gsA_affine, gsB_affine, gsC_affine.
  eapply Rle_trans.
  - apply (Rmin_ge_convex (Rmin (gsA ax ay bx by_ P) (gsB bx by_ cx cy P))
             (gsC ax ay cx cy P)
             (Rmin (gsA ax ay bx by_ Q) (gsB bx by_ cx cy Q))
             (gsC ax ay cx cy Q) t Ht0 Ht1).
  - apply Rmin_le_compat_l.
    apply (Rmin_ge_convex (gsA ax ay bx by_ P) (gsB bx by_ cx cy P)
             (gsA ax ay bx by_ Q) (gsB bx by_ cx cy Q) t Ht0 Ht1).
Qed.

(* -------------------------------------------------------------------------- *)
(* Centroid of a CCW triangle is strictly interior.                           *)
(* -------------------------------------------------------------------------- *)

Lemma gsA_centroid3 : forall ax ay bx by_ cx cy,
  gsA ax ay bx by_
    (centroid3 (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)) =
  gdbl ax ay bx by_ cx cy / 3.
Proof. intros; unfold gsA, gdbl, centroid3; simpl; field. Qed.

Lemma gsB_centroid3 : forall ax ay bx by_ cx cy,
  gsB bx by_ cx cy
    (centroid3 (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)) =
  gdbl ax ay bx by_ cx cy / 3.
Proof. intros; unfold gsB, gdbl, centroid3; simpl; field. Qed.

Lemma gsC_centroid3 : forall ax ay bx by_ cx cy,
  gsC ax ay cx cy
    (centroid3 (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)) =
  gdbl ax ay bx by_ cx cy / 3.
Proof. intros; unfold gsC, gdbl, centroid3; simpl; field. Qed.

Lemma gtri_centroid3_eq : forall ax ay bx by_ cx cy,
  gtri ax ay bx by_ cx cy
    (centroid3 (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)) =
  gdbl ax ay bx by_ cx cy / 3.
Proof.
  intros ax ay bx by_ cx cy.
  unfold gtri.
  rewrite gsA_centroid3, gsB_centroid3, gsC_centroid3.
  rewrite (Rmin_left (gdbl ax ay bx by_ cx cy / 3)
                     (gdbl ax ay bx by_ cx cy / 3)) by apply Rle_refl.
  rewrite (Rmin_left (gdbl ax ay bx by_ cx cy / 3)
                     (gdbl ax ay bx by_ cx cy / 3)) by apply Rle_refl.
  reflexivity.
Qed.

Lemma gtri_centroid3_pos : forall ax ay bx by_ cx cy,
  0 < gdbl ax ay bx by_ cx cy ->
  0 < gtri ax ay bx by_ cx cy
         (centroid3 (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)).
Proof.
  intros ax ay bx by_ cx cy H.
  rewrite gtri_centroid3_eq. lra.
Qed.

Lemma gtri_at_vertex_a_eq0 : forall ax ay bx by_ cx cy,
  0 < gdbl ax ay bx by_ cx cy ->
  gtri ax ay bx by_ cx cy (mkPoint ax ay) = 0.
Proof.
  intros ax ay bx by_ cx cy Hccw.
  unfold gtri.
  assert (HA : gsA ax ay bx by_ (mkPoint ax ay) = 0)
    by (unfold gsA; simpl; ring).
  assert (HC : gsC ax ay cx cy (mkPoint ax ay) = 0)
    by (unfold gsC; simpl; ring).
  assert (HB : gsB bx by_ cx cy (mkPoint ax ay) = gdbl ax ay bx by_ cx cy)
    by (unfold gsB, gdbl; simpl; ring).
  rewrite HA, HB, HC.
  rewrite (Rmin_left 0 (gdbl ax ay bx by_ cx cy)) by (apply Rlt_le; exact Hccw).
  rewrite (Rmin_left 0 0) by apply Rle_refl.
  reflexivity.
Qed.

Lemma gtri_at_vertex_b_eq0 : forall ax ay bx by_ cx cy,
  0 < gdbl ax ay bx by_ cx cy ->
  gtri ax ay bx by_ cx cy (mkPoint bx by_) = 0.
Proof.
  intros ax ay bx by_ cx cy Hccw.
  unfold gtri.
  assert (HA : gsA ax ay bx by_ (mkPoint bx by_) = 0)
    by (unfold gsA; simpl; ring).
  assert (HB : gsB bx by_ cx cy (mkPoint bx by_) = 0)
    by (unfold gsB; simpl; ring).
  assert (HC : gsC ax ay cx cy (mkPoint bx by_) = gdbl ax ay bx by_ cx cy)
    by (unfold gsC, gdbl; simpl; ring).
  rewrite HA, HB, HC.
  rewrite (Rmin_left 0 0) by apply Rle_refl.
  rewrite (Rmin_left 0 (gdbl ax ay bx by_ cx cy)) by (apply Rlt_le; exact Hccw).
  reflexivity.
Qed.

Lemma gtri_at_vertex_c_eq0 : forall ax ay bx by_ cx cy,
  0 < gdbl ax ay bx by_ cx cy ->
  gtri ax ay bx by_ cx cy (mkPoint cx cy) = 0.
Proof.
  intros ax ay bx by_ cx cy Hccw.
  unfold gtri.
  assert (HB : gsB bx by_ cx cy (mkPoint cx cy) = 0)
    by (unfold gsB; simpl; ring).
  assert (HC : gsC ax ay cx cy (mkPoint cx cy) = 0)
    by (unfold gsC; simpl; ring).
  assert (HA : gsA ax ay bx by_ (mkPoint cx cy) = gdbl ax ay bx by_ cx cy)
    by (unfold gsA, gdbl; simpl; ring).
  rewrite HA, HB, HC.
  rewrite (Rmin_right (gdbl ax ay bx by_ cx cy) 0) by (apply Rlt_le; exact Hccw).
  rewrite (Rmin_left 0 0) by apply Rle_refl.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Explicit nudge parameter.                                                  *)
(* -------------------------------------------------------------------------- *)

Definition overlap_nudge_t (g0 gc : R) : R :=
  g0 / (g0 + 1 + Rabs gc).

Lemma overlap_nudge_t_range : forall g0 gc,
  0 < g0 ->
  0 < overlap_nudge_t g0 gc < 1.
Proof.
  intros g0 gc Hg0.
  unfold overlap_nudge_t, Rdiv.
  pose proof (Rabs_pos gc) as Habs.
  split.
  - apply Rmult_lt_0_compat; [ exact Hg0 | apply Rinv_0_lt_compat; lra ].
  - apply Rmult_lt_reg_r with (r := g0 + 1 + Rabs gc); [ lra | ].
    replace (g0 * / (g0 + 1 + Rabs gc) * (g0 + 1 + Rabs gc)) with g0
      by (field; lra).
    lra.
Qed.

Lemma overlap_nudge_t_keeps_pos : forall g0 gc,
  0 < g0 ->
  0 < (1 - overlap_nudge_t g0 gc) * g0 + overlap_nudge_t g0 gc * gc.
Proof.
  intros g0 gc Hg0.
  unfold overlap_nudge_t, Rdiv.
  pose proof (Rabs_pos gc) as Habs.
  pose proof (Rle_abs gc) as Hle.
  set (d := g0 + 1 + Rabs gc).
  assert (Hd : 0 < d) by (unfold d; lra).
  replace (1 - g0 * / d) with ((1 + Rabs gc) / d)
    by (unfold d; field; lra).
  unfold Rdiv.
  replace ((1 + Rabs gc) * / d * g0 + g0 * / d * gc)
    with (g0 * (1 + Rabs gc + gc) / d)
    by (unfold Rdiv; field; lra).
  unfold Rdiv.
  apply Rmult_lt_0_compat; [ | apply Rinv_0_lt_compat; exact Hd ].
  destruct (Rle_dec 0 gc) as [Hge | Hn].
  - rewrite (Rabs_right gc) by lra. nra.
  - apply Rnot_le_lt in Hn. rewrite (Rabs_left gc) by lra. nra.
Qed.

Definition slack_neg_nudge_t (sv sc : R) : R :=
  (- sv) / ((- sv) + 1 + Rabs sc).

Lemma slack_neg_nudge_t_range : forall sv sc,
  sv < 0 ->
  0 < slack_neg_nudge_t sv sc < 1.
Proof.
  intros sv sc Hsv.
  unfold slack_neg_nudge_t.
  pose proof (Rabs_pos sc) as Habs.
  split.
  - apply Rdiv_lt_0_compat; lra.
  - apply Rmult_lt_reg_r with (r := (- sv) + 1 + Rabs sc); [ lra | ].
    unfold Rdiv.
    replace ((- sv) * / ((- sv) + 1 + Rabs sc)
             * ((- sv) + 1 + Rabs sc)) with (- sv) by (field; lra).
    lra.
Qed.

Lemma slack_neg_nudge_keeps_neg : forall sv sc,
  sv < 0 ->
  (1 - slack_neg_nudge_t sv sc) * sv + slack_neg_nudge_t sv sc * sc < 0.
Proof.
  intros sv sc Hsv.
  unfold slack_neg_nudge_t, Rdiv.
  set (d := (- sv) + 1 + Rabs sc).
  assert (Hd : 0 < d) by (unfold d; pose proof (Rabs_pos sc); lra).
  assert (Hdnz : d <> 0) by lra.
  replace (1 - (- sv) * / d) with ((1 + Rabs sc) * / d)
    by (unfold d; field; exact Hdnz).
  replace ((1 + Rabs sc) * / d * sv + (- sv) * / d * sc)
    with (sv * (1 + Rabs sc - sc) * / d)
    by (field; exact Hdnz).
  assert (0 < 1 + Rabs sc - sc).
  { destruct (Rle_dec 0 sc) as [Hge | Hn].
    - rewrite (Rabs_right sc) by lra. lra.
    - apply Rnot_le_lt in Hn. rewrite (Rabs_left sc) by lra. lra. }
  set (k := 1 + Rabs sc - sc).
  assert (Hk : 0 < k) by (unfold k; assumption).
  replace (sv * k * / d) with (- ((- sv) * k * / d)) by ring.
  apply Ropp_lt_gt_0_contravar.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat; [ lra | exact Hk ].
  - apply Rinv_0_lt_compat; exact Hd.
Qed.

(* -------------------------------------------------------------------------- *)
(* Interior / exterior witnesses from the certificate vertices.               *)
(* -------------------------------------------------------------------------- *)

Lemma combo_in_A_from_B_interior :
  forall ax ay bx by_ cx cy v c,
    0 < gtri ax ay bx by_ cx cy v ->
    let t := overlap_nudge_t (gtri ax ay bx by_ cx cy v)
                             (gtri ax ay bx by_ cx cy c) in
    0 < gtri ax ay bx by_ cx cy (convex_combination v c t).
Proof.
  intros ax ay bx by_ cx cy v c Hv t.
  pose proof (overlap_nudge_t_range _ (gtri ax ay bx by_ cx cy c) Hv)
    as [Ht0 Ht1].
  pose proof (overlap_nudge_t_keeps_pos _ (gtri ax ay bx by_ cx cy c) Hv)
    as Hkeep.
  pose proof (gtri_concave ax ay bx by_ cx cy v c t (Rlt_le _ _ Ht0)
                (Rlt_le _ _ Ht1)) as Hconc.
  unfold t in *.
  eapply Rlt_le_trans; [ exact Hkeep | exact Hconc ].
Qed.

Lemma combo_in_B_from_B_vertex_a :
  forall dx dy ex ey fx fy t,
    0 < gdbl dx dy ex ey fx fy ->
    0 < t -> t <= 1 ->
    0 < gtri dx dy ex ey fx fy
           (convex_combination (mkPoint dx dy)
              (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)) t).
Proof.
  intros dx dy ex ey fx fy t Hccw Ht0 Ht1.
  pose proof (gtri_at_vertex_a_eq0 dx dy ex ey fx fy Hccw) as Hv.
  pose proof (gtri_centroid3_pos dx dy ex ey fx fy Hccw) as Hc.
  pose proof (gtri_concave dx dy ex ey fx fy (mkPoint dx dy)
                (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy))
                t (Rlt_le _ _ Ht0) Ht1) as Hconc.
  rewrite Hv in Hconc.
  eapply Rlt_le_trans; [ | exact Hconc ].
  nra.
Qed.

Lemma combo_in_B_from_B_vertex_b :
  forall dx dy ex ey fx fy t,
    0 < gdbl dx dy ex ey fx fy ->
    0 < t -> t <= 1 ->
    0 < gtri dx dy ex ey fx fy
           (convex_combination (mkPoint ex ey)
              (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)) t).
Proof.
  intros dx dy ex ey fx fy t Hccw Ht0 Ht1.
  pose proof (gtri_at_vertex_b_eq0 dx dy ex ey fx fy Hccw) as Hv.
  pose proof (gtri_centroid3_pos dx dy ex ey fx fy Hccw) as Hc.
  pose proof (gtri_concave dx dy ex ey fx fy (mkPoint ex ey)
                (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy))
                t (Rlt_le _ _ Ht0) Ht1) as Hconc.
  rewrite Hv in Hconc.
  eapply Rlt_le_trans; [ | exact Hconc ].
  nra.
Qed.

Lemma combo_in_B_from_B_vertex_c :
  forall dx dy ex ey fx fy t,
    0 < gdbl dx dy ex ey fx fy ->
    0 < t -> t <= 1 ->
    0 < gtri dx dy ex ey fx fy
           (convex_combination (mkPoint fx fy)
              (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)) t).
Proof.
  intros dx dy ex ey fx fy t Hccw Ht0 Ht1.
  pose proof (gtri_at_vertex_c_eq0 dx dy ex ey fx fy Hccw) as Hv.
  pose proof (gtri_centroid3_pos dx dy ex ey fx fy Hccw) as Hc.
  pose proof (gtri_concave dx dy ex ey fx fy (mkPoint fx fy)
                (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy))
                t (Rlt_le _ _ Ht0) Ht1) as Hconc.
  rewrite Hv in Hconc.
  eapply Rlt_le_trans; [ | exact Hconc ].
  nra.
Qed.

Lemma combo_stays_neg_of_slack_A :
  forall ax ay bx by_ cx cy v c sv,
    sv = gsA ax ay bx by_ v ->
    sv < 0 ->
    let t := slack_neg_nudge_t sv (gsA ax ay bx by_ c) in
    gtri ax ay bx by_ cx cy (convex_combination v c t) < 0.
Proof.
  intros ax ay bx by_ cx cy v c sv Heq Hsv t.
  subst sv.
  pose proof (slack_neg_nudge_keeps_neg (gsA ax ay bx by_ v)
                (gsA ax ay bx by_ c) Hsv) as Hneg.
  unfold t.
  eapply Rle_lt_trans;
    [ apply (gtri_le_gsA ax ay bx by_ cx cy (convex_combination v c _)) | ].
  rewrite gsA_affine. exact Hneg.
Qed.

Lemma combo_stays_neg_of_slack_B :
  forall ax ay bx by_ cx cy v c sv,
    sv = gsB bx by_ cx cy v ->
    sv < 0 ->
    let t := slack_neg_nudge_t sv (gsB bx by_ cx cy c) in
    gtri ax ay bx by_ cx cy (convex_combination v c t) < 0.
Proof.
  intros ax ay bx by_ cx cy v c sv Heq Hsv t.
  subst sv.
  pose proof (slack_neg_nudge_keeps_neg (gsB bx by_ cx cy v)
                (gsB bx by_ cx cy c) Hsv) as Hneg.
  unfold t.
  eapply Rle_lt_trans;
    [ apply (gtri_le_gsB ax ay bx by_ cx cy (convex_combination v c _)) | ].
  rewrite gsB_affine. exact Hneg.
Qed.

Lemma combo_stays_neg_of_slack_C :
  forall ax ay bx by_ cx cy v c sv,
    sv = gsC ax ay cx cy v ->
    sv < 0 ->
    let t := slack_neg_nudge_t sv (gsC ax ay cx cy c) in
    gtri ax ay bx by_ cx cy (convex_combination v c t) < 0.
Proof.
  intros ax ay bx by_ cx cy v c sv Heq Hsv t.
  subst sv.
  pose proof (slack_neg_nudge_keeps_neg (gsC ax ay cx cy v)
                (gsC ax ay cx cy c) Hsv) as Hneg.
  unfold t.
  eapply Rle_lt_trans;
    [ apply (gtri_le_gsC ax ay bx by_ cx cy (convex_combination v c _)) | ].
  rewrite gsC_affine. exact Hneg.
Qed.

(* A point that is interior to both, given a B-vertex interior to A. *)
Lemma ii_witness_of_B_vertex_a :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    0 < gdbl dx dy ex ey fx fy ->
    0 < gtri ax ay bx by_ cx cy (mkPoint dx dy) ->
    exists pt,
      in_tri_interior (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) pt /\
      in_tri_interior (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) pt.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy HccwB Hin.
  set (cB := centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)).
  set (t := overlap_nudge_t (gtri ax ay bx by_ cx cy (mkPoint dx dy))
                            (gtri ax ay bx by_ cx cy cB)).
  exists (convex_combination (mkPoint dx dy) cB t).
  split.
  - unfold in_tri_interior. subst t cB.
    exact (combo_in_A_from_B_interior ax ay bx by_ cx cy
             (mkPoint dx dy)
             (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)) Hin).
  - unfold in_tri_interior. subst t cB.
    pose proof (overlap_nudge_t_range
                  (gtri ax ay bx by_ cx cy (mkPoint dx dy))
                  (gtri ax ay bx by_ cx cy
                     (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)))
                  Hin) as [Ht0 Ht1].
    exact (combo_in_B_from_B_vertex_a dx dy ex ey fx fy _ HccwB Ht0
             (Rlt_le _ _ Ht1)).
Qed.

Lemma ii_witness_of_B_vertex_b :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    0 < gdbl dx dy ex ey fx fy ->
    0 < gtri ax ay bx by_ cx cy (mkPoint ex ey) ->
    exists pt,
      in_tri_interior (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) pt /\
      in_tri_interior (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) pt.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy HccwB Hin.
  set (cB := centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)).
  set (t := overlap_nudge_t (gtri ax ay bx by_ cx cy (mkPoint ex ey))
                            (gtri ax ay bx by_ cx cy cB)).
  exists (convex_combination (mkPoint ex ey) cB t).
  split.
  - unfold in_tri_interior. subst t cB.
    exact (combo_in_A_from_B_interior ax ay bx by_ cx cy
             (mkPoint ex ey)
             (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)) Hin).
  - unfold in_tri_interior. subst t cB.
    pose proof (overlap_nudge_t_range
                  (gtri ax ay bx by_ cx cy (mkPoint ex ey))
                  (gtri ax ay bx by_ cx cy
                     (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)))
                  Hin) as [Ht0 Ht1].
    exact (combo_in_B_from_B_vertex_b dx dy ex ey fx fy _ HccwB Ht0
             (Rlt_le _ _ Ht1)).
Qed.

Lemma ii_witness_of_B_vertex_c :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    0 < gdbl dx dy ex ey fx fy ->
    0 < gtri ax ay bx by_ cx cy (mkPoint fx fy) ->
    exists pt,
      in_tri_interior (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) pt /\
      in_tri_interior (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) pt.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy HccwB Hin.
  set (cB := centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)).
  set (t := overlap_nudge_t (gtri ax ay bx by_ cx cy (mkPoint fx fy))
                            (gtri ax ay bx by_ cx cy cB)).
  exists (convex_combination (mkPoint fx fy) cB t).
  split.
  - unfold in_tri_interior. subst t cB.
    exact (combo_in_A_from_B_interior ax ay bx by_ cx cy
             (mkPoint fx fy)
             (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)) Hin).
  - unfold in_tri_interior. subst t cB.
    pose proof (overlap_nudge_t_range
                  (gtri ax ay bx by_ cx cy (mkPoint fx fy))
                  (gtri ax ay bx by_ cx cy
                     (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)))
                  Hin) as [Ht0 Ht1].
    exact (combo_in_B_from_B_vertex_c dx dy ex ey fx fy _ HccwB Ht0
             (Rlt_le _ _ Ht1)).
Qed.

(* Exterior-to-A / interior-to-B: nudge a B-vertex that sits outside A
   toward B's centroid, keeping the negative A-slack. *)
Lemma bext_A_of_B_vertex :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy v,
    0 < gdbl dx dy ex ey fx fy ->
    (v = mkPoint dx dy \/ v = mkPoint ex ey \/ v = mkPoint fx fy) ->
    gtri ax ay bx by_ cx cy v < 0 ->
    exists pt,
      in_tri_interior (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) pt /\
      in_tri_exterior (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) pt.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy v HccwB Hv Hneg.
  set (cB := centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)).
  apply gtri_neg_some_slack in Hneg as [HA | [HB | HC]].
  - set (t := slack_neg_nudge_t (gsA ax ay bx by_ v) (gsA ax ay bx by_ cB)).
    exists (convex_combination v cB t).
    split.
    + unfold in_tri_interior. subst t cB.
      pose proof (slack_neg_nudge_t_range (gsA ax ay bx by_ v)
                    (gsA ax ay bx by_ (centroid3 (mkPoint dx dy)
                       (mkPoint ex ey) (mkPoint fx fy))) HA) as [Ht0 Ht1].
      destruct Hv as [-> | [-> | ->]].
      * exact (combo_in_B_from_B_vertex_a dx dy ex ey fx fy _ HccwB Ht0
                 (Rlt_le _ _ Ht1)).
      * exact (combo_in_B_from_B_vertex_b dx dy ex ey fx fy _ HccwB Ht0
                 (Rlt_le _ _ Ht1)).
      * exact (combo_in_B_from_B_vertex_c dx dy ex ey fx fy _ HccwB Ht0
                 (Rlt_le _ _ Ht1)).
    + unfold in_tri_exterior. subst t cB.
      exact (combo_stays_neg_of_slack_A ax ay bx by_ cx cy v
               (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy))
               _ eq_refl HA).
  - set (t := slack_neg_nudge_t (gsB bx by_ cx cy v) (gsB bx by_ cx cy cB)).
    exists (convex_combination v cB t).
    split.
    + unfold in_tri_interior. subst t cB.
      pose proof (slack_neg_nudge_t_range (gsB bx by_ cx cy v)
                    (gsB bx by_ cx cy (centroid3 (mkPoint dx dy)
                       (mkPoint ex ey) (mkPoint fx fy))) HB) as [Ht0 Ht1].
      destruct Hv as [-> | [-> | ->]].
      * exact (combo_in_B_from_B_vertex_a dx dy ex ey fx fy _ HccwB Ht0
                 (Rlt_le _ _ Ht1)).
      * exact (combo_in_B_from_B_vertex_b dx dy ex ey fx fy _ HccwB Ht0
                 (Rlt_le _ _ Ht1)).
      * exact (combo_in_B_from_B_vertex_c dx dy ex ey fx fy _ HccwB Ht0
                 (Rlt_le _ _ Ht1)).
    + unfold in_tri_exterior. subst t cB.
      exact (combo_stays_neg_of_slack_B ax ay bx by_ cx cy v
               (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy))
               _ eq_refl HB).
  - set (t := slack_neg_nudge_t (gsC ax ay cx cy v) (gsC ax ay cx cy cB)).
    exists (convex_combination v cB t).
    split.
    + unfold in_tri_interior. subst t cB.
      pose proof (slack_neg_nudge_t_range (gsC ax ay cx cy v)
                    (gsC ax ay cx cy (centroid3 (mkPoint dx dy)
                       (mkPoint ex ey) (mkPoint fx fy))) HC) as [Ht0 Ht1].
      destruct Hv as [-> | [-> | ->]].
      * exact (combo_in_B_from_B_vertex_a dx dy ex ey fx fy _ HccwB Ht0
                 (Rlt_le _ _ Ht1)).
      * exact (combo_in_B_from_B_vertex_b dx dy ex ey fx fy _ HccwB Ht0
                 (Rlt_le _ _ Ht1)).
      * exact (combo_in_B_from_B_vertex_c dx dy ex ey fx fy _ HccwB Ht0
                 (Rlt_le _ _ Ht1)).
    + unfold in_tri_exterior. subst t cB.
      exact (combo_stays_neg_of_slack_C ax ay bx by_ cx cy v
               (centroid3 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy))
               _ eq_refl HC).
Qed.

(* Interior-to-A / exterior-to-B: nudge an A-vertex that sits outside B
   toward A's centroid. *)
Lemma aext_B_of_A_vertex :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy v,
    0 < gdbl ax ay bx by_ cx cy ->
    (v = mkPoint ax ay \/ v = mkPoint bx by_ \/ v = mkPoint cx cy) ->
    gtri dx dy ex ey fx fy v < 0 ->
    exists pt,
      in_tri_interior (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) pt /\
      in_tri_exterior (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) pt.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy v HccwA Hv Hneg.
  destruct (bext_A_of_B_vertex dx dy ex ey fx fy ax ay bx by_ cx cy v
              HccwA Hv Hneg) as [pt [HiA HeB]].
  exists pt. split; [ exact HiA | exact HeB ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Earlier branches derived false.                                            *)
(* -------------------------------------------------------------------------- *)

Lemma opposite_sides_b_false_AB : forall ax ay bx by_ cx cy p,
  0 < gtri ax ay bx by_ cx cy p ->
  opposite_sides_b (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) p = false.
Proof.
  intros ax ay bx by_ cx cy p Hp.
  unfold opposite_sides_b.
  rewrite <- gdbl_eq_cross, <- gsA_eq_cross.
  apply gtri_pos_slacks in Hp as [HA [HB HC]].
  pose proof (gdbl_eq_slack_sum ax ay bx by_ cx cy p) as Hs.
  destruct (Rlt_dec (gdbl ax ay bx by_ cx cy * gsA ax ay bx by_ p) 0)
    as [Hlt | _]; [ exfalso; nra | reflexivity ].
Qed.

Lemma opposite_sides_b_false_BC : forall ax ay bx by_ cx cy p,
  0 < gtri ax ay bx by_ cx cy p ->
  opposite_sides_b (mkPoint bx by_) (mkPoint cx cy) (mkPoint ax ay) p = false.
Proof.
  intros ax ay bx by_ cx cy p Hp.
  unfold opposite_sides_b.
  rewrite cross_BCA_eq_gdbl, <- gsB_eq_cross.
  apply gtri_pos_slacks in Hp as [HA [HB HC]].
  pose proof (gdbl_eq_slack_sum ax ay bx by_ cx cy p) as Hs.
  destruct (Rlt_dec (gdbl ax ay bx by_ cx cy * gsB bx by_ cx cy p) 0)
    as [Hlt | _]; [ exfalso; nra | reflexivity ].
Qed.

Lemma opposite_sides_b_false_CA : forall ax ay bx by_ cx cy p,
  0 < gtri ax ay bx by_ cx cy p ->
  opposite_sides_b (mkPoint cx cy) (mkPoint ax ay) (mkPoint bx by_) p = false.
Proof.
  intros ax ay bx by_ cx cy p Hp.
  unfold opposite_sides_b.
  rewrite cross_CAB_eq_gdbl, <- gsC_eq_cross.
  apply gtri_pos_slacks in Hp as [HA [HB HC]].
  pose proof (gdbl_eq_slack_sum ax ay bx by_ cx cy p) as Hs.
  destruct (Rlt_dec (gdbl ax ay bx by_ cx cy * gsC ax ay cx cy p) 0)
    as [Hlt | _]; [ exfalso; nra | reflexivity ].
Qed.

Lemma shares_edge_b_false_of_b_ne : forall a1 a2 b c,
  b <> a1 -> b <> a2 ->
  shares_edge_b a1 a2 b c = false.
Proof.
  intros a1 a2 b c Hb1 Hb2.
  unfold shares_edge_b.
  rewrite (point_eqb_false a1 b (not_eq_sym Hb1)).
  rewrite (point_eqb_false a2 b (not_eq_sym Hb2)).
  rewrite andb_false_l, andb_false_r, orb_false_l. reflexivity.
Qed.

Lemma shares_edge_b_false_of_b_ne_swap : forall a1 a2 b c,
  b <> a1 -> b <> a2 ->
  shares_edge_b a1 a2 c b = false.
Proof.
  intros a1 a2 b c Hb1 Hb2.
  unfold shares_edge_b.
  rewrite (point_eqb_false a2 b (not_eq_sym Hb2)).
  rewrite (point_eqb_false a1 b (not_eq_sym Hb1)).
  rewrite andb_false_r, andb_false_l, orb_false_r. reflexivity.
Qed.

Lemma touch_edge_b_false_of_B_interior :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    (0 < gtri ax ay bx by_ cx cy (mkPoint dx dy) \/
     0 < gtri ax ay bx by_ cx cy (mkPoint ex ey) \/
     0 < gtri ax ay bx by_ cx cy (mkPoint fx fy)) ->
    touch_edge_b (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hvin.
  pose (A1 := mkPoint ax ay).
  pose (A2 := mkPoint bx by_).
  pose (A3 := mkPoint cx cy).
  pose (B1 := mkPoint dx dy).
  pose (B2 := mkPoint ex ey).
  pose (B3 := mkPoint fx fy).
  assert (NA : forall p, 0 < gtri ax ay bx by_ cx cy p ->
                  p <> A1 /\ p <> A2 /\ p <> A3).
  { intros p Hp. unfold A1, A2, A3. repeat split.
    - exact (gtri_pos_ne_vertex_a ax ay bx by_ cx cy p Hp).
    - exact (gtri_pos_ne_vertex_b ax ay bx by_ cx cy p Hp).
    - exact (gtri_pos_ne_vertex_c ax ay bx by_ cx cy p Hp). }
  unfold touch_edge_b, A1, A2, A3, B1, B2, B3.
  destruct Hvin as [H1 | [H2 | H3]].
  - destruct (NA (mkPoint dx dy) H1) as (N1 & N2 & N3).
    unfold A1, A2, A3 in N1, N2, N3.
    rewrite (shares_edge_b_false_of_b_ne (mkPoint ax ay) (mkPoint bx by_)
               (mkPoint dx dy) (mkPoint ex ey) N1 N2).
    rewrite (shares_edge_b_false_of_b_ne_swap (mkPoint ax ay) (mkPoint bx by_)
               (mkPoint dx dy) (mkPoint fx fy) N1 N2).
    rewrite (opposite_sides_b_false_AB ax ay bx by_ cx cy (mkPoint dx dy) H1).
    rewrite (shares_edge_b_false_of_b_ne (mkPoint bx by_) (mkPoint cx cy)
               (mkPoint dx dy) (mkPoint ex ey) N2 N3).
    rewrite (shares_edge_b_false_of_b_ne_swap (mkPoint bx by_) (mkPoint cx cy)
               (mkPoint dx dy) (mkPoint fx fy) N2 N3).
    rewrite (opposite_sides_b_false_BC ax ay bx by_ cx cy (mkPoint dx dy) H1).
    rewrite (shares_edge_b_false_of_b_ne (mkPoint cx cy) (mkPoint ax ay)
               (mkPoint dx dy) (mkPoint ex ey) N3 N1).
    rewrite (shares_edge_b_false_of_b_ne_swap (mkPoint cx cy) (mkPoint ax ay)
               (mkPoint dx dy) (mkPoint fx fy) N3 N1).
    rewrite (opposite_sides_b_false_CA ax ay bx by_ cx cy (mkPoint dx dy) H1).
    btauto.
  - destruct (NA (mkPoint ex ey) H2) as (N1 & N2 & N3).
    unfold A1, A2, A3 in N1, N2, N3.
    rewrite (shares_edge_b_false_of_b_ne_swap (mkPoint ax ay) (mkPoint bx by_)
               (mkPoint ex ey) (mkPoint dx dy) N1 N2).
    rewrite (shares_edge_b_false_of_b_ne (mkPoint ax ay) (mkPoint bx by_)
               (mkPoint ex ey) (mkPoint fx fy) N1 N2).
    rewrite (opposite_sides_b_false_AB ax ay bx by_ cx cy (mkPoint ex ey) H2).
    rewrite (shares_edge_b_false_of_b_ne_swap (mkPoint bx by_) (mkPoint cx cy)
               (mkPoint ex ey) (mkPoint dx dy) N2 N3).
    rewrite (shares_edge_b_false_of_b_ne (mkPoint bx by_) (mkPoint cx cy)
               (mkPoint ex ey) (mkPoint fx fy) N2 N3).
    rewrite (opposite_sides_b_false_BC ax ay bx by_ cx cy (mkPoint ex ey) H2).
    rewrite (shares_edge_b_false_of_b_ne_swap (mkPoint cx cy) (mkPoint ax ay)
               (mkPoint ex ey) (mkPoint dx dy) N3 N1).
    rewrite (shares_edge_b_false_of_b_ne (mkPoint cx cy) (mkPoint ax ay)
               (mkPoint ex ey) (mkPoint fx fy) N3 N1).
    rewrite (opposite_sides_b_false_CA ax ay bx by_ cx cy (mkPoint ex ey) H2).
    btauto.
  - destruct (NA (mkPoint fx fy) H3) as (N1 & N2 & N3).
    unfold A1, A2, A3 in N1, N2, N3.
    rewrite (shares_edge_b_false_of_b_ne (mkPoint ax ay) (mkPoint bx by_)
               (mkPoint fx fy) (mkPoint dx dy) N1 N2).
    rewrite (shares_edge_b_false_of_b_ne_swap (mkPoint ax ay) (mkPoint bx by_)
               (mkPoint fx fy) (mkPoint ex ey) N1 N2).
    rewrite (opposite_sides_b_false_AB ax ay bx by_ cx cy (mkPoint fx fy) H3).
    rewrite (shares_edge_b_false_of_b_ne (mkPoint bx by_) (mkPoint cx cy)
               (mkPoint fx fy) (mkPoint dx dy) N2 N3).
    rewrite (shares_edge_b_false_of_b_ne_swap (mkPoint bx by_) (mkPoint cx cy)
               (mkPoint fx fy) (mkPoint ex ey) N2 N3).
    rewrite (opposite_sides_b_false_BC ax ay bx by_ cx cy (mkPoint fx fy) H3).
    rewrite (shares_edge_b_false_of_b_ne (mkPoint cx cy) (mkPoint ax ay)
               (mkPoint fx fy) (mkPoint dx dy) N3 N1).
    rewrite (shares_edge_b_false_of_b_ne_swap (mkPoint cx cy) (mkPoint ax ay)
               (mkPoint fx fy) (mkPoint ex ey) N3 N1).
    rewrite (opposite_sides_b_false_CA ax ay bx by_ cx cy (mkPoint fx fy) H3).
    btauto.
Qed.

Lemma contains_b_false_of_B_exterior :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    gtri ax ay bx by_ cx cy (mkPoint dx dy) < 0 \/
    gtri ax ay bx by_ cx cy (mkPoint ex ey) < 0 \/
    gtri ax ay bx by_ cx cy (mkPoint fx fy) < 0 ->
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hext.
  unfold contains_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [_ | _]; [ | reflexivity ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint dx dy))) as [Hd | _].
  2: reflexivity.
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint ex ey))) as [He | _].
  2: reflexivity.
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint fx fy))) as [Hf | _].
  2: reflexivity.
  destruct Hext as [H | [H | H]]; lra.
Qed.

Lemma gtri_strict_pos_b_true : forall ax ay bx by_ cx cy p,
  gtri_strict_pos_b ax ay bx by_ cx cy p = true ->
  0 < gtri ax ay bx by_ cx cy p.
Proof.
  intros ax ay bx by_ cx cy p H.
  unfold gtri_strict_pos_b in H.
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy p)) as [Hlt | _];
    [ exact Hlt | discriminate ].
Qed.

Lemma gtri_strict_neg_b_true : forall ax ay bx by_ cx cy p,
  gtri_strict_neg_b ax ay bx by_ cx cy p = true ->
  gtri ax ay bx by_ cx cy p < 0.
Proof.
  intros ax ay bx by_ cx cy p H.
  unfold gtri_strict_neg_b in H.
  destruct (Rlt_dec (gtri ax ay bx by_ cx cy p) 0) as [Hlt | _];
    [ exact Hlt | discriminate ].
Qed.

Lemma some_vertex_strict_pos_elim : forall ax ay bx by_ cx cy p q r,
  some_vertex_strict_pos ax ay bx by_ cx cy p q r = true ->
  0 < gtri ax ay bx by_ cx cy p \/
  0 < gtri ax ay bx by_ cx cy q \/
  0 < gtri ax ay bx by_ cx cy r.
Proof.
  intros ax ay bx by_ cx cy p q r H.
  unfold some_vertex_strict_pos in H.
  apply orb_true_iff in H as [H | H].
  - apply orb_true_iff in H as [H | H].
    + left. exact (gtri_strict_pos_b_true _ _ _ _ _ _ _ H).
    + right. left. exact (gtri_strict_pos_b_true _ _ _ _ _ _ _ H).
  - right. right. exact (gtri_strict_pos_b_true _ _ _ _ _ _ _ H).
Qed.

Lemma some_vertex_strict_neg_elim : forall ax ay bx by_ cx cy p q r,
  some_vertex_strict_neg ax ay bx by_ cx cy p q r = true ->
  gtri ax ay bx by_ cx cy p < 0 \/
  gtri ax ay bx by_ cx cy q < 0 \/
  gtri ax ay bx by_ cx cy r < 0.
Proof.
  intros ax ay bx by_ cx cy p q r H.
  unfold some_vertex_strict_neg in H.
  apply orb_true_iff in H as [H | H].
  - apply orb_true_iff in H as [H | H].
    + left. exact (gtri_strict_neg_b_true _ _ _ _ _ _ _ H).
    + right. left. exact (gtri_strict_neg_b_true _ _ _ _ _ _ _ H).
  - right. right. exact (gtri_strict_neg_b_true _ _ _ _ _ _ _ H).
Qed.

Lemma overlap_b_unpack :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    0 < gdbl ax ay bx by_ cx cy /\
    0 < gdbl dx dy ex ey fx fy /\
    (0 < gtri ax ay bx by_ cx cy (mkPoint dx dy) \/
     0 < gtri ax ay bx by_ cx cy (mkPoint ex ey) \/
     0 < gtri ax ay bx by_ cx cy (mkPoint fx fy)) /\
    (gtri ax ay bx by_ cx cy (mkPoint dx dy) < 0 \/
     gtri ax ay bx by_ cx cy (mkPoint ex ey) < 0 \/
     gtri ax ay bx by_ cx cy (mkPoint fx fy) < 0) /\
    (gtri dx dy ex ey fx fy (mkPoint ax ay) < 0 \/
     gtri dx dy ex ey fx fy (mkPoint bx by_) < 0 \/
     gtri dx dy ex ey fx fy (mkPoint cx cy) < 0).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold overlap_b in H.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [ | discriminate ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [ | discriminate ].
  apply andb_true_iff in H as [H HoutA].
  apply andb_true_iff in H as [HinB HoutB].
  repeat split.
  - exact HA.
  - exact HB.
  - exact (some_vertex_strict_pos_elim _ _ _ _ _ _ _ _ _ HinB).
  - exact (some_vertex_strict_neg_elim _ _ _ _ _ _ _ _ _ HoutB).
  - exact (some_vertex_strict_neg_elim _ _ _ _ _ _ _ _ _ HoutA).
Qed.

(* The headline regime theorem: overlap_b forces TPR_Overlap, with
   touch_edge_b and contains_b derived false. *)
Theorem triangle_pair_regime_overlap :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy = TPR_Overlap.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hov.
  pose proof (overlap_b_unpack _ _ _ _ _ _ _ _ _ _ _ _ Hov)
    as (_ & _ & Hin & HoutB & _).
  unfold triangle_pair_regime.
  rewrite (touch_edge_b_false_of_B_interior ax ay bx by_ cx cy
             dx dy ex ey fx fy Hin).
  rewrite (contains_b_false_of_B_exterior ax ay bx by_ cx cy
             dx dy ex ey fx fy HoutB).
  rewrite Hov. reflexivity.
Qed.

(* WITNESS topic: relate · claimId: 522-b · witness: 522-b-overlap-bar1 *)
Theorem overlap_b_partial_overlap :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangles_partial_overlap
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hov.
  pose proof (overlap_b_unpack _ _ _ _ _ _ _ _ _ _ _ _ Hov)
    as (HccwA & HccwB & Hin & HoutB & HoutA).
  unfold triangles_partial_overlap.
  split; [ | split ].
  - destruct Hin as [H | [H | H]].
    + exact (ii_witness_of_B_vertex_a ax ay bx by_ cx cy
               dx dy ex ey fx fy HccwB H).
    + exact (ii_witness_of_B_vertex_b ax ay bx by_ cx cy
               dx dy ex ey fx fy HccwB H).
    + exact (ii_witness_of_B_vertex_c ax ay bx by_ cx cy
               dx dy ex ey fx fy HccwB H).
  - destruct HoutA as [H | [H | H]].
    + exact (aext_B_of_A_vertex ax ay bx by_ cx cy dx dy ex ey fx fy
               (mkPoint ax ay) HccwA (or_introl eq_refl) H).
    + exact (aext_B_of_A_vertex ax ay bx by_ cx cy dx dy ex ey fx fy
               (mkPoint bx by_) HccwA (or_intror (or_introl eq_refl)) H).
    + exact (aext_B_of_A_vertex ax ay bx by_ cx cy dx dy ex ey fx fy
               (mkPoint cx cy) HccwA (or_intror (or_intror eq_refl)) H).
  - destruct HoutB as [H | [H | H]].
    + exact (bext_A_of_B_vertex ax ay bx by_ cx cy dx dy ex ey fx fy
               (mkPoint dx dy) HccwB (or_introl eq_refl) H).
    + exact (bext_A_of_B_vertex ax ay bx by_ cx cy dx dy ex ey fx fy
               (mkPoint ex ey) HccwB (or_intror (or_introl eq_refl)) H).
    + exact (bext_A_of_B_vertex ax ay bx by_ cx cy dx dy ex ey fx fy
               (mkPoint fx fy) HccwB (or_intror (or_intror eq_refl)) H).
Qed.

Theorem triangle_pair_regime_overlap_sound :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy = TPR_Overlap ->
    triangles_partial_overlap
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hreg.
  unfold triangle_pair_regime in Hreg.
  destruct (touch_edge_b _ _ _ _ _ _) ; [ discriminate | ].
  destruct (contains_b ax ay bx by_ cx cy dx dy ex ey fx fy);
    [ discriminate | ].
  destruct (overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy) eqn:Hov.
  - exact (overlap_b_partial_overlap _ _ _ _ _ _ _ _ _ _ _ _ Hov).
  - destruct (separated_b ax ay bx by_ cx cy dx dy ex ey fx fy);
      [ discriminate | ].
    destruct (touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy);
      [ discriminate | ].
    destruct (touch_partial_edge_b _ _ _ _ _ _);
      [ discriminate | ].
    destruct (touch_onesided_t_b _ _ _ _ _ _);
      [ discriminate | ].
    destruct (touch_obtuse_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy);
      [ discriminate | ].
    destruct (mixed_cone_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy);
      [ discriminate | ].
    destruct (same_cone_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy);
      discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Concrete lens-stab pair: the #567 overlap witness now classifies.          *)
(* A = (0,0)(1,0)(0,1), B = (1/4,1/4)(5/4,1/4)(1/4,5/4).                      *)
(* B's first vertex is strictly interior to A; the other two sit outside A;   *)
(* A's origin sits outside B.  Common interior point (3/8, 3/8).              *)
(* -------------------------------------------------------------------------- *)

Lemma overlap_ex_gtri_A_B0 :
  0 < gtri 0 0 1 0 0 1 (mkPoint (1/4) (1/4)).
Proof.
  unfold gtri, gsA, gsB, gsC; cbn [px py].
  apply Rmin_pos_iff. split; [ apply Rmin_pos_iff; split | ]; lra.
Qed.

Lemma overlap_ex_gtri_A_B1 :
  gtri 0 0 1 0 0 1 (mkPoint (5/4) (1/4)) < 0.
Proof.
  eapply Rle_lt_trans; [ apply (gtri_le_gsB 0 0 1 0 0 1 (mkPoint (5/4) (1/4))) | ].
  unfold gsB; cbn [px py]; lra.
Qed.

Lemma overlap_ex_gtri_B_A0 :
  gtri (1/4) (1/4) (5/4) (1/4) (1/4) (5/4) (mkPoint 0 0) < 0.
Proof.
  eapply Rle_lt_trans;
    [ apply (gtri_le_gsA (1/4) (1/4) (5/4) (1/4) (1/4) (5/4) (mkPoint 0 0)) | ].
  unfold gsA; cbn [px py]; lra.
Qed.

Lemma overlap_ex_overlap_b :
  overlap_b 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4) = true.
Proof.
  unfold overlap_b, some_vertex_strict_pos, some_vertex_strict_neg,
         gtri_strict_pos_b, gtri_strict_neg_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl (1/4) (1/4) (5/4) (1/4) (1/4) (5/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint (1/4) (1/4)))) as [_ | Hn];
    [ | exfalso; apply Hn; exact overlap_ex_gtri_A_B0 ].
  destruct (Rlt_dec (gtri 0 0 1 0 0 1 (mkPoint (1/4) (1/4))) 0) as [Hbad | _];
    [ exfalso; pose proof overlap_ex_gtri_A_B0; lra | ].
  destruct (Rlt_dec (gtri 0 0 1 0 0 1 (mkPoint (5/4) (1/4))) 0) as [_ | Hn];
    [ | exfalso; apply Hn; exact overlap_ex_gtri_A_B1 ].
  destruct (Rlt_dec (gtri (1/4) (1/4) (5/4) (1/4) (1/4) (5/4) (mkPoint 0 0)) 0)
    as [_ | Hn];
    [ | exfalso; apply Hn; exact overlap_ex_gtri_B_A0 ].
  reflexivity.
Qed.

Example overlap_ex_common_interior :
  in_tri_interior (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                  (mkPoint (3/8) (3/8)) /\
  in_tri_interior (mkPoint (1/4) (1/4)) (mkPoint (5/4) (1/4))
                  (mkPoint (1/4) (5/4)) (mkPoint (3/8) (3/8)).
Proof.
  split; unfold in_tri_interior, gtri, gsA, gsB, gsC; cbn [px py].
  - apply Rmin_pos_iff. split; [ apply Rmin_pos_iff; split | ]; lra.
  - apply Rmin_pos_iff. split; [ apply Rmin_pos_iff; split | ]; lra.
Qed.

Example relate_triangle_overlap_ex :
  relate (triangle_geometry 0 0 1 0 0 1)
         (triangle_geometry (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)) =
  tris_relate 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4) TPR_Overlap.
Proof.
  rewrite relate_on_triangles_dispatches.
  rewrite (triangle_pair_regime_overlap 0 0 1 0 0 1
             (1/4) (1/4) (5/4) (1/4) (1/4) (5/4) overlap_ex_overlap_b).
  reflexivity.
Qed.

(* Mutation replay (in-tree, #570; not an ADR-0004 mint).  Flip exactly
   one comparison below, rebuild this file, then restore the sign.
     1. `gtri_strict_pos_b`: `0 < gtri` → `0 <= gtri`
        pin: `overlap_b_partial_overlap` (II nudge needs a strict
        interior B-vertex; a boundary vertex has gtri_B = 0 and the
        concave lower bound collapses to 0).
     2. `gtri_strict_neg_b`: `gtri < 0` → `gtri <= 0`
        pin: `overlap_b_partial_overlap` (stay-negative interpolation
        starts from a strictly negative slack).
     3. `overlap_nudge_t` denominator: drop the `1 +` and the theorem
        `overlap_nudge_t_keeps_pos` fails when gc = -g0. *)

Print Assumptions triangle_pair_regime_overlap.
Print Assumptions overlap_b_partial_overlap.
Print Assumptions triangle_pair_regime_overlap_sound.
Print Assumptions relate_triangle_overlap_ex.
