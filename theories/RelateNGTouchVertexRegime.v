(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchVertexRegime
   ----------------------------------------------------------------------------
   Slice of #572 / 522-i. Earlier-branch exclusions, the TPR_TouchVertex
   headlines, and the ticket / former-decline pins.  The original name
   RelateNGTouchVertex.v is the Require Export umbrella.

   Separating-line machinery is shared with disjoint as a *pattern*
   (affine side, barycentric lift, strict-at-vertices ⇒
   strict-on-closure), not as helpers: disjoint's line is an existing
   edge (`cross` / `opposite_sides_b`); this line is a constructed
   normal through `v` (`side_dot` / `vec_sum_from`).

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
  RelateNGDisjoint RelateNGTouchVertexCone.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Earlier branches derived false.                                            *)
(* -------------------------------------------------------------------------- *)

Lemma exactly_one_shared_elim : forall a1 a2 a3 b1 b2 b3,
  exactly_one_shared_from_a a1 a2 a3 b1 b2 b3 = true ->
  (is_vertex_b a1 b1 b2 b3 = true /\
   is_vertex_b a2 b1 b2 b3 = false /\
   is_vertex_b a3 b1 b2 b3 = false) \/
  (is_vertex_b a1 b1 b2 b3 = false /\
   is_vertex_b a2 b1 b2 b3 = true /\
   is_vertex_b a3 b1 b2 b3 = false) \/
  (is_vertex_b a1 b1 b2 b3 = false /\
   is_vertex_b a2 b1 b2 b3 = false /\
   is_vertex_b a3 b1 b2 b3 = true).
Proof.
  intros a1 a2 a3 b1 b2 b3 H.
  unfold exactly_one_shared_from_a in H.
  apply orb_true_iff in H as [H | H3];
    [ apply orb_true_iff in H as [H1 | H2] | ].
  - apply andb_true_iff in H1 as [Hab Hn3].
    apply andb_true_iff in Hab as [Hs1 Hn2].
    apply negb_true_iff in Hn2. apply negb_true_iff in Hn3.
    left. repeat split; assumption.
  - apply andb_true_iff in H2 as [Hab Hn3].
    apply andb_true_iff in Hab as [Hn1 Hs2].
    apply negb_true_iff in Hn1. apply negb_true_iff in Hn3.
    right. left. repeat split; assumption.
  - apply andb_true_iff in H3 as [Hab Hs3].
    apply andb_true_iff in Hab as [Hn1 Hn2].
    apply negb_true_iff in Hn1. apply negb_true_iff in Hn2.
    right. right. repeat split; assumption.
Qed.

Lemma is_vertex_b_false : forall v p q r,
  is_vertex_b v p q r = false -> ~ is_vertex_of v p q r.
Proof.
  intros v p q r H Hv.
  unfold is_vertex_b in H.
  destruct Hv as [E | [E | E]]; subst v.
  - destruct (orb_false_elim _ _ H) as [H1 _].
    destruct (orb_false_elim _ _ H1) as [H1' _].
    rewrite point_eqb_complete in H1'; [ discriminate | reflexivity ].
  - destruct (orb_false_elim _ _ H) as [H1 _].
    destruct (orb_false_elim _ _ H1) as [_ H2].
    rewrite point_eqb_complete in H2; [ discriminate | reflexivity ].
  - destruct (orb_false_elim _ _ H) as [_ H3].
    rewrite point_eqb_complete in H3; [ discriminate | reflexivity ].
Qed.

Lemma shares_edge_b_false :
  forall p1 p2 q1 q2,
    ~ is_vertex_of p1 q1 q2 p2 \/ ~ is_vertex_of p2 q1 q2 p1 ->
    shares_edge_b p1 p2 q1 q2 = false.
Proof.
  intros p1 p2 q1 q2 H.
  unfold shares_edge_b.
  assert (kill : is_vertex_of p1 q1 q2 p2 -> is_vertex_of p2 q1 q2 p1 -> False).
  { intros Hp Hq. destruct H as [Hn | Hn]; apply Hn; assumption. }
  destruct (andb (point_eqb p1 q1) (point_eqb p2 q2)) eqn:Efwd;
    destruct (andb (point_eqb p1 q2) (point_eqb p2 q1)) eqn:Erev;
    try reflexivity.
  - apply andb_true_iff in Efwd as [H1 H2].
    apply point_eqb_sound in H1. apply point_eqb_sound in H2.
    subst. exfalso. apply kill; [ left; reflexivity | right; left; reflexivity ].
  - apply andb_true_iff in Efwd as [H1 H2].
    apply point_eqb_sound in H1. apply point_eqb_sound in H2.
    subst. exfalso. apply kill; [ left; reflexivity | right; left; reflexivity ].
  - apply andb_true_iff in Erev as [H1 H2].
    apply point_eqb_sound in H1. apply point_eqb_sound in H2.
    subst. exfalso. apply kill; [ right; left; reflexivity | left; reflexivity ].
Qed.

Lemma not_two_A_on_B :
  forall a1 a2 a3 b1 b2 b3 p q,
    exactly_one_shared_from_a a1 a2 a3 b1 b2 b3 = true ->
    (p = a1 \/ p = a2 \/ p = a3) ->
    (q = a1 \/ q = a2 \/ q = a3) ->
    p <> q ->
    ~ is_vertex_of p b1 b2 b3 \/ ~ is_vertex_of q b1 b2 b3.
Proof.
  intros a1 a2 a3 b1 b2 b3 p q Hex Hp Hq Hne.
  apply exactly_one_shared_elim in Hex.
  destruct Hex as [Hex | [Hex | Hex]];
    destruct Hex as (S1 & S2 & S3);
    destruct Hp as [Ep | [Ep | Ep]]; subst p;
    destruct Hq as [Eq | [Eq | Eq]]; subst q;
    try (exfalso; apply Hne; reflexivity);
    try (right; apply is_vertex_b_false; assumption);
    try (left; apply is_vertex_b_false; assumption).
Qed.

Lemma shares_edge_b_false_on_A_edge :
  forall a1 a2 a3 b1 b2 b3 p1 p2 q1 q2,
    exactly_one_shared_from_a a1 a2 a3 b1 b2 b3 = true ->
    (p1 = a1 \/ p1 = a2 \/ p1 = a3) ->
    (p2 = a1 \/ p2 = a2 \/ p2 = a3) ->
    p1 <> p2 ->
    (q1 = b1 \/ q1 = b2 \/ q1 = b3) ->
    (q2 = b1 \/ q2 = b2 \/ q2 = b3) ->
    shares_edge_b p1 p2 q1 q2 = false.
Proof.
  intros a1 a2 a3 b1 b2 b3 p1 p2 q1 q2 Hex Hp1 Hp2 Hne Hq1 Hq2.
  pose proof (not_two_A_on_B a1 a2 a3 b1 b2 b3 p1 p2 Hex Hp1 Hp2 Hne) as Hnb.
  unfold shares_edge_b.
  destruct (andb (point_eqb p1 q1) (point_eqb p2 q2)) eqn:Efwd;
    destruct (andb (point_eqb p1 q2) (point_eqb p2 q1)) eqn:Erev;
    try reflexivity.
  - apply andb_true_iff in Efwd as [H1 H2].
    apply point_eqb_sound in H1. apply point_eqb_sound in H2. subst.
    destruct Hnb as [Hn | Hn]; exfalso; apply Hn;
      [ destruct Hq1 as [E | [E | E]]; subst;
        [ left | right; left | right; right ]; reflexivity
      | destruct Hq2 as [E | [E | E]]; subst;
        [ left | right; left | right; right ]; reflexivity ].
  - apply andb_true_iff in Efwd as [H1 H2].
    apply point_eqb_sound in H1. apply point_eqb_sound in H2. subst.
    destruct Hnb as [Hn | Hn]; exfalso; apply Hn;
      [ destruct Hq1 as [E | [E | E]]; subst;
        [ left | right; left | right; right ]; reflexivity
      | destruct Hq2 as [E | [E | E]]; subst;
        [ left | right; left | right; right ]; reflexivity ].
  - apply andb_true_iff in Erev as [H1 H2].
    apply point_eqb_sound in H1. apply point_eqb_sound in H2. subst.
    destruct Hnb as [Hn | Hn]; exfalso; apply Hn;
      [ destruct Hq2 as [E | [E | E]]; subst;
        [ left | right; left | right; right ]; reflexivity
      | destruct Hq1 as [E | [E | E]]; subst;
        [ left | right; left | right; right ]; reflexivity ].
Qed.

Lemma touch_edge_b_false_of_exactly_one :
  forall a1 a2 a3 b1 b2 b3,
    exactly_one_shared_from_a a1 a2 a3 b1 b2 b3 = true ->
    a1 <> a2 -> a2 <> a3 -> a3 <> a1 ->
    touch_edge_b a1 a2 a3 b1 b2 b3 = false.
Proof.
  intros a1 a2 a3 b1 b2 b3 Hex H12 H23 H31.
  unfold touch_edge_b.
  rewrite (shares_edge_b_false_on_A_edge a1 a2 a3 b1 b2 b3 a1 a2 b1 b2
             Hex (or_introl eq_refl) (or_intror (or_introl eq_refl)) H12
             (or_introl eq_refl) (or_intror (or_introl eq_refl))).
  rewrite (shares_edge_b_false_on_A_edge a1 a2 a3 b1 b2 b3 a1 a2 b2 b3
             Hex (or_introl eq_refl) (or_intror (or_introl eq_refl)) H12
             (or_intror (or_introl eq_refl)) (or_intror (or_intror eq_refl))).
  rewrite (shares_edge_b_false_on_A_edge a1 a2 a3 b1 b2 b3 a1 a2 b3 b1
             Hex (or_introl eq_refl) (or_intror (or_introl eq_refl)) H12
             (or_intror (or_intror eq_refl)) (or_introl eq_refl)).
  rewrite (shares_edge_b_false_on_A_edge a1 a2 a3 b1 b2 b3 a2 a3 b1 b2
             Hex (or_intror (or_introl eq_refl)) (or_intror (or_intror eq_refl)) H23
             (or_introl eq_refl) (or_intror (or_introl eq_refl))).
  rewrite (shares_edge_b_false_on_A_edge a1 a2 a3 b1 b2 b3 a2 a3 b2 b3
             Hex (or_intror (or_introl eq_refl)) (or_intror (or_intror eq_refl)) H23
             (or_intror (or_introl eq_refl)) (or_intror (or_intror eq_refl))).
  rewrite (shares_edge_b_false_on_A_edge a1 a2 a3 b1 b2 b3 a2 a3 b3 b1
             Hex (or_intror (or_introl eq_refl)) (or_intror (or_intror eq_refl)) H23
             (or_intror (or_intror eq_refl)) (or_introl eq_refl)).
  rewrite (shares_edge_b_false_on_A_edge a1 a2 a3 b1 b2 b3 a3 a1 b1 b2
             Hex (or_intror (or_intror eq_refl)) (or_introl eq_refl) H31
             (or_introl eq_refl) (or_intror (or_introl eq_refl))).
  rewrite (shares_edge_b_false_on_A_edge a1 a2 a3 b1 b2 b3 a3 a1 b2 b3
             Hex (or_intror (or_intror eq_refl)) (or_introl eq_refl) H31
             (or_intror (or_introl eq_refl)) (or_intror (or_intror eq_refl))).
  rewrite (shares_edge_b_false_on_A_edge a1 a2 a3 b1 b2 b3 a3 a1 b3 b1
             Hex (or_intror (or_intror eq_refl)) (or_introl eq_refl) H31
             (or_intror (or_intror eq_refl)) (or_introl eq_refl)).
  reflexivity.
Qed.

Lemma ccw_vertices_distinct : forall a1 a2 a3,
  0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
  a1 <> a2 /\ a2 <> a3 /\ a3 <> a1.
Proof.
  intros a1 a2 a3 H.
  repeat split; intros E; subst;
    unfold gdbl in H; cbn [px py] in H; lra.
Qed.

Lemma opposite_sides_b_same_point : forall p1 p2 q,
  opposite_sides_b p1 p2 q q = false.
Proof.
  intros p1 p2 q. unfold opposite_sides_b.
  destruct (Rlt_dec (cross p1 p2 q * cross p1 p2 q) 0) as [Hlt | _];
    [ exfalso; nra | reflexivity ].
Qed.

Lemma opposite_sides_b_endpoint : forall p1 p2 apex,
  opposite_sides_b p1 p2 apex p1 = false /\
  opposite_sides_b p1 p2 apex p2 = false.
Proof.
  intros p1 p2 apex. unfold opposite_sides_b.
  split;
    destruct (Rlt_dec (cross p1 p2 apex * cross p1 p2 _) 0) as [Hlt | _];
    try reflexivity;
    exfalso; unfold cross in Hlt; destruct p1, p2, apex; simpl in Hlt; nra.
Qed.

Lemma opposite_sides_b_false_on_line_pt : forall p1 p2 apex v,
  v = p1 \/ v = p2 \/ v = apex ->
  opposite_sides_b p1 p2 apex v = false.
Proof.
  intros p1 p2 apex v [E | [E | E]]; subst v.
  - apply (opposite_sides_b_endpoint p1 p2 apex).
  - apply (opposite_sides_b_endpoint p1 p2 apex).
  - apply opposite_sides_b_same_point.
Qed.

Lemma edge_separates_b_false_shared_q :
  forall p1 p2 apex q1 q2 q3 v,
    (v = q1 \/ v = q2 \/ v = q3) ->
    (v = p1 \/ v = p2 \/ v = apex) ->
    edge_separates_b p1 p2 apex q1 q2 q3 = false.
Proof.
  intros p1 p2 apex q1 q2 q3 v Hq Hp.
  unfold edge_separates_b.
  assert (Hv : opposite_sides_b p1 p2 apex v = false)
    by (apply opposite_sides_b_false_on_line_pt; exact Hp).
  destruct Hq as [E | [E | E]]; subst v; rewrite Hv.
  - reflexivity.
  - destruct (opposite_sides_b p1 p2 apex q1); reflexivity.
  - destruct (opposite_sides_b p1 p2 apex q1);
    destruct (opposite_sides_b p1 p2 apex q2); reflexivity.
Qed.

Lemma is_vertex_of_rotate : forall v a1 a2 a3,
  is_vertex_of v a1 a2 a3 -> is_vertex_of v a2 a3 a1.
Proof.
  intros v a1 a2 a3 [E | [E | E]]; subst v;
    [ right; right | left | right; left ]; reflexivity.
Qed.

Lemma some_edge_separates_b_false_of_shared :
  forall a1 a2 a3 b1 b2 b3 v,
    is_vertex_of v a1 a2 a3 ->
    is_vertex_of v b1 b2 b3 ->
    some_edge_separates_b a1 a2 a3 b1 b2 b3 = false.
Proof.
  intros a1 a2 a3 b1 b2 b3 v HvA HvB.
  unfold some_edge_separates_b.
  pose proof (is_vertex_of_rotate v a1 a2 a3 HvA) as HvA2.
  pose proof (is_vertex_of_rotate v a2 a3 a1 HvA2) as HvA3.
  pose proof (is_vertex_of_rotate v b1 b2 b3 HvB) as HvB2.
  pose proof (is_vertex_of_rotate v b2 b3 b1 HvB2) as HvB3.
  rewrite (edge_separates_b_false_shared_q a1 a2 a3 b1 b2 b3 v HvB HvA).
  rewrite (edge_separates_b_false_shared_q a2 a3 a1 b1 b2 b3 v HvB HvA2).
  rewrite (edge_separates_b_false_shared_q a3 a1 a2 b1 b2 b3 v HvB HvA3).
  rewrite (edge_separates_b_false_shared_q b1 b2 b3 a1 a2 a3 v HvA HvB).
  rewrite (edge_separates_b_false_shared_q b2 b3 b1 a1 a2 a3 v HvA HvB2).
  rewrite (edge_separates_b_false_shared_q b3 b1 b2 a1 a2 a3 v HvA HvB3).
  reflexivity.
Qed.

Lemma separated_b_false_of_touch_vertex :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htv.
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [_ | _]; [ | reflexivity ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [_ | _]; [ | reflexivity ].
  pose proof (touch_vertex_b_unpack _ _ _ _ _ _ _ _ _ _ _ _ Htv)
    as (_ & _ & _ & Hfrom).
  destruct Hfrom as [Hv | [Hv | Hv]];
    apply touch_vertex_from_v_elim in Hv;
    destruct Hv as (HvA & HvB & _);
    apply (some_edge_separates_b_false_of_shared
             (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
             (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) _ HvA HvB).
Qed.

Lemma gtri_le0_of_A_vertex :
  forall ax ay bx by_ cx cy p,
    is_vertex_of p (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) ->
    gtri ax ay bx by_ cx cy p <= 0.
Proof.
  intros ax ay bx by_ cx cy p [E | [E | E]]; subst p;
    [ exact (gtri_at_own_vertex_a_le0 ax ay bx by_ cx cy)
    | exact (gtri_at_own_vertex_b_le0 ax ay bx by_ cx cy)
    | exact (gtri_at_own_vertex_c_le0 ax ay bx by_ cx cy) ].
Qed.

Lemma contains_b_false_of_B_on_A :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    is_vertex_of (mkPoint dx dy) (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) \/
    is_vertex_of (mkPoint ex ey) (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) \/
    is_vertex_of (mkPoint fx fy) (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) ->
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hv.
  unfold contains_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [_ | _]; [ | reflexivity ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint dx dy))) as [Ha | _];
    [ | reflexivity ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint ex ey))) as [Hb | _];
    [ | reflexivity ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint fx fy))) as [Hc | _];
    [ | reflexivity ].
  destruct Hv as [Hv | [Hv | Hv]];
    pose proof (gtri_le0_of_A_vertex ax ay bx by_ cx cy _ Hv); lra.
Qed.

Lemma touch_vertex_some_B_on_A :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    is_vertex_of (mkPoint dx dy) (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) \/
    is_vertex_of (mkPoint ex ey) (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) \/
    is_vertex_of (mkPoint fx fy) (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htv.
  pose proof (touch_vertex_b_unpack _ _ _ _ _ _ _ _ _ _ _ _ Htv)
    as (_ & _ & _ & Hfrom).
  destruct Hfrom as [Hv | [Hv | Hv]];
    apply touch_vertex_from_v_elim in Hv;
    destruct Hv as (HvA & HvB & _).
  - destruct HvB as [E | [E | E]];
      [ left | right; left | right; right ]; rewrite <- E; exact HvA.
  - destruct HvB as [E | [E | E]];
      [ left | right; left | right; right ]; rewrite <- E; exact HvA.
  - destruct HvB as [E | [E | E]];
      [ left | right; left | right; right ]; rewrite <- E; exact HvA.
Qed.

Lemma contains_b_false_of_touch_vertex :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htv.
  apply contains_b_false_of_B_on_A.
  exact (touch_vertex_some_B_on_A _ _ _ _ _ _ _ _ _ _ _ _ Htv).
Qed.

Lemma others_when_vertex : forall v p q r,
  is_vertex_of v p q r ->
  (others_fst v p q r = q /\ others_snd v p q r = r /\ v = p) \/
  (others_fst v p q r = p /\ others_snd v p q r = r /\ v = q) \/
  (others_fst v p q r = p /\ others_snd v p q r = q /\ v = r).
Proof.
  intros v p q r Hv.
  pose proof (others_cover v p q r) as Hc.
  destruct Hc as [Hc | [Hc | Hc]].
  - left. exact Hc.
  - right. left. exact Hc.
  - right. right.
    destruct Hc as (E1 & E2 & Np & Nq).
    split; [ exact E1 | split; [ exact E2 | ] ].
    destruct Hv as [Ev | [Ev | Ev]]; subst v.
    + rewrite point_eqb_complete in Np; [ discriminate | reflexivity ].
    + rewrite point_eqb_complete in Nq; [ discriminate | reflexivity ].
    + reflexivity.
Qed.

Lemma vertex_is_v_or_others : forall v p q r s,
  is_vertex_of v p q r ->
  is_vertex_of s p q r ->
  s = v \/ s = others_fst v p q r \/ s = others_snd v p q r.
Proof.
  intros v p q r s Hv Hs.
  pose proof (others_when_vertex v p q r Hv) as Ho.
  destruct Ho as [Ho | [Ho | Ho]];
    destruct Ho as (E1 & E2 & Ev);
    destruct Hs as [Es | [Es | Es]]; subst; auto.
Qed.

Lemma not_closure_if_side_neg_owner_pos :
  forall v n a1 a2 a3 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    0 <= side_dot v n a1 ->
    0 <= side_dot v n a2 ->
    0 <= side_dot v n a3 ->
    side_dot v n pt < 0 ->
    ~ in_tri_closure a1 a2 a3 pt.
Proof.
  intros v n a1 a2 a3 pt Hd Hs1 Hs2 Hs3 Hn Hcl.
  assert (Hpos : 0 <= side_dot v n pt)
    by (apply (side_combo_pos v n a1 a2 a3 pt
                 (side_dot v n a1) (side_dot v n a2) (side_dot v n a3)
                 Hd Hcl eq_refl eq_refl eq_refl Hs1 Hs2 Hs3)).
  lra.
Qed.

Lemma not_closure_if_side_pos_owner_neg :
  forall v n a1 a2 a3 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    side_dot v n a1 <= 0 ->
    side_dot v n a2 <= 0 ->
    side_dot v n a3 <= 0 ->
    0 < side_dot v n pt ->
    ~ in_tri_closure a1 a2 a3 pt.
Proof.
  intros v n a1 a2 a3 pt Hd Hs1 Hs2 Hs3 Hp Hcl.
  assert (Hneg : side_dot v n pt <= 0)
    by (apply (side_combo_neg v n a1 a2 a3 pt
                 (side_dot v n a1) (side_dot v n a2) (side_dot v n a3)
                 Hd Hcl eq_refl eq_refl eq_refl Hs1 Hs2 Hs3)).
  lra.
Qed.

Lemma remaining_B_not_in_A_of_cone :
  forall v a1 a2 a3 b1 b2 b3,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    is_vertex_of v a1 a2 a3 ->
    is_vertex_of v b1 b2 b3 ->
    cone_separates_b v
      (others_fst v a1 a2 a3) (others_snd v a1 a2 a3)
      (others_fst v b1 b2 b3) (others_snd v b1 b2 b3) = true ->
    ~ in_tri_closure a1 a2 a3 (others_fst v b1 b2 b3) /\
    ~ in_tri_closure a1 a2 a3 (others_snd v b1 b2 b3).
Proof.
  intros v a1 a2 a3 b1 b2 b3 HdA HvA HvB Hc.
  apply cone_separates_b_elim in Hc.
  set (ra1 := others_fst v a1 a2 a3).
  set (ra2 := others_snd v a1 a2 a3).
  set (rb1 := others_fst v b1 b2 b3).
  set (rb2 := others_snd v b1 b2 b3).
  destruct Hc as [HA_side | HB_side].
  - destruct HA_side as (P1 & P2 & N1 & N2).
    pose proof (assign_sides_owner v (vec_sum_from v ra1 ra2)
                  a1 a2 a3 ra1 ra2 HvA eq_refl eq_refl P1 P2)
      as (Os1 & Os2 & Os3).
    split;
      (apply (not_closure_if_side_neg_owner_pos v (vec_sum_from v ra1 ra2)
                a1 a2 a3 _ HdA Os1 Os2 Os3); assumption).
  - destruct HB_side as (P1 & P2 & N1 & N2).
    pose proof (assign_sides_other v (vec_sum_from v rb1 rb2)
                  a1 a2 a3 ra1 ra2 HvA eq_refl eq_refl N1 N2)
      as (Ns1 & Ns2 & Ns3).
    split;
      (apply (not_closure_if_side_pos_owner_neg v (vec_sum_from v rb1 rb2)
                a1 a2 a3 _ HdA Ns1 Ns2 Ns3); assumption).
Qed.

Lemma gtri_strict_pos_b_false_of_nlt :
  forall ax ay bx by_ cx cy p,
    ~ (0 < gtri ax ay bx by_ cx cy p) ->
    gtri_strict_pos_b ax ay bx by_ cx cy p = false.
Proof.
  intros ax ay bx by_ cx cy p Hn. unfold gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy p)) as [Hlt | _];
    [ contradiction | reflexivity ].
Qed.

Lemma gtri_strict_pos_b_false_of_not_closure :
  forall ax ay bx by_ cx cy p,
    ~ in_tri_closure (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) p ->
    gtri_strict_pos_b ax ay bx by_ cx cy p = false.
Proof.
  intros ax ay bx by_ cx cy p Hn.
  apply gtri_strict_pos_b_false_of_nlt.
  intros Hpos. apply Hn. unfold in_tri_closure. cbn [px py]. lra.
Qed.

Lemma gtri_strict_pos_b_false_of_A_vertex :
  forall ax ay bx by_ cx cy p,
    is_vertex_of p (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) ->
    gtri_strict_pos_b ax ay bx by_ cx cy p = false.
Proof.
  intros ax ay bx by_ cx cy p Hv.
  apply gtri_strict_pos_b_false_of_nlt.
  intros Hpos.
  pose proof (gtri_le0_of_A_vertex ax ay bx by_ cx cy p Hv). lra.
Qed.

Lemma gtri_strict_pos_b_false_of_B_under_cone :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy v q,
    0 < gdbl ax ay bx by_ cx cy ->
    is_vertex_of v (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) ->
    is_vertex_of v (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    cone_separates_b v
      (others_fst v (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy))
      (others_snd v (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy))
      (others_fst v (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy))
      (others_snd v (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)) = true ->
    is_vertex_of q (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    gtri_strict_pos_b ax ay bx by_ cx cy q = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy v q HdA HvA HvB Hc Hq.
  pose (A1 := mkPoint ax ay).
  pose (A2 := mkPoint bx by_).
  pose (A3 := mkPoint cx cy).
  pose (B1 := mkPoint dx dy).
  pose (B2 := mkPoint ex ey).
  pose (B3 := mkPoint fx fy).
  assert (HdA' : 0 < gdbl (px A1) (py A1) (px A2) (py A2) (px A3) (py A3))
    by (unfold A1, A2, A3; exact HdA).
  pose proof (remaining_B_not_in_A_of_cone v A1 A2 A3 B1 B2 B3 HdA' HvA HvB Hc)
    as (Hn1 & Hn2).
  pose proof (vertex_is_v_or_others v B1 B2 B3 q HvB Hq) as Hqv.
  destruct Hqv as [Eq | [Eq | Eq]].
  - subst q. apply gtri_strict_pos_b_false_of_A_vertex. exact HvA.
  - subst q. unfold A1, A2, A3, B1, B2, B3 in Hn1.
    apply gtri_strict_pos_b_false_of_not_closure. exact Hn1.
  - subst q. unfold A1, A2, A3, B1, B2, B3 in Hn2.
    apply gtri_strict_pos_b_false_of_not_closure. exact Hn2.
Qed.

Lemma overlap_b_false_of_touch_vertex :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htv.
  pose proof (touch_vertex_b_unpack _ _ _ _ _ _ _ _ _ _ _ _ Htv)
    as (HccwA & HccwB & _ & Hfrom).
  unfold overlap_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [_ | Hn];
    [ | exfalso; apply Hn; exact HccwA ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [_ | Hn];
    [ | exfalso; apply Hn; exact HccwB ].
  unfold some_vertex_strict_pos.
  destruct Hfrom as [Hv | [Hv | Hv]];
    apply touch_vertex_from_v_elim in Hv;
    destruct Hv as (HvA & HvB & Hc);
    rewrite (gtri_strict_pos_b_false_of_B_under_cone
               ax ay bx by_ cx cy dx dy ex ey fx fy _ (mkPoint dx dy)
               HccwA HvA HvB Hc (or_introl eq_refl));
    rewrite (gtri_strict_pos_b_false_of_B_under_cone
               ax ay bx by_ cx cy dx dy ex ey fx fy _ (mkPoint ex ey)
               HccwA HvA HvB Hc (or_intror (or_introl eq_refl)));
    rewrite (gtri_strict_pos_b_false_of_B_under_cone
               ax ay bx by_ cx cy dx dy ex ey fx fy _ (mkPoint fx fy)
               HccwA HvA HvB Hc (or_intror (or_intror eq_refl)));
    reflexivity.
Qed.

Lemma touch_edge_b_false_of_touch_vertex :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    touch_edge_b (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htv.
  pose proof (touch_vertex_b_unpack _ _ _ _ _ _ _ _ _ _ _ _ Htv)
    as (HccwA & _ & Hex & _).
  pose proof (ccw_vertices_distinct
                (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) HccwA)
    as (D12 & D23 & D31).
  exact (touch_edge_b_false_of_exactly_one
           (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
           (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
           Hex D12 D23 D31).
Qed.

(* The headline regime theorem: touch_vertex_b forces TPR_TouchVertex, with
   touch_edge_b, contains_b, overlap_b and separated_b derived false. *)
(* WITNESS {"claimId":"522-i","topic":"relate","lemma":"triangle_pair_regime_touchvertex","title":"TPR_TouchVertex reachable at relate bar 1 via a line-through-vertex certificate","file":"theories/RelateNGTouchVertexRegime.v","witness":"522-i-touchvertex-bar1","board":"#572"} *)
Theorem triangle_pair_regime_touchvertex :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy = TPR_TouchVertex.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htv.
  unfold triangle_pair_regime.
  rewrite (touch_edge_b_false_of_touch_vertex _ _ _ _ _ _ _ _ _ _ _ _ Htv).
  rewrite (contains_b_false_of_touch_vertex _ _ _ _ _ _ _ _ _ _ _ _ Htv).
  rewrite (overlap_b_false_of_touch_vertex _ _ _ _ _ _ _ _ _ _ _ _ Htv).
  rewrite (separated_b_false_of_touch_vertex _ _ _ _ _ _ _ _ _ _ _ _ Htv).
  rewrite Htv. reflexivity.
Qed.

Theorem triangle_pair_regime_touchvertex_sound :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy = TPR_TouchVertex ->
    triangles_touch_at_vertex
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hreg.
  unfold triangle_pair_regime in Hreg.
  destruct (touch_edge_b _ _ _ _ _ _); [ discriminate | ].
  destruct (contains_b ax ay bx by_ cx cy dx dy ex ey fx fy);
    [ discriminate | ].
  destruct (overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy);
    [ discriminate | ].
  destruct (separated_b ax ay bx by_ cx cy dx dy ex ey fx fy);
    [ discriminate | ].
  destruct (touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy) eqn:Htv;
    [ | ].
  - exact (touch_vertex_b_triangles_touch _ _ _ _ _ _ _ _ _ _ _ _ Htv).
  - destruct (touch_partial_edge_b _ _ _ _ _ _);
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
(* Concrete #572 pair: A = (0,0)(2,0)(0,2), B = (0,0)(-2,0)(0,-2).            *)
(* Shared origin; cone normal nA = (2,2) puts A's remaining vertices          *)
(* strictly positive and B's remaining vertices strictly negative.            *)
(* Nudging B's third vertex into A's interior flips the certificate off.      *)
(* Designated fill is `aa_matrix_touch_vertical` (starter; not a proven       *)
(* 0-dim vertex-touch matrix).                                                *)
(* -------------------------------------------------------------------------- *)

Lemma touchvertex_ex_touch_vertex_b :
  touch_vertex_b 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = true.
Proof.
  unfold touch_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 0 (-2))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  apply andb_true_intro. split.
  - unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
    cbn [px py].
    repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
    reflexivity.
  - apply orb_true_intro. left. apply orb_true_intro. left.
    unfold touch_vertex_from_v, is_vertex_b, cone_separates_b,
           both_strict_pos_b, both_strict_neg_b, others_fst, others_snd,
           vec_sum_from, side_dot, point_eqb.
    cbn [px py].
    repeat (progress (destruct (Req_dec_T _ _) as [?e | ?n];
                      try (exfalso; lra))).
    cbn [px py].
    repeat (
      match goal with
      | |- context [Rlt_dec 0 ?e] =>
          let Hlt := fresh "Hlt" in
          assert (Hlt : 0 < e) by (cbn; lra);
          destruct (Rlt_dec 0 e) as [_ | Hn]; [ | lra ]
      | |- context [Rlt_dec ?e 0] =>
          let Hlt := fresh "Hlt" in
          assert (Hlt : e < 0) by (cbn; lra);
          destruct (Rlt_dec e 0) as [_ | Hn]; [ | lra ]
      end).
    reflexivity.
Qed.

(* The former #571 decline pin: A = (0,0)(1,0)(0,1), B = (1,0)(2,0)(2,1)
   share only (1,0).  Cone normal nA = (-2,1) now classifies vertex-touch. *)
Lemma vertex_touch_pair_touch_vertex_b :
  touch_vertex_b 0 0 1 0 0 1 1 0 2 0 2 1 = true.
Proof.
  unfold touch_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 2 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  apply andb_true_intro. split.
  - unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
    cbn [px py].
    repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
    reflexivity.
  - apply orb_true_intro. left. apply orb_true_intro. right.
    unfold touch_vertex_from_v, is_vertex_b, cone_separates_b,
           both_strict_pos_b, both_strict_neg_b, others_fst, others_snd,
           vec_sum_from, side_dot, point_eqb.
    cbn [px py].
    repeat (progress (destruct (Req_dec_T _ _) as [?e | ?n];
                      try (exfalso; lra))).
    cbn [px py].
    repeat (
      match goal with
      | |- context [Rlt_dec 0 ?e] =>
          let Hlt := fresh "Hlt" in
          assert (Hlt : 0 < e) by (cbn; lra);
          destruct (Rlt_dec 0 e) as [_ | Hn]; [ | lra ]
      | |- context [Rlt_dec ?e 0] =>
          let Hlt := fresh "Hlt" in
          assert (Hlt : e < 0) by (cbn; lra);
          destruct (Rlt_dec e 0) as [_ | Hn]; [ | lra ]
      end).
    reflexivity.
Qed.

Lemma vertex_touch_pair_regime :
  triangle_pair_regime 0 0 1 0 0 1 1 0 2 0 2 1 = TPR_TouchVertex.
Proof.
  apply triangle_pair_regime_touchvertex.
  exact vertex_touch_pair_touch_vertex_b.
Qed.

Lemma both_strict_neg_b_false_fst : forall v n p q,
  ~ (side_dot v n p < 0) ->
  both_strict_neg_b v n p q = false.
Proof.
  intros v n p q Hn. unfold both_strict_neg_b.
  destruct (Rlt_dec (side_dot v n p) 0) as [Hlt | _];
    [ contradiction | reflexivity ].
Qed.

Lemma both_strict_pos_b_false_fst : forall v n p q,
  ~ (0 < side_dot v n p) ->
  both_strict_pos_b v n p q = false.
Proof.
  intros v n p q Hn. unfold both_strict_pos_b.
  destruct (Rlt_dec 0 (side_dot v n p)) as [Hlt | _];
    [ contradiction | reflexivity ].
Qed.

Lemma cone_separates_b_false_of_arms : forall v a1 a2 b1 b2,
  both_strict_neg_b v (vec_sum_from v a1 a2) b1 b2 = false ->
  both_strict_pos_b v (vec_sum_from v b1 b2) b1 b2 = false ->
  cone_separates_b v a1 a2 b1 b2 = false.
Proof.
  intros v a1 a2 b1 b2 HnA HnB.
  unfold cone_separates_b.
  rewrite HnA, HnB.
  rewrite andb_false_r, andb_false_l.
  reflexivity.
Qed.

Lemma point_eqb_false_of_neq : forall p q,
  p <> q -> point_eqb p q = false.
Proof.
  intros p q Hne.
  destruct (point_eqb p q) eqn:E; [ | reflexivity ].
  exfalso. apply Hne, point_eqb_sound, E.
Qed.

Lemma is_vertex_b_false_of_none : forall v p q r,
  v <> p -> v <> q -> v <> r ->
  is_vertex_b v p q r = false.
Proof.
  intros v p q r Hp Hq Hr.
  unfold is_vertex_b.
  rewrite (point_eqb_false_of_neq v p Hp).
  rewrite (point_eqb_false_of_neq v q Hq).
  rewrite (point_eqb_false_of_neq v r Hr).
  reflexivity.
Qed.

Lemma mkPoint_neq_px : forall x1 y1 x2 y2,
  x1 <> x2 -> mkPoint x1 y1 <> mkPoint x2 y2.
Proof.
  intros x1 y1 x2 y2 Hn Heq.
  apply (f_equal px) in Heq. cbn in Heq. contradiction.
Qed.

Lemma mkPoint_neq_py : forall x1 y1 x2 y2,
  y1 <> y2 -> mkPoint x1 y1 <> mkPoint x2 y2.
Proof.
  intros x1 y1 x2 y2 Hn Heq.
  apply (f_equal py) in Heq. cbn in Heq. contradiction.
Qed.

(* Ticket nudge: B's third vertex moved into A's interior.  CCW order
   (0,0)(1/2,1/2)(-2,0) so the B-CCW guard still holds; the cone fails
   because (1/2,1/2) sits on A's side of nA = (2,2).  Completeness of
   the resulting overlap is #570. *)
Example touchvertex_nudge_off :
  touch_vertex_b 0 0 2 0 0 2 0 0 (1/2) (1/2) (-2) 0 = false.
Proof.
  unfold touch_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (1/2) (1/2) (-2) 0)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  assert (HA2 : touch_vertex_from_v
            (mkPoint 2 0)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (1/2) (1/2)) (mkPoint (-2) 0) = false).
  { unfold touch_vertex_from_v.
    rewrite (is_vertex_b_false_of_none
               (mkPoint 2 0)
               (mkPoint 0 0) (mkPoint (1/2) (1/2)) (mkPoint (-2) 0)).
    - rewrite andb_false_r, andb_false_l. reflexivity.
    - apply mkPoint_neq_px; lra.
    - apply mkPoint_neq_px; lra.
    - apply mkPoint_neq_px; lra. }
  assert (HA3 : touch_vertex_from_v
            (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (1/2) (1/2)) (mkPoint (-2) 0) = false).
  { unfold touch_vertex_from_v.
    rewrite (is_vertex_b_false_of_none
               (mkPoint 0 2)
               (mkPoint 0 0) (mkPoint (1/2) (1/2)) (mkPoint (-2) 0)).
    - rewrite andb_false_r, andb_false_l. reflexivity.
    - apply mkPoint_neq_py; lra.
    - apply mkPoint_neq_py; lra.
    - apply mkPoint_neq_py; lra. }
  assert (HA1 : touch_vertex_from_v
            (mkPoint 0 0)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (1/2) (1/2)) (mkPoint (-2) 0) = false).
  { unfold touch_vertex_from_v, others_fst, others_snd.
    rewrite (point_eqb_complete (mkPoint 0 0) (mkPoint 0 0) eq_refl).
    rewrite (cone_separates_b_false_of_arms
               (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
               (mkPoint (1/2) (1/2)) (mkPoint (-2) 0)).
    - rewrite andb_false_r. reflexivity.
    - apply both_strict_neg_b_false_fst.
      unfold vec_sum_from, side_dot. cbn [px py]. lra.
    - apply both_strict_pos_b_false_fst.
      unfold vec_sum_from, side_dot. cbn [px py]. lra. }
  rewrite HA1, HA2, HA3.
  rewrite !orb_false_r, andb_false_r.
  reflexivity.
Qed.

Example relate_triangle_touchvertex_ex :
  relate (triangle_geometry 0 0 2 0 0 2)
         (triangle_geometry 0 0 (-2) 0 0 (-2)) =
  tris_relate 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) TPR_TouchVertex.
Proof.
  rewrite relate_on_triangles_dispatches.
  rewrite (triangle_pair_regime_touchvertex 0 0 2 0 0 2
             0 0 (-2) 0 0 (-2) touchvertex_ex_touch_vertex_b).
  reflexivity.
Qed.

(* Open-edge pins. One `lra` per call — `repeat lra` on a 12-hypothesis
   leftover-Ⅰ/Ⅲ miss dies in the pinned flocq container. *)
Lemma on_open_seg_b_false_of_ncross : forall p q r,
  cross p q r <> 0 ->
  on_open_seg_b p q r = false.
Proof.
  intros p q r Hnz.
  unfold on_open_seg_b.
  destruct (Req_dec_T (cross p q r) 0) as [Heq | _];
    [ contradiction | reflexivity ].
Qed.

Lemma on_open_seg_b_false_of_nbetween_fst : forall p q r,
  ~ (0 < (px r - px p) * (px q - px p) + (py r - py p) * (py q - py p)) ->
  on_open_seg_b p q r = false.
Proof.
  intros p q r Hn.
  unfold on_open_seg_b.
  destruct (Req_dec_T (cross p q r) 0) as [_ | _]; [ | reflexivity ].
  destruct (Rlt_dec 0 ((px r - px p) * (px q - px p)
                       + (py r - py p) * (py q - py p)))
    as [Hlt | _]; [ contradiction | reflexivity ].
Qed.

Lemma on_open_seg_b_false_of_nbetween_snd : forall p q r,
  ~ (0 < (px r - px q) * (px p - px q) + (py r - py q) * (py p - py q)) ->
  on_open_seg_b p q r = false.
Proof.
  intros p q r Hn.
  unfold on_open_seg_b.
  destruct (Req_dec_T (cross p q r) 0) as [_ | _]; [ | reflexivity ].
  destruct (Rlt_dec 0 ((px r - px p) * (px q - px p)
                       + (py r - py p) * (py q - py p)))
    as [_ | _]; [ | reflexivity ].
  destruct (Rlt_dec 0 ((px r - px q) * (px p - px q)
                       + (py r - py q) * (py p - py q)))
    as [Hlt | _]; [ contradiction | reflexivity ].
Qed.

(* Leftover Ⅴ mixed-cone: no vertex sits in an open edge.
   Shared origin is an endpoint (nbetween), every other hit has
   nonzero cross. Used by leftover-Ⅴ classify, not a remint. *)
Lemma mixed_cone_no_open_A :
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1) = false.
Proof.
  unfold some_vertex_on_open_edges, vertex_on_open_edges.
  rewrite (on_open_seg_b_false_of_nbetween_fst
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 2 0) (mkPoint 0 2) (mkPoint 0 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_snd
             (mkPoint 0 2) (mkPoint 0 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint (-1) (-1))
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 2 0) (mkPoint 0 2) (mkPoint (-1) (-1))
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 2) (mkPoint 0 0) (mkPoint (-1) (-1))
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 3 1)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 2 0) (mkPoint 0 2) (mkPoint 3 1)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 2) (mkPoint 0 0) (mkPoint 3 1)
             ltac:(unfold cross; cbn [px py]; lra)).
  reflexivity.
Qed.

Lemma mixed_cone_no_open_B :
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 3 1)
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) = false.
Proof.
  unfold some_vertex_on_open_edges, vertex_on_open_edges.
  rewrite (on_open_seg_b_false_of_nbetween_fst
             (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint (-1) (-1)) (mkPoint 3 1) (mkPoint 0 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_snd
             (mkPoint 3 1) (mkPoint 0 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 2 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint (-1) (-1)) (mkPoint 3 1) (mkPoint 2 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 3 1) (mkPoint 0 0) (mkPoint 2 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 0) (mkPoint (-1) (-1)) (mkPoint 0 2)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint (-1) (-1)) (mkPoint 3 1) (mkPoint 0 2)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 3 1) (mkPoint 0 0) (mkPoint 0 2)
             ltac:(unfold cross; cbn [px py]; lra)).
  reflexivity.
Qed.

Lemma mixed_cone_vertex_b_true :
  mixed_cone_vertex_b 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = true.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-1) (-1) 3 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold mixed_cone_from_v, others_fst, others_snd, is_vertex_b, point_eqb.
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

(* Unnamed CCW completeness cex after leftover Ⅴ lives in
   RelateNGUnnamedCex.v (split-gate: this file stays under 1234). *)

(* Mutation replay (in-tree, #572; not an ADR-0004 mint).  Flip exactly
   one comparison below, rebuild this file, then restore the sign.
     1. `both_strict_pos_b`: `0 < side` → `0 <= side`
        pin: `touch_vertex_b_triangles_touch` / `cone_pos_meet_is_v`
        (a remaining vertex on the line lets a non-v boundary point
        sit in both closures).
     2. `both_strict_neg_b`: `side < 0` → `side <= 0`
        pin: `cone_line_unique` (a remaining B-vertex on the line can
        share an edge-segment with A).
     3. `exactly_one_shared_from_a`: drop a `negb` — a shared edge
        would steal the `touch_edge_b` branch. *)

Print Assumptions triangle_pair_regime_touchvertex.
Print Assumptions triangle_pair_regime_touchvertex_sound.
Print Assumptions relate_triangle_touchvertex_ex.
Print Assumptions touchvertex_nudge_off.

