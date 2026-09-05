(* ============================================================================
   NetTopologySuite.Proofs.RelateNGDisjoint
   ----------------------------------------------------------------------------
   Issue #571 / #522 claimId 522-c: TPR_Disjoint reachable at relate bar
   level 1.

   `separated_b` (RelateNGCore) is a sound-but-partial certificate: both
   triangles CCW and some edge of one is a strict supporting line — the
   owner's remaining vertex and the other triangle's three vertices have
   opposite `cross` signs (six edge candidates, pure `Rlt_dec`).  The
   side function is affine, strict at the three far vertices, hence
   strict on every convex combination of those vertices; the owner's
   closed region sits in the complementary half-plane by the definition
   of `gtri`.  Closed regions therefore share no point, which is
   `triangles_separated`.

   Earlier classifier branches are derived false (not assumed).  Pairs
   whose closures miss without a vertex-strict supporting edge
   (partial-edge kiss) used to decline — leftover `Ⅰ` now names
   that pair `TPR_TouchPartialEdge` (fill still `im_unsupported`).
   Completeness is still #577 / leftover `Ⅱ`. Vertex-touch is #572.

   Frozen anchors stay untouched: `touch_int_ext_exclusion` and the
   II-guard maximality refutation.  `triangles_touch_on_shared_edge`
   is not referenced.

   WITNESS topic: relate · claimId: 522-c · witness: 522-c-disjoint-bar1
   macro: relate
   lane: proofs
   issue: #571 / #522
   ADR-0004: not a remint. 522-c is the existing #571 ticket id.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

(* WITNESS {"claimId":"522-c","topic":"relate","lemma":"triangle_pair_regime_disjoint","title":"TPR_Disjoint reachable at relate bar 1 via a separating-edge certificate","file":"theories/RelateNGDisjoint.v","witness":"522-c-disjoint-bar1","board":"#571"} *)

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
From NTS.Proofs Require Import RelateNGCore RelateNGContains RelateNGOverlap.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Boolean unpackers.                                                         *)
(* -------------------------------------------------------------------------- *)

Lemma opposite_sides_b_true : forall p1 p2 p q,
  opposite_sides_b p1 p2 p q = true ->
  cross p1 p2 p * cross p1 p2 q < 0.
Proof.
  intros p1 p2 p q H.
  unfold opposite_sides_b in H.
  destruct (Rlt_dec (cross p1 p2 p * cross p1 p2 q) 0) as [Hlt | _];
    [ exact Hlt | discriminate ].
Qed.

Lemma edge_separates_b_true : forall p1 p2 apex q1 q2 q3,
  edge_separates_b p1 p2 apex q1 q2 q3 = true ->
  opposite_sides p1 p2 apex q1 /\
  opposite_sides p1 p2 apex q2 /\
  opposite_sides p1 p2 apex q3.
Proof.
  intros p1 p2 apex q1 q2 q3 H.
  unfold edge_separates_b in H.
  apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H1 H2].
  unfold opposite_sides; cbn [fst snd].
  repeat split; apply opposite_sides_b_true; assumption.
Qed.

Lemma some_edge_separates_b_elim : forall a1 a2 a3 b1 b2 b3,
  some_edge_separates_b a1 a2 a3 b1 b2 b3 = true ->
  edge_separates_b a1 a2 a3 b1 b2 b3 = true \/
  edge_separates_b a2 a3 a1 b1 b2 b3 = true \/
  edge_separates_b a3 a1 a2 b1 b2 b3 = true \/
  edge_separates_b b1 b2 b3 a1 a2 a3 = true \/
  edge_separates_b b2 b3 b1 a1 a2 a3 = true \/
  edge_separates_b b3 b1 b2 a1 a2 a3 = true.
Proof.
  intros a1 a2 a3 b1 b2 b3 H.
  unfold some_edge_separates_b in H.
  apply orb_true_iff in H as [H | H6];
    [ apply orb_true_iff in H as [H | H5];
      [ apply orb_true_iff in H as [H | H4];
        [ apply orb_true_iff in H as [H | H3];
          [ apply orb_true_iff in H as [H1 | H2];
            [ left; exact H1
            | right; left; exact H2 ]
          | right; right; left; exact H3 ]
        | right; right; right; left; exact H4 ]
      | right; right; right; right; left; exact H5 ]
    | right; right; right; right; right; exact H6 ].
Qed.

Lemma separated_b_unpack :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    0 < gdbl ax ay bx by_ cx cy /\
    0 < gdbl dx dy ex ey fx fy /\
    some_edge_separates_b
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = true.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold separated_b in H.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [ | discriminate ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [ | discriminate ].
  repeat split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cyclic slack / orientation identities.                                     *)
(* -------------------------------------------------------------------------- *)

Lemma gdbl_cyclic : forall ax ay bx by_ cx cy,
  gdbl bx by_ cx cy ax ay = gdbl ax ay bx by_ cx cy.
Proof. intros; unfold gdbl; ring. Qed.

Lemma gsA_eq_gsB_cyc : forall (bx by_ cx cy : R) (pt : Point),
  gsA bx by_ cx cy pt = gsB bx by_ cx cy pt.
Proof. intros; unfold gsA, gsB; ring. Qed.

Lemma gsB_eq_gsC_cyc : forall (ax ay cx cy : R) (pt : Point),
  gsB cx cy ax ay pt = gsC ax ay cx cy pt.
Proof. intros; unfold gsB, gsC; ring. Qed.

Lemma gsC_eq_gsA_cyc : forall (ax ay bx by_ : R) (pt : Point),
  gsC bx by_ ax ay pt = gsA ax ay bx by_ pt.
Proof. intros; unfold gsA, gsC; ring. Qed.

Lemma in_tri_closure_cyclic : forall a1 a2 a3 pt,
  in_tri_closure a1 a2 a3 pt <-> in_tri_closure a2 a3 a1 pt.
Proof.
  intros a1 a2 a3 pt.
  unfold in_tri_closure.
  rewrite !gtri_nonneg_iff.
  rewrite (gsA_eq_gsB_cyc (px a2) (py a2) (px a3) (py a3) pt).
  rewrite (gsB_eq_gsC_cyc (px a1) (py a1) (px a3) (py a3) pt).
  rewrite (gsC_eq_gsA_cyc (px a1) (py a1) (px a2) (py a2) pt).
  split.
  - intros [HA [HB HC]]. repeat split; assumption.
  - intros [HB [HC HA]]. repeat split; assumption.
Qed.

Lemma tri_ccw_cyclic : forall a1 a2 a3,
  tri_ccw a1 a2 a3 <-> tri_ccw a2 a3 a1.
Proof.
  intros a1 a2 a3. unfold tri_ccw.
  rewrite (gdbl_cyclic (px a1) (py a1) (px a2) (py a2) (px a3) (py a3)).
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Affine side function: barycentric combination of `cross`.                  *)
(* -------------------------------------------------------------------------- *)

Lemma slack_sum_free : forall ax ay bx by_ cx cy pt,
  gsA ax ay bx by_ pt + gsB bx by_ cx cy pt + gsC ax ay cx cy pt =
  gdbl ax ay bx by_ cx cy.
Proof. intros; unfold gsA, gsB, gsC, gdbl; ring. Qed.

Lemma cross_barycentric :
  forall p1 p2 dx dy ex ey fx fy pt,
    cross p1 p2 pt * gdbl dx dy ex ey fx fy =
      gsB ex ey fx fy pt * cross p1 p2 (mkPoint dx dy)
    + gsC dx dy fx fy pt * cross p1 p2 (mkPoint ex ey)
    + gsA dx dy ex ey pt * cross p1 p2 (mkPoint fx fy).
Proof. intros; unfold cross, gsA, gsB, gsC, gdbl; simpl; ring. Qed.

Lemma cross_neg_on_closure :
  forall p1 p2 dx dy ex ey fx fy pt,
    0 < gdbl dx dy ex ey fx fy ->
    0 <= gtri dx dy ex ey fx fy pt ->
    cross p1 p2 (mkPoint dx dy) < 0 ->
    cross p1 p2 (mkPoint ex ey) < 0 ->
    cross p1 p2 (mkPoint fx fy) < 0 ->
    cross p1 p2 pt < 0.
Proof.
  intros p1 p2 dx dy ex ey fx fy pt Hd Hg HcD HcE HcF.
  apply gtri_nonneg_iff in Hg.
  destruct Hg as [HA [HB HC]].
  pose proof (slack_sum_free dx dy ex ey fx fy pt) as Hs.
  pose proof (cross_barycentric p1 p2 dx dy ex ey fx fy pt) as Hb.
  set (wD := gsB ex ey fx fy pt).
  set (wE := gsC dx dy fx fy pt).
  set (wF := gsA dx dy ex ey pt).
  set (cD := cross p1 p2 (mkPoint dx dy)).
  set (cE := cross p1 p2 (mkPoint ex ey)).
  set (cF := cross p1 p2 (mkPoint fx fy)).
  set (d := gdbl dx dy ex ey fx fy).
  assert (HwD : 0 <= wD) by (unfold wD; exact HB).
  assert (HwE : 0 <= wE) by (unfold wE; exact HC).
  assert (HwF : 0 <= wF) by (unfold wF; exact HA).
  assert (Hsum : wF + wD + wE = d) by (unfold wD, wE, wF, d; exact Hs).
  assert (HdD : 0 < - cD) by (unfold cD; lra).
  assert (HdE : 0 < - cE) by (unfold cE; lra).
  assert (HdF : 0 < - cF) by (unfold cF; lra).
  assert (Hpos : 0 < wD * (- cD) + wE * (- cE) + wF * (- cF)).
  { assert (Hm : 0 < Rmin (Rmin (- cD) (- cE)) (- cF)).
    { rewrite !Rmin_pos_iff. repeat split; assumption. }
    pose proof (Rmin_l (- cD) (- cE)) as M1.
    pose proof (Rmin_r (- cD) (- cE)) as M2.
    pose proof (Rmin_l (Rmin (- cD) (- cE)) (- cF)) as M3.
    pose proof (Rmin_r (Rmin (- cD) (- cE)) (- cF)) as M4.
    unfold d in Hsum, Hd.
    nra. }
  assert (Hcombo : wD * cD + wE * cE + wF * cF < 0) by lra.
  assert (Hprod : cross p1 p2 pt * d < 0).
  { unfold d. rewrite Hb. fold wD wE wF cD cE cF. exact Hcombo. }
  unfold d in Hprod. unfold d in Hd. nra.
Qed.

Lemma opposite_sides_apex_pos_far_neg : forall p1 p2 apex q,
  0 < cross p1 p2 apex ->
  opposite_sides p1 p2 apex q ->
  cross p1 p2 q < 0.
Proof.
  intros p1 p2 apex q Hapex Hopp.
  unfold opposite_sides in Hopp.
  nra.
Qed.

Lemma gsA_at_apex : forall ax ay bx by_ cx cy,
  gsA ax ay bx by_ (mkPoint cx cy) = gdbl ax ay bx by_ cx cy.
Proof. intros; unfold gsA, gdbl; simpl; ring. Qed.

Lemma gdbl_eq_cross_pt : forall a1 a2 a3,
  gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) = cross a1 a2 a3.
Proof. intros [] [] []; unfold gdbl, cross; simpl; ring. Qed.

Lemma gsA_eq_cross_pt : forall a1 a2 p,
  gsA (px a1) (py a1) (px a2) (py a2) p = cross a1 a2 p.
Proof. intros [] [] p; unfold gsA, cross; simpl; ring. Qed.

Lemma point_eta : forall p, mkPoint (px p) (py p) = p.
Proof. intros []; reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* One supporting edge implies the closed regions miss.                       *)
(* -------------------------------------------------------------------------- *)

Lemma edge_separates_no_common :
  forall a1 a2 a3 b1 b2 b3 pt,
    tri_ccw a1 a2 a3 ->
    tri_ccw b1 b2 b3 ->
    opposite_sides a1 a2 a3 b1 ->
    opposite_sides a1 a2 a3 b2 ->
    opposite_sides a1 a2 a3 b3 ->
    ~ (in_tri_closure a1 a2 a3 pt /\ in_tri_closure b1 b2 b3 pt).
Proof.
  intros a1 a2 a3 b1 b2 b3 pt HccwA HccwB Hop1 Hop2 Hop3 [HA HB].
  unfold tri_ccw in HccwA, HccwB.
  unfold in_tri_closure in HA, HB.
  assert (Hapex : 0 < cross a1 a2 a3).
  { rewrite <- gdbl_eq_cross_pt. exact HccwA. }
  assert (Hn1 : cross a1 a2 b1 < 0)
    by (apply (opposite_sides_apex_pos_far_neg a1 a2 a3 b1 Hapex Hop1)).
  assert (Hn2 : cross a1 a2 b2 < 0)
    by (apply (opposite_sides_apex_pos_far_neg a1 a2 a3 b2 Hapex Hop2)).
  assert (Hn3 : cross a1 a2 b3 < 0)
    by (apply (opposite_sides_apex_pos_far_neg a1 a2 a3 b3 Hapex Hop3)).
  apply gtri_nonneg_iff in HA.
  destruct HA as [HsA _].
  rewrite gsA_eq_cross_pt in HsA.
  assert (Hneg : cross a1 a2 pt < 0).
  { apply (cross_neg_on_closure a1 a2
             (px b1) (py b1) (px b2) (py b2) (px b3) (py b3) pt HccwB HB);
      rewrite !point_eta; assumption. }
  lra.
Qed.

Lemma edge_separates_b_no_common :
  forall a1 a2 a3 b1 b2 b3 pt,
    tri_ccw a1 a2 a3 ->
    tri_ccw b1 b2 b3 ->
    edge_separates_b a1 a2 a3 b1 b2 b3 = true ->
    ~ (in_tri_closure a1 a2 a3 pt /\ in_tri_closure b1 b2 b3 pt).
Proof.
  intros a1 a2 a3 b1 b2 b3 pt HccwA HccwB Hsep.
  apply edge_separates_b_true in Hsep.
  destruct Hsep as (H1 & H2 & H3).
  exact (edge_separates_no_common a1 a2 a3 b1 b2 b3 pt HccwA HccwB H1 H2 H3).
Qed.

Lemma edge_separates_b_no_common_cyc :
  forall a1 a2 a3 b1 b2 b3 pt,
    tri_ccw a1 a2 a3 ->
    tri_ccw b1 b2 b3 ->
    edge_separates_b a2 a3 a1 b1 b2 b3 = true ->
    ~ (in_tri_closure a1 a2 a3 pt /\ in_tri_closure b1 b2 b3 pt).
Proof.
  intros a1 a2 a3 b1 b2 b3 pt HccwA HccwB Hsep [HA HB].
  apply (edge_separates_b_no_common a2 a3 a1 b1 b2 b3 pt);
    [ rewrite <- tri_ccw_cyclic; exact HccwA | exact HccwB | exact Hsep | ].
  split; [ rewrite <- in_tri_closure_cyclic; exact HA | exact HB ].
Qed.

Lemma edge_separates_b_no_common_cyc2 :
  forall a1 a2 a3 b1 b2 b3 pt,
    tri_ccw a1 a2 a3 ->
    tri_ccw b1 b2 b3 ->
    edge_separates_b a3 a1 a2 b1 b2 b3 = true ->
    ~ (in_tri_closure a1 a2 a3 pt /\ in_tri_closure b1 b2 b3 pt).
Proof.
  intros a1 a2 a3 b1 b2 b3 pt HccwA HccwB Hsep [HA HB].
  apply (edge_separates_b_no_common a3 a1 a2 b1 b2 b3 pt);
    [ rewrite <- tri_ccw_cyclic, <- tri_ccw_cyclic; exact HccwA
    | exact HccwB | exact Hsep | ].
  split; [ rewrite <- in_tri_closure_cyclic, <- in_tri_closure_cyclic; exact HA
         | exact HB ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Certificate ⇒ geometry.                                                    *)
(* -------------------------------------------------------------------------- *)

Theorem separated_b_triangles_separated :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangles_separated
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hsep.
  pose proof (separated_b_unpack _ _ _ _ _ _ _ _ _ _ _ _ Hsep)
    as (HccwA & HccwB & Hedge).
  unfold triangles_separated, tri_ccw.
  split; [ exact HccwA | split; [ exact HccwB | ] ].
  intros pt Hboth.
  pose (A1 := mkPoint ax ay).
  pose (A2 := mkPoint bx by_).
  pose (A3 := mkPoint cx cy).
  pose (B1 := mkPoint dx dy).
  pose (B2 := mkPoint ex ey).
  pose (B3 := mkPoint fx fy).
  assert (HccwAP : tri_ccw A1 A2 A3) by (unfold A1, A2, A3, tri_ccw; exact HccwA).
  assert (HccwBP : tri_ccw B1 B2 B3) by (unfold B1, B2, B3, tri_ccw; exact HccwB).
  apply some_edge_separates_b_elim in Hedge.
  destruct Hedge as [H | [H | [H | [H | [H | H]]]]].
  - exact (edge_separates_b_no_common A1 A2 A3 B1 B2 B3 pt HccwAP HccwBP H Hboth).
  - exact (edge_separates_b_no_common_cyc A1 A2 A3 B1 B2 B3 pt HccwAP HccwBP H Hboth).
  - exact (edge_separates_b_no_common_cyc2 A1 A2 A3 B1 B2 B3 pt HccwAP HccwBP H Hboth).
  - apply (edge_separates_b_no_common B1 B2 B3 A1 A2 A3 pt HccwBP HccwAP H).
    destruct Hboth; split; assumption.
  - apply (edge_separates_b_no_common_cyc B1 B2 B3 A1 A2 A3 pt HccwBP HccwAP H).
    destruct Hboth; split; assumption.
  - apply (edge_separates_b_no_common_cyc2 B1 B2 B3 A1 A2 A3 pt HccwBP HccwAP H).
    destruct Hboth; split; assumption.
Qed.

(* WITNESS topic: relate · claimId: 522-c · witness: 522-c-disjoint-bar1 *)
(* WITNESS {"claimId":"522-c","topic":"relate","lemma":"triangle_pair_regime_disjoint","title":"TPR_Disjoint reachable at relate bar 1 via a separating-edge certificate","file":"theories/RelateNGDisjoint.v","witness":"522-c-disjoint-bar1","board":"#571"} *)

Theorem separated_b_partial_separated :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangles_separated
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy).
Proof. exact separated_b_triangles_separated. Qed.

(* -------------------------------------------------------------------------- *)
(* Earlier branches derived false.                                            *)
(* -------------------------------------------------------------------------- *)

Lemma B_vertex_exterior_of_separated :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy p,
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    is_vertex_of p (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    gtri ax ay bx by_ cx cy p < 0.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy p Hsep Hv.
  pose proof (separated_b_triangles_separated _ _ _ _ _ _ _ _ _ _ _ _ Hsep)
    as (HccwA & HccwB & Hmiss).
  assert (HB : in_tri_closure (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) p)
    by (apply vertex_in_tri_closure; [ exact HccwB | exact Hv ]).
  assert (HnA : ~ in_tri_closure (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) p)
    by (intros HA; exact (Hmiss p (conj HA HB))).
  unfold in_tri_closure in HnA. apply Rnot_le_lt. exact HnA.
Qed.

Lemma vertex_ne_of_separated :
  forall a1 a2 a3 b1 b2 b3 va vb,
    triangles_separated a1 a2 a3 b1 b2 b3 ->
    is_vertex_of va a1 a2 a3 ->
    is_vertex_of vb b1 b2 b3 ->
    va <> vb.
Proof.
  intros a1 a2 a3 b1 b2 b3 va vb (HccwA & HccwB & Hmiss) HvA HvB Heq.
  subst vb.
  exact (Hmiss va (conj (vertex_in_tri_closure _ _ _ _ HccwA HvA)
                        (vertex_in_tri_closure _ _ _ _ HccwB HvB))).
Qed.

Lemma A_vertices_ne_B_of_separated :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    mkPoint ax ay <> mkPoint dx dy /\
    mkPoint ax ay <> mkPoint ex ey /\
    mkPoint ax ay <> mkPoint fx fy /\
    mkPoint bx by_ <> mkPoint dx dy /\
    mkPoint bx by_ <> mkPoint ex ey /\
    mkPoint bx by_ <> mkPoint fx fy /\
    mkPoint cx cy <> mkPoint dx dy /\
    mkPoint cx cy <> mkPoint ex ey /\
    mkPoint cx cy <> mkPoint fx fy.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hsep.
  pose proof (separated_b_triangles_separated _ _ _ _ _ _ _ _ _ _ _ _ Hsep) as Hgeo.
  pose (A1 := mkPoint ax ay).
  pose (A2 := mkPoint bx by_).
  pose (A3 := mkPoint cx cy).
  pose (B1 := mkPoint dx dy).
  pose (B2 := mkPoint ex ey).
  pose (B3 := mkPoint fx fy).
  unfold A1, A2, A3, B1, B2, B3.
  repeat split;
    (eapply (vertex_ne_of_separated (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
               (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy));
     [ exact Hgeo
     | first [ left; reflexivity | right; left; reflexivity | right; right; reflexivity ]
     | first [ left; reflexivity | right; left; reflexivity | right; right; reflexivity ] ]).
Qed.

Lemma touch_edge_b_false_of_separated :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    touch_edge_b (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hsep.
  pose proof (A_vertices_ne_B_of_separated _ _ _ _ _ _ _ _ _ _ _ _ Hsep)
    as (N11 & N12 & N13 & N21 & N22 & N23 & N31 & N32 & N33).
  exact (touch_edge_b_false_of_ne _ _ _ _ _ _
           N11 N12 N13 N21 N22 N23 N31 N32 N33).
Qed.

Lemma contains_b_false_of_separated :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hsep.
  apply contains_b_false_of_B_exterior.
  left.
  apply (B_vertex_exterior_of_separated _ _ _ _ _ _ _ _ _ _ _ _ (mkPoint dx dy) Hsep).
  left; reflexivity.
Qed.

Lemma overlap_b_false_of_separated :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hsep.
  unfold overlap_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [_ | _]; [ | reflexivity ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [_ | _]; [ | reflexivity ].
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  assert (H1 : gtri ax ay bx by_ cx cy (mkPoint dx dy) < 0)
    by (apply (B_vertex_exterior_of_separated _ _ _ _ _ _ _ _ _ _ _ _ _ Hsep);
        left; reflexivity).
  assert (H2 : gtri ax ay bx by_ cx cy (mkPoint ex ey) < 0)
    by (apply (B_vertex_exterior_of_separated _ _ _ _ _ _ _ _ _ _ _ _ _ Hsep);
        right; left; reflexivity).
  assert (H3 : gtri ax ay bx by_ cx cy (mkPoint fx fy) < 0)
    by (apply (B_vertex_exterior_of_separated _ _ _ _ _ _ _ _ _ _ _ _ _ Hsep);
        right; right; reflexivity).
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint dx dy))) as [Hlt | _];
    [ exfalso; lra | ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint ex ey))) as [Hlt | _];
    [ exfalso; lra | ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint fx fy))) as [Hlt | _];
    [ exfalso; lra | reflexivity ].
Qed.

(* The headline regime theorem: separated_b forces TPR_Disjoint, with
   touch_edge_b, contains_b and overlap_b derived false. *)
Theorem triangle_pair_regime_disjoint :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy = TPR_Disjoint.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hsep.
  unfold triangle_pair_regime.
  rewrite (touch_edge_b_false_of_separated _ _ _ _ _ _ _ _ _ _ _ _ Hsep).
  rewrite (contains_b_false_of_separated _ _ _ _ _ _ _ _ _ _ _ _ Hsep).
  rewrite (overlap_b_false_of_separated _ _ _ _ _ _ _ _ _ _ _ _ Hsep).
  rewrite Hsep. reflexivity.
Qed.

Theorem triangle_pair_regime_disjoint_sound :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy = TPR_Disjoint ->
    triangles_separated
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
  destruct (separated_b ax ay bx by_ cx cy dx dy ex ey fx fy) eqn:Hsep;
    [ exact (separated_b_triangles_separated _ _ _ _ _ _ _ _ _ _ _ _ Hsep)
    | ].
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
(* Concrete #530 pair now classifies disjoint.                                *)
(* A = (0,0)(1,0)(0,1), B = (2,0)(3,0)(2,1).                                  *)
(* A's hypotenuse is a strict supporting line; designated fill is             *)
(* `aa_matrix_disjoint` (the TPR_Disjoint witness).                           *)
(* -------------------------------------------------------------------------- *)

Lemma dispatch_pair_separated_b :
  separated_b 0 0 1 0 0 1 2 0 3 0 2 1 = true.
Proof.
  unfold separated_b, some_edge_separates_b, edge_separates_b, opposite_sides_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 2 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  destruct (Rlt_dec (cross (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                    * cross (mkPoint 0 0) (mkPoint 1 0) (mkPoint 2 0)) 0)
    as [Hbot | _];
    [ exfalso; unfold cross in Hbot; cbn [px py] in Hbot; lra | ].
  destruct (Rlt_dec (cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
                    * cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 2 0)) 0)
    as [_ | Hn];
    [ | exfalso; apply Hn; unfold cross; cbn [px py]; lra ].
  destruct (Rlt_dec (cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
                    * cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 3 0)) 0)
    as [_ | Hn];
    [ | exfalso; apply Hn; unfold cross; cbn [px py]; lra ].
  destruct (Rlt_dec (cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
                    * cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 2 1)) 0)
    as [_ | Hn];
    [ | exfalso; apply Hn; unfold cross; cbn [px py]; lra ].
  reflexivity.
Qed.

Example relate_triangle_disjoint_ex :
  relate (triangle_geometry 0 0 1 0 0 1)
         (triangle_geometry 2 0 3 0 2 1) =
  tris_relate 0 0 1 0 0 1 2 0 3 0 2 1 TPR_Disjoint.
Proof. exact relate_triangle_dispatch_ex. Qed.

Example relate_triangle_disjoint_ex_separated :
  triangles_separated
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1).
Proof. exact (separated_b_triangles_separated 0 0 1 0 0 1 2 0 3 0 2 1
                 dispatch_pair_separated_b). Qed.

Lemma opposite_sides_b_false_of_nlt : forall p1 p2 p q,
  ~ (cross p1 p2 p * cross p1 p2 q < 0) ->
  opposite_sides_b p1 p2 p q = false.
Proof.
  intros p1 p2 p q Hn. unfold opposite_sides_b.
  destruct (Rlt_dec (cross p1 p2 p * cross p1 p2 q) 0) as [Hlt | _];
    [ contradiction | reflexivity ].
Qed.

Lemma edge_separates_b_false_l : forall p1 p2 apex q1 q2 q3,
  opposite_sides_b p1 p2 apex q1 = false ->
  edge_separates_b p1 p2 apex q1 q2 q3 = false.
Proof.
  intros p1 p2 apex q1 q2 q3 H. unfold edge_separates_b. rewrite H. reflexivity.
Qed.

Lemma vertex_touch_no_separator :
  some_edge_separates_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 2 0) (mkPoint 2 1) = false.
Proof.
  unfold some_edge_separates_b.
  (* A bottom: B's (1,0) is an endpoint. *)
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
             (mkPoint 1 0) (mkPoint 2 0) (mkPoint 2 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* A hypotenuse: B's (1,0) is an endpoint. *)
  rewrite (edge_separates_b_false_l (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
             (mkPoint 1 0) (mkPoint 2 0) (mkPoint 2 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* A left: B's (1,0) is the apex of A, same side. *)
  rewrite (edge_separates_b_false_l (mkPoint 0 1) (mkPoint 0 0) (mkPoint 1 0)
             (mkPoint 1 0) (mkPoint 2 0) (mkPoint 2 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* B bottom: A's (0,0) is collinear on y = 0. *)
  rewrite (edge_separates_b_false_l (mkPoint 1 0) (mkPoint 2 0) (mkPoint 2 1)
             (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* B right x=2: A's (0,0) is on the same side as the apex (1,0). *)
  rewrite (edge_separates_b_false_l (mkPoint 2 0) (mkPoint 2 1) (mkPoint 1 0)
             (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* B hypotenuse: A's (1,0) is an endpoint (q2). *)
  assert (E6 : edge_separates_b (mkPoint 2 1) (mkPoint 1 0) (mkPoint 2 0)
                 (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) = false).
  { unfold edge_separates_b, opposite_sides_b, cross; cbn [px py].
    destruct (Rlt_dec (_ * _) 0) as [_ | Hn];
      [ | exfalso; apply Hn; lra ].
    destruct (Rlt_dec (_ * _) 0) as [Hbad | _];
      [ exfalso; lra | reflexivity ]. }
  rewrite E6. reflexivity.
Qed.

(* Partial-edge kiss / T-junction still declines: A = (0,0)(2,0)(0,1),
   B = (1,0)(3,0)(2,1) share a boundary segment but no vertex and no
   full edge.  Completeness of leftover declines is #577.  The former
   vertex-touch pin now classifies as TPR_TouchVertex (#572). *)
Lemma tjunction_no_separator :
  some_edge_separates_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 3 0) (mkPoint 2 1) = false.
Proof.
  unfold some_edge_separates_b.
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
             (mkPoint 1 0) (mkPoint 3 0) (mkPoint 2 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 2 0) (mkPoint 0 1) (mkPoint 0 0)
             (mkPoint 1 0) (mkPoint 3 0) (mkPoint 2 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 0 1) (mkPoint 0 0) (mkPoint 2 0)
             (mkPoint 1 0) (mkPoint 3 0) (mkPoint 2 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 1 0) (mkPoint 3 0) (mkPoint 2 1)
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 3 0) (mkPoint 2 1) (mkPoint 1 0)
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  assert (E6 : edge_separates_b (mkPoint 2 1) (mkPoint 1 0) (mkPoint 3 0)
                 (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1) = false).
  { unfold edge_separates_b, opposite_sides_b, cross; cbn [px py].
    destruct (Rlt_dec (_ * _) 0) as [_ | Hn];
      [ | exfalso; apply Hn; lra ].
    destruct (Rlt_dec (_ * _) 0) as [Hbad | _];
      [ exfalso; lra | reflexivity ]. }
  rewrite E6. reflexivity.
Qed.

Lemma tjunction_touch_partial_edge_b :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 3 0) (mkPoint 2 1) = true.
Proof.
  unfold touch_partial_edge_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma tjunction_pair_touch_partial :
  triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1 = TPR_TouchPartialEdge.
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
  destruct (Rlt_dec 0 (gdbl 1 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 1 (mkPoint 1 0))) as [H1 | _];
    [ exfalso; lra | ].
  assert (H30 : gtri 0 0 2 0 0 1 (mkPoint 3 0) <= 0).
  { unfold gtri.
    assert (H : gsA 0 0 2 0 (mkPoint 3 0) = 0) by (unfold gsA; simpl; ring).
    rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_l_le ]. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 1 (mkPoint 3 0))) as [H2 | _];
    [ exfalso; lra | ].
  assert (H21 : gtri 0 0 2 0 0 1 (mkPoint 2 1) < 0).
  { eapply Rle_lt_trans; [ apply (gtri_le_gsB 0 0 2 0 0 1 (mkPoint 2 1)) | ].
    unfold gsB; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 1 (mkPoint 2 1))) as [H3 | _];
    [ exfalso; lra | ].
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  rewrite tjunction_no_separator.
  unfold touch_vertex_b, exactly_one_shared_from_a, is_vertex_b, point_eqb.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  rewrite tjunction_touch_partial_edge_b.
  reflexivity.
Qed.

(** The leftover-Ⅰ pair's fill is still [im_unsupported]
    (historical name: the regime used to be [TPR_Unsupported]). *)
Lemma tjunction_pair_unsupported :
  triangle_pair_fill
    (triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1) = im_unsupported.
Proof.
  rewrite tjunction_pair_touch_partial.
  exact triangle_pair_fill_touch_partial_eq.
Qed.

Lemma relate_tjunction_pair_no_predicate :
  forall r : RelatePredicate,
    ~ predicate_holds r (relate (triangle_geometry 0 0 2 0 0 1)
                                (triangle_geometry 1 0 3 0 2 1)).
Proof.
  intros r.
  rewrite relate_on_triangles_dispatches.
  unfold tris_relate.
  rewrite tjunction_pair_unsupported.
  exact (im_unsupported_no_predicate r).
Qed.

(* Mutation replay (in-tree, #571; not an ADR-0004 mint).  Flip exactly
   one comparison below, rebuild this file, then restore the sign.
     1. `opposite_sides_b`: `cross * cross < 0` → `cross * cross <= 0`
        pin: `separated_b_triangles_separated` / `cross_neg_on_closure`
        (a collinear far vertex puts a B-vertex on the supporting line,
        so the closures can meet on that line).
     2. `separated_b` CCW guards: drop `0 < gdbl B`
        pin: `separated_b_triangles_separated` (CW B empties the closed
        region `{0 <= gtri}` and the barycentric weights change sign).
     3. `cross_neg_on_closure`: weaken one far-vertex `cross < 0` to
        `cross <= 0` — the nonnegative combination can land at 0. *)

Print Assumptions triangle_pair_regime_disjoint.
Print Assumptions separated_b_triangles_separated.
Print Assumptions triangle_pair_regime_disjoint_sound.
Print Assumptions relate_triangle_disjoint_ex.
Print Assumptions relate_tjunction_pair_no_predicate.
