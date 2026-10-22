(* ============================================================================
   NetTopologySuite.Proofs.ArcSimilarityImage
   ----------------------------------------------------------------------------
   claimId `arc-sim-image`.  The proof half of the statement/proof split; the
   statements live in ArcSimilarityStmt.v and this file proves exactly
     arc_similarity_claim      : ArcSimilarityStmt.claim       (main)
     arc_similarity_supporting : ArcSimilarityStmt.supporting  (supporting)
     arc_similarity_witness    : ArcSimilarityStmt.witness     (witness)
   (pinned by scripts/check_claim_statements.py, docs/claim-statements.json).

   A similarity z |-> (a + b i) z + t or z |-> (a + b i) conj(z) + t
   (a + b i <> 0, i.e. sim_k2 = a^2 + b^2 <> 0; t the translation) maps the
   SQL/MM three-point arc `CurveGeometry.CircularArc` to the arc through the
   images of its three control points:
     sim_dist_sq      squared distance scales by a^2 + b^2;
     sim_valid_arc    non-collinear controls stay non-collinear;
     sim_arc_center   the image of the centre is the centre of the image arc;
     sim_arc_radius   the radius scales by sqrt (a^2 + b^2);
     sim_on_arc_iff   X is on the arc iff its image is on the image arc
                      (`CurveRingSimple.on_arc`: circumcircle and sweep).
   `is_similarity_q_dec` decides the similarity test on rational affine maps,
   and `qaff_similarity_on_arc_iff` transports the arc for every map it accepts.

   Witness (one sample, not a converse): the non-similarity scale (2,1) is NOT
   exact on the control points of the unit upper arc (1,0),(0,1),(-1,0): the
   image (6/5,4/5) of the arc point (3/5,4/5) is off the circle through the
   three moved controls.  The Q twin computes that residual from the controls
   (`q_circ_resid`, centre via CircularCookLineArcZ.qOx/qOy, bridged to
   arc_center by `q_circ_resid_R`): 12/25, not 0.  That is the squared
   residual at the single point (3/5, 4/5).  Over the whole arc the residual
   is 3 y (1 - y) (`scale21_resid_formula`), so its maximum is 3/4, at
   (sqrt 3 / 2, 1/2) (`scale21_resid_max`); 12/25 is not the maximum.

   Suspected consumer (a suspicion, not a verified finding): GEOS
   GEOSGeom_transformXY moves arc control points independently, which by the
   witness is not the image of the arc unless the transform is a similarity.

   Ideas from openai/math@1581d4cb (Koebe 071 rigidity, Comparator split);
   nothing from that catalogue is cited as proved.  ExactCircularArc is the
   JTS Java class; the Rocq arc here is CircularArc.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending
   (review.status in docs/claim-statements.json).
   ========================================================================== *)

From Stdlib Require Import Reals Lra QArith Qreals Bool.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcIntersect
  CurveRingSimple CircularCookLineArcZ CircularCookLineArcR ArcSimilarityStmt.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Scaling laws of a similarity.                                          *)
(* -------------------------------------------------------------------------- *)

Definition sim_sign (m : Sim2) : R := if sim_refl m then -1 else 1.

Lemma sim_sign_sq : forall m, sim_sign m * sim_sign m = 1.
Proof. intros [a b tx ty [|]]; unfold sim_sign; simpl; ring. Qed.

Lemma sim_dist_sq : sim_dist_sq_stmt.
Proof.
  intros [a b tx ty [|]] p q; unfold sim_apply, sim_k2, dist_sq; simpl; ring.
Qed.

Lemma sim_cross : forall m P0 P1 Q,
  cross_R_pt (sim_apply m P0) (sim_apply m P1) (sim_apply m Q)
  = sim_sign m * sim_k2 m * cross_R_pt P0 P1 Q.
Proof.
  intros [a b tx ty [|]] P0 P1 Q; unfold sim_apply, sim_k2, sim_sign, cross_R_pt;
    simpl; ring.
Qed.

Lemma sim_incircle : forall m A B C P,
  inCircle_R (sim_apply m A) (sim_apply m B) (sim_apply m C) (sim_apply m P)
  = sim_sign m * (sim_k2 m * sim_k2 m) * inCircle_R A B C P.
Proof.
  intros [a b tx ty [|]] A B C P; unfold sim_apply, sim_k2, sim_sign, inCircle_R;
    simpl; ring.
Qed.

Lemma sim_k2_nonneg : forall m, 0 <= sim_k2 m.
Proof. intro m. unfold sim_k2. nra. Qed.

Lemma sim_sign_k2_neq : forall m, sim_k2 m <> 0 -> sim_sign m * sim_k2 m <> 0.
Proof.
  intros m Hk. apply Rmult_integral_contrapositive_currified; [|exact Hk].
  unfold sim_sign. destruct (sim_refl m); lra.
Qed.

Lemma sim_injective : forall m p q,
  sim_k2 m <> 0 -> sim_apply m p = sim_apply m q -> p = q.
Proof.
  intros m p q Hk He.
  assert (H0 : sim_k2 m * dist_sq p q = 0).
  { rewrite <- sim_dist_sq, He. apply dist_sq_zero_iff_eq. split; reflexivity. }
  destruct (Rmult_integral _ _ H0) as [H|H]; [contradiction|].
  apply dist_sq_zero_iff_eq in H. destruct p as [x1 y1], q as [x2 y2]. simpl in H.
  destruct H as [-> ->]. reflexivity.
Qed.

(* valid_arc is the cross product of (start, mid, end). *)
Lemma valid_arc_cross : forall a,
  valid_arc a <-> cross_R_pt (arc_start a) (arc_mid a) (arc_end a) <> 0.
Proof.
  intro a. unfold valid_arc, cross_R_pt. cbv zeta.
  replace ((px (arc_mid a) - px (arc_start a)) * (py (arc_end a) - py (arc_start a))
           - (px (arc_end a) - px (arc_start a)) * (py (arc_mid a) - py (arc_start a)))
    with ((px (arc_mid a) - px (arc_start a)) * (py (arc_end a) - py (arc_start a))
          - (py (arc_mid a) - py (arc_start a)) * (px (arc_end a) - px (arc_start a)))
    by ring.
  reflexivity.
Qed.

Lemma sim_valid_arc : sim_valid_arc_stmt.
Proof.
  intros m a Hk Hv. apply valid_arc_cross. apply valid_arc_cross in Hv.
  unfold map_arc. cbn [arc_start arc_mid arc_end]. rewrite sim_cross.
  apply Rmult_integral_contrapositive_currified; [apply sim_sign_k2_neq|]; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The centre, the radius and arc membership are transported.              *)
(* -------------------------------------------------------------------------- *)

Lemma sim_arc_center : sim_arc_center_stmt.
Proof.
  intros m a Hk Hv. apply valid_arc_cross in Hv.
  assert (Hm : cross_R_pt (sim_apply m (arc_start a)) (sim_apply m (arc_mid a))
                 (sim_apply m (arc_end a)) <> 0).
  { rewrite sim_cross. apply Rmult_integral_contrapositive_currified;
      [apply sim_sign_k2_neq|]; assumption. }
  destruct a as [[sx sy] [mx my] [ex ey]].
  destruct m as [ka kb tx ty [|]];
  unfold sim_k2, map_arc, arc_center, sim_apply, cross_R_pt in *;
  cbn [arc_start arc_mid arc_end px py sim_a sim_b sim_tx sim_ty sim_refl] in *;
  f_equal; field; repeat split; intro H0;
  first [ apply Hm; lra | apply Hv; lra | apply Hm; nra | apply Hv; nra ].
Qed.

Lemma sim_arc_radius : sim_arc_radius_stmt.
Proof.
  intros m a Hk Hv. unfold arc_radius, dist.
  rewrite sim_arc_center by assumption.
  unfold map_arc. cbn [arc_start].
  rewrite sim_dist_sq. apply sqrt_mult; [apply sim_k2_nonneg | apply dist_sq_nonneg].
Qed.

Lemma sim_on_arc_iff : forall m a X, sim_k2 m <> 0 ->
  (on_arc a X <-> on_arc (map_arc (sim_apply m) a) (sim_apply m X)).
Proof.
  intros m a X Hk.
  assert (Hc : sim_sign m * (sim_k2 m * sim_k2 m) <> 0).
  { replace (sim_sign m * (sim_k2 m * sim_k2 m)) with ((sim_sign m * sim_k2 m) * sim_k2 m)
      by ring.
    apply Rmult_integral_contrapositive_currified; [apply sim_sign_k2_neq|]; assumption. }
  assert (Hp : 0 < (sim_sign m * sim_k2 m) * (sim_sign m * sim_k2 m)).
  { pose proof (sim_sign_k2_neq m Hk). nra. }
  unfold on_arc, map_arc, arc_span_contains, arc_interior_side, arc_side_chord.
  cbn [arc_start arc_mid arc_end].
  rewrite sim_incircle, !sim_cross.
  split.
  - intros [Hi Hs]. split.
    + rewrite Hi. ring.
    + destruct Hs as [Hs | [Hs | Hs]].
      * left.
        replace (sim_sign m * sim_k2 m * cross_R_pt (arc_start a) (arc_end a) (arc_mid a)
                 * (sim_sign m * sim_k2 m * cross_R_pt (arc_start a) (arc_end a) X))
          with ((sim_sign m * sim_k2 m) * (sim_sign m * sim_k2 m)
                * (cross_R_pt (arc_start a) (arc_end a) (arc_mid a)
                   * cross_R_pt (arc_start a) (arc_end a) X)) by ring.
        apply Rmult_lt_0_compat; assumption.
      * right; left. rewrite Hs. reflexivity.
      * right; right. rewrite Hs. reflexivity.
  - intros [Hi Hs]. split.
    + destruct (Rmult_integral _ _ Hi) as [H|H]; [contradiction | exact H].
    + destruct Hs as [Hs | [Hs | Hs]].
      * left.
        replace (sim_sign m * sim_k2 m * cross_R_pt (arc_start a) (arc_end a) (arc_mid a)
                 * (sim_sign m * sim_k2 m * cross_R_pt (arc_start a) (arc_end a) X))
          with ((sim_sign m * sim_k2 m) * (sim_sign m * sim_k2 m)
                * (cross_R_pt (arc_start a) (arc_end a) (arc_mid a)
                   * cross_R_pt (arc_start a) (arc_end a) X)) in Hs by ring.
        nra.
      * right; left. exact (sim_injective m _ _ Hk Hs).
      * right; right. exact (sim_injective m _ _ Hk Hs).
Qed.

Theorem arc_similarity_claim : ArcSimilarityStmt.claim.
Proof.
  unfold claim. split; [exact sim_dist_sq|].
  split; [exact sim_valid_arc|]. split; [exact sim_arc_center|].
  split; [exact sim_arc_radius|]. exact sim_on_arc_iff.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Rational affine maps: the decidable similarity test.                    *)
(* -------------------------------------------------------------------------- *)

Definition is_similarity_qb (m : QAff) : bool :=
  ((Qeq_bool (qm11 m) (qm22 m) && Qeq_bool (qm12 m) (- qm21 m))
   || (Qeq_bool (qm11 m) (- qm22 m) && Qeq_bool (qm12 m) (qm21 m)))
  && negb (Qeq_bool (qm11 m * qm11 m + qm21 m * qm21 m) 0).

Lemma is_similarity_qb_iff : forall m, is_similarity_qb m = true <-> is_similarity_q m.
Proof.
  intro m. unfold is_similarity_qb, is_similarity_q.
  rewrite andb_true_iff, orb_true_iff, !andb_true_iff, negb_true_iff, !Qeq_bool_iff.
  split.
  - intros [H Hn]. split; [exact H|]. intro H0.
    apply Qeq_bool_iff in H0. rewrite H0 in Hn. discriminate.
  - intros [H Hn]. split; [exact H|].
    destruct (Qeq_bool _ _) eqn:E; [|reflexivity].
    apply Qeq_bool_iff in E. contradiction.
Qed.

Definition is_similarity_q_dec (m : QAff) : {is_similarity_q m} + {~ is_similarity_q m} :=
  match is_similarity_qb m as b return is_similarity_qb m = b -> _ with
  | true => fun H => left (proj1 (is_similarity_qb_iff m) H)
  | false => fun H => right (fun P =>
      diff_false_true (eq_trans (eq_sym H) (proj2 (is_similarity_qb_iff m) P)))
  end eq_refl.

(* The similarity a rational affine map denotes once it passes the test. *)
Definition sim_of_qaff (m : QAff) : Sim2 :=
  mkSim2 (Q2R (qm11 m)) (Q2R (qm21 m)) (Q2R (qtx m)) (Q2R (qty m))
         (negb (Qeq_bool (qm11 m) (qm22 m) && Qeq_bool (qm12 m) (- qm21 m))).

Lemma map_arc_ext : forall f g a, (forall p, f p = g p) -> map_arc f a = map_arc g a.
Proof. intros f g a H. unfold map_arc. rewrite !H. reflexivity. Qed.

Lemma qaff_R_sim : forall m, is_similarity_q m ->
  sim_k2 (sim_of_qaff m) <> 0 /\ forall p, qaff_R m p = sim_apply (sim_of_qaff m) p.
Proof.
  intros m [Hs Hn]. split.
  - unfold sim_k2, sim_of_qaff. cbn [sim_a sim_b].
    rewrite <- !Q2R_mult, <- Q2R_plus. intro H. apply Hn. apply eqR_Qeq.
    rewrite H, RMicromega.Q2R_0. reflexivity.
  - intro p. unfold qaff_R, sim_apply, sim_of_qaff. cbn [sim_a sim_b sim_tx sim_ty sim_refl].
    destruct (Qeq_bool (qm11 m) (qm22 m) && Qeq_bool (qm12 m) (- qm21 m)) eqn:E;
      cbn [negb].
    + apply andb_true_iff in E. destruct E as [E1 E2].
      apply Qeq_bool_iff, Qeq_eqR in E1. apply Qeq_bool_iff, Qeq_eqR in E2.
      rewrite Q2R_opp in E2. rewrite E2, <- E1. f_equal; ring.
    + destruct Hs as [[E1 E2] | [E3 E4]].
      * apply Qeq_bool_iff in E1. apply Qeq_bool_iff in E2. rewrite E1, E2 in E.
        discriminate.
      * apply Qeq_eqR in E3. apply Qeq_eqR in E4. rewrite Q2R_opp in E3.
        rewrite E4. replace (Q2R (qm22 m)) with (- Q2R (qm11 m)) by lra.
        f_equal; ring.
Qed.

Lemma qaff_similarity_on_arc_iff : forall m, is_similarity_q m ->
  forall a X, on_arc a X <-> on_arc (map_arc (qaff_R m) a) (qaff_R m X).
Proof.
  intros m Hm a X. destruct (qaff_R_sim m Hm) as [Hk He].
  rewrite (map_arc_ext _ _ a He), He. apply sim_on_arc_iff. exact Hk.
Qed.

Theorem arc_similarity_supporting : ArcSimilarityStmt.supporting.
Proof. exact qaff_similarity_on_arc_iff. Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The non-similarity witness: scale (2,1) on the unit upper arc.          *)
(* -------------------------------------------------------------------------- *)

Definition scale21 : QAff := mkQAff 2 0 0 1 0 0.

Lemma scale21_not_similarity : ~ is_similarity_q scale21.
Proof. intro H. apply is_similarity_qb_iff in H. vm_compute in H. discriminate. Qed.

Definition unit_upper_arc : CircularArc :=
  mkCircularArc (mkPoint 1 0) (mkPoint 0 1) (mkPoint (-1) 0).
Definition upper_pt35 : Point := mkPoint (3/5) (4/5).

Lemma scale21_unit_arc_fixtures :
  valid_arc unit_upper_arc /\ on_arc unit_upper_arc upper_pt35 /\
  ~ on_arc (map_arc (qaff_R scale21) unit_upper_arc) (qaff_R scale21 upper_pt35).
Proof.
  assert (H2 : Q2R 2 = 2) by exact Q2R_2.
  assert (H1 : Q2R 1 = 1) by exact RMicromega.Q2R_1.
  assert (H0 : Q2R 0 = 0) by exact RMicromega.Q2R_0.
  unfold valid_arc, on_arc, arc_span_contains, arc_interior_side, arc_side_chord,
    cross_R_pt, inCircle_R, map_arc, qaff_R, unit_upper_arc, upper_pt35, scale21.
  cbn [arc_start arc_mid arc_end px py qm11 qm12 qm21 qm22 qtx qty].
  rewrite H2, H1, H0. split; [lra|]. split.
  - split; [field | left; lra].
  - intros [Hi _]. field_simplify in Hi. lra.
Qed.

Theorem arc_similarity_witness : ArcSimilarityStmt.witness.
Proof.
  exists scale21, unit_upper_arc, upper_pt35.
  destruct scale21_unit_arc_fixtures as [Hv [Ho Hn]].
  exact (conj scale21_not_similarity (conj Hv (conj Ho Hn))).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Q twin: the residual is computed from the controls, never pinned.       *)
(* -------------------------------------------------------------------------- *)

Local Open Scope Q_scope.

Definition qaff_q (m : QAff) (p : QPt) : QPt :=
  mkQPt (qm11 m * qx p + qm12 m * qy p + qtx m) (qm21 m * qx p + qm22 m * qy p + qty m).

(* |X - O|^2 - |A - O|^2 for O the circumcentre of (A, M, C). *)
Definition q_circ_resid (A M C X : QPt) : Q :=
  let ox := qOx A M C in let oy := qOy A M C in
  ((qx X - ox) * (qx X - ox) + (qy X - oy) * (qy X - oy))
  - ((qx A - ox) * (qx A - ox) + (qy A - oy) * (qy A - oy)).

Definition q_upA : QPt := mkQPt 1 0.
Definition q_upM : QPt := mkQPt 0 1.
Definition q_upC : QPt := mkQPt (-1) 0.
Definition q_pt35 : QPt := mkQPt (3#5) (4#5).

Local Close Scope Q_scope.

Lemma qaff_q_R : forall m p, qpt_R (qaff_q m p) = qaff_R m (qpt_R p).
Proof. intros m p. unfold qaff_q, qaff_R, qpt_R. cbn [qx qy px py]. push_Q2R. reflexivity. Qed.

Lemma q_circ_resid_R : forall A M C X, ~ (qarc_D A M C == 0)%Q ->
  Q2R (q_circ_resid A M C X)
  = dist_sq (qpt_R X) (arc_center (arc_of A M C))
    - dist_sq (qpt_R A) (arc_center (arc_of A M C)).
Proof.
  intros A M C X HD. destruct (center_Q2R A M C HD) as [Ex Ey].
  unfold q_circ_resid, dist_sq. cbv zeta. push_Q2R. rewrite Ex, Ey.
  unfold qpt_R. cbn [px py]. reflexivity.
Qed.

(* Control arc: residual 0 at the arc point.  Scaled arc: residual 12/25. *)
Lemma unit_arc_resid_fixtures :
  (q_circ_resid q_upA q_upM q_upC q_pt35 == 0)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma scale21_unit_arc_resid_fixtures :
  (q_circ_resid (qaff_q scale21 q_upA) (qaff_q scale21 q_upM) (qaff_q scale21 q_upC)
                (qaff_q scale21 q_pt35) == 12 # 25)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma scale21_unit_arc_resid_neq :
  ~ (q_circ_resid (qaff_q scale21 q_upA) (qaff_q scale21 q_upM) (qaff_q scale21 q_upC)
                  (qaff_q scale21 q_pt35) == 0)%Q.
Proof. rewrite scale21_unit_arc_resid_fixtures. vm_compute. discriminate. Qed.

Lemma scale21_arc_D_neq : ~ (qarc_D (qaff_q scale21 q_upA) (qaff_q scale21 q_upM)
                                    (qaff_q scale21 q_upC) == 0)%Q.
Proof. vm_compute. discriminate. Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The (2,1) residual over the whole arc: 3 y (1 - y), maximum 3/4.       *)
(*     12/25 above is its value at the one point (3/5, 4/5), not the max.    *)
(* -------------------------------------------------------------------------- *)

Definition scale21_image_arc : CircularArc := map_arc (qaff_R scale21) unit_upper_arc.

(* |f X - O'|^2 - |f A - O'|^2, with O' the centre of the image arc. *)
Definition scale21_resid (X : Point) : R :=
  dist_sq (qaff_R scale21 X) (arc_center scale21_image_arc)
  - dist_sq (arc_start scale21_image_arc) (arc_center scale21_image_arc).

Definition upper_pt_half : Point := mkPoint (sqrt 3 / 2) (1 / 2).

Lemma scale21_qaff_R : forall X, qaff_R scale21 X = mkPoint (2 * px X) (py X).
Proof.
  intros X. unfold qaff_R, scale21. cbn [qm11 qm12 qm21 qm22 qtx qty].
  rewrite Q2R_2, RMicromega.Q2R_1, RMicromega.Q2R_0. f_equal; ring.
Qed.

Lemma scale21_image_center : arc_center scale21_image_arc = mkPoint 0 (-3 / 2).
Proof.
  unfold scale21_image_arc, map_arc. rewrite !scale21_qaff_R.
  unfold arc_center, unit_upper_arc. cbn [arc_start arc_mid arc_end px py].
  f_equal; field.
Qed.

Lemma scale21_resid_formula : forall X,
  px X * px X + py X * py X = 1 -> scale21_resid X = 3 * py X * (1 - py X).
Proof.
  intros [x y] Hc. cbn [px py] in Hc. unfold scale21_resid.
  rewrite scale21_image_center. unfold scale21_image_arc, map_arc.
  rewrite !scale21_qaff_R. unfold dist_sq, unit_upper_arc.
  cbn [arc_start px py]. nra.
Qed.

Lemma unit_upper_arc_on : forall X, on_arc unit_upper_arc X ->
  px X * px X + py X * py X = 1 /\ 0 <= py X.
Proof.
  intros [x y] [Hc Hs].
  unfold inCircle_R, unit_upper_arc in Hc. cbn [arc_start arc_mid arc_end px py] in Hc.
  split; [cbn [px py]; nra|].
  destruct Hs as [Hi | [He | He]].
  - unfold arc_interior_side, arc_side_chord, cross_R_pt, unit_upper_arc in Hi.
    cbn [arc_start arc_mid arc_end px py] in Hi. cbn [py]. nra.
  - unfold unit_upper_arc in He. cbn [arc_start] in He. inversion He. cbn [py]. lra.
  - unfold unit_upper_arc in He. cbn [arc_end] in He. inversion He. cbn [py]. lra.
Qed.

Theorem scale21_resid_max :
  (forall X, on_arc unit_upper_arc X -> 0 <= scale21_resid X <= 3 / 4) /\
  on_arc unit_upper_arc upper_pt_half /\ scale21_resid upper_pt_half = 3 / 4.
Proof.
  assert (Hs3 : sqrt 3 * sqrt 3 = 3) by (apply sqrt_sqrt; lra).
  assert (Hon : on_arc unit_upper_arc upper_pt_half).
  { split.
    - unfold inCircle_R, unit_upper_arc, upper_pt_half.
      cbn [arc_start arc_mid arc_end px py]. nra.
    - left. unfold arc_interior_side, arc_side_chord, cross_R_pt, unit_upper_arc, upper_pt_half.
      cbn [arc_start arc_mid arc_end px py]. lra. }
  split; [|split; [exact Hon|]].
  - intros X HX. destruct (unit_upper_arc_on X HX) as [Hc Hy].
    rewrite (scale21_resid_formula X Hc).
    pose proof (Rle_0_sqr (px X)) as Hx2. pose proof (Rle_0_sqr (py X - 1 / 2)) as Hh.
    unfold Rsqr in Hx2, Hh.
    assert (Hy1 : py X <= 1) by nra.
    split; [apply Rmult_le_pos; lra | nra].
  - rewrite scale21_resid_formula.
    + unfold upper_pt_half. cbn [py]. field.
    + unfold upper_pt_half. cbn [px py]. nra.
Qed.

(* The Q sample, now an R theorem about the image arc's own centre. *)
Lemma scale21_resid_pt35_fixtures :
  scale21_resid upper_pt35 = 12 / 25 /\
  Q2R (q_circ_resid (qaff_q scale21 q_upA) (qaff_q scale21 q_upM)
                    (qaff_q scale21 q_upC) (qaff_q scale21 q_pt35)) = 12 / 25.
Proof.
  split.
  - rewrite scale21_resid_formula; unfold upper_pt35; cbn [px py]; field.
  - rewrite scale21_unit_arc_resid_fixtures. unfold Q2R. cbn. field.
Qed.

Print Assumptions sim_sign_sq.
Print Assumptions sim_dist_sq.
Print Assumptions sim_cross.
Print Assumptions sim_incircle.
Print Assumptions sim_k2_nonneg.
Print Assumptions sim_sign_k2_neq.
Print Assumptions sim_injective.
Print Assumptions valid_arc_cross.
Print Assumptions sim_valid_arc.
Print Assumptions sim_arc_center.
Print Assumptions sim_arc_radius.
Print Assumptions sim_on_arc_iff.
Print Assumptions arc_similarity_claim.
Print Assumptions is_similarity_qb_iff.
Print Assumptions is_similarity_q_dec.
Print Assumptions map_arc_ext.
Print Assumptions qaff_R_sim.
Print Assumptions qaff_similarity_on_arc_iff.
Print Assumptions arc_similarity_supporting.
Print Assumptions scale21_not_similarity.
Print Assumptions scale21_unit_arc_fixtures.
Print Assumptions arc_similarity_witness.
Print Assumptions qaff_q_R.
Print Assumptions q_circ_resid_R.
Print Assumptions unit_arc_resid_fixtures.
Print Assumptions scale21_unit_arc_resid_fixtures.
Print Assumptions scale21_unit_arc_resid_neq.
Print Assumptions scale21_arc_D_neq.
Print Assumptions scale21_qaff_R.
Print Assumptions scale21_image_center.
Print Assumptions scale21_resid_formula.
Print Assumptions unit_upper_arc_on.
Print Assumptions scale21_resid_max.
Print Assumptions scale21_resid_pt35_fixtures.
