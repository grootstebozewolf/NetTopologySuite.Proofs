(* NetTopologySuite.Proofs.TinSurfaceTopo
   Metric interior and boundary of a TIN carrier.
   interior_pt is a ball inside the carrier. boundary_pt meets the
   carrier and its complement in every ball.
   An open cell and a shared-edge relative interior are interior
   points. A once-edge is boundary.
   The internal-vertex case and the equalities with tin_int_cells /
   tin_bd_cells are TinSurfaceVertex.
   Fixtures: strip_shared_interior_fixtures,
   bowtie_vertex_boundary_fixtures, hole_boundary_fixtures.
   topic: relate
   claimId: tri-de9im-t4
   witness: TinSurfaceVertex.tin_interior_eq
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7).
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra Lia List Bool PeanoNat.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex ConvexClip
  TrianglePairCommon TrianglePairEdge TrianglePairBound
  TrianglePairExterior TrianglePairTin TrianglePairTinSurface.
Local Open Scope R_scope.
Definition interior_pt (S : Point -> Prop) (X : Point) : Prop :=
  exists r, 0 < r /\ forall Y, dist X Y < r -> S Y.
Definition boundary_pt (S : Point -> Prop) (X : Point) : Prop :=
  forall r, 0 < r ->
    (exists Y, dist X Y < r /\ S Y) /\
    (exists Y, dist X Y < r /\ ~ S Y).
Lemma interior_in : forall S X, interior_pt S X -> S X.
Proof.
  intros S X [r [Hr HS]]. apply HS. rewrite dist_refl. exact Hr.
Qed.
Lemma interior_not_boundary : forall S X,
  interior_pt S X -> ~ boundary_pt S X.
Proof.
  intros S X [r [Hr Hin]] Hb.
  destruct (Hb r Hr) as [_ [Y [Hd Hout]]].
  apply Hout. apply Hin. exact Hd.
Qed.
Lemma cross_diff : forall P Q X Y,
  cross P Q Y - cross P Q X =
    (px Q - px P) * (py Y - py X) - (px Y - px X) * (py Q - py P).
Proof. intros. unfold cross. ring. Qed.
Lemma cross_rev : forall P Q X, cross Q P X = - cross P Q X.
Proof. intros. unfold cross. ring. Qed.
Lemma abs_dx_le_dist : forall X Y, Rabs (px Y - px X) <= dist X Y.
Proof.
  intros X Y. apply Rsqr_incr_0.
  - rewrite <- Rsqr_abs. unfold Rsqr. rewrite dist_mul_self.
    unfold dist_sq.
    replace ((px Y - px X) * (px Y - px X))
      with ((px X - px Y) * (px X - px Y)) by ring.
    rewrite <- Rplus_0_r at 1. apply Rplus_le_compat_l. apply sqr_nonneg.
  - apply Rabs_pos.
  - apply dist_nonneg.
Qed.
Lemma abs_dy_le_dist : forall X Y, Rabs (py Y - py X) <= dist X Y.
Proof.
  intros X Y. apply Rsqr_incr_0.
  - rewrite <- Rsqr_abs. unfold Rsqr. rewrite dist_mul_self.
    unfold dist_sq. rewrite Rplus_comm.
    replace ((py Y - py X) * (py Y - py X))
      with ((py X - py Y) * (py X - py Y)) by ring.
    rewrite <- Rplus_0_r at 1. apply Rplus_le_compat_l. apply sqr_nonneg.
  - apply Rabs_pos.
  - apply dist_nonneg.
Qed.
Lemma cross_lip : forall P Q X Y,
  Rabs (cross P Q Y - cross P Q X) <=
    (Rabs (px Q - px P) + Rabs (py Q - py P)) * dist X Y.
Proof.
  intros P Q X Y. rewrite cross_diff.
  set (a := px Q - px P). set (b := py Q - py P).
  set (dx := px Y - px X). set (dy := py Y - py X).
  apply Rle_trans with (Rabs (a * dy) + Rabs (dx * b)).
  - replace (a * dy - dx * b) with (a * dy + - (dx * b)) by ring.
    apply Rle_trans with (Rabs (a * dy) + Rabs (- (dx * b))).
    + apply Rabs_triang.
    + rewrite Rabs_Ropp. apply Rle_refl.
  - rewrite !Rabs_mult.
    replace ((Rabs a + Rabs b) * dist X Y)
      with (Rabs a * dist X Y + dist X Y * Rabs b) by ring.
    apply Rplus_le_compat.
    + apply Rmult_le_compat_l; [apply Rabs_pos | apply abs_dy_le_dist].
    + apply Rmult_le_compat_r; [apply Rabs_pos | apply abs_dx_le_dist].
Qed.
Lemma neg_abs_le : forall d, - Rabs d <= d.
Proof.
  intros d. destruct (Rle_dec 0 d) as [Hd|Hd].
  - rewrite (Rabs_right d (Rle_ge _ _ Hd)). lra.
  - apply Rnot_le_lt in Hd. rewrite (Rabs_left d Hd). lra.
Qed.
Lemma below_abs : forall x d, x - Rabs d <= x + d.
Proof.
  intros x d. apply Rplus_le_compat_l. apply neg_abs_le.
Qed.
Lemma slack_ball : forall P Q X,
  0 < cross P Q X ->
  exists r, 0 < r /\ forall Y, dist X Y < r -> 0 < cross P Q Y.
Proof.
  intros P Q X Hs.
  set (K := Rabs (px Q - px P) + Rabs (py Q - py P)).
  set (r := cross P Q X / (2 * (K + 1))).
  assert (HK0 : 0 <= K).
  { unfold K. apply Rplus_le_le_0_compat; apply Rabs_pos. }
  assert (Hden : 0 < 2 * (K + 1)) by lra.
  assert (Hr : 0 < r).
  { unfold r. apply Rdiv_lt_0_compat; assumption. }
  exists r. split; [exact Hr|]. intros Y HY.
  assert (Hlip : Rabs (cross P Q Y - cross P Q X) <= K * dist X Y)
    by apply cross_lip.
  assert (Hhalf : K * dist X Y < cross P Q X / 2).
  { destruct (Req_EM_T K 0) as [HK|HK].
    - rewrite HK. rewrite Rmult_0_l.
      apply Rdiv_lt_0_compat; lra.
    - assert (0 < K) by lra.
      apply Rle_lt_trans with (r2 := K * r).
      + apply Rmult_le_compat_l; [apply Rlt_le; exact H | apply Rlt_le; exact HY].
      + unfold r.
        replace (K * (cross P Q X / (2 * (K + 1))))
          with (K / (K + 1) * (cross P Q X / 2)) by (field; lra).
        assert (K / (K + 1) < 1).
        { apply Rmult_lt_reg_r with (r := K + 1); [lra|].
          unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
          rewrite Rmult_1_l, Rmult_1_r. lra. }
        apply Rlt_le_trans with (1 * (cross P Q X / 2)).
        * apply Rmult_lt_compat_r; [apply Rdiv_lt_0_compat; lra | exact H0].
        * rewrite Rmult_1_l. apply Rle_refl. }
  assert (Hdrop : cross P Q X - K * dist X Y <=
                  cross P Q X - Rabs (cross P Q Y - cross P Q X)).
  { apply Rplus_le_compat_l. apply Ropp_le_contravar. exact Hlip. }
  assert (Hback : cross P Q X - Rabs (cross P Q Y - cross P Q X) <=
                   cross P Q X + (cross P Q Y - cross P Q X))
    by apply below_abs.
  replace (cross P Q X + (cross P Q Y - cross P Q X))
    with (cross P Q Y) in Hback by ring.
  assert (Hpos : 0 < cross P Q X - K * dist X Y) by lra.
  lra.
Qed.
Lemma neg_cross_ball : forall P Q X,
  cross P Q X < 0 ->
  exists r, 0 < r /\ forall Y, dist X Y < r -> cross P Q Y < 0.
Proof.
  intros P Q X Hs.
  assert (Hp : 0 < cross Q P X).
  { rewrite cross_rev. lra. }
  destruct (slack_ball Q P X Hp) as [r [Hr HY]].
  exists r. split; [exact Hr|]. intros Y HD.
  assert (0 < cross Q P Y) by (apply HY; exact HD).
  rewrite cross_rev in H. lra.
Qed.
Lemma open_nbhd : forall A B C X,
  tri_open A B C X ->
  exists r, 0 < r /\ forall Y, dist X Y < r -> tri_open A B C Y.
Proof.
  intros A B C X [Hab [Hbc Hca]].
  destruct (slack_ball A B X Hab) as [r1 [H1 P1]].
  destruct (slack_ball B C X Hbc) as [r2 [H2 P2]].
  destruct (slack_ball C A X Hca) as [r3 [H3 P3]].
  exists (Rmin r1 (Rmin r2 r3)). split.
  - apply Rmin_pos; [exact H1 | apply Rmin_pos; assumption].
  - intros Y HY. repeat split.
    + apply P1. eapply Rlt_le_trans; [exact HY | apply Rmin_l].
    + apply P2. eapply Rlt_le_trans; [exact HY|].
      eapply Rle_trans; [apply Rmin_r | apply Rmin_l].
    + apply P3. eapply Rlt_le_trans; [exact HY|].
      eapply Rle_trans; [apply Rmin_r | apply Rmin_r].
Qed.
Lemma tri_open_in : forall A B C X,
  0 < cross A B C -> tri_open A B C X -> in_tri A B C X.
Proof.
  intros A B C X Hd [Hab [Hbc Hca]].
  apply (proj1 (tri_slack_hull A B C X Hd)).
  split; [apply Rlt_le; exact Hab|].
  split; apply Rlt_le; assumption.
Qed.
Lemma open_tri_interior : forall ts A B C X,
  In (((A, B), C) : Tri) ts -> tri_open A B C X ->
  interior_pt (tin_carrier ts) X.
Proof.
  intros ts A B C X Hin Ho.
  destruct (open_nbhd A B C X Ho) as [r [Hr HY]].
  exists r. split; [exact Hr|]. intros Y Hd.
  exists ((A, B), C). split; [exact Hin|]. left. apply HY. exact Hd.
Qed.
Lemma out_nbhd : forall A B C X,
  0 < cross A B C -> ~ in_tri A B C X ->
  exists r, 0 < r /\ forall Y, dist X Y < r -> ~ in_tri A B C Y.
Proof.
  intros A B C X Hd Hout.
  assert (Hneg : cross A B X < 0 \/ cross B C X < 0 \/ cross C A X < 0).
  { destruct (Rle_dec 0 (cross A B X)) as [Hab|Hab];
    destruct (Rle_dec 0 (cross B C X)) as [Hbc|Hbc];
    destruct (Rle_dec 0 (cross C A X)) as [Hca|Hca].
    - exfalso. apply Hout. apply (proj1 (tri_slack_hull A B C X Hd)).
      split; [exact Hab|]. split; assumption.
    - right. right. apply Rnot_le_lt. exact Hca.
    - right. left. apply Rnot_le_lt. exact Hbc.
    - right. left. apply Rnot_le_lt. exact Hbc.
    - left. apply Rnot_le_lt. exact Hab.
    - left. apply Rnot_le_lt. exact Hab.
    - left. apply Rnot_le_lt. exact Hab.
    - left. apply Rnot_le_lt. exact Hab. }
  destruct Hneg as [H|H].
  - destruct (neg_cross_ball A B X H) as [r [Hr HY]].
    exists r. split; [exact Hr|]. intros Y HD Hin.
    assert (Hc : cross A B Y < 0) by (apply HY; exact HD).
    destruct (proj2 (tri_slack_hull A B C Y Hd) Hin) as [Hab _]. lra.
  - destruct H as [H|H].
    + destruct (neg_cross_ball B C X H) as [r [Hr HY]].
      exists r. split; [exact Hr|]. intros Y HD Hin.
      assert (Hc : cross B C Y < 0) by (apply HY; exact HD).
      destruct (proj2 (tri_slack_hull A B C Y Hd) Hin) as [_ [Hbc _]]. lra.
    + destruct (neg_cross_ball C A X H) as [r [Hr HY]].
      exists r. split; [exact Hr|]. intros Y HD Hin.
      assert (Hc : cross C A Y < 0) by (apply HY; exact HD).
      destruct (proj2 (tri_slack_hull A B C Y Hd) Hin) as [_ [_ Hca]]. lra.
Qed.
Lemma piece_miss : forall A B C X,
  0 < cross A B C -> ~ (tri_open A B C X \/ on_bd A B C X) ->
  exists r, 0 < r /\ forall Y, dist X Y < r ->
    ~ (tri_open A B C Y \/ on_bd A B C Y).
Proof.
  intros A B C X Hd Hout.
  assert (Hnin : ~ in_tri A B C X).
  { intros Hin. apply Hout. apply in_tri_open_or_bd; assumption. }
  destruct (out_nbhd A B C X Hd Hnin) as [r [Hr HY]].
  exists r. split; [exact Hr|]. intros Y HD [Ho|Hb].
  - apply (HY Y HD). apply tri_open_in; assumption.
  - apply (HY Y HD). apply on_bd_in_tri. exact Hb.
Qed.
Lemma carrier_complement_open : forall ts X,
  (forall T, In T ts -> tri_pos T) ->
  ~ tin_carrier ts X ->
  exists r, 0 < r /\ forall Y, dist X Y < r -> ~ tin_carrier ts Y.
Proof.
  induction ts as [|T rest IH]; intros X Hpos Hout.
  - exists 1. split; [lra|]. intros Y _ [U [[] _]].
  - assert (Hposr : forall U, In U rest -> tri_pos U).
    { intros U HU. apply Hpos. right. exact HU. }
    assert (Hhead : ~ (open_of T X \/ bd_of T X)).
    { intros Hp. apply Hout. exists T. split; [left; reflexivity|]. exact Hp. }
    assert (Hrest : ~ tin_carrier rest X).
    { intros [U [Hin Hp]]. apply Hout. exists U. split; [right; exact Hin|]. exact Hp. }
    destruct (IH X Hposr Hrest) as [rr [Hrr Pr]].
    destruct T as [[A B] C].
    assert (Hd0 : tri_pos ((A, B), C)).
    { apply Hpos. left. reflexivity. }
    simpl in Hd0.
    destruct (piece_miss A B C X Hd0 Hhead) as [rh [Hrh Ph]].
    exists (Rmin rh rr). split.
    + apply Rmin_pos; assumption.
    + intros Y HY [U [Hin Hp]].
      destruct Hin as [Heq|Hin].
      * subst U. apply (Ph Y).
        -- eapply Rlt_le_trans; [exact HY | apply Rmin_l].
        -- exact Hp.
      * apply (Pr Y).
        -- eapply Rlt_le_trans; [exact HY | apply Rmin_r].
        -- exists U. split; assumption.
Qed.
Lemma piece_dec : forall A B C X,
  {tri_open A B C X \/ on_bd A B C X} +
  {~ (tri_open A B C X \/ on_bd A B C X)}.
Proof.
  intros A B C X.
  destruct (tri_open_b A B C X) eqn:Ho.
  - left. left. apply tri_open_b_true. exact Ho.
  - destruct (on_seg_b A B X || on_seg_b B C X || on_seg_b C A X) eqn:Hb.
    + left. right.
      apply orb_true_iff in Hb. destruct Hb as [Hb|Hc].
      * apply orb_true_iff in Hb. destruct Hb as [Ha|Hb'].
        -- left. apply on_seg_b_iff. exact Ha.
        -- right. left. apply on_seg_b_iff. exact Hb'.
      * right. right. apply on_seg_b_iff. exact Hc.
    + right. intros [Ho'|Hb'].
      * apply tri_open_b_true in Ho'. rewrite Ho in Ho'. discriminate.
      * assert (Htrue : on_seg_b A B X || on_seg_b B C X || on_seg_b C A X = true).
        { destruct Hb' as [Hs|[Hs|Hs]].
          - apply on_seg_b_iff in Hs.
            apply orb_true_iff. left. apply orb_true_iff. left. exact Hs.
          - apply on_seg_b_iff in Hs.
            apply orb_true_iff. left. apply orb_true_iff. right. exact Hs.
          - apply on_seg_b_iff in Hs.
            apply orb_true_iff. right. exact Hs. }
        congruence.
Qed.
Lemma carrier_dec : forall ts X,
  {tin_carrier ts X} + {~ tin_carrier ts X}.
Proof.
  induction ts as [|T rest IH]; intros X.
  - right. intros [U [[] _]].
  - destruct (IH X) as [Hin|Hout].
    + left. destruct Hin as [U [Hi Hp]].
      exists U. split; [right; exact Hi| exact Hp].
    + destruct T as [[A B] C].
      destruct (piece_dec A B C X) as [Hp|Hn].
      * left. exists ((A, B), C). split; [left; reflexivity | exact Hp].
      * right. intros [U [Hi Hp0]].
        destruct Hi as [Heq|Hi].
        -- rewrite <- Heq in Hp0. apply Hn. exact Hp0.
        -- apply Hout. exists U. split; assumption.
Qed.
Lemma boundary_in_carrier : forall ts X,
  (forall T, In T ts -> tri_pos T) ->
  boundary_pt (tin_carrier ts) X -> tin_carrier ts X.
Proof.
  intros ts X Hpos Hb.
  destruct (carrier_dec ts X) as [Hin|Hout].
  - exact Hin.
  - destruct (carrier_complement_open ts X Hpos Hout) as [r [Hr Hmiss]].
    destruct (Hb r Hr) as [[Y [Hd HinY]] _].
    exfalso. apply (Hmiss Y Hd). exact HinY.
Qed.
Lemma relint_side : forall A B C X,
  0 < cross A B C -> on_seg_open A B X ->
  cross A B X = 0 /\ 0 < cross B C X /\ 0 < cross C A X.
Proof.
  intros A B C X Hd [t [Ht ->]].
  split.
  - apply cross_combo0.
  - rewrite !cross_combo.
    assert (HBB : cross B C B = 0) by apply cross_at_P0_is_collinear.
    assert (HBA : cross B C A = cross A B C) by (symmetry; apply cross_cycle).
    assert (HAA : cross C A A = 0) by (unfold cross; ring).
    assert (HAB : cross C A B = cross A B C) by (symmetry; apply cross_cycle2).
    rewrite HBB, HBA, HAA, HAB.
    split.
    + replace ((1 - t) * cross A B C + t * 0)
        with ((1 - t) * cross A B C) by ring.
      apply Rmult_lt_0_compat; lra.
    + replace ((1 - t) * 0 + t * cross A B C)
        with (t * cross A B C) by ring.
      apply Rmult_lt_0_compat; lra.
Qed.
Lemma seg_t_combo : forall A B t,
  0 < dist_sq B A ->
  seg_t A B (convex_combination A B t) = t.
Proof.
  intros [ax ay] [bx by_] t Hd.
  unfold seg_t, dot, vsub, convex_combination, dist_sq in *. simpl in *.
  assert (Hd0 : (bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay) <> 0) by lra.
  field. exact Hd0.
Qed.
Lemma dot_disp_bound : forall X Y A B,
  Rabs (dot (vsub Y X) (vsub B A)) <=
    (Rabs (px B - px A) + Rabs (py B - py A)) * dist X Y.
Proof.
  intros X Y A B.
  unfold dot, vsub. simpl.
  apply Rle_trans with
    (Rabs ((px Y - px X) * (px B - px A)) +
     Rabs ((py Y - py X) * (py B - py A))).
  - apply Rabs_triang.
  - rewrite !Rabs_mult.
    set (K := Rabs (px B - px A) + Rabs (py B - py A)).
    replace (K * dist X Y)
      with (Rabs (px B - px A) * dist X Y +
            Rabs (py B - py A) * dist X Y) by (unfold K; ring).
    apply Rplus_le_compat.
    + rewrite Rmult_comm. apply Rmult_le_compat_l.
      * apply Rabs_pos.
      * apply abs_dx_le_dist.
    + rewrite Rmult_comm. apply Rmult_le_compat_l.
      * apply Rabs_pos.
      * apply abs_dy_le_dist.
Qed.
Lemma frac_lt_one : forall K, 0 < K -> K / (K + 1) < 1.
Proof.
  intros K HK. apply Rmult_lt_reg_r with (r := K + 1); [lra|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
  rewrite Rmult_1_l, Rmult_1_r. lra.
Qed.
Lemma step_lt : forall rad base,
  0 < rad -> 0 < base -> rad / (2 * (base + 1)) * base < rad.
Proof.
  intros rad base Hr Hb.
  replace (rad / (2 * (base + 1)) * base)
    with ((base / (base + 1)) * (rad / 2)) by (field; lra).
  assert (Hf : base / (base + 1) < 1) by (apply frac_lt_one; exact Hb).
  replace (rad / 2) with (1 * (rad / 2)) at 2 by ring.
  apply Rlt_trans with (1 * (rad / 2)); [| lra].
  apply Rmult_lt_compat_r; [lra | exact Hf].
Qed.
Lemma on_line_near : forall A B X t Y,
  0 < t < 1 -> X = convex_combination A B t ->
  0 < dist_sq B A -> cross A B Y = 0 ->
  let K := Rabs (px B - px A) + Rabs (py B - py A) in
  dist X Y < Rmin t (1 - t) * dist_sq B A / (2 * (K + 1)) ->
  on_seg_open A B Y.
Proof.
  intros A B X t Y Ht HX Hd Hz K Hdist.
  assert (HK : 0 <= K) by (unfold K; apply Rplus_le_le_0_compat; apply Rabs_pos).
  assert (Hden2 : 0 < 2 * (K + 1)) by lra.
  set (gap := Rmin t (1 - t)).
  assert (Hgap : 0 < gap) by (unfold gap; apply Rmin_pos; lra).
  assert (HsX : seg_t A B X = t) by (rewrite HX; apply seg_t_combo; exact Hd).
  assert (Hsub : dot (vsub Y A) (vsub B A) - dot (vsub X A) (vsub B A)
                 = dot (vsub Y X) (vsub B A)).
  { unfold dot, vsub. simpl. ring. }
  assert (Hdiff : seg_t A B Y - seg_t A B X =
                  dot (vsub Y X) (vsub B A) / dist_sq B A).
  { unfold seg_t. rewrite <- Hsub. field. lra. }
  assert (Habs : Rabs (seg_t A B Y - t) <= K * dist X Y / dist_sq B A).
  { rewrite <- HsX. rewrite Hdiff. unfold Rdiv. rewrite Rabs_mult.
    rewrite Rabs_inv by lra.
    rewrite (Rabs_right (dist_sq B A)) by (apply Rle_ge; apply Rlt_le; exact Hd).
    apply Rmult_le_compat_r.
    - apply Rlt_le. apply Rinv_0_lt_compat. exact Hd.
    - apply dot_disp_bound. }
  assert (Hsmall : K * dist X Y / dist_sq B A < gap).
  { destruct (Req_EM_T K 0) as [HK0|HK0].
    - rewrite HK0. unfold Rdiv. rewrite Rmult_0_l, Rmult_0_l. exact Hgap.
    - assert (HKp : 0 < K) by lra.
      apply Rmult_lt_reg_r with (r := dist_sq B A); [exact Hd|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
      apply Rlt_trans with
        (r2 := K * (gap * dist_sq B A / (2 * (K + 1)))).
      + apply Rmult_lt_compat_l; [exact HKp | exact Hdist].
      + replace (K * (gap * dist_sq B A / (2 * (K + 1))))
          with ((K / (K + 1)) * (gap / 2) * dist_sq B A) by (field; lra).
        apply Rlt_le_trans with ((gap / 2) * dist_sq B A).
        * apply Rmult_lt_compat_r; [exact Hd|].
          replace (gap / 2) with (1 * (gap / 2)) at 2 by ring.
          apply Rmult_lt_compat_r; [lra | apply frac_lt_one; exact HKp].
        * apply Rmult_le_compat_r; [apply Rlt_le; exact Hd|].
          lra. }
  assert (Hband : Rabs (seg_t A B Y - t) < gap).
  { eapply Rle_lt_trans; [exact Habs | exact Hsmall]. }
  destruct (Rabs_def2 _ _ Hband) as [Hhi Hlo].
  assert (HY2 : Y = convex_combination A B (seg_t A B Y)).
  { apply on_line_combo; [exact Hd | exact Hz]. }
  exists (seg_t A B Y). split; [| exact HY2].
  assert (Hle1 : gap <= t) by (unfold gap; apply Rmin_l).
  assert (Hle2 : gap <= 1 - t) by (unfold gap; apply Rmin_r).
  split; lra.
Qed.
Definition left_nudge (P Q X : Point) (t : R) : Point :=
  mkPoint (px X - t * (py Q - py P)) (py X + t * (px Q - px P)).
Lemma nudge_cross : forall P Q X t,
  cross P Q (left_nudge P Q X t) = cross P Q X + t * dist_sq Q P.
Proof. intros. unfold cross, left_nudge, dist_sq. simpl. ring. Qed.
Lemma nudge_dist : forall P Q X t,
  0 <= t -> dist X (left_nudge P Q X t) = t * dist P Q.
Proof.
  intros P Q X t Ht. apply Rsqr_inj.
  - apply dist_nonneg.
  - apply Rmult_le_pos; [exact Ht | apply dist_nonneg].
  - rewrite Rsqr_mult. unfold Rsqr. rewrite !dist_mul_self.
    unfold dist_sq, left_nudge. simpl. ring.
Qed.
Lemma combo_sep : forall P Q a b,
  dist (convex_combination P Q a) (convex_combination P Q b) =
  Rabs (a - b) * dist P Q.
Proof.
  intros P Q a b. apply Rsqr_inj.
  - apply dist_nonneg.
  - apply Rmult_le_pos; [apply Rabs_pos | apply dist_nonneg].
  - rewrite Rsqr_mult. rewrite <- Rsqr_abs. unfold Rsqr.
    rewrite !dist_mul_self.
    unfold dist_sq, convex_combination. destruct P, Q. simpl. ring.
Qed.
Lemma seg_open_sym : forall P Q X, on_seg_open P Q X -> on_seg_open Q P X.
Proof.
  intros P Q X [t [Ht ->]]. exists (1 - t). split; [lra|].
  unfold convex_combination. destruct P, Q. simpl. f_equal; ring.
Qed.
Lemma tri_open_rot : forall A B C X,
  tri_open A B C X -> tri_open B C A X.
Proof.
  intros A B C X [H1 [H2 H3]]. repeat split; assumption.
Qed.
Lemma on_bd_rot : forall A B C X, on_bd A B C X -> on_bd B C A X.
Proof.
  intros A B C X [H|[H|H]].
  - right. right. exact H.
  - left. exact H.
  - right. left. exact H.
Qed.
Lemma ab_pos_nbhd : forall A B C X,
  0 < cross A B C -> on_seg_open A B X ->
  exists r, 0 < r /\ forall Y, dist X Y < r ->
    (0 < cross A B Y -> tri_open A B C Y) /\
    (cross A B Y = 0 -> on_bd A B C Y).
Proof.
  intros A B C X Hd Ho.
  destruct (relint_side A B C X Hd Ho) as [_ [Hbc Hca]].
  destruct (slack_ball B C X Hbc) as [rbc [Hrbc Pbc]].
  destruct (slack_ball C A X Hca) as [rca [Hrca Pca]].
  destruct Ho as [t [Ht HX]]. destruct Ht as [Ht0 Ht1].
  assert (Hne : A <> B) by (intros ->; unfold cross in Hd; lra).
  assert (Hds : 0 < dist_sq B A) by (apply dist_pos_neq; exact Hne).
  set (K := Rabs (px B - px A) + Rabs (py B - py A)).
  set (rline := Rmin t (1 - t) * dist_sq B A / (2 * (K + 1))).
  assert (Hrline : 0 < rline).
  { unfold rline. apply Rdiv_lt_0_compat.
    - apply Rmult_lt_0_compat.
      + apply Rmin_pos; lra.
      + exact Hds.
    - assert (0 < K + 1) by (unfold K; pose proof (Rabs_pos (px B - px A));
        pose proof (Rabs_pos (py B - py A)); lra).
      lra. }
  exists (Rmin rline (Rmin rbc rca)). split.
  - apply Rmin_pos; [exact Hrline | apply Rmin_pos; assumption].
  - intros Y HY. split.
    + intros Hp. split; [exact Hp|]. split.
      * apply Pbc. eapply Rlt_le_trans; [exact HY|].
        eapply Rle_trans; [apply Rmin_r | apply Rmin_l].
      * apply Pca. eapply Rlt_le_trans; [exact HY|].
        eapply Rle_trans; [apply Rmin_r | apply Rmin_r].
    + intros HzY. left. apply on_seg_open_seg.
      apply (on_line_near A B X t Y (conj Ht0 Ht1) HX Hds HzY).
      eapply Rlt_le_trans; [exact HY | apply Rmin_l].
Qed.
Definition owns_dir (A B C P Q : Point) : Prop :=
  (P = A /\ Q = B) \/ (P = B /\ Q = C) \/ (P = C /\ Q = A).
Lemma owns_or_rev : forall A B C P Q,
  vert_edge A B C P Q -> owns_dir A B C P Q \/ owns_dir A B C Q P.
Proof.
  intros A B C P Q [H|[H|H]]; destruct H as [[-> ->]|[-> ->]].
  - left. left. split; reflexivity.
  - right. left. split; reflexivity.
  - left. right. left. split; reflexivity.
  - right. right. left. split; reflexivity.
  - left. right. right. split; reflexivity.
  - right. right. right. split; reflexivity.
Qed.
Lemma owns_dir_neq : forall A B C P Q,
  0 < cross A B C -> owns_dir A B C P Q -> P <> Q.
Proof.
  intros A B C P Q Hd [[-> ->]|[[-> ->]|[-> ->]]] Heq;
  subst; unfold cross in Hd; lra.
Qed.
Lemma owns_dir_nbhd : forall A B C P Q X,
  0 < cross A B C -> owns_dir A B C P Q -> on_seg_open P Q X ->
  exists r, 0 < r /\ forall Y, dist X Y < r ->
    (0 < cross P Q Y -> tri_open A B C Y) /\
    (cross P Q Y = 0 -> on_bd A B C Y).
Proof.
  intros A B C P Q X Hd Ho Hs.
  destruct Ho as [[-> ->]|[[-> ->]|[-> ->]]].
  - apply ab_pos_nbhd; assumption.
  - destruct (ab_pos_nbhd B C A X) as [r [Hr HY]].
    + rewrite <- (cross_cycle A B C). exact Hd.
    + exact Hs.
    + exists r. split; [exact Hr|]. intros Y HD.
      destruct (HY Y HD) as [Hp Hz]. split.
      * intros Hc. apply tri_open_rot. apply tri_open_rot.
        apply Hp. exact Hc.
      * intros Hc. apply on_bd_rot. apply on_bd_rot. apply Hz. exact Hc.
  - destruct (ab_pos_nbhd C A B X) as [r [Hr HY]].
    + rewrite <- (cross_cycle2 A B C). exact Hd.
    + exact Hs.
    + exists r. split; [exact Hr|]. intros Y HD.
      destruct (HY Y HD) as [Hp Hz]. split.
      * intros Hc. apply tri_open_rot. apply Hp. exact Hc.
      * intros Hc. apply on_bd_rot. apply Hz. exact Hc.
Qed.
Lemma small_left_nudge : forall P Q X r,
  P <> Q -> on_seg_open P Q X -> 0 < r ->
  exists Y, dist X Y < r /\ 0 < cross P Q Y.
Proof.
  intros P Q X r Hne Ho Hr.
  assert (Hdp : 0 < dist P Q).
  { apply dist_pos_iff_distinct. intros [Ex Ey]. apply Hne.
    destruct P, Q. simpl in *. subst. reflexivity. }
  assert (Hds : 0 < dist_sq Q P) by (apply dist_pos_neq; exact Hne).
  set (t := r / (2 * (dist P Q + 1))).
  assert (Ht : 0 < t) by (unfold t; apply Rdiv_lt_0_compat; lra).
  exists (left_nudge P Q X t). split.
  - rewrite nudge_dist by (apply Rlt_le; exact Ht). unfold t.
    apply step_lt; assumption.
  - rewrite nudge_cross.
    assert (Hz : cross P Q X = 0).
    { apply on_seg_cross0. apply on_seg_open_seg. exact Ho. }
    rewrite Hz. rewrite Rplus_0_l. apply Rmult_lt_0_compat; assumption.
Qed.
Lemma same_dir_meet : forall A B C D E F P Q X,
  0 < cross A B C -> 0 < cross D E F ->
  owns_dir A B C P Q -> owns_dir D E F P Q -> on_seg_open P Q X ->
  exists Y, tri_open A B C Y /\ tri_open D E F Y.
Proof.
  intros A B C D E F P Q X HA HD OA OD Hs.
  destruct (owns_dir_nbhd A B C P Q X HA OA Hs) as [r1 [Hr1 H1]].
  destruct (owns_dir_nbhd D E F P Q X HD OD Hs) as [r2 [Hr2 H2]].
  assert (Hne : P <> Q) by (apply (owns_dir_neq A B C); assumption).
  destruct (small_left_nudge P Q X (Rmin r1 r2) Hne Hs) as [Y [HY Hp]].
  { apply Rmin_pos; assumption. }
  destruct (H1 Y) as [O1 _].
  { eapply Rlt_le_trans; [exact HY | apply Rmin_l]. }
  destruct (H2 Y) as [O2 _].
  { eapply Rlt_le_trans; [exact HY | apply Rmin_r]. }
  exists Y. split; [apply O1; exact Hp | apply O2; exact Hp].
Qed.
Lemma uses_ge2_two : forall ts P Q,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  (2 <= edge_uses ts P Q)%nat ->
  exists T U, In T ts /\ In U ts /\ T <> U /\
    tri_edge_b T P Q = true /\ tri_edge_b U P Q = true.
Proof.
  induction ts as [|T rest IH]; intros P Q Hpos Hsem Hge; simpl in Hge, Hsem.
  - lia.
  - destruct Hsem as [Hall Hrest].
    destruct (tri_edge_b T P Q) eqn:Hb.
    + assert (Hge1 : (1 <= edge_uses rest P Q)%nat) by lia.
      destruct (uses_ge1_owner rest P Q Hge1) as [U [Hin HbU]].
      exists T, U. split; [left; reflexivity|].
      split; [right; exact Hin|]. split; [| split; assumption].
      intros Heq. subst U.
      assert (Hps : tri_pair_sem T T) by (apply Hall; exact Hin).
      assert (Hd0 : tri_pos T) by (apply Hpos; left; reflexivity).
      destruct T as [[A B] C]. simpl in Hps, Hd0.
      destruct Hps as [Hopen _]. apply Hopen.
      exists (inner_pt A B C). split; apply inner_open; exact Hd0.
    + destruct (IH P Q) as [T1 [U [Hi1 [HiU [Hneq [Hb1 HbU]]]]]].
      * intros V HV. apply Hpos. right. exact HV.
      * exact Hrest.
      * exact Hge.
      * exists T1, U. split; [right; exact Hi1|].
        split; [right; exact HiU|]. split; [exact Hneq|]. split; assumption.
Qed.
Lemma opp_edge_ball : forall ts A B C D E F P Q X,
  In (((A, B), C) : Tri) ts -> In (((D, E), F) : Tri) ts ->
  0 < cross A B C -> 0 < cross D E F ->
  owns_dir A B C P Q -> owns_dir D E F Q P -> on_seg_open P Q X ->
  interior_pt (tin_carrier ts) X.
Proof.
  intros ts A B C D E F P Q X HinT HinU HA HD DA DD Ho.
  destruct (owns_dir_nbhd A B C P Q X HA DA Ho) as [r1 [Hr1 H1]].
  assert (HoR : on_seg_open Q P X) by (apply seg_open_sym; exact Ho).
  destruct (owns_dir_nbhd D E F Q P X HD DD HoR) as [r2 [Hr2 H2]].
  exists (Rmin r1 r2). split.
  - apply Rmin_pos; assumption.
  - intros Y HY.
    destruct (Rle_dec (cross P Q Y) 0) as [Hle|Hgt].
    + destruct (Req_dec_T (cross P Q Y) 0) as [Hz|Hnz].
      * exists ((A, B), C). split; [exact HinT|]. right.
        destruct (H1 Y) as [_ HzB].
        { eapply Rlt_le_trans; [exact HY | apply Rmin_l]. }
        apply HzB. exact Hz.
      * assert (Hneg : cross P Q Y < 0) by lra.
        assert (Hpos2 : 0 < cross Q P Y) by (rewrite cross_rev; lra).
        exists ((D, E), F). split; [exact HinU|]. left.
        destruct (H2 Y) as [Ho2 _].
        { eapply Rlt_le_trans; [exact HY | apply Rmin_r]. }
        apply Ho2. exact Hpos2.
    + assert (Hp : 0 < cross P Q Y) by (apply Rnot_le_lt; exact Hgt).
      exists ((A, B), C). split; [exact HinT|]. left.
      destruct (H1 Y) as [Ho1 _].
      { eapply Rlt_le_trans; [exact HY | apply Rmin_l]. }
      apply Ho1. exact Hp.
Qed.
Lemma int_edge_interior : forall ts X,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  shared_rel ts X -> interior_pt (tin_carrier ts) X.
Proof.
  intros ts X Hpos Hsem [P [Q [Hne [Hge Ho]]]].
  destruct (uses_ge2_two ts P Q Hpos Hsem Hge)
    as [T [U [HinT [HinU [Hneq [HbT HbU]]]]]].
  assert (Hpair : tri_pair_sem T U).
  { destruct (tin_ordered_pair ts T U Hsem HinT HinU Hneq) as [H|H].
    - exact H.
    - apply tri_pair_sem_sym. exact H. }
  destruct T as [[A B] C], U as [[D E] F].
  apply tri_edge_b_true in HbT. simpl in HbT.
  apply tri_edge_b_true in HbU. simpl in HbU.
  assert (HA : 0 < cross A B C).
  { apply Hpos in HinT. simpl in HinT. exact HinT. }
  assert (HD : 0 < cross D E F).
  { apply Hpos in HinU. simpl in HinU. exact HinU. }
  simpl in Hpair.
  destruct (owns_or_rev A B C P Q HbT) as [DA|DA];
  destruct (owns_or_rev D E F P Q HbU) as [DD|DD].
  - exfalso.
    destruct (same_dir_meet A B C D E F P Q X HA HD DA DD Ho) as [Y HY].
    destruct Hpair as [Hopen _]. apply Hopen. exists Y. exact HY.
  - apply (opp_edge_ball ts A B C D E F P Q X HinT HinU HA HD DA DD Ho).
  - apply (opp_edge_ball ts D E F A B C P Q X HinU HinT HD HA DD DA Ho).
  - exfalso.
    assert (HoR : on_seg_open Q P X) by (apply seg_open_sym; exact Ho).
    destruct (same_dir_meet A B C D E F Q P X HA HD DA DD HoR) as [Y HY].
    destruct Hpair as [Hopen _]. apply Hopen. exists Y. exact HY.
Qed.
Lemma nudge_out_cross : forall P Q X t,
  cross P Q X = 0 ->
  cross P Q (left_nudge Q P X t) = - t * dist_sq P Q.
Proof.
  intros P Q X t Hz.
  set (Y := left_nudge Q P X t).
  assert (Hflip : cross P Q Y = - cross Q P Y) by (rewrite cross_rev; ring).
  rewrite Hflip. unfold Y. rewrite nudge_cross.
  replace (cross Q P X) with (- cross P Q X) by (rewrite cross_rev; ring).
  rewrite Hz. ring.
Qed.
Lemma owns_out_miss : forall A B C P Q X t,
  0 < cross A B C -> owns_dir A B C P Q -> on_seg_open P Q X -> 0 < t ->
  ~ in_tri A B C (left_nudge Q P X t).
Proof.
  intros A B C P Q X t Hd Ho Hs Ht Hin.
  assert (Hz : cross P Q X = 0).
  { apply on_seg_cross0. apply on_seg_open_seg. exact Hs. }
  assert (Hc : cross P Q (left_nudge Q P X t) < 0).
  { rewrite (nudge_out_cross P Q X t Hz).
    assert (Hne : P <> Q) by (apply (owns_dir_neq A B C); assumption).
    assert (Hds : 0 < dist_sq Q P) by (apply dist_pos_neq; exact Hne).
    replace (dist_sq P Q) with (dist_sq Q P) by (unfold dist_sq; ring).
    assert (Hpos : 0 < t * dist_sq Q P) by (apply Rmult_lt_0_compat; assumption).
    apply Ropp_lt_contravar in Hpos. rewrite Ropp_0 in Hpos.
    replace (- t * dist_sq Q P) with (- (t * dist_sq Q P)) by ring.
    exact Hpos. }
  destruct Ho as [[-> ->]|[[-> ->]|[-> ->]]].
  - destruct (proj2 (tri_slack_hull A B C _ Hd) Hin) as [Hab _]. lra.
  - destruct (proj2 (tri_slack_hull A B C _ Hd) Hin) as [_ [Hbc _]]. lra.
  - destruct (proj2 (tri_slack_hull A B C _ Hd) Hin) as [_ [_ Hca]]. lra.
Qed.
Fixpoint drop_tri (T : Tri) (ts : list Tri) : list Tri :=
  match ts with
  | [] => []
  | U :: rest => if tri_eqb T U then drop_tri T rest else U :: drop_tri T rest
  end.
Lemma drop_in : forall T ts U,
  In U (drop_tri T ts) -> In U ts /\ tri_eqb T U = false.
Proof.
  induction ts as [|V rest IH]; intros U Hin; simpl in Hin; [contradiction|].
  destruct (tri_eqb T V) eqn:Heq.
  - destruct (IH U Hin) as [Hi Hb]. split; [right; exact Hi | exact Hb].
  - destruct Hin as [->|Hin].
    + split; [left; reflexivity | exact Heq].
    + destruct (IH U Hin) as [Hi Hb]. split; [right; exact Hi | exact Hb].
Qed.
Lemma drop_keep : forall T ts U,
  In U ts -> tri_eqb T U = false -> In U (drop_tri T ts).
Proof.
  induction ts as [|V rest IH]; intros U Hin Hb; simpl in Hin; [contradiction|].
  simpl. destruct (tri_eqb T V) eqn:Heq.
  - destruct Hin as [->|Hin]; [congruence | apply IH; assumption].
  - destruct Hin as [->|Hin]; [left; reflexivity | right; apply IH; assumption].
Qed.
Lemma drop_pos : forall ts T,
  (forall V, In V ts -> tri_pos V) ->
  forall U, In U (drop_tri T ts) -> tri_pos U.
Proof.
  intros ts T Hpos U Hin. destruct (drop_in T ts U Hin) as [Hi _].
  apply Hpos. exact Hi.
Qed.
Lemma carrier_not_split : forall ts T Y,
  ~ (open_of T Y \/ bd_of T Y) ->
  ~ tin_carrier (drop_tri T ts) Y ->
  ~ tin_carrier ts Y.
Proof.
  intros ts T Y Ho Hd [U [Hin Hp]].
  destruct (tri_eqb T U) eqn:Heq.
  - apply tri_eqb_true in Heq. subst U. apply Ho. exact Hp.
  - apply Hd. exists U. split; [| exact Hp]. apply drop_keep; assumption.
Qed.
Lemma once_relint_foreign : forall ts P Q X U,
  (forall V, In V ts -> tri_pos V) -> tin_sem ts ->
  P <> Q -> edge_uses ts P Q = 1%nat -> on_seg_open P Q X ->
  In U ts -> tri_edge_b U P Q = false ->
  ~ (open_of U X \/ bd_of U X).
Proof.
  intros ts P Q X U Hpos Hsem Hne Hu Ho HinU HbU Happ.
  destruct (uses_eq1_owner ts P Q Hu) as [T [HinT [HbT _]]].
  assert (Hneq : U <> T) by (intros Heq; subst U; congruence).
  destruct Happ as [Hp|Hb].
  - destruct T as [[D E] F]. apply tri_edge_b_true in HbT. simpl in HbT.
    apply (open_vs_bd ts U ((D, E), F) X Hpos Hsem HinU HinT Hp).
    apply (bd_of_edge D E F P Q X HbT). apply on_seg_open_seg. exact Ho.
  - assert (Hps : tri_pair_sem U T).
    { destruct (tin_ordered_pair ts U T Hsem HinU HinT Hneq) as [H|H].
      - exact H.
      - apply tri_pair_sem_sym. exact H. }
    destruct U as [[A B] C], T as [[D E] F].
    simpl in Hb, Hps. apply tri_edge_b_true in HbT. simpl in HbT.
    assert (HA : 0 < cross A B C).
    { apply Hpos in HinU. simpl in HinU. exact HinU. }
    assert (HD : 0 < cross D E F).
    { apply Hpos in HinT. simpl in HinT. exact HinT. }
    destruct Hps as [_ [Hempty|[Hedge|Hvtx]]].
    + apply Hempty. exists X. split.
      * exact Hb.
      * apply (bd_of_edge D E F P Q X HbT). apply on_seg_open_seg. exact Ho.
    + destruct Hedge as [R [S [_ [HeU [HeT Hex]]]]].
      assert (HonT : on_bd D E F X).
      { apply (bd_of_edge D E F P Q X HbT). apply on_seg_open_seg. exact Ho. }
      assert (Hs : on_seg R S X) by (apply (proj1 (Hex X)); split; assumption).
      assert (Hid : edge_id P Q R S).
      { apply (same_edge_if_relint D E F P Q R S X HD Hne HbT Ho HeT Hs). }
      apply (tri_edge_b_false A B C P Q HbU).
      apply (vert_edge_transfer A B C P Q R S Hid HeU).
    + destruct Hvtx as [V [HvU [HvT [_ [_ Honly]]]]].
      assert (HonT : on_bd D E F X).
      { apply (bd_of_edge D E F P Q X HbT). apply on_seg_open_seg. exact Ho. }
      assert (EX : X = V) by (apply Honly; split; assumption).
      destruct (relint_not_vert D E F P Q X HD Hne HbT Ho) as [nD [nE nF]].
      destruct HvT as [Ed|[Ee|Ef]].
      * apply nD. rewrite <- Ed. exact EX.
      * apply nE. rewrite <- Ee. exact EX.
      * apply nF. rewrite <- Ef. exact EX.
Qed.
Lemma tri_eqb_refl : forall T, tri_eqb T T = true.
Proof.
  intros [[A B] C]. unfold tri_eqb. rewrite !point_eqb_refl. reflexivity.
Qed.
Lemma relint_once_boundary : forall ts P Q X,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  P <> Q -> edge_uses ts P Q = 1%nat -> on_seg_open P Q X ->
  boundary_pt (tin_carrier ts) X.
Proof.
  intros ts P Q X Hpos Hsem Hne Hu Ho r Hr.
  destruct (uses_eq1_owner ts P Q Hu) as [T [HinT [HbT Huniq]]].
  destruct T as [[A B] C].
  apply tri_edge_b_true in HbT. simpl in HbT.
  assert (HA : 0 < cross A B C).
  { apply Hpos in HinT. simpl in HinT. exact HinT. }
  assert (Hmiss : ~ tin_carrier (drop_tri ((A, B), C) ts) X).
  { intros [U [HinU Hp]].
    destruct (drop_in ((A, B), C) ts U HinU) as [HinUts Hneqb].
    assert (HbF : tri_edge_b U P Q = false).
    { destruct (tri_edge_b U P Q) eqn:He; [| reflexivity].
      apply tri_edge_b_true in He.
      assert (HU : U = ((A, B), C)).
      { apply Huniq. exact HinUts. apply tri_edge_b_true. exact He. }
      subst U. rewrite tri_eqb_refl in Hneqb. discriminate. }
    apply (once_relint_foreign ts P Q X U Hpos Hsem Hne Hu Ho HinUts HbF).
    exact Hp. }
  assert (Hposd : forall U, In U (drop_tri ((A, B), C) ts) -> tri_pos U).
  { intros U HU. apply (drop_pos ts ((A, B), C) Hpos U HU). }
  destruct (carrier_complement_open (drop_tri ((A, B), C) ts) X Hposd Hmiss)
    as [rd [Hrd Hout]].
  assert (Hdp : 0 < dist P Q).
  { apply dist_pos_iff_distinct. intros [Ex Ey]. apply Hne.
    destruct P, Q. simpl in *. subst. reflexivity. }
  set (rad := Rmin r rd).
  assert (Hrad : 0 < rad) by (apply Rmin_pos; assumption).
  set (tn := rad / (2 * (dist P Q + 1))).
  assert (Htn : 0 < tn) by (unfold tn; apply Rdiv_lt_0_compat; lra).
  destruct (owns_or_rev A B C P Q HbT) as [Hdir|Hdir].
  - set (Y := left_nudge Q P X tn).
    assert (HY : dist X Y < rad).
    { unfold Y. rewrite nudge_dist by (apply Rlt_le; exact Htn).
      rewrite (dist_sym Q P). unfold tn. apply step_lt; assumption. }
    assert (Hown : ~ (open_of ((A, B), C) Y \/ bd_of ((A, B), C) Y)).
    { intros [HoY|HbY].
      - apply (owns_out_miss A B C P Q X tn HA Hdir Ho Htn).
        apply tri_open_in; assumption.
      - apply (owns_out_miss A B C P Q X tn HA Hdir Ho Htn).
        apply on_bd_in_tri. exact HbY. }
    assert (Hno : ~ tin_carrier ts Y).
    { apply (carrier_not_split ts ((A, B), C) Y Hown).
      apply Hout. eapply Rlt_le_trans; [exact HY | apply Rmin_r]. }
    split.
    + exists X. split; [rewrite dist_refl; exact Hr|].
      exists ((A, B), C). split; [exact HinT|]. right.
      apply (bd_of_edge A B C P Q X HbT). apply on_seg_open_seg. exact Ho.
    + exists Y. split; [| exact Hno].
      eapply Rlt_le_trans; [exact HY | apply Rmin_l].
  - set (Y := left_nudge P Q X tn).
    assert (HoR : on_seg_open Q P X) by (apply seg_open_sym; exact Ho).
    assert (HY : dist X Y < rad).
    { unfold Y. rewrite nudge_dist by (apply Rlt_le; exact Htn).
      unfold tn. apply step_lt; assumption. }
    assert (Hown : ~ (open_of ((A, B), C) Y \/ bd_of ((A, B), C) Y)).
    { intros [HoY|HbY].
      - apply (owns_out_miss A B C Q P X tn HA Hdir HoR Htn).
        apply tri_open_in; assumption.
      - apply (owns_out_miss A B C Q P X tn HA Hdir HoR Htn).
        apply on_bd_in_tri. exact HbY. }
    assert (Hno : ~ tin_carrier ts Y).
    { apply (carrier_not_split ts ((A, B), C) Y Hown).
      apply Hout. eapply Rlt_le_trans; [exact HY | apply Rmin_r]. }
    split.
    + exists X. split; [rewrite dist_refl; exact Hr|].
      exists ((A, B), C). split; [exact HinT|]. right.
      apply (bd_of_edge A B C P Q X HbT). apply on_seg_open_seg. exact Ho.
    + exists Y. split; [| exact Hno].
      eapply Rlt_le_trans; [exact HY | apply Rmin_l].
Qed.
Lemma on_seg_near_open : forall P Q X r,
  P <> Q -> on_seg P Q X -> 0 < r ->
  exists Z, on_seg_open P Q Z /\ dist X Z < r.
Proof.
  intros P Q X r Hne [t [Ht HX]] Hr.
  destruct Ht as [Ht0 Ht1].
  assert (Hdp : 0 < dist P Q).
  { apply dist_pos_iff_distinct. intros [Ex Ey]. apply Hne.
    destruct P, Q. simpl in *. subst. reflexivity. }
  set (s := Rmin (1 / 2) (r / (2 * (dist P Q + 1)))).
  assert (Hs : 0 < s).
  { unfold s. apply Rmin_pos; [lra|]. apply Rdiv_lt_0_compat; lra. }
  assert (Hs1 : s < 1).
  { unfold s. eapply Rle_lt_trans; [apply Rmin_l|]. lra. }
  assert (Hsd : s * dist P Q < r).
  { apply Rle_lt_trans with ((r / (2 * (dist P Q + 1))) * dist P Q).
    - apply Rmult_le_compat_r; [apply dist_nonneg|]. unfold s. apply Rmin_r.
    - apply step_lt; assumption. }
  destruct (Rlt_dec 0 t) as [Ht0'|Ht0'];
  destruct (Rlt_dec t 1) as [Ht1'|Ht1'].
  - subst X. exists (convex_combination P Q t). split.
    + exists t. split; [split; assumption | reflexivity].
    + rewrite dist_refl. exact Hr.
  - assert (Heqt : t = 1) by lra. subst t. rewrite combo_right in HX. subst X.
    exists (convex_combination P Q (1 - s)). split.
    + exists (1 - s). split; [| reflexivity]. split; lra.
    + set (Z := convex_combination P Q (1 - s)).
      assert (HQ : convex_combination P Q 1 = Q) by apply combo_right.
      rewrite <- HQ. unfold Z. rewrite combo_sep.
      replace (1 - (1 - s)) with s by ring.
      rewrite (Rabs_right s) by lra. exact Hsd.
  - assert (Heqt : t = 0) by lra. subst t. rewrite combo_left in HX. subst X.
    exists (convex_combination P Q s). split.
    + exists s. split; [| reflexivity]. split; lra.
    + set (Z := convex_combination P Q s).
      assert (HP : convex_combination P Q 0 = P) by apply combo_left.
      rewrite <- HP. unfold Z. rewrite combo_sep.
      replace (0 - s) with (- s) by ring.
      rewrite Rabs_Ropp. rewrite (Rabs_right s) by lra. exact Hsd.
  - lra.
Qed.
Lemma bd_edge_boundary : forall ts X,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  tin_bd_cells ts X -> boundary_pt (tin_carrier ts) X.
Proof.
  intros ts X Hpos Hsem [P [Q [Hne [Hu Hs]]]] r Hr.
  destruct (on_seg_near_open P Q X (r / 2) Hne Hs) as [Z [HZ HdZ]]; [lra|].
  assert (HbZ : boundary_pt (tin_carrier ts) Z).
  { apply (relint_once_boundary ts P Q Z Hpos Hsem Hne Hu HZ). }
  destruct (HbZ (r / 2) ltac:(lra)) as [_ [Y [HdY Hout]]].
  split.
  - exists X. split; [rewrite dist_refl; exact Hr|].
    destruct (uses_eq1_owner ts P Q Hu) as [T [HinT [HbT _]]].
    destruct T as [[A B] C]. apply tri_edge_b_true in HbT. simpl in HbT.
    exists ((A, B), C). split; [exact HinT|]. right.
    apply (bd_of_edge A B C P Q X HbT Hs).
  - exists Y. split; [| exact Hout].
    apply Rle_lt_trans with (dist X Z + dist Z Y).
    + apply dist_triangle.
    + lra.
Qed.
Lemma neg_piece : forall A B C Y,
  0 < cross A B C ->
  cross A B Y < 0 \/ cross B C Y < 0 \/ cross C A Y < 0 ->
  ~ (tri_open A B C Y \/ on_bd A B C Y).
Proof.
  intros A B C Y Hd Hn [Ho|Hb].
  - destruct Ho as [a [b c]]. destruct Hn as [h|[h|h]]; lra.
  - apply on_bd_in_tri in Hb.
    destruct (proj2 (tri_slack_hull A B C Y Hd) Hb) as [a [b c]].
    destruct Hn as [h|[h|h]]; lra.
Qed.
Definition strip_ts : list Tri :=
  [((mkPoint 1 0, mkPoint 0 1), mkPoint 0 0);
   ((mkPoint 0 1, mkPoint 1 0), mkPoint 1 1)].
Definition strip_mid : Point := mkPoint (1 / 2) (1 / 2).
Lemma strip_pos : forall T, In T strip_ts -> tri_pos T.
Proof.
  intros T Hin. simpl in Hin. destruct Hin as [<-|[<-|[]]].
  - unfold tri_pos, cross. simpl. lra.
  - unfold tri_pos, cross. simpl. lra.
Qed.
Lemma strip_sem : tin_sem strip_ts.
Proof.
  split.
  - intros U Hin. simpl in Hin. destruct Hin as [<-|[]].
    destruct tin_strip as [Hsem _]. exact Hsem.
  - simpl. split; [intros U []| exact I].
Qed.
Ltac kill_pts :=
  repeat match goal with
  | |- context [point_eqb ?a ?a] => rewrite (point_eqb_refl a)
  | |- context [point_eqb (mkPoint ?x1 ?y1) (mkPoint ?x2 ?y2)] =>
      rewrite (point_eqb_false_neq (mkPoint x1 y1) (mkPoint x2 y2)) by
        (apply pts_neq; first [ left; simpl; lra | right; simpl; lra ])
  end.
Lemma strip_uses :
  edge_uses strip_ts (mkPoint 1 0) (mkPoint 0 1) = 2%nat.
Proof.
  unfold strip_ts.
  rewrite uses_cons_true
    by (cbv [tri_edge_b vert_edge_b edge_id_b]; kill_pts; simpl; reflexivity).
  rewrite uses_cons_true
    by (cbv [tri_edge_b vert_edge_b edge_id_b]; kill_pts; simpl; reflexivity).
  reflexivity.
Qed.
Lemma strip_shared_interior_fixtures :
  interior_pt (tin_carrier strip_ts) strip_mid.
Proof.
  apply (int_edge_interior strip_ts strip_mid strip_pos strip_sem).
  exists (mkPoint 1 0), (mkPoint 0 1). split.
  - apply pts_neq. left. simpl. lra.
  - split; [rewrite strip_uses; lia|].
    exists (1 / 2). split; [lra|].
    unfold strip_mid, convex_combination. simpl. f_equal; lra.
Qed.
Definition bow_ts : list Tri :=
  [((mkPoint 0 0, mkPoint 1 0), mkPoint 0 1);
   ((mkPoint 0 0, mkPoint (-1) 0), mkPoint 0 (-1))].
Lemma bowtie_vertex_boundary_fixtures :
  boundary_pt (tin_carrier bow_ts) (mkPoint 0 0).
Proof.
  intros r Hr.
  set (d := Rmin (r / 3) (1 / 2)).
  assert (Hd : 0 < d) by (unfold d; apply Rmin_pos; lra).
  set (Y := mkPoint d (- d)).
  assert (HY : dist (mkPoint 0 0) Y < r).
  { assert (Hsq : dist_sq (mkPoint 0 0) Y = 2 * d * d)
      by (unfold Y, dist_sq; simpl; ring).
    assert (Hlt : 2 * d * d < r * r).
    { assert (Hle : d <= r / 3) by (unfold d; apply Rmin_l).
      assert (H2 : 2 * d < r) by lra.
      assert (H4 : (2 * d) * (2 * d) < r * (2 * d)).
      { apply Rmult_lt_compat_r; lra. }
      assert (H5 : r * (2 * d) < r * r) by (apply Rmult_lt_compat_l; lra).
      replace ((2 * d) * (2 * d)) with (4 * (d * d)) in H4 by ring.
      apply Rlt_trans with (4 * (d * d)).
      - replace (2 * d * d) with (2 * (d * d)) by ring.
        apply Rmult_lt_compat_r; [apply Rmult_lt_0_compat; assumption | lra].
      - apply Rlt_trans with (r * (2 * d)); [exact H4 | exact H5]. }
    unfold dist. rewrite Hsq.
    apply Rlt_le_trans with (sqrt (r * r)).
    - apply sqrt_lt_1.
      + apply Rmult_le_pos; [apply Rmult_le_pos; [lra | lra] | lra].
      + apply Rmult_le_pos; [lra| lra].
      + exact Hlt.
    - rewrite sqrt_square; lra. }
  split.
  - exists (mkPoint 0 0). split.
    + rewrite dist_refl. exact Hr.
    + exists ((mkPoint 0 0, mkPoint 1 0), mkPoint 0 1). split.
      * unfold bow_ts. simpl. left. reflexivity.
      * right. left. exact (proj1 (seg_ends (mkPoint 0 0) (mkPoint 1 0))).
  - exists Y. split; [exact HY|].
    intros [U [Hin Hp]]. simpl in Hin. destruct Hin as [<-|[<-|[]]].
    + apply (neg_piece (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) Y).
      * unfold cross. simpl. lra.
      * left. unfold Y, cross. simpl. lra.
      * exact Hp.
    + apply (neg_piece (mkPoint 0 0) (mkPoint (-1) 0) (mkPoint 0 (-1)) Y).
      * unfold cross. simpl. lra.
      * right. right. unfold Y, cross. simpl. lra.
      * exact Hp.
Qed.
Definition hole_ts : list Tri :=
  [((mkPoint 0 0, mkPoint 3 0), mkPoint 2 1);
   ((mkPoint 0 0, mkPoint 2 1), mkPoint 1 1);
   ((mkPoint 3 0, mkPoint 3 3), mkPoint 2 2);
   ((mkPoint 3 0, mkPoint 2 2), mkPoint 2 1);
   ((mkPoint 3 3, mkPoint 0 3), mkPoint 1 2);
   ((mkPoint 3 3, mkPoint 1 2), mkPoint 2 2);
   ((mkPoint 0 3, mkPoint 0 0), mkPoint 1 1);
   ((mkPoint 0 3, mkPoint 1 1), mkPoint 1 2)].
Definition hole_mid : Point := mkPoint (3 / 2) 1.
Lemma hole_vdist : forall d,
  0 <= d -> dist hole_mid (mkPoint (3 / 2) (1 + d)) = d.
Proof.
  intros d Hd. unfold dist, dist_sq, hole_mid. simpl.
  replace ((3 / 2 - 3 / 2) * (3 / 2 - 3 / 2) +
           (1 - (1 + d)) * (1 - (1 + d))) with (d * d) by ring.
  apply sqrt_square. exact Hd.
Qed.
Lemma hole_vdist_in : forall d,
  0 <= d -> dist hole_mid (mkPoint (3 / 2) (1 - d)) = d.
Proof.
  intros d Hd. unfold dist, dist_sq, hole_mid. simpl.
  replace ((3 / 2 - 3 / 2) * (3 / 2 - 3 / 2) +
           (1 - (1 - d)) * (1 - (1 - d))) with (d * d) by ring.
  apply sqrt_square. exact Hd.
Qed.
Lemma hole_boundary_fixtures : boundary_pt (tin_carrier hole_ts) hole_mid.
Proof.
  intros r Hr.
  set (d := Rmin (r / 2) (1 / 8)).
  assert (Hd : 0 < d) by (unfold d; apply Rmin_pos; lra).
  assert (Hle : d <= r / 2) by (unfold d; apply Rmin_l).
  assert (Hd4 : d < 1 / 4).
  { unfold d. eapply Rle_lt_trans; [apply Rmin_r|]. lra. }
  clearbody d.
  set (Yin := mkPoint (3 / 2) (1 - d)).
  set (Yout := mkPoint (3 / 2) (1 + d)).
  split.
  - exists Yin. split.
    + unfold Yin. rewrite hole_vdist_in by lra.
      lra.
    + exists ((mkPoint 0 0, mkPoint 2 1), mkPoint 1 1). split.
      * unfold hole_ts. simpl. right. left. reflexivity.
      * left. unfold Yin.
        { clear - Hd Hd4. unfold tri_open. split; [| split].
          - unfold cross. simpl. lra.
          - unfold cross. simpl. lra.
          - unfold cross. simpl. lra. }
  - exists Yout. split.
    + unfold Yout. rewrite hole_vdist by lra.
      lra.
    + intros [U [Hin Hp]]. simpl in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
      * apply (neg_piece (mkPoint 0 0) (mkPoint 3 0) (mkPoint 2 1) Yout);
          [| | exact Hp]; unfold cross, Yout; simpl; [lra | right; right; lra].
      * apply (neg_piece (mkPoint 0 0) (mkPoint 2 1) (mkPoint 1 1) Yout);
          [| | exact Hp]; unfold cross, Yout; simpl; [lra | right; left; lra].
      * apply (neg_piece (mkPoint 3 0) (mkPoint 3 3) (mkPoint 2 2) Yout);
          [| | exact Hp]; unfold cross, Yout; simpl; [lra | right; right; lra].
      * apply (neg_piece (mkPoint 3 0) (mkPoint 2 2) (mkPoint 2 1) Yout);
          [| | exact Hp]; unfold cross, Yout; simpl; [lra | right; left; lra].
      * apply (neg_piece (mkPoint 3 3) (mkPoint 0 3) (mkPoint 1 2) Yout);
          [| | exact Hp]; unfold cross, Yout; simpl; [lra | right; left; lra].
      * apply (neg_piece (mkPoint 3 3) (mkPoint 1 2) (mkPoint 2 2) Yout);
          [| | exact Hp]; unfold cross, Yout; simpl; [lra | right; left; lra].
      * apply (neg_piece (mkPoint 0 3) (mkPoint 0 0) (mkPoint 1 1) Yout);
          [| | exact Hp]; unfold cross, Yout; simpl; [lra | right; left; lra].
      * apply (neg_piece (mkPoint 0 3) (mkPoint 1 1) (mkPoint 1 2) Yout);
          [| | exact Hp]; unfold cross, Yout; simpl; [lra | right; left; lra].
Qed.

(* Assumptions: sig_not_dec, sig_forall_dec, functional_extensionality_dep. *)
Print Assumptions interior_in.
Print Assumptions interior_not_boundary.
Print Assumptions cross_diff.
Print Assumptions cross_rev.
Print Assumptions abs_dx_le_dist.
Print Assumptions abs_dy_le_dist.
Print Assumptions cross_lip.
Print Assumptions neg_abs_le.
Print Assumptions below_abs.
Print Assumptions slack_ball.
Print Assumptions neg_cross_ball.
Print Assumptions open_nbhd.
Print Assumptions tri_open_in.
Print Assumptions open_tri_interior.
Print Assumptions out_nbhd.
Print Assumptions piece_miss.
Print Assumptions carrier_complement_open.
Print Assumptions piece_dec.
Print Assumptions carrier_dec.
Print Assumptions boundary_in_carrier.
Print Assumptions relint_side.
Print Assumptions seg_t_combo.
Print Assumptions dot_disp_bound.
Print Assumptions frac_lt_one.
Print Assumptions step_lt.
Print Assumptions on_line_near.
Print Assumptions nudge_cross.
Print Assumptions nudge_dist.
Print Assumptions combo_sep.
Print Assumptions seg_open_sym.
Print Assumptions tri_open_rot.
Print Assumptions on_bd_rot.
Print Assumptions ab_pos_nbhd.
Print Assumptions owns_or_rev.
Print Assumptions owns_dir_neq.
Print Assumptions owns_dir_nbhd.
Print Assumptions small_left_nudge.
Print Assumptions same_dir_meet.
Print Assumptions uses_ge2_two.
Print Assumptions opp_edge_ball.
Print Assumptions int_edge_interior.
Print Assumptions nudge_out_cross.
Print Assumptions owns_out_miss.
Print Assumptions drop_in.
Print Assumptions drop_keep.
Print Assumptions drop_pos.
Print Assumptions carrier_not_split.
Print Assumptions once_relint_foreign.
Print Assumptions tri_eqb_refl.
Print Assumptions relint_once_boundary.
Print Assumptions on_seg_near_open.
Print Assumptions bd_edge_boundary.
Print Assumptions neg_piece.
Print Assumptions strip_pos.
Print Assumptions strip_sem.
Print Assumptions strip_uses.
Print Assumptions strip_shared_interior_fixtures.
Print Assumptions bowtie_vertex_boundary_fixtures.
Print Assumptions hole_vdist.
Print Assumptions hole_vdist_in.
Print Assumptions hole_boundary_fixtures.
