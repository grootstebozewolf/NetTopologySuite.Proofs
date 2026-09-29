(* NetTopologySuite.Proofs.ConvexClipComplete
   Completeness, CCW preservation, and rational vertices for one
   half-plane clip. ConvexClipPoly holds the frame and the chord bound;
   this file stays under the 1234-line monolith floor.
   topic: relate
   claimId: tri-de9im-a
   witness: TrianglePairClip.ii_nonempty_iff
   secondary witness: clip_correct
   3-axiom host. No Admitted. AI-drafted (Cursor Grok 4.7), human-reviewed.
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra Lia List Compare_dec QArith Qreals.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex RingArea979 ConvexClip ConvexClipPoly.
Local Open Scope R_scope.
(* Split a weight list into the vertices a boolean keeps and the ones it drops.
   Lengths follow filter, so the two pieces are hull witnesses on their own. *)
Fixpoint take_w (keep : Point -> bool) (w : list R) (ps : list Point) : list R :=
  match w, ps with
  | a :: wt, v :: vt =>
      if keep v then a :: take_w keep wt vt else take_w keep wt vt
  | _, _ => []
  end.
Lemma take_w_length : forall keep w ps,
  length w = length ps ->
  length (take_w keep w ps) = length (filter keep ps).
Proof.
  intros keep w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl; simpl in *; try discriminate.
  - reflexivity.
  - destruct (keep v) eqn:Hk; simpl; [| apply IH; lia].
    f_equal. apply IH. lia.
Qed.
Lemma take_w_nonneg : forall keep w ps,
  length w = length ps -> nonneg_w w -> nonneg_w (take_w keep w ps).
Proof.
  intros keep w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl Hw; simpl in *; try discriminate.
  - intros z Hz. contradiction.
  - intros z Hz. destruct (keep v) eqn:Hk.
    + simpl in Hz. destruct Hz as [->|Hz].
      * apply Hw. left. reflexivity.
      * apply (IH w); [lia | | exact Hz].
        intros u Hu. apply Hw. right. exact Hu.
    + apply (IH w); [lia | | exact Hz].
      intros u Hu. apply Hw. right. exact Hu.
Qed.
Lemma rsum_take_split : forall keep w ps,
  length w = length ps ->
  rsum (take_w keep w ps)
  + rsum (take_w (fun v => negb (keep v)) w ps) = rsum w.
Proof.
  intros keep w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl; simpl in Hl; try discriminate.
  - simpl. ring.
  - specialize (IH w ltac:(lia)). destruct (keep v) eqn:Hk; simpl.
    + rewrite Hk. simpl. rewrite <- IH. ring.
    + rewrite Hk. simpl. rewrite <- IH. ring.
Qed.
Lemma wpt_take_split : forall keep w ps,
  length w = length ps ->
  px (wpt w ps)
    = px (wpt (take_w keep w ps) (filter keep ps))
      + px (wpt (take_w (fun v => negb (keep v)) w ps)
                (filter (fun v => negb (keep v)) ps)) /\
  py (wpt w ps)
    = py (wpt (take_w keep w ps) (filter keep ps))
      + py (wpt (take_w (fun v => negb (keep v)) w ps)
                (filter (fun v => negb (keep v)) ps)).
Proof.
  intros keep w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl; simpl in Hl; try discriminate.
  - simpl. split; ring.
  - destruct (IH w ltac:(lia)) as [Ex Ey].
    destruct (keep v) eqn:Hk; cbn [take_w filter]; rewrite Hk.
    + replace (if true then a :: take_w keep w ps else take_w keep w ps)
        with (a :: take_w keep w ps) by reflexivity.
      replace (if true then v :: filter keep ps else filter keep ps)
        with (v :: filter keep ps) by reflexivity.
      replace (if negb true
               then a :: take_w (fun u => negb (keep u)) w ps
               else take_w (fun u => negb (keep u)) w ps)
        with (take_w (fun u => negb (keep u)) w ps) by reflexivity.
      replace (if negb true
               then v :: filter (fun u => negb (keep u)) ps
               else filter (fun u => negb (keep u)) ps)
        with (filter (fun u => negb (keep u)) ps) by reflexivity.
      change (px (wpt (a :: w) (v :: ps))) with (a * px v + px (wpt w ps)).
      change (py (wpt (a :: w) (v :: ps))) with (a * py v + py (wpt w ps)).
      change (px (wpt (a :: take_w keep w ps) (v :: filter keep ps)))
        with (a * px v + px (wpt (take_w keep w ps) (filter keep ps))).
      change (py (wpt (a :: take_w keep w ps) (v :: filter keep ps)))
        with (a * py v + py (wpt (take_w keep w ps) (filter keep ps))).
      rewrite Ex, Ey. split; ring.
    + replace (if false then a :: take_w keep w ps else take_w keep w ps)
        with (take_w keep w ps) by reflexivity.
      replace (if false then v :: filter keep ps else filter keep ps)
        with (filter keep ps) by reflexivity.
      replace (if negb false
               then a :: take_w (fun u => negb (keep u)) w ps
               else take_w (fun u => negb (keep u)) w ps)
        with (a :: take_w (fun u => negb (keep u)) w ps) by reflexivity.
      replace (if negb false
               then v :: filter (fun u => negb (keep u)) ps
               else filter (fun u => negb (keep u)) ps)
        with (v :: filter (fun u => negb (keep u)) ps) by reflexivity.
      change (px (wpt (a :: w) (v :: ps))) with (a * px v + px (wpt w ps)).
      change (py (wpt (a :: w) (v :: ps))) with (a * py v + py (wpt w ps)).
      change (px (wpt (a :: take_w (fun u => negb (keep u)) w ps)
                      (v :: filter (fun u => negb (keep u)) ps)))
        with (a * px v + px (wpt (take_w (fun u => negb (keep u)) w ps)
                                 (filter (fun u => negb (keep u)) ps))).
      change (py (wpt (a :: take_w (fun u => negb (keep u)) w ps)
                      (v :: filter (fun u => negb (keep u)) ps)))
        with (a * py v + py (wpt (take_w (fun u => negb (keep u)) w ps)
                                 (filter (fun u => negb (keep u)) ps))).
      rewrite Ex, Ey. split; ring.
Qed.
Lemma cross_dot_scale : forall t p q w ps,
  length w = length ps ->
  cross_dot p q (rscale t w) ps = t * cross_dot p q w ps.
Proof.
  intros t p q w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl; simpl in *; try discriminate.
  - ring.
  - rewrite (IH w) by lia. ring.
Qed.
Lemma in_hull_rescale : forall ps w,
  length w = length ps -> nonneg_w w -> 0 < rsum w ->
  in_hull ps (mkPoint (px (wpt w ps) / rsum w) (py (wpt w ps) / rsum w)).
Proof.
  intros ps w Hl Hn Hs.
  exists (rscale (/ rsum w) w).
  assert (Hpos : 0 < / rsum w) by (apply Rinv_0_lt_compat; exact Hs).
  repeat split.
  - rewrite rscale_length. exact Hl.
  - apply rscale_nonneg; [apply Rlt_le; exact Hpos | exact Hn].
  - rewrite rsum_scale. apply Rinv_l. lra.
  - rewrite wpt_scale by exact Hl. destruct (wpt w ps) as [x y]. simpl.
    f_equal; unfold Rdiv; ring.
Qed.
Lemma take_pos_existsb : forall keep w ps,
  length w = length ps -> nonneg_w w ->
  0 < rsum (take_w keep w ps) ->
  existsb keep ps = true.
Proof.
  intros keep w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl Hw Hs; simpl in Hl; try discriminate.
  - simpl in Hs. lra.
  - destruct (keep v) eqn:Hk; simpl.
    + rewrite Hk. simpl. reflexivity.
    + simpl in Hs. rewrite Hk in Hs. simpl in Hs.
      rewrite Hk. simpl.
      apply IH with (w := w); [lia | | exact Hs].
      intros z Hz. apply Hw. right. exact Hz.
Qed.
Lemma filter_in_clip : forall poly p q v,
  point_eqb p q = false ->
  (3 <= length poly)%nat ->
  In v (filter (inside_b p q) poly) ->
  In v (clip_halfplane poly p q).
Proof.
  intros poly p q v Hpq Hlen Hin.
  apply filter_In in Hin. destruct Hin as [Hin Hb].
  apply clip_keeps_inside; assumption.
Qed.
Lemma negb_inside_cross : forall p q v,
  negb (inside_b p q v) = true -> cross p q v < 0.
Proof.
  intros p q v H. apply inside_b_false. apply negb_true_iff. exact H.
Qed.
(* n >= 3. Inside mass stays in the clip; outside mass crosses the chord
   between one leaving hit and one entering hit, both emitted. *)
Lemma clip_n3_complete : forall poly p q x,
  point_eqb p q = false ->
  (3 <= length poly)%nat ->
  convex_supports poly ->
  in_hull poly x ->
  inside_closed p q x ->
  in_hull (clip_halfplane poly p q) x.
Proof.
  intros poly p q x Hpq Hlen Hconv Hx HinC.
  destruct poly as [|a [|b [|c rest]]]; simpl in Hlen; try lia.
  destruct Hx as [w [Hl [Hn [Hs Hp]]]].
  set (keep := inside_b p q).
  set (drop := fun v : Point => negb (keep v)).
  set (wI := take_w keep w (a :: b :: c :: rest)).
  set (wO := take_w drop w (a :: b :: c :: rest)).
  set (pI := filter keep (a :: b :: c :: rest)).
  set (pO := filter drop (a :: b :: c :: rest)).
  set (sI := rsum wI). set (sO := rsum wO).
  assert (HlenI : length wI = length pI) by (unfold wI, pI; apply take_w_length; exact Hl).
  assert (HlenO : length wO = length pO) by (unfold wO, pO; apply take_w_length; exact Hl).
  assert (HnI : nonneg_w wI) by (unfold wI; apply take_w_nonneg; assumption).
  assert (HnO : nonneg_w wO) by (unfold wO; apply take_w_nonneg; assumption).
  assert (Hsum : sI + sO = 1).
  { unfold sI, sO, wI, wO, drop, keep.
    rewrite rsum_take_split by exact Hl. exact Hs. }
  assert (Hsplit := wpt_take_split keep w (a :: b :: c :: rest) Hl).
  assert (HleO : 0 <= sO) by (apply rsum_nonneg; exact HnO).
  assert (HleI : 0 <= sI) by (apply rsum_nonneg; exact HnI).
  destruct (Rle_lt_or_eq_dec 0 sO HleO) as [Hso|Hso0].
  - (* positive outside mass *)
    destruct (Rle_lt_or_eq_dec 0 sI HleI) as [Hsi|Hsi0].
    + (* both sides. x crosses from an inside combination to an outside one. *)
      set (xI := mkPoint (px (wpt wI pI) / sI) (py (wpt wI pI) / sI)).
      set (xO := mkPoint (px (wpt wO pO) / sO) (py (wpt wO pO) / sO)).
      assert (HxI : in_hull pI xI).
      { unfold xI. apply in_hull_rescale; [exact HlenI | exact HnI | exact Hsi]. }
      assert (HxO : in_hull pO xO).
      { unfold xO. apply in_hull_rescale; [exact HlenO | exact HnO | exact Hso]. }
      assert (HexI : existsb keep (a :: b :: c :: rest) = true).
      { apply take_pos_existsb with (w := w); [exact Hl | exact Hn |].
        unfold sI, wI, keep in Hsi. exact Hsi. }
      assert (HexO : existsb drop (a :: b :: c :: rest) = true).
      { apply take_pos_existsb with (w := w); [exact Hl | exact Hn |].
        unfold sO, wO, drop in Hso. exact Hso. }
      assert (Hwalk : chain_supports a ((b :: c :: rest) ++ [a]) (a :: b :: c :: rest)).
      { unfold convex_supports in Hconv. simpl in Hconv. exact Hconv. }
      destruct (find_leave a ((b :: c :: rest) ++ [a]) p q) as [[aL bL]|] eqn:Hleave.
      2: { exfalso. apply (closed_has_leave a (b :: c :: rest) p q); auto. }
      destruct (find_enter a ((b :: c :: rest) ++ [a]) p q) as [[aE bE]|] eqn:Henter.
      2: { exfalso. apply (closed_has_enter a (b :: c :: rest) p q); auto. }
      destruct (find_leave_spec _ _ _ _ _ _ Hleave) as [HaL [HbL HinL]].
      destruct (find_enter_spec _ _ _ _ _ _ Henter) as [HaE [HbE HinE]].
      assert (HsupL : forall v, In v (a :: b :: c :: rest) -> 0 <= cross aL bL v).
      { apply walk_edge_supports with (prev := a) (rest := (b :: c :: rest) ++ [a]).
        - exact Hwalk.
        - apply (find_leave_has_edge a ((b :: c :: rest) ++ [a]) p q). exact Hleave. }
      assert (HsupE : forall v, In v (a :: b :: c :: rest) -> 0 <= cross aE bE v).
      { apply walk_edge_supports with (prev := a) (rest := (b :: c :: rest) ++ [a]).
        - exact Hwalk.
        - apply (find_enter_has_edge a ((b :: c :: rest) ++ [a]) p q). exact Henter. }
      assert (Hdist : points_distinct p q) by (apply point_eqb_false_distinct; exact Hpq).
      assert (HallO : forall v, In v pO -> cross p q v < 0).
      { intros v Hv. apply filter_In in Hv. destruct Hv as [_ Hd].
        apply negb_inside_cross. unfold drop, keep in Hd. exact Hd. }
      assert (HfO : cross p q xO < 0).
      { unfold xO.
        replace (mkPoint (px (wpt wO pO) / sO) (py (wpt wO pO) / sO))
          with (wpt (rscale (/ sO) wO) pO).
        - rewrite cross_wpt_sum1.
          + apply cross_dot_neg.
            * rewrite rscale_length. exact HlenO.
            * apply rscale_nonneg;
                [apply Rlt_le, Rinv_0_lt_compat; exact Hso | exact HnO].
            * assert (Hnz : sO <> 0)
                by (intro E; rewrite E in Hso; exact (Rlt_irrefl 0 Hso)).
              unfold sO in Hnz. rewrite rsum_scale. apply Rinv_l. exact Hnz.
            * exact HallO.
          + rewrite rscale_length. exact HlenO.
          + assert (Hnz : sO <> 0)
              by (intro E; rewrite E in Hso; exact (Rlt_irrefl 0 Hso)).
            unfold sO in Hnz. rewrite rsum_scale. apply Rinv_l. exact Hnz.
        - rewrite wpt_scale by exact HlenO.
          destruct (wpt wO pO) as [ox oy]. simpl. f_equal; unfold Rdiv; ring. }
      assert (HsIeq : sI = 1 - sO).
      { apply Rplus_eq_reg_r with (r := sO). rewrite Hsum. ring. }
      assert (Exx : x = convex_combination xI xO sO).
      { destruct Hsplit as [Ex Ey]. rewrite Hp in Ex, Ey.
        unfold convex_combination. destruct x as [xx xy]. simpl in *.
        replace (px xI) with (px (wpt wI pI) / sI) by (unfold xI; reflexivity).
        replace (py xI) with (py (wpt wI pI) / sI) by (unfold xI; reflexivity).
        replace (px xO) with (px (wpt wO pO) / sO) by (unfold xO; reflexivity).
        replace (py xO) with (py (wpt wO pO) / sO) by (unfold xO; reflexivity).
        assert (HnzI : sI <> 0)
          by (intro E; rewrite E in Hsi; exact (Rlt_irrefl 0 Hsi)).
        assert (HnzO : sO <> 0)
          by (intro E; rewrite E in Hso; exact (Rlt_irrefl 0 Hso)).
        f_equal.
        - replace ((1 - sO) * (px (wpt wI pI) / sI)) with (px (wpt wI pI)).
          + replace (sO * (px (wpt wO pO) / sO)) with (px (wpt wO pO)).
            * unfold wI, wO, pI, pO, drop. exact Ex.
            * field. exact HnzO.
          + rewrite HsIeq. field. rewrite <- HsIeq. exact HnzI.
        - replace ((1 - sO) * (py (wpt wI pI) / sI)) with (py (wpt wI pI)).
          + replace (sO * (py (wpt wO pO) / sO)) with (py (wpt wO pO)).
            * unfold wI, wO, pI, pO, drop. exact Ey.
            * field. exact HnzO.
          + rewrite HsIeq. field. rewrite <- HsIeq. exact HnzI. }
      assert (HfI : 0 < cross p q xI).
      { assert (Hfx : cross p q x =
            (1 - sO) * cross p q xI + sO * cross p q xO).
        { rewrite Exx. apply cross_combo. }
        assert (Hge : 0 <= sI * cross p q xI + sO * cross p q xO).
        { replace (sI * cross p q xI) with ((1 - sO) * cross p q xI).
          - rewrite <- Hfx. exact HinC.
          - rewrite <- HsIeq. reflexivity. }
        assert (Hneg : sO * cross p q xO < 0).
        { apply Rmult_lt_compat_l with (r := sO) in HfO; [| exact Hso].
          rewrite Rmult_0_r in HfO. exact HfO. }
        assert (Hshift : - (sO * cross p q xO) <= sI * cross p q xI).
        { apply Rplus_le_reg_l with (r := sO * cross p q xO).
          replace (sO * cross p q xO + - (sO * cross p q xO)) with 0 by ring.
          replace (sO * cross p q xO + sI * cross p q xI)
            with (sI * cross p q xI + sO * cross p q xO) by ring.
          exact Hge. }
        apply Rmult_lt_reg_l with (r := sI); [exact Hsi|].
        apply Rlt_le_trans with (- (sO * cross p q xO)); [lra | exact Hshift]. }
      destruct (line_hit_on_seg xI xO p q) as [tM [HtM [HeqM HzM]]].
      { left. split; [apply Rlt_le; exact HfI | exact HfO]. }
      assert (Hs_le : sO <= tM).
      { assert (Et : (1 - tM) * cross p q xI + tM * cross p q xO = 0).
        { rewrite <- (cross_combo p q xI xO tM). rewrite <- HeqM. exact HzM. }
        assert (EtD : tM * (cross p q xI - cross p q xO) = cross p q xI).
        { apply Rminus_diag_uniq.
          replace (tM * (cross p q xI - cross p q xO) - cross p q xI)
            with (- ((1 - tM) * cross p q xI + tM * cross p q xO)) by ring.
          rewrite Et. ring. }
        assert (Es : 0 <= cross p q xI - sO * (cross p q xI - cross p q xO)).
        { assert (Exf : cross p q x =
              (1 - sO) * cross p q xI + sO * cross p q xO).
          { rewrite Exx. apply cross_combo. }
          replace (cross p q xI - sO * (cross p q xI - cross p q xO))
            with ((1 - sO) * cross p q xI + sO * cross p q xO) by ring.
          rewrite <- Exf. exact HinC. }
        assert (HD : 0 < cross p q xI - cross p q xO) by lra.
        apply Rmult_le_reg_r with (r := cross p q xI - cross p q xO); [exact HD|].
        rewrite EtD.
        apply Rplus_le_reg_r with (r := - (sO * (cross p q xI - cross p q xO))).
        replace (sO * (cross p q xI - cross p q xO)
                 + - (sO * (cross p q xI - cross p q xO))) with 0 by ring.
        replace (cross p q xI + - (sO * (cross p q xI - cross p q xO)))
          with (cross p q xI - sO * (cross p q xI - cross p q xO)) by ring.
        exact Es. }
      assert (Htpos : 0 < tM).
      { destruct HtM as [Ht0 _]. destruct (Rle_lt_or_eq_dec 0 tM Ht0) as [Hlt|Heq];
          [exact Hlt|].
        exfalso.
        assert (Et : (1 - tM) * cross p q xI + tM * cross p q xO = 0).
        { rewrite <- (cross_combo p q xI xO tM). rewrite <- HeqM. exact HzM. }
        rewrite <- Heq in Et. ring_simplify in Et. lra. }
      set (u := sO / tM).
      assert (Hu01 : 0 <= u <= 1).
      { unfold u. split.
        - apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; exact Htpos].
        - apply Rmult_le_reg_r with (r := tM); [exact Htpos|].
          unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; lra. }
      assert (Hxu : x = convex_combination xI (line_hit xI xO p q) u).
      { rewrite HeqM. rewrite (combo_nest xI xO tM u).
        replace (u * tM) with sO by (unfold u; field; lra).
        exact Exx. }
      assert (HIpoly : in_hull (a :: b :: c :: rest) xI).
      { apply members_in_hull with (K := pI); [| exact HxI].
        intros v Hv. apply in_hull_in.
        apply filter_In in Hv. destruct Hv as [Hin _]. exact Hin. }
      assert (HOpoly : in_hull (a :: b :: c :: rest) xO).
      { apply members_in_hull with (K := pO); [| exact HxO].
        intros v Hv. apply in_hull_in.
        apply filter_In in Hv. destruct Hv as [Hin _]. exact Hin. }
      assert (HMpoly : in_hull (a :: b :: c :: rest) (line_hit xI xO p q)).
      { rewrite HeqM. apply in_hull_conv; [exact HIpoly | exact HOpoly | exact HtM]. }
      destruct (hull_between_hits (a :: b :: c :: rest) p q aL bL aE bE
                  (line_hit xI xO p q) Hdist HaL HbL HaE HbE HsupL HsupE
                  HMpoly HzM) as [tC [HtC HeqC]].
      assert (HMclip : in_hull (clip_halfplane (a :: b :: c :: rest) p q)
                         (line_hit xI xO p q)).
      { rewrite HeqC. apply in_hull_conv.
        - apply in_hull_in. unfold clip_halfplane. rewrite Hpq.
          simpl. exact HinL.
        - apply in_hull_in. unfold clip_halfplane. rewrite Hpq.
          simpl. exact HinE.
        - exact HtC. }
      assert (HIclip : in_hull (clip_halfplane (a :: b :: c :: rest) p q) xI).
      { apply members_in_hull with (K := pI); [| exact HxI].
        intros v Hv. apply in_hull_in. apply filter_in_clip; [exact Hpq | simpl; lia | exact Hv]. }
      rewrite Hxu. apply in_hull_conv; [exact HIclip | exact HMclip | exact Hu01].
    + exfalso.
      assert (HsO1 : sO = 1) by lra.
      assert (Hzero : forall t, In t wI -> t = 0).
      { apply nonneg_sum0; [exact HnI | unfold sI in Hsi0; symmetry; exact Hsi0]. }
      assert (Hwi : wpt wI pI = mkPoint 0 0).
      { apply wpt_zeros; [exact HlenI | exact Hzero]. }
      assert (HxOeq : wpt wO pO = x).
      { destruct Hsplit as [Ex Ey].
        unfold wI, pI, wO, pO, drop in Ex, Ey, Hwi |- *.
        rewrite Hwi in Ex, Ey. rewrite Hp in Ex, Ey.
        replace (px (mkPoint 0 0)) with 0 in Ex by reflexivity.
        replace (py (mkPoint 0 0)) with 0 in Ey by reflexivity.
        rewrite Rplus_0_l in Ex, Ey.
        destruct x as [xx xy]. simpl in Ex, Ey.
        match goal with
        | |- ?L = ?R =>
            replace L with (mkPoint (px L) (py L)) by (destruct L; reflexivity);
            replace R with (mkPoint (px R) (py R)) by (destruct R; reflexivity)
        end.
        f_equal.
        - exact (eq_sym Ex).
        - exact (eq_sym Ey). }
      assert (HallO : forall v, In v pO -> cross p q v < 0).
      { intros v Hv. apply filter_In in Hv. destruct Hv as [_ Hd].
        apply negb_inside_cross. unfold drop, keep in Hd. exact Hd. }
      assert (Hneg : cross p q x < 0).
      { rewrite <- HxOeq. rewrite cross_wpt_sum1 by (try exact HlenO; unfold sO in HsO1; lra).
        apply cross_dot_neg; [exact HlenO | exact HnO | | exact HallO].
        unfold sO in HsO1. exact HsO1. }
      unfold inside_closed in HinC. lra.
  - (* sO = 0: x is a combination of inside vertices, all kept *)
    assert (HsI1 : sI = 1) by lra.
    assert (Hzero : forall t, In t wO -> t = 0).
    { apply nonneg_sum0; [exact HnO | unfold sO in Hso0; symmetry; exact Hso0]. }
    assert (Hwo : wpt wO pO = mkPoint 0 0).
    { apply wpt_zeros; [exact HlenO | exact Hzero]. }
    assert (HxI : wpt wI pI = x).
    { destruct Hsplit as [Ex Ey].
      unfold wI, pI, wO, pO, drop in Ex, Ey, Hwo |- *.
      rewrite Hwo in Ex, Ey. rewrite Hp in Ex, Ey.
      replace (px (mkPoint 0 0)) with 0 in Ex by reflexivity.
      replace (py (mkPoint 0 0)) with 0 in Ey by reflexivity.
      rewrite Rplus_0_r in Ex, Ey.
      destruct x as [xx xy]. simpl in Ex, Ey.
      match goal with
      | |- ?L = ?R =>
          replace L with (mkPoint (px L) (py L)) by (destruct L; reflexivity);
          replace R with (mkPoint (px R) (py R)) by (destruct R; reflexivity)
      end.
      f_equal.
      - exact (eq_sym Ex).
      - exact (eq_sym Ey). }
    assert (HinI : in_hull pI x).
    { unfold sI in HsI1.
      assert (Hr : in_hull pI (mkPoint (px (wpt wI pI) / rsum wI) (py (wpt wI pI) / rsum wI))).
      { apply in_hull_rescale; [exact HlenI | exact HnI | lra]. }
      replace x with (mkPoint (px (wpt wI pI) / rsum wI) (py (wpt wI pI) / rsum wI)).
      - exact Hr.
      - rewrite <- HxI. destruct (wpt wI pI) as [ux uy]. simpl.
        f_equal; rewrite HsI1; field. }
    apply members_in_hull with (K := pI); [| exact HinI].
    intros v Hv. apply in_hull_in. apply filter_in_clip; [exact Hpq | | exact Hv]. simpl. lia.
Qed.
Lemma in_hull_nil : forall x, in_hull [] x -> False.
Proof.
  intros x [w [Hl [_ [Hs _]]]].
  destruct w; simpl in Hl; try discriminate. simpl in Hs. exact (R1_neq_R0 (eq_sym Hs)).
Qed.
Lemma in_hull_one : forall a x, in_hull [a] x <-> x = a.
Proof.
  intros a x. split.
  - intros [w [Hl [_ [Hs Hp]]]].
    destruct w as [|t w]; simpl in Hl; try discriminate.
    destruct w; simpl in Hl; try discriminate.
    assert (Et : t = 1) by (simpl in Hs; lra).
    rewrite Et in Hp. simpl in Hp.
    replace (1 * px a + 0) with (px a) in Hp by ring.
    replace (1 * py a + 0) with (py a) in Hp by ring.
    destruct a as [ax ay], x as [xx xy]. simpl in Hp. inversion Hp. reflexivity.
  - intros ->. exists [1]. split; [reflexivity|].
    split.
    + intros z Hz. simpl in Hz. destruct Hz as [<-|[]]. lra.
    + split; [simpl; ring|]. simpl.
      destruct a as [ax ay]. simpl. f_equal; ring.
Qed.
Lemma inside_closed_b : forall p q x,
  inside_closed p q x -> inside_b p q x = true.
Proof.
  intros p q x H. unfold inside_b, inside_closed in *.
  destruct (Rle_dec 0 (cross p q x)); [reflexivity | exfalso; apply n; exact H].
Qed.
Theorem clip_correct : forall poly p q x,
  convex_supports poly ->
  in_hull (clip_halfplane poly p q) x <->
  in_hull poly x /\ inside_closed p q x.
Proof.
  intros poly p q x Hconv. split.
  - apply clip_sound.
  - intros [Hx Hin]. destruct (point_eqb p q) eqn:Epq.
    + apply point_eqb_true in Epq. subst q.
      unfold clip_halfplane. rewrite point_eqb_refl. exact Hx.
    + destruct poly as [|a [|b [|c rest]]].
      * exfalso. exact (in_hull_nil x Hx).
      * apply in_hull_one in Hx. subst x.
        unfold clip_halfplane. rewrite Epq. simpl.
        rewrite inside_closed_b by exact Hin.
        apply in_hull_one. reflexivity.
      * unfold clip_halfplane. rewrite Epq. simpl.
        apply seg_clip_complete; assumption.
      * apply clip_n3_complete; [exact Epq | simpl; lia | exact Hconv | exact Hx | exact Hin].
Qed.
(* CCW. A forward piece of a supporting edge stays supporting, and a chord    *)
(* along the clip line, oriented with the line, keeps the half-plane on its  *)
(* left. The clip walk emits only those two kinds of edge.                   *)
Lemma cross_subseg : forall a b s t x,
  cross (convex_combination a b s) (convex_combination a b t) x =
    (t - s) * cross a b x.
Proof.
  intros a b s t x. unfold cross, convex_combination.
  destruct a as [ax ay], b as [bx by_], x as [xx xy]. simpl. ring.
Qed.
Lemma subseg_left : forall a b s t x,
  0 <= s <= t ->
  0 <= cross a b x ->
  0 <= cross (convex_combination a b s) (convex_combination a b t) x.
Proof.
  intros a b s t x [Hs Ht] Hc. rewrite cross_subseg.
  apply Rmult_le_pos; lra.
Qed.
Lemma hull_cross_ge : forall a b poly x,
  (forall v, In v poly -> 0 <= cross a b v) ->
  in_hull poly x ->
  0 <= cross a b x.
Proof.
  intros a b poly x Hall [w [Hl [Hn [Hs Hx]]]].
  rewrite <- Hx. rewrite (cross_wpt_sum1 a b w poly Hl Hs).
  apply cross_dot_ge0; assumption.
Qed.
Lemma chord_left : forall p q u v x,
  points_distinct p q ->
  cross p q u = 0 ->
  cross p q v = 0 ->
  line_g p q u <= line_g p q v ->
  0 <= cross p q x ->
  0 <= cross u v x.
Proof.
  intros p q u v x Hdist Hu Hv Hg Hx.
  assert (Hd : 0 < dist_sq q p) by (apply dist_pos_distinct; exact Hdist).
  apply Rmult_le_reg_l with (r := dist_sq q p); [exact Hd|].
  rewrite Rmult_0_r. rewrite (chord_frame p q u v x Hu Hv).
  apply Rmult_le_pos; lra.
Qed.
Lemma g_leave_enter : forall poly p q aL bL aE bE,
  points_distinct p q ->
  inside_b p q aL = true -> inside_b p q bL = false ->
  inside_b p q aE = false -> inside_b p q bE = true ->
  (forall z, In z poly -> 0 <= cross aL bL z) ->
  In aE poly -> In bE poly ->
  line_g p q (line_hit aL bL p q) <= line_g p q (line_hit aE bE p q).
Proof.
  intros poly p q aL bL aE bE Hdist HaL HbL HaE HbE Hsup HinE HinB.
  assert (HdenE : cross p q aE - cross p q bE <> 0).
  { assert (Ha : cross p q aE < 0) by (apply inside_b_false; exact HaE).
    assert (Hb : 0 <= cross p q bE) by (apply inside_b_true; exact HbE).
    intro E.
    apply (Rlt_irrefl 0).
    apply Rlt_le_trans with (r2 := cross p q bE - cross p q aE).
    - apply Rlt_0_minus. apply Rlt_le_trans with (r2 := 0); [exact Ha | exact Hb].
    - replace (cross p q bE - cross p q aE)
        with (- (cross p q aE - cross p q bE)) by ring.
      rewrite E. lra. }
  assert (Hz : cross p q (line_hit aE bE p q) = 0)
    by (apply line_hit_on_line; exact HdenE).
  destruct (line_hit_on_seg aE bE p q) as [t [Ht [Heq _]]].
  { right. split; [apply inside_b_false; exact HaE | apply inside_b_true; exact HbE]. }
  assert (Hin : in_hull poly (line_hit aE bE p q)).
  { rewrite Heq. apply in_hull_conv; [apply in_hull_in; exact HinE |
                                       apply in_hull_in; exact HinB | exact Ht]. }
  assert (Hbound : forall v, In v poly ->
      line_g p q (line_hit aL bL p q) <=
      line_g p q v - line_mu p q aL bL * cross p q v).
  { intros v Hv. unfold line_mu. apply leave_psi_ge; try assumption.
    - apply inside_b_true. exact HaL.
    - apply inside_b_false. exact HbL.
    - apply Hsup. exact Hv. }
  assert (Hpsi := hull_psi_ge p q (line_mu p q aL bL)
            (line_g p q (line_hit aL bL p q)) poly (line_hit aE bE p q) Hbound Hin).
  rewrite Hz, Rmult_0_r, Rminus_0_r in Hpsi. exact Hpsi.
Qed.
Definition open_left (out all : list Point) : Prop :=
  match out with
  | [] => True
  | p :: r => chain_supports p r all
  end.
Fixpoint last_pt (prev : Point) (rest : list Point) : Point :=
  match rest with
  | [] => prev
  | c :: rest' => last_pt c rest'
  end.
Lemma last_pt_app : forall prev rest b,
  last_pt prev (rest ++ [b]) = b.
Proof.
  intros prev rest b. revert prev. induction rest as [|c rest IH]; intros prev; simpl; auto.
Qed.
Lemma chain_extend_last : forall prev rest all b L,
  chain_supports prev rest all ->
  last_pt prev rest = L ->
  (forall v, In v all -> 0 <= cross L b v) ->
  chain_supports prev (rest ++ [b]) all.
Proof.
  intros prev rest all b L. revert prev L.
  induction rest as [|c rest IH]; intros prev L Hs HL Hall; simpl in *.
  - subst L. split; [exact Hall | exact I].
  - destruct Hs as [Hedge Htail]. split; [exact Hedge |].
    apply IH with (L := L); [exact Htail | exact HL | exact Hall].
Qed.
Definition oplast (ps : list Point) : option Point :=
  match ps with
  | [] => None
  | p :: r => Some (last_pt p r)
  end.
Lemma oplast_snoc : forall acc e, oplast (acc ++ [e]) = Some e.
Proof.
  intros acc e. destruct acc as [|a acc]; simpl.
  - reflexivity.
  - rewrite last_pt_app. reflexivity.
Qed.
Lemma last_pt_end : forall prev xs y z,
  last_pt prev (xs ++ y :: z :: nil) = z.
Proof.
  intros prev xs y z. revert prev.
  induction xs as [|h xs IH]; intros prev; simpl; [reflexivity | apply IH].
Qed.
Lemma oplast_app_two : forall acc e1 e2, oplast (acc ++ [e1; e2]) = Some e2.
Proof.
  intros acc e1 e2. destruct acc as [|a acc]; simpl.
  - reflexivity.
  - rewrite last_pt_end. reflexivity.
Qed.
Lemma open_left_add : forall out all e,
  open_left out all ->
  match oplast out with
  | None => True
  | Some L => forall v, In v all -> 0 <= cross L e v
  end ->
  open_left (out ++ [e]) all.
Proof.
  intros out all e Ho Hedge.
  destruct out as [|p r]; simpl in *.
  - exact I.
  - apply chain_extend_last with (L := last_pt p r); [exact Ho | reflexivity |].
    exact Hedge.
Qed.
Lemma open_left_add2 : forall out all e1 e2,
  open_left out all ->
  match oplast out with
  | None => True
  | Some L => forall v, In v all -> 0 <= cross L e1 v
  end ->
  (forall v, In v all -> 0 <= cross e1 e2 v) ->
  open_left (out ++ [e1; e2]) all.
Proof.
  intros out all e1 e2 Ho Hj He.
  replace (out ++ [e1; e2]) with ((out ++ [e1]) ++ [e2])
    by (rewrite <- app_assoc; reflexivity).
  apply open_left_add.
  - apply open_left_add; [exact Ho | exact Hj].
  - rewrite oplast_snoc. exact He.
Qed.
Lemma comb0 : forall a b, convex_combination a b 0 = a.
Proof.
  intros a b. unfold convex_combination. destruct a, b. simpl. f_equal; ring.
Qed.
Lemma comb1 : forall a b, convex_combination a b 1 = b.
Proof.
  intros a b. unfold convex_combination. destruct a, b. simpl. f_equal; ring.
Qed.
Lemma subseg_from_start : forall a b t x,
  0 <= t ->
  0 <= cross a b x ->
  0 <= cross a (convex_combination a b t) x.
Proof.
  intros a b t x Ht Hx. rewrite <- (comb0 a b) at 1.
  apply subseg_left; [split; lra | exact Hx].
Qed.
Lemma subseg_to_end : forall a b t x,
  0 <= t <= 1 ->
  0 <= cross a b x ->
  0 <= cross (convex_combination a b t) b x.
Proof.
  intros a b t x Ht Hx. rewrite <- (comb1 a b) at 2.
  apply subseg_left; [exact Ht | exact Hx].
Qed.
(* Edges must keep the clipped region on the left: hull points that also
   lie in the closed half-plane. Outside vertices of the input need not. *)
Definition kept (poly : list Point) (p q v : Point) : Prop :=
  in_hull poly v /\ inside_closed p q v.
Fixpoint chain_P (prev : Point) (rest : list Point) (P : Point -> Prop) : Prop :=
  match rest with
  | [] => True
  | cur :: rs => (forall v, P v -> 0 <= cross prev cur v) /\ chain_P cur rs P
  end.
Definition open_P (out : list Point) (P : Point -> Prop) : Prop :=
  match out with
  | [] => True
  | h :: rs => chain_P h rs P
  end.
Lemma chain_P_extend : forall prev rest P b L,
  chain_P prev rest P ->
  last_pt prev rest = L ->
  (forall v, P v -> 0 <= cross L b v) ->
  chain_P prev (rest ++ [b]) P.
Proof.
  intros prev rest P b L. revert prev L.
  induction rest as [|c rest IH]; intros prev L Hs HL Hall; simpl in *.
  - subst L. split; [exact Hall | exact I].
  - destruct Hs as [Hedge Htail]. split; [exact Hedge |].
    apply IH with (L := L); [exact Htail | exact HL | exact Hall].
Qed.
Lemma open_P_add : forall out P e,
  open_P out P ->
  match oplast out with
  | None => True
  | Some L => forall v, P v -> 0 <= cross L e v
  end ->
  open_P (out ++ [e]) P.
Proof.
  intros out P e Ho Hedge.
  destruct out as [|h r]; simpl in *.
  - exact I.
  - apply chain_P_extend with (L := last_pt h r); [exact Ho | reflexivity | exact Hedge].
Qed.
Lemma open_P_add2 : forall out P e1 e2,
  open_P out P ->
  match oplast out with
  | None => True
  | Some L => forall v, P v -> 0 <= cross L e1 v
  end ->
  (forall v, P v -> 0 <= cross e1 e2 v) ->
  open_P (out ++ [e1; e2]) P.
Proof.
  intros out P e1 e2 Ho Hj He.
  replace (out ++ [e1; e2]) with ((out ++ [e1]) ++ [e2])
    by (rewrite <- app_assoc; reflexivity).
  apply open_P_add.
  - apply open_P_add; [exact Ho | exact Hj].
  - rewrite oplast_snoc. exact He.
Qed.
Lemma hit_den_nz : forall p q a b,
  inside_b p q a = true -> inside_b p q b = false ->
  cross p q a - cross p q b <> 0.
Proof.
  intros p q a b Ha Hb E.
  assert (Ha' : 0 <= cross p q a) by (apply inside_b_true; exact Ha).
  assert (Hb' : cross p q b < 0) by (apply inside_b_false; exact Hb).
  apply Rminus_diag_uniq in E.
  rewrite E in Ha'. apply (Rle_not_lt _ _ Ha'). exact Hb'.
Qed.
(* What the most recent emission was, relative to the vertex the walk is
   about to leave. None means nothing has been emitted on this outside or
   inside run yet. *)
Definition phase_ok (poly : list Point) (p q prev : Point) (L : option Point) : Prop :=
  match inside_b p q prev, L with
  | true, None => True
  | true, Some v => v = prev
  | false, None => True
  | false, Some v =>
      exists a b,
        v = line_hit a b p q /\
        In a poly /\ In b poly /\
        inside_b p q a = true /\ inside_b p q b = false /\
        (forall z, In z poly -> 0 <= cross a b z)
  end.
Lemma clip_acc_left : forall prev rest poly p q acc,
  point_eqb p q = false ->
  chain_supports prev rest poly ->
  (forall u, In u (prev :: rest) -> In u poly) ->
  open_P acc (kept poly p q) ->
  phase_ok poly p q prev (oplast acc) ->
  open_P (acc ++ clip_chain prev rest p q) (kept poly p q) /\
  phase_ok poly p q (last_pt prev rest)
    (oplast (acc ++ clip_chain prev rest p q)).
Proof.
  intros prev rest poly p q. revert prev.
  induction rest as [|cur rest IH]; intros prev acc Hpq Hs Hin Ho Hp.
  - simpl. rewrite app_nil_r. split; [exact Ho | exact Hp].
  - simpl in Hs. destruct Hs as [Hedge Htail].
    assert (Hdist : points_distinct p q)
      by (apply point_eqb_false_distinct; exact Hpq).
    assert (Hprev : In prev poly) by (apply Hin; simpl; left; reflexivity).
    assert (Hcur : In cur poly) by (apply Hin; simpl; right; left; reflexivity).
    assert (Hnext : forall u, In u (cur :: rest) -> In u poly).
    { intros u Hu. apply Hin. simpl in Hu. destruct Hu as [->|Hu];
        [simpl; right; left; reflexivity | simpl; right; right; exact Hu]. }
    cbn [clip_chain].
    replace (acc ++ (emit_edge prev cur p q ++ clip_chain cur rest p q))
      with ((acc ++ emit_edge prev cur p q) ++ clip_chain cur rest p q)
      by (rewrite app_assoc; reflexivity).
    destruct (inside_b p q prev) eqn:Hip;
    destruct (inside_b p q cur) eqn:Hic.
    + unfold emit_edge. rewrite Hip, Hic.
      apply IH with (prev := cur); [exact Hpq | exact Htail | exact Hnext | |].
      * apply open_P_add; [exact Ho |].
        destruct (oplast acc) as [L|] eqn:HL; [| exact I].
        intros v Hv. unfold phase_ok in Hp. rewrite Hip in Hp. subst L.
        destruct Hv as [Hhull _]. apply hull_cross_ge with (poly := poly); assumption.
      * unfold phase_ok. rewrite Hic, oplast_snoc. reflexivity.
    + unfold emit_edge. rewrite Hip, Hic.
      apply IH with (prev := cur); [exact Hpq | exact Htail | exact Hnext | |].
      * apply open_P_add; [exact Ho |].
        destruct (oplast acc) as [L|] eqn:HL; [| exact I].
        intros v Hv. unfold phase_ok in Hp. rewrite Hip in Hp. subst L.
        destruct Hv as [Hhull _].
        destruct (line_hit_on_seg prev cur p q) as [t [Ht [Heq _]]].
        { left. split; [apply inside_b_true; exact Hip | apply inside_b_false; exact Hic]. }
        destruct Ht as [Ht0 _].
        rewrite Heq. apply subseg_from_start; [exact Ht0 |].
        apply hull_cross_ge with (poly := poly); assumption.
      * unfold phase_ok. rewrite Hic, oplast_snoc.
        exists prev, cur. repeat split; try assumption; auto.
    + unfold emit_edge. rewrite Hip, Hic.
      apply IH with (prev := cur); [exact Hpq | exact Htail | exact Hnext | |].
      * apply open_P_add2; [exact Ho | |].
        -- destruct (oplast acc) as [L|] eqn:HL; [| exact I].
           intros v Hv. unfold phase_ok in Hp. rewrite Hip in Hp.
           destruct Hp as [aL [bL [HLv [HinL [HinR [HaL [HbL Hsup]]]]]]].
           subst L. destruct Hv as [_ Hinside].
           destruct (line_hit_on_seg prev cur p q) as [tE [HtE [HeqE HzE]]].
           { right. split; [apply inside_b_false; exact Hip | apply inside_b_true; exact Hic]. }
           assert (HzL : cross p q (line_hit aL bL p q) = 0).
           { apply line_hit_on_line. apply hit_den_nz; assumption. }
           apply chord_left with (p := p) (q := q).
           { exact Hdist. }
           { exact HzL. }
           { exact HzE. }
           { apply g_leave_enter with (poly := poly); assumption. }
           { exact Hinside. }
        -- intros v Hv. destruct Hv as [Hhull _].
           destruct (line_hit_on_seg prev cur p q) as [t [Ht [Heq _]]].
           { right. split; [apply inside_b_false; exact Hip | apply inside_b_true; exact Hic]. }
           rewrite Heq. apply subseg_to_end; [exact Ht |].
           apply hull_cross_ge with (poly := poly); assumption.
      * unfold phase_ok. rewrite Hic, oplast_app_two. reflexivity.
    + unfold emit_edge. rewrite Hip, Hic. rewrite app_nil_r.
      apply IH with (prev := cur); [exact Hpq | exact Htail | exact Hnext | exact Ho |].
      unfold phase_ok in Hp. unfold phase_ok. rewrite Hip in Hp. rewrite Hic.
      destruct (oplast acc) as [L|] eqn:HL.
      * destruct Hp as [aL [bL Hleave]]. exists aL, bL. exact Hleave.
      * exact I.
Qed.
Lemma chain_P_In : forall prev rest (P : Point -> Prop) all,
  chain_P prev rest P ->
  (forall v, In v all -> P v) ->
  chain_supports prev rest all.
Proof.
  intros prev rest P all. revert prev.
  induction rest as [|c rest IH]; intros prev Hs Hall; simpl in *.
  - exact I.
  - destruct Hs as [He Ht]. split.
    + intros v Hv. apply He, Hall, Hv.
    + apply IH; assumption.
Qed.
Lemma convex_short : forall ps, (length ps < 3)%nat -> convex_supports ps.
Proof.
  intros [|a [|b [|c r]]] H.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
  - simpl in H. lia.
Qed.
Lemma seg_clip_short : forall a b p q, (length (seg_clip a b p q) <= 2)%nat.
Proof.
  intros a b p q. unfold seg_clip.
  destruct (inside_b p q a); destruct (inside_b p q b); simpl; lia.
Qed.
Lemma clip_short_out : forall poly p q,
  (length poly < 3)%nat ->
  (length (clip_halfplane poly p q) < 3)%nat.
Proof.
  intros poly p q H. unfold clip_halfplane.
  destruct (point_eqb p q).
  - exact H.
  - destruct poly as [|a [|b [|c r]]]; simpl in H |- *.
    + lia.
    + destruct (inside_b p q a); simpl; lia.
    + pose proof (seg_clip_short a b p q). lia.
    + lia.
Qed.
Lemma clip_chain_end_in : forall prev rest a p q,
  inside_b p q a = true ->
  exists pre, clip_chain prev (rest ++ [a]) p q = pre ++ [a].
Proof.
  intros prev rest a p q Ha. revert prev.
  induction rest as [|c rest IH]; intros prev.
  - simpl. unfold emit_edge. rewrite Ha. destruct (inside_b p q prev).
    + exists []. reflexivity.
    + exists [line_hit prev a p q]. reflexivity.
  - simpl. destruct (IH c) as [pre Hpre]. rewrite Hpre.
    exists (emit_edge prev c p q ++ pre). rewrite app_assoc. reflexivity.
Qed.
Lemma clip_head_enter : forall prev rest p q h t,
  inside_b p q prev = false ->
  clip_chain prev rest p q = h :: t ->
  exists a b,
    h = line_hit a b p q /\
    inside_b p q a = false /\ inside_b p q b = true /\
    In a (prev :: rest) /\ In b (prev :: rest).
Proof.
  intros prev rest p q. revert prev.
  induction rest as [|cur rest IH]; intros prev h t Hp Heq; simpl in Heq.
  - discriminate.
  - unfold emit_edge in Heq. rewrite Hp in Heq.
    destruct (inside_b p q cur) eqn:Hc; simpl in Heq.
    + injection Heq as Eh _. exists prev, cur.
      split; [symmetry; exact Eh |].
      repeat split; try assumption; simpl; tauto.
    + destruct (IH cur h t Hc Heq) as [a [b [Hh [Ha [Hb [Ia Ib]]]]]].
      exists a, b. repeat split; try assumption; simpl; right; assumption.
Qed.
Lemma walk_in_poly : forall (a u : Point) (rest : list Point),
  In u (a :: rest ++ [a]) -> In u (a :: rest).
Proof.
  intros a u rest. induction rest as [|c rest IH]; simpl; intros Hu.
  - destruct Hu as [<-|[<-|[]]].
    + left. reflexivity.
    + left. reflexivity.
  - destruct Hu as [<-|Hu].
    + left. reflexivity.
    + destruct Hu as [<-|Hu].
      * right. left. reflexivity.
      * assert (Hin : In u (a :: rest)).
        { apply IH. right. exact Hu. }
        destruct Hin as [<-|Hin].
        -- left. reflexivity.
        -- right. right. exact Hin.
Qed.
Theorem clip_convex_ccw : forall poly p q,
  convex_supports poly ->
  convex_supports (clip_halfplane poly p q).
Proof.
  intros poly p q Hconv.
  destruct (point_eqb p q) eqn:Epq.
  - apply point_eqb_true in Epq. subst q.
    unfold clip_halfplane. rewrite point_eqb_refl. exact Hconv.
  - destruct (lt_dec (length (clip_halfplane poly p q)) 3) as [Hshort|Hlong].
    + apply convex_short. exact Hshort.
    + assert (Hlen : (3 <= length poly)%nat).
      { destruct (lt_dec (length poly) 3) as [Hs|Hl].
        - pose proof (clip_short_out poly p q Hs) as Ho. lia.
        - lia. }
      destruct poly as [|a [|b [|c rest0]]]; simpl in Hlen; try lia.
      unfold clip_halfplane. rewrite Epq.
      set (walk := (b :: c :: rest0) ++ [a]).
      set (out := clip_chain a walk p q).
      assert (Hwalk_in : forall u, In u (a :: walk) -> In u (a :: b :: c :: rest0)).
      { intros u Hu. unfold walk in Hu. apply walk_in_poly. exact Hu. }
      assert (Hsup : chain_supports a walk (a :: b :: c :: rest0)).
      { unfold convex_supports in Hconv. simpl in Hconv. unfold walk. exact Hconv. }
      assert (Hacc := clip_acc_left a walk (a :: b :: c :: rest0) p q []
                        Epq Hsup Hwalk_in I).
      assert (Hphase_prev : phase_ok (a :: b :: c :: rest0) p q a None).
      { unfold phase_ok. destruct (inside_b p q a); exact I. }
      destruct (Hacc Hphase_prev) as [Hopen Hphase].
      assert (Hend : last_pt a walk = a) by (unfold walk; rewrite last_pt_app; reflexivity).
      rewrite Hend in Hphase. rewrite !app_nil_l in Hopen, Hphase.
      set (poly3 := a :: b :: c :: rest0).
      assert (Hkept : forall v, In v out -> kept poly3 p q v).
      { intros v Hv. unfold kept. apply clip_verts_ok.
        unfold out in Hv. unfold clip_halfplane. rewrite Epq. exact Hv. }
      change (convex_supports out). destruct out as [|h r] eqn:Hoeq.
      * simpl. exact I.
      * destruct r as [|h2 r2].
        -- simpl. exact I.
        -- destruct (lt_dec (length (h :: h2 :: r2)) 3) as [Hs|Hl].
           ++ apply convex_short. exact Hs.
           ++               assert (Echain : clip_chain a walk p q = h :: h2 :: r2).
              { unfold out in Hoeq. exact Hoeq. }
              assert (Hedge0 : forall v, In v poly3 -> 0 <= cross a b v).
              { unfold poly3. destruct Hsup as [He _]. exact He. }
              assert (Hwrap : forall v, kept poly3 p q v ->
                         0 <= cross (last_pt h (h2 :: r2)) h v).
              { intros v Hv.
                destruct (inside_b p q a) eqn:Ha.
                - assert (Hphase' := Hphase).
                  unfold phase_ok in Hphase'. rewrite Ha in Hphase'.
                  rewrite Echain in Hphase'. simpl in Hphase'. simpl. rewrite Hphase'.
                  unfold out in Hoeq. unfold walk in Hoeq.
                  simpl in Hoeq. unfold emit_edge in Hoeq. rewrite Ha in Hoeq.
                  destruct (inside_b p q b) eqn:Hb.
                  + injection Hoeq as Eh _. symmetry in Eh. subst h.
                    destruct Hv as [Hhull _].
                    apply hull_cross_ge with (poly := poly3); assumption.
                  + injection Hoeq as Eh _. symmetry in Eh. subst h.
                    destruct Hv as [Hhull _].
                    destruct (line_hit_on_seg a b p q) as [t [Ht [Heq _]]].
                    { left. split; [apply inside_b_true; exact Ha |
                                    apply inside_b_false; exact Hb]. }
                    destruct Ht as [Ht0 _]. rewrite Heq.
                    apply subseg_from_start; [exact Ht0 |].
                    apply hull_cross_ge with (poly := poly3); assumption.
                - assert (Hphase' := Hphase).
                  unfold phase_ok in Hphase'. rewrite Ha in Hphase'.
                  rewrite Echain in Hphase'. simpl in Hphase'. simpl.
                  destruct Hphase' as [aL [bL [HL [HinL [HinR [HaL [HbL HsupL]]]]]]].
                  rewrite HL.
                  assert (Hent : exists aE bE,
                      h = line_hit aE bE p q /\
                      inside_b p q aE = false /\ inside_b p q bE = true /\
                      In aE (a :: walk) /\ In bE (a :: walk)).
                  { apply (clip_head_enter a walk p q h (h2 :: r2) Ha).
                    unfold out in Hoeq. exact Hoeq. }
                  destruct Hent as [aE [bE [Hh [HaE [HbE [Ia Ib]]]]]].
                  subst h.
                  destruct Hv as [_ Hinside].
                  assert (HzL : cross p q (line_hit aL bL p q) = 0).
                  { apply line_hit_on_line. apply hit_den_nz; assumption. }
                  assert (HdenE : cross p q aE - cross p q bE <> 0).
                  { assert (Hout : cross p q aE < 0) by (apply inside_b_false; exact HaE).
                    assert (HinB : 0 <= cross p q bE) by (apply inside_b_true; exact HbE).
                    intro E0. apply (Rlt_irrefl 0).
                    apply Rlt_le_trans with (r2 := cross p q bE - cross p q aE).
                    - apply Rlt_0_minus.
                      apply Rlt_le_trans with (r2 := 0); [exact Hout | exact HinB].
                    - replace (cross p q bE - cross p q aE)
                        with (- (cross p q aE - cross p q bE)) by ring.
                      rewrite E0. lra. }
                  assert (HzE : cross p q (line_hit aE bE p q) = 0).
                  { apply line_hit_on_line. exact HdenE. }
                  assert (Hdist : points_distinct p q)
                    by (apply point_eqb_false_distinct; exact Epq).
                  apply chord_left with (p := p) (q := q).
                  + exact Hdist.
                  + exact HzL.
                  + exact HzE.
                  + apply g_leave_enter with (poly := poly3).
                    * exact Hdist.
                    * exact HaL.
                    * exact HbL.
                    * exact HaE.
                    * exact HbE.
                    * exact HsupL.
                    * apply Hwalk_in. exact Ia.
                    * apply Hwalk_in. exact Ib.
                  + exact Hinside. }
              assert (Hchain : chain_P h ((h2 :: r2) ++ [h]) (kept poly3 p q)).
              { rewrite Echain in Hopen. simpl in Hopen.
                apply chain_P_extend with (L := last_pt h (h2 :: r2)).
                - exact Hopen.
                - reflexivity.
                - exact Hwrap. }
              assert (HinOut : forall v, In v (h :: h2 :: r2) -> kept poly3 p q v).
              { intros v Hv. apply Hkept. exact Hv. }
              assert (Hcs : chain_supports h ((h2 :: r2) ++ [h]) (h :: h2 :: r2)).
              { apply chain_P_In with (P := kept poly3 p q); assumption. }
              destruct r2 as [|h3 r3]; [simpl in Hl; lia|].
              unfold convex_supports. simpl.
              exact Hcs.
Qed.
(* Rational coordinates survive an exact hit. The denominator is the cross    *)
(* difference, nonzero exactly when the edge changes side.                    *)
Definition coord_Q (x : R) : Prop := exists q : Q, Q2R q = x.
Definition point_Q (v : Point) : Prop := coord_Q (px v) /\ coord_Q (py v).
Definition list_Q (ps : list Point) : Prop := forall v, In v ps -> point_Q v.
Lemma coord_Q_add : forall x y, coord_Q x -> coord_Q y -> coord_Q (x + y).
Proof.
  intros x y [qx Hx] [qy Hy]. exists (qx + qy)%Q.
  rewrite Q2R_plus, Hx, Hy. reflexivity.
Qed.
Lemma coord_Q_opp : forall x, coord_Q x -> coord_Q (- x).
Proof.
  intros x [qx Hx]. exists (- qx)%Q. rewrite Q2R_opp, Hx. reflexivity.
Qed.
Lemma coord_Q_sub : forall x y, coord_Q x -> coord_Q y -> coord_Q (x - y).
Proof.
  intros x y Hx Hy. unfold Rminus. apply coord_Q_add; [| apply coord_Q_opp]; assumption.
Qed.
Lemma coord_Q_mul : forall x y, coord_Q x -> coord_Q y -> coord_Q (x * y).
Proof.
  intros x y [qx Hx] [qy Hy]. exists (qx * qy)%Q.
  rewrite Q2R_mult, Hx, Hy. reflexivity.
Qed.
Lemma coord_Q_div : forall x y, coord_Q x -> coord_Q y -> y <> 0 -> coord_Q (x / y).
Proof.
  intros x y [qx Hx] [qy Hy] Hnz. exists (qx / qy)%Q. rewrite Q2R_div.
  - rewrite Hx, Hy. reflexivity.
  - intro Hq. apply Hnz. rewrite <- Hy. rewrite (Qeq_eqR _ _ Hq).
    apply RMicromega.Q2R_0.
Qed.
Lemma cross_Q : forall p q a,
  point_Q p -> point_Q q -> point_Q a -> coord_Q (cross p q a).
Proof.
  intros p q a [Hpx Hpy] [Hqx Hqy] [Hax Hay]. unfold cross.
  apply coord_Q_sub.
  - apply coord_Q_mul; apply coord_Q_sub; assumption.
  - apply coord_Q_mul; apply coord_Q_sub; assumption.
Qed.
Lemma point_Q_mk : forall x y, coord_Q x -> coord_Q y -> point_Q (mkPoint x y).
Proof. intros x y Hx Hy. split; assumption. Qed.
Lemma hit_den_nz_enter : forall p q a b,
  inside_b p q a = false -> inside_b p q b = true ->
  cross p q a - cross p q b <> 0.
Proof.
  intros p q a b Ha Hb E.
  assert (Ha' : cross p q a < 0) by (apply inside_b_false; exact Ha).
  assert (Hb' : 0 <= cross p q b) by (apply inside_b_true; exact Hb).
  apply Rminus_diag_uniq in E. apply (Rlt_irrefl 0).
  apply Rle_lt_trans with (r2 := cross p q a).
  - rewrite E. exact Hb'.
  - exact Ha'.
Qed.
Lemma line_hit_Q : forall a b p q,
  point_Q a -> point_Q b -> point_Q p -> point_Q q ->
  cross p q a - cross p q b <> 0 ->
  point_Q (line_hit a b p q).
Proof.
  intros a b p q Ha Hb Hp Hq Hd.
  assert (Hfa : coord_Q (cross p q a)) by (apply cross_Q; assumption).
  assert (Hfb : coord_Q (cross p q b)) by (apply cross_Q; assumption).
  assert (Hden : coord_Q (cross p q a - cross p q b))
    by (apply coord_Q_sub; assumption).
  destruct Ha as [Hax Hay], Hb as [Hbx Hby]. unfold line_hit. split; simpl.
  - apply coord_Q_add; [exact Hax|]. apply coord_Q_mul.
    + apply coord_Q_div; assumption.
    + apply coord_Q_sub; [exact Hbx | exact Hax].
  - apply coord_Q_add; [exact Hay|]. apply coord_Q_mul.
    + apply coord_Q_div; assumption.
    + apply coord_Q_sub; [exact Hby | exact Hay].
Qed.
Lemma emit_edge_Q : forall a b p q v,
  point_Q a -> point_Q b -> point_Q p -> point_Q q ->
  In v (emit_edge a b p q) -> point_Q v.
Proof.
  intros a b p q v Ha Hb Hp Hq Hin. unfold emit_edge in Hin.
  destruct (inside_b p q a) eqn:Ia; destruct (inside_b p q b) eqn:Ib; simpl in Hin.
  - destruct Hin as [<-|[]]. exact Hb.
  - destruct Hin as [<-|[]]. apply line_hit_Q; try assumption. apply hit_den_nz; assumption.
  - destruct Hin as [<-|[<-|[]]].
    + apply line_hit_Q; try assumption. apply hit_den_nz_enter; assumption.
    + exact Hb.
  - contradiction.
Qed.
Lemma seg_clip_Q : forall a b p q v,
  point_Q a -> point_Q b -> point_Q p -> point_Q q ->
  In v (seg_clip a b p q) -> point_Q v.
Proof.
  intros a b p q v Ha Hb Hp Hq Hin. unfold seg_clip in Hin.
  destruct (inside_b p q a) eqn:Ia; destruct (inside_b p q b) eqn:Ib; simpl in Hin.
  - destruct Hin as [<-|[<-|[]]]; assumption.
  - destruct Hin as [<-|[<-|[]]].
    + exact Ha.
    + apply line_hit_Q; try assumption. apply hit_den_nz; assumption.
  - destruct Hin as [<-|[<-|[]]].
    + apply line_hit_Q; try assumption. apply hit_den_nz_enter; assumption.
    + exact Hb.
  - contradiction.
Qed.
Lemma clip_chain_Q : forall prev rest p q v,
  point_Q prev -> point_Q p -> point_Q q ->
  (forall u, In u rest -> point_Q u) ->
  In v (clip_chain prev rest p q) -> point_Q v.
Proof.
  intros prev rest p q. revert prev.
  induction rest as [|cur rest IH]; intros prev v Hp Hp' Hq Hall Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + apply emit_edge_Q with (a := prev) (b := cur) (p := p) (q := q).
      * exact Hp.
      * apply Hall. simpl. left. reflexivity.
      * exact Hp'.
      * exact Hq.
      * exact Hin.
    + apply IH with (prev := cur).
      * apply Hall. simpl. left. reflexivity.
      * exact Hp'.
      * exact Hq.
      * intros u Hu. apply Hall. simpl. right. exact Hu.
      * exact Hin.
Qed.
Theorem clip_rational : forall poly p q,
  list_Q poly -> point_Q p -> point_Q q ->
  list_Q (clip_halfplane poly p q).
Proof.
  intros poly p q Hpoly Hp Hq v Hin.
  destruct (point_eqb p q) eqn:Epq.
  - unfold clip_halfplane in Hin. rewrite Epq in Hin. apply Hpoly. exact Hin.
  - unfold clip_halfplane in Hin. rewrite Epq in Hin.
    destruct poly as [|a [|b [|c rest]]].
    + contradiction.
    + simpl in Hin. destruct (inside_b p q a); [| contradiction].
      destruct Hin as [<-|[]]. apply Hpoly. simpl. left. reflexivity.
    + apply seg_clip_Q with (a := a) (b := b) (p := p) (q := q).
      * apply Hpoly. simpl. left. reflexivity.
      * apply Hpoly. simpl. right. left. reflexivity.
      * exact Hp.
      * exact Hq.
      * exact Hin.
    + apply clip_chain_Q with (prev := a) (rest := (b :: c :: rest) ++ [a]) (p := p) (q := q).
      * apply Hpoly. simpl. left. reflexivity.
      * exact Hp.
      * exact Hq.
      * intros u Hu. apply in_app_or in Hu. destruct Hu as [Hu|Hu].
        -- apply Hpoly. simpl. right. exact Hu.
        -- destruct Hu as [<-|[]]. apply Hpoly. simpl. left. reflexivity.
      * exact Hin.
Qed.

(* Assumptions: sig_not_dec, sig_forall_dec, functional_extensionality_dep. *)
Print Assumptions take_w_length.
Print Assumptions take_w_nonneg.
Print Assumptions rsum_take_split.
Print Assumptions wpt_take_split.
Print Assumptions cross_dot_scale.
Print Assumptions in_hull_rescale.
Print Assumptions take_pos_existsb.
Print Assumptions filter_in_clip.
Print Assumptions negb_inside_cross.
Print Assumptions clip_n3_complete.
Print Assumptions in_hull_nil.
Print Assumptions in_hull_one.
Print Assumptions inside_closed_b.
Print Assumptions clip_correct.
Print Assumptions cross_subseg.
Print Assumptions subseg_left.
Print Assumptions hull_cross_ge.
Print Assumptions chord_left.
Print Assumptions g_leave_enter.
Print Assumptions last_pt_app.
Print Assumptions chain_extend_last.
Print Assumptions oplast_snoc.
Print Assumptions last_pt_end.
Print Assumptions oplast_app_two.
Print Assumptions open_left_add.
Print Assumptions open_left_add2.
Print Assumptions comb0.
Print Assumptions comb1.
Print Assumptions subseg_from_start.
Print Assumptions subseg_to_end.
Print Assumptions chain_P_extend.
Print Assumptions open_P_add.
Print Assumptions open_P_add2.
Print Assumptions hit_den_nz.
Print Assumptions clip_acc_left.
Print Assumptions chain_P_In.
Print Assumptions convex_short.
Print Assumptions seg_clip_short.
Print Assumptions clip_short_out.
Print Assumptions clip_chain_end_in.
Print Assumptions clip_head_enter.
Print Assumptions walk_in_poly.
Print Assumptions clip_convex_ccw.
Print Assumptions coord_Q_add.
Print Assumptions coord_Q_opp.
Print Assumptions coord_Q_sub.
Print Assumptions coord_Q_mul.
Print Assumptions coord_Q_div.
Print Assumptions cross_Q.
Print Assumptions point_Q_mk.
Print Assumptions hit_den_nz_enter.
Print Assumptions line_hit_Q.
Print Assumptions emit_edge_Q.
Print Assumptions seg_clip_Q.
Print Assumptions clip_chain_Q.
Print Assumptions clip_rational.
