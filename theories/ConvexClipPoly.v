(* NetTopologySuite.Proofs.ConvexClipPoly
   Polygon-level half-plane clip: soundness for every list, completeness
   for convex polygons of length at most 5 (what tri_inter consumes),
   CCW preservation, and rational vertices.
   topic: relate
   claimId: tri-de9im-a
   witness: TrianglePairClip.ii_nonempty_iff
   secondary witness: ConvexClipComplete.clip_correct
   3-axiom host. No Admitted. AI-drafted (Cursor Grok 4.7), human-reviewed.
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra Lia List QArith Qreals.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex RingArea979 ConvexClip.
Local Open Scope R_scope.
Definition line_g (p q x : Point) : R :=
  (px q - px p) * (px x - px p) + (py q - py p) * (py x - py p).
Lemma g_affine : forall p q a b t,
  line_g p q (convex_combination a b t) =
    (1 - t) * line_g p q a + t * line_g p q b.
Proof.
  intros. unfold line_g, convex_combination. destruct a, b. simpl. ring.
Qed.
Lemma g_line_hit : forall p q a b,
  cross p q a - cross p q b <> 0 ->
  line_g p q (line_hit a b p q) =
    (cross p q a * line_g p q b - cross p q b * line_g p q a)
    / (cross p q a - cross p q b).
Proof.
  intros p q a b Hd. rewrite line_hit_combo, g_affine. field. exact Hd.
Qed.
Lemma g_hit_cleared : forall p q A B D,
  (cross p q B * line_g p q D - cross p q D * line_g p q B)
    * (cross p q A - cross p q D)
  - (cross p q A * line_g p q D - cross p q D * line_g p q A)
    * (cross p q B - cross p q D)
  = dist_sq q p * cross p q D * cross D A B.
Proof.
  intros. unfold line_g, cross, dist_sq. destruct p, q, A, B, D. simpl. ring.
Qed.
Lemma frame_inj : forall p q x y,
  line_g p q x = line_g p q y ->
  cross p q x = cross p q y ->
  dist_sq q p <> 0 ->
  x = y.
Proof.
  intros p q x y Hg Hf Hd.
  destruct p as [px0 py0], q as [qx qy], x as [xx xy], y as [yx yy].
  unfold line_g, cross, dist_sq in *. simpl in *.
  assert (E1 : (qx - px0) * (xx - yx) + (qy - py0) * (xy - yy) = 0).
  { replace ((qx - px0) * (xx - yx) + (qy - py0) * (xy - yy))
      with (((qx - px0) * (xx - px0) + (qy - py0) * (xy - py0))
          - ((qx - px0) * (yx - px0) + (qy - py0) * (yy - py0))) by ring.
    rewrite Hg. ring. }
  assert (E2 : (qx - px0) * (xy - yy) - (xx - yx) * (qy - py0) = 0).
  { replace ((qx - px0) * (xy - yy) - (xx - yx) * (qy - py0))
      with (((qx - px0) * (xy - py0) - (xx - px0) * (qy - py0))
          - ((qx - px0) * (yy - py0) - (yx - px0) * (qy - py0))) by ring.
    rewrite Hf. ring. }
  assert (Dx : ((qx - px0) * (qx - px0) + (qy - py0) * (qy - py0)) * (xx - yx) = 0).
  { replace (((qx - px0) * (qx - px0) + (qy - py0) * (qy - py0)) * (xx - yx))
      with ((qx - px0) * ((qx - px0) * (xx - yx) + (qy - py0) * (xy - yy))
          - (qy - py0) * ((qx - px0) * (xy - yy) - (xx - yx) * (qy - py0))) by ring.
    rewrite E1, E2. ring. }
  assert (Dy : ((qx - px0) * (qx - px0) + (qy - py0) * (qy - py0)) * (xy - yy) = 0).
  { replace (((qx - px0) * (qx - px0) + (qy - py0) * (qy - py0)) * (xy - yy))
      with ((qy - py0) * ((qx - px0) * (xx - yx) + (qy - py0) * (xy - yy))
          + (qx - px0) * ((qx - px0) * (xy - yy) - (xx - yx) * (qy - py0))) by ring.
    rewrite E1, E2. ring. }
  apply Rmult_integral in Dx. apply Rmult_integral in Dy.
  destruct Dx as [Hd0|Hx]; [exfalso; exact (Hd Hd0)|].
  destruct Dy as [Hd1|Hy]; [exfalso; exact (Hd Hd1)|].
  f_equal; lra.
Qed.
Lemma on_line_between : forall p q h1 h2 m,
  points_distinct p q ->
  cross p q h1 = 0 -> cross p q h2 = 0 -> cross p q m = 0 ->
  (line_g p q h1 <= line_g p q m /\ line_g p q m <= line_g p q h2) \/
  (line_g p q h2 <= line_g p q m /\ line_g p q m <= line_g p q h1) ->
  exists t, 0 <= t <= 1 /\ m = convex_combination h1 h2 t.
Proof.
  intros p q h1 h2 m Hdist Hz1 Hz2 Hzm Hg.
  set (g1 := line_g p q h1). set (g2 := line_g p q h2). set (gm := line_g p q m).
  assert (Hd : dist_sq q p <> 0).
  { assert (HneP : ~ (px q = px p /\ py q = py p)).
    { intros [Ex Ey]. unfold points_distinct in Hdist.
      destruct p as [ap bp], q as [aq bq]. simpl in *.
      destruct Hdist as [H|H]; congruence. }
    assert (Hp : 0 < dist_sq q p).
    { apply dist_sq_pos_iff_distinct. exact HneP. }
    lra. }
  destruct (Req_dec_T g1 g2) as [He|Hne].
  - assert (E12 : h1 = h2).
    { apply (frame_inj p q); [unfold g1, g2 in He; exact He |
        rewrite Hz1, Hz2; reflexivity | exact Hd]. }
    assert (Egm : gm = g1).
    { destruct Hg as [[H1 H2]|[H1 H2]].
      - change (line_g p q h1) with g1 in H1.
        change (line_g p q h2) with g2 in H2.
        change (line_g p q m) with gm in H1.
        change (line_g p q m) with gm in H2.
        apply Rle_antisym; [rewrite <- He in H2; exact H2 | exact H1].
      - change (line_g p q h1) with g1 in H2.
        change (line_g p q h2) with g2 in H1.
        change (line_g p q m) with gm in H1.
        change (line_g p q m) with gm in H2.
        apply Rle_antisym; [exact H2 | rewrite <- He in H1; exact H1]. }
    assert (Em : m = h1).
    { apply (frame_inj p q); [| rewrite Hzm, Hz1; reflexivity | exact Hd].
      unfold gm, g1 in Egm. exact Egm. }
    exists 0. split; [lra|]. rewrite Em, E12. unfold convex_combination.
    destruct h2. simpl. f_equal; ring.
  - set (t := (gm - g1) / (g2 - g1)).
    assert (Ht : 0 <= t <= 1).
    { unfold t. destruct Hg as [[Ha Hb]|[Ha Hb]].
      - change (line_g p q h1) with g1 in Ha.
        change (line_g p q h2) with g2 in Hb.
        change (line_g p q m) with gm in Ha.
        change (line_g p q m) with gm in Hb.
        assert (Hle : g1 <= g2) by (apply Rle_trans with gm; assumption).
        assert (Hlt12 : g1 < g2).
        { destruct (Rle_lt_or_eq_dec g1 g2 Hle) as [Hlt|Heq];
            [exact Hlt | exfalso; exact (Hne Heq)]. }
        assert (Hden : 0 < g2 - g1).
        { apply Rplus_lt_compat_r with (r := - g1) in Hlt12.
          replace (g1 + - g1) with 0 in Hlt12 by ring.
          replace (g2 + - g1) with (g2 - g1) in Hlt12 by ring. exact Hlt12. }
        assert (Hnz : g2 - g1 <> 0).
        { intro E. rewrite E in Hden. exact (Rlt_irrefl 0 Hden). }
        assert (Hnum : 0 <= gm - g1).
        { apply Rplus_le_compat_r with (r := - g1) in Ha.
          replace (g1 + - g1) with 0 in Ha by ring.
          replace (gm + - g1) with (gm - g1) in Ha by ring. exact Ha. }
        assert (Hspan : gm - g1 <= g2 - g1).
        { apply Rplus_le_compat_r. exact Hb. }
        split.
        + apply Rmult_le_pos; [exact Hnum | apply Rlt_le, Rinv_0_lt_compat; exact Hden].
        + apply Rmult_le_reg_r with (r := g2 - g1); [exact Hden|].
          unfold Rdiv. rewrite Rmult_assoc, Rinv_l by exact Hnz.
          rewrite Rmult_1_r, Rmult_1_l. exact Hspan.
      - change (line_g p q h2) with g2 in Ha.
        change (line_g p q h1) with g1 in Hb.
        change (line_g p q m) with gm in Ha.
        change (line_g p q m) with gm in Hb.
        assert (Hle : g2 <= g1) by (apply Rle_trans with gm; assumption).
        assert (Hlt21 : g2 < g1).
        { destruct (Rle_lt_or_eq_dec g2 g1 Hle) as [Hlt|Heq].
          - exact Hlt.
          - symmetry in Heq. exfalso. exact (Hne Heq). }
        assert (Hden : 0 < g1 - g2).
        { apply Rplus_lt_compat_r with (r := - g2) in Hlt21.
          replace (g2 + - g2) with 0 in Hlt21 by ring.
          replace (g1 + - g2) with (g1 - g2) in Hlt21 by ring. exact Hlt21. }
        assert (Hnz : g1 - g2 <> 0).
        { intro E. rewrite E in Hden. exact (Rlt_irrefl 0 Hden). }
        replace ((gm - g1) / (g2 - g1)) with ((g1 - gm) / (g1 - g2)).
        + assert (Hnum : 0 <= g1 - gm).
          { apply Rplus_le_compat_r with (r := - gm) in Hb.
            replace (gm + - gm) with 0 in Hb by ring.
            replace (g1 + - gm) with (g1 - gm) in Hb by ring. exact Hb. }
          assert (Hspan : g1 - gm <= g1 - g2).
          { apply Rplus_le_compat_l. apply Ropp_le_contravar. exact Ha. }
          split.
          * apply Rmult_le_pos; [exact Hnum | apply Rlt_le, Rinv_0_lt_compat; exact Hden].
          * apply Rmult_le_reg_r with (r := g1 - g2); [exact Hden|].
            unfold Rdiv. rewrite Rmult_assoc, Rinv_l by exact Hnz.
            rewrite Rmult_1_r, Rmult_1_l. exact Hspan.
        + unfold Rdiv. replace (gm - g1) with (- (g1 - gm)) by ring.
          replace (g2 - g1) with (- (g1 - g2)) by ring.
          rewrite (Rinv_opp (g1 - g2)) by exact Hnz. ring. }
    exists t. split; [exact Ht|].
    apply (frame_inj p q); [| | exact Hd].
    + rewrite g_affine.
      assert (Ez : t * (g2 - g1) = gm - g1).
      { assert (Hden0 : g2 - g1 <> 0).
        { intro E. assert (Eq : g2 = g1).
          { apply Rplus_eq_reg_r with (r := - g1).
            replace (g2 + - g1) with (g2 - g1) by ring.
            replace (g1 + - g1) with 0 by ring. exact E. }
          symmetry in Eq. exact (Hne Eq). }
        unfold t, Rdiv. rewrite Rmult_assoc, Rinv_l by exact Hden0.
        rewrite Rmult_1_r. reflexivity. }
      replace ((1 - t) * line_g p q h1 + t * line_g p q h2)
        with (g1 + t * (g2 - g1)).
      * rewrite Ez. unfold gm.
        replace (g1 + (line_g p q m - g1)) with (line_g p q m).
        -- reflexivity.
        -- unfold Rminus. rewrite <- Rplus_assoc.
           rewrite (Rplus_comm g1 (line_g p q m)). rewrite Rplus_assoc.
           rewrite Rplus_opp_r. rewrite Rplus_0_r. reflexivity.
      * unfold Rminus.
        rewrite Rmult_plus_distr_l. rewrite <- Ropp_mult_distr_r.
        change (line_g p q h1) with g1. change (line_g p q h2) with g2.
        rewrite Rmult_plus_distr_r. rewrite Rmult_1_l.
        rewrite <- Ropp_mult_distr_l.
        rewrite (Rplus_comm (t * g2) (- (t * g1))).
        rewrite <- Rplus_assoc. reflexivity.
    + clearbody t. rewrite Hzm, cross_combo, Hz1, Hz2.
      rewrite !Rmult_0_r, Rplus_0_l. reflexivity.
Qed.
(* Soundness for an arbitrary vertex list: the clip hull sits in the input   *)
(* hull and in the closed half-plane. Consecutive duplicates are harmless.   *)
Lemma clip_chain_vert : forall poly prev rest p q v,
  in_hull poly prev ->
  (forall u, In u rest -> in_hull poly u) ->
  In v (clip_chain prev rest p q) ->
  in_hull poly v /\ inside_closed p q v.
Proof.
  intros poly prev rest p q v. revert prev v.
  induction rest as [|cur rest IH]; intros prev v Hp Hrest Hin; simpl in Hin.
  - contradiction.
  - apply in_app_or in Hin. destruct Hin as [He|He].
    + destruct (emit_in_edge prev cur p q v He) as [Hh Hi]. split; [| exact Hi].
      apply members_in_hull with (K := [prev; cur]); [| exact Hh].
      intros z Hz. simpl in Hz. destruct Hz as [->|[->|[]]];
        [exact Hp | apply Hrest; simpl; tauto].
    + apply IH with (prev := cur); [| | exact He].
      * apply Hrest. simpl. tauto.
      * intros u Hu. apply Hrest. simpl. tauto.
Qed.
Lemma in_closed_walk : forall (a : Point) rest u,
  In u (tl ((a :: rest) ++ [a])) -> In u (a :: rest).
Proof.
  intros a rest u Hu. destruct rest as [|b rest].
  - simpl in Hu. destruct Hu as [->|[]]. simpl. tauto.
  - simpl in Hu. destruct Hu as [->|Hu].
    + simpl. tauto.
    + apply in_app_or in Hu. destruct Hu as [Hu|Hu].
      * simpl. tauto.
      * simpl in Hu. destruct Hu as [->|[]]. simpl. tauto.
Qed.
Lemma clip_verts_ok : forall poly p q v,
  In v (clip_halfplane poly p q) ->
  in_hull poly v /\ inside_closed p q v.
Proof.
  intros poly p q v Hin.
  destruct (point_eqb p q) eqn:Epq.
  - apply point_eqb_true in Epq. subst q.
    unfold clip_halfplane in Hin. rewrite point_eqb_refl in Hin.
    split; [apply in_hull_in; exact Hin | unfold inside_closed, cross].
    ring_simplify. lra.
  - unfold clip_halfplane in Hin. rewrite Epq in Hin.
    destruct poly as [|a [|b rest]].
    + contradiction.
    + simpl in Hin. destruct (inside_b p q a) eqn:Ha.
      * destruct Hin as [->|[]]. split.
        -- apply in_hull_in. simpl. tauto.
        -- apply inside_b_true. exact Ha.
      * contradiction.
    + destruct rest as [|c rest].
      * assert (Hs : in_hull [a; b] v /\ inside_closed p q v).
        { unfold seg_clip in Hin.
          destruct (inside_b p q a) eqn:Ha; destruct (inside_b p q b) eqn:Hb;
            simpl in Hin.
          - destruct Hin as [<-|[<-|[]]].
            + split; [apply in_hull_in; simpl; tauto | apply inside_b_true; exact Ha].
            + split; [apply in_hull_in; simpl; tauto | apply inside_b_true; exact Hb].
          - destruct Hin as [<-|[<-|[]]].
            + split; [apply in_hull_in; simpl; tauto | apply inside_b_true; exact Ha].
            + destruct (line_hit_on_seg a b p q) as [t [Ht [Heq Hz]]].
              { left. split; [apply inside_b_true; exact Ha | apply inside_b_false; exact Hb]. }
              split.
              * rewrite Heq. apply in_hull_conv; try exact Ht;
                  apply in_hull_in; simpl; tauto.
              * unfold inside_closed. rewrite Hz. lra.
          - destruct Hin as [<-|[<-|[]]].
            + destruct (line_hit_on_seg a b p q) as [t [Ht [Heq Hz]]].
              { right. split; [apply inside_b_false; exact Ha | apply inside_b_true; exact Hb]. }
              split.
              * rewrite Heq. apply in_hull_conv; try exact Ht;
                  apply in_hull_in; simpl; tauto.
              * unfold inside_closed. rewrite Hz. lra.
            + split; [apply in_hull_in; simpl; tauto | apply inside_b_true; exact Hb].
          - contradiction. }
        destruct Hs as [Hh Hi]. split; [| exact Hi].
        apply in_hull_embed2 with (a:=a) (b:=b); simpl; tauto.
      * assert (Hprev : in_hull (a :: b :: c :: rest) a).
        { apply in_hull_in. simpl. tauto. }
        assert (Hrest : forall u, In u (tl ((a :: b :: c :: rest) ++ [a])) ->
                              in_hull (a :: b :: c :: rest) u).
        { intros u Hu. apply in_hull_in. apply in_closed_walk. exact Hu. }
        apply clip_chain_vert with (prev := a)
          (rest := tl ((a :: b :: c :: rest) ++ [a])); assumption.
Qed.
Theorem clip_sound : forall poly p q x,
  in_hull (clip_halfplane poly p q) x ->
  in_hull poly x /\ inside_closed p q x.
Proof.
  intros poly p q x Hx. split.
  - apply members_in_hull with (K := clip_halfplane poly p q); [| exact Hx].
    intros v Hv. destruct (clip_verts_ok _ _ _ _ Hv) as [H _]. exact H.
  - apply members_inside with (K := clip_halfplane poly p q); [| exact Hx].
    intros v Hv. destruct (clip_verts_ok _ _ _ _ Hv) as [_ H]. exact H.
Qed.
(* A polygon is CCW convex when every boundary edge, including the close,    *)
(* has the whole vertex list in its closed left half-plane. Length < 3 is   *)
(* included (a segment, a point, or nothing has no corner to test).          *)
Fixpoint chain_supports (prev : Point) (rest all : list Point) : Prop :=
  match rest with
  | [] => True
  | cur :: rest' =>
      (forall v, In v all -> 0 <= cross prev cur v) /\
      chain_supports cur rest' all
  end.
Definition convex_supports (ps : list Point) : Prop :=
  match ps with
  | _ :: _ :: _ :: _ =>
      match ps with
      | a :: _ => chain_supports a (tl (ps ++ [a])) ps
      | [] => True
      end
  | _ => True
  end.
Lemma support_cleared : forall p q a b v,
  cross p q a * line_g p q b - cross p q b * line_g p q a
  - line_g p q v * (cross p q a - cross p q b)
  + (line_g p q a - line_g p q b) * cross p q v
  = - dist_sq q p * cross a b v.
Proof.
  intros. unfold line_g, cross, dist_sq. destruct p, q, a, b, v. simpl. ring.
Qed.
Lemma on_line_dx : forall p q h,
  cross p q h = 0 ->
  dist_sq q p * (px h - px p) = line_g p q h * (px q - px p) /\
  dist_sq q p * (py h - py p) = line_g p q h * (py q - py p).
Proof.
  intros p q h Hz.
  destruct p as [px0 py0], q as [qx qy], h as [hx hy].
  unfold dist_sq, cross, line_g in *. simpl in *.
  assert (Ex :
    ((qx - px0) * (qx - px0) + (qy - py0) * (qy - py0)) * (hx - px0)
    - ((qx - px0) * (hx - px0) + (qy - py0) * (hy - py0)) * (qx - px0)
    = (py0 - qy) *
      ((qx - px0) * (hy - py0) - (hx - px0) * (qy - py0))).
  { ring. }
  assert (Ey :
    ((qx - px0) * (qx - px0) + (qy - py0) * (qy - py0)) * (hy - py0)
    - ((qx - px0) * (hx - px0) + (qy - py0) * (hy - py0)) * (qy - py0)
    = (qx - px0) *
      ((qx - px0) * (hy - py0) - (hx - px0) * (qy - py0))).
  { ring. }
  rewrite Hz in Ex, Ey.
  split; apply Rminus_diag_uniq.
  - rewrite Ex. ring.
  - rewrite Ey. ring.
Qed.
Lemma chord_frame : forall p q h1 h2 x,
  cross p q h1 = 0 ->
  cross p q h2 = 0 ->
  dist_sq q p * cross h1 h2 x =
    (line_g p q h2 - line_g p q h1) * cross p q x.
Proof.
  intros p q h1 h2 x H1 H2.
  destruct (on_line_dx p q h1 H1) as [X1 Y1].
  destruct (on_line_dx p q h2 H2) as [X2 Y2].
  destruct p as [px0 py0], q as [qx qy], h1 as [ax ay], h2 as [bx by_],
           x as [vx vy].
  simpl in *.
  assert (Dx : dist_sq (mkPoint qx qy) (mkPoint px0 py0) * (bx - ax)
               = (line_g (mkPoint px0 py0) (mkPoint qx qy) (mkPoint bx by_)
                  - line_g (mkPoint px0 py0) (mkPoint qx qy) (mkPoint ax ay))
                 * (qx - px0)).
  { replace (bx - ax) with ((bx - px0) - (ax - px0)) by ring.
    rewrite Rmult_minus_distr_l, X2, X1. ring. }
  assert (Dy : dist_sq (mkPoint qx qy) (mkPoint px0 py0) * (by_ - ay)
               = (line_g (mkPoint px0 py0) (mkPoint qx qy) (mkPoint bx by_)
                  - line_g (mkPoint px0 py0) (mkPoint qx qy) (mkPoint ax ay))
                 * (qy - py0)).
  { replace (by_ - ay) with ((by_ - py0) - (ay - py0)) by ring.
    rewrite Rmult_minus_distr_l, Y2, Y1. ring. }
  set (D := dist_sq (mkPoint qx qy) (mkPoint px0 py0)).
  set (G := line_g (mkPoint px0 py0) (mkPoint qx qy) (mkPoint bx by_)
            - line_g (mkPoint px0 py0) (mkPoint qx qy) (mkPoint ax ay)).
  assert (Ec :
    D * ((bx - ax) * (vy - ay) - (vx - ax) * (by_ - ay)) =
    G * ((qx - px0) * (vy - py0) - (vx - px0) * (qy - py0))).
  { replace (D * ((bx - ax) * (vy - ay) - (vx - ax) * (by_ - ay)))
      with (D * (bx - ax) * (vy - ay) - (vx - ax) * (D * (by_ - ay))) by ring.
    replace (D * (bx - ax)) with (G * (qx - px0)) by (unfold D, G; symmetry; exact Dx).
    replace (D * (by_ - ay)) with (G * (qy - py0)) by (unfold D, G; symmetry; exact Dy).
    assert (Hf :
      (qx - px0) * (vy - ay) - (vx - ax) * (qy - py0)
      = (qx - px0) * (vy - py0) - (vx - px0) * (qy - py0)).
    { apply Rminus_diag_uniq.
      unfold cross in H1. simpl in H1.
      replace (((qx - px0) * (vy - ay) - (vx - ax) * (qy - py0))
               - ((qx - px0) * (vy - py0) - (vx - px0) * (qy - py0)))
        with (- ((qx - px0) * (ay - py0) - (ax - px0) * (qy - py0))) by ring.
      rewrite H1. ring. }
    replace (G * (qx - px0) * (vy - ay) - (vx - ax) * (G * (qy - py0)))
      with (G * ((qx - px0) * (vy - ay) - (vx - ax) * (qy - py0))) by ring.
    rewrite Hf. ring. }
  unfold D, G, dist_sq, cross, line_g in Ec. simpl in Ec. exact Ec.
Qed.
(* Affine readings of a convex combination. cross and line_g are affine, so  *)
(* on a weight-1 combination the constant term cancels.                      *)
Fixpoint cross_dot (p q : Point) (w : list R) (ps : list Point) : R :=
  match w, ps with
  | a :: wt, v :: vt => a * cross p q v + cross_dot p q wt vt
  | _, _ => 0
  end.
Lemma cross_at_origin : forall p q,
  cross p q (mkPoint 0 0) =
    - (px q - px p) * py p + (py q - py p) * px p.
Proof. intros. unfold cross. simpl. ring. Qed.
Lemma cross_wpt_aff : forall p q w ps,
  length w = length ps ->
  cross p q (wpt w ps) =
    cross_dot p q w ps + cross p q (mkPoint 0 0) * (1 - rsum w).
Proof.
  intros p q w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl; simpl in Hl; try discriminate.
  - simpl. unfold cross. simpl. ring.
  - simpl wpt. simpl cross_dot. simpl rsum.
    assert (E :
      cross p q (mkPoint (a * px v + px (wpt w ps)) (a * py v + py (wpt w ps))) =
      a * cross p q v + cross p q (wpt w ps) - a * cross p q (mkPoint 0 0)).
    { destruct v as [vx vy]. destruct (wpt w ps) as [ax ay]. unfold cross. simpl. ring. }
    rewrite E. rewrite (IH w) by lia. ring.
Qed.
Lemma cross_wpt_sum1 : forall p q w ps,
  length w = length ps ->
  rsum w = 1 ->
  cross p q (wpt w ps) = cross_dot p q w ps.
Proof.
  intros p q w ps Hl Hs. rewrite cross_wpt_aff by exact Hl. rewrite Hs. ring.
Qed.
Fixpoint g_dot (p q : Point) (w : list R) (ps : list Point) : R :=
  match w, ps with
  | a :: wt, v :: vt => a * line_g p q v + g_dot p q wt vt
  | _, _ => 0
  end.
Lemma g_wpt_aff : forall p q w ps,
  length w = length ps ->
  line_g p q (wpt w ps) =
    g_dot p q w ps + line_g p q (mkPoint 0 0) * (1 - rsum w).
Proof.
  intros p q w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl; simpl in Hl; try discriminate.
  - simpl. unfold line_g. simpl. ring.
  - simpl wpt. simpl g_dot. simpl rsum.
    assert (E :
      line_g p q (mkPoint (a * px v + px (wpt w ps)) (a * py v + py (wpt w ps))) =
      a * line_g p q v + line_g p q (wpt w ps) - a * line_g p q (mkPoint 0 0)).
    { destruct v as [vx vy]. destruct (wpt w ps) as [ax ay]. unfold line_g. simpl. ring. }
    rewrite E. rewrite (IH w) by lia. ring.
Qed.
Lemma g_wpt_sum1 : forall p q w ps,
  length w = length ps ->
  rsum w = 1 ->
  line_g p q (wpt w ps) = g_dot p q w ps.
Proof.
  intros p q w ps Hl Hs. rewrite g_wpt_aff by exact Hl. rewrite Hs. ring.
Qed.
Lemma cross_dot_le0 : forall p q w ps,
  length w = length ps ->
  nonneg_w w ->
  (forall v, In v ps -> cross p q v <= 0) ->
  cross_dot p q w ps <= 0.
Proof.
  intros p q w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl Hw Hall; simpl in *; try discriminate.
  - lra.
  - assert (Ha : 0 <= a) by (apply Hw; left; reflexivity).
    assert (Hv : cross p q v <= 0) by (apply Hall; left; reflexivity).
    assert (Htail : cross_dot p q w ps <= 0).
    { apply IH; [lia | |].
      - intros z Hz. apply Hw. right. exact Hz.
      - intros u Hu. apply Hall. right. exact Hu. }
    assert (Hp : a * cross p q v <= 0).
    { replace 0 with (a * 0) by ring. apply Rmult_le_compat_l; lra. }
    lra.
Qed.
Lemma cross_dot_neg : forall p q w ps,
  length w = length ps ->
  nonneg_w w ->
  rsum w = 1 ->
  (forall v, In v ps -> cross p q v < 0) ->
  cross_dot p q w ps < 0.
Proof.
  intros p q w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl Hw Hs Hall; simpl in *; try discriminate.
  - lra.
  - assert (Ha : 0 <= a) by (apply Hw; left; reflexivity).
    assert (Hv : cross p q v < 0) by (apply Hall; left; reflexivity).
    assert (Hle : cross_dot p q w ps <= 0).
    { apply cross_dot_le0; [lia | |].
      - intros z Hz. apply Hw. right. exact Hz.
      - intros u Hu. apply Rlt_le. apply Hall. right. exact Hu. }
    destruct (Req_dec_T a 0) as [Ea|Ha0].
    + rewrite Ea in Hs. simpl in Hs.
      replace (0 + rsum w) with (rsum w) in Hs by ring.
      assert (Htail : cross_dot p q w ps < 0).
      { apply IH; [lia | | exact Hs |].
        - intros z Hz. apply Hw. right. exact Hz.
        - intros u Hu. apply Hall. right. exact Hu. }
      rewrite Ea. ring_simplify. exact Htail.
    + assert (Hp : a * cross p q v < 0).
      { replace 0 with (a * 0) by ring. apply Rmult_lt_compat_l; lra. }
      lra.
Qed.
Lemma wpt_seg : forall a b t,
  wpt [(1 - t); t] [a; b] = convex_combination a b t.
Proof.
  intros a b t. unfold convex_combination. simpl.
  destruct a, b. simpl. f_equal; ring.
Qed.
Lemma seg_mem : forall a b t, 0 <= t <= 1 -> in_hull [a; b] (convex_combination a b t).
Proof.
  intros a b t Ht.
  exists [(1 - t); t].
  split; [reflexivity|].
  split.
  - intros z Hz. simpl in Hz. destruct Hz as [<-|[<-|[]]]; lra.
  - split; [simpl; ring | apply wpt_seg].
Qed.
Lemma seg_clip_complete : forall a b p q x,
  point_eqb p q = false ->
  in_hull [a; b] x ->
  inside_closed p q x ->
  in_hull (seg_clip a b p q) x.
Proof.
  intros a b p q x Hpq Hx Hin.
  destruct Hx as [w [Hl [Hw [Hs Hp]]]].
  destruct w as [|t0 [|t1 w]]; simpl in Hl; try discriminate.
  destruct w; simpl in Hl; try discriminate.
  assert (Ht0 : 0 <= t0) by (apply Hw; simpl; tauto).
  assert (Ht1 : 0 <= t1) by (apply Hw; simpl; tauto).
  assert (Hsum : t0 + t1 = 1) by (simpl in Hs; lra).
  assert (Hxpt : x = convex_combination a b t1).
  { replace t0 with (1 - t1) in Hp by lra. rewrite wpt_seg in Hp. symmetry. exact Hp. }
  assert (Hfx : cross p q x = (1 - t1) * cross p q a + t1 * cross p q b).
  { rewrite Hxpt. apply cross_combo. }
  destruct (inside_b p q a) eqn:Ha; destruct (inside_b p q b) eqn:Hb;
    unfold seg_clip; rewrite Ha, Hb; simpl.
  - rewrite Hxpt. apply seg_mem. lra.
  - assert (Hfa : 0 <= cross p q a) by (apply inside_b_true; exact Ha).
    assert (Hfb : cross p q b < 0) by (apply inside_b_false; exact Hb).
    destruct (line_hit_on_seg a b p q) as [s [Hs01 [Heq Hz]]].
    { left. split; [exact Hfa | exact Hfb]. }
    assert (Hle : t1 <= s).
    { assert (Hd : 0 < cross p q a - cross p q b) by lra.
      apply Rmult_le_reg_r with (r := cross p q a - cross p q b); [exact Hd|].
      replace (t1 * (cross p q a - cross p q b))
        with (cross p q a - ((1 - t1) * cross p q a + t1 * cross p q b)) by ring.
      rewrite <- Hfx. unfold inside_closed in Hin.
      replace (s * (cross p q a - cross p q b)) with (cross p q a).
      - lra.
      - assert (E0 : (1 - s) * cross p q a + s * cross p q b = 0).
        { rewrite <- (cross_combo p q a b s). rewrite <- Heq. exact Hz. }
        lra. }
    set (h := line_hit a b p q).
    destruct (Req_dec_T s 0) as [Es|Es].
    + assert (Et : t1 = 0) by lra. rewrite Hxpt, Et.
      replace (convex_combination a b 0) with a.
      * apply in_hull_in. simpl. tauto.
      * unfold convex_combination. destruct a. simpl. f_equal; ring.
    + assert (Hspos : 0 < s) by lra.
      set (u := t1 / s).
      assert (Hu : 0 <= u <= 1).
      { unfold u. split.
        - apply Rmult_le_pos; [exact Ht1 | apply Rlt_le, Rinv_0_lt_compat; exact Hspos].
        - apply Rmult_le_reg_r with (r := s); [exact Hspos|].
          unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; lra. }
      assert (Ex : x = convex_combination a h u).
      { rewrite Hxpt. unfold u, convex_combination, h. rewrite Heq.
        destruct a, b. simpl. f_equal; field; lra. }
      rewrite Ex. apply seg_mem. exact Hu.
  - assert (Hfa : cross p q a < 0) by (apply inside_b_false; exact Ha).
    assert (Hfb : 0 <= cross p q b) by (apply inside_b_true; exact Hb).
    destruct (line_hit_on_seg a b p q) as [s [Hs01 [Heq Hz]]].
    { right. split; [exact Hfa | exact Hfb]. }
    assert (Hge : s <= t1).
    { assert (E0 : (1 - s) * cross p q a + s * cross p q b = 0).
      { rewrite <- (cross_combo p q a b s). rewrite <- Heq. exact Hz. }
      assert (Es : s * (cross p q a - cross p q b) = cross p q a) by lra.
      unfold inside_closed in Hin. rewrite Hfx in Hin.
      assert (Ht : t1 * (cross p q a - cross p q b) <= cross p q a) by lra.
      rewrite <- Es in Ht.
      apply Rmult_le_reg_l with (r := - (cross p q a - cross p q b)).
      - lra.
      - replace (- (cross p q a - cross p q b) * s)
          with (- (s * (cross p q a - cross p q b))) by ring.
        replace (- (cross p q a - cross p q b) * t1)
          with (- (t1 * (cross p q a - cross p q b))) by ring.
        lra. }
    set (h := line_hit a b p q).
    destruct (Req_dec_T s 1) as [Es|Es].
    + assert (Et : t1 = 1) by lra. rewrite Hxpt, Et.
      replace (convex_combination a b 1) with b.
      * apply in_hull_in. simpl. right. left. reflexivity.
      * unfold convex_combination. destruct b. simpl. f_equal; ring.
    + assert (Hlt : s < 1) by lra.
      set (u := (t1 - s) / (1 - s)).
      assert (Hu : 0 <= u <= 1).
      { assert (Hden : 0 < 1 - s) by lra.
        unfold u. split.
        - apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; exact Hden].
        - apply Rmult_le_reg_r with (r := 1 - s); [exact Hden|].
          unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; lra. }
      assert (Ex : x = convex_combination h b u).
      { rewrite Hxpt. unfold u, convex_combination, h. rewrite Heq.
        destruct a, b. simpl. f_equal; field; lra. }
      rewrite Ex. apply seg_mem. exact Hu.
  - assert (Hall : forall v, In v [a; b] -> cross p q v < 0).
    { intros v Hv. simpl in Hv. destruct Hv as [<-|[<-|[]]].
      - apply inside_b_false. exact Ha.
      - apply inside_b_false. exact Hb. }
    assert (Hneg : cross p q x < 0).
    { rewrite <- Hp. rewrite cross_wpt_sum1 with (w := [t0; t1])
        by (simpl; first [lia | lra]).
      apply cross_dot_neg with (w := [t0; t1]).
      - simpl. lia.
      - intros z Hz. simpl in Hz. destruct Hz as [<-|[<-|[]]]; lra.
      - simpl. lra.
      - exact Hall. }
    unfold inside_closed in Hin. lra.
Qed.
Lemma dist_pos_distinct : forall p q,
  points_distinct p q -> 0 < dist_sq q p.
Proof.
  intros p q H. apply dist_sq_pos_iff_distinct.
  intros [Ex Ey]. destruct H as [H|H]; congruence.
Qed.
Lemma emit_keeps_cur : forall prev cur p q,
  inside_b p q cur = true -> In cur (emit_edge prev cur p q).
Proof.
  intros prev cur p q Hc. unfold emit_edge.
  destruct (inside_b p q prev); rewrite Hc; simpl; tauto.
Qed.
Lemma clip_chain_keeps : forall prev rest p q v,
  inside_b p q v = true ->
  In v rest ->
  In v (clip_chain prev rest p q).
Proof.
  intros prev rest p q v Hc. revert prev.
  induction rest as [|cur rest IH]; intros prev Hin; simpl in Hin; try contradiction.
  simpl. destruct Hin as [->|Hin].
  - apply in_or_app. left. apply emit_keeps_cur. exact Hc.
  - apply in_or_app. right. apply IH. exact Hin.
Qed.
Lemma in_closed_suffix : forall (a v : Point) rest,
  In v (a :: rest) -> In v (rest ++ [a]).
Proof.
  intros a v rest Hin. destruct Hin as [->|Hin].
  - apply in_or_app. right. simpl. tauto.
  - apply in_or_app. left. exact Hin.
Qed.
Lemma clip_keeps_inside : forall poly p q v,
  point_eqb p q = false ->
  (3 <= length poly)%nat ->
  inside_b p q v = true ->
  In v poly ->
  In v (clip_halfplane poly p q).
Proof.
  intros poly p q v Hpq Hlen Hc Hin.
  destruct poly as [|a [|b [|c rest]]]; simpl in Hlen; try lia.
  unfold clip_halfplane. rewrite Hpq.
  replace (tl ((a :: b :: c :: rest) ++ [a]))
    with ((b :: c :: rest) ++ [a]) by reflexivity.
  apply clip_chain_keeps; [exact Hc|].
  apply in_closed_suffix. exact Hin.
Qed.
(* A closed walk that meets both half-planes has a leaving edge and an
   entering edge. The clip emits both intersection points. *)
Fixpoint find_leave (prev : Point) (rest : list Point) (p q : Point)
  : option (Point * Point) :=
  match rest with
  | [] => None
  | cur :: rest' =>
      if andb (inside_b p q prev) (negb (inside_b p q cur))
      then Some (prev, cur)
      else find_leave cur rest' p q
  end.
Fixpoint find_enter (prev : Point) (rest : list Point) (p q : Point)
  : option (Point * Point) :=
  match rest with
  | [] => None
  | cur :: rest' =>
      if andb (negb (inside_b p q prev)) (inside_b p q cur)
      then Some (prev, cur)
      else find_enter cur rest' p q
  end.
Lemma find_leave_spec : forall prev rest p q a b,
  find_leave prev rest p q = Some (a, b) ->
  inside_b p q a = true /\ inside_b p q b = false /\
  In (line_hit a b p q) (clip_chain prev rest p q).
Proof.
  intros prev rest p q. revert prev.
  induction rest as [|cur rest IH]; intros prev a b Hf; simpl in Hf; try discriminate.
  destruct (andb (inside_b p q prev) (negb (inside_b p q cur))) eqn:He.
  - injection Hf as -> ->. simpl. apply andb_true_iff in He. destruct He as [Hp Hn].
    apply negb_true_iff in Hn. split; [exact Hp|]. split; [exact Hn|].
    apply in_or_app. left. unfold emit_edge. rewrite Hp, Hn. simpl. tauto.
  - simpl. specialize (IH cur a b Hf) as [Ha [Hb Hin]].
    split; [exact Ha|]. split; [exact Hb|]. apply in_or_app. right. exact Hin.
Qed.
Lemma find_enter_spec : forall prev rest p q a b,
  find_enter prev rest p q = Some (a, b) ->
  inside_b p q a = false /\ inside_b p q b = true /\
  In (line_hit a b p q) (clip_chain prev rest p q).
Proof.
  intros prev rest p q. revert prev.
  induction rest as [|cur rest IH]; intros prev a b Hf; simpl in Hf; try discriminate.
  destruct (andb (negb (inside_b p q prev)) (inside_b p q cur)) eqn:He.
  - injection Hf as -> ->. simpl. apply andb_true_iff in He. destruct He as [Hn Hp].
    apply negb_true_iff in Hn. split; [exact Hn|]. split; [exact Hp|].
    apply in_or_app. left. unfold emit_edge. rewrite Hn, Hp. simpl. left. reflexivity.
  - simpl. specialize (IH cur a b Hf) as [Ha [Hb Hin]].
    split; [exact Ha|]. split; [exact Hb|]. apply in_or_app. right. exact Hin.
Qed.
Lemma bool_run_leave : forall (prev : Point) (rest : list Point) p q,
  inside_b p q prev = true ->
  existsb (fun v => negb (inside_b p q v)) (prev :: rest) = true ->
  find_leave prev rest p q <> None.
Proof.
  intros prev rest p q Hp. revert prev Hp.
  induction rest as [|cur rest IH]; intros prev Hp Hex.
  - simpl in Hex. rewrite Hp in Hex. discriminate.
  - destruct (inside_b p q cur) eqn:Hc.
    + simpl. rewrite Hp, Hc. simpl. apply IH; [exact Hc|].
      simpl in Hex. rewrite Hp, Hc in Hex. simpl in Hex.
      simpl. rewrite Hc. simpl. exact Hex.
    + simpl. rewrite Hp, Hc. simpl. congruence.
Qed.
Lemma bool_run_enter : forall (prev : Point) (rest : list Point) p q,
  inside_b p q prev = false ->
  existsb (inside_b p q) (prev :: rest) = true ->
  find_enter prev rest p q <> None.
Proof.
  intros prev rest p q Hp. revert prev Hp.
  induction rest as [|cur rest IH]; intros prev Hp Hex.
  - simpl in Hex. rewrite Hp in Hex. discriminate.
  - destruct (inside_b p q cur) eqn:Hc.
    + simpl. rewrite Hp, Hc. simpl. congruence.
    + simpl. rewrite Hp, Hc. simpl. apply IH; [exact Hc|].
      simpl in Hex. rewrite Hp, Hc in Hex. simpl in Hex.
      simpl. rewrite Hc. simpl. exact Hex.
Qed.
Lemma existsb_closed_out : forall a rest p q,
  existsb (fun v => negb (inside_b p q v)) (a :: rest) = true ->
  existsb (fun v => negb (inside_b p q v)) (rest ++ [a]) = true.
Proof.
  intros a rest p q H. apply existsb_exists in H. destruct H as [v [Hin Hv]].
  apply existsb_exists. exists v. split; [| exact Hv].
  apply in_closed_suffix. exact Hin.
Qed.
Lemma existsb_closed_in : forall a rest p q,
  existsb (inside_b p q) (a :: rest) = true ->
  existsb (inside_b p q) (rest ++ [a]) = true.
Proof.
  intros a rest p q H. apply existsb_exists in H. destruct H as [v [Hin Hv]].
  apply existsb_exists. exists v. split; [| exact Hv].
  apply in_closed_suffix. exact Hin.
Qed.
(* On a supporting leave edge the clip hit is a lower bound, in the line
   frame, for g - μ f at every vertex. An enter edge is an upper bound.
   A weight-1 combination with f = 0 therefore lies between the two hits. *)
Lemma leave_psi_lin : forall p q a b v,
  cross p q a - cross p q b <> 0 ->
  (cross p q a - cross p q b) *
    (line_g p q (line_hit a b p q)
     - (line_g p q v
        - ((line_g p q a - line_g p q b) / (cross p q a - cross p q b))
          * cross p q v))
  = - dist_sq q p * cross a b v.
Proof.
  intros p q a b v Hd.
  rewrite (g_line_hit p q a b Hd).
  pose proof (support_cleared p q a b v) as Hs.
  assert (E :
    (cross p q a - cross p q b) *
      ((cross p q a * line_g p q b - cross p q b * line_g p q a)
         / (cross p q a - cross p q b)
       - (line_g p q v
          - ((line_g p q a - line_g p q b) / (cross p q a - cross p q b))
            * cross p q v))
    = cross p q a * line_g p q b - cross p q b * line_g p q a
      - line_g p q v * (cross p q a - cross p q b)
      + (line_g p q a - line_g p q b) * cross p q v).
  { field. exact Hd. }
  rewrite E. exact Hs.
Qed.
Lemma leave_psi_ge : forall p q a b v,
  points_distinct p q ->
  0 <= cross p q a ->
  cross p q b < 0 ->
  0 <= cross a b v ->
  line_g p q (line_hit a b p q) <=
    line_g p q v -
    ((line_g p q a - line_g p q b) / (cross p q a - cross p q b))
      * cross p q v.
Proof.
  intros p q a b v Hdist Ha Hb Hv.
  assert (HD : 0 < cross p q a - cross p q b) by lra.
  assert (Hnz : cross p q a - cross p q b <> 0) by lra.
  assert (Hdiff :
    line_g p q (line_hit a b p q)
    - (line_g p q v
       - ((line_g p q a - line_g p q b) / (cross p q a - cross p q b))
         * cross p q v) <= 0).
  { apply Rmult_le_reg_l with (r := cross p q a - cross p q b); [exact HD|].
    rewrite Rmult_0_r.
    rewrite (leave_psi_lin p q a b v Hnz).
    assert (Hp : 0 <= dist_sq q p * cross a b v).
    { apply Rmult_le_pos;
        [apply Rlt_le, dist_pos_distinct; exact Hdist | exact Hv]. }
    apply Ropp_le_contravar in Hp. rewrite Ropp_0 in Hp.
    replace (- dist_sq q p * cross a b v)
      with (- (dist_sq q p * cross a b v)) by ring.
    exact Hp. }
  lra.
Qed.
Lemma enter_psi_le : forall p q a b v,
  points_distinct p q ->
  cross p q a < 0 ->
  0 <= cross p q b ->
  0 <= cross a b v ->
  line_g p q v -
    ((line_g p q a - line_g p q b) / (cross p q a - cross p q b))
      * cross p q v
  <= line_g p q (line_hit a b p q).
Proof.
  intros p q a b v Hdist Ha Hb Hv.
  set (D := cross p q a - cross p q b).
  assert (HD : D < 0) by (unfold D; lra).
  assert (Hnz : D <> 0) by (unfold D; lra).
  assert (Hn : 0 < - D) by lra.
  assert (Hle : D *
      (line_g p q (line_hit a b p q)
       - (line_g p q v
          - ((line_g p q a - line_g p q b) / D) * cross p q v))
      <= 0).
  { replace D with (cross p q a - cross p q b) by (unfold D; reflexivity).
    rewrite (leave_psi_lin p q a b v Hnz).
    assert (Hp : 0 <= dist_sq q p * cross a b v).
    { apply Rmult_le_pos; [apply Rlt_le, dist_pos_distinct; exact Hdist | exact Hv]. }
    apply Ropp_le_contravar in Hp. rewrite Ropp_0 in Hp.
    replace (- dist_sq q p * cross a b v)
      with (- (dist_sq q p * cross a b v)) by ring.
    exact Hp. }
  assert (Hflip : 0 <= (- D) *
      (line_g p q (line_hit a b p q)
       - (line_g p q v
          - ((line_g p q a - line_g p q b) / D) * cross p q v))).
  { apply Ropp_le_contravar in Hle. rewrite Ropp_0 in Hle.
    replace (- (D *
        (line_g p q (line_hit a b p q)
         - (line_g p q v
            - ((line_g p q a - line_g p q b) / D) * cross p q v))))
      with ((- D) *
        (line_g p q (line_hit a b p q)
         - (line_g p q v
            - ((line_g p q a - line_g p q b) / D) * cross p q v))) in Hle by ring.
    exact Hle. }
  assert (Hdiff : 0 <=
    line_g p q (line_hit a b p q)
    - (line_g p q v
       - ((line_g p q a - line_g p q b) / D) * cross p q v)).
  { apply Rmult_le_reg_l with (r := - D); [exact Hn|].
    rewrite Rmult_0_r. exact Hflip. }
  unfold D in *. lra.
Qed.
Definition line_mu (p q a b : Point) : R :=
  (line_g p q a - line_g p q b) / (cross p q a - cross p q b).
Lemma cross_dot_ge0 : forall p q w ps,
  length w = length ps ->
  nonneg_w w ->
  (forall v, In v ps -> 0 <= cross p q v) ->
  0 <= cross_dot p q w ps.
Proof.
  intros p q w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl Hw Hall; simpl in *; try discriminate.
  - lra.
  - assert (Ha : 0 <= a) by (apply Hw; left; reflexivity).
    assert (Hv : 0 <= cross p q v) by (apply Hall; left; reflexivity).
    assert (Htail : 0 <= cross_dot p q w ps).
    { apply IH; [lia| |].
      - intros z Hz. apply Hw. right. exact Hz.
      - intros u Hu. apply Hall. right. exact Hu. }
    apply Rplus_le_le_0_compat; [| exact Htail].
    apply Rmult_le_pos; assumption.
Qed.
(* A consecutive pair on the clip walk inherits the polygon's support. *)
Fixpoint walk_has_edge (prev : Point) (rest : list Point) (a b : Point) : Prop :=
  match rest with
  | [] => False
  | cur :: rest' => (prev = a /\ cur = b) \/ walk_has_edge cur rest' a b
  end.
Lemma find_leave_has_edge : forall prev rest p q a b,
  find_leave prev rest p q = Some (a, b) ->
  walk_has_edge prev rest a b.
Proof.
  intros prev rest p q. revert prev.
  induction rest as [|cur rest IH]; intros prev a b Hf; simpl in Hf; try discriminate.
  destruct (andb (inside_b p q prev) (negb (inside_b p q cur))) eqn:He.
  - injection Hf as -> ->. simpl. left. split; reflexivity.
  - simpl. right. apply IH. exact Hf.
Qed.
Lemma find_enter_has_edge : forall prev rest p q a b,
  find_enter prev rest p q = Some (a, b) ->
  walk_has_edge prev rest a b.
Proof.
  intros prev rest p q. revert prev.
  induction rest as [|cur rest IH]; intros prev a b Hf; simpl in Hf; try discriminate.
  destruct (andb (negb (inside_b p q prev)) (inside_b p q cur)) eqn:He.
  - injection Hf as -> ->. simpl. left. split; reflexivity.
  - simpl. right. apply IH. exact Hf.
Qed.
Lemma walk_edge_supports : forall prev rest all a b,
  chain_supports prev rest all ->
  walk_has_edge prev rest a b ->
  forall v, In v all -> 0 <= cross a b v.
Proof.
  intros prev rest all a b. revert prev.
  induction rest as [|cur rest IH]; intros prev Hs He v Hv; simpl in He; try contradiction.
  destruct Hs as [Hedge Htail]. destruct He as [[-> ->]|He].
  - apply Hedge. exact Hv.
  - apply IH with (prev := cur); assumption.
Qed.
Lemma existsb_out_snoc : forall prev rest endp p q,
  inside_b p q endp = false ->
  existsb (fun v => negb (inside_b p q v)) (prev :: rest ++ [endp]) = true.
Proof.
  intros prev rest endp p q Hend. apply existsb_exists. exists endp. split.
  - right. apply in_or_app. right. simpl. left. reflexivity.
  - rewrite Hend. reflexivity.
Qed.
Lemma existsb_in_snoc : forall prev rest endp p q,
  inside_b p q endp = true ->
  existsb (inside_b p q) (prev :: rest ++ [endp]) = true.
Proof.
  intros prev rest endp p q Hend. apply existsb_exists. exists endp. split.
  - right. apply in_or_app. right. simpl. left. reflexivity.
  - exact Hend.
Qed.
Lemma find_leave_before_out : forall prev rest endp p q,
  inside_b p q endp = false ->
  existsb (inside_b p q) (prev :: rest) = true ->
  find_leave prev (rest ++ [endp]) p q <> None.
Proof.
  intros prev rest endp p q Hend. revert prev.
  induction rest as [|cur rest IH]; intros prev Hin.
  - simpl in Hin. rewrite orb_false_r in Hin.
    simpl. rewrite Hin, Hend. simpl. congruence.
  - destruct (inside_b p q prev) eqn:Hp.
    + apply bool_run_leave; [exact Hp |].
      apply existsb_out_snoc. exact Hend.
    + simpl in Hin. rewrite Hp in Hin. simpl in Hin.
      replace ((cur :: rest) ++ [endp]) with (cur :: rest ++ [endp]) by reflexivity.
      simpl. rewrite Hp. simpl. apply IH. exact Hin.
Qed.
Lemma find_enter_before_in : forall prev rest endp p q,
  inside_b p q endp = true ->
  existsb (fun v => negb (inside_b p q v)) (prev :: rest) = true ->
  find_enter prev (rest ++ [endp]) p q <> None.
Proof.
  intros prev rest endp p q Hend. revert prev.
  induction rest as [|cur rest IH]; intros prev Hin.
  - simpl in Hin. rewrite orb_false_r in Hin.
    simpl. rewrite Hend, Hin. simpl. congruence.
  - destruct (inside_b p q prev) eqn:Hp.
    + simpl in Hin. rewrite Hp in Hin. simpl in Hin.
      replace ((cur :: rest) ++ [endp]) with (cur :: rest ++ [endp]) by reflexivity.
      simpl. rewrite Hp. simpl. apply IH. exact Hin.
    + apply bool_run_enter; [exact Hp |].
      apply existsb_in_snoc. exact Hend.
Qed.
Lemma existsb_cons_app : forall (f : Point -> bool) a rest v,
  existsb f (a :: rest) = true ->
  existsb f (a :: rest ++ [v]) = true.
Proof.
  intros f a rest v H. apply existsb_exists in H. destruct H as [u [Hu Hf]].
  apply existsb_exists. exists u. split; [| exact Hf].
  simpl in Hu. destruct Hu as [->|Hu].
  - simpl. left. reflexivity.
  - simpl. right. apply in_or_app. left. exact Hu.
Qed.
Lemma closed_has_leave : forall a rest p q,
  existsb (inside_b p q) (a :: rest) = true ->
  existsb (fun v => negb (inside_b p q v)) (a :: rest) = true ->
  find_leave a (rest ++ [a]) p q <> None.
Proof.
  intros a rest p q Hin Hout.
  destruct (inside_b p q a) eqn:Ha.
  - apply bool_run_leave; [exact Ha |].
    apply existsb_cons_app. exact Hout.
  - apply find_leave_before_out; [exact Ha | exact Hin].
Qed.
Lemma closed_has_enter : forall a rest p q,
  existsb (inside_b p q) (a :: rest) = true ->
  existsb (fun v => negb (inside_b p q v)) (a :: rest) = true ->
  find_enter a (rest ++ [a]) p q <> None.
Proof.
  intros a rest p q Hin Hout.
  destruct (inside_b p q a) eqn:Ha.
  - apply find_enter_before_in; [exact Ha | exact Hout].
  - apply bool_run_enter; [exact Ha |].
    apply existsb_cons_app. exact Hin.
Qed.
Lemma weighted_psi_ge : forall p q mu bound w ps,
  length w = length ps ->
  nonneg_w w ->
  (forall v, In v ps -> bound <= line_g p q v - mu * cross p q v) ->
  rsum w * bound <= g_dot p q w ps - mu * cross_dot p q w ps.
Proof.
  intros p q mu bound w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl Hw Hall; simpl in *; try discriminate.
  - lra.
  - assert (Ha : 0 <= a) by (apply Hw; left; reflexivity).
    assert (Hv : bound <= line_g p q v - mu * cross p q v)
      by (apply Hall; left; reflexivity).
    assert (Htail : rsum w * bound <= g_dot p q w ps - mu * cross_dot p q w ps).
    { apply IH; [lia| |].
      - intros z Hz. apply Hw. right. exact Hz.
      - intros u Hu. apply Hall. right. exact Hu. }
    assert (Hhead : a * bound <= a * (line_g p q v - mu * cross p q v)).
    { apply Rmult_le_compat_l; [exact Ha | exact Hv]. }
    replace ((a + rsum w) * bound) with (a * bound + rsum w * bound) by ring.
    apply Rle_trans with
      (a * (line_g p q v - mu * cross p q v)
       + (g_dot p q w ps - mu * cross_dot p q w ps)).
    { apply Rplus_le_compat; assumption. }
    { apply Req_le. ring. }
Qed.
Lemma hull_psi_ge : forall p q mu bound poly x,
  (forall v, In v poly -> bound <= line_g p q v - mu * cross p q v) ->
  in_hull poly x ->
  bound <= line_g p q x - mu * cross p q x.
Proof.
  intros p q mu bound poly x Hall [w [Hl [Hn [Hs Hx]]]].
  assert (Hw := weighted_psi_ge p q mu bound w poly Hl Hn Hall).
  rewrite Hs, Rmult_1_l in Hw.
  rewrite <- (g_wpt_sum1 p q w poly Hl Hs) in Hw.
  rewrite <- (cross_wpt_sum1 p q w poly Hl Hs) in Hw.
  rewrite Hx in Hw. exact Hw.
Qed.
Lemma weighted_psi_le : forall p q mu bound w ps,
  length w = length ps ->
  nonneg_w w ->
  (forall v, In v ps -> line_g p q v - mu * cross p q v <= bound) ->
  g_dot p q w ps - mu * cross_dot p q w ps <= rsum w * bound.
Proof.
  intros p q mu bound w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl Hw Hall; simpl in *; try discriminate.
  - lra.
  - assert (Ha : 0 <= a) by (apply Hw; left; reflexivity).
    assert (Hv : line_g p q v - mu * cross p q v <= bound)
      by (apply Hall; left; reflexivity).
    assert (Htail :
      g_dot p q w ps - mu * cross_dot p q w ps <= rsum w * bound).
    { apply IH; [lia| |].
      - intros z Hz. apply Hw. right. exact Hz.
      - intros u Hu. apply Hall. right. exact Hu. }
    assert (Hhead : a * (line_g p q v - mu * cross p q v) <= a * bound).
    { apply Rmult_le_compat_l; [exact Ha | exact Hv]. }
    replace ((a + rsum w) * bound) with (a * bound + rsum w * bound) by ring.
    apply Rle_trans with
      (a * (line_g p q v - mu * cross p q v)
       + (g_dot p q w ps - mu * cross_dot p q w ps)).
    { apply Req_le. ring. }
    { apply Rplus_le_compat; assumption. }
Qed.
Lemma hull_psi_le : forall p q mu bound poly x,
  (forall v, In v poly -> line_g p q v - mu * cross p q v <= bound) ->
  in_hull poly x ->
  line_g p q x - mu * cross p q x <= bound.
Proof.
  intros p q mu bound poly x Hall [w [Hl [Hn [Hs Hx]]]].
  assert (Hw := weighted_psi_le p q mu bound w poly Hl Hn Hall).
  rewrite <- (g_wpt_sum1 p q w poly Hl Hs) in Hw.
  rewrite <- (cross_wpt_sum1 p q w poly Hl Hs) in Hw.
  rewrite Hx, Hs, Rmult_1_l in Hw. exact Hw.
Qed.
Lemma hull_between_hits : forall poly p q aL bL aE bE x,
  points_distinct p q ->
  inside_b p q aL = true -> inside_b p q bL = false ->
  inside_b p q aE = false -> inside_b p q bE = true ->
  (forall v, In v poly -> 0 <= cross aL bL v) ->
  (forall v, In v poly -> 0 <= cross aE bE v) ->
  in_hull poly x ->
  cross p q x = 0 ->
  exists t, 0 <= t <= 1 /\
    x = convex_combination (line_hit aL bL p q) (line_hit aE bE p q) t.
Proof.
  intros poly p q aL bL aE bE x Hdist HaL HbL HaE HbE HsupL HsupE Hx Hz.
  assert (HdenL : cross p q aL - cross p q bL <> 0).
  { assert (Ha : 0 <= cross p q aL) by (apply inside_b_true; exact HaL).
    assert (Hb : cross p q bL < 0) by (apply inside_b_false; exact HbL). lra. }
  assert (HdenE : cross p q aE - cross p q bE <> 0).
  { assert (Ha : cross p q aE < 0) by (apply inside_b_false; exact HaE).
    assert (Hb : 0 <= cross p q bE) by (apply inside_b_true; exact HbE). lra. }
  assert (HzL : cross p q (line_hit aL bL p q) = 0).
  { apply line_hit_on_line. exact HdenL. }
  assert (HzE : cross p q (line_hit aE bE p q) = 0).
  { apply line_hit_on_line. exact HdenE. }
  assert (Hlo : line_g p q (line_hit aL bL p q) <= line_g p q x).
  { assert (Hpsi := hull_psi_ge p q (line_mu p q aL bL)
      (line_g p q (line_hit aL bL p q)) poly x).
    assert (Hap : forall v, In v poly ->
        line_g p q (line_hit aL bL p q) <=
        line_g p q v - line_mu p q aL bL * cross p q v).
    { intros v Hv. unfold line_mu.
      apply leave_psi_ge; try assumption.
      - apply inside_b_true. exact HaL.
      - apply inside_b_false. exact HbL.
      - apply HsupL. exact Hv. }
    specialize (Hpsi Hap Hx). rewrite Hz, Rmult_0_r, Rminus_0_r in Hpsi.
    exact Hpsi. }
  assert (Hhi : line_g p q x <= line_g p q (line_hit aE bE p q)).
  { assert (Hup : forall v, In v poly ->
        line_g p q v - line_mu p q aE bE * cross p q v
        <= line_g p q (line_hit aE bE p q)).
    { intros v Hv. unfold line_mu. apply enter_psi_le; try assumption.
      - apply inside_b_false. exact HaE.
      - apply inside_b_true. exact HbE.
      - apply HsupE. exact Hv. }
    assert (Hpsi := hull_psi_le p q (line_mu p q aE bE)
      (line_g p q (line_hit aE bE p q)) poly x Hup Hx).
    rewrite Hz, Rmult_0_r, Rminus_0_r in Hpsi. exact Hpsi. }
  apply (on_line_between p q (line_hit aL bL p q) (line_hit aE bE p q) x);
    try assumption.
  left. split; assumption.
Qed.

(* Assumptions: sig_not_dec, sig_forall_dec, functional_extensionality_dep. *)
Print Assumptions g_affine.
Print Assumptions g_line_hit.
Print Assumptions g_hit_cleared.
Print Assumptions frame_inj.
Print Assumptions on_line_between.
Print Assumptions clip_chain_vert.
Print Assumptions in_closed_walk.
Print Assumptions clip_verts_ok.
Print Assumptions clip_sound.
Print Assumptions support_cleared.
Print Assumptions on_line_dx.
Print Assumptions chord_frame.
Print Assumptions cross_at_origin.
Print Assumptions cross_wpt_aff.
Print Assumptions cross_wpt_sum1.
Print Assumptions g_wpt_aff.
Print Assumptions g_wpt_sum1.
Print Assumptions cross_dot_le0.
Print Assumptions cross_dot_neg.
Print Assumptions wpt_seg.
Print Assumptions seg_mem.
Print Assumptions seg_clip_complete.
Print Assumptions dist_pos_distinct.
Print Assumptions emit_keeps_cur.
Print Assumptions clip_chain_keeps.
Print Assumptions in_closed_suffix.
Print Assumptions clip_keeps_inside.
Print Assumptions find_leave_spec.
Print Assumptions find_enter_spec.
Print Assumptions bool_run_leave.
Print Assumptions bool_run_enter.
Print Assumptions existsb_closed_out.
Print Assumptions existsb_closed_in.
Print Assumptions leave_psi_lin.
Print Assumptions leave_psi_ge.
Print Assumptions enter_psi_le.
Print Assumptions cross_dot_ge0.
Print Assumptions find_leave_has_edge.
Print Assumptions find_enter_has_edge.
Print Assumptions walk_edge_supports.
Print Assumptions existsb_out_snoc.
Print Assumptions existsb_in_snoc.
Print Assumptions find_leave_before_out.
Print Assumptions find_enter_before_in.
Print Assumptions existsb_cons_app.
Print Assumptions closed_has_leave.
Print Assumptions closed_has_enter.
Print Assumptions weighted_psi_ge.
Print Assumptions hull_psi_ge.
Print Assumptions weighted_psi_le.
Print Assumptions hull_psi_le.
Print Assumptions hull_between_hits.
