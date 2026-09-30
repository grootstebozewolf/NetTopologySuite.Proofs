(* NetTopologySuite.Proofs.TrianglePairEdge
   One triangle edge clipped by the other triangle's half-planes, and the
   boolean edge-contact tests those clips decide. The I∩B / B∩I / B∩B
   entries live in TrianglePairBound. Exterior cells are T1c.
   topic: relate
   claimId: tri-de9im-b
   witness: TrianglePairBound.bound_cells_iff
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7), human-reviewed.
   License: BSD-3-Clause *)

From Stdlib Require Import Reals Lra Lia List Bool.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex
  ConvexClip ConvexClipPoly ConvexClipComplete TrianglePairCommon.
Local Open Scope R_scope.

Definition on_seg (P Q X : Point) : Prop :=
  exists t, 0 <= t <= 1 /\ X = convex_combination P Q t.

Definition vsub (P Q : Point) : Point :=
  mkPoint (px P - px Q) (py P - py Q).

Definition dot (P Q : Point) : R := px P * px Q + py P * py Q.

Definition seg_t (A B X : Point) : R :=
  dot (vsub X A) (vsub B A) / dist_sq B A.

Definition seg_clip_tri (P Q A B C : Point) : list Point :=
  clip_halfplane (clip_halfplane (clip_halfplane [P; Q] A B) B C) C A.

Definition tri_open_b (A B C X : Point) : bool :=
  if Rlt_dec 0 (cross A B X) then
    if Rlt_dec 0 (cross B C X) then
      if Rlt_dec 0 (cross C A X) then true else false
    else false
  else false.

Lemma supports_short : forall ps, Nat.le (length ps) 2 -> convex_supports ps.
Proof.
  intros ps Hlen.
  destruct ps as [|a [|b [|c rest]]]; simpl in Hlen; try lia.
  - unfold convex_supports. simpl. exact I.
  - unfold convex_supports. simpl. exact I.
  - unfold convex_supports. simpl. exact I.
Qed.

Lemma clip_halfplane_len2 : forall ps p q,
  Nat.le (length ps) 2 -> Nat.le (length (clip_halfplane ps p q)) 2.
Proof.
  intros ps p q Hlen.
  destruct ps as [|a [|b [|c rest]]]; simpl in Hlen; try lia.
  - unfold clip_halfplane. destruct (point_eqb p q); simpl; lia.
  - unfold clip_halfplane. destruct (point_eqb p q); simpl.
    + lia.
    + destruct (inside_b p q a); simpl; lia.
  - unfold clip_halfplane. destruct (point_eqb p q); simpl.
    + lia.
    + unfold seg_clip.
      destruct (inside_b p q a); destruct (inside_b p q b); simpl; lia.
Qed.

Lemma in_hull_on_seg : forall P Q X, in_hull [P; Q] X <-> on_seg P Q X.
Proof.
  intros P Q X. split.
  - intros [w [Hl [Hn [Hs Hp]]]].
    destruct w as [|a [|b [|]]]; simpl in Hl; try discriminate.
    assert (Ha : 0 <= a) by (apply Hn; simpl; tauto).
    assert (Hb : 0 <= b) by (apply Hn; simpl; tauto).
    assert (Ea : a = 1 - b) by (simpl in Hs; lra).
    exists b. split; [simpl in Hs; lra|].
    rewrite wpt2 in Hp. rewrite Ea in Hp.
    destruct P as [px0 py0], Q as [qx qy], X as [xx xy].
    simpl in Hp. inversion Hp. unfold convex_combination. simpl. f_equal; lra.
  - intros [t [Ht Hx]]. rewrite Hx. apply seg_mem. exact Ht.
Qed.

Lemma seg_clip_tri_len : forall P Q A B C,
  Nat.le (length (seg_clip_tri P Q A B C)) 2.
Proof.
  intros P Q A B C. unfold seg_clip_tri.
  apply clip_halfplane_len2. apply clip_halfplane_len2. apply clip_halfplane_len2.
  simpl. lia.
Qed.

Lemma seg_clip_tri_correct : forall P Q A B C x,
  0 < cross A B C ->
  in_hull (seg_clip_tri P Q A B C) x <-> on_seg P Q x /\ in_tri A B C x.
Proof.
  intros P Q A B C x HA.
  set (K0 := [P; Q]).
  set (K1 := clip_halfplane K0 A B).
  set (K2 := clip_halfplane K1 B C).
  assert (L0 : Nat.le (length K0) 2) by (subst K0; simpl; lia).
  assert (L1 : Nat.le (length K1) 2) by (apply clip_halfplane_len2; exact L0).
  assert (L2 : Nat.le (length K2) 2) by (apply clip_halfplane_len2; exact L1).
  assert (S0 : convex_supports K0) by (apply supports_short; exact L0).
  assert (S1 : convex_supports K1) by (apply supports_short; exact L1).
  assert (S2 : convex_supports K2) by (apply supports_short; exact L2).
  unfold seg_clip_tri.
  replace (clip_halfplane (clip_halfplane (clip_halfplane [P; Q] A B) B C) C A)
    with (clip_halfplane K2 C A) by (unfold K2, K1, K0; reflexivity).
  rewrite (clip_correct K2 C A x S2).
  replace K2 with (clip_halfplane K1 B C) by (unfold K2; reflexivity).
  rewrite (clip_correct K1 B C x S1).
  replace K1 with (clip_halfplane K0 A B) by (unfold K1; reflexivity).
  rewrite (clip_correct K0 A B x S0).
  subst K0. rewrite in_hull_on_seg.
  rewrite <- (tri_slack_hull A B C x HA).
  unfold inside_closed. tauto.
Qed.

Lemma tri_open_b_true : forall A B C X,
  tri_open_b A B C X = true <-> tri_open A B C X.
Proof.
  intros A B C X. unfold tri_open_b, tri_open. split.
  - intros H.
    destruct (Rlt_dec 0 (cross A B X)); [| discriminate].
    destruct (Rlt_dec 0 (cross B C X)); [| discriminate].
    destruct (Rlt_dec 0 (cross C A X)); [| discriminate].
    repeat split; assumption.
  - intros [Hab [Hbc Hca]].
    destruct (Rlt_dec 0 (cross A B X)); [| contradiction].
    destruct (Rlt_dec 0 (cross B C X)); [| contradiction].
    destruct (Rlt_dec 0 (cross C A X)); [| contradiction].
    reflexivity.
Qed.

Lemma point_eqb_false_neq : forall p q, p <> q -> point_eqb p q = false.
Proof.
  intros p q H. destruct (point_eqb p q) eqn:E.
  - apply point_eqb_true in E. contradiction.
  - reflexivity.
Qed.

Lemma distinct_of_neq : forall p q, p <> q -> points_distinct p q.
Proof.
  intros p q H. unfold points_distinct.
  destruct (Req_dec_T (px p) (px q)) as [Hx|Hx].
  - destruct (Req_dec_T (py p) (py q)) as [Hy|Hy].
    + exfalso. apply H. destruct p, q. simpl in Hx, Hy. subst. reflexivity.
    + right. exact Hy.
  - left. exact Hx.
Qed.

Lemma neq_of_distinct : forall p q, points_distinct p q -> p <> q.
Proof.
  intros p q H E. subst q. destruct H; contradiction.
Qed.

Lemma edge_sep : forall A B C, 0 < cross A B C -> A <> B /\ B <> C /\ C <> A.
Proof.
  intros A B C H. repeat split; intros E; subst;
    unfold cross in H; ring_simplify in H; lra.
Qed.

Lemma in_hull_dup : forall a x, in_hull [a; a] x -> x = a.
Proof.
  intros a x Hx. apply in_hull_on_seg in Hx. destruct Hx as [t [_ Hx]].
  rewrite Hx. unfold convex_combination. destruct a. simpl. f_equal; ring.
Qed.

Lemma hull_pair_of_two : forall ps X Y,
  Nat.le (length ps) 2 -> in_hull ps X -> in_hull ps Y -> X <> Y ->
  exists u v, ps = [u; v] /\ u <> v.
Proof.
  intros ps X Y Hlen HX HY Hne.
  destruct ps as [|u [|v [|w rest]]]; simpl in Hlen; try lia.
  - exfalso. apply (in_hull_nil X HX).
  - exfalso. apply Hne. apply in_hull_one in HX. apply in_hull_one in HY.
    subst. reflexivity.
  - exists u, v. split; [reflexivity|]. intros Heq. subst v. apply Hne.
    assert (Xu : X = u) by (apply in_hull_dup; exact HX).
    assert (Yu : Y = u) by (apply in_hull_dup; exact HY).
    subst. reflexivity.
Qed.

Lemma combo_sep : forall P Q t h,
  P <> Q -> h <> 0 ->
  convex_combination P Q (t + h) <> convex_combination P Q t.
Proof.
  intros P Q t h Hne Hh Heq.
  destruct P as [px0 py0], Q as [qx qy].
  unfold convex_combination in Heq. simpl in Heq. inversion Heq as [Hx].
  assert (Ex : h * (qx - px0) = 0) by lra.
  assert (Ey : h * (qy - py0) = 0) by lra.
  apply Rmult_integral in Ex. apply Rmult_integral in Ey.
  destruct Ex as [Eh|Ex]; [| destruct Ey as [Eh|Ey]].
  - apply Hh. exact Eh.
  - apply Hh. exact Eh.
  - apply Hne. f_equal; lra.
Qed.

Lemma slack_step : forall s ds h,
  0 < s -> Rabs h <= s / (1 + Rabs ds) / 2 -> 0 < s + h * ds.
Proof.
  intros s ds h Hs Hmag.
  assert (Hden : 0 < 1 + Rabs ds) by (pose proof (Rabs_pos ds); lra).
  assert (Hds : Rabs ds <= 1 + Rabs ds) by (pose proof (Rabs_pos ds); lra).
  assert (Hh : Rabs (h * ds) <= s / 2).
  { rewrite Rabs_mult.
    apply Rle_trans with (r2 := (s / (1 + Rabs ds) / 2) * Rabs ds).
    - apply Rmult_le_compat_r; [apply Rabs_pos | exact Hmag].
    - apply Rle_trans with (r2 := (s / (1 + Rabs ds) / 2) * (1 + Rabs ds)).
      + apply Rmult_le_compat_l; [| exact Hds].
        apply Rlt_le. apply Rdiv_lt_0_compat; [| lra].
        apply Rdiv_lt_0_compat; [exact Hs | exact Hden].
      + replace ((s / (1 + Rabs ds) / 2) * (1 + Rabs ds)) with (s / 2)
          by (field; lra).
        apply Rle_refl. }
  pose proof (Rle_abs (- (h * ds))) as Hneg.
  rewrite Rabs_Ropp in Hneg.
  assert (Hdrop : - Rabs (h * ds) <= h * ds) by lra.
  lra.
Qed.

Lemma open_spread : forall A B C P Q X t,
  P <> Q -> tri_open A B C X -> 0 <= t <= 1 ->
  X = convex_combination P Q t ->
  exists Y, Y <> X /\ tri_open A B C Y /\ on_seg P Q Y.
Proof.
  intros A B C P Q X t Hne Hopen Ht HX.
  destruct Hopen as [Hab [Hbc Hca]].
  set (dAB := cross A B Q - cross A B P).
  set (dBC := cross B C Q - cross B C P).
  set (dCA := cross C A Q - cross C A P).
  set (endroom := if Rlt_dec t 1 then (1 - t) / 2 else t / 2).
  assert (Hend : 0 < endroom).
  { unfold endroom. destruct (Rlt_dec t 1); destruct Ht; lra. }
  set (mag := Rmin endroom
               (Rmin (cross A B X / (1 + Rabs dAB) / 2)
                     (Rmin (cross B C X / (1 + Rabs dBC) / 2)
                           (cross C A X / (1 + Rabs dCA) / 2)))).
  assert (Hmag : 0 < mag).
  { unfold mag. apply Rmin_pos; [exact Hend|]. apply Rmin_pos.
    - apply Rdiv_lt_0_compat; [| lra].
      apply Rdiv_lt_0_compat; [exact Hab | pose proof (Rabs_pos dAB); lra].
    - apply Rmin_pos.
      + apply Rdiv_lt_0_compat; [| lra].
        apply Rdiv_lt_0_compat; [exact Hbc | pose proof (Rabs_pos dBC); lra].
      + apply Rdiv_lt_0_compat; [| lra].
        apply Rdiv_lt_0_compat; [exact Hca | pose proof (Rabs_pos dCA); lra]. }
  set (h := if Rlt_dec t 1 then mag else - mag).
  assert (Hh0 : h <> 0) by (unfold h; destruct (Rlt_dec t 1); lra).
  assert (Habs_h : Rabs h = mag).
  { unfold h. destruct (Rlt_dec t 1).
    - rewrite Rabs_right; [reflexivity | apply Rle_ge, Rlt_le, Hmag].
    - rewrite Rabs_Ropp. rewrite Rabs_right; [reflexivity | apply Rle_ge, Rlt_le, Hmag]. }
  assert (Hrange : 0 <= t + h <= 1).
  { unfold h. destruct (Rlt_dec t 1) as [Ht1|Ht1].
    - assert (mag <= (1 - t) / 2).
      { unfold mag, endroom. destruct (Rlt_dec t 1); [apply Rmin_l | contradiction]. }
      split; [apply Rlt_le in Hmag; lra | destruct Ht; lra].
    - assert (t = 1) by (destruct Ht; lra). subst t.
      assert (mag <= 1 / 2).
      { unfold mag, endroom. destruct (Rlt_dec 1 1) as [H11|H11].
        - exfalso. lra.
        - apply Rmin_l. }
      split; [apply Rlt_le in Hmag; lra | apply Rlt_le in Hmag; lra]. }
  set (Y := convex_combination P Q (t + h)).
  assert (Halong : forall p q,
            cross p q Y = cross p q X + h * (cross p q Q - cross p q P)).
  { intros p q. unfold Y. rewrite cross_combo. rewrite HX. rewrite cross_combo. ring. }
  assert (Hmag_le : forall s ds, 0 < s ->
            mag <= s / (1 + Rabs ds) / 2 -> Rabs h <= s / (1 + Rabs ds) / 2).
  { intros s ds Hs Hle. rewrite Habs_h. exact Hle. }
  assert (HAB : 0 < cross A B Y).
  { rewrite Halong. apply slack_step; [exact Hab|].
    apply Hmag_le; [exact Hab|]. unfold mag.
    apply Rle_trans with
      (r2 := Rmin (cross A B X / (1 + Rabs dAB) / 2)
                  (Rmin (cross B C X / (1 + Rabs dBC) / 2)
                        (cross C A X / (1 + Rabs dCA) / 2))).
    - apply Rmin_r.
    - apply Rle_trans with (r2 := cross A B X / (1 + Rabs dAB) / 2).
      + apply Rmin_l.
      + unfold dAB. lra. }
  assert (HBC : 0 < cross B C Y).
  { rewrite Halong. apply slack_step; [exact Hbc|].
    rewrite Habs_h. unfold mag.
    apply Rle_trans with
      (r2 := Rmin (cross A B X / (1 + Rabs dAB) / 2)
                  (Rmin (cross B C X / (1 + Rabs dBC) / 2)
                        (cross C A X / (1 + Rabs dCA) / 2))).
    - apply Rmin_r.
    - apply Rle_trans with
        (r2 := Rmin (cross B C X / (1 + Rabs dBC) / 2)
                    (cross C A X / (1 + Rabs dCA) / 2)).
      + apply Rmin_r.
      + apply Rmin_l. }
  assert (HCA : 0 < cross C A Y).
  { rewrite Halong. apply slack_step; [exact Hca|].
    rewrite Habs_h. unfold mag.
    apply Rle_trans with
      (r2 := Rmin (cross A B X / (1 + Rabs dAB) / 2)
                  (Rmin (cross B C X / (1 + Rabs dBC) / 2)
                        (cross C A X / (1 + Rabs dCA) / 2))).
    - apply Rmin_r.
    - apply Rle_trans with
        (r2 := Rmin (cross B C X / (1 + Rabs dBC) / 2)
                    (cross C A X / (1 + Rabs dCA) / 2)).
      + apply Rmin_r.
      + apply Rmin_r. }
  exists Y. split; [| split].
  - unfold Y. rewrite HX. apply combo_sep; [exact Hne | exact Hh0].
  - repeat split; assumption.
  - exists (t + h). split; [exact Hrange | unfold Y; reflexivity].
Qed.

Lemma tri_open_in : forall A B C X,
  0 < cross A B C -> tri_open A B C X -> in_tri A B C X.
Proof.
  intros A B C X Hd [Hab [Hbc Hca]].
  apply (proj1 (tri_slack_hull A B C X Hd)).
  repeat split; apply Rlt_le; assumption.
Qed.

Lemma seg_mid_open : forall A B C u v,
  0 < cross A B C -> u <> v ->
  in_tri A B C u -> in_tri A B C v ->
  (exists X, on_seg u v X /\ tri_open A B C X) ->
  tri_open A B C (convex_combination u v (1 / 2)).
Proof.
  intros A B C u v HA Hne Hu Hv [X [HXs HXo]].
  destruct HXo as [Hab [Hbc Hca]].
  apply tri_slack_hull in Hu; [| exact HA].
  apply tri_slack_hull in Hv; [| exact HA].
  destruct Hu as [Hau [Hbu Hcu]]. destruct Hv as [Hav [Hbv Hcv]].
  set (M := convex_combination u v (1 / 2)).
  assert (Em : forall p q, cross p q M = (cross p q u + cross p q v) / 2).
  { intros p q. unfold M. rewrite cross_combo. field. }
  assert (Hone : forall p q su sv sx,
            su = cross p q u -> sv = cross p q v -> sx = cross p q X ->
            0 <= su -> 0 <= sv -> 0 < sx -> 0 < cross p q M).
  { intros p q su sv sx Hsu Hsv Hsx Hsu0 Hsv0 Hsx0.
    rewrite Em. apply Rnot_le_lt. intros Hle.
    assert (su = 0 /\ sv = 0) by (rewrite <- Hsu, <- Hsv in Hle; lra).
    destruct H as [Eu Ev].
    destruct HXs as [t [Ht HXt]].
    assert (cross p q X = 0).
    { rewrite HXt. rewrite cross_combo. rewrite <- Hsu, <- Hsv, Eu, Ev. ring. }
    lra. }
  repeat split.
  - eapply Hone; try reflexivity; eassumption.
  - eapply Hone; try reflexivity; eassumption.
  - eapply Hone; try reflexivity; eassumption.
Qed.

Definition edge_meets_open_b (A B C P Q : Point) : bool :=
  match seg_clip_tri P Q A B C with
  | [u; v] =>
      if point_eqb u v then false
      else tri_open_b A B C (convex_combination u v (1 / 2))
  | _ => false
  end.

Lemma edge_open_iff : forall A B C P Q,
  0 < cross A B C -> P <> Q ->
  edge_meets_open_b A B C P Q = true <->
  exists X, tri_open A B C X /\ on_seg P Q X.
Proof.
  intros A B C P Q HA Hne. split.
  - intros Hb. unfold edge_meets_open_b in Hb.
    destruct (seg_clip_tri P Q A B C) as [|u [|v [|]]] eqn:E; try discriminate.
    destruct (point_eqb u v) eqn:Eq; [discriminate|].
    apply tri_open_b_true in Hb.
    assert (Huv : u <> v).
    { intros Heq. subst v. rewrite point_eqb_refl in Eq. discriminate. }
    assert (Hm : in_hull (seg_clip_tri P Q A B C)
                   (convex_combination u v (1 / 2))).
    { rewrite E. apply seg_mem. lra. }
    apply seg_clip_tri_correct in Hm; [| exact HA].
    destruct Hm as [Hs _]. exists (convex_combination u v (1 / 2)).
    split; assumption.
  - intros [X [Hopen Hs]].
    destruct Hs as [t [Ht HX]].
    destruct (open_spread A B C P Q X t Hne Hopen Ht HX) as [Y [HXY [HYo HYs]]].
    assert (Xin : in_hull (seg_clip_tri P Q A B C) X).
    { apply seg_clip_tri_correct; [exact HA|]. split.
      - exists t. split; assumption.
      - apply tri_open_in; assumption. }
    assert (Yin : in_hull (seg_clip_tri P Q A B C) Y).
    { apply seg_clip_tri_correct; [exact HA|]. split; [exact HYs|].
      apply tri_open_in; assumption. }
    destruct (hull_pair_of_two (seg_clip_tri P Q A B C) X Y)
      as [u [v [Euv Huv]]].
    { apply seg_clip_tri_len. }
    { exact Xin. }
    { exact Yin. }
    { intros E. apply HXY. symmetry. exact E. }
    assert (Hu : in_tri A B C u).
    { destruct (proj1 (seg_clip_tri_correct P Q A B C u HA)
        ltac:(rewrite Euv; apply in_hull_in; simpl; auto)) as [_ Htri].
      exact Htri. }
    assert (Hv : in_tri A B C v).
    { destruct (proj1 (seg_clip_tri_correct P Q A B C v HA)
        ltac:(rewrite Euv; apply in_hull_in; simpl; auto)) as [_ Htri].
      exact Htri. }
    assert (Xuv : on_seg u v X).
    { apply in_hull_on_seg. rewrite <- Euv. exact Xin. }
    assert (Hmid : tri_open A B C (convex_combination u v (1 / 2))).
    { apply seg_mid_open; try assumption. exists X. split; assumption. }
    unfold edge_meets_open_b. rewrite Euv.
    rewrite (point_eqb_false_neq u v Huv).
    apply tri_open_b_true. exact Hmid.
Qed.

Lemma seg_slack_nonpos : forall p q P Q X,
  cross p q P <= 0 -> cross p q Q <= 0 -> on_seg P Q X -> cross p q X <= 0.
Proof.
  intros p q P Q X Hp Hq [t [Ht ->]].
  rewrite cross_combo.
  assert (H1 : (1 - t) * cross p q P <= 0).
  { replace 0 with ((1 - t) * 0) by ring. apply Rmult_le_compat_l; lra. }
  assert (H2 : t * cross p q Q <= 0).
  { replace 0 with (t * 0) by ring. apply Rmult_le_compat_l; lra. }
  lra.
Qed.

Lemma on_edge_in_tri : forall A B C X, on_seg A B X -> in_tri A B C X.
Proof.
  intros A B C X Hs. apply in_tri_hull3.
  apply in_hull_embed2 with (a := A) (b := B).
  - simpl. left. reflexivity.
  - simpl. right. left. reflexivity.
  - apply in_hull_on_seg. exact Hs.
Qed.

Lemma dist_pos_neq : forall A B, A <> B -> 0 < dist_sq B A.
Proof.
  intros A B H. apply dist_sq_pos_iff_distinct.
  intros [Hx Hy]. apply H. destruct A, B. simpl in Hx, Hy. subst. reflexivity.
Qed.

Lemma on_line_combo : forall A B X,
  0 < dist_sq B A -> cross A B X = 0 ->
  X = convex_combination A B (seg_t A B X).
Proof.
  intros [ax ay] [bx by_] [xx xy] Hd Hz.
  unfold seg_t, dot, vsub, dist_sq, convex_combination, cross in *.
  simpl in *.
  set (dx := bx - ax) in *.
  set (dy := by_ - ay) in *.
  set (wx := xx - ax) in *.
  set (wy := xy - ay) in *.
  set (d2 := dx * dx + dy * dy) in *.
  set (num := wx * dx + wy * dy) in *.
  assert (Hd2 : d2 <> 0) by (unfold d2, dx, dy in *; lra).
  assert (Hc : dx * wy = wx * dy).
  { unfold dx, dy, wx, wy, cross in *. cbn in *. lra. }
  assert (Ex : d2 * wx = num * dx).
  { apply Rminus_diag_uniq. unfold d2, num.
    assert (E : (dx * dx + dy * dy) * wx - (wx * dx + wy * dy) * dx
                = dy * (wx * dy - dx * wy)) by ring.
    rewrite E. rewrite Hc. ring. }
  assert (Ey : d2 * wy = num * dy).
  { apply Rminus_diag_uniq. unfold d2, num.
    assert (E : (dx * dx + dy * dy) * wy - (wx * dx + wy * dy) * dy
                = dx * (dx * wy - wx * dy)) by ring.
    rewrite E. rewrite <- Hc. ring. }
  f_equal.
  - apply Rmult_eq_reg_l with (r := d2); [| exact Hd2].
    replace (d2 * xx) with (d2 * ax + d2 * wx) by (unfold wx; ring).
    rewrite Ex.
    replace (d2 * ((1 - num / d2) * ax + num / d2 * bx))
      with (d2 * ax + num * (bx - ax)) by (field; exact Hd2).
    unfold dx. ring.
  - apply Rmult_eq_reg_l with (r := d2); [| exact Hd2].
    replace (d2 * xy) with (d2 * ay + d2 * wy) by (unfold wy; ring).
    rewrite Ey.
    replace (d2 * ((1 - num / d2) * ay + num / d2 * by_))
      with (d2 * ay + num * (by_ - ay)) by (field; exact Hd2).
    unfold dy. ring.
Qed.

Lemma seg_t_combo : forall A B t,
  0 < dist_sq B A -> seg_t A B (convex_combination A B t) = t.
Proof.
  intros [ax ay] [bx by_] t Hd.
  unfold seg_t, dot, vsub, dist_sq, convex_combination in *. simpl.
  field. unfold dist_sq in Hd. simpl in Hd. lra.
Qed.

Lemma seg_t_left : forall A B, A <> B -> seg_t A B A = 0.
Proof.
  intros A B H. rewrite <- (seg_t_combo A B 0 (dist_pos_neq A B H)).
  f_equal. destruct A as [ax ay]. unfold convex_combination. simpl. f_equal; ring.
Qed.

Lemma seg_t_right : forall A B, A <> B -> seg_t A B B = 1.
Proof.
  intros A B H. rewrite <- (seg_t_combo A B 1 (dist_pos_neq A B H)).
  f_equal. destruct B as [bx by_]. unfold convex_combination. simpl. f_equal; ring.
Qed.

Lemma combo_affine : forall A B t1 t2 s,
  convex_combination (convex_combination A B t1) (convex_combination A B t2) s
    = convex_combination A B ((1 - s) * t1 + s * t2).
Proof.
  intros [ax ay] [bx by_] t1 t2 s.
  unfold convex_combination. simpl. f_equal; ring.
Qed.

Lemma combo_inj : forall A B t1 t2,
  A <> B -> convex_combination A B t1 = convex_combination A B t2 -> t1 = t2.
Proof.
  intros A B t1 t2 Hne Heq.
  assert (Hd := dist_pos_neq A B Hne).
  rewrite <- (seg_t_combo A B t1 Hd), <- (seg_t_combo A B t2 Hd), Heq.
  reflexivity.
Qed.

Definition on_seg_b (P Q X : Point) : bool :=
  if point_eqb P Q then point_eqb P X
  else if Req_dec_T (cross P Q X) 0 then
    if Rle_dec 0 (seg_t P Q X) then
      if Rle_dec (seg_t P Q X) 1 then true else false
    else false
  else false.

Lemma on_seg_b_iff : forall P Q X, on_seg_b P Q X = true <-> on_seg P Q X.
Proof.
  intros P Q X. split.
  - intros H. unfold on_seg_b in H.
    destruct (point_eqb P Q) eqn:Epq.
    + apply point_eqb_true in Epq. subst Q.
      apply point_eqb_true in H. subst X.
      exists 0. split; [lra|]. unfold convex_combination. destruct P. simpl.
      f_equal; ring.
    + destruct (Req_dec_T (cross P Q X) 0) as [Hz|Hz]; [| discriminate].
      destruct (Rle_dec 0 (seg_t P Q X)) as [Ht0|Ht0]; [| discriminate].
      destruct (Rle_dec (seg_t P Q X) 1) as [Ht1|Ht1]; [| discriminate].
      assert (Hne : P <> Q).
      { intros E. subst Q. rewrite point_eqb_refl in Epq. discriminate. }
      exists (seg_t P Q X). split; [lra|].
      apply on_line_combo; [apply dist_pos_neq; exact Hne | exact Hz].
  - intros [t [Ht HX]]. unfold on_seg_b.
    destruct (point_eqb P Q) eqn:Epq.
    + apply point_eqb_true in Epq. subst Q. rewrite HX.
      unfold convex_combination. destruct P as [ax ay]. simpl.
      replace ((1 - t) * ax + t * ax) with ax by ring.
      replace ((1 - t) * ay + t * ay) with ay by ring.
      apply point_eqb_refl.
    + assert (Hne : P <> Q).
      { intros E. subst Q. rewrite point_eqb_refl in Epq. discriminate. }
      assert (Hd := dist_pos_neq P Q Hne).
      assert (Hz : cross P Q X = 0).
      { rewrite HX. rewrite cross_combo.
        assert (Hp0 : cross P Q P = 0) by apply cross_at_P0_is_collinear.
        assert (Hq0 : cross P Q Q = 0) by (unfold cross; ring).
        rewrite Hp0, Hq0. ring. }
      assert (Et : seg_t P Q X = t).
      { rewrite HX. apply seg_t_combo. exact Hd. }
      destruct (Req_dec_T (cross P Q X) 0) as [_|Hn]; [ | contradiction].
      destruct (Rle_dec 0 (seg_t P Q X)) as [_|Hn0].
      { destruct (Rle_dec (seg_t P Q X) 1) as [_|Hn1]; [reflexivity|].
        exfalso. apply Hn1. rewrite Et. lra. }
      { exfalso. apply Hn0. rewrite Et. lra. }
Qed.

Definition overlap_pos_b (A B D E : Point) : bool :=
  if point_eqb A B then false
  else if point_eqb D E then false
  else if Req_dec_T (cross A B D) 0 then
    if Req_dec_T (cross A B E) 0 then
      let tD := seg_t A B D in
      let tE := seg_t A B E in
      let lo := Rmax 0 (Rmin tD tE) in
      let hi := Rmin 1 (Rmax tD tE) in
      if Rlt_dec lo hi then true else false
    else false
  else false.

Lemma overlap_pos_cross : forall A B D E,
  cross A B D <> 0 -> overlap_pos_b A B D E = false.
Proof.
  intros A B D E H. unfold overlap_pos_b.
  destruct (point_eqb A B); [reflexivity|].
  destruct (point_eqb D E); [reflexivity|].
  destruct (Req_dec_T (cross A B D) 0) as [Hz|Hz]; [contradiction | reflexivity].
Qed.

Lemma overlap_pos_b_true : forall A B D E,
  A <> B -> D <> E ->
  cross A B D = 0 -> cross A B E = 0 ->
  Rmax 0 (Rmin (seg_t A B D) (seg_t A B E)) <
    Rmin 1 (Rmax (seg_t A B D) (seg_t A B E)) ->
  overlap_pos_b A B D E = true.
Proof.
  intros A B D E HAB HDE Hd He Hlt. unfold overlap_pos_b.
  rewrite (point_eqb_false_neq A B HAB).
  rewrite (point_eqb_false_neq D E HDE).
  destruct (Req_dec_T (cross A B D) 0) as [_|Hn]; [| contradiction].
  destruct (Req_dec_T (cross A B E) 0) as [_|Hn]; [| contradiction].
  destruct (Rlt_dec (Rmax 0 (Rmin (seg_t A B D) (seg_t A B E)))
                    (Rmin 1 (Rmax (seg_t A B D) (seg_t A B E))));
    [reflexivity | contradiction].
Qed.

Lemma overlap_same : forall A B, A <> B -> overlap_pos_b A B A B = true.
Proof.
  intros A B Hne.
  apply overlap_pos_b_true; try assumption.
  - apply cross_at_P0_is_collinear.
  - unfold cross. ring.
  - rewrite (seg_t_left A B Hne), (seg_t_right A B Hne).
    rewrite (Rmin_left 0 1) by lra.
    rewrite (Rmax_right 0 1) by lra.
    rewrite (Rmax_left 0 0) by lra.
    rewrite (Rmin_left 1 1) by lra.
    lra.
Qed.

Definition proper_cross_b (A B D E : Point) : bool :=
  if Rlt_dec (cross A B D * cross A B E) 0 then
    if Rlt_dec (cross D E A * cross D E B) 0 then true else false
  else false.

Definition endpoint_on_b (A B D E : Point) : bool :=
  on_seg_b A B D || on_seg_b A B E || on_seg_b D E A || on_seg_b D E B.

Lemma affine_zero_prod : forall a b t,
  0 <= t <= 1 -> (1 - t) * a + t * b = 0 -> a * b <= 0.
Proof.
  intros a b t [Ht0 Ht1] Hz.
  destruct (Req_dec t 0) as [->|Hn0].
  - ring_simplify in Hz. rewrite Hz. lra.
  - destruct (Req_dec t 1) as [->|Hn1].
    + ring_simplify in Hz. rewrite Hz. lra.
    + assert (Ha : a = - (t / (1 - t)) * b).
      { assert (He : (1 - t) * a = - t * b) by lra.
        apply Rmult_eq_reg_l with (r := 1 - t); [| lra].
        replace ((1 - t) * (- (t / (1 - t)) * b)) with (- t * b)
          by (field; lra).
        exact He. }
      rewrite Ha.
      assert (0 <= b * b) by apply Rle_0_sqr.
      assert (0 < t / (1 - t)) by (apply Rdiv_lt_0_compat; lra).
      replace ((- (t / (1 - t)) * b) * b) with (- (t / (1 - t) * (b * b))) by ring.
      assert (0 <= t / (1 - t) * (b * b)) by (apply Rmult_le_pos; lra).
      lra.
Qed.

Lemma share_prod_nonpos : forall A B D E X,
  on_seg A B X -> on_seg D E X ->
  cross A B D * cross A B E <= 0 /\ cross D E A * cross D E B <= 0.
Proof.
  intros A B D E X [s [Hs HXs]] [r [Hr HXr]].
  assert (HA0 : cross A B A = 0) by apply cross_at_P0_is_collinear.
  assert (HB0 : cross A B B = 0) by (unfold cross; ring).
  assert (HD0 : cross D E D = 0) by apply cross_at_P0_is_collinear.
  assert (HE0 : cross D E E = 0) by (unfold cross; ring).
  split.
  - apply affine_zero_prod with (t := r); [exact Hr|].
    rewrite <- (cross_combo A B D E r), <- HXr, HXs, cross_combo.
    rewrite HA0, HB0. ring.
  - apply affine_zero_prod with (t := s); [exact Hs|].
    rewrite <- (cross_combo D E A B s), <- HXs, HXr, cross_combo.
    rewrite HD0, HE0. ring.
Qed.

Lemma cross_line_diff : forall A B D E,
  cross A B E - cross A B D =
    (px B - px A) * (py E - py D) - (px E - px D) * (py B - py A).
Proof. intros. unfold cross. ring. Qed.

Lemma one_intersection : forall A B D E P Q,
  cross A B E - cross A B D <> 0 ->
  cross A B P = 0 -> cross A B Q = 0 ->
  cross D E P = 0 -> cross D E Q = 0 -> P = Q.
Proof.
  intros [ax ay] [bx by_] [dx dy] [ex ey] [px0 py0] [qx qy] Hn HpA HqA HpD HqD.
  unfold cross in *. simpl in *.
  assert (Hx : (bx - ax) * (qy - py0) = (qx - px0) * (by_ - ay)) by lra.
  assert (Hy : (ex - dx) * (qy - py0) = (qx - px0) * (ey - dy)) by lra.
  assert (Edir : (bx - ax) * (ey - ay) - (ex - ax) * (by_ - ay)
                 - ((bx - ax) * (dy - ay) - (dx - ax) * (by_ - ay))
                 = (bx - ax) * (ey - dy) - (ex - dx) * (by_ - ay)) by ring.
  rewrite Edir in Hn.
  assert (Hdet : (bx - ax) * (ey - dy) - (ex - dx) * (by_ - ay) <> 0)
    by exact Hn.
  assert (Ewx : (qx - px0) * ((bx - ax) * (ey - dy) - (ex - dx) * (by_ - ay)) = 0).
  { assert (E : (qx - px0) * ((bx - ax) * (ey - dy) - (ex - dx) * (by_ - ay))
                = (bx - ax) * ((qx - px0) * (ey - dy) - (ex - dx) * (qy - py0))
                  - (ex - dx) * ((qx - px0) * (by_ - ay) - (bx - ax) * (qy - py0)))
      by ring.
    rewrite E. rewrite <- Hx, <- Hy. ring. }
  assert (Ewy : (qy - py0) * ((bx - ax) * (ey - dy) - (ex - dx) * (by_ - ay)) = 0).
  { assert (E : (qy - py0) * ((bx - ax) * (ey - dy) - (ex - dx) * (by_ - ay))
                = (ey - dy) * ((bx - ax) * (qy - py0) - (qx - px0) * (by_ - ay))
                  - (by_ - ay) * ((ex - dx) * (qy - py0) - (qx - px0) * (ey - dy)))
      by ring.
    rewrite E, Hx, Hy. ring. }
  apply Rmult_integral in Ewx. apply Rmult_integral in Ewy.
  destruct Ewx as [Ewx|Ewx]; [| contradiction].
  destruct Ewy as [Ewy|Ewy]; [| contradiction].
  f_equal; lra.
Qed.

Lemma opp_prod_pos : forall a b, a < 0 -> b < 0 -> 0 < a * b.
Proof.
  intros a b Ha Hb.
  assert (0 < - a) by lra.
  assert (0 < - b) by lra.
  assert (0 < (- a) * (- b)) by (apply Rmult_lt_0_compat; assumption).
  replace (a * b) with ((- a) * (- b)) by ring. assumption.
Qed.

Lemma proper_cross_point : forall A B D E,
  cross A B D * cross A B E < 0 ->
  cross D E A * cross D E B < 0 ->
  exists X, on_seg A B X /\ on_seg D E X.
Proof.
  intros A B D E H1 H2.
  assert (HAB : A <> B).
  { intros Eeq. subst B. unfold cross in H1. ring_simplify in H1. lra. }
  assert (HDE : D <> E).
  { intros Eeq. subst E. unfold cross in H2. ring_simplify in H2. lra. }
  assert (Hd1 : cross A B D - cross A B E <> 0).
  { intro Eq.
    assert (Eeq : cross A B D = cross A B E) by (apply Rminus_diag_uniq; exact Eq).
    rewrite Eeq in H1.
    pose proof (Rle_0_sqr (cross A B E)) as Hs. apply (Rle_not_lt _ _ Hs). exact H1. }
  assert (Hd2 : cross D E A - cross D E B <> 0).
  { intro Eq.
    assert (Eeq : cross D E A = cross D E B) by (apply Rminus_diag_uniq; exact Eq).
    rewrite Eeq in H2.
    pose proof (Rle_0_sqr (cross D E B)) as Hs. apply (Rle_not_lt _ _ Hs). exact H2. }
  destruct (Rle_dec 0 (cross A B D)) as [HDd|HDd].
  - assert (HEd : cross A B E < 0).
    { apply Rnot_le_lt. intros Hle.
      pose proof (Rmult_le_pos _ _ HDd Hle) as Hp.
      apply (Rle_not_lt (cross A B D * cross A B E) 0 Hp). exact H1. }
    destruct (line_hit_on_seg D E A B) as [t [Ht [Heq Hz]]].
    { left. split; [exact HDd | exact HEd]. }
    set (s := cross D E A / (cross D E A - cross D E B)).
    destruct (hit_param_01 (cross D E A) (cross D E B)) as [_ [Hs0 Hs1]].
    { destruct (Rle_dec 0 (cross D E A)) as [Ha|Ha].
      - left. split; [exact Ha|]. apply Rnot_le_lt. intros Hb.
        pose proof (Rmult_le_pos _ _ Ha Hb) as Hp.
        apply (Rle_not_lt (cross D E A * cross D E B) 0 Hp). exact H2.
      - right. split; [apply Rnot_le_lt; exact Ha|].
        apply Rnot_lt_le. intros Hb.
        assert (Ha' : cross D E A < 0) by (apply Rnot_le_lt; exact Ha).
        pose proof (opp_prod_pos _ _ Ha' Hb) as Hp.
        apply (Rlt_not_le (cross D E A * cross D E B) 0 Hp).
        apply Rlt_le. exact H2. }
    set (X := line_hit D E A B).
    set (Y := convex_combination A B s).
    assert (HY0 : cross A B Y = 0).
    { unfold Y. rewrite cross_combo.
      rewrite (cross_at_P0_is_collinear A B).
      replace (cross A B B) with 0 by (unfold cross; ring). ring. }
    assert (HYd : cross D E Y = 0).
    { unfold Y, s. rewrite cross_combo. field. exact Hd2. }
    assert (HX0 : cross A B X = 0) by (unfold X; exact Hz).
    assert (HXd : cross D E X = 0).
    { unfold X. rewrite Heq. rewrite cross_combo.
      rewrite (cross_at_P0_is_collinear D E).
      replace (cross D E E) with 0 by (unfold cross; ring). ring. }
    assert (Hdir : cross A B E - cross A B D <> 0) by lra.
    assert (EXY : X = Y).
    { apply (one_intersection A B D E X Y Hdir HX0 HY0 HXd HYd). }
    exists X. split.
    + rewrite EXY. exists s. split; [split; assumption | reflexivity].
    + exists t. split; [exact Ht | unfold X; exact Heq].
  - assert (HDd' : cross A B D < 0) by (apply Rnot_le_lt; exact HDd).
    assert (HEd : 0 <= cross A B E).
    { apply Rnot_lt_le. intros Hlt.
      pose proof (opp_prod_pos _ _ HDd' Hlt) as Hp.
      apply (Rlt_not_le (cross A B D * cross A B E) 0 Hp).
      apply Rlt_le. exact H1. }
    destruct (line_hit_on_seg D E A B) as [t [Ht [Heq Hz]]].
    { right. split; [exact HDd' | exact HEd]. }
    set (s := cross D E A / (cross D E A - cross D E B)).
    destruct (hit_param_01 (cross D E A) (cross D E B)) as [_ [Hs0 Hs1]].
    { destruct (Rle_dec 0 (cross D E A)) as [Ha|Ha].
      - left. split; [exact Ha|]. apply Rnot_le_lt. intros Hb.
        pose proof (Rmult_le_pos _ _ Ha Hb) as Hp.
        apply (Rle_not_lt (cross D E A * cross D E B) 0 Hp). exact H2.
      - right. split; [apply Rnot_le_lt; exact Ha|].
        destruct (Rle_dec 0 (cross D E B)) as [Hb|Hb]; [exact Hb|].
        exfalso.
        assert (Ha' : cross D E A < 0) by (apply Rnot_le_lt; exact Ha).
        assert (Hb' : cross D E B < 0) by (apply Rnot_le_lt; exact Hb).
        pose proof (opp_prod_pos _ _ Ha' Hb') as Hp.
        apply (Rlt_not_le (cross D E A * cross D E B) 0 Hp).
        apply Rlt_le. exact H2. }
    set (X := line_hit D E A B).
    set (Y := convex_combination A B s).
    assert (HY0 : cross A B Y = 0).
    { unfold Y. rewrite cross_combo.
      rewrite (cross_at_P0_is_collinear A B).
      replace (cross A B B) with 0 by (unfold cross; ring). ring. }
    assert (HYd : cross D E Y = 0).
    { unfold Y, s. rewrite cross_combo. field. exact Hd2. }
    assert (HX0 : cross A B X = 0) by (unfold X; exact Hz).
    assert (HXd : cross D E X = 0).
    { unfold X. rewrite Heq. rewrite cross_combo.
      rewrite (cross_at_P0_is_collinear D E).
      replace (cross D E E) with 0 by (unfold cross; ring). ring. }
    assert (Hdir : cross A B E - cross A B D <> 0) by lra.
    assert (EXY : X = Y).
    { apply (one_intersection A B D E X Y Hdir HX0 HY0 HXd HYd). }
    exists X. split.
    + rewrite EXY. exists s. split; [split; assumption | reflexivity].
    + exists t. split; [exact Ht | unfold X; exact Heq].
Qed.

Lemma endpoint_share : forall A B D E,
  endpoint_on_b A B D E = true -> exists X, on_seg A B X /\ on_seg D E X.
Proof.
  intros A B D E H. unfold endpoint_on_b in H.
  apply orb_true_iff in H. destruct H as [H|H].
  apply orb_true_iff in H. destruct H as [H|H].
  apply orb_true_iff in H. destruct H as [H|H].
  - apply on_seg_b_iff in H. exists D. split; [exact H | exists 0].
    split; [lra|]. unfold convex_combination. destruct D as [dx dy].
    simpl. f_equal; ring.
  - apply on_seg_b_iff in H. exists E. split; [exact H | exists 1].
    split; [lra|]. unfold convex_combination. destruct E as [ex ey].
    simpl. f_equal; ring.
  - apply on_seg_b_iff in H. exists A. split; [| exact H]. exists 0.
    split; [lra|]. unfold convex_combination. destruct A as [ax ay].
    simpl. f_equal; ring.
  - apply on_seg_b_iff in H. exists B. split; [| exact H]. exists 1.
    split; [lra|]. unfold convex_combination. destruct B as [bx by_].
    simpl. f_equal; ring.
Qed.

Lemma on_seg_cross0 : forall P Q X, on_seg P Q X -> cross P Q X = 0.
Proof.
  intros P Q X [t [_ ->]]. rewrite cross_combo.
  rewrite (cross_at_P0_is_collinear P Q).
  replace (cross P Q Q) with 0 by (unfold cross; ring). ring.
Qed.

Lemma combo_left : forall A B, convex_combination A B 0 = A.
Proof.
  intros A B. unfold convex_combination. destruct A as [ax ay]. simpl. f_equal; ring.
Qed.

Lemma combo_right : forall A B, convex_combination A B 1 = B.
Proof.
  intros A B. unfold convex_combination. destruct B as [bx by_]. simpl. f_equal; ring.
Qed.

Lemma proper_cross_b_true : forall A B D E,
  cross A B D * cross A B E < 0 ->
  cross D E A * cross D E B < 0 ->
  proper_cross_b A B D E = true.
Proof.
  intros A B D E H1 H2. unfold proper_cross_b.
  destruct (Rlt_dec (cross A B D * cross A B E) 0); [| contradiction].
  destruct (Rlt_dec (cross D E A * cross D E B) 0); [reflexivity | contradiction].
Qed.

Lemma proper_cross_share : forall A B D E,
  proper_cross_b A B D E = true -> exists X, on_seg A B X /\ on_seg D E X.
Proof.
  intros A B D E H. unfold proper_cross_b in H.
  destruct (Rlt_dec (cross A B D * cross A B E) 0) as [H1|H1]; [| discriminate].
  destruct (Rlt_dec (cross D E A * cross D E B) 0) as [H2|H2]; [| discriminate].
  apply proper_cross_point; assumption.
Qed.

Lemma endpoint_on_intro : forall A B D E,
  on_seg A B D \/ on_seg A B E \/ on_seg D E A \/ on_seg D E B ->
  endpoint_on_b A B D E = true.
Proof.
  intros A B D E H. unfold endpoint_on_b.
  destruct H as [H|[H|[H|H]]].
  - apply orb_true_iff. left. apply orb_true_iff. left. apply orb_true_iff. left.
    apply on_seg_b_iff. exact H.
  - apply orb_true_iff. left. apply orb_true_iff. left. apply orb_true_iff. right.
    apply on_seg_b_iff. exact H.
  - apply orb_true_iff. left. apply orb_true_iff. right.
    apply on_seg_b_iff. exact H.
  - apply orb_true_iff. right. apply on_seg_b_iff. exact H.
Qed.

Lemma cross_combo_line : forall D E p q r,
  cross (convex_combination D E p) (convex_combination D E q)
        (convex_combination D E r) = 0.
Proof.
  intros D E p q r. unfold convex_combination, cross.
  destruct D as [dx dy], E as [ex ey]. simpl. ring.
Qed.

Lemma line_cross_transfer : forall D E A B,
  D <> E -> cross D E A = 0 -> cross D E B = 0 ->
  cross A B D = 0 /\ cross A B E = 0.
Proof.
  intros D E A B Hne Ha Hb.
  assert (Hd := dist_pos_neq D E Hne).
  assert (EA := on_line_combo D E A Hd Ha).
  assert (EB := on_line_combo D E B Hd Hb).
  split.
  - replace D with (convex_combination D E 0) by (apply combo_left).
    rewrite EA, EB. apply cross_combo_line.
  - replace E with (convex_combination D E 1) by (apply combo_right).
    rewrite EA, EB. apply cross_combo_line.
Qed.

Lemma on_seg_forced_end : forall P Q R S X,
  on_seg P Q X -> on_seg R S X ->
  cross P Q R = 0 -> cross P Q S <> 0 -> X = R.
Proof.
  intros P Q R S X HPQ HRS HR HS.
  destruct HRS as [r [_ HX]].
  assert (Hz : cross P Q X = 0) by (apply on_seg_cross0; exact HPQ).
  rewrite HX, cross_combo, HR in Hz.
  assert (Hr0 : r * cross P Q S = 0).
  { ring_simplify in Hz. exact Hz. }
  apply Rmult_integral in Hr0. destruct Hr0 as [Hr0|Hr0]; [| contradiction].
  rewrite HX, Hr0. apply combo_left.
Qed.

Lemma mix_bounds : forall a b r,
  0 <= r <= 1 -> Rmin a b <= (1 - r) * a + r * b <= Rmax a b.
Proof.
  intros a b r [Hr0 Hr1].
  destruct (Rle_dec a b) as [Hab|Hab].
  - rewrite (Rmin_left a b Hab), (Rmax_right a b Hab).
    split.
    + assert ((1 - r) * a + r * a <= (1 - r) * a + r * b).
      { apply Rplus_le_compat_l. apply Rmult_le_compat_l; lra. }
      replace ((1 - r) * a + r * a) with a in * by ring. lra.
    + assert ((1 - r) * a + r * b <= (1 - r) * b + r * b).
      { apply Rplus_le_compat_r. apply Rmult_le_compat_l; lra. }
      replace ((1 - r) * b + r * b) with b in * by ring. lra.
  - assert (Hba : b < a) by (apply Rnot_le_lt; exact Hab).
    rewrite (Rmin_right a b (Rlt_le _ _ Hba)), (Rmax_left a b (Rlt_le _ _ Hba)).
    split.
    + assert ((1 - r) * b + r * b <= (1 - r) * a + r * b).
      { apply Rplus_le_compat_r. apply Rmult_le_compat_l; lra. }
      replace ((1 - r) * b + r * b) with b in * by ring. lra.
    + assert ((1 - r) * a + r * b <= (1 - r) * a + r * a).
      { apply Rplus_le_compat_l. apply Rmult_le_compat_l; lra. }
      replace ((1 - r) * a + r * a) with a in * by ring. lra.
Qed.

Lemma clamp_mem : forall m M s,
  m <= s <= M -> 0 <= s <= 1 -> Rmax 0 m <= s /\ s <= Rmin 1 M.
Proof.
  intros m M s [Hms HsM] [Hs0 Hs1]. split.
  - destruct (Rle_dec 0 m) as [Hm|Hm].
    + rewrite (Rmax_right 0 m Hm). exact Hms.
    + assert (Hm' : m < 0) by (apply Rnot_le_lt; exact Hm).
      rewrite (Rmax_left 0 m (Rlt_le _ _ Hm')). exact Hs0.
  - destruct (Rle_dec 1 M) as [HM|HM].
    + rewrite (Rmin_left 1 M HM). exact Hs1.
    + assert (HM' : M < 1) by (apply Rnot_le_lt; exact HM).
      rewrite (Rmin_right 1 M (Rlt_le _ _ HM')). exact HsM.
Qed.

Lemma mix_solve : forall a b t,
  a <> b -> Rmin a b <= t <= Rmax a b ->
  exists r, 0 <= r <= 1 /\ t = (1 - r) * a + r * b.
Proof.
  intros a b t Hne [Hlo Hhi].
  exists ((t - a) / (b - a)).
  split.
  - destruct (Rle_dec a b) as [Hab|Hab].
    + rewrite (Rmin_left a b Hab) in Hlo.
      rewrite (Rmax_right a b Hab) in Hhi.
      assert (Hd : 0 < b - a) by lra. split.
      * unfold Rdiv. apply Rmult_le_pos; [lra |].
        apply Rlt_le, Rinv_0_lt_compat. exact Hd.
      * apply Rmult_le_reg_r with (r := b - a); [exact Hd |].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; lra.
    + assert (Hba : b < a) by (apply Rnot_le_lt; exact Hab).
      rewrite (Rmin_right a b (Rlt_le _ _ Hba)) in Hlo.
      rewrite (Rmax_left a b (Rlt_le _ _ Hba)) in Hhi.
      assert (He : (t - a) / (b - a) = (a - t) / (a - b)) by (field; lra).
      rewrite He.
      assert (Hd : 0 < a - b) by lra. split.
      * unfold Rdiv. apply Rmult_le_pos; [lra |].
        apply Rlt_le, Rinv_0_lt_compat. exact Hd.
      * apply Rmult_le_reg_r with (r := a - b); [exact Hd |].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; lra.
  - field. lra.
Qed.

Lemma collinear_class : forall A B D E X,
  A <> B -> D <> E ->
  on_seg A B X -> on_seg D E X ->
  cross A B D = 0 -> cross A B E = 0 ->
  overlap_pos_b A B D E = true \/ endpoint_on_b A B D E = true.
Proof.
  intros A B D E X HAB HDE HXAB HXDE Hd He.
  destruct HXAB as [s [Hs HXs]].
  destruct HXDE as [r [Hr HXr]].
  set (tD := seg_t A B D). set (tE := seg_t A B E).
  assert (HdAB := dist_pos_neq A B HAB).
  assert (HD : D = convex_combination A B tD) by (apply on_line_combo; assumption).
  assert (HE : E = convex_combination A B tE) by (apply on_line_combo; assumption).
  assert (Hmix : X = convex_combination A B ((1 - r) * tD + r * tE)).
  { rewrite HXr, HD, HE. apply combo_affine. }
  assert (Es : s = (1 - r) * tD + r * tE).
  { apply (combo_inj A B); [exact HAB |]. rewrite <- HXs. exact Hmix. }
  assert (Hspan : Rmin tD tE <= s <= Rmax tD tE).
  { rewrite Es. apply mix_bounds. exact Hr. }
  set (lo := Rmax 0 (Rmin tD tE)).
  set (hi := Rmin 1 (Rmax tD tE)).
  assert (Hclamp : lo <= s /\ s <= hi).
  { unfold lo, hi. apply clamp_mem; [exact Hspan | exact Hs]. }
  destruct (Rlt_dec lo hi) as [Hlt|Hlt].
  - left. apply overlap_pos_b_true; assumption.
  - right.
    destruct Hclamp as [Hlos Hshi].
    assert (Elohi : lo = hi).
    { apply Rle_antisym; [| apply Rnot_lt_le; exact Hlt].
      apply Rle_trans with (r2 := s); assumption. }
    assert (Es0 : s = lo) by lra.
    assert (Hte : tD <> tE).
    { intros Ete. apply HDE. rewrite HD, HE, Ete. reflexivity. }
    destruct (Rlt_dec 0 s) as [Hspos|Hsnon].
    + destruct (Rlt_dec s 1) as [Hslt|Hsge].
      * exfalso.
        assert (Em : Rmin tD tE = s).
        { unfold lo in Es0.
          destruct (Rle_dec (Rmin tD tE) 0) as [Hm|Hm].
          - rewrite (Rmax_left 0 (Rmin tD tE) Hm) in Es0. lra.
          - rewrite (Rmax_right 0 (Rmin tD tE) (Rlt_le _ _ (Rnot_le_lt _ _ Hm)))
              in Es0. lra. }
        assert (EM : Rmax tD tE = s).
        { unfold hi in Elohi.
          destruct (Rle_dec 1 (Rmax tD tE)) as [HM|HM].
          - exfalso. rewrite (Rmin_left 1 (Rmax tD tE) HM) in Elohi. lra.
          - rewrite (Rmin_right 1 (Rmax tD tE)
              (Rlt_le _ _ (Rnot_le_lt _ _ HM))) in Elohi. lra. }
        assert (EtD : tD = s).
        { apply Rle_antisym.
          - rewrite <- EM. apply Rmax_l.
          - rewrite <- Em. apply Rmin_l. }
        assert (EtE : tE = s).
        { apply Rle_antisym.
          - rewrite <- EM. apply Rmax_r.
          - rewrite <- Em. apply Rmin_r. }
        apply Hte. rewrite EtD, EtE. reflexivity.
      * assert (Hs1 : s = 1) by (destruct Hs; lra).
        assert (XB : X = B).
        { rewrite HXs, Hs1. apply combo_right. }
        apply endpoint_on_intro. right. right. right.
        rewrite <- XB. exists r. split; [exact Hr | exact HXr].
    + assert (Hs0 : s = 0) by (destruct Hs; apply Rnot_lt_le in Hsnon; lra).
      assert (XA : X = A).
      { rewrite HXs, Hs0. apply combo_left. }
      apply endpoint_on_intro. right. right. left.
      rewrite <- XA. exists r. split; [exact Hr | exact HXr].
Qed.

Lemma on_seg_sym : forall P Q X, on_seg P Q X -> on_seg Q P X.
Proof.
  intros P Q X [t [Ht ->]]. exists (1 - t). split; [lra|].
  unfold convex_combination. destruct P as [px0 py0], Q as [qx qy].
  simpl. f_equal; ring.
Qed.

Lemma edge_touch_class : forall A B D E,
  A <> B -> D <> E ->
  (exists X, on_seg A B X /\ on_seg D E X) ->
  overlap_pos_b A B D E = true \/
  proper_cross_b A B D E = true \/
  endpoint_on_b A B D E = true.
Proof.
  intros A B D E HAB HDE [X [HXAB HXDE]].
  destruct (share_prod_nonpos A B D E X HXAB HXDE) as [HpAB HpDE].
  destruct (Rlt_dec (cross A B D * cross A B E) 0) as [HltAB|HnotAB].
  - destruct (Rlt_dec (cross D E A * cross D E B) 0) as [HltDE|HnotDE].
    + right. left. apply proper_cross_b_true; assumption.
    + right. right.
      assert (Hp0 : cross D E A * cross D E B = 0).
      { apply Rle_antisym; [| apply Rnot_lt_le; exact HnotDE]. exact HpDE. }
      apply Rmult_integral in Hp0. destruct Hp0 as [Ha0|Hb0].
      * destruct (Req_dec (cross D E B) 0) as [Hb0'|Hb0'].
        -- exfalso.
           destruct (line_cross_transfer D E A B HDE Ha0 Hb0') as [Hd0 He0].
           apply (Rlt_not_eq _ _ HltAB). rewrite Hd0, He0. ring.
        -- assert (XA : X = A).
           { apply (on_seg_forced_end D E A B X HXDE HXAB Ha0 Hb0'). }
           apply endpoint_on_intro. right. right. left. rewrite <- XA. exact HXDE.
      * assert (Hna : cross D E A <> 0).
        { intros Hz.
          destruct (line_cross_transfer D E A B HDE Hz Hb0) as [Hd0 He0].
          apply (Rlt_not_eq _ _ HltAB). rewrite Hd0, He0. ring. }
        assert (XB : X = B).
        { apply (on_seg_forced_end D E B A X HXDE (on_seg_sym _ _ _ HXAB) Hb0 Hna). }
        apply endpoint_on_intro. right. right. right. rewrite <- XB. exact HXDE.
  - assert (Hp0 : cross A B D * cross A B E = 0).
    { apply Rle_antisym; [| apply Rnot_lt_le; exact HnotAB]. exact HpAB. }
    apply Rmult_integral in Hp0. destruct Hp0 as [Hd0|He0].
    + destruct (Req_dec (cross A B E) 0) as [He0'|He0'].
      * destruct (collinear_class A B D E X HAB HDE HXAB HXDE Hd0 He0')
          as [Ho|Hen].
        -- left. exact Ho.
        -- right. right. exact Hen.
      * right. right.
        assert (XD : X = D).
        { apply (on_seg_forced_end A B D E X HXAB HXDE Hd0 He0'). }
        apply endpoint_on_intro. left. rewrite <- XD. exact HXAB.
    + destruct (Req_dec (cross A B D) 0) as [Hd0'|Hd0'].
      * destruct (collinear_class A B D E X HAB HDE HXAB HXDE Hd0' He0)
          as [Ho|Hen].
        -- left. exact Ho.
        -- right. right. exact Hen.
      * right. right.
        assert (XE : X = E).
        { apply (on_seg_forced_end A B E D X HXAB (on_seg_sym _ _ _ HXDE) He0 Hd0'). }
        apply endpoint_on_intro. right. left. rewrite <- XE. exact HXAB.
Qed.

Lemma overlap_segment : forall A B D E,
  overlap_pos_b A B D E = true ->
  exists U V, U <> V /\
    (forall X, on_seg U V X -> on_seg A B X /\ on_seg D E X).
Proof.
  intros A B D E H. unfold overlap_pos_b in H.
  destruct (point_eqb A B) eqn:Eab; [discriminate|].
  destruct (point_eqb D E) eqn:Ede; [discriminate|].
  destruct (Req_dec_T (cross A B D) 0) as [Hd|Hd]; [| discriminate].
  destruct (Req_dec_T (cross A B E) 0) as [He|He]; [| discriminate].
  set (tD := seg_t A B D) in *.
  set (tE := seg_t A B E) in *.
  set (lo := Rmax 0 (Rmin tD tE)) in *.
  set (hi := Rmin 1 (Rmax tD tE)) in *.
  destruct (Rlt_dec lo hi) as [Hlt|Hlt]; [| discriminate].
  assert (HAB : A <> B).
  { intros Eq. subst B. rewrite point_eqb_refl in Eab. discriminate. }
  assert (HDE : D <> E).
  { intros Eq. subst E. rewrite point_eqb_refl in Ede. discriminate. }
  assert (HdAB := dist_pos_neq A B HAB).
  assert (HD : D = convex_combination A B tD).
  { apply on_line_combo; assumption. }
  assert (HE : E = convex_combination A B tE).
  { apply on_line_combo; assumption. }
  set (U := convex_combination A B lo).
  set (V := convex_combination A B hi).
  assert (Huv : U <> V).
  { intros Eq. apply (Rlt_not_eq lo hi Hlt).
    apply (combo_inj A B lo hi HAB). unfold U, V in Eq. exact Eq. }
  assert (Hte : tD <> tE).
  { intros Ete. apply HDE. rewrite HD, HE, Ete. reflexivity. }
  exists U, V. split; [exact Huv|].
  intros X [s [Hs HX]].
  set (t := (1 - s) * lo + s * hi).
  assert (Et : X = convex_combination A B t).
  { rewrite HX. unfold U, V, t. apply combo_affine. }
  assert (Hlo0 : 0 <= lo).
  { unfold lo. destruct (Rle_dec 0 (Rmin tD tE)) as [Hm|Hm].
    - rewrite (Rmax_right 0 (Rmin tD tE) Hm). exact Hm.
    - rewrite (Rmax_left 0 (Rmin tD tE) (Rlt_le _ _ (Rnot_le_lt _ _ Hm))). lra. }
  assert (Hhi1 : hi <= 1).
  { unfold hi. destruct (Rle_dec 1 (Rmax tD tE)) as [HM|HM].
    - rewrite (Rmin_left 1 (Rmax tD tE) HM). lra.
    - rewrite (Rmin_right 1 (Rmax tD tE) (Rlt_le _ _ (Rnot_le_lt _ _ HM))).
      apply Rlt_le, Rnot_le_lt. exact HM. }
  assert (Htspan : lo <= t <= hi).
  { destruct Hs as [Hs0 Hs1].
    assert (Hlh : lo <= hi) by (apply Rlt_le; exact Hlt). split.
    - assert ((1 - s) * lo + s * lo <= t).
      { unfold t. apply Rplus_le_compat_l. apply Rmult_le_compat_l; lra. }
      replace ((1 - s) * lo + s * lo) with lo in * by ring. lra.
    - assert (t <= (1 - s) * hi + s * hi).
      { unfold t. apply Rplus_le_compat_r. apply Rmult_le_compat_l; lra. }
      replace ((1 - s) * hi + s * hi) with hi in * by ring. lra. }
  assert (Ht01 : 0 <= t <= 1) by (destruct Htspan; lra).
  assert (Hbetween : Rmin tD tE <= t <= Rmax tD tE).
  { destruct Htspan as [Htlo Hthi]. split.
    - apply Rle_trans with (r2 := lo); [| exact Htlo]. unfold lo. apply Rmax_r.
    - apply Rle_trans with (r2 := hi); [exact Hthi |]. unfold hi. apply Rmin_r. }
  split.
  - exists t. split; [exact Ht01 | exact Et].
  - destruct (mix_solve tD tE t Hte Hbetween) as [r [Hr Etm]].
    exists r. split; [exact Hr|].
    rewrite Et. replace t with ((1 - r) * tD + r * tE) by (symmetry; exact Etm).
    rewrite <- (combo_affine A B tD tE r). rewrite <- HD, <- HE. reflexivity.
Qed.
Print Assumptions supports_short.
Print Assumptions clip_halfplane_len2.
Print Assumptions in_hull_on_seg.
Print Assumptions seg_clip_tri_len.
Print Assumptions seg_clip_tri_correct.
Print Assumptions tri_open_b_true.
Print Assumptions point_eqb_false_neq.
Print Assumptions distinct_of_neq.
Print Assumptions neq_of_distinct.
Print Assumptions edge_sep.
Print Assumptions in_hull_dup.
Print Assumptions hull_pair_of_two.
Print Assumptions combo_sep.
Print Assumptions slack_step.
Print Assumptions open_spread.
Print Assumptions tri_open_in.
Print Assumptions seg_mid_open.
Print Assumptions edge_open_iff.
Print Assumptions seg_slack_nonpos.
Print Assumptions on_edge_in_tri.
Print Assumptions dist_pos_neq.
Print Assumptions on_line_combo.
Print Assumptions seg_t_combo.
Print Assumptions seg_t_left.
Print Assumptions seg_t_right.
Print Assumptions combo_affine.
Print Assumptions combo_inj.
Print Assumptions on_seg_b_iff.
Print Assumptions overlap_pos_cross.
Print Assumptions overlap_pos_b_true.
Print Assumptions overlap_same.
Print Assumptions affine_zero_prod.
Print Assumptions share_prod_nonpos.
Print Assumptions cross_line_diff.
Print Assumptions one_intersection.
Print Assumptions opp_prod_pos.
Print Assumptions proper_cross_point.
Print Assumptions endpoint_share.
Print Assumptions on_seg_cross0.
Print Assumptions combo_left.
Print Assumptions combo_right.
Print Assumptions proper_cross_b_true.
Print Assumptions proper_cross_share.
Print Assumptions endpoint_on_intro.
Print Assumptions cross_combo_line.
Print Assumptions line_cross_transfer.
Print Assumptions on_seg_forced_end.
Print Assumptions mix_bounds.
Print Assumptions clamp_mem.
Print Assumptions mix_solve.
Print Assumptions collinear_class.
Print Assumptions on_seg_sym.
Print Assumptions edge_touch_class.
Print Assumptions overlap_segment.
