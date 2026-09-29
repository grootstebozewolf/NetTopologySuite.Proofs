(* NetTopologySuite.Proofs.ConvexClip
   Sutherland–Hodgman clip of one closed half-plane. Regions are convex
   hulls (nonnegative weights); positive-area convex polygons agree with
   cyclic slack. No Jordan. Polygon-level lemmas: ConvexClipPoly.
   topic: relate
   claimId: tri-de9im-a
   witness: TrianglePairClip.ii_nonempty_iff
   secondary witness: ConvexClipComplete.clip_correct
   3-axiom host. No Admitted. AI-drafted (Cursor Grok 4.7), human-reviewed.
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra Lia List QArith Qreals.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex RingArea979.
Local Open Scope R_scope.
(* Half-plane test, exact edge intersection, Sutherland–Hodgman step.         *)
Definition point_eqb (p q : Point) : bool :=
  if Req_dec_T (px p) (px q)
  then if Req_dec_T (py p) (py q) then true else false
  else false.
Definition points_distinct (p q : Point) : Prop :=
  px p <> px q \/ py p <> py q.
Definition inside_closed (p q x : Point) : Prop := 0 <= cross p q x.
Definition inside_b (p q x : Point) : bool :=
  if Rle_dec 0 (cross p q x) then true else false.
Definition line_hit (a b p q : Point) : Point :=
  let fa := cross p q a in
  let fb := cross p q b in
  let d := fa - fb in
  mkPoint (px a + (fa / d) * (px b - px a))
          (py a + (fa / d) * (py b - py a)).
Definition emit_edge (prev cur p q : Point) : list Point :=
  let ip := inside_b p q prev in
  let ic := inside_b p q cur in
  if ip then (if ic then [cur] else [line_hit prev cur p q])
  else if ic then [line_hit prev cur p q; cur] else [].
Fixpoint clip_chain (prev : Point) (rest : list Point) (p q : Point)
  : list Point :=
  match rest with
  | [] => []
  | cur :: rest' => emit_edge prev cur p q ++ clip_chain cur rest' p q
  end.
Definition seg_clip (a b p q : Point) : list Point :=
  let ia := inside_b p q a in
  let ib := inside_b p q b in
  if ia then (if ib then [a; b] else [a; line_hit a b p q])
  else if ib then [line_hit a b p q; b] else [].
Definition clip_halfplane (poly : list Point) (p q : Point) : list Point :=
  if point_eqb p q then poly else
  match poly with
  | [] => []
  | [a] => if inside_b p q a then [a] else []
  | [a; b] => seg_clip a b p q
  | a :: _ => clip_chain a (tl (poly ++ [a])) p q
  end.
(* Convex hull by nonnegative weights. Consecutive duplicate vertices are     *)
(* harmless: a zero-length edge has cross 0 and does not change the hull.    *)
Fixpoint rsum (w : list R) : R :=
  match w with [] => 0 | a :: t => a + rsum t end.
Fixpoint wpt (w : list R) (ps : list Point) : Point :=
  match w, ps with
  | a :: wt, r :: rt =>
      let acc := wpt wt rt in
      mkPoint (a * px r + px acc) (a * py r + py acc)
  | _, _ => mkPoint 0 0
  end.
Definition nonneg_w (w : list R) : Prop := forall a, In a w -> 0 <= a.
Definition in_hull (ps : list Point) (x : Point) : Prop :=
  exists w, length w = length ps /\ nonneg_w w /\ rsum w = 1 /\ wpt w ps = x.
Definition bary3 (a b c : R) (A B C : Point) : Point :=
  mkPoint (a * px A + b * px B + c * px C)
          (a * py A + b * py B + c * py C).
Definition in_tri (A B C x : Point) : Prop :=
  exists a b c, 0 <= a /\ 0 <= b /\ 0 <= c /\ a + b + c = 1 /\
    x = bary3 a b c A B C.
(* Orientation and hit algebra.                                               *)
Lemma point_eqb_true : forall p q, point_eqb p q = true -> p = q.
Proof.
  intros p q H. unfold point_eqb in H.
  destruct (Req_dec_T (px p) (px q)); [| discriminate].
  destruct (Req_dec_T (py p) (py q)); [| discriminate].
  destruct p, q. simpl in *. subst. reflexivity.
Qed.
Lemma point_eqb_false_distinct : forall p q,
  point_eqb p q = false -> points_distinct p q.
Proof.
  intros p q H. unfold point_eqb in H. unfold points_distinct.
  destruct (Req_dec_T (px p) (px q)) as [Hx|Hx].
  - destruct (Req_dec_T (py p) (py q)) as [Hy|Hy].
    + destruct p, q. simpl in *. subst. discriminate.
    + right. exact Hy.
  - left. exact Hx.
Qed.
Lemma point_eqb_refl : forall p, point_eqb p p = true.
Proof.
  intros p. unfold point_eqb.
  destruct (Req_dec_T (px p) (px p)); [| contradiction].
  destruct (Req_dec_T (py p) (py p)); [| contradiction].
  reflexivity.
Qed.
Lemma cross_cycle : forall A B C, cross A B C = cross B C A.
Proof. intros. unfold cross. ring. Qed.
Lemma cross_cycle2 : forall A B C, cross A B C = cross C A B.
Proof. intros. unfold cross. ring. Qed.
Lemma cross_swap : forall A B C, cross A B C = - cross A C B.
Proof. intros. apply cross_antisymmetric. Qed.
Lemma cross_bary3 : forall p q A B C a b c,
  a + b + c = 1 ->
  cross p q (bary3 a b c A B C) =
    a * cross p q A + b * cross p q B + c * cross p q C.
Proof.
  intros p q A B C a b c Hab.
  destruct p, q, A, B, C. unfold cross, bary3. simpl.
  replace a with (1 - b - c) by lra. ring.
Qed.
Lemma cross_sum3 : forall A B C x,
  cross A B x + cross B C x + cross C A x = cross A B C.
Proof. intros. unfold cross. ring. Qed.
Lemma cross_combo : forall p q a b t,
  cross p q (convex_combination a b t) =
    (1 - t) * cross p q a + t * cross p q b.
Proof.
  intros. unfold cross, convex_combination. destruct p, q, a, b. simpl. ring.
Qed.
Lemma line_hit_combo : forall a b p q,
  line_hit a b p q =
    convex_combination a b (cross p q a / (cross p q a - cross p q b)).
Proof.
  intros. unfold line_hit, convex_combination. destruct a, b. simpl. f_equal; ring.
Qed.
Lemma line_hit_on_line : forall a b p q,
  cross p q a - cross p q b <> 0 ->
  cross p q (line_hit a b p q) = 0.
Proof.
  intros. rewrite line_hit_combo. rewrite cross_combo.
  field. exact H.
Qed.
Lemma inside_b_true : forall p q x,
  inside_b p q x = true -> inside_closed p q x.
Proof.
  intros p q x H. unfold inside_b, inside_closed in *.
  destruct (Rle_dec 0 (cross p q x)); [exact r | discriminate].
Qed.
Lemma inside_b_false : forall p q x,
  inside_b p q x = false -> cross p q x < 0.
Proof.
  intros p q x H. unfold inside_b in H.
  destruct (Rle_dec 0 (cross p q x)); [discriminate |].
  apply Rnot_le_lt. exact n.
Qed.
Lemma in_tri_hull3 : forall A B C x,
  in_tri A B C x <-> in_hull [A; B; C] x.
Proof.
  intros A B C x. split.
  - intros [a [b [c [Ha [Hb [Hc [Hs Hx]]]]]]].
    exists [a; b; c]. unfold nonneg_w. simpl. repeat split; try lra.
    + intros z Hin. simpl in Hin. intuition subst; assumption.
    + rewrite Hx. unfold bary3, wpt. destruct A, B, C. simpl. f_equal; ring.
  - intros [w [Hlen [Hnn [Hs Hw]]]].
    destruct w as [|a [|b [|c [|]]]]; simpl in Hlen; try discriminate.
    exists a, b, c. simpl in Hs, Hw.
    assert (Ha : 0 <= a) by (apply Hnn; simpl; tauto).
    assert (Hb : 0 <= b) by (apply Hnn; simpl; tauto).
    assert (Hc : 0 <= c) by (apply Hnn; simpl; tauto).
    repeat split; try assumption; try lra.
    rewrite <- Hw. unfold bary3, wpt. destruct A, B, C. simpl. f_equal; ring.
Qed.
Lemma tri_bary_recon : forall A B C x,
  cross A B C <> 0 ->
  let d := cross A B C in
  let a := cross B C x / d in
  let b := cross C A x / d in
  let c := cross A B x / d in
  a + b + c = 1 /\ x = bary3 a b c A B C.
Proof.
  intros A B C x Hd d a b c.
  assert (Hsum : cross B C x + cross C A x + cross A B x = d).
  { unfold d, cross. ring. }
  split.
  - unfold a, b, c.
    replace (cross B C x / d + cross C A x / d + cross A B x / d)
      with ((cross B C x + cross C A x + cross A B x) / d)
      by (field; exact Hd).
    rewrite Hsum. field. exact Hd.
  - destruct x as [x y], A as [ax ay], B as [bx by_], C as [cx cy].
    unfold bary3, a, b, c, d, cross in *. simpl in *.
    f_equal; field; exact Hd.
Qed.
Lemma tri_slack_hull : forall A B C x,
  0 < cross A B C ->
  (0 <= cross A B x /\ 0 <= cross B C x /\ 0 <= cross C A x) <->
  in_tri A B C x.
Proof.
  intros A B C x Hd. split.
  - intros [Hab [Hbc Hca]].
    destruct (tri_bary_recon A B C x) as [Hs Hx].
    { lra. }
    set (d := cross A B C) in *.
    set (a := cross B C x / d) in *.
    set (b := cross C A x / d) in *.
    set (c := cross A B x / d) in *.
    exists a, b, c. repeat split; try lra; try exact Hs; try exact Hx.
    + unfold a, d. apply Rmult_le_pos; [exact Hbc |].
      apply Rlt_le, Rinv_0_lt_compat. exact Hd.
    + unfold b, d. apply Rmult_le_pos; [exact Hca |].
      apply Rlt_le, Rinv_0_lt_compat. exact Hd.
    + unfold c, d. apply Rmult_le_pos; [exact Hab |].
      apply Rlt_le, Rinv_0_lt_compat. exact Hd.
  - intros [a [b [c [Ha [Hb [Hc [Hs Hx]]]]]]].
    assert (HAB0 : cross A B A = 0) by apply cross_at_P0_is_collinear.
    assert (HBB0 : cross A B B = 0) by (unfold cross; ring).
    assert (HBC0 : cross B C B = 0) by apply cross_at_P0_is_collinear.
    assert (HCC0 : cross B C C = 0) by (unfold cross; ring).
    assert (HCA0 : cross C A C = 0) by apply cross_at_P0_is_collinear.
    assert (HAA0 : cross C A A = 0) by (unfold cross; ring).
    rewrite Hx. rewrite !cross_bary3 by exact Hs.
    assert (Ebc : cross B C A = cross A B C)
      by (symmetry; apply cross_cycle).
    assert (Eca : cross C A B = cross A B C)
      by (symmetry; apply cross_cycle2).
    split; [| split].
    + rewrite HAB0, HBB0.
      repeat apply Rplus_le_le_0_compat;
        apply Rmult_le_pos; try lra; apply Rlt_le; exact Hd.
    + rewrite HBC0, HCC0, Ebc.
      repeat apply Rplus_le_le_0_compat;
        apply Rmult_le_pos; try lra; apply Rlt_le; exact Hd.
    + rewrite HCA0, HAA0, Eca.
      repeat apply Rplus_le_le_0_compat;
        apply Rmult_le_pos; try lra; apply Rlt_le; exact Hd.
Qed.
(* Weight-list algebra.                                                       *)
Fixpoint rscale (t : R) (w : list R) : list R :=
  match w with [] => [] | a :: q => (t * a) :: rscale t q end.
Fixpoint radd (u v : list R) : list R :=
  match u, v with
  | a :: us, b :: vs => (a + b) :: radd us vs
  | _, _ => []
  end.
Lemma rsum_scale : forall t w, rsum (rscale t w) = t * rsum w.
Proof.
  intros t w. induction w; simpl; [ring | rewrite IHw; ring].
Qed.
Lemma rsum_add : forall u v, length u = length v ->
  rsum (radd u v) = rsum u + rsum v.
Proof.
  intros u v. revert v. induction u; intros v Hl; destruct v; simpl in *;
    try discriminate; [ring | rewrite IHu by lia; ring].
Qed.
Lemma rscale_nonneg : forall t w,
  0 <= t -> nonneg_w w -> nonneg_w (rscale t w).
Proof.
  intros t w Ht Hw a Ha. induction w; simpl in Ha; try contradiction.
  destruct Ha as [E|Hin].
  - subst. apply Rmult_le_pos; [exact Ht | apply Hw; simpl; tauto].
  - apply IHw; [| exact Hin]. intros z Hz. apply Hw. simpl. tauto.
Qed.
Lemma radd_nonneg : forall u v,
  nonneg_w u -> nonneg_w v -> length u = length v -> nonneg_w (radd u v).
Proof.
  intros u v Hu Hv. revert v Hv. induction u; intros v Hv Hl;
    destruct v; simpl in *; try discriminate.
  - intros z Hz. contradiction.
  - intros z Hz. destruct Hz as [E|Hin].
    + subst. apply Rplus_le_le_0_compat;
        [apply Hu; simpl; tauto | apply Hv; simpl; tauto].
    + apply IHu with (v := v); try (simpl; lia).
      * intros w Hw2. apply Hu. simpl. tauto.
      * intros w Hw2. apply Hv. simpl. tauto.
      * exact Hin.
Qed.
Lemma wpt_scale : forall t w ps,
  length w = length ps ->
  wpt (rscale t w) ps =
    mkPoint (t * px (wpt w ps)) (t * py (wpt w ps)).
Proof.
  intros t w ps. revert w. induction ps; intros w Hl; destruct w;
    simpl in *; try discriminate.
  - f_equal; ring.
  - rewrite (IHps w) by lia.
    destruct a. simpl. f_equal; ring.
Qed.
Lemma wpt_add : forall u v ps,
  length u = length ps -> length v = length ps ->
  wpt (radd u v) ps =
    mkPoint (px (wpt u ps) + px (wpt v ps))
            (py (wpt u ps) + py (wpt v ps)).
Proof.
  intros u v ps. revert u v. induction ps; intros u v Hu Hv;
    destruct u, v; simpl in *; try discriminate.
  - f_equal; ring.
  - rewrite (IHps u v) by lia. destruct a. simpl. f_equal; ring.
Qed.
Lemma rscale_length : forall t w, length (rscale t w) = length w.
Proof. intros t w. induction w; simpl; congruence. Qed.
Lemma radd_length : forall u v,
  length u = length v -> length (radd u v) = length u.
Proof.
  intros u v. revert v. induction u; intros v H; destruct v; simpl in *;
    try discriminate; [reflexivity | f_equal; apply IHu; lia].
Qed.
Lemma in_hull_conv : forall ps a b t,
  in_hull ps a -> in_hull ps b -> 0 <= t <= 1 ->
  in_hull ps (convex_combination a b t).
Proof.
  intros ps a b t [wa [Ha1 [Ha2 [Ha3 Ha4]]]] [wb [Hb1 [Hb2 [Hb3 Hb4]]]] Ht.
  exists (radd (rscale (1 - t) wa) (rscale t wb)).
  assert (Hlen : length (rscale (1 - t) wa) = length ps)
    by (rewrite rscale_length; exact Ha1).
  assert (Hlenb : length (rscale t wb) = length ps)
    by (rewrite rscale_length; exact Hb1).
  repeat split.
  - rewrite radd_length by congruence. exact Hlen.
  - apply radd_nonneg.
    + apply rscale_nonneg; [lra | exact Ha2].
    + apply rscale_nonneg; [lra | exact Hb2].
    + congruence.
  - rewrite rsum_add by congruence.
    rewrite !rsum_scale, Ha3, Hb3. lra.
  - rewrite wpt_add by (rewrite ?rsum_scale; congruence).
    rewrite !wpt_scale by congruence.
    rewrite Ha4, Hb4. unfold convex_combination. destruct a, b. simpl.
    f_equal; ring.
Qed.
Lemma zero_weights : forall ps,
  exists w, length w = length ps /\ nonneg_w w /\ rsum w = 0 /\
    wpt w ps = mkPoint 0 0.
Proof.
  induction ps as [|p ps IH].
  - exists []. split.
    + exact eq_refl.
    + split.
      * intros z Hz. contradiction.
      * split; exact eq_refl.
  - destruct IH as [w [Hl [Hn [Hs Hp]]]].
    exists (0 :: w). repeat split.
    + simpl. f_equal. exact Hl.
    + intros z Hz. simpl in Hz. destruct Hz as [<-|Hin]; [lra | apply Hn; exact Hin].
    + simpl. rewrite Hs. ring.
    + simpl. rewrite Hp. destruct p. simpl. f_equal; ring.
Qed.
Lemma in_hull_in : forall v ps, In v ps -> in_hull ps v.
Proof.
  intros v ps Hin. induction ps as [|a ps IH]; simpl in Hin; try contradiction.
  destruct Hin as [->|Hin].
  - destruct (zero_weights ps) as [w [Hl [Hn [Hs Hp]]]].
    exists (1 :: w). repeat split.
    + simpl. f_equal. exact Hl.
    + intros z Hz. simpl in Hz. destruct Hz as [<-|Hinz]; [lra | apply Hn; exact Hinz].
    + simpl. rewrite Hs. ring.
    + simpl. rewrite Hp. destruct v. simpl. f_equal; ring.
  - destruct (IH Hin) as [w [Hl [Hn [Hs Hp]]]].
    exists (0 :: w). repeat split.
    + simpl. f_equal. exact Hl.
    + intros z Hz. simpl in Hz. destruct Hz as [<-|Hinz]; [lra | apply Hn; exact Hinz].
    + simpl. rewrite Hs. ring.
    + simpl. rewrite Hp. destruct v. simpl. f_equal; ring.
Qed.
Lemma wpt2 : forall u v a b,
  wpt [u; v] [a; b] =
    mkPoint (u * px a + v * px b) (u * py a + v * py b).
Proof.
  intros. simpl. destruct a, b. simpl. f_equal; ring.
Qed.
Lemma in_hull_embed2 : forall a b ps x,
  In a ps -> In b ps -> in_hull [a; b] x -> in_hull ps x.
Proof.
  intros a b ps x Ha Hb [w [Hl [Hn [Hs Hp]]]].
  destruct w as [|u [|v [|]]]; simpl in Hl; try discriminate.
  assert (Hu : 0 <= u) by (apply Hn; simpl; tauto).
  assert (Hv : 0 <= v) by (apply Hn; simpl; tauto).
  assert (Eu : u = 1 - v) by (simpl in Hs; lra).
  assert (Hx : x = convex_combination a b v).
  { rewrite wpt2 in Hp. rewrite Eu in Hp. unfold convex_combination.
    symmetry. exact Hp. }
  rewrite Hx. apply in_hull_conv.
  - apply in_hull_in. exact Ha.
  - apply in_hull_in. exact Hb.
  - split; [exact Hv |].
    simpl in Hs. lra.
Qed.
(* Edge hits land on the segment when the endpoints have opposite signs.      *)
Lemma hit_param_01 : forall fa fb,
  (0 <= fa /\ fb < 0) \/ (fa < 0 /\ 0 <= fb) ->
  fa - fb <> 0 /\ 0 <= fa / (fa - fb) /\ fa / (fa - fb) <= 1.
Proof.
  intros fa fb [[Hfa Hfb] | [Hfa Hfb]].
  - assert (Hd : 0 < fa - fb) by lra.
    split; [lra |]. split.
    + apply Rmult_le_pos; [exact Hfa |].
      apply Rlt_le, Rinv_0_lt_compat. exact Hd.
    + apply Rmult_le_reg_r with (r := fa - fb); [exact Hd |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; lra.
  - assert (Hd : 0 < - (fa - fb)) by lra.
    assert (Heq : fa / (fa - fb) = (- fa) / (- (fa - fb))) by (field; lra).
    split; [lra |]. rewrite Heq. split.
    + apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; exact Hd].
    + apply Rmult_le_reg_r with (r := - (fa - fb)); [exact Hd |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; lra.
Qed.
Lemma line_hit_on_seg : forall a b p q,
  (inside_closed p q a /\ cross p q b < 0) \/
  (cross p q a < 0 /\ inside_closed p q b) ->
  exists t, 0 <= t <= 1 /\
    line_hit a b p q = convex_combination a b t /\
    cross p q (line_hit a b p q) = 0.
Proof.
  intros a b p q Hsign.
  pose (t := cross p q a / (cross p q a - cross p q b)).
  destruct (hit_param_01 (cross p q a) (cross p q b)) as [Hd [Ht0 Ht1]].
  { destruct Hsign as [[Ha Hb] | [Ha Hb]]; unfold inside_closed in *; tauto. }
  exists t. split; [split; assumption |]. split.
  - rewrite line_hit_combo. unfold t. reflexivity.
  - apply line_hit_on_line. exact Hd.
Qed.
Lemma emit_in_edge : forall a b p q v,
  In v (emit_edge a b p q) ->
  in_hull [a; b] v /\ inside_closed p q v.
Proof.
  intros a b p q v Hin.
  unfold emit_edge in Hin.
  destruct (inside_b p q a) eqn:Ha; destruct (inside_b p q b) eqn:Hb;
    simpl in Hin.
  - destruct Hin as [E|[]]; subst.
    split.
    + apply in_hull_in. simpl. tauto.
    + apply inside_b_true. exact Hb.
  - destruct Hin as [E|[]]; subst.
    destruct (line_hit_on_seg a b p q) as [t [Ht [Heq Hz]]].
    { left. split; [apply inside_b_true; exact Ha | apply inside_b_false; exact Hb]. }
    split.
    + rewrite Heq. apply in_hull_conv; try exact Ht.
      * apply in_hull_in. simpl. tauto.
      * apply in_hull_in. simpl. tauto.
    + unfold inside_closed. lra.
  - destruct Hin as [E|[E|[]]]; subst.
    + destruct (line_hit_on_seg a b p q) as [t [Ht [Heq Hz]]].
      { right. split; [apply inside_b_false; exact Ha | apply inside_b_true; exact Hb]. }
      split.
      * rewrite Heq. apply in_hull_conv; try exact Ht.
        -- apply in_hull_in. simpl. tauto.
        -- apply in_hull_in. simpl. tauto.
      * unfold inside_closed. lra.
    + split; [apply in_hull_in; simpl; tauto | apply inside_b_true; exact Hb].
  - contradiction.
Qed.
Lemma clip_tri_list : forall A B C p q,
  point_eqb p q = false ->
  clip_halfplane [A; B; C] p q =
    emit_edge A B p q ++ emit_edge B C p q ++ emit_edge C A p q.
Proof.
  intros A B C p q Hpq.
  unfold clip_halfplane. rewrite Hpq. simpl. rewrite !app_nil_r. reflexivity.
Qed.
(* A convex combination of points already in a hull stays in that hull.       *)
(* The same decomposition shows a closed half-plane is preserved.             *)
Lemma rsum_nonneg : forall w, nonneg_w w -> 0 <= rsum w.
Proof.
  intros w Hw. induction w; simpl; [lra |].
  apply Rplus_le_le_0_compat; [apply Hw; simpl; tauto | apply IHw].
  intros z Hz. apply Hw. simpl. tauto.
Qed.
Lemma nonneg_sum0 : forall w, nonneg_w w -> rsum w = 0 ->
  forall a, In a w -> a = 0.
Proof.
  intros w Hw Hs a Ha. induction w; simpl in Ha; try contradiction.
  assert (H0 : 0 <= a0) by (apply Hw; simpl; tauto).
  assert (Ht : 0 <= rsum w).
  { apply rsum_nonneg. intros z Hz. apply Hw. simpl. tauto. }
  simpl in Hs. destruct Ha as [->|Hin].
  - lra.
  - apply IHw; try lra.
    + intros z Hz. apply Hw. simpl. tauto.
    + exact Hin.
Qed.
Lemma wpt_zeros : forall w ps,
  length w = length ps -> (forall a, In a w -> a = 0) ->
  wpt w ps = mkPoint 0 0.
Proof.
  intros w ps. revert w. induction ps; intros w Hl Hz; destruct w;
    simpl in *; try discriminate.
  - reflexivity.
  - rewrite IHps by (try lia; intros z Hin; apply Hz; simpl; tauto).
    assert (E : r = 0) by (apply Hz; simpl; tauto).
    rewrite E. destruct a. simpl. f_equal; ring.
Qed.
Lemma inside_conv : forall p q a b t,
  0 <= t <= 1 -> inside_closed p q a -> inside_closed p q b ->
  inside_closed p q (convex_combination a b t).
Proof.
  intros p q a b t Ht Ha Hb. unfold inside_closed in *.
  rewrite cross_combo. destruct Ht as [Ht0 Ht1].
  apply Rplus_le_le_0_compat; apply Rmult_le_pos; lra.
Qed.
Lemma members_in_hull : forall K ps x,
  (forall v, In v K -> in_hull ps v) ->
  in_hull K x -> in_hull ps x.
Proof.
  intros K. induction K as [|v K IH]; intros ps x HK [w [Hl [Hn [Hs Hp]]]].
  - destruct w; simpl in Hs, Hl; try discriminate.
    exfalso. exact (R1_neq_R0 (eq_sym Hs)).
  - destruct w as [|a wt]; simpl in Hl; try discriminate.
    assert (Ha : 0 <= a) by (apply Hn; simpl; tauto).
    assert (Hwt : nonneg_w wt).
    { intros z Hz. apply Hn. simpl. tauto. }
    assert (Hs' : a + rsum wt = 1) by (simpl in Hs; exact Hs).
    assert (Hsn : 0 <= rsum wt) by (apply rsum_nonneg; exact Hwt).
    destruct (Rle_lt_dec (rsum wt) 0) as [Hz|Hpos].
    + assert (Hzero : rsum wt = 0) by lra.
      assert (Ea : a = 1) by lra.
      assert (Hp0 : wpt wt K = mkPoint 0 0).
      { apply wpt_zeros; [lia |]. intros z Hin.
        apply nonneg_sum0 with (w := wt); auto. }
      assert (Ex : x = v).
      { rewrite <- Hp. simpl. rewrite Hp0, Ea. destruct v. simpl. f_equal; ring. }
      rewrite Ex. apply HK. simpl. tauto.
    + set (y := wpt (rscale (/ rsum wt) wt) K).
      assert (Hy : in_hull K y).
      { exists (rscale (/ rsum wt) wt). split.
        { rewrite rscale_length. lia. }
        split.
        { apply rscale_nonneg; [apply Rlt_le, Rinv_0_lt_compat; exact Hpos | exact Hwt]. }
        split.
        { rewrite rsum_scale. field. lra. }
        reflexivity. }
      assert (Hx : x = convex_combination v y (rsum wt)).
      { rewrite <- Hp. unfold y, convex_combination.
        rewrite wpt_scale by lia. simpl.
        replace a with (1 - rsum wt) by lra.
        destruct v. simpl. f_equal; field; lra. }
      rewrite Hx. apply in_hull_conv.
      * apply HK. simpl. tauto.
      * apply IH; [| exact Hy]. intros z Hin. apply HK. simpl. tauto.
      * split; [exact Hsn | lra].
Qed.
Lemma members_inside : forall p q K x,
  (forall v, In v K -> inside_closed p q v) ->
  in_hull K x -> inside_closed p q x.
Proof.
  intros p q K. induction K as [|v K IH]; intros x HK [w [Hl [Hn [Hs Hp]]]].
  - destruct w; simpl in Hs, Hl; try discriminate.
    exfalso. exact (R1_neq_R0 (eq_sym Hs)).
  - destruct w as [|a wt]; simpl in Hl; try discriminate.
    assert (Ha : 0 <= a) by (apply Hn; simpl; tauto).
    assert (Hwt : nonneg_w wt).
    { intros z Hz. apply Hn. simpl. tauto. }
    assert (Hs' : a + rsum wt = 1) by (simpl in Hs; exact Hs).
    assert (Hsn : 0 <= rsum wt) by (apply rsum_nonneg; exact Hwt).
    destruct (Rle_lt_dec (rsum wt) 0) as [Hz|Hpos].
    + assert (Hp0 : wpt wt K = mkPoint 0 0).
      { apply wpt_zeros; [lia |]. intros z Hin.
        apply nonneg_sum0 with (w := wt); try lra; auto. }
      assert (Ex : x = v).
      { rewrite <- Hp. simpl. rewrite Hp0. assert (Ea : a = 1) by lra.
        rewrite Ea. destruct v. simpl. f_equal; ring. }
      rewrite Ex. apply HK. simpl. tauto.
    + set (y := wpt (rscale (/ rsum wt) wt) K).
      assert (Hy : in_hull K y).
      { exists (rscale (/ rsum wt) wt). split.
        { rewrite rscale_length. lia. }
        split.
        { apply rscale_nonneg; [apply Rlt_le, Rinv_0_lt_compat; exact Hpos | exact Hwt]. }
        split.
        { rewrite rsum_scale. field. lra. }
        reflexivity. }
      assert (Hx : x = convex_combination v y (rsum wt)).
      { rewrite <- Hp. unfold y, convex_combination. rewrite wpt_scale by lia.
        simpl. replace a with (1 - rsum wt) by lra.
        destruct v. simpl. f_equal; field; lra. }
      rewrite Hx. apply inside_conv; [split; lra | apply HK; simpl; tauto |].
      apply IH; [| exact Hy]. intros z Hin. apply HK. simpl. tauto.
Qed.
Lemma clip_tri_sound : forall A B C p q x,
  point_eqb p q = false ->
  in_hull (clip_halfplane [A; B; C] p q) x ->
  in_hull [A; B; C] x /\ inside_closed p q x.
Proof.
  intros A B C p q x Hpq Hx.
  rewrite clip_tri_list in Hx by exact Hpq.
  assert (Hmem : forall v, In v (emit_edge A B p q ++ emit_edge B C p q ++
                                 emit_edge C A p q) ->
                    in_hull [A; B; C] v /\ inside_closed p q v).
  { intros v Hv. apply in_app_or in Hv. destruct Hv as [Hv|Hv].
    - destruct (emit_in_edge A B p q v Hv) as [Hh Hi].
      split; [| exact Hi]. apply in_hull_embed2 with (a := A) (b := B); simpl; tauto.
    - apply in_app_or in Hv. destruct Hv as [Hv|Hv].
      + destruct (emit_in_edge B C p q v Hv) as [Hh Hi].
        split; [| exact Hi]. apply in_hull_embed2 with (a := B) (b := C); simpl; tauto.
      + destruct (emit_in_edge C A p q v Hv) as [Hh Hi].
        split; [| exact Hi]. apply in_hull_embed2 with (a := C) (b := A); simpl; tauto. }
  split.
  - apply members_in_hull with
      (K := emit_edge A B p q ++ emit_edge B C p q ++ emit_edge C A p q);
      [| exact Hx].
    intros v Hv. apply Hmem. exact Hv.
  - apply members_inside with
      (K := emit_edge A B p q ++ emit_edge B C p q ++ emit_edge C A p q);
      [| exact Hx].
    intros v Hv. apply Hmem. exact Hv.
Qed.
Lemma line_hit_sym : forall a b p q,
  cross p q a - cross p q b <> 0 ->
  line_hit a b p q = line_hit b a p q.
Proof.
  intros a b p q Hd. unfold line_hit. destruct a, b. simpl. f_equal; field; lra.
Qed.
Lemma weighted_neg : forall a b c fa fb fc,
  0 <= a -> 0 <= b -> 0 <= c -> a + b + c = 1 ->
  fa < 0 -> fb < 0 -> fc < 0 ->
  a * fa + b * fb + c * fc < 0.
Proof.
  intros a b c fa fb fc Ha Hb Hc Hs Hfa Hfb Hfc.
  destruct (Rlt_dec 0 a) as [Qa|Qa].
  - assert (Hpa : a * fa < 0).
    { replace 0 with (a * 0) by ring. apply Rmult_lt_compat_l; lra. }
    assert (Hpb : b * fb <= 0).
    { replace 0 with (b * 0) by ring. apply Rmult_le_compat_l; lra. }
    assert (Hpc : c * fc <= 0).
    { replace 0 with (c * 0) by ring. apply Rmult_le_compat_l; lra. }
    assert (Hlt : a * fa + b * fb + c * fc < 0 + 0 + 0).
    { apply Rplus_lt_le_compat; [apply Rplus_lt_le_compat; [exact Hpa | exact Hpb] | exact Hpc]. }
    replace 0 with (0 + 0 + 0) by ring. exact Hlt.
  - assert (Ea : a = 0) by lra. rewrite Ea in Hs. simpl in Hs.
    destruct (Rlt_dec 0 b) as [Qb|Qb].
    + assert (Hpb : b * fb < 0).
      { replace 0 with (b * 0) by ring. apply Rmult_lt_compat_l; lra. }
      assert (Hpc : c * fc <= 0).
      { replace 0 with (c * 0) by ring. apply Rmult_le_compat_l; lra. }
      assert (Hlt : a * fa + b * fb + c * fc < 0 + 0).
      { apply Rplus_lt_le_compat; [| exact Hpc]. rewrite Ea. ring_simplify. exact Hpb. }
      replace 0 with (0 + 0) by ring. exact Hlt.
    + assert (Eb : b = 0) by lra. rewrite Eb in Hs.
      assert (Ec : c = 1) by lra. rewrite Ea, Eb, Ec. ring_simplify. exact Hfc.
Qed.
Lemma hit_blend : forall A B C p q bp cp fa fb fc,
  fa = cross p q A -> fb = cross p q B -> fc = cross p q C ->
  0 <= bp -> 0 <= cp -> bp + cp = 1 ->
  let xout := bary3 0 bp cp A B C in
  let fout := bp * fb + cp * fc in
  fa - fb <> 0 -> fa - fc <> 0 -> fa - fout <> 0 ->
  let u := bp * (fa - fb) / (fa - fout) in
  let v := cp * (fa - fc) / (fa - fout) in
  cross p q xout = fout /\
  u + v = 1 /\
  line_hit A xout p q = bary3 u v 0 (line_hit A B p q) (line_hit A C p q) A.
Proof.
  intros A B C p q bp cp fa fb fc Hfa Hfb Hfc Hbp Hcp Hsum xout fout
    Hdb Hdc Hd u v.
  assert (Hf : cross p q xout = fout).
  { unfold xout, fout. rewrite cross_bary3 by lra.
    rewrite <- Hfa, <- Hfb, <- Hfc. ring. }
  assert (Huv : u + v = 1).
  { unfold u, v, fout. replace bp with (1 - cp) by lra. field.
    unfold fout in Hd. replace bp with (1 - cp) in Hd by lra. exact Hd. }
  split; [exact Hf |]. split; [exact Huv |].
  set (sAB := fa / (fa - fb)).
  set (sAC := fa / (fa - fc)).
  set (lam := fa / (fa - fout)).
  assert (HAB : line_hit A B p q = convex_combination A B sAB).
  { rewrite line_hit_combo. unfold sAB. f_equal. rewrite <- Hfa, <- Hfb. reflexivity. }
  assert (HAC : line_hit A C p q = convex_combination A C sAC).
  { rewrite line_hit_combo. unfold sAC. f_equal. rewrite <- Hfa, <- Hfc. reflexivity. }
  assert (HM : line_hit A xout p q = convex_combination A xout lam).
  { rewrite line_hit_combo. unfold lam. f_equal. rewrite <- Hfa, Hf. reflexivity. }
  assert (Hu : u * sAB = bp * lam).
    { unfold u, sAB, lam, fout. field. split; [exact Hd | exact Hdb]. }
  assert (Hv : v * sAC = cp * lam).
  { unfold v, sAC, lam, fout. field. split; [exact Hd | exact Hdc]. }
  assert (Ha : u * (1 - sAB) + v * (1 - sAC) = 1 - lam).
    { unfold u, v, sAB, sAC, lam, fout. replace bp with (1 - cp) by lra.
      assert (Hden : fa - ((1 - cp) * fb + cp * fc) <> 0).
      { replace ((1 - cp) * fb + cp * fc) with fout; [exact Hd |].
        unfold fout. replace bp with (1 - cp) by lra. ring. }
      field. split; [| split]; [exact Hden | exact Hdc | exact Hdb]. }
  rewrite HM, HAB, HAC. unfold bary3, convex_combination, xout.
  destruct A as [ax ay], B as [bx by_], C as [cx cy]. simpl.
  f_equal.
  - transitivity ((u * (1 - sAB) + v * (1 - sAC)) * ax
                    + (u * sAB) * bx + (v * sAC) * cx).
    + rewrite Ha, Hu, Hv. ring.
    + ring.
  - transitivity ((u * (1 - sAB) + v * (1 - sAC)) * ay
                    + (u * sAB) * by_ + (v * sAC) * cy).
    + rewrite Ha, Hu, Hv. ring.
    + ring.
Qed.
Lemma in_clip_app_l : forall (v : Point) l m, In v l -> In v (l ++ m).
Proof. intros. apply in_or_app. left. assumption. Qed.
Lemma in_clip_app_r : forall (v : Point) l m, In v m -> In v (l ++ m).
Proof. intros. apply in_or_app. right. assumption. Qed.
Lemma clip_tri_emit_in : forall A B C p q v,
  point_eqb p q = false ->
  In v (emit_edge A B p q) \/ In v (emit_edge B C p q) \/ In v (emit_edge C A p q) ->
  In v (clip_halfplane [A; B; C] p q).
Proof.
  intros A B C p q v Hpq H.
  rewrite clip_tri_list by exact Hpq.
  destruct H as [H|[H|H]].
  - apply in_clip_app_l. exact H.
  - apply in_clip_app_r, in_clip_app_l. exact H.
  - apply in_clip_app_r, in_clip_app_r. exact H.
Qed.
Lemma emit_cur_in : forall a b p q,
  inside_b p q a = true -> inside_b p q b = true -> In b (emit_edge a b p q).
Proof.
  intros. unfold emit_edge. rewrite H, H0. simpl. tauto.
Qed.
Lemma emit_leave_hit : forall a b p q,
  inside_b p q a = true -> inside_b p q b = false ->
  In (line_hit a b p q) (emit_edge a b p q).
Proof.
  intros. unfold emit_edge. rewrite H, H0. simpl. tauto.
Qed.
Lemma emit_enter_hit : forall a b p q,
  inside_b p q a = false -> inside_b p q b = true ->
  In (line_hit a b p q) (emit_edge a b p q).
Proof.
  intros. unfold emit_edge. rewrite H, H0. simpl. left. reflexivity.
Qed.
Lemma emit_enter_cur : forall a b p q,
  inside_b p q a = false -> inside_b p q b = true -> In b (emit_edge a b p q).
Proof.
  intros. unfold emit_edge. rewrite H, H0. simpl. right. left. reflexivity.
Qed.
Lemma two_weight_neg : forall b c fb fc,
  0 <= b -> 0 <= c -> b + c = 1 -> fb < 0 -> fc < 0 ->
  b * fb + c * fc < 0.
Proof.
  intros b c fb fc Hb Hc Hs Hfb Hfc.
  assert (Hlt : 0 * (-1) + b * fb + c * fc < 0).
  { apply weighted_neg; lra. }
  replace (b * fb + c * fc) with (0 * (-1) + b * fb + c * fc) by ring.
  exact Hlt.
Qed.
Lemma frac_le_1 : forall s fa fout,
  0 < fa ->
  0 <= (1 - s) * fa + s * fout ->
  s * (fa - fout) / fa <= 1.
Proof.
  intros s fa fout Hfa Hnn.
  set (z := s * (fa - fout)).
  apply Rmult_le_reg_r with (r := fa); [exact Hfa |].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l by lra.
  assert (Hz : 0 <= fa - z).
  { unfold z. replace (fa - s * (fa - fout)) with ((1 - s) * fa + s * fout) by ring.
    exact Hnn. }
  apply Rplus_le_compat_r with (r := z) in Hz.
  replace z with (s * (fa - fout)) by reflexivity.
  ring_simplify in Hz. exact Hz.
Qed.
Lemma combo_nest : forall A X lam t,
  convex_combination A (convex_combination A X lam) t =
    convex_combination A X (t * lam).
Proof.
  intros. unfold convex_combination. destruct A, X. simpl. f_equal; ring.
Qed.
Lemma clip_tri_one_in : forall A B C p q x,
  point_eqb p q = false ->
  inside_b p q A = true -> inside_b p q B = false -> inside_b p q C = false ->
  in_hull [A; B; C] x -> inside_closed p q x ->
  in_hull (clip_halfplane [A; B; C] p q) x.
Proof.
  intros A B C p q x Hpq HA HB HC Hx Hin.
  apply in_tri_hull3 in Hx.
  destruct Hx as [a [b [c [Ha0 [Hb0 [Hc0 [Hs Hxeq]]]]]]].
  set (fa := cross p q A). set (fb := cross p q B). set (fc := cross p q C).
  assert (Hfa : 0 <= fa) by (apply inside_b_true in HA; exact HA).
  assert (Hfb : fb < 0) by (apply inside_b_false; exact HB).
  assert (Hfc : fc < 0) by (apply inside_b_false; exact HC).
  assert (Hfx : cross p q x = a * fa + b * fb + c * fc).
  { rewrite Hxeq. unfold fa, fb, fc. apply cross_bary3. exact Hs. }
  set (s := b + c).
  assert (Ea : a = 1 - s) by (unfold s; lra).
  destruct (Rle_lt_dec s 0) as [Hs0|Hspos].
  - assert (Eb : b = 0) by (unfold s in *; lra).
    assert (Ec : c = 0) by (unfold s in *; lra).
    assert (Es0 : s = 0) by (unfold s; lra).
    assert (Ex : x = A).
    { rewrite Hxeq, Eb, Ec, Ea, Es0. unfold bary3. destruct A. simpl.
      f_equal; ring. }
    rewrite Ex. apply in_hull_in.
    apply clip_tri_emit_in; [exact Hpq |]. right. right.
    apply emit_enter_cur; auto.
  - set (bp := b / s). set (cp := c / s). set (fout := bp * fb + cp * fc).
    assert (Hbp : 0 <= bp).
    { unfold bp. apply Rmult_le_pos; [exact Hb0 |].
      apply Rlt_le, Rinv_0_lt_compat. exact Hspos. }
    assert (Hcp : 0 <= cp).
    { unfold cp. apply Rmult_le_pos; [exact Hc0 |].
      apply Rlt_le, Rinv_0_lt_compat. exact Hspos. }
    assert (Hsp : bp + cp = 1).
    { unfold bp, cp. replace s with (b + c) by reflexivity. field. lra. }
    assert (Hfo : fout < 0).
    { unfold fout. apply two_weight_neg; assumption. }
    assert (Hsf : s * fout = b * fb + c * fc).
    { unfold fout, bp, cp. replace s with (b + c) by reflexivity. field. lra. }
    assert (Hfa1 : 0 < fa).
    { destruct (Rle_lt_dec fa 0) as [Hle|Hlt]; [| exact Hlt].
      assert (E0 : fa = 0) by lra.
      assert (Hbad : cross p q x < 0).
      { rewrite Hfx, E0, Ea.
        replace ((1 - s) * 0 + b * fb + c * fc) with (s * fout).
        - replace 0 with (s * 0) by ring. apply Rmult_lt_compat_l; lra.
        - rewrite Hsf. ring. }
      unfold inside_closed in Hin. lra. }
    assert (HposZ : 0 < fa - fout) by lra.
    assert (Hdb : fa - fb <> 0) by lra.
    assert (Hdc : fa - fc <> 0) by lra.
    assert (Hd0 : fa - fout <> 0) by lra.
    destruct (hit_blend A B C p q bp cp fa fb fc
                eq_refl eq_refl eq_refl Hbp Hcp Hsp Hdb Hdc Hd0)
      as [Hcross [Huv Hpt]].
    set (u := bp * (fa - fb) / (fa - fout)).
    set (v := cp * (fa - fc) / (fa - fout)).
    set (X := bary3 0 bp cp A B C).
    set (M := line_hit A X p q).
    set (hAB := line_hit A B p q).
    set (hAC := line_hit A C p q).
    assert (Hu : 0 <= u).
    { unfold u. apply Rmult_le_pos.
      - apply Rmult_le_pos; [exact Hbp | lra].
      - apply Rlt_le, Rinv_0_lt_compat. exact HposZ. }
    assert (Hv : 0 <= v).
    { unfold v. apply Rmult_le_pos.
      - apply Rmult_le_pos; [exact Hcp | lra].
      - apply Rlt_le, Rinv_0_lt_compat. exact HposZ. }
    assert (HM : in_hull [hAB; hAC] M).
    { exists [u; v]. split; [reflexivity |]. split.
      { intros z Hz. simpl in Hz. destruct Hz as [<-|[<-|[]]]; assumption. }
      split.
      { simpl. assert (Euv : u + v = 1) by exact Huv.
        replace (u + (v + 0)) with (u + v) by ring. exact Euv. }
      assert (Hpt' : M = bary3 u v 0 hAB hAC A).
      { unfold M, hAB, hAC, X. exact Hpt. }
      rewrite wpt2, Hpt'. unfold bary3. destruct hAB, hAC, A. simpl.
      f_equal; ring. }
    assert (HinM : In hAB (clip_halfplane [A; B; C] p q)
                /\ In hAC (clip_halfplane [A; B; C] p q)
                /\ In A (clip_halfplane [A; B; C] p q)).
    { split; [| split].
      - apply clip_tri_emit_in; [exact Hpq |]. left. apply emit_leave_hit; auto.
      - apply clip_tri_emit_in; [exact Hpq |]. right. right.
        unfold hAC. rewrite line_hit_sym by (unfold fa, fc in Hdc; exact Hdc).
        apply emit_enter_hit; auto.
      - apply clip_tri_emit_in; [exact Hpq |]. right. right.
        apply emit_enter_cur; auto. }
    assert (HMclip : in_hull (clip_halfplane [A; B; C] p q) M).
    { apply members_in_hull with (K := [hAB; hAC]); [ | exact HM].
      intros vtx Hvtx. simpl in Hvtx. destruct HinM as [Iab [Iac _]].
      destruct Hvtx as [E|[E|[]]].
      - rewrite <- E. apply in_hull_in. exact Iab.
      - rewrite <- E. apply in_hull_in. exact Iac. }
    set (lam := fa / (fa - fout)).
    set (t := s * (fa - fout) / fa).
    assert (Ht0 : 0 <= t).
    { unfold t. apply Rmult_le_pos; [apply Rmult_le_pos; lra |].
      apply Rlt_le, Rinv_0_lt_compat. exact Hfa1. }
    assert (Ht1 : t <= 1).
    { unfold t. apply frac_le_1. exact Hfa1.
      rewrite <- Ea, Hsf.
      assert (Efx : a * fa + (b * fb + c * fc) = cross p q x).
      { transitivity (a * fa + b * fb + c * fc); [ring |].
        symmetry. exact Hfx. }
      rewrite Efx. exact Hin. }
    assert (Htl : t * lam = s).
    { unfold t, lam. field. lra. }
    assert (HM2 : M = convex_combination A X lam).
    { unfold M, lam. rewrite line_hit_combo. f_equal.
      replace (cross p q A) with fa by reflexivity.
      replace (cross p q X) with fout by (unfold X, fout; symmetry; exact Hcross).
      field; try exact Hd0; lra. }
    assert (HX : x = convex_combination A X s).
    { rewrite Hxeq. unfold X, convex_combination, bary3. rewrite Ea.
      destruct A, B, C. simpl. f_equal; unfold bp, cp, s; field; lra. }
    assert (HxM : x = convex_combination A M t).
    { rewrite HM2, combo_nest, Htl. exact HX. }
    rewrite HxM. apply in_hull_conv; try (split; [exact Ht0 | exact Ht1]).
    + apply in_hull_in. tauto.
    + exact HMclip.
Qed.
Lemma hull_rot3 : forall a b c x,
  (forall v, In v (a ++ b ++ c) -> In v (b ++ c ++ a)) ->
  (forall v, In v (b ++ c ++ a) -> In v (a ++ b ++ c)) ->
  in_hull (a ++ b ++ c) x <-> in_hull (b ++ c ++ a) x.
Proof.
  intros a b c x Hab Hba. split; intros Hx.
  - apply members_in_hull with (K := a ++ b ++ c); [| exact Hx].
    intros v Hv. apply in_hull_in, Hab, Hv.
  - apply members_in_hull with (K := b ++ c ++ a); [| exact Hx].
    intros v Hv. apply in_hull_in, Hba, Hv.
Qed.
Lemma clip_tri_cycle_hull : forall A B C p q x,
  point_eqb p q = false ->
  (in_hull (clip_halfplane [A; B; C] p q) x <->
   in_hull (clip_halfplane [B; C; A] p q) x).
Proof.
  intros A B C p q x Hpq.
  rewrite !clip_tri_list by exact Hpq.
  apply hull_rot3; intros v Hv; apply in_app_or in Hv; destruct Hv as [Hv|Hv].
  - apply in_clip_app_r, in_clip_app_r. exact Hv.
  - apply in_app_or in Hv. destruct Hv as [Hv|Hv].
    + apply in_clip_app_l. exact Hv.
    + apply in_clip_app_r, in_clip_app_l. exact Hv.
  - apply in_clip_app_r, in_clip_app_l. exact Hv.
  - apply in_app_or in Hv. destruct Hv as [Hv|Hv].
    + apply in_clip_app_r, in_clip_app_r. exact Hv.
    + apply in_clip_app_l. exact Hv.
Qed.
Lemma clip_tri_two_in : forall A B C p q x,
  point_eqb p q = false ->
  inside_b p q A = true -> inside_b p q B = true -> inside_b p q C = false ->
  in_hull [A; B; C] x -> inside_closed p q x ->
  in_hull (clip_halfplane [A; B; C] p q) x.
Proof.
  intros A B C p q x Hpq HA HB HC Hx Hin.
  apply in_tri_hull3 in Hx.
  destruct Hx as [a [b [c [Ha0 [Hb0 [Hc0 [Hs Hxeq]]]]]]].
  set (fa := cross p q A). set (fb := cross p q B). set (fc := cross p q C).
  assert (Hfa : 0 <= fa) by (apply inside_b_true in HA; exact HA).
  assert (Hfb : 0 <= fb) by (apply inside_b_true in HB; exact HB).
  assert (Hfc : fc < 0) by (apply inside_b_false; exact HC).
  assert (Hfx : cross p q x = a * fa + b * fb + c * fc).
  { rewrite Hxeq. unfold fa, fb, fc. apply cross_bary3. exact Hs. }
  set (s := a + b).
  assert (Es : s = 1 - c) by (unfold s; lra).
  destruct (Rle_lt_dec c 0) as [Hc0'|Hpos].
  - assert (Ec : c = 0) by lra.
    assert (Eab : a + b = 1) by lra.
    assert (Hxab : x = convex_combination A B b).
    { rewrite Hxeq, Ec. unfold convex_combination, bary3. rewrite <- Eab.
      destruct A, B. simpl. f_equal; ring. }
    rewrite Hxab. apply in_hull_conv; [ | | split; [exact Hb0 | lra]].
    + apply in_hull_in. apply clip_tri_emit_in; [exact Hpq |].
      right. right. apply emit_enter_cur; auto.
    + apply in_hull_in. apply clip_tri_emit_in; [exact Hpq |].
      left. apply emit_cur_in; auto.
  - set (ap := a / s). set (bp := b / s). set (fin := ap * fa + bp * fb).
    assert (Hspos : 0 < s).
    { unfold s. destruct (Rle_lt_dec (a + b) 0) as [Hab|Hab]; [| exact Hab].
      assert (Ea0 : a = 0) by lra. assert (Eb0 : b = 0) by lra.
      assert (Ec1 : c = 1) by lra.
      assert (Hbad : cross p q x < 0).
      { rewrite Hfx, Ea0, Eb0, Ec1. ring_simplify. exact Hfc. }
      unfold inside_closed in Hin. exfalso. exact (Rle_not_lt _ _ Hin Hbad). }
    assert (Hap : 0 <= ap).
    { unfold ap. apply Rmult_le_pos; [exact Ha0 | apply Rlt_le, Rinv_0_lt_compat; exact Hspos]. }
    assert (Hbp : 0 <= bp).
    { unfold bp. apply Rmult_le_pos; [exact Hb0 | apply Rlt_le, Rinv_0_lt_compat; exact Hspos]. }
    assert (Hsum : ap + bp = 1).
    { unfold ap, bp. replace s with (a + b) by reflexivity. field. lra. }
    assert (Hsf : s * fin = a * fa + b * fb).
    { unfold fin, ap, bp. replace s with (a + b) by reflexivity. field. lra. }
    assert (Hfin_ge : 0 <= fin).
    { unfold fin. apply Rplus_le_le_0_compat; apply Rmult_le_pos; assumption. }
    assert (Hfin : 0 < fin).
    { destruct (Rle_lt_dec fin 0) as [Hle|Hlt]; [| exact Hlt].
      assert (E0 : fin = 0) by lra.
      assert (Hbad : cross p q x < 0).
      { rewrite Hfx.
        replace (a * fa + b * fb + c * fc) with (s * fin + c * fc).
        - rewrite E0. replace (s * 0 + c * fc) with (c * fc) by ring.
          replace 0 with (c * 0) by ring. apply Rmult_lt_compat_l; lra.
        - rewrite Hsf. ring. }
      unfold inside_closed in Hin. exfalso. exact (Rle_not_lt _ _ Hin Hbad). }
    assert (Hdb : fc - fa <> 0) by lra.
    assert (Hdc : fc - fb <> 0) by lra.
    assert (Hd0 : fc - fin <> 0) by lra.
    destruct (hit_blend C A B p q ap bp fc fa fb eq_refl eq_refl eq_refl
                Hap Hbp Hsum Hdb Hdc Hd0) as [Hcross [Huv Hpt]].
    set (Xin := bary3 0 ap bp C A B).
    set (M := line_hit C Xin p q).
    set (hCA := line_hit C A p q).
    set (hCB := line_hit C B p q).
    set (u := ap * (fc - fa) / (fc - fin)).
    set (v := bp * (fc - fb) / (fc - fin)).
    assert (Hu : 0 <= u).
    { unfold u.
      replace (ap * (fc - fa) / (fc - fin))
        with ((- (ap * (fc - fa))) / (- (fc - fin))) by (field; lra).
      apply Rmult_le_pos.
      - replace (- (ap * (fc - fa))) with (ap * (fa - fc)) by ring.
        apply Rmult_le_pos; lra.
      - apply Rlt_le, Rinv_0_lt_compat. lra. }
    assert (Hv : 0 <= v).
    { unfold v.
      replace (bp * (fc - fb) / (fc - fin))
        with ((- (bp * (fc - fb))) / (- (fc - fin))) by (field; lra).
      apply Rmult_le_pos.
      - replace (- (bp * (fc - fb))) with (bp * (fb - fc)) by ring.
        apply Rmult_le_pos; lra.
      - apply Rlt_le, Rinv_0_lt_compat. lra. }
    assert (HM : in_hull [hCA; hCB] M).
    { exists [u; v]. split; [reflexivity |]. split.
      { intros z Hz. simpl in Hz. destruct Hz as [<-|[<-|[]]]; assumption. }
      split.
      { simpl. assert (Euv : u + v = 1) by exact Huv.
        replace (u + (v + 0)) with (u + v) by ring. exact Euv. }
      assert (Hpt' : M = bary3 u v 0 hCA hCB C).
      { unfold M, hCA, hCB, Xin. exact Hpt. }
      rewrite wpt2, Hpt'. unfold bary3. destruct hCA, hCB, C. simpl.
      f_equal; ring. }
    assert (ICA : In hCA (clip_halfplane [A; B; C] p q)).
    { apply clip_tri_emit_in; [exact Hpq |]. right. right.
      unfold hCA. apply emit_enter_hit; auto. }
    assert (ICB : In (line_hit B C p q) (clip_halfplane [A; B; C] p q)).
    { apply clip_tri_emit_in; [exact Hpq |]. right. left.
      apply emit_leave_hit; auto. }
    assert (IA : In A (clip_halfplane [A; B; C] p q)).
    { apply clip_tri_emit_in; [exact Hpq |]. right. right.
      apply emit_enter_cur; auto. }
    assert (IB : In B (clip_halfplane [A; B; C] p q)).
    { apply clip_tri_emit_in; [exact Hpq |]. left. apply emit_cur_in; auto. }
    assert (HsymB : hCB = line_hit B C p q).
    { unfold hCB. apply line_hit_sym. unfold fb, fc in Hdc. exact Hdc. }
    assert (HMclip : in_hull (clip_halfplane [A; B; C] p q) M).
    { apply members_in_hull with (K := [hCA; hCB]); [| exact HM].
      intros vtx Hvtx. simpl in Hvtx. destruct Hvtx as [E|[E|[]]].
      - rewrite <- E. apply in_hull_in. exact ICA.
      - rewrite <- E, HsymB. apply in_hull_in. exact ICB. }
    set (lam := fin / (fin - fc)).
    set (t := c * (fin - fc) / fin).
    assert (Ht0 : 0 <= t).
    { unfold t. apply Rmult_le_pos; [apply Rmult_le_pos; lra |].
      apply Rlt_le, Rinv_0_lt_compat. exact Hfin. }
    assert (Ht1 : t <= 1).
    { unfold t. apply frac_le_1. exact Hfin.
      (* 0 <= (1-c)*fin + c*fc = s*fin + c*fc = fx *)
      replace ((1 - c) * fin + c * fc) with (s * fin + c * fc) by (rewrite Es; ring).
      rewrite Hsf, <- Hfx. exact Hin. }
    assert (Htl : t * lam = c).
    { unfold t, lam. field. lra. }
    assert (HXin : x = convex_combination Xin C c).
    { rewrite Hxeq. unfold Xin, convex_combination, bary3. rewrite <- Es.
      destruct A, B, C. simpl. f_equal.
      - unfold ap, bp. replace s with (a + b) by reflexivity. field. lra.
      - unfold ap, bp. replace s with (a + b) by reflexivity. field. lra. }
    assert (HM2 : line_hit Xin C p q = convex_combination Xin C lam).
    { rewrite line_hit_combo. f_equal.
      assert (Efin : cross p q Xin = fin).
      { unfold Xin, fin. exact Hcross. }
      rewrite Efin. replace (cross p q C) with fc by reflexivity.
      unfold lam. reflexivity. }
    assert (HMeq : M = line_hit Xin C p q).
    { unfold M. apply line_hit_sym.
      unfold Xin. rewrite Hcross. unfold fin in Hd0. exact Hd0. }
    assert (HxM : x = convex_combination Xin M t).
    { rewrite <- HMeq in HM2. rewrite HM2, combo_nest, Htl. exact HXin. }
    (* Xin is in the clip because it is a combo of A and B. *)
    assert (HXin_hull : in_hull (clip_halfplane [A; B; C] p q) Xin).
    { assert (E : Xin = convex_combination A B bp).
      { unfold Xin, convex_combination, bary3. replace ap with (1 - bp) by lra.
        destruct A, B, C. simpl. f_equal; ring. }
      rewrite E. apply in_hull_conv; try (split; [exact Hbp | lra]).
      - apply in_hull_in. exact IA.
      - apply in_hull_in. exact IB. }
    rewrite HxM. apply in_hull_conv; try (split; [exact Ht0 | exact Ht1]).
    + exact HXin_hull.
    + exact HMclip.
Qed.
Lemma in_hull_rot : forall A B C x,
  in_hull [A; B; C] x -> in_hull [B; C; A] x.
Proof.
  intros A B C x Hx. apply in_tri_hull3 in Hx.
  destruct Hx as [a [b [c [Ha [Hb [Hc [Hs Hxeq]]]]]]].
  apply in_tri_hull3. exists b, c, a. repeat split; try lra.
  rewrite Hxeq. unfold bary3. destruct A, B, C. simpl. f_equal; ring.
Qed.
Lemma clip_tri_all_in : forall A B C p q x,
  point_eqb p q = false ->
  inside_b p q A = true -> inside_b p q B = true -> inside_b p q C = true ->
  in_hull [A; B; C] x ->
  in_hull (clip_halfplane [A; B; C] p q) x.
Proof.
  intros A B C p q x Hpq HA HB HC Hx.
  apply in_tri_hull3 in Hx.
  destruct Hx as [a [b [c [Ha [Hb [Hc [Hs Hxeq]]]]]]].
  rewrite clip_tri_list by exact Hpq.
  unfold emit_edge. rewrite HA, HB, HC. simpl.
  apply in_tri_hull3. exists b, c, a. repeat split; try lra.
  rewrite Hxeq. unfold bary3. destruct A, B, C. simpl. f_equal; ring.
Qed.
Lemma clip_tri_all_out : forall A B C p q x,
  inside_b p q A = false -> inside_b p q B = false -> inside_b p q C = false ->
  in_hull [A; B; C] x -> ~ inside_closed p q x.
Proof.
  intros A B C p q x HA HB HC Hx Hin.
  apply in_tri_hull3 in Hx.
  destruct Hx as [a [b [c [Ha [Hb [Hc [Hs Hxeq]]]]]]].
  assert (Hfx : cross p q x =
    a * cross p q A + b * cross p q B + c * cross p q C).
  { rewrite Hxeq. apply cross_bary3. exact Hs. }
  assert (Hlt : cross p q x < 0).
  { rewrite Hfx. apply weighted_neg; try assumption; apply inside_b_false; assumption. }
  unfold inside_closed in Hin. exact (Rle_not_lt _ _ Hin Hlt).
Qed.
Theorem clip_tri_correct : forall A B C p q x,
  in_hull (clip_halfplane [A; B; C] p q) x <->
  in_hull [A; B; C] x /\ inside_closed p q x.
Proof.
  intros A B C p q x. destruct (point_eqb p q) eqn:Epq.
  - apply point_eqb_true in Epq. subst q.
    unfold clip_halfplane. rewrite point_eqb_refl. split.
    + intros Hx. split; [exact Hx | unfold inside_closed].
      unfold cross. ring_simplify. lra.
    + intros [Hx _]. exact Hx.
  - split.
    + apply clip_tri_sound. exact Epq.
    + intros [Hx Hin].
      destruct (inside_b p q A) eqn:iA;
      destruct (inside_b p q B) eqn:iB;
      destruct (inside_b p q C) eqn:iC.
      * apply clip_tri_all_in; assumption.
      * apply clip_tri_two_in; assumption.
      * (* A,C inside, B outside: two-in on [C;A;B] *)
        rewrite (clip_tri_cycle_hull A B C p q x Epq).
        rewrite (clip_tri_cycle_hull B C A p q x Epq).
        apply clip_tri_two_in; try assumption.
        apply in_hull_rot, in_hull_rot. exact Hx.
      * apply clip_tri_one_in; assumption.
      * (* B,C inside, A outside: two-in on [B;C;A] *)
        rewrite (clip_tri_cycle_hull A B C p q x Epq).
        apply clip_tri_two_in; try assumption.
        apply in_hull_rot. exact Hx.
      * (* only B inside *)
        rewrite (clip_tri_cycle_hull A B C p q x Epq).
        apply clip_tri_one_in; try assumption.
        apply in_hull_rot. exact Hx.
      * (* only C inside: one-in on [C;A;B] *)
        rewrite (clip_tri_cycle_hull A B C p q x Epq).
        rewrite (clip_tri_cycle_hull B C A p q x Epq).
        apply clip_tri_one_in; try assumption.
        apply in_hull_rot, in_hull_rot. exact Hx.
      * exfalso.
        apply clip_tri_all_out with (A:=A) (B:=B) (C:=C) (p:=p) (q:=q) (x:=x); assumption.
Qed.

(* Assumptions: sig_not_dec, sig_forall_dec, functional_extensionality_dep. *)
Print Assumptions point_eqb_true.
Print Assumptions point_eqb_false_distinct.
Print Assumptions point_eqb_refl.
Print Assumptions cross_cycle.
Print Assumptions cross_cycle2.
Print Assumptions cross_swap.
Print Assumptions cross_bary3.
Print Assumptions cross_sum3.
Print Assumptions cross_combo.
Print Assumptions line_hit_combo.
Print Assumptions line_hit_on_line.
Print Assumptions inside_b_true.
Print Assumptions inside_b_false.
Print Assumptions in_tri_hull3.
Print Assumptions tri_bary_recon.
Print Assumptions tri_slack_hull.
Print Assumptions rsum_scale.
Print Assumptions rsum_add.
Print Assumptions rscale_nonneg.
Print Assumptions radd_nonneg.
Print Assumptions wpt_scale.
Print Assumptions wpt_add.
Print Assumptions rscale_length.
Print Assumptions radd_length.
Print Assumptions in_hull_conv.
Print Assumptions zero_weights.
Print Assumptions in_hull_in.
Print Assumptions wpt2.
Print Assumptions in_hull_embed2.
Print Assumptions hit_param_01.
Print Assumptions line_hit_on_seg.
Print Assumptions emit_in_edge.
Print Assumptions clip_tri_list.
Print Assumptions rsum_nonneg.
Print Assumptions nonneg_sum0.
Print Assumptions wpt_zeros.
Print Assumptions inside_conv.
Print Assumptions members_in_hull.
Print Assumptions members_inside.
Print Assumptions clip_tri_sound.
Print Assumptions line_hit_sym.
Print Assumptions weighted_neg.
Print Assumptions hit_blend.
Print Assumptions in_clip_app_l.
Print Assumptions in_clip_app_r.
Print Assumptions clip_tri_emit_in.
Print Assumptions emit_cur_in.
Print Assumptions emit_leave_hit.
Print Assumptions emit_enter_hit.
Print Assumptions emit_enter_cur.
Print Assumptions two_weight_neg.
Print Assumptions frac_le_1.
Print Assumptions combo_nest.
Print Assumptions clip_tri_one_in.
Print Assumptions hull_rot3.
Print Assumptions clip_tri_cycle_hull.
Print Assumptions clip_tri_two_in.
Print Assumptions in_hull_rot.
Print Assumptions clip_tri_all_in.
Print Assumptions clip_tri_all_out.
Print Assumptions clip_tri_correct.
