(* NetTopologySuite.Proofs.TrianglePairClip
   Exact intersection of two CCW triangles by three half-plane clips,
   the I∩I DE-9IM entry, and the separating-edge corollary.
   I∩B, B∩I, B∩B are T1b. Exterior cells are T1c.
   topic: relate
   claimId: tri-de9im-a
   witness: ConvexClip.clip_halfplane
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7), human-reviewed.
   License: BSD-3-Clause *)

From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex RingArea979 Centroid
  DE9IM ConvexClip ConvexClipPoly ConvexClipComplete.
Local Open Scope R_scope.

Definition Dim2 : DimValue := Some 2%nat.
Definition DimF : DimValue := None.

Definition poly_area2 (ps : list Point) : R := signed_area2 ps.

Definition tri_open (A B C X : Point) : Prop :=
  0 < cross A B X /\ 0 < cross B C X /\ 0 < cross C A X.

Definition tri_inter (A B C D E F : Point) : list Point :=
  clip_halfplane
    (clip_halfplane
      (clip_halfplane [A; B; C] D E) E F) F D.

(* -------------------------------------------------------------------------- *)
(* A positive triangle supports itself, so three clips are exact.             *)
(* -------------------------------------------------------------------------- *)

Lemma tri_ccw_supports : forall A B C,
  0 < cross A B C -> convex_supports [A; B; C].
Proof.
  intros A B C Hd. unfold convex_supports. simpl.
  split; [| split; [| split; [ | exact I ]]].
  - intros v Hv. destruct Hv as [<-|[<-|[<-|[]]]].
    + unfold cross. ring_simplify. lra.
    + unfold cross. ring_simplify. lra.
    + apply Rlt_le. exact Hd.
  - intros v Hv. destruct Hv as [<-|[<-|[<-|[]]]].
    + rewrite <- (cross_cycle A B C). apply Rlt_le. exact Hd.
    + unfold cross. ring_simplify. lra.
    + unfold cross. ring_simplify. lra.
  - intros v Hv. destruct Hv as [<-|[<-|[<-|[]]]].
    + unfold cross. ring_simplify. lra.
    + rewrite <- (cross_cycle2 A B C). apply Rlt_le. exact Hd.
    + unfold cross. ring_simplify. lra.
Qed.

Theorem tri_inter_correct : forall A B C D E F x,
  0 < cross A B C -> 0 < cross D E F ->
  in_hull (tri_inter A B C D E F) x <->
  in_tri A B C x /\ in_tri D E F x.
Proof.
  intros A B C D E F x HA HB.
  set (K0 := [A; B; C]).
  set (K1 := clip_halfplane K0 D E).
  set (K2 := clip_halfplane K1 E F).
  set (K3 := clip_halfplane K2 F D).
  assert (S0 : convex_supports K0) by (unfold K0; apply tri_ccw_supports; exact HA).
  assert (S1 : convex_supports K1) by (apply clip_convex_ccw; exact S0).
  assert (S2 : convex_supports K2) by (apply clip_convex_ccw; exact S1).
  assert (E3 : tri_inter A B C D E F = clip_halfplane K2 F D) by reflexivity.
  assert (E2 : K2 = clip_halfplane K1 E F) by reflexivity.
  assert (E1 : K1 = clip_halfplane K0 D E) by reflexivity.
  assert (E0 : K0 = [A; B; C]) by reflexivity.
  rewrite E3, (clip_correct K2 F D x S2).
  rewrite E2, (clip_correct K1 E F x S1).
  rewrite E1, (clip_correct K0 D E x S0), E0.
  unfold inside_closed. split.
  - intros [[[Hh Hde] Hef] Hfd]. split.
    + apply (in_tri_hull3 A B C x). exact Hh.
    + apply (tri_slack_hull D E F x HB). repeat split; assumption.
  - intros [Ha Hb]. apply (tri_slack_hull D E F x HB) in Hb.
    apply (in_tri_hull3 A B C x) in Ha.
    destruct Hb as [Hde Hb1]. destruct Hb1 as [Hef Hfd].
    repeat split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Shoelace is the fan of crosses from the first vertex. Convex chains have   *)
(* nonnegative fans, and a zero fan puts every hull point on one line.        *)
(* -------------------------------------------------------------------------- *)

Fixpoint fan_area (o prev : Point) (rest : list Point) : R :=
  match rest with
  | [] => 0
  | cur :: rs => cross o prev cur + fan_area o cur rs
  end.

Lemma cross_ooo : forall o z, cross o o z = 0.
Proof. intros. unfold cross. ring. Qed.

Lemma signed_area2_pair0 : forall o p, poly_area2 [o; p] = 0.
Proof.
  intros o p. unfold poly_area2, signed_area2. cbn [app].
  rewrite !shoelace_open_cons2, shoelace_open_single.
  unfold edge_cross. ring.
Qed.

Lemma signed_area2_single0 : forall o, poly_area2 [o] = 0.
Proof.
  intros o. unfold poly_area2, signed_area2. cbn [app].
  rewrite shoelace_open_cons2, shoelace_open_single.
  unfold edge_cross. ring.
Qed.

Lemma signed_area2_nil0 : poly_area2 [] = 0.
Proof. unfold poly_area2, signed_area2. reflexivity. Qed.

Lemma signed_area2_open3 : forall o p z r,
  poly_area2 (o :: p :: z :: r) =
  edge_cross o p + edge_cross p z + shoelace_open (z :: r ++ [o]).
Proof.
  intros. unfold poly_area2, signed_area2. simpl.
  assert (E : shoelace_open (z :: r ++ [o]) =
    match r ++ [o] with
    | [] => 0
    | q :: _ => edge_cross z q + shoelace_open (r ++ [o])
    end) by reflexivity.
  rewrite <- E. ring.
Qed.

Lemma signed_area2_open2 : forall o z r,
  poly_area2 (o :: z :: r) =
  edge_cross o z + shoelace_open (z :: r ++ [o]).
Proof.
  intros. unfold poly_area2, signed_area2. simpl.
  assert (E : shoelace_open (z :: r ++ [o]) =
    match r ++ [o] with
    | [] => 0
    | q :: _ => edge_cross z q + shoelace_open (r ++ [o])
    end) by reflexivity.
  rewrite <- E. ring.
Qed.

Lemma signed_area2_peel : forall o p r,
  poly_area2 (o :: p :: r) =
  match r with
  | [] => 0
  | z :: _ => cross o p z + poly_area2 (o :: r)
  end.
Proof.
  intros o p r. destruct r as [|z r'].
  - apply signed_area2_pair0.
  - change (poly_area2 (o :: p :: z :: r') =
            cross o p z + poly_area2 (o :: z :: r')).
    rewrite signed_area2_open3, signed_area2_open2.
    replace (edge_cross o p + edge_cross p z)
      with (cross o p z + edge_cross o z)
      by (unfold edge_cross, cross; ring).
    ring.
Qed.

Lemma chain_supports_prefix : forall prev rest extra all,
  chain_supports prev (rest ++ extra) all ->
  chain_supports prev rest all.
Proof.
  intros prev rest extra all. revert prev.
  induction rest as [|cur rest IH]; intros prev Hs.
  - simpl. exact I.
  - simpl in Hs. destruct Hs as [He Ht]. simpl. split.
    + exact He.
    + apply IH. exact Ht.
Qed.

Lemma signed_area2_fan : forall o p r,
  poly_area2 (o :: p :: r) = fan_area o p r.
Proof.
  intros o p r. revert p. induction r as [|z r IH]; intros p.
  - rewrite signed_area2_peel. reflexivity.
  - rewrite signed_area2_peel.
    change (cross o p z + poly_area2 (o :: z :: r) =
            cross o p z + fan_area o z r).
    rewrite IH. reflexivity.
Qed.

Lemma fan_area_ge0 : forall o prev rest all,
  chain_supports prev rest all ->
  In o all ->
  0 <= fan_area o prev rest.
Proof.
  intros o prev rest all. revert prev.
  induction rest as [|cur rest IH]; intros prev Hs Ho.
  - simpl. lra.
  - simpl in Hs. destruct Hs as [He Ht]. simpl.
    assert (Hz : 0 <= cross prev cur o) by (apply He; exact Ho).
    rewrite (cross_cycle2 prev cur o) in Hz.
    apply Rplus_le_le_0_compat; [exact Hz |].
    apply IH; assumption.
Qed.

Lemma poly_area2_ge0 : forall poly,
  convex_supports poly -> 0 <= poly_area2 poly.
Proof.
  intros poly Hs.
  destruct poly as [|o [|p [|z r]]].
  - rewrite signed_area2_nil0. lra.
  - rewrite signed_area2_single0. lra.
  - rewrite signed_area2_pair0. lra.
  - unfold convex_supports in Hs. simpl in Hs.
    destruct Hs as [_ Htail].
    rewrite signed_area2_fan.
    apply fan_area_ge0 with (all := o :: p :: z :: r).
    + apply chain_supports_prefix with (extra := [o]). exact Htail.
    + simpl. left. reflexivity.
Qed.

Lemma cross_le_fan : forall o prev rest all v,
  chain_supports prev rest all ->
  In o all ->
  In v all ->
  In v (o :: prev :: rest) ->
  cross o prev v <= fan_area o prev rest.
Proof.
  intros o prev rest all v. revert prev v.
  induction rest as [|cur rest IH]; intros prev v Hs Ho Hall Hv.
  - simpl. destruct Hv as [->|[->|[]]]; unfold cross; ring_simplify; lra.
  - simpl in Hs. destruct Hs as [He Ht]. simpl.
    destruct Hv as [<-|[<-|[<-|Hv]]].
    + rewrite cross_third_eq_first.
      assert (Hc : 0 <= cross o prev cur).
      { rewrite cross_cycle. apply He. exact Ho. }
      apply Rplus_le_le_0_compat; [exact Hc |].
      apply fan_area_ge0 with (all := all); assumption.
    + rewrite cross_third_eq_second.
      assert (Hc : 0 <= cross o prev cur).
      { rewrite cross_cycle. apply He. exact Ho. }
      apply Rplus_le_le_0_compat; [exact Hc |].
      apply fan_area_ge0 with (all := all); assumption.
    + assert (Hf : 0 <= fan_area o cur rest)
        by (apply fan_area_ge0 with (all := all); assumption).
      assert (Hc : 0 <= cross o prev cur).
      { rewrite cross_cycle. apply He. exact Ho. }
      lra.
    + assert (IH' : cross o cur v <= fan_area o cur rest).
      { apply IH; [exact Ht | exact Ho | exact Hall |].
        right. right. exact Hv. }
      assert (Hedge : 0 <= cross prev cur v) by (apply He; exact Hall).
      assert (Hid : cross o prev cur + cross o cur v - cross prev cur v
                    = cross o prev v) by (unfold cross; ring).
      lra.
Qed.

Lemma cross_dot_zero : forall p q w ps,
  length w = length ps ->
  (forall v, In v ps -> cross p q v = 0) ->
  cross_dot p q w ps = 0.
Proof.
  intros p q w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl Hz; simpl in *; try discriminate.
  - reflexivity.
  - assert (Ev : cross p q v = 0) by (apply Hz; left; reflexivity).
    rewrite (IH w).
    + rewrite Ev. ring.
    + lia.
    + intros u Hu. apply Hz. right. exact Hu.
Qed.

Lemma hull_on_line : forall p q ps x,
  (forall v, In v ps -> cross p q v = 0) ->
  in_hull ps x ->
  cross p q x = 0.
Proof.
  intros p q ps x Hz [w [Hl [_ [Hs Hw]]]].
  rewrite <- Hw. rewrite (cross_wpt_sum1 p q w ps Hl Hs).
  apply cross_dot_zero; assumption.
Qed.

Lemma three_on_line : forall p q h1 h2 x,
  points_distinct p q ->
  cross p q h1 = 0 ->
  cross p q h2 = 0 ->
  cross p q x = 0 ->
  cross h1 h2 x = 0.
Proof.
  intros p q h1 h2 x Hd H1 H2 Hx.
  assert (E := chord_frame p q h1 h2 x H1 H2).
  assert (E0 : dist_sq q p * cross h1 h2 x = 0).
  { rewrite Hx in E.
    replace ((line_g p q h2 - line_g p q h1) * 0) with 0 in E by ring.
    exact E. }
  assert (Hpos : 0 < dist_sq q p) by (apply dist_pos_distinct; exact Hd).
  assert (Hd0 : dist_sq q p <> 0).
  { apply not_eq_sym. apply Rlt_not_eq. exact Hpos. }
  apply (Rmult_eq_reg_l (dist_sq q p) (cross h1 h2 x) 0).
  - rewrite E0. ring.
  - exact Hd0.
Qed.

Lemma wpt_const : forall p w ps,
  length w = length ps ->
  (forall v, In v ps -> v = p) ->
  wpt w ps = mkPoint (rsum w * px p) (rsum w * py p).
Proof.
  intros p w ps. revert w.
  induction ps as [|v ps IH]; intros [|a w] Hl Hall; simpl in Hl; try discriminate.
  - simpl. f_equal; ring.
  - injection Hl as Hl.
    assert (Ev : v = p) by (apply Hall; left; reflexivity).
    subst v. simpl.
    rewrite (IH w).
    + destruct p as [px0 py0]. simpl. f_equal; ring.
    + exact Hl.
    + intros u Hu. apply Hall. right. exact Hu.
Qed.

Lemma in_hull_const : forall ps p x,
  (forall v, In v ps -> v = p) ->
  in_hull ps x ->
  x = p.
Proof.
  intros ps p x Hall [w [Hl [_ [Hs Hw]]]].
  rewrite <- Hw. rewrite (wpt_const p w ps Hl Hall). rewrite Hs.
  destruct p as [px0 py0]. simpl. f_equal; ring.
Qed.

Lemma in_hull_dup_head : forall o ps x,
  in_hull (o :: o :: ps) x -> in_hull (o :: ps) x.
Proof.
  intros o ps x [w [Hl [Hn [Hs Hw]]]].
  destruct w as [|a [|b wt]]; simpl in Hl; try discriminate.
  injection Hl as Hl.
  exists ((a + b) :: wt).
  assert (Ha : 0 <= a) by (apply Hn; simpl; left; reflexivity).
  assert (Hb : 0 <= b) by (apply Hn; simpl; right; left; reflexivity).
  repeat split.
  - simpl. f_equal. exact Hl.
  - intros z Hz. simpl in Hz. destruct Hz as [<-|Hz].
    + lra.
    + apply Hn. simpl. right. right. exact Hz.
  - simpl in Hs. simpl. lra.
  - rewrite <- Hw. simpl. destruct o as [ox oy]. simpl. f_equal; ring.
Qed.

Lemma chain_supports_fewer : forall prev rest all all',
  (forall v, In v all' -> In v all) ->
  chain_supports prev rest all ->
  chain_supports prev rest all'.
Proof.
  intros prev rest all all' Hsub. revert prev.
  induction rest as [|cur rest IH]; intros prev Hs.
  - simpl. exact I.
  - simpl in Hs. destruct Hs as [He Ht]. simpl. split.
    + intros v Hv. apply He. apply Hsub. exact Hv.
    + apply IH. exact Ht.
Qed.

Lemma verts_on_first_edge : forall o p z r v,
  convex_supports (o :: p :: z :: r) ->
  poly_area2 (o :: p :: z :: r) = 0 ->
  In v (o :: p :: z :: r) ->
  cross o p v = 0.
Proof.
  intros o p z r v Hs Ha Hin.
  unfold convex_supports in Hs. simpl in Hs.
  destruct Hs as [Hedge Htail].
  assert (Hge : 0 <= cross o p v) by (apply Hedge; exact Hin).
  assert (Hle : cross o p v <= fan_area o p (z :: r)).
  { apply cross_le_fan with (all := o :: p :: z :: r).
    - apply chain_supports_prefix with (extra := [o]). exact Htail.
    - simpl. left. reflexivity.
    - exact Hin.
    - exact Hin. }
  rewrite signed_area2_fan in Ha. lra.
Qed.

Lemma area_drop_dup : forall o z r,
  poly_area2 (o :: o :: z :: r) = poly_area2 (o :: z :: r).
Proof.
  intros o z r. rewrite (signed_area2_peel o o (z :: r)).
  rewrite cross_ooo. ring.
Qed.

Lemma supports_drop_dup : forall o z r,
  convex_supports (o :: o :: z :: r) ->
  convex_supports (o :: z :: r).
Proof.
  intros o z r Hs.
  destruct r as [|w r'].
  - unfold convex_supports. exact I.
  - unfold convex_supports in Hs. cbn [tl app] in Hs.
    assert (Ehs :
      chain_supports o (o :: z :: w :: r' ++ [o]) (o :: o :: z :: w :: r') =
      ((forall v, In v (o :: o :: z :: w :: r') -> 0 <= cross o o v) /\
       chain_supports o (z :: w :: r' ++ [o]) (o :: o :: z :: w :: r')))
      by reflexivity.
    rewrite Ehs in Hs. destruct Hs as [_ Ht].
    unfold convex_supports. cbn [tl app].
    apply chain_supports_fewer with (all := o :: o :: z :: w :: r').
    + intros v Hv. destruct Hv as [<-|[<-|[<-|Hv]]].
      * left. reflexivity.
      * right. right. left. reflexivity.
      * right. right. right. left. reflexivity.
      * right. right. right. right. exact Hv.
    + exact Ht.
Qed.

Lemma flat_hull_len : forall n poly,
  length poly = n ->
  convex_supports poly ->
  poly_area2 poly = 0 ->
  forall x y z,
    in_hull poly x -> in_hull poly y -> in_hull poly z ->
    cross x y z = 0.
Proof.
  induction n as [|n IH]; intros poly Hlen Hs Ha x y z Hx Hy Hz.
  - destruct poly; [apply in_hull_nil in Hx; contradiction | simpl in Hlen; lia].
  - destruct poly as [|o [|p [|z0 r]]].
    + simpl in Hlen. lia.
    + apply in_hull_one in Hx, Hy, Hz. subst. unfold cross. ring.
    + assert (Hv : forall v, In v [o; p] -> cross o p v = 0).
      { intros v Hin. destruct Hin as [<-|[<-|[]]].
        - apply cross_third_eq_first.
        - apply cross_third_eq_second. }
      assert (Hx0 : cross o p x = 0) by (apply hull_on_line with (ps := [o; p]); assumption).
      assert (Hy0 : cross o p y = 0) by (apply hull_on_line with (ps := [o; p]); assumption).
      assert (Hz0 : cross o p z = 0) by (apply hull_on_line with (ps := [o; p]); assumption).
      destruct (point_eqb o p) eqn:Eop.
      * apply point_eqb_true in Eop. subst p.
        assert (Hall : forall v, In v [o; o] -> v = o).
        { intros v Hin. destruct Hin as [<-|[<-|[]]]; reflexivity. }
        assert (Ex : x = o) by (apply (in_hull_const [o; o] o x Hall); exact Hx).
        assert (Ey : y = o) by (apply (in_hull_const [o; o] o y Hall); exact Hy).
        assert (Ez : z = o) by (apply (in_hull_const [o; o] o z Hall); exact Hz).
        subst. unfold cross. ring.
      * apply three_on_line with (p := o) (q := p); try assumption.
        apply point_eqb_false_distinct. exact Eop.
    + destruct (point_eqb o p) eqn:Eop.
      * apply point_eqb_true in Eop. subst p.
        assert (HlenT : length (o :: z0 :: r) = n).
        { simpl in Hlen. simpl. lia. }
        assert (HaT : poly_area2 (o :: z0 :: r) = 0).
        { rewrite <- area_drop_dup. exact Ha. }
        assert (HsT : convex_supports (o :: z0 :: r)) by (apply supports_drop_dup; exact Hs).
        apply (IH (o :: z0 :: r) HlenT HsT HaT).
        -- apply in_hull_dup_head. exact Hx.
        -- apply in_hull_dup_head. exact Hy.
        -- apply in_hull_dup_head. exact Hz.
      * assert (Hvert : forall v, In v (o :: p :: z0 :: r) -> cross o p v = 0).
        { intros v Hin. apply verts_on_first_edge with (z := z0) (r := r); assumption. }
        assert (Hx0 : cross o p x = 0).
        { apply hull_on_line with (ps := o :: p :: z0 :: r); assumption. }
        assert (Hy0 : cross o p y = 0).
        { apply hull_on_line with (ps := o :: p :: z0 :: r); assumption. }
        assert (Hz0 : cross o p z = 0).
        { apply hull_on_line with (ps := o :: p :: z0 :: r); assumption. }
        apply three_on_line with (p := o) (q := p); try assumption.
        apply point_eqb_false_distinct. exact Eop.
Qed.

Lemma flat_hull : forall poly x y z,
  convex_supports poly ->
  poly_area2 poly = 0 ->
  in_hull poly x -> in_hull poly y -> in_hull poly z ->
  cross x y z = 0.
Proof.
  intros poly x y z Hs Ha Hx Hy Hz.
  apply flat_hull_len with (n := length poly) (poly := poly); try assumption.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Positive area exposes a strict interior point; a strict interior point     *)
(* forces positive area. Both use only the closed hull of the clip.           *)
(* -------------------------------------------------------------------------- *)

Lemma ccw_edge_distinct : forall A B C,
  0 < cross A B C -> points_distinct A B.
Proof.
  intros A B C H. destruct (point_eqb A B) eqn:E.
  - apply point_eqb_true in E. subst B. rewrite cross_ooo in H. lra.
  - apply point_eqb_false_distinct. exact E.
Qed.

Lemma fan_pos_triple : forall o prev rest all,
  chain_supports prev rest all ->
  In o all ->
  In prev all ->
  (forall v, In v rest -> In v all) ->
  0 < fan_area o prev rest ->
  exists p q, In p all /\ In q all /\ 0 < cross o p q.
Proof.
  intros o prev rest. revert prev.
  induction rest as [|cur rest IH]; intros prev all Hs Ho Hp Hsub Hf.
  - simpl in Hf. lra.
  - simpl in Hs. destruct Hs as [He Ht]. simpl in Hf.
    assert (Hc : 0 <= cross o prev cur).
    { rewrite cross_cycle. apply He. exact Ho. }
    assert (Hcur : In cur all) by (apply Hsub; simpl; left; reflexivity).
    destruct (Rle_lt_or_eq_dec 0 (cross o prev cur) Hc) as [Hlt|Heq].
    + exists prev, cur. repeat split; assumption.
    + apply IH with (prev := cur).
      * exact Ht.
      * exact Ho.
      * exact Hcur.
      * intros v Hv. apply Hsub. simpl. right. exact Hv.
      * lra.
Qed.

Lemma area_pos_triple : forall poly,
  convex_supports poly ->
  0 < poly_area2 poly ->
  exists o p q, In o poly /\ In p poly /\ In q poly /\ 0 < cross o p q.
Proof.
  intros poly Hs Ha.
  destruct poly as [|o [|p [|z r]]].
  - rewrite signed_area2_nil0 in Ha. lra.
  - rewrite signed_area2_single0 in Ha. lra.
  - rewrite signed_area2_pair0 in Ha. lra.
  - rewrite signed_area2_fan in Ha.
    unfold convex_supports in Hs. simpl in Hs.
    destruct Hs as [_ Htail].
    assert (Hchain : chain_supports p (z :: r) (o :: p :: z :: r)).
    { apply chain_supports_prefix with (extra := [o]). exact Htail. }
    destruct (fan_pos_triple o p (z :: r) (o :: p :: z :: r) Hchain)
      as [u [v [Hu [Hv Hc]]]].
    + simpl. left. reflexivity.
    + simpl. right. left. reflexivity.
    + intros x Hx. destruct Hx as [<-|Hx].
      * simpl. right. right. left. reflexivity.
      * simpl. right. right. right. exact Hx.
    + exact Ha.
    + exists o, u, v. repeat split; try assumption.
      simpl. left. reflexivity.
Qed.

Lemma cross_centroid3 : forall p q A B C,
  cross p q (centroid3 A B C) =
    (cross p q A + cross p q B + cross p q C) / 3.
Proof.
  intros p q A B C. unfold centroid3, cross.
  destruct p, q, A, B, C. simpl. field.
Qed.

Lemma centroid3_combo : forall A B C,
  centroid3 A B C =
    convex_combination (convex_combination A B (1 / 2)) C (1 / 3).
Proof.
  intros A B C. unfold centroid3, convex_combination.
  destruct A, B, C. simpl. f_equal; field.
Qed.

Lemma centroid3_in_hull : forall ps A B C,
  in_hull ps A -> in_hull ps B -> in_hull ps C ->
  in_hull ps (centroid3 A B C).
Proof.
  intros ps A B C Ha Hb Hc. rewrite centroid3_combo.
  apply in_hull_conv.
  - apply in_hull_conv; try assumption. split; lra.
  - exact Hc.
  - split; lra.
Qed.

Lemma sum3_zero : forall a b c,
  0 <= a -> 0 <= b -> 0 <= c ->
  a + b + c = 0 -> a = 0 /\ b = 0 /\ c = 0.
Proof. intros. repeat split; lra. Qed.

Lemma edge_slack_centroid : forall A B o p q,
  points_distinct A B ->
  0 <= cross A B o -> 0 <= cross A B p -> 0 <= cross A B q ->
  0 < cross o p q ->
  0 < cross A B (centroid3 o p q).
Proof.
  intros A B o p q Hd Ho Hp Hq Hc.
  rewrite cross_centroid3.
  set (s := cross A B o + cross A B p + cross A B q).
  destruct (Req_dec_T s 0) as [Hz|Hnz].
  - assert (Ez : cross A B o = 0 /\ cross A B p = 0 /\ cross A B q = 0).
    { apply sum3_zero; [exact Ho | exact Hp | exact Hq | unfold s in Hz; exact Hz]. }
    destruct Ez as [Eo [Ep Eq]].
    assert (Hc0 : cross o p q = 0).
    { apply three_on_line with (p := A) (q := B); assumption. }
    lra.
  - assert (Hle : 0 <= s) by (unfold s; lra).
    destruct (Rle_lt_or_eq_dec 0 s Hle) as [Hs|Heq].
    + apply Rdiv_lt_0_compat; [exact Hs | lra].
    + exfalso. apply Hnz. symmetry. exact Heq.
Qed.

Lemma tri_open_centroid : forall A B C o p q,
  0 < cross A B C ->
  in_tri A B C o -> in_tri A B C p -> in_tri A B C q ->
  0 < cross o p q ->
  tri_open A B C (centroid3 o p q).
Proof.
  intros A B C o p q Hd Ho Hp Hq Hc.
  assert (So : 0 <= cross A B o /\ 0 <= cross B C o /\ 0 <= cross C A o).
  { apply (proj2 (tri_slack_hull A B C o Hd)). exact Ho. }
  assert (Sp : 0 <= cross A B p /\ 0 <= cross B C p /\ 0 <= cross C A p).
  { apply (proj2 (tri_slack_hull A B C p Hd)). exact Hp. }
  assert (Sq : 0 <= cross A B q /\ 0 <= cross B C q /\ 0 <= cross C A q).
  { apply (proj2 (tri_slack_hull A B C q Hd)). exact Hq. }
  destruct So as [Habo [Hbco Hcao]].
  destruct Sp as [Habp [Hbcp Hcap]].
  destruct Sq as [Habq [Hbcq Hcaq]].
  repeat split.
  - apply edge_slack_centroid; try assumption.
    apply ccw_edge_distinct with (C := C). exact Hd.
  - apply edge_slack_centroid; try assumption.
    apply ccw_edge_distinct with (C := A). rewrite <- cross_cycle. exact Hd.
  - apply edge_slack_centroid; try assumption.
    apply ccw_edge_distinct with (C := B). rewrite <- cross_cycle2. exact Hd.
Qed.

Lemma tri_inter_supports : forall A B C D E F,
  0 < cross A B C ->
  convex_supports (tri_inter A B C D E F).
Proof.
  intros A B C D E F H. unfold tri_inter.
  apply clip_convex_ccw. apply clip_convex_ccw. apply clip_convex_ccw.
  apply tri_ccw_supports. exact H.
Qed.

Definition seg_room (sx sg : R) : R :=
  if Rle_dec 0 (sg - sx) then 1 else sx / (sx - sg).

Lemma seg_room_pos : forall sx sg, 0 < sx -> 0 < seg_room sx sg.
Proof.
  intros sx sg Hs. unfold seg_room.
  destruct (Rle_dec 0 (sg - sx)) as [|H].
  - lra.
  - apply Rnot_le_lt in H.
    apply Rdiv_lt_0_compat; lra.
Qed.

Lemma slack_nonneg_room : forall sx sg t,
  0 < sx -> 0 <= t -> t <= seg_room sx sg ->
  0 <= (1 - t) * sx + t * sg.
Proof.
  intros sx sg t Hs Ht0 Ht. unfold seg_room in Ht.
  destruct (Rle_dec 0 (sg - sx)) as [Hg|Hg].
  - replace ((1 - t) * sx + t * sg) with (sx + t * (sg - sx)) by ring.
    apply Rplus_le_le_0_compat; [apply Rlt_le; exact Hs |].
    apply Rmult_le_pos; lra.
  - apply Rnot_le_lt in Hg.
    assert (Hd : 0 < sx - sg) by lra.
    assert (Hnz : sx - sg <> 0).
    { apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
    replace ((1 - t) * sx + t * sg)
      with ((sx - sg) * (sx / (sx - sg) - t)) by (field; exact Hnz).
    apply Rmult_le_pos; lra.
Qed.

Fixpoint rmin_list (rs : list R) : R :=
  match rs with
  | [] => 1 / 2
  | a :: t => Rmin a (rmin_list t)
  end.

Lemma Rmin_pos : forall a b, 0 < a -> 0 < b -> 0 < Rmin a b.
Proof.
  intros a b Ha Hb. destruct (Rle_dec a b) as [H|H].
  - rewrite Rmin_left by exact H. exact Ha.
  - apply Rnot_le_lt in H. rewrite Rmin_right by (apply Rlt_le; exact H). exact Hb.
Qed.

Lemma rmin_list_pos : forall rs,
  (forall a, In a rs -> 0 < a) -> 0 < rmin_list rs.
Proof.
  induction rs as [|a rs IH]; intros Hp.
  - simpl. lra.
  - simpl. apply Rmin_pos.
    + apply Hp. simpl. left. reflexivity.
    + apply IH. intros b Hb. apply Hp. simpl. right. exact Hb.
Qed.

Lemma rmin_list_le : forall rs a, In a rs -> rmin_list rs <= a.
Proof.
  induction rs as [|b rs IH]; intros a Hin; simpl in Hin; try contradiction.
  simpl. destruct Hin as [<-|Hin].
  - apply Rmin_l.
  - apply Rle_trans with (r2 := rmin_list rs).
    + apply Rmin_r.
    + apply IH. exact Hin.
Qed.

Lemma rmin_list_half : forall rs, rmin_list rs <= 1 / 2.
Proof.
  induction rs as [|a rs IH].
  - simpl. lra.
  - simpl. apply Rle_trans with (r2 := rmin_list rs); [apply Rmin_r | exact IH].
Qed.

Lemma nudge_closed : forall A B C X V t,
  0 < cross A B C ->
  0 < cross A B X -> 0 < cross B C X -> 0 < cross C A X ->
  0 <= t ->
  t <= seg_room (cross A B X) (cross A B V) ->
  t <= seg_room (cross B C X) (cross B C V) ->
  t <= seg_room (cross C A X) (cross C A V) ->
  in_tri A B C (convex_combination X V t).
Proof.
  intros A B C X V t Hd Hab Hbc Hca Ht HrAB HrBC HrCA.
  apply (proj1 (tri_slack_hull A B C (convex_combination X V t) Hd)).
  repeat split; rewrite cross_combo.
  - apply slack_nonneg_room; assumption.
  - apply slack_nonneg_room; assumption.
  - apply slack_nonneg_room; assumption.
Qed.

Lemma cross_nudge : forall X A B C t,
  cross (convex_combination X A t)
        (convex_combination X B t)
        (convex_combination X C t)
  = t * t * cross A B C.
Proof.
  intros X A B C t. unfold convex_combination, cross.
  destruct X, A, B, C. simpl. ring.
Qed.

Lemma vertex_in_tri : forall A B C V,
  In V [A; B; C] -> in_tri A B C V.
Proof.
  intros A B C V Hin. apply in_tri_hull3. apply in_hull_in. exact Hin.
Qed.

Theorem ii_nonempty_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  (exists X, tri_open A B C X /\ tri_open D E F X) <->
  0 < poly_area2 (tri_inter A B C D E F).
Proof.
  intros A B C D E F HA HB. split.
  - intros [X [HOA HOB]].
    set (K := tri_inter A B C D E F).
    assert (HsK : convex_supports K) by (apply tri_inter_supports; exact HA).
    assert (Hge : 0 <= poly_area2 K) by (apply poly_area2_ge0; exact HsK).
    destruct (Rle_lt_or_eq_dec 0 (poly_area2 K) Hge) as [Hlt|Heq].
    + exact Hlt.
    + exfalso.
      destruct HOA as [HABX [HBCX HCAX]].
      destruct HOB as [HDEX [HEFX HFDX]].
      set (rooms :=
        [ seg_room (cross D E X) (cross D E A);
          seg_room (cross D E X) (cross D E B);
          seg_room (cross D E X) (cross D E C);
          seg_room (cross E F X) (cross E F A);
          seg_room (cross E F X) (cross E F B);
          seg_room (cross E F X) (cross E F C);
          seg_room (cross F D X) (cross F D A);
          seg_room (cross F D X) (cross F D B);
          seg_room (cross F D X) (cross F D C) ]).
      set (t := rmin_list rooms).
      assert (Ht : 0 < t).
      { unfold t, rooms. apply rmin_list_pos. intros s Hin.
        simpl in Hin.
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
        - apply seg_room_pos. exact HDEX.
        - apply seg_room_pos. exact HDEX.
        - apply seg_room_pos. exact HDEX.
        - apply seg_room_pos. exact HEFX.
        - apply seg_room_pos. exact HEFX.
        - apply seg_room_pos. exact HEFX.
        - apply seg_room_pos. exact HFDX.
        - apply seg_room_pos. exact HFDX.
        - apply seg_room_pos. exact HFDX. }
      assert (Ht12 : t <= 1 / 2) by (unfold t; apply rmin_list_half).
      assert (Ht0 : 0 <= t) by lra.
      assert (Ht1 : t <= 1) by lra.
      assert (RDEA : t <= seg_room (cross D E X) (cross D E A)).
      { unfold t. apply rmin_list_le. unfold rooms. simpl. left. reflexivity. }
      assert (RDEB : t <= seg_room (cross D E X) (cross D E B)).
      { unfold t. apply rmin_list_le. unfold rooms. simpl. right. left. reflexivity. }
      assert (RDEC : t <= seg_room (cross D E X) (cross D E C)).
      { unfold t. apply rmin_list_le. unfold rooms. simpl.
        right. right. left. reflexivity. }
      assert (REFA : t <= seg_room (cross E F X) (cross E F A)).
      { unfold t. apply rmin_list_le. unfold rooms. simpl.
        right. right. right. left. reflexivity. }
      assert (REFB : t <= seg_room (cross E F X) (cross E F B)).
      { unfold t. apply rmin_list_le. unfold rooms. simpl.
        right. right. right. right. left. reflexivity. }
      assert (REFC : t <= seg_room (cross E F X) (cross E F C)).
      { unfold t. apply rmin_list_le. unfold rooms. simpl.
        right. right. right. right. right. left. reflexivity. }
      assert (RFDA : t <= seg_room (cross F D X) (cross F D A)).
      { unfold t. apply rmin_list_le. unfold rooms. simpl.
        right. right. right. right. right. right. left. reflexivity. }
      assert (RFDB : t <= seg_room (cross F D X) (cross F D B)).
      { unfold t. apply rmin_list_le. unfold rooms. simpl.
        right. right. right. right. right. right. right. left. reflexivity. }
      assert (RFDC : t <= seg_room (cross F D X) (cross F D C)).
      { unfold t. apply rmin_list_le. unfold rooms. simpl.
        right. right. right. right. right. right. right. right. left. reflexivity. }
      set (P := convex_combination X A t).
      set (Q := convex_combination X B t).
      set (Rc := convex_combination X C t).
      assert (XinA : in_tri A B C X).
      { apply (proj1 (tri_slack_hull A B C X HA)). repeat split; apply Rlt_le; assumption. }
      assert (XinD : in_tri D E F X).
      { apply (proj1 (tri_slack_hull D E F X HB)). repeat split; apply Rlt_le; assumption. }
      assert (PinA : in_tri A B C P).
      { unfold P. apply in_tri_hull3. apply in_hull_conv.
        - apply in_tri_hull3. exact XinA.
        - apply in_tri_hull3. apply vertex_in_tri. simpl. left. reflexivity.
        - split; assumption. }
      assert (QinA : in_tri A B C Q).
      { unfold Q. apply in_tri_hull3. apply in_hull_conv.
        - apply in_tri_hull3. exact XinA.
        - apply in_tri_hull3. apply vertex_in_tri. simpl. right. left. reflexivity.
        - split; assumption. }
      assert (RinA : in_tri A B C Rc).
      { unfold Rc. apply in_tri_hull3. apply in_hull_conv.
        - apply in_tri_hull3. exact XinA.
        - apply in_tri_hull3. apply vertex_in_tri. simpl. right. right. left. reflexivity.
        - split; assumption. }
      assert (PinD : in_tri D E F P).
      { unfold P. apply nudge_closed; try assumption. }
      assert (QinD : in_tri D E F Q).
      { unfold Q. apply nudge_closed; try assumption. }
      assert (RinD : in_tri D E F Rc).
      { unfold Rc. apply nudge_closed; try assumption. }
      assert (HP : in_hull K P).
      { apply tri_inter_correct; try assumption. split; assumption. }
      assert (HQ : in_hull K Q).
      { apply tri_inter_correct; try assumption. split; assumption. }
      assert (HR : in_hull K Rc).
      { apply tri_inter_correct; try assumption. split; assumption. }
      assert (Hc : cross P Q Rc = t * t * cross A B C).
      { unfold P, Q, Rc. apply cross_nudge. }
      assert (Hpos : 0 < cross P Q Rc).
      { rewrite Hc. apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; exact Ht | exact HA]. }
      assert (Hz : cross P Q Rc = 0).
      { apply flat_hull with (poly := K); try assumption. symmetry. exact Heq. }
      apply (Rlt_not_eq 0 (cross P Q Rc) Hpos). symmetry. exact Hz.
  - intros Harea.
    set (K := tri_inter A B C D E F).
    assert (HsK : convex_supports K) by (apply tri_inter_supports; exact HA).
    destruct (area_pos_triple K HsK Harea) as [o [p [q [Ho [Hp [Hq Hc]]]]]].
    set (G := centroid3 o p q).
    assert (Eo : in_tri A B C o /\ in_tri D E F o).
    { apply tri_inter_correct; try assumption. apply in_hull_in. exact Ho. }
    assert (Ep : in_tri A B C p /\ in_tri D E F p).
    { apply tri_inter_correct; try assumption. apply in_hull_in. exact Hp. }
    assert (Eq : in_tri A B C q /\ in_tri D E F q).
    { apply tri_inter_correct; try assumption. apply in_hull_in. exact Hq. }
    destruct Eo as [EoA EoD]. destruct Ep as [EpA EpD]. destruct Eq as [EqA EqD].
    exists G. split.
    + unfold G. apply tri_open_centroid; assumption.
    + unfold G. apply tri_open_centroid; assumption.
Qed.

Definition ii_entry (A B C D E F : Point) : DimValue :=
  if Rlt_dec 0 (poly_area2 (tri_inter A B C D E F)) then Dim2 else DimF.

(* -------------------------------------------------------------------------- *)
(* A closed outer edge of either triangle keeps the interiors apart.          *)
(* The converse uses the same clip: no outer edge, so the interiors meet.     *)
(* -------------------------------------------------------------------------- *)

Definition outer3 (p q a b c : Point) : Prop :=
  cross p q a <= 0 /\ cross p q b <= 0 /\ cross p q c <= 0.

Definition some_outer (A B C D E F : Point) : Prop :=
  outer3 A B D E F \/ outer3 B C D E F \/ outer3 C A D E F \/
  outer3 D E A B C \/ outer3 E F A B C \/ outer3 F D A B C.

Lemma cross_tri_le : forall p q a b c X,
  cross p q a <= 0 -> cross p q b <= 0 -> cross p q c <= 0 ->
  in_tri a b c X ->
  cross p q X <= 0.
Proof.
  intros p q a b c X Ha Hb Hc [u [v [w [Hu [Hv [Hw [Hs Hx]]]]]]].
  rewrite Hx. rewrite (cross_bary3 p q a b c u v w Hs).
  assert (H1 : u * cross p q a <= 0).
  { replace 0 with (u * 0) by ring. apply Rmult_le_compat_l; lra. }
  assert (H2 : v * cross p q b <= 0).
  { replace 0 with (v * 0) by ring. apply Rmult_le_compat_l; lra. }
  assert (H3 : w * cross p q c <= 0).
  { replace 0 with (w * 0) by ring. apply Rmult_le_compat_l; lra. }
  lra.
Qed.

Lemma tri_open_closed : forall A B C X,
  0 < cross A B C -> tri_open A B C X -> in_tri A B C X.
Proof.
  intros A B C X Hd [Hab [Hbc Hca]].
  apply (proj1 (tri_slack_hull A B C X Hd)).
  repeat split; apply Rlt_le; assumption.
Qed.

Lemma outer3_disjoint : forall p q r a b c,
  0 < cross p q r ->
  0 < cross a b c ->
  outer3 p q a b c ->
  ~ exists X, tri_open p q r X /\ tri_open a b c X.
Proof.
  intros p q r a b c Hp Ha [H1 [H2 H3]] [X [HXp HXa]].
  destruct HXp as [Hpq _].
  assert (Hin : in_tri a b c X) by (apply tri_open_closed; assumption).
  assert (Hle : cross p q X <= 0) by (apply cross_tri_le with (a := a) (b := b) (c := c); assumption).
  lra.
Qed.

Lemma sep_nb_A : forall A B C P Q,
  cross P Q A * cross A B C =
    - (cross A B P * cross C A Q - cross A B Q * cross C A P).
Proof.
  intros A B C P Q. unfold cross.
  destruct A, B, C, P, Q. simpl. ring.
Qed.

Lemma sep_nb_B : forall A B C P Q,
  cross P Q B * cross A B C =
    - (cross A B P * cross C A Q - cross A B Q * cross C A P
       + cross A B C * (cross A B Q - cross A B P)).
Proof.
  intros A B C P Q. unfold cross.
  destruct A, B, C, P, Q. simpl. ring.
Qed.

Lemma sep_nb_C : forall A B C P Q,
  cross P Q C * cross A B C =
    - (cross A B P * cross C A Q - cross A B Q * cross C A P
       + cross A B C * (cross C A P - cross C A Q)).
Proof.
  intros A B C P Q. unfold cross.
  destruct A, B, C, P, Q. simpl. ring.
Qed.

Lemma nb_outer : forall A B C P Q,
  0 < cross A B C ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  0 < cross C A P ->
  0 <= cross A B P * cross C A Q - cross A B Q * cross C A P ->
  outer3 P Q A B C.
Proof.
  intros A B C P Q Hd HpN HqP HpB Hnb.
  set (Nb := cross A B P * cross C A Q - cross A B Q * cross C A P) in *.
  assert (HbQ : cross C A Q < 0).
  { destruct (Rle_dec 0 (cross C A Q)) as [Hq|Hq].
    - assert (Hpos : 0 <= ((- cross A B P) * cross C A Q)).
      { apply Rmult_le_pos; lra. }
      assert (Hleft : cross A B P * cross C A Q <= 0).
      { assert (E : cross A B P * cross C A Q
                    + (- cross A B P) * cross C A Q = 0) by ring.
        lra. }
      assert (Hright : 0 < cross A B Q * cross C A P).
      { apply Rmult_lt_0_compat; assumption. }
      unfold Nb in Hnb. lra.
    - apply Rnot_le_lt. exact Hq. }
  assert (HgapB : 0 < cross C A P - cross C A Q) by lra.
  assert (HgapC : 0 < cross A B Q - cross A B P) by lra.
  assert (HA : cross P Q A * cross A B C = - Nb) by (apply sep_nb_A).
  assert (HB : cross P Q B * cross A B C = - (Nb + cross A B C * (cross A B Q - cross A B P))).
  { rewrite sep_nb_B. unfold Nb. ring. }
  assert (HC : cross P Q C * cross A B C = - (Nb + cross A B C * (cross C A P - cross C A Q))).
  { rewrite sep_nb_C. unfold Nb. ring. }
  assert (HAp : Nb + cross A B C * (cross A B Q - cross A B P) > 0).
  { apply Rplus_le_lt_0_compat; [exact Hnb |]. apply Rmult_lt_0_compat; assumption. }
  assert (HCp : Nb + cross A B C * (cross C A P - cross C A Q) > 0).
  { apply Rplus_le_lt_0_compat; [exact Hnb |]. apply Rmult_lt_0_compat; assumption. }
  repeat split.
  - apply Rmult_le_reg_r with (r := cross A B C); [exact Hd |].
    rewrite HA. lra.
  - apply Rmult_le_reg_r with (r := cross A B C); [exact Hd |].
    rewrite HB. lra.
  - apply Rmult_le_reg_r with (r := cross A B C); [exact Hd |].
    rewrite HC. lra.
Qed.

Lemma meet_contained : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  in_tri A B C D -> in_tri A B C E -> in_tri A B C F ->
  tri_open A B C (centroid3 D E F) /\ tri_open D E F (centroid3 D E F).
Proof.
  intros A B C D E F HA HB HD HE HF. split.
  - apply tri_open_centroid; assumption.
  - apply tri_open_centroid; try assumption.
    + apply vertex_in_tri. simpl. left. reflexivity.
    + apply vertex_in_tri. simpl. right. left. reflexivity.
    + apply vertex_in_tri. simpl. right. right. left. reflexivity.
Qed.

Lemma slack_pos_room : forall sx sg t,
  0 < sx -> 0 <= t -> t < seg_room sx sg ->
  0 < (1 - t) * sx + t * sg.
Proof.
  intros sx sg t Hs Ht0 Ht. unfold seg_room in Ht.
  destruct (Rle_dec 0 (sg - sx)) as [Hg|Hg].
  - replace ((1 - t) * sx + t * sg) with (sx + t * (sg - sx)) by ring.
    assert (0 <= t * (sg - sx)) by (apply Rmult_le_pos; lra).
    lra.
  - apply Rnot_le_lt in Hg.
    assert (Hd : 0 < sx - sg) by lra.
    assert (Hnz : sx - sg <> 0).
    { apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
    replace ((1 - t) * sx + t * sg)
      with ((sx - sg) * (sx / (sx - sg) - t)) by (field; exact Hnz).
    apply Rmult_lt_0_compat; lra.
Qed.

Lemma tri_vertex_slack : forall A B C,
  cross A B A = 0 /\ cross B C A = cross A B C /\ cross C A A = 0.
Proof.
  intros A B C. repeat split.
  - apply cross_third_eq_first.
  - rewrite <- cross_cycle. reflexivity.
  - apply cross_third_eq_second.
Qed.

Lemma slack_mix_pos : forall sV sG t,
  0 <= sV -> 0 < sG -> 0 < t -> t <= 1 ->
  0 < (1 - t) * sV + t * sG.
Proof.
  intros sV sG t Hv Hg Ht0 Ht1.
  assert (H1 : 0 <= (1 - t) * sV) by (apply Rmult_le_pos; lra).
  assert (H2 : 0 < t * sG) by (apply Rmult_lt_0_compat; assumption).
  lra.
Qed.

Lemma own_centroid_open : forall A B C,
  0 < cross A B C -> tri_open A B C (centroid3 A B C).
Proof.
  intros A B C Hd.
  apply tri_open_centroid; try assumption.
  - apply vertex_in_tri. simpl. left. reflexivity.
  - apply vertex_in_tri. simpl. right. left. reflexivity.
  - apply vertex_in_tri. simpl. right. right. left. reflexivity.
Qed.

Lemma meet_vertex : forall A B C D E F V,
  0 < cross A B C -> 0 < cross D E F ->
  In V [D; E; F] ->
  tri_open A B C V ->
  exists X, tri_open A B C X /\ tri_open D E F X.
Proof.
  intros A B C D E F V HA HB Hin HV.
  set (G := centroid3 D E F).
  assert (HG : tri_open D E F G) by (unfold G; apply own_centroid_open; exact HB).
  destruct HV as [Hab [Hbc Hca]].
  destruct HG as [Gab [Gbc Gca]].
  assert (Vin : in_tri D E F V) by (apply vertex_in_tri; exact Hin).
  assert (SV : 0 <= cross D E V /\ 0 <= cross E F V /\ 0 <= cross F D V).
  { apply (proj2 (tri_slack_hull D E F V HB)). exact Vin. }
  destruct SV as [SVde [SVef SVfd]].
  set (rooms :=
    [ seg_room (cross A B V) (cross A B G);
      seg_room (cross B C V) (cross B C G);
      seg_room (cross C A V) (cross C A G) ]).
  set (t := rmin_list rooms).
  assert (Ht : 0 < t).
  { unfold t, rooms. apply rmin_list_pos. intros s Hs. simpl in Hs.
    destruct Hs as [<-|[<-|[<-|[]]]].
    - apply seg_room_pos. exact Hab.
    - apply seg_room_pos. exact Hbc.
    - apply seg_room_pos. exact Hca. }
  assert (Ht1 : t <= 1 / 2) by (unfold t; apply rmin_list_half).
  assert (Ht0 : 0 < t) by exact Ht.
  assert (RAB : t <= seg_room (cross A B V) (cross A B G)).
  { unfold t. apply rmin_list_le. unfold rooms. simpl. left. reflexivity. }
  assert (RBC : t <= seg_room (cross B C V) (cross B C G)).
  { unfold t. apply rmin_list_le. unfold rooms. simpl. right. left. reflexivity. }
  assert (RCA : t <= seg_room (cross C A V) (cross C A G)).
  { unfold t. apply rmin_list_le. unfold rooms. simpl. right. right. left. reflexivity. }
  (* Half the bound is strictly below every room and at most 1/4. *)
  set (u := t / 2).
  assert (Hu : 0 < u) by (unfold u; lra).
  assert (Hu1 : u <= 1) by (unfold u; lra).
  assert (HuAB : u < seg_room (cross A B V) (cross A B G)).
  { unfold u. assert (t / 2 < t) by lra.
    apply Rlt_le_trans with (r2 := t); assumption. }
  assert (HuBC : u < seg_room (cross B C V) (cross B C G)).
  { unfold u. apply Rlt_le_trans with (r2 := t); [lra | exact RBC]. }
  assert (HuCA : u < seg_room (cross C A V) (cross C A G)).
  { unfold u. apply Rlt_le_trans with (r2 := t); [lra | exact RCA]. }
  set (X := convex_combination V G u).
  exists X. split.
  - unfold X. repeat split; rewrite cross_combo.
    + apply slack_pos_room; [exact Hab | lra | exact HuAB].
    + apply slack_pos_room; [exact Hbc | lra | exact HuBC].
    + apply slack_pos_room; [exact Hca | lra | exact HuCA].
  - unfold X. repeat split; rewrite cross_combo.
    + apply slack_mix_pos; [exact SVde | exact Gab | exact Hu | exact Hu1].
    + apply slack_mix_pos; [exact SVef | exact Gbc | exact Hu | exact Hu1].
    + apply slack_mix_pos; [exact SVfd | exact Gca | exact Hu | exact Hu1].
Qed.

Lemma some_outer_disjoint : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  some_outer A B C D E F ->
  ~ exists X, tri_open A B C X /\ tri_open D E F X.
Proof.
  intros A B C D E F HA HB H [X [HXA HXB]].
  destruct H as [H|[H|[H|[H|[H|H]]]]].
  - apply (outer3_disjoint A B C D E F HA HB H). exists X. split; assumption.
  - apply (outer3_disjoint B C A D E F).
    + rewrite <- cross_cycle. exact HA.
    + exact HB.
    + exact H.
    + exists X. split; [destruct HXA as [Hab [Hbc Hca]]; repeat split; assumption | exact HXB].
  - apply (outer3_disjoint C A B D E F).
    + rewrite <- cross_cycle2. exact HA.
    + exact HB.
    + exact H.
    + exists X. split; [destruct HXA as [Hab [Hbc Hca]]; repeat split; assumption | exact HXB].
  - apply (outer3_disjoint D E F A B C HB HA H). exists X. split; assumption.
  - apply (outer3_disjoint E F D A B C).
    + rewrite <- cross_cycle. exact HB.
    + exact HA.
    + exact H.
    + exists X. split; [destruct HXB as [Hde [Hef Hfd]]; repeat split; assumption | exact HXA].
  - apply (outer3_disjoint F D E A B C).
    + rewrite <- cross_cycle2. exact HB.
    + exact HA.
    + exact H.
    + exists X. split; [destruct HXB as [Hde [Hef Hfd]]; repeat split; assumption | exact HXA].
Qed.

Lemma ii_entry_dim2_witness : forall A B C D E F X,
  0 < cross A B C -> 0 < cross D E F ->
  tri_open A B C X -> tri_open D E F X ->
  ii_entry A B C D E F = Dim2.
Proof.
  intros A B C D E F X HA HB HXA HXB. unfold ii_entry.
  destruct (Rlt_dec 0 (poly_area2 (tri_inter A B C D E F))) as [_|Hn].
  - reflexivity.
  - exfalso. apply Hn. apply ii_nonempty_iff; try assumption.
    exists X. split; assumption.
Qed.

Lemma ii_entry_dimF_outer : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  some_outer A B C D E F ->
  ii_entry A B C D E F = DimF.
Proof.
  intros A B C D E F HA HB Ho. unfold ii_entry.
  destruct (Rlt_dec 0 (poly_area2 (tri_inter A B C D E F))) as [Hp|].
  - exfalso.
    apply (some_outer_disjoint A B C D E F HA HB Ho).
    apply ii_nonempty_iff; assumption.
  - reflexivity.
Qed.

Definition strict3 (p q a b c : Point) : Prop :=
  cross p q a < 0 /\ cross p q b < 0 /\ cross p q c < 0.

Lemma strict3_outer : forall p q a b c,
  strict3 p q a b c -> outer3 p q a b c.
Proof.
  intros p q a b c [Ha [Hb Hc]]. repeat split; apply Rlt_le; assumption.
Qed.

Lemma ii_entry_separated : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  (strict3 A B D E F \/ strict3 B C D E F \/ strict3 C A D E F \/
   strict3 D E A B C \/ strict3 E F A B C \/ strict3 F D A B C) ->
  ii_entry A B C D E F = DimF.
Proof.
  intros A B C D E F HA HB H.
  apply ii_entry_dimF_outer; try assumption.
  destruct H as [H|[H|[H|[H|[H|H]]]]];
    [left | right; left | right; right; left | right; right; right; left
     | right; right; right; right; left | right; right; right; right; right];
    apply strict3_outer; exact H.
Qed.

(* Concrete pairs. Swaps are the same witness with the triangles exchanged. *)

Definition fxA0 : Point := mkPoint 0 0.
Definition fxA1 : Point := mkPoint 1 0.
Definition fxA2 : Point := mkPoint 0 1.

Lemma ii_entry_agrees_concrete :
  ii_entry fxA0 fxA1 fxA2
    (mkPoint (1/4) (1/4)) (mkPoint (5/4) (1/4)) (mkPoint (1/4) (5/4)) = Dim2 /\
  ii_entry (mkPoint (1/4) (1/4)) (mkPoint (5/4) (1/4)) (mkPoint (1/4) (5/4))
    fxA0 fxA1 fxA2 = Dim2 /\
  ii_entry (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 3 0) (mkPoint 2 1) = Dim2 /\
  ii_entry (mkPoint 1 0) (mkPoint 3 0) (mkPoint 2 1)
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1) = Dim2 /\
  ii_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = Dim2 /\
  ii_entry (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = Dim2 /\
  ii_entry (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4)) = Dim2 /\
  ii_entry (mkPoint 1 0) (mkPoint (5/4) (1/4)) (mkPoint (3/4) (1/4))
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1) = Dim2 /\
  ii_entry fxA0 fxA1 fxA2 (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) = DimF /\
  ii_entry fxA0 fxA1 fxA2 (mkPoint 1 0) (mkPoint 1 1) (mkPoint 0 1) = DimF /\
  ii_entry (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 0 (-2)) = DimF.
Proof.
  repeat split.
  - apply ii_entry_dim2_witness with (X := mkPoint (2/5) (2/5));
      unfold tri_open, cross, fxA0, fxA1, fxA2; simpl; lra.
  - apply ii_entry_dim2_witness with (X := mkPoint (2/5) (2/5));
      unfold tri_open, cross, fxA0, fxA1, fxA2; simpl; lra.
  - apply ii_entry_dim2_witness with (X := mkPoint (3/2) (1/20));
      unfold tri_open, cross; simpl; lra.
  - apply ii_entry_dim2_witness with (X := mkPoint (3/2) (1/20));
      unfold tri_open, cross; simpl; lra.
  - apply ii_entry_dim2_witness with (X := mkPoint 1 (1/2));
      unfold tri_open, cross; simpl; lra.
  - apply ii_entry_dim2_witness with (X := mkPoint 1 (1/2));
      unfold tri_open, cross; simpl; lra.
  - apply ii_entry_dim2_witness with (X := mkPoint 1 (1/6));
      unfold tri_open, cross; simpl; lra.
  - apply ii_entry_dim2_witness with (X := mkPoint 1 (1/6));
      unfold tri_open, cross; simpl; lra.
  - apply ii_entry_dimF_outer; unfold cross, fxA0, fxA1, fxA2, some_outer, outer3; simpl.
    + lra.
    + lra.
    + right. left. repeat split; unfold cross; simpl; lra.
  - apply ii_entry_dimF_outer; unfold cross, fxA0, fxA1, fxA2, some_outer, outer3; simpl.
    + lra.
    + lra.
    + right. left. repeat split; unfold cross; simpl; lra.
  - apply ii_entry_dimF_outer; unfold some_outer, outer3, cross; simpl.
    + lra.
    + lra.
    + left. repeat split; unfold cross; simpl; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* A proper edge crossing puts a point in both open triangles.                *)
(* -------------------------------------------------------------------------- *)

Definition pdot (p q : Point) : R := px p * px q + py p * py q.

Definition left_n (p q : Point) : Point :=
  mkPoint (- (py q - py p)) (px q - px p).

Definition shift (h v : Point) (t : R) : Point :=
  mkPoint (px h + t * px v) (py h + t * py v).

Lemma pdot_left_sq : forall p q,
  pdot (left_n p q) (left_n p q) = dist_sq p q.
Proof. intros. unfold pdot, left_n, dist_sq. simpl. ring. Qed.

Lemma cross_shift : forall p q h v t,
  cross p q (shift h v t) = cross p q h + t * pdot (left_n p q) v.
Proof.
  intros. unfold cross, shift, pdot, left_n.
  destruct p, q, h, v. simpl. ring.
Qed.

Lemma sum_sqr_zero : forall x y, x * x + y * y = 0 -> x = 0 /\ y = 0.
Proof.
  intros x y H.
  assert (Hx : 0 <= x * x) by apply sqr_nonneg.
  assert (Hy : 0 <= y * y) by apply sqr_nonneg.
  assert (Ex : x * x = 0) by lra.
  assert (Ey : y * y = 0) by lra.
  split; apply sqr_eq_zero; assumption.
Qed.

Lemma dist_sq_pos_points : forall p q,
  points_distinct p q -> 0 < dist_sq p q.
Proof.
  intros p q Hdis.
  pose proof (dist_sq_nonneg p q) as Hnn.
  destruct (Req_dec (dist_sq p q) 0) as [Hz|Hnz].
  - exfalso. unfold dist_sq in Hz.
    destruct (sum_sqr_zero _ _ Hz) as [Hx Hy].
    destruct Hdis as [Hpx|Hpy].
    + apply Hpx. lra.
    + apply Hpy. lra.
  - lra.
Qed.

Lemma edge_len_pos : forall A B C,
  0 < cross A B C -> 0 < dist_sq A B.
Proof.
  intros A B C H. apply dist_sq_pos_points. apply (ccw_edge_distinct A B C H).
Qed.

Lemma opp_div_open : forall fa fb,
  fa * fb < 0 ->
  fa - fb <> 0 /\ 0 < fa / (fa - fb) /\ fa / (fa - fb) < 1.
Proof.
  intros fa fb Hneg.
  destruct (Rlt_dec 0 fa) as [Hfa|Hfa].
  - assert (Hfb : fb < 0).
    { destruct (Rle_dec 0 fb) as [Hfb|Hfb].
      - assert (0 <= fa * fb) by (apply Rmult_le_pos; lra). lra.
      - apply Rnot_le_lt. exact Hfb. }
    assert (Hd : 0 < fa - fb) by lra.
    split; [lra |]. split.
    + unfold Rdiv. apply Rmult_lt_0_compat; [exact Hfa | apply Rinv_0_lt_compat; exact Hd].
    + apply Rmult_lt_reg_r with (r := fa - fb); [exact Hd |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; lra.
  - apply Rnot_lt_le in Hfa.
    assert (Hfa0 : fa < 0).
    { destruct (Req_dec fa 0) as [Z|]; [| lra]. subst fa. lra. }
    assert (Hfb : 0 < fb).
    { destruct (Rle_dec fb 0) as [Hfb|Hfb].
      - assert (E : fa * fb = (- fa) * (- fb)) by ring.
        assert (0 <= (- fa) * (- fb)) by (apply Rmult_le_pos; lra).
        lra.
      - apply Rnot_le_lt. exact Hfb. }
    assert (Hd : 0 < - (fa - fb)) by lra.
    assert (Heq : fa / (fa - fb) = (- fa) / (- (fa - fb))) by (field; lra).
    split; [lra |]. rewrite Heq. split.
    + unfold Rdiv. apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hd].
    + apply Rmult_lt_reg_r with (r := - (fa - fb)); [exact Hd |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; lra.
Qed.

Lemma line_hit_comm : forall A B D E,
  cross A B D <> cross A B E ->
  cross D E A <> cross D E B ->
  line_hit A B D E = line_hit D E A B.
Proof.
  intros A B D E HAB HDE.
  destruct A as [ax ay], B as [bx by_], D as [dx dy], E as [ex ey].
  unfold line_hit, cross in *. simpl in *. f_equal; field; lra.
Qed.

Lemma proper_open_point : forall A B D E,
  cross A B D * cross A B E < 0 ->
  cross D E A * cross D E B < 0 ->
  exists h t s,
    0 < t < 1 /\ 0 < s < 1 /\
    h = convex_combination A B t /\
    h = convex_combination D E s.
Proof.
  intros A B D E HAB HDE.
  destruct (opp_div_open (cross D E A) (cross D E B) HDE)
    as [Hne1 [Ht0 Ht1]].
  destruct (opp_div_open (cross A B D) (cross A B E) HAB)
    as [Hne2 [Hs0 Hs1]].
  set (t := cross D E A / (cross D E A - cross D E B)).
  set (s := cross A B D / (cross A B D - cross A B E)).
  set (h := line_hit A B D E).
  assert (Ecomm : h = line_hit D E A B).
  { unfold h. apply line_hit_comm; lra. }
  exists h, t, s. split; [split; assumption |]. split; [split; assumption |]. split.
  - unfold h, t. rewrite line_hit_combo. reflexivity.
  - rewrite Ecomm. unfold s. rewrite line_hit_combo. reflexivity.
Qed.

Lemma open_seg_slacks : forall A B C X t,
  0 < cross A B C ->
  0 < t < 1 ->
  X = convex_combination A B t ->
  cross A B X = 0 /\ 0 < cross B C X /\ 0 < cross C A X.
Proof.
  intros A B C X t Hd Ht Hx. destruct Ht as [Ht0 Ht1]. subst X.
  assert (Hab : cross A B (convex_combination A B t) = 0).
  { rewrite cross_combo. rewrite cross_third_eq_first.
    assert (E : cross A B B = 0) by (unfold cross; ring). rewrite E. ring. }
  assert (Hbc : cross B C (convex_combination A B t) = (1 - t) * cross A B C).
  { rewrite cross_combo. rewrite cross_third_eq_first.
    assert (EA : cross B C A = cross A B C) by (rewrite <- cross_cycle; reflexivity).
    rewrite EA. ring. }
  assert (Hca : cross C A (convex_combination A B t) = t * cross A B C).
  { rewrite cross_combo. rewrite cross_third_eq_second.
    assert (EB : cross C A B = cross A B C) by (rewrite <- cross_cycle2; reflexivity).
    rewrite EB. ring. }
  repeat split.
  - exact Hab.
  - rewrite Hbc. apply Rmult_lt_0_compat; lra.
  - rewrite Hca. apply Rmult_lt_0_compat; assumption.
Qed.

Lemma lagrange_dot : forall n1 n2,
  pdot n1 n1 * pdot n2 n2 - pdot n1 n2 * pdot n1 n2 =
    (px n1 * py n2 - py n1 * px n2) * (px n1 * py n2 - py n1 * px n2).
Proof. intros. unfold pdot. destruct n1, n2. simpl. ring. Qed.

Lemma left_cross_diff : forall A B D E,
  px (left_n A B) * py (left_n D E) - py (left_n A B) * px (left_n D E) =
    cross A B E - cross A B D.
Proof. intros. unfold left_n, cross. destruct A, B, D, E. simpl. ring. Qed.

Lemma sqr_pos_neq : forall x, x <> 0 -> 0 < x * x.
Proof.
  intros x Hx.
  pose proof (sqr_nonneg x) as Hnn.
  destruct (Req_dec (x * x) 0) as [Hz|Hnz].
  - apply sqr_eq_zero in Hz. contradiction.
  - lra.
Qed.

Lemma inward_pair : forall n1 n2,
  0 < pdot n1 n1 ->
  0 < pdot n2 n2 ->
  px n1 * py n2 - py n1 * px n2 <> 0 ->
  exists v, 0 < pdot n1 v /\ 0 < pdot n2 v.
Proof.
  intros n1 n2 Ha Hb Hcr.
  set (d := pdot n1 n2).
  set (a2 := pdot n1 n1).
  set (b2 := pdot n2 n2).
  destruct (Rle_dec 0 d) as [Hd|Hd].
  - set (v := mkPoint (px n1 + px n2) (py n1 + py n2)).
    exists v. split.
    + assert (E : pdot n1 v = a2 + d).
      { unfold v, a2, d, pdot. destruct n1 as [x1 y1], n2 as [x2 y2]. simpl. ring. }
      rewrite E. apply Rplus_lt_le_0_compat; [unfold a2; exact Ha | exact Hd].
    + assert (E : pdot n2 v = b2 + d).
      { unfold v, b2, d, pdot. destruct n1 as [x1 y1], n2 as [x2 y2]. simpl. ring. }
      rewrite E. apply Rplus_lt_le_0_compat; [unfold b2; exact Hb | exact Hd].
  - apply Rnot_le_lt in Hd. unfold d in Hd.
    assert (Hdisc : 0 < pdot n1 n1 * pdot n2 n2 - pdot n1 n2 * pdot n1 n2).
    { rewrite lagrange_dot. apply sqr_pos_neq. exact Hcr. }
    assert (Ea : pdot n1 n1 <> 0).
    { intro Hz. rewrite Hz in Ha. apply (Rlt_irrefl 0). exact Ha. }
    assert (Ed : - pdot n1 n2 <> 0).
    { intro Hz. apply (f_equal Ropp) in Hz.
      rewrite Ropp_involutive, Ropp_0 in Hz. rewrite Hz in Hd.
      exact (Rlt_irrefl 0 Hd). }
    set (alpha := (pdot n1 n1 * pdot n2 n2 + pdot n1 n2 * pdot n1 n2)
                    / (2 * pdot n1 n1 * (- pdot n1 n2))).
    set (v := mkPoint (alpha * px n1 + px n2) (alpha * py n1 + py n2)).
    assert (E1 : pdot n1 v =
        (pdot n1 n1 * pdot n2 n2 - pdot n1 n2 * pdot n1 n2)
          / (2 * (- pdot n1 n2))).
    { assert (Ev : pdot n1 v = alpha * pdot n1 n1 + pdot n1 n2).
      { unfold v, pdot. destruct n1 as [x1 y1], n2 as [x2 y2]. simpl. ring. }
      rewrite Ev. unfold alpha. field. split.
      - intro Hz. rewrite Hz in Hd. exact (Rlt_irrefl 0 Hd).
      - exact Ea. }
    assert (E2 : pdot n2 v =
        (pdot n1 n1 * pdot n2 n2 - pdot n1 n2 * pdot n1 n2)
          / (2 * pdot n1 n1)).
    { assert (Ev : pdot n2 v = alpha * pdot n1 n2 + pdot n2 n2).
      { unfold v, pdot. destruct n1 as [x1 y1], n2 as [x2 y2]. simpl. ring. }
      rewrite Ev. unfold alpha. field. split.
      - exact Ea.
      - intro Hz. rewrite Hz in Hd. exact (Rlt_irrefl 0 Hd). }
    exists v. split.
    + rewrite E1. apply Rdiv_lt_0_compat.
      * exact Hdisc.
      * lra.
    + rewrite E2. apply Rdiv_lt_0_compat; [exact Hdisc |].
      apply Rmult_lt_0_compat; [lra | exact Ha].
Qed.

Definition step_room (s0 ds : R) : R :=
  if Rle_dec 0 ds then 1 else s0 / (2 * (- ds)).

Lemma step_room_pos : forall s0 ds, 0 < s0 -> 0 < step_room s0 ds.
Proof.
  intros s0 ds Hs. unfold step_room.
  destruct (Rle_dec 0 ds) as [_|Hds].
  - lra.
  - apply Rnot_le_lt in Hds.
    apply Rdiv_lt_0_compat; lra.
Qed.

Lemma slack_step_pos : forall s0 ds t,
  0 < s0 -> 0 < t -> t <= step_room s0 ds -> 0 < s0 + t * ds.
Proof.
  intros s0 ds t Hs Ht Hle. unfold step_room in Hle.
  destruct (Rle_dec 0 ds) as [Hd|Hd].
  - assert (0 <= t * ds) by (apply Rmult_le_pos; lra). lra.
  - apply Rnot_le_lt in Hd.
    assert (Hden : 0 < 2 * (- ds)) by lra.
    assert (Ht2 : t * (2 * (- ds)) <= s0).
    { apply Rmult_le_reg_r with (r := / (2 * (- ds))).
      - apply Rinv_0_lt_compat. exact Hden.
      - replace (t * (2 * (- ds)) * / (2 * (- ds))) with t by (field; lra).
        unfold Rdiv in Hle. exact Hle. }
    assert (E : t * (2 * (- ds)) = 2 * (t * (- ds))) by ring.
    lra.
Qed.

Lemma wedge_edges : forall A B C D E F,
  0 < cross A B C ->
  0 < cross D E F ->
  cross A B D * cross A B E < 0 ->
  cross D E A * cross D E B < 0 ->
  exists X, tri_open A B C X /\ tri_open D E F X.
Proof.
  intros A B C D E F HA HB HAB HDE.
  destruct (proper_open_point A B D E HAB HDE) as [h [t [s [Ht [Hs [HtX HsX]]]]]].
  destruct (open_seg_slacks A B C h t HA Ht HtX) as [Hab0 [Hbc0 Hca0]].
  destruct (open_seg_slacks D E F h s HB Hs HsX) as [Hde0 [Hef0 Hfd0]].
  set (n1 := left_n A B).
  set (n2 := left_n D E).
  assert (Hn1 : 0 < pdot n1 n1).
  { unfold n1. rewrite pdot_left_sq. apply edge_len_pos with (C := C). exact HA. }
  assert (Hn2 : 0 < pdot n2 n2).
  { unfold n2. rewrite pdot_left_sq. apply edge_len_pos with (C := F). exact HB. }
  assert (Hcr : px n1 * py n2 - py n1 * px n2 <> 0).
  { unfold n1, n2. rewrite left_cross_diff. intro Heq.
    assert (Heq' : cross A B E = cross A B D) by lra.
    assert (Hsq : cross A B D * cross A B E = cross A B D * cross A B D)
      by (rewrite Heq'; ring).
    assert (0 <= cross A B D * cross A B D) by apply sqr_nonneg.
    lra. }
  destruct (inward_pair n1 n2 Hn1 Hn2 Hcr) as [v [Hv1 Hv2]].
  set (dBC := pdot (left_n B C) v).
  set (dCA := pdot (left_n C A) v).
  set (dEF := pdot (left_n E F) v).
  set (dFD := pdot (left_n F D) v).
  set (r1 := step_room (cross B C h) dBC).
  set (r2 := step_room (cross C A h) dCA).
  set (r3 := step_room (cross E F h) dEF).
  set (r4 := step_room (cross F D h) dFD).
  set (u := Rmin (Rmin r1 r2) (Rmin r3 r4)).
  assert (Hu : 0 < u).
  { unfold u. apply Rmin_pos; apply Rmin_pos; apply step_room_pos; assumption. }
  assert (Hu1 : u <= r1).
  { unfold u. apply Rle_trans with (r2 := Rmin r1 r2); apply Rmin_l. }
  assert (Hu2 : u <= r2).
  { unfold u. apply Rle_trans with (r2 := Rmin r1 r2).
    - apply Rmin_l.
    - apply Rmin_r. }
  assert (Hu3 : u <= r3).
  { unfold u. apply Rle_trans with (r2 := Rmin r3 r4).
    - apply Rmin_r.
    - apply Rmin_l. }
  assert (Hu4 : u <= r4).
  { unfold u. apply Rle_trans with (r2 := Rmin r3 r4); apply Rmin_r. }
  set (X := shift h v u).
  exists X. split; unfold X, tri_open.
  - repeat split.
    + rewrite cross_shift. unfold n1 in Hv1.
      assert (Heq1 : cross A B h + u * pdot (left_n A B) v = u * pdot n1 v).
      { unfold n1. rewrite Hab0. ring. }
      rewrite Heq1. apply Rmult_lt_0_compat; assumption.
    + rewrite cross_shift. unfold r1, dBC in Hu1.
      apply slack_step_pos; assumption.
    + rewrite cross_shift. unfold r2, dCA in Hu2.
      apply slack_step_pos; assumption.
  - repeat split.
    + rewrite cross_shift. unfold n2 in Hv2.
      assert (Heq2 : cross D E h + u * pdot (left_n D E) v = u * pdot n2 v).
      { unfold n2. rewrite Hde0. ring. }
      rewrite Heq2. apply Rmult_lt_0_compat; assumption.
    + rewrite cross_shift. unfold r3, dEF in Hu3.
      apply slack_step_pos; assumption.
    + rewrite cross_shift. unfold r4, dFD in Hu4.
      apply slack_step_pos; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* A CCW edge that straddles a cap separates, or the interiors meet.          *)
(* -------------------------------------------------------------------------- *)

Lemma na_nb_sum : forall A B C P Q,
  (cross A B P * cross B C Q - cross A B Q * cross B C P)
  + (cross A B P * cross C A Q - cross A B Q * cross C A P)
  = cross A B C * (cross A B P - cross A B Q).
Proof. intros. unfold cross. destruct A, B, C, P, Q. simpl. ring. Qed.

Lemma cross_pq_B_na : forall A B C P Q,
  cross P Q B * cross A B C =
    cross A B P * cross B C Q - cross A B Q * cross B C P.
Proof. intros. unfold cross. destruct A, B, C, P, Q. simpl. ring. Qed.

Lemma pqc_na : forall A B C P Q,
  cross P Q C * cross A B C =
    (cross A B P * cross B C Q - cross A B Q * cross B C P)
    + cross A B C * (cross B C P - cross B C Q).
Proof. intros. unfold cross. destruct A, B, C, P, Q. simpl. ring. Qed.

Lemma au_aq_id : forall A B C P Q U,
  (cross B C U - cross B C Q) * (cross A B Q - cross A B P)
  = cross P Q U * cross A B C
    + (cross A B Q - cross A B U) * (cross B C P - cross B C Q).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma qu_B_minus_A : forall A B C Q U,
  cross Q U B * cross A B C =
    cross Q U A * cross A B C
    + cross A B C * (cross A B Q - cross A B U).
Proof. intros. unfold cross. destruct A, B, C, Q, U. simpl. ring. Qed.

Lemma qu_C_minus_B : forall A B C Q U,
  cross Q U C * cross A B C =
    cross Q U B * cross A B C
    + cross A B C * (cross B C Q - cross B C U).
Proof. intros. unfold cross. destruct A, B, C, Q, U. simpl. ring. Qed.

Lemma up_b_from_qu : forall A B C P Q U,
  cross U P B * cross A B Q * cross A B C
  + cross A B P * cross Q U B * cross A B C
  + cross A B U
      * (cross A B P * cross B C Q - cross A B Q * cross B C P) = 0.
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma aq_neg : forall A B C P Q,
  cross A B P < 0 ->
  0 < cross A B Q ->
  0 < cross B C P ->
  0 <= cross A B P * cross B C Q - cross A B Q * cross B C P ->
  cross B C Q < 0.
Proof.
  intros A B C P Q Hp Hq Ha Hna.
  destruct (Rle_dec 0 (cross B C Q)) as [Hq0|Hq0].
  - assert (Hle : cross A B P * cross B C Q <= cross A B P * 0).
    { apply Rmult_le_compat_neg_l; lra. }
    assert (Hpos : 0 < cross A B Q * cross B C P).
    { apply Rmult_lt_0_compat; assumption. }
    replace (cross A B P * 0) with 0 in Hle by ring. lra.
  - apply Rnot_le_lt. exact Hq0.
Qed.

Lemma au_gt_aq : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < cross A B Q ->
  cross A B U < cross A B Q ->
  cross B C Q < cross B C P ->
  cross B C Q < cross B C U.
Proof.
  intros A B C P Q U Hd Hs Hc HcU Ha.
  assert (Hid := au_aq_id A B C P Q U).
  assert (Hden : 0 < cross A B Q - cross A B P) by lra.
  apply Rmult_lt_reg_r with (r := cross A B Q - cross A B P).
  - exact Hden.
  - assert (Hpos : 0 < cross P Q U * cross A B C
                     + (cross A B Q - cross A B U)
                       * (cross B C P - cross B C Q)).
    { apply Rplus_lt_0_compat.
      - apply Rmult_lt_0_compat; assumption.
      - apply Rmult_lt_0_compat; lra. }
    rewrite <- Hid in Hpos. lra.
Qed.

Lemma touch_line_open : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross P Q B = 0 ->
  0 < cross Q U B ->
  0 < cross U P B ->
  0 < cross P Q A ->
  0 < cross P Q C ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U HA HB HpqB HquB HupB HpqA HpqC.
  set (G := centroid3 A B C).
  assert (HG : tri_open A B C G) by (unfold G; apply own_centroid_open; exact HA).
  destruct HG as [GAB [GBC GCA]].
  assert (HPQG : 0 < cross P Q G).
  { unfold G. rewrite cross_centroid3. rewrite HpqB.
    assert (Hs : 0 < cross P Q A + 0 + cross P Q C) by lra.
    unfold Rdiv. apply Rmult_lt_0_compat; [exact Hs | apply Rinv_0_lt_compat; lra]. }
  set (rQU := seg_room (cross Q U B) (cross Q U G)).
  set (rUP := seg_room (cross U P B) (cross U P G)).
  assert (HrQU : 0 < rQU) by (unfold rQU; apply seg_room_pos; exact HquB).
  assert (HrUP : 0 < rUP) by (unfold rUP; apply seg_room_pos; exact HupB).
  set (u := Rmin (Rmin rQU rUP / 2) (1 / 2)).
  assert (Hu : 0 < u).
  { unfold u. apply Rmin_pos; [ | lra].
    apply Rmult_lt_0_compat; [apply Rmin_pos; assumption | lra]. }
  assert (Hu1 : u <= 1).
  { unfold u. apply Rle_trans with (r2 := 1 / 2); [apply Rmin_r | lra]. }
  assert (Hhalf : 0 < Rmin rQU rUP) by (apply Rmin_pos; assumption).
  assert (HuQU : u < rQU).
  { apply Rlt_le_trans with (r2 := Rmin rQU rUP).
    - apply Rle_lt_trans with (r2 := Rmin rQU rUP / 2).
      + unfold u. apply Rmin_l.
      + apply Rmult_lt_reg_r with (r := 2); [lra |].
        field_simplify; lra.
    - apply Rmin_l. }
  assert (HuUP : u < rUP).
  { apply Rlt_le_trans with (r2 := Rmin rQU rUP).
    - apply Rle_lt_trans with (r2 := Rmin rQU rUP / 2).
      + unfold u. apply Rmin_l.
      + apply Rmult_lt_reg_r with (r := 2); [lra |].
        field_simplify; lra.
    - apply Rmin_r. }
  set (X := convex_combination B G u).
  exists X. split.
  - unfold X. repeat split; rewrite cross_combo.
    + replace (cross A B B) with 0 by (symmetry; apply cross_third_eq_second).
      replace ((1 - u) * 0 + u * cross A B G) with (u * cross A B G) by ring.
      apply Rmult_lt_0_compat; assumption.
    + replace (cross B C B) with 0 by (symmetry; apply cross_third_eq_first).
      replace ((1 - u) * 0 + u * cross B C G) with (u * cross B C G) by ring.
      apply Rmult_lt_0_compat; assumption.
    + apply slack_mix_pos.
      * rewrite <- cross_cycle2. apply Rlt_le. exact HA.
      * exact GCA.
      * exact Hu.
      * exact Hu1.
  - unfold X. repeat split; rewrite cross_combo.
    + rewrite HpqB. replace ((1 - u) * 0 + u * cross P Q G) with (u * cross P Q G) by ring.
      apply Rmult_lt_0_compat; assumption.
    + apply slack_pos_room; [exact HquB | lra | exact HuQU].
    + apply slack_pos_room; [exact HupB | lra | exact HuUP].
Qed.

Lemma na_cap_closed_u : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  cross A B U <= 0 ->
  0 < cross B C P ->
  0 <= cross A B P * cross B C Q - cross A B Q * cross B C P ->
  some_outer A B C P Q U \/ exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu HaP Hna.
  assert (Haq : cross B C Q < 0) by (apply aq_neg with (A := A) (B := B) (C := C) (P := P); assumption).
  assert (Hau : cross B C Q < cross B C U).
  { apply au_gt_aq with (A := A) (B := B) (C := C) (P := P) (Q := Q) (U := U); lra. }
  destruct (Rle_dec (cross Q U B) 0) as [HquB|HquB].
  - left. do 4 right. left. repeat split.
    + apply Rlt_le.
      assert (E := qu_B_minus_A A B C Q U).
      apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      replace (cross Q U A * cross A B C) with
        (cross Q U B * cross A B C
         - cross A B C * (cross A B Q - cross A B U)) by lra.
      assert (0 < cross A B C * (cross A B Q - cross A B U)).
      { apply Rmult_lt_0_compat; lra. }
      assert (Hble : cross Q U B * cross A B C <= 0 * cross A B C).
      { apply Rmult_le_compat_r; lra. }
      replace (0 * cross A B C) with 0 in Hble by ring. lra.
    + apply Rmult_le_reg_r with (r := cross A B C); [exact Hd |].
      replace (0 * cross A B C) with 0 by ring.
      assert (Hble : cross Q U B * cross A B C <= 0 * cross A B C).
      { apply Rmult_le_compat_r; lra. }
      replace (0 * cross A B C) with 0 in Hble by ring. exact Hble.
    + apply Rlt_le.
      assert (E := qu_C_minus_B A B C Q U).
      apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      replace (cross Q U C * cross A B C) with
        (cross Q U B * cross A B C
         + cross A B C * (cross B C Q - cross B C U)) by lra.
      assert (Hneg : cross B C Q - cross B C U < 0) by lra.
      assert (Hmul : cross A B C * (cross B C Q - cross B C U) < cross A B C * 0).
      { apply Rmult_lt_compat_l; [exact Hd | exact Hneg]. }
      replace (cross A B C * 0) with 0 in Hmul by ring.
      assert (Hble : cross Q U B * cross A B C <= 0 * cross A B C).
      { apply Rmult_le_compat_r; lra. }
      replace (0 * cross A B C) with 0 in Hble by ring. lra.
  - apply Rnot_le_lt in HquB.
    assert (HupB : 0 < cross U P B).
    { assert (E := up_b_from_qu A B C P Q U).
      assert (Hrhs : 0 < - cross A B P * cross Q U B * cross A B C
                       + - cross A B U
                         * (cross A B P * cross B C Q - cross A B Q * cross B C P)).
      { apply Rplus_lt_le_0_compat.
        - apply Rmult_lt_0_compat.
          + apply Rmult_lt_0_compat; lra.
          + exact Hd.
        - apply Rmult_le_pos; lra. }
      assert (Hprod : 0 < cross U P B * cross A B Q * cross A B C) by lra.
      apply Rmult_lt_reg_r with (r := cross A B Q * cross A B C).
      - apply Rmult_lt_0_compat; assumption.
      - replace (0 * (cross A B Q * cross A B C)) with 0 by ring.
        replace (cross U P B * (cross A B Q * cross A B C))
          with (cross U P B * cross A B Q * cross A B C) by ring.
        exact Hprod. }
    destruct (Rle_lt_or_eq_dec 0
                (cross A B P * cross B C Q - cross A B Q * cross B C P) Hna)
      as [HnaP|Hna0].
    + right.
      assert (Hopen : tri_open P Q U B).
      { repeat split; try assumption.
        apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
        rewrite cross_pq_B_na. replace (0 * cross A B C) with 0 by ring.
        exact HnaP. }
      destruct (meet_vertex P Q U A B C B Hs Hd
                  (or_intror (or_introl eq_refl)) Hopen) as [X [HXu HXa]].
      exists X. split; assumption.
    + right. apply touch_line_open; try assumption.
      * assert (E0 : cross P Q B * cross A B C = 0).
        { rewrite cross_pq_B_na. rewrite <- Hna0. ring. }
        apply Rmult_eq_reg_l with (r := cross A B C).
        -- replace (cross A B C * cross P Q B)
             with (cross P Q B * cross A B C) by ring.
           replace (cross A B C * 0) with 0 by ring. exact E0.
        -- apply not_eq_sym. apply Rlt_not_eq. exact Hd.
      * assert (EA := sep_nb_A A B C P Q).
        assert (Nb_neg : cross A B P * cross C A Q - cross A B Q * cross C A P < 0).
        { assert (Es := na_nb_sum A B C P Q).
          assert (Hlt : cross A B P - cross A B Q < 0) by lra.
          assert (Hprod : cross A B C * (cross A B P - cross A B Q)
                          < cross A B C * 0).
          { apply Rmult_lt_compat_l; [exact Hd | exact Hlt]. }
          replace (cross A B C * 0) with 0 in Hprod by ring.
          rewrite <- Hna0 in Es. lra. }
        apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
        rewrite EA. replace (0 * cross A B C) with 0 by ring. lra.
      * apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
        rewrite pqc_na. rewrite <- Hna0.
        replace (0 * cross A B C) with 0 by ring.
        assert (Hgap : 0 < cross B C P - cross B C Q) by lra.
        assert (Hmul : 0 < cross A B C * (cross B C P - cross B C Q)).
        {         apply Rmult_lt_0_compat; [exact Hd | exact Hgap]. }
        lra.
Qed.

Lemma gap_cp_cross : forall A B C P U,
  (cross B C U * cross C A P - cross C A U * cross B C P) * cross A B P
  = (cross A B P * cross B C U - cross A B U * cross B C P)
      * (cross A B C - cross A B P)
    + cross B C P * cross A B C * (cross A B U - cross A B P).
Proof. intros. unfold cross. destruct A, B, C, P, U. simpl. ring. Qed.

Lemma cross_up_A : forall A B C P U,
  cross U P A * cross A B C =
    cross A B P * cross C A U - cross A B U * cross C A P.
Proof. intros. unfold cross. destruct A, B, C, P, U. simpl. ring. Qed.

Lemma cross_up_B : forall A B C P U,
  cross U P B * cross A B C =
    - (cross A B P * cross B C U - cross A B U * cross B C P).
Proof. intros. unfold cross. destruct A, B, C, P, U. simpl. ring. Qed.

Lemma cross_up_C : forall A B C P U,
  cross U P C * cross A B C =
    cross B C U * cross C A P - cross C A U * cross B C P.
Proof. intros. unfold cross. destruct A, B, C, P, U. simpl. ring. Qed.

Lemma quA_nb : forall A B C P Q U,
  cross Q U A * cross A B P * cross A B C =
      cross A B U * (cross A B P * cross C A Q - cross A B Q * cross C A P)
    - cross A B Q * (cross A B P * cross C A U - cross A B U * cross C A P).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma prod_neg : forall a b, a < 0 -> 0 < b -> a * b < 0.
Proof.
  intros a b Ha Hb.
  assert (E : a * b < 0 * b) by (apply Rmult_lt_compat_r; assumption).
  replace (0 * b) with 0 in E by ring. exact E.
Qed.

Lemma prod_pos_neg : forall a b, 0 < a -> b < 0 -> a * b < 0.
Proof.
  intros a b Ha Hb.
  assert (E : a * b < a * 0) by (apply Rmult_lt_compat_l; assumption).
  replace (a * 0) with 0 in E by ring. exact E.
Qed.

Lemma wedge_c_succ : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  cross A B P * cross B C Q - cross A B Q * cross B C P < 0 ->
  cross A B P * cross C A Q - cross A B Q * cross C A P < 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hna Hnb.
  apply wedge_edges; try assumption.
  - apply prod_neg; assumption.
  - assert (HA : 0 < cross P Q A).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      rewrite sep_nb_A. replace (0 * cross A B C) with 0 by ring. lra. }
    assert (HB : cross P Q B < 0).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      rewrite cross_pq_B_na. replace (0 * cross A B C) with 0 by ring.
      exact Hna. }
    apply prod_pos_neg; assumption.
Qed.

Lemma up_outer_na : forall A B C P U,
  0 < cross A B C ->
  cross A B P < 0 ->
  cross A B P < cross A B U ->
  0 < cross B C P ->
  0 <= cross A B P * cross B C U - cross A B U * cross B C P ->
  outer3 U P A B C.
Proof.
  intros A B C P U Hd Hp Hlt HaP Hna.
  set (Na := cross A B P * cross B C U - cross A B U * cross B C P) in *.
  set (Gap := cross B C U * cross C A P - cross C A U * cross B C P).
  assert (Hgap : Gap < 0).
  { assert (E := gap_cp_cross A B C P U).
    unfold Na, Gap in E.
    assert (H2 : 0 < cross B C P * cross A B C * (cross A B U - cross A B P)).
    { apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; assumption | lra]. }
    assert (H1a : 0 <= cross A B P * cross B C U - cross A B U * cross B C P)
      by exact Hna.
    assert (H1b : 0 <= cross A B C - cross A B P) by lra.
    assert (H1 : 0 <= (cross A B P * cross B C U - cross A B U * cross B C P)
                   * (cross A B C - cross A B P))
      by (apply Rmult_le_pos; assumption).
    assert (Hprod : 0 < Gap * cross A B P).
    { unfold Gap. rewrite E.
      apply Rplus_le_lt_0_compat; [exact H1 | exact H2]. }
    destruct (Rle_dec 0 Gap) as [Hg|Hg].
    - assert (Hle : cross A B P * Gap <= cross A B P * 0).
      { apply Rmult_le_compat_neg_l; lra. }
      replace (cross A B P * 0) with 0 in Hle by ring.
      assert (Gap * cross A B P = cross A B P * Gap) by ring. lra.
    - apply Rnot_le_lt. exact Hg. }
  assert (Hnb : cross A B P * cross C A U - cross A B U * cross C A P < 0).
  { assert (Es := na_nb_sum A B C P U).
    assert (Hlt' : cross A B P - cross A B U < 0) by lra.
    assert (Hmul : cross A B C * (cross A B P - cross A B U) < 0).
    { assert (E1 : cross A B C * (cross A B P - cross A B U)
                   < cross A B C * 0).
      { apply Rmult_lt_compat_l; [exact Hd | exact Hlt']. }
      replace (cross A B C * 0) with 0 in E1 by ring. exact E1. }
    apply Rplus_lt_reg_l with
      (r := cross A B P * cross B C U - cross A B U * cross B C P).
    replace ((cross A B P * cross B C U - cross A B U * cross B C P) + 0)
      with (cross A B P * cross B C U - cross A B U * cross B C P) by ring.
    rewrite Es.
    apply Rlt_le_trans with (r2 := 0); [exact Hmul | exact Hna]. }
  repeat split.
  - apply Rlt_le.
    apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_A. replace (0 * cross A B C) with 0 by ring. exact Hnb.
  - apply Rmult_le_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_B. replace (0 * cross A B C) with 0 by ring.
    assert (Hle : - Na <= - 0) by (apply Ropp_le_contravar; exact Hna).
    replace (- 0) with 0 in Hle by ring. unfold Na in Hle. exact Hle.
  - apply Rlt_le.
    apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_C. replace (0 * cross A B C) with 0 by ring.
    unfold Gap in Hgap. exact Hgap.
Qed.

Lemma nb_of_sum : forall A B C P Q,
  cross A B P < cross A B Q ->
  0 < cross A B C ->
  0 <= cross A B P * cross B C Q - cross A B Q * cross B C P ->
  cross A B P * cross C A Q - cross A B Q * cross C A P < 0.
Proof.
  intros A B C P Q Hlt Hd Hna.
  assert (Es := na_nb_sum A B C P Q).
  assert (Hmul : cross A B C * (cross A B P - cross A B Q) < 0).
  { assert (Hdiff : cross A B P - cross A B Q < 0) by lra.
    assert (E1 : cross A B C * (cross A B P - cross A B Q)
                 < cross A B C * 0).
    { apply Rmult_lt_compat_l; assumption. }
    replace (cross A B C * 0) with 0 in E1 by ring. exact E1. }
  apply Rplus_lt_reg_l with
    (r := cross A B P * cross B C Q - cross A B Q * cross B C P).
  replace ((cross A B P * cross B C Q - cross A B Q * cross B C P) + 0)
    with (cross A B P * cross B C Q - cross A B Q * cross B C P) by ring.
  rewrite Es.
  apply Rlt_le_trans with (r2 := 0); [exact Hmul | exact Hna].
Qed.

Lemma openA_nbU : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  0 < cross A B U ->
  0 < cross B C P ->
  0 <= cross A B P * cross B C Q - cross A B Q * cross B C P ->
  0 < cross A B P * cross C A U - cross A B U * cross C A P ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu HaP HnaQ HnbU.
  assert (HnbQ : cross A B P * cross C A Q - cross A B Q * cross C A P < 0).
  { apply nb_of_sum; try assumption; lra. }
  assert (HpqA : 0 < cross P Q A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite sep_nb_A. replace (0 * cross A B C) with 0 by ring. lra. }
  assert (HupA : 0 < cross U P A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_A. replace (0 * cross A B C) with 0 by ring. exact HnbU. }
  assert (HquA : 0 < cross Q U A).
  { assert (E := quA_nb A B C P Q U).
    assert (Hleft : cross A B U
                      * (cross A B P * cross C A Q - cross A B Q * cross C A P) < 0).
    { apply prod_pos_neg; assumption. }
    assert (Hnonneg : 0 <= cross A B Q
                        * (cross A B P * cross C A U - cross A B U * cross C A P)).
    { apply Rmult_le_pos; [apply Rlt_le; exact Hq | apply Rlt_le; exact HnbU]. }
    assert (Hneg : - (cross A B Q
                        * (cross A B P * cross C A U - cross A B U * cross C A P)) <= 0).
    { apply Ropp_le_contravar in Hnonneg.
      replace (- 0) with 0 in Hnonneg by ring. exact Hnonneg. }
    assert (Hrhs0 : cross A B U
                      * (cross A B P * cross C A Q - cross A B Q * cross C A P)
                    + - (cross A B Q
                          * (cross A B P * cross C A U
                             - cross A B U * cross C A P)) < 0 + 0).
    { apply Rplus_lt_le_compat; [exact Hleft | exact Hneg]. }
    assert (Hrhs : cross A B U
                     * (cross A B P * cross C A Q - cross A B Q * cross C A P)
                   - cross A B Q
                     * (cross A B P * cross C A U - cross A B U * cross C A P) < 0).
    { replace 0 with (0 + 0) by ring.
      replace (cross A B U
                 * (cross A B P * cross C A Q - cross A B Q * cross C A P)
               - cross A B Q
                 * (cross A B P * cross C A U - cross A B U * cross C A P))
        with (cross A B U
                * (cross A B P * cross C A Q - cross A B Q * cross C A P)
              + - (cross A B Q
                     * (cross A B P * cross C A U - cross A B U * cross C A P)))
        by ring.
      exact Hrhs0. }
    assert (Hprod : cross Q U A * cross A B P * cross A B C < 0).
    { rewrite E. exact Hrhs. }
    assert (Hden : cross A B P * cross A B C < 0) by (apply prod_neg; assumption).
    destruct (Rle_dec (cross Q U A) 0) as [Hqle|Hqlt].
    - assert (Hge : cross A B P * cross A B C * 0 <=
                    cross A B P * cross A B C * cross Q U A).
      { apply Rmult_le_compat_neg_l; [apply Rlt_le; exact Hden | exact Hqle]. }
      replace (cross A B P * cross A B C * 0) with 0 in Hge by ring.
      assert (Heq : cross Q U A * cross A B P * cross A B C =
                    cross A B P * cross A B C * cross Q U A) by ring.
      rewrite Heq in Hprod.
      exfalso. apply (Rlt_not_le _ _ Hprod). exact Hge.
    - apply Rnot_le_lt. exact Hqlt. }
  destruct (meet_vertex P Q U A B C A Hs Hd
              (or_introl eq_refl)
              (conj HpqA (conj HquA HupA))) as [X [HXu HXa]].
  exists X. split; assumption.
Qed.

Lemma wedge_c_pred : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B U ->
  cross A B P * cross B C U - cross A B U * cross B C P < 0 ->
  cross A B P * cross C A U - cross A B U * cross C A P < 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hu Hna Hnb.
  assert (Hmeet : exists X, tri_open A B C X /\ tri_open U P Q X).
  { apply wedge_edges; try assumption.
    - rewrite cross_cycle. exact Hs.
    - apply prod_pos_neg; [exact Hu | exact Hp].
    - assert (HA : cross U P A < 0).
      { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
        rewrite cross_up_A. replace (0 * cross A B C) with 0 by ring.
        exact Hnb. }
      assert (HB : 0 < cross U P B).
      { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
        rewrite cross_up_B. replace (0 * cross A B C) with 0 by ring.
        assert (Hopp : - 0 <
            - (cross A B P * cross B C U - cross A B U * cross B C P)).
        { apply Ropp_lt_contravar. exact Hna. }
        replace (- 0) with 0 in Hopp by ring. exact Hopp. }
      apply prod_neg; assumption. }
  destruct Hmeet as [X [HXa HXu]].
  destruct HXu as [Hup [Hpq Hqu]].
  exists X. split; [exact HXa | repeat split; assumption].
Qed.

Lemma some_outer_ab : forall A B C P Q U,
  outer3 A B P Q U -> some_outer A B C P Q U.
Proof. intros. left. assumption. Qed.

Lemma some_outer_pq : forall A B C P Q U,
  outer3 P Q A B C -> some_outer A B C P Q U.
Proof. intros. do 3 right. left. assumption. Qed.

Lemma some_outer_qu : forall A B C P Q U,
  outer3 Q U A B C -> some_outer A B C P Q U.
Proof. intros. do 4 right. left. assumption. Qed.

Lemma some_outer_up : forall A B C P Q U,
  outer3 U P A B C -> some_outer A B C P Q U.
Proof. intros. do 5 right. assumption. Qed.

Lemma qua_bb : forall A B C Q U,
  cross Q U A * cross A B C =
    cross C A Q * cross A B U - cross A B Q * cross C A U.
Proof. intros. unfold cross. destruct A, B, C, Q, U. simpl. ring. Qed.

Lemma qu_b_gap : forall A B C Q U,
  (cross Q U B - cross Q U A) * cross A B C =
    cross A B C * (cross A B Q - cross A B U).
Proof. intros. unfold cross. destruct A, B, C, Q, U. simpl. ring. Qed.

Lemma qu_c_gap : forall A B C Q U,
  (cross Q U C - cross Q U A) * cross A B C =
    cross A B C * (cross C A U - cross C A Q).
Proof. intros. unfold cross. destruct A, B, C, Q, U. simpl. ring. Qed.

Lemma s_qua_id : forall A B C P Q U,
  cross P Q U * cross A B C =
    cross Q U A * cross A B C
    - cross A B P * (cross C A Q - cross C A U)
    + cross C A P * (cross A B Q - cross A B U).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma b_gap_from_s : forall A B C P Q U,
  - cross A B P * (cross C A Q - cross C A U) =
    cross P Q U * cross A B C
    - cross Q U A * cross A B C
    + cross C A P * (cross A B U - cross A B Q).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma pqa_cu_id : forall A B C P Q U,
  (cross C A P * cross A B Q - cross A B P * cross C A Q) * cross A B U =
    - cross A B P
        * (cross C A Q * cross A B U - cross A B Q * cross C A U)
    - cross A B Q
        * (cross A B P * cross C A U - cross A B U * cross C A P).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma bU_of_nb : forall A B C P U,
  cross A B P < 0 ->
  0 < cross A B U ->
  0 < cross C A P ->
  0 <= cross A B P * cross C A U - cross A B U * cross C A P ->
  cross C A U < 0.
Proof.
  intros A B C P U Hp Hu Hb Hnb.
  destruct (Rle_dec 0 (cross C A U)) as [Hge|Hlt].
  - assert (Hle : cross A B P * cross C A U <= cross A B P * 0).
    { apply Rmult_le_compat_neg_l; lra. }
    replace (cross A B P * 0) with 0 in Hle by ring.
    assert (Hpos : 0 < cross A B U * cross C A P).
    { apply Rmult_lt_0_compat; assumption. }
    assert (Hdiff : cross A B P * cross C A U < cross A B U * cross C A P).
    { apply Rle_lt_trans with (r2 := 0); assumption. }
    assert (Hsum : cross A B P * cross C A U
                   + - (cross A B U * cross C A P)
                   < cross A B U * cross C A P
                   + - (cross A B U * cross C A P)).
    { apply Rplus_lt_compat_r. exact Hdiff. }
    replace (cross A B U * cross C A P + - (cross A B U * cross C A P))
      with 0 in Hsum by ring.
    replace (cross A B P * cross C A U + - (cross A B U * cross C A P))
      with (cross A B P * cross C A U - cross A B U * cross C A P)
      in Hsum by ring.
    exfalso. apply (Rlt_not_le _ _ Hsum). exact Hnb.
  - apply Rnot_le_lt. exact Hlt.
Qed.

(* Vertex A of ABC lies on line UP, strictly left of PQ and QU, and B is
   strictly left of UP. A short step toward B, with a smaller step toward C,
   lands in both open triangles. *)
Lemma touch_up_A : forall A B C P Q U,
  0 < cross A B C ->
  cross U P A = 0 ->
  0 < cross P Q A ->
  0 < cross Q U A ->
  0 < cross U P B ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd HupA HpqA HquA HupB.
  set (alpha := Rmin (step_room (cross U P B) (cross U P C)) (1 / 2)).
  assert (Halpha : 0 < alpha).
  { unfold alpha. apply Rmin_pos; [| lra].
    apply step_room_pos. exact HupB. }
  assert (HalphaR : alpha <= step_room (cross U P B) (cross U P C)).
  { unfold alpha. apply Rmin_l. }
  assert (HupMix : 0 < cross U P B + alpha * cross U P C).
  { apply slack_step_pos; assumption. }
  set (dsPQ := cross P Q B + alpha * cross P Q C
               - (1 + alpha) * cross P Q A).
  set (dsQU := cross Q U B + alpha * cross Q U C
               - (1 + alpha) * cross Q U A).
  assert (Hden : 0 < 1 + alpha) by lra.
  assert (Hdenz : 1 + alpha <> 0).
  { apply not_eq_sym. apply Rlt_not_eq. exact Hden. }
  set (cap := 1 / (2 * (1 + alpha))).
  assert (Hcap : 0 < cap).
  { unfold cap. apply Rdiv_lt_0_compat; [lra |].
    apply Rmult_lt_0_compat; lra. }
  set (t := Rmin (Rmin (step_room (cross P Q A) dsPQ)
                       (step_room (cross Q U A) dsQU)) cap).
  assert (Ht : 0 < t).
  { unfold t. apply Rmin_pos; [| exact Hcap].
    apply Rmin_pos; apply step_room_pos; assumption. }
  assert (HtPQ : t <= step_room (cross P Q A) dsPQ).
  { unfold t. apply Rle_trans with
      (r2 := Rmin (step_room (cross P Q A) dsPQ)
                  (step_room (cross Q U A) dsQU)).
    - apply Rmin_l.
    - apply Rmin_l. }
  assert (HtQU : t <= step_room (cross Q U A) dsQU).
  { unfold t. apply Rle_trans with
      (r2 := Rmin (step_room (cross P Q A) dsPQ)
                  (step_room (cross Q U A) dsQU)).
    - apply Rmin_l.
    - apply Rmin_r. }
  assert (Htcap : t <= cap) by (unfold t; apply Rmin_r).
  assert (Hhalf : t * (1 + alpha) <= 1 / 2).
  { apply Rle_trans with (r2 := cap * (1 + alpha)).
    - apply Rmult_le_compat_r; [apply Rlt_le; exact Hden | exact Htcap].
    - unfold cap. field_simplify; lra. }
  set (s := alpha * t).
  assert (Hs0 : 0 < s) by (unfold s; apply Rmult_lt_0_compat; assumption).
  assert (Hrest : 0 < 1 - t - s).
  { unfold s. assert (t * (1 + alpha) <= 1 / 2) by exact Hhalf. lra. }
  set (X := bary3 (1 - t - s) t s A B C).
  assert (Hw : (1 - t - s) + t + s = 1) by ring.
  exists X. split.
  - repeat split.
    + unfold X. rewrite (cross_bary3 A B A B C (1 - t - s) t s Hw).
      replace (cross A B A) with 0 by (symmetry; apply cross_third_eq_first).
      replace (cross A B B) with 0 by (symmetry; apply cross_third_eq_second).
      replace ((1 - t - s) * 0 + t * 0 + s * cross A B C)
        with (s * cross A B C) by ring.
      apply Rmult_lt_0_compat; assumption.
    + unfold X. rewrite (cross_bary3 B C A B C (1 - t - s) t s Hw).
      replace (cross B C A) with (cross A B C) by apply cross_cycle.
      replace (cross B C B) with 0 by (symmetry; apply cross_third_eq_first).
      replace (cross B C C) with 0 by (symmetry; apply cross_third_eq_second).
      replace ((1 - t - s) * cross A B C + t * 0 + s * 0)
        with ((1 - t - s) * cross A B C) by ring.
      apply Rmult_lt_0_compat; assumption.
    + unfold X. rewrite (cross_bary3 C A A B C (1 - t - s) t s Hw).
      replace (cross C A A) with 0 by (symmetry; apply cross_third_eq_second).
      replace (cross C A B) with (cross A B C) by apply cross_cycle2.
      replace (cross C A C) with 0 by (symmetry; apply cross_third_eq_first).
      replace ((1 - t - s) * 0 + t * cross A B C + s * 0)
        with (t * cross A B C) by ring.
      apply Rmult_lt_0_compat; assumption.
  - repeat split.
    + unfold X. rewrite (cross_bary3 P Q A B C (1 - t - s) t s Hw).
      replace ((1 - t - s) * cross P Q A + t * cross P Q B + s * cross P Q C)
        with (cross P Q A + t * dsPQ) by (unfold s, dsPQ; ring).
      apply slack_step_pos; assumption.
    + unfold X. rewrite (cross_bary3 Q U A B C (1 - t - s) t s Hw).
      replace ((1 - t - s) * cross Q U A + t * cross Q U B + s * cross Q U C)
        with (cross Q U A + t * dsQU) by (unfold s, dsQU; ring).
      apply slack_step_pos; assumption.
    + unfold X. rewrite (cross_bary3 U P A B C (1 - t - s) t s Hw).
      rewrite HupA.
      replace ((1 - t - s) * 0 + t * cross U P B + s * cross U P C)
        with (t * (cross U P B + alpha * cross U P C)) by (unfold s; ring).
      apply Rmult_lt_0_compat; assumption.
Qed.

Lemma pqa_prod_cu : forall A B C P Q U,
  (cross P Q A * cross A B C) * cross A B U =
    (- cross A B P) * (cross Q U A * cross A B C)
    + (- cross A B Q)
        * (cross A B P * cross C A U - cross A B U * cross C A P).
Proof. intros. unfold cross. destruct A, B, C, P, Q, U. simpl. ring. Qed.

Lemma qu_outer_qua : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  cross A B Q <= 0 ->
  0 < cross A B U ->
  0 < cross C A P ->
  cross Q U A <= 0 ->
  outer3 Q U A B C.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu HbP Hqa.
  assert (HquB : cross Q U B < 0).
  { assert (Hlt : (cross Q U B - cross Q U A) * cross A B C
                  < 0 * cross A B C).
    { rewrite qu_b_gap. replace (0 * cross A B C) with 0 by ring.
      apply prod_pos_neg; [exact Hd | lra]. }
    apply Rmult_lt_reg_r in Hlt; [| exact Hd]. lra. }
  assert (Hbg : 0 < cross C A Q - cross C A U).
  { assert (HcP : 0 < - cross A B P) by lra.
    assert (Hpos : 0 < - cross A B P * (cross C A Q - cross C A U)).
    { rewrite b_gap_from_s.
      assert (H1 : 0 < cross P Q U * cross A B C).
      { apply Rmult_lt_0_compat; assumption. }
      assert (Hnqa : 0 <= - cross Q U A).
      { assert (Hopp : - 0 <= - cross Q U A).
        { apply Ropp_le_contravar. exact Hqa. }
        replace (- 0) with 0 in Hopp by ring. exact Hopp. }
      assert (H2 : 0 <= - cross Q U A * cross A B C).
      { apply Rmult_le_pos; [exact Hnqa | apply Rlt_le; exact Hd]. }
      assert (H3 : 0 < cross C A P * (cross A B U - cross A B Q)).
      { apply Rmult_lt_0_compat; [exact HbP | lra]. }
      assert (H13 : 0 < cross P Q U * cross A B C
                      + cross C A P * (cross A B U - cross A B Q)).
      { apply Rplus_lt_0_compat; assumption. }
      assert (Hsum : 0 < cross P Q U * cross A B C
                        + cross C A P * (cross A B U - cross A B Q)
                        + - cross Q U A * cross A B C).
      { apply Rplus_lt_le_0_compat; [exact H13 | exact H2]. }
      replace (cross P Q U * cross A B C
               - cross Q U A * cross A B C
               + cross C A P * (cross A B U - cross A B Q))
        with (cross P Q U * cross A B C
              + cross C A P * (cross A B U - cross A B Q)
              + - cross Q U A * cross A B C) by ring.
      exact Hsum. }
    apply Rmult_lt_reg_l with (r := - cross A B P); [exact HcP |].
    replace ((- cross A B P) * 0) with 0 by ring.
    exact Hpos. }
  assert (HquC : cross Q U C < 0).
  { assert (Hlt : (cross Q U C - cross Q U A) * cross A B C
                  < 0 * cross A B C).
    { rewrite qu_c_gap. replace (0 * cross A B C) with 0 by ring.
      apply prod_pos_neg; [exact Hd | lra]. }
    apply Rmult_lt_reg_r in Hlt; [| exact Hd]. lra. }
  repeat split; [exact Hqa | apply Rlt_le; exact HquB | apply Rlt_le; exact HquC].
Qed.

Lemma pqa_of_qua : forall A B C P Q U,
  0 < cross A B C ->
  cross A B P < 0 ->
  cross A B Q <= 0 ->
  0 < cross A B U ->
  0 < cross Q U A ->
  0 <= cross A B P * cross C A U - cross A B U * cross C A P ->
  0 < cross P Q A.
Proof.
  intros A B C P Q U Hd Hp Hq Hu Hqa Hnb.
  assert (E := pqa_prod_cu A B C P Q U).
  assert (H1 : 0 < (- cross A B P) * (cross Q U A * cross A B C)).
  { apply Rmult_lt_0_compat; [lra | apply Rmult_lt_0_compat; assumption]. }
  assert (Hnq : 0 <= - cross A B Q).
  { assert (Hopp : - 0 <= - cross A B Q).
    { apply Ropp_le_contravar. exact Hq. }
    replace (- 0) with 0 in Hopp by ring. exact Hopp. }
  assert (H2 : 0 <= (- cross A B Q)
                 * (cross A B P * cross C A U - cross A B U * cross C A P)).
  { apply Rmult_le_pos; assumption. }
  assert (Hsum : 0 < (- cross A B P) * (cross Q U A * cross A B C)
                    + (- cross A B Q)
                      * (cross A B P * cross C A U
                         - cross A B U * cross C A P)).
  { apply Rplus_lt_le_0_compat; assumption. }
  assert (Hprod : 0 < (cross P Q A * cross A B C) * cross A B U).
  { rewrite E. exact Hsum. }
  apply Rmult_lt_reg_r with (r := cross A B U); [exact Hu |].
  replace (0 * cross A B U) with 0 by ring.
  apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
  replace (0 * cross A B C) with 0 by ring.
  replace ((cross P Q A * cross A B U) * cross A B C)
    with ((cross P Q A * cross A B C) * cross A B U) by ring.
  exact Hprod.
Qed.

Lemma succ_line_A : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  0 < cross A B U ->
  0 < cross B C P ->
  0 <= cross A B P * cross B C Q - cross A B Q * cross B C P ->
  cross A B P * cross B C U - cross A B U * cross B C P < 0 ->
  cross A B P * cross C A U - cross A B U * cross C A P = 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu HaP Hna HnaU Hnb0.
  assert (HnbQ : cross A B P * cross C A Q - cross A B Q * cross C A P < 0).
  { apply nb_of_sum; try assumption; lra. }
  assert (HpqA : 0 < cross P Q A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite sep_nb_A. replace (0 * cross A B C) with 0 by ring. lra. }
  assert (HquA : 0 < cross Q U A).
  { assert (E := quA_nb A B C P Q U).
    rewrite Hnb0 in E.
    assert (Hrhs : cross A B U
                     * (cross A B P * cross C A Q - cross A B Q * cross C A P)
                   < 0).
    { apply prod_pos_neg; assumption. }
    assert (E0 : cross Q U A * cross A B P * cross A B C < 0).
    { rewrite E.
      replace (cross A B U
                 * (cross A B P * cross C A Q - cross A B Q * cross C A P)
               - cross A B Q * 0)
        with (cross A B U
                * (cross A B P * cross C A Q - cross A B Q * cross C A P))
        by ring.
      exact Hrhs. }
    assert (Hden : cross A B P * cross A B C < 0) by (apply prod_neg; assumption).
    destruct (Rle_dec (cross Q U A) 0) as [Hqle|Hqlt].
    - assert (Hge : cross A B P * cross A B C * 0 <=
                    cross A B P * cross A B C * cross Q U A).
      { apply Rmult_le_compat_neg_l; [apply Rlt_le; exact Hden | exact Hqle]. }
      replace (cross A B P * cross A B C * 0) with 0 in Hge by ring.
      assert (Heqa : cross Q U A * cross A B P * cross A B C =
                     cross A B P * cross A B C * cross Q U A) by ring.
      rewrite Heqa in E0.
      exfalso. apply (Rlt_not_le _ _ E0). exact Hge.
    - apply Rnot_le_lt. exact Hqlt. }
  assert (HupA : cross U P A = 0).
  { assert (E0 : cross U P A * cross A B C = 0).
    { rewrite cross_up_A. exact Hnb0. }
    apply Rmult_eq_reg_l with (r := cross A B C).
    - replace (cross A B C * cross U P A)
        with (cross U P A * cross A B C) by ring.
      replace (cross A B C * 0) with 0 by ring. exact E0.
    - apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
  assert (HupB : 0 < cross U P B).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_B. replace (0 * cross A B C) with 0 by ring.
    assert (Hopp : - 0 <
        - (cross A B P * cross B C U - cross A B U * cross B C P)).
    { apply Ropp_lt_contravar. exact HnaU. }
    replace (- 0) with 0 in Hopp by ring. exact Hopp. }
  apply touch_up_A; assumption.
Qed.

Lemma cap_succ : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross A B Q ->
  0 < cross B C P ->
  0 < cross C A P ->
  some_outer A B C P Q U \/ exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq HaP HbP.
  destruct (Rle_dec 0 (cross A B P * cross B C Q - cross A B Q * cross B C P))
    as [Hna|Hna].
  - destruct (Rle_dec (cross A B U) 0) as [Hu|Hu].
    + apply na_cap_closed_u; assumption.
    + apply Rnot_le_lt in Hu.
      destruct (Rle_dec 0
                  (cross A B P * cross B C U - cross A B U * cross B C P))
        as [HnaU|HnaU].
      * left. apply some_outer_up.
        apply up_outer_na; try assumption; lra.
      * apply Rnot_le_lt in HnaU.
        destruct (Rle_dec 0
                    (cross A B P * cross C A U - cross A B U * cross C A P))
          as [HnbU|HnbU].
        -- destruct (Rle_lt_or_eq_dec 0
                       (cross A B P * cross C A U
                        - cross A B U * cross C A P) HnbU) as [Hgt|Heq].
           ++ right. apply openA_nbU; try assumption; lra.
           ++ right. apply succ_line_A; try assumption.
              symmetry. exact Heq.
        -- apply Rnot_le_lt in HnbU.
           right. apply wedge_c_pred; assumption.
  - apply Rnot_le_lt in Hna.
    destruct (Rle_dec 0 (cross A B P * cross C A Q - cross A B Q * cross C A P))
      as [Hnb|Hnb].
    + left. apply some_outer_pq. apply nb_outer; assumption.
    + apply Rnot_le_lt in Hnb.
      right. apply wedge_c_succ; assumption.
Qed.

Lemma cap_pred : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  cross A B Q <= 0 ->
  0 < cross A B U ->
  0 < cross B C P ->
  0 < cross C A P ->
  some_outer A B C P Q U \/ exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu HaP HbP.
  destruct (Rle_dec 0 (cross A B P * cross B C U - cross A B U * cross B C P))
    as [HnaU|HnaU].
  - left. apply some_outer_up. apply up_outer_na; try assumption; lra.
  - apply Rnot_le_lt in HnaU.
    destruct (Rle_dec 0 (cross A B P * cross C A U - cross A B U * cross C A P))
      as [HnbU|HnbU].
    + destruct (Rle_dec (cross Q U A) 0) as [Hqa|Hqa].
      * left. apply some_outer_qu. apply (qu_outer_qua A B C P Q U); assumption.
      * apply Rnot_le_lt in Hqa.
        assert (HpqA : 0 < cross P Q A).
        { apply (pqa_of_qua A B C P Q U); assumption. }
        destruct (Rle_lt_or_eq_dec 0
                    (cross A B P * cross C A U - cross A B U * cross C A P)
                    HnbU) as [Hgt|Heq].
        -- right.
           assert (HupA : 0 < cross U P A).
           { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
             rewrite cross_up_A. replace (0 * cross A B C) with 0 by ring.
             exact Hgt. }
           destruct (meet_vertex P Q U A B C A Hs Hd
                      (or_introl eq_refl)
                      (conj HpqA (conj Hqa HupA))) as [X [HXu HXa]].
           exists X. split; assumption.
        -- right.
           assert (HupA0 : cross U P A = 0).
           { assert (E0 : cross U P A * cross A B C = 0).
             { rewrite cross_up_A. symmetry. exact Heq. }
             apply Rmult_eq_reg_l with (r := cross A B C).
             - replace (cross A B C * cross U P A)
                 with (cross U P A * cross A B C) by ring.
               replace (cross A B C * 0) with 0 by ring. exact E0.
             - apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
           assert (HupB : 0 < cross U P B).
           { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
             rewrite cross_up_B. replace (0 * cross A B C) with 0 by ring.
             assert (Hopp : - 0 <
                 - (cross A B P * cross B C U - cross A B U * cross B C P)).
             { apply Ropp_lt_contravar. exact HnaU. }
             replace (- 0) with 0 in Hopp by ring. exact Hopp. }
           apply touch_up_A; assumption.
    + apply Rnot_le_lt in HnbU.
      right. apply wedge_c_pred; assumption.
Qed.

Lemma cap_ab : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross P Q U ->
  cross A B P < 0 ->
  0 < cross B C P ->
  0 < cross C A P ->
  some_outer A B C P Q U \/ exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp HaP HbP.
  destruct (Rlt_dec 0 (cross A B Q)) as [Hq|Hq].
  - apply cap_succ; assumption.
  - apply Rnot_lt_le in Hq.
    destruct (Rlt_dec 0 (cross A B U)) as [Hu|Hu].
    + apply cap_pred; assumption.
    + apply Rnot_lt_le in Hu.
      left. apply some_outer_ab. repeat split.
      * apply Rlt_le. exact Hp.
      * exact Hq.
      * exact Hu.
Qed.

Lemma tri_open_rot : forall A B C X,
  tri_open A B C X -> tri_open B C A X.
Proof.
  intros A B C X [Hab [Hbc Hca]]. repeat split; assumption.
Qed.

Lemma tri_open_rot2 : forall A B C X,
  tri_open A B C X -> tri_open C A B X.
Proof.
  intros A B C X [Hab [Hbc Hca]]. repeat split; assumption.
Qed.

Lemma outer3_rot : forall p q a b c,
  outer3 p q a b c -> outer3 p q b c a.
Proof.
  intros p q a b c [H1 [H2 H3]]. repeat split; assumption.
Qed.

Lemma outer3_rot2 : forall p q a b c,
  outer3 p q a b c -> outer3 p q c a b.
Proof.
  intros p q a b c [H1 [H2 H3]]. repeat split; assumption.
Qed.

Lemma some_outer_swap : forall A B C P Q U,
  some_outer P Q U A B C -> some_outer A B C P Q U.
Proof.
  intros A B C P Q U [H|[H|[H|[H|[H|H]]]]].
  - do 3 right. left. exact H.
  - do 4 right. left. exact H.
  - do 5 right. exact H.
  - left. exact H.
  - right. left. exact H.
  - do 2 right. left. exact H.
Qed.

Lemma meet_swap : forall A B C P Q U,
  (exists X, tri_open P Q U X /\ tri_open A B C X) ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U [X [Hs Ht]]. exists X. split; assumption.
Qed.

Lemma meet_rot_T : forall A B C P Q U,
  (exists X, tri_open B C A X /\ tri_open P Q U X) ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U [X [Ht Hs]].
  exists X. split; [| exact Hs].
  destruct Ht as [Hbc [Hca Hab]]. repeat split; assumption.
Qed.

Lemma meet_rot_S : forall A B C P Q U,
  (exists X, tri_open A B C X /\ tri_open Q U P X) ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U [X [Ht Hs]].
  exists X. split; [exact Ht |].
  destruct Hs as [Hqu [Hup Hpq]]. repeat split; assumption.
Qed.

(* P sits in the exterior corner at A, Q at B, U at C. Vertex A of ABC
   is then strictly inside triangle PQU. *)
Lemma surround_open_A : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross B C P -> cross C A P < 0 -> cross A B P < 0 ->
  cross B C Q < 0 -> 0 < cross C A Q -> cross A B Q < 0 ->
  cross B C U < 0 -> cross C A U < 0 -> 0 < cross A B U ->
  tri_open P Q U A.
Proof.
  intros A B C P Q U Hd HaP HbP HcP HaQ HbQ HcQ HaU HbU HcU.
  repeat split.
  - apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite sep_nb_A. replace (0 * cross A B C) with 0 by ring.
    assert (H1 : 0 < (- cross A B P) * cross C A Q).
    { apply Rmult_lt_0_compat; lra. }
    assert (Hnq : 0 < - cross A B Q) by lra.
    assert (Hnp : 0 < - cross C A P) by lra.
    assert (H2 : 0 < (- cross A B Q) * (- cross C A P)).
    { apply Rmult_lt_0_compat; assumption. }
    replace ((- cross A B Q) * (- cross C A P))
      with (cross A B Q * cross C A P) in H2 by ring.
    assert (Hsum : 0 < (- cross A B P) * cross C A Q
                      + cross A B Q * cross C A P).
    { apply Rplus_lt_0_compat; assumption. }
    replace (- (cross A B P * cross C A Q - cross A B Q * cross C A P))
      with ((- cross A B P) * cross C A Q + cross A B Q * cross C A P)
      by ring.
    exact Hsum.
  - apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite qua_bb. replace (0 * cross A B C) with 0 by ring.
    assert (Eb := cross_sum3 A B C Q).
    assert (Eu := cross_sum3 A B C U).
    set (ap := - cross B C Q).
    set (cq := - cross A B Q).
    set (au := - cross B C U).
    set (bu := - cross C A U).
    assert (Hap : 0 < ap) by (unfold ap; lra).
    assert (Hcq : 0 < cq) by (unfold cq; lra).
    assert (Hau : 0 < au) by (unfold au; lra).
    assert (Hbu : 0 < bu) by (unfold bu; lra).
    assert (EbQ : cross C A Q = cross A B C + ap + cq).
    { unfold ap, cq.
      replace (cross A B C - cross B C Q - cross A B Q)
        with (cross A B C + - cross B C Q + - cross A B Q) by ring.
      assert (Esum : cross A B Q + cross B C Q + cross C A Q = cross A B C)
        by exact Eb.
      lra. }
    assert (EcU : cross A B U = cross A B C + au + bu).
    { unfold au, bu.
      assert (Esum : cross A B U + cross B C U + cross C A U = cross A B C)
        by exact Eu.
      lra. }
    rewrite EbQ, EcU.
    assert (Hdd : 0 < cross A B C * cross A B C).
    { apply Rmult_lt_0_compat; assumption. }
    assert (H1 : 0 < cross A B C * au) by (apply Rmult_lt_0_compat; assumption).
    assert (H2 : 0 < cross A B C * bu) by (apply Rmult_lt_0_compat; assumption).
    assert (H3 : 0 < cross A B C * ap) by (apply Rmult_lt_0_compat; assumption).
    assert (H4 : 0 < cross A B C * cq) by (apply Rmult_lt_0_compat; assumption).
    assert (H5 : 0 < ap * au) by (apply Rmult_lt_0_compat; assumption).
    assert (H6 : 0 < ap * bu) by (apply Rmult_lt_0_compat; assumption).
    assert (H7 : 0 < cq * au) by (apply Rmult_lt_0_compat; assumption).
    assert (S01 : 0 < cross A B C * cross A B C + cross A B C * au).
    { apply Rplus_lt_0_compat; assumption. }
    assert (S02 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu).
    { apply Rplus_lt_0_compat; [exact S01 | exact H2]. }
    assert (S03 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap).
    { apply Rplus_lt_0_compat; [exact S02 | exact H3]. }
    assert (S04 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq).
    { apply Rplus_lt_0_compat; [exact S03 | exact H4]. }
    assert (S05 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq + ap * au).
    { apply Rplus_lt_0_compat; [exact S04 | exact H5]. }
    assert (S06 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq + ap * au + ap * bu).
    { apply Rplus_lt_0_compat; [exact S05 | exact H6]. }
    assert (S07 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq + ap * au + ap * bu + cq * au).
    { apply Rplus_lt_0_compat; [exact S06 | exact H7]. }
    assert (HeqS : (cross A B C + ap + cq) * (cross A B C + au + bu)
                   - cross A B Q * cross C A U
                 = cross A B C * cross A B C
                   + cross A B C * au + cross A B C * bu
                   + cross A B C * ap + cross A B C * cq
                   + ap * au + ap * bu + cq * au).
    { unfold ap, cq, au, bu. ring. }
    rewrite <- HeqS in S07. exact S07.
  - apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_A. replace (0 * cross A B C) with 0 by ring.
    assert (H1 : 0 < cross A B P * cross C A U).
    { assert (Hn1 : 0 < - cross A B P) by lra.
      assert (Hn2 : 0 < - cross C A U) by lra.
      assert (Hp : 0 < (- cross A B P) * (- cross C A U)).
      { apply Rmult_lt_0_compat; assumption. }
      replace ((- cross A B P) * (- cross C A U))
        with (cross A B P * cross C A U) in Hp by ring.
      exact Hp. }
    assert (H2 : 0 < cross A B U * (- cross C A P)).
    { apply Rmult_lt_0_compat; [exact HcU | lra]. }
    assert (Hsum : 0 < cross A B P * cross C A U
                      + cross A B U * (- cross C A P)).
    { apply Rplus_lt_0_compat; assumption. }
    replace (cross A B P * cross C A U - cross A B U * cross C A P)
      with (cross A B P * cross C A U + cross A B U * (- cross C A P))
      by ring.
    exact Hsum.
Qed.

(* A strict spike has exactly one positive slack. skA sits in the
   exterior corner at A, and likewise for skB and skC. *)
Definition skA (A B C X : Point) : Prop :=
  0 < cross B C X /\ cross C A X < 0 /\ cross A B X < 0.
Definition skB (A B C X : Point) : Prop :=
  cross B C X < 0 /\ 0 < cross C A X /\ cross A B X < 0.
Definition skC (A B C X : Point) : Prop :=
  cross B C X < 0 /\ cross C A X < 0 /\ 0 < cross A B X.

Lemma skB_rot : forall A B C X, skB A B C X -> skA B C A X.
Proof. intros A B C X [Ha [Hb Hc]]. repeat split; assumption. Qed.

Lemma skC_rot : forall A B C X, skC A B C X -> skB B C A X.
Proof. intros A B C X [Ha [Hb Hc]]. repeat split; assumption. Qed.

Lemma skA_rot : forall A B C X, skA A B C X -> skC B C A X.
Proof. intros A B C X [Ha [Hb Hc]]. repeat split; assumption. Qed.

Lemma spikes_ccw : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skA A B C P -> skB A B C Q -> skC A B C U ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  destruct Hp as [HaP [HbP HcP]].
  destruct Hq as [HaQ [HbQ HcQ]].
  destruct Hu as [HaU [HbU HcU]].
  assert (Hopen : tri_open P Q U A).
  { apply (surround_open_A A B C P Q U); assumption. }
  destruct (meet_vertex P Q U A B C A Hs Hd (or_introl eq_refl) Hopen)
    as [X [HsX HtX]].
  exists X. split; assumption.
Qed.

Lemma spikes_ccw_rot : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skB A B C P -> skC A B C Q -> skA A B C U ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply meet_rot_T.
  apply spikes_ccw.
  - replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd.
  - exact Hs.
  - apply skB_rot. exact Hp.
  - apply skC_rot. exact Hq.
  - apply skA_rot. exact Hu.
Qed.

Lemma spikes_ccw_rot2 : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skC A B C P -> skA A B C Q -> skB A B C U ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply meet_rot_T.
  apply spikes_ccw_rot.
  - replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd.
  - exact Hs.
  - apply skC_rot. exact Hp.
  - apply skA_rot. exact Hq.
  - apply skB_rot. exact Hu.
Qed.

Lemma spikes_cw_false : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skA A B C P -> skC A B C Q -> skB A B C U -> False.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  destruct Hp as [HaP [HbP HcP]].
  destruct Hq as [HaQ [HbQ HcQ]].
  destruct Hu as [HaU [HbU HcU]].
  assert (Hopen : tri_open P U Q A).
  { apply (surround_open_A A B C P U Q); assumption. }
  destruct Hopen as [Hpu [Huq Hqp]].
  assert (Hpq : cross P Q A < 0).
  { assert (E := cross_swap_first_two Q P A). lra. }
  assert (Hqu : cross Q U A < 0).
  { assert (E := cross_swap_first_two U Q A). lra. }
  assert (Hup : cross U P A < 0).
  { assert (E := cross_swap_first_two P U A). lra. }
  assert (Esum := cross_sum3 P Q U A). lra.
Qed.

Lemma spikes_cw_rot_false : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skB A B C P -> skA A B C Q -> skC A B C U -> False.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply (spikes_cw_false B C A P Q U).
  - replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd.
  - exact Hs.
  - apply skB_rot. exact Hp.
  - apply skA_rot. exact Hq.
  - apply skC_rot. exact Hu.
Qed.

Lemma spikes_cw_rot2_false : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skC A B C P -> skB A B C Q -> skA A B C U -> False.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply (spikes_cw_false C A B P Q U).
  - replace (cross C A B) with (cross A B C) by apply cross_cycle2. exact Hd.
  - exact Hs.
  - apply (skB_rot B C A). apply skC_rot. exact Hp.
  - apply (skA_rot B C A). apply skB_rot. exact Hq.
  - apply (skC_rot B C A). apply skA_rot. exact Hu.
Qed.

Local Ltac le_c :=
  match goal with
  | H : skA ?A ?B ?C ?X |- cross ?A ?B ?X <= 0 =>
      destruct H as [? [? Hc]]; apply Rlt_le; exact Hc
  | H : skB ?A ?B ?C ?X |- cross ?A ?B ?X <= 0 =>
      destruct H as [? [? Hc]]; apply Rlt_le; exact Hc
  end.

Local Ltac le_a :=
  match goal with
  | H : skB ?A ?B ?C ?X |- cross ?B ?C ?X <= 0 =>
      destruct H as [Ha [? ?]]; apply Rlt_le; exact Ha
  | H : skC ?A ?B ?C ?X |- cross ?B ?C ?X <= 0 =>
      destruct H as [Ha [? ?]]; apply Rlt_le; exact Ha
  end.

Local Ltac le_b :=
  match goal with
  | H : skA ?A ?B ?C ?X |- cross ?C ?A ?X <= 0 =>
      destruct H as [? [Hb ?]]; apply Rlt_le; exact Hb
  | H : skC ?A ?B ?C ?X |- cross ?C ?A ?X <= 0 =>
      destruct H as [? [Hb ?]]; apply Rlt_le; exact Hb
  end.

Local Ltac out_c :=
  left; apply some_outer_ab; unfold outer3; repeat split; le_c.
Local Ltac out_a :=
  left; unfold some_outer; right; left; unfold outer3; repeat split; le_a.
Local Ltac out_b :=
  left; unfold some_outer; do 2 right; left; unfold outer3; repeat split; le_b.

Lemma spikes_cert : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  (skA A B C P \/ skB A B C P \/ skC A B C P) ->
  (skA A B C Q \/ skB A B C Q \/ skC A B C Q) ->
  (skA A B C U \/ skB A B C U \/ skC A B C U) ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  destruct Hp as [Pa|[Pb|Pc]]; destruct Hq as [Qa|[Qb|Qc]];
  destruct Hu as [Ua|[Ub|Uc]].
  - out_c. (* AAA *)
  - out_c. (* AAB *)
  - out_b. (* AAC *)
  - out_c. (* ABA *)
  - out_c. (* ABB *)
  - apply or_intror. apply (spikes_ccw A B C P Q U); assumption. (* ABC *)
  - out_b. (* ACA *)
  - exfalso. apply (spikes_cw_false A B C P Q U); assumption. (* ACB *)
  - out_b. (* ACC *)
  - out_c. (* BAA *)
  - out_c. (* BAB *)
  - exfalso. apply (spikes_cw_rot_false A B C P Q U); assumption. (* BAC *)
  - out_c. (* BBA *)
  - out_c. (* BBB *)
  - out_a. (* BBC *)
  - apply or_intror. apply (spikes_ccw_rot A B C P Q U); assumption. (* BCA *)
  - out_a. (* BCB *)
  - out_a. (* BCC *)
  - out_b. (* CAA *)
  - apply or_intror. apply (spikes_ccw_rot2 A B C P Q U); assumption. (* CAB *)
  - out_b. (* CAC *)
  - exfalso. apply (spikes_cw_rot2_false A B C P Q U); assumption. (* CBA *)
  - out_a. (* CBB *)
  - out_a. (* CBC *)
  - out_b. (* CCA *)
  - out_a. (* CCB *)
  - out_a. (* CCC *)
Qed.

Lemma qu_gap_b : forall A B C Q U,
  0 < cross A B C ->
  cross Q U B - cross Q U A = cross A B Q - cross A B U.
Proof.
  intros A B C Q U Hd.
  assert (E := qu_b_gap A B C Q U).
  apply Rmult_eq_reg_l with (r := cross A B C).
  - replace (cross A B C * (cross Q U B - cross Q U A))
      with ((cross Q U B - cross Q U A) * cross A B C) by ring.
    exact E.
  - apply not_eq_sym. apply Rlt_not_eq. exact Hd.
Qed.

Lemma qu_gap_c : forall A B C Q U,
  0 < cross A B C ->
  cross Q U C - cross Q U A = cross C A U - cross C A Q.
Proof.
  intros A B C Q U Hd.
  assert (E := qu_c_gap A B C Q U).
  apply Rmult_eq_reg_l with (r := cross A B C).
  - replace (cross A B C * (cross Q U C - cross Q U A))
      with ((cross Q U C - cross Q U A) * cross A B C) by ring.
    exact E.
  - apply not_eq_sym. apply Rlt_not_eq. exact Hd.
Qed.

(* P lies on line AB, strictly beyond A: c = 0, b < 0, a > 0. *)
Lemma z1_pqA : forall A B C P Q,
  cross A B P = 0 ->
  cross P Q A * cross A B C = cross A B Q * cross C A P.
Proof.
  intros A B C P Q Hc.
  assert (E := sep_nb_A A B C P Q). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma z1_pqB : forall A B C P Q,
  cross A B P = 0 ->
  cross P Q B * cross A B C = - cross A B Q * cross B C P.
Proof.
  intros A B C P Q Hc.
  assert (E := cross_pq_B_na A B C P Q). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma z1_upA : forall A B C P U,
  cross A B P = 0 ->
  cross U P A * cross A B C = - cross A B U * cross C A P.
Proof.
  intros A B C P U Hc.
  assert (E := cross_up_A A B C P U). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma z1_upB : forall A B C P U,
  cross A B P = 0 ->
  cross U P B * cross A B C = cross A B U * cross B C P.
Proof.
  intros A B C P U Hc.
  assert (E := cross_up_B A B C P U). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma wedge_cab : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross C A P * cross C A Q < 0 ->
  cross P Q C * cross P Q A < 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hca Hpq.
  assert (Hm : exists X, tri_open C A B X /\ tri_open P Q U X).
  { apply wedge_edges; try assumption.
    replace (cross C A B) with (cross A B C) by apply cross_cycle2. exact Hd. }
  destruct Hm as [X [Ht HsX]].
  exists X. split; [| exact HsX].
  apply tri_open_rot. exact Ht.
Qed.

Lemma wedge_bca : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross B C P * cross B C Q < 0 ->
  cross P Q B * cross P Q C < 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hbc Hpq.
  assert (Hm : exists X, tri_open B C A X /\ tri_open P Q U X).
  { apply wedge_edges; try assumption.
    replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd. }
  destruct Hm as [X [Ht HsX]].
  exists X. split; [| exact HsX].
  destruct Ht as [H1 [H2 H3]]. repeat split; assumption.
Qed.

Lemma z1_succ : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross A B P = 0 -> cross C A P < 0 -> 0 < cross B C P ->
  0 < cross A B Q -> cross A B U < 0 ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs HcP HbP HaP Hq Hu.
  assert (HPQA : cross P Q A < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqA A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_pos_neg; assumption. }
  assert (HPQB : cross P Q B < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqB A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_neg; [lra | exact HaP]. }
  destruct (Rlt_dec 0 (cross C A U)) as [HbU|HbU].
  - assert (HUPA : cross U P A < 0).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      rewrite (z1_upA A B C P U HcP).
      replace (0 * cross A B C) with 0 by ring.
      apply prod_pos_neg; [lra | exact HbP]. }
    assert (HUPB : cross U P B < 0).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      rewrite (z1_upB A B C P U HcP).
      replace (0 * cross A B C) with 0 by ring.
      apply prod_neg; assumption. }
    assert (HUPC : cross U P C < 0).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      assert (E := cross_up_C A B C P U).
      assert (Ea := cross_sum3 A B C P). rewrite HcP in Ea.
      assert (Eu := cross_sum3 A B C U).
      replace (0 * cross A B C) with 0 by ring.
      (* UPC * Δ = Δ * (bP - bU) - cU * bP *)
      assert (Hrew : cross U P C * cross A B C =
          cross A B C * (cross C A P - cross C A U)
          - cross A B U * cross C A P).
      { rewrite E.
        replace (cross B C U) with
          (cross A B C - cross C A U - cross A B U) by lra.
        replace (cross B C P) with
          (cross A B C - cross C A P) by lra.
        ring. }
      rewrite Hrew.
      assert (H1 : cross A B C * (cross C A P - cross C A U) < 0).
      { apply prod_pos_neg; [exact Hd | lra]. }
      assert (H2 : - cross A B U * cross C A P < 0).
      { apply prod_pos_neg; [lra | exact HbP]. }
      replace (cross A B C * (cross C A P - cross C A U)
                 - cross A B U * cross C A P)
        with (cross A B C * (cross C A P - cross C A U)
              + (- cross A B U * cross C A P)) by ring.
      replace 0 with (0 + 0) by ring.
      apply Rplus_lt_compat; assumption. }
    left. apply some_outer_up. repeat split; apply Rlt_le; assumption.
  - apply Rnot_lt_le in HbU.
    destruct (Rlt_dec 0 (cross P Q C)) as [HC|HC].
    + destruct (Rlt_dec 0 (cross C A Q)) as [HbQ|HbQ].
      * right. apply wedge_cab; try assumption.
        -- apply prod_neg; assumption.
        -- assert (Hprod : cross P Q A * cross P Q C < 0).
           { apply prod_neg; [exact HPQA | exact HC]. }
           replace (cross P Q C * cross P Q A)
             with (cross P Q A * cross P Q C) by ring.
           exact Hprod.
      * apply Rnot_lt_le in HbQ.
        left. unfold some_outer. right. right. left.
        repeat split; [apply Rlt_le; exact HbP | exact HbQ | exact HbU].
    + apply Rnot_lt_le in HC.
      left. apply some_outer_pq. repeat split; [apply Rlt_le; exact HPQA |
        apply Rlt_le; exact HPQB | exact HC].
Qed.

Lemma face_pos : forall sM sV u,
  0 <= sM -> 0 <= sV -> 0 < u -> u < 1 ->
  (sM = 0 -> 0 < sV) ->
  0 < (1 - u) * sM + u * sV.
Proof.
  intros sM sV u Hm Hv Hu Hu1 Hlift.
  destruct (Rle_lt_or_eq_dec 0 sM Hm) as [Hgt|Heq].
  - apply Rplus_lt_le_0_compat; [apply Rmult_lt_0_compat; lra | apply Rmult_le_pos; lra].
  - apply slack_mix_pos; [rewrite <- Heq; lra | apply Hlift; symmetry; exact Heq | exact Hu | lra].
Qed.

Lemma nudge_meet : forall A B C D E F M V,
  0 < cross A B C ->
  tri_open A B C M ->
  0 <= cross D E M -> 0 <= cross E F M -> 0 <= cross F D M ->
  0 <= cross D E V -> 0 <= cross E F V -> 0 <= cross F D V ->
  (cross D E M = 0 -> 0 < cross D E V) ->
  (cross E F M = 0 -> 0 < cross E F V) ->
  (cross F D M = 0 -> 0 < cross F D V) ->
  exists X, tri_open A B C X /\ tri_open D E F X.
Proof.
  intros A B C D E F M V Hd HM HdeM HefM HfdM HdeV HefV HfdV Lde Lef Lfd.
  destruct HM as [HmAB [HmBC HmCA]].
  set (rooms :=
    [ seg_room (cross A B M) (cross A B V);
      seg_room (cross B C M) (cross B C V);
      seg_room (cross C A M) (cross C A V) ]).
  set (t := rmin_list rooms).
  assert (Ht : 0 < t).
  { unfold t, rooms. apply rmin_list_pos. intros s Hin. simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]]; apply seg_room_pos; assumption. }
  set (u := t / 2).
  assert (Hu : 0 < u) by (unfold u; lra).
  assert (Hu1 : u < 1).
  { assert (Hh := rmin_list_half rooms). unfold u, t in *. lra. }
  assert (HuAB : u < seg_room (cross A B M) (cross A B V)).
  { apply Rlt_le_trans with (r2 := t); [unfold u; lra | unfold t].
    apply rmin_list_le. unfold rooms. simpl. left. reflexivity. }
  assert (HuBC : u < seg_room (cross B C M) (cross B C V)).
  { apply Rlt_le_trans with (r2 := t); [unfold u; lra | unfold t].
    apply rmin_list_le. unfold rooms. simpl. right. left. reflexivity. }
  assert (HuCA : u < seg_room (cross C A M) (cross C A V)).
  { apply Rlt_le_trans with (r2 := t); [unfold u; lra | unfold t].
    apply rmin_list_le. unfold rooms. simpl. right. right. left. reflexivity. }
  set (X := convex_combination M V u). exists X. split.
  - repeat split; unfold X; rewrite cross_combo.
    + apply slack_pos_room; [exact HmAB | apply Rlt_le; exact Hu | exact HuAB].
    + apply slack_pos_room; [exact HmBC | apply Rlt_le; exact Hu | exact HuBC].
    + apply slack_pos_room; [exact HmCA | apply Rlt_le; exact Hu | exact HuCA].
  - repeat split; unfold X; rewrite cross_combo.
    + apply face_pos; assumption.
    + apply face_pos; assumption.
    + apply face_pos; assumption.
Qed.

Lemma z1_pred : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross A B P = 0 -> cross C A P < 0 -> 0 < cross B C P ->
  cross A B Q < 0 -> 0 < cross A B U ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs HcP HbP HaP Hq Hu.
  assert (HPQA : 0 < cross P Q A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqA A B C P Q HcP). replace (0 * cross A B C) with 0 by ring.
    replace (cross A B Q * cross C A P)
      with ((- cross A B Q) * (- cross C A P)) by ring.
    apply Rmult_lt_0_compat; lra. }
  assert (HUPA : 0 < cross U P A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_upA A B C P U HcP). replace (0 * cross A B C) with 0 by ring.
    replace (- cross A B U * cross C A P)
      with (cross A B U * (- cross C A P)) by ring.
    apply Rmult_lt_0_compat; lra. }
  destruct (Rlt_dec 0 (cross Q U A)) as [HQA|HQA].
  - right.
    destruct (meet_vertex P Q U A B C A Hs Hd (or_introl eq_refl)
                (conj HPQA (conj HQA HUPA))) as [X [HsX HtX]].
    exists X. split; assumption.
  - apply Rnot_lt_le in HQA.
    assert (HQUB : cross Q U B < 0).
    { assert (E := qu_gap_b A B C Q U Hd). lra. }
    destruct (Rlt_dec 0 (cross Q U C)) as [HQC|HQC].
    + assert (HbQ : cross C A Q < 0).
      { destruct (Rle_dec 0 (cross C A Q)) as [Hge|Hlt];
          [| apply Rnot_le_lt; exact Hlt].
        assert (Hgc := qu_gap_c A B C Q U Hd). exfalso.
        destruct (Rlt_dec (cross C A U) 0) as [Hun|Hup].
        - assert (E := Hgc). assert (HQ : cross Q U C < 0) by lra.
          apply (Rlt_asym 0 (cross Q U C) HQC HQ).
        - apply Rnot_lt_le in Hup.
          assert (Eneg : cross Q U A * cross A B C =
              cross C A Q * cross A B U + (- cross A B Q) * cross C A U).
          { rewrite (qua_bb A B C Q U). ring. }
          assert (Hle : cross Q U A * cross A B C <= 0).
          { apply Rle_trans with (r2 := 0 * cross A B C).
            - apply Rmult_le_compat_r; [apply Rlt_le; exact Hd | exact HQA].
            - replace (0 * cross A B C) with 0 by ring. apply Rle_refl. }
          destruct (Rle_lt_or_eq_dec 0 (cross C A Q) Hge) as [Hqb|Hqe].
          + assert (Hpos : 0 < cross C A Q * cross A B U
                             + (- cross A B Q) * cross C A U).
            { apply Rplus_lt_le_0_compat.
              - apply Rmult_lt_0_compat; [exact Hqb | exact Hu].
              - apply Rmult_le_pos; lra. }
            apply (Rle_not_lt 0 _ Hle). rewrite Eneg. exact Hpos.
          + destruct (Rle_lt_or_eq_dec 0 (cross C A U) Hup) as [Hub|Hue].
            * assert (Hpos : 0 < cross C A Q * cross A B U
                               + (- cross A B Q) * cross C A U).
              { rewrite <- Hqe.
                replace (0 * cross A B U + (- cross A B Q) * cross C A U)
                  with ((- cross A B Q) * cross C A U) by ring.
                apply Rmult_lt_0_compat; lra. }
              apply (Rle_not_lt 0 _ Hle). rewrite Eneg. exact Hpos.
            * assert (Hz : cross Q U A = 0).
              { apply Rmult_eq_reg_l with (r := cross A B C).
                - replace (cross A B C * cross Q U A)
                    with (cross Q U A * cross A B C) by ring.
                  rewrite Eneg. rewrite <- Hqe. rewrite <- Hue. ring.
                - apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
              assert (Hc0 : cross Q U C = 0).
              { assert (E := Hgc). rewrite Hz in E. rewrite <- Hqe in E.
                rewrite <- Hue in E. lra. }
              apply (Rlt_not_eq 0 (cross Q U C) HQC). symmetry. exact Hc0. }
      destruct (Rlt_dec 0 (cross C A U)) as [HbU|HbU].
      * right.
        destruct (Rle_lt_or_eq_dec _ _ HQA) as [Hqa|Hqe].
        -- assert (Hm : exists X, tri_open A B C X /\ tri_open Q U P X).
           { apply wedge_cab; try assumption.
             - replace (cross Q U P) with (cross P Q U)
                 by (rewrite cross_cycle; reflexivity). exact Hs.
             - apply prod_neg; assumption.
             - apply prod_pos_neg; [exact HQC | exact Hqa]. }
           destruct Hm as [X [Ht HsX]]. exists X. split;
             [exact Ht | apply tri_open_rot; apply tri_open_rot; exact HsX].
        -- assert (HaQ : 0 < cross B C Q).
           { assert (E := cross_sum3 A B C Q). lra. }
           destruct (Rlt_dec 0 (cross B C U)) as [HaU|HaU].
           ++ destruct (meet_vertex A B C P Q U U Hd Hs
                         (or_intror (or_intror (or_introl eq_refl)))
                         (conj Hu (conj HaU HbU))) as [X [Ht HsX]].
              exists X. split; assumption.
           ++ apply Rnot_lt_le in HaU.
              destruct (Rle_lt_or_eq_dec _ _ HaU) as [HaUn|HaU0].
              ** assert (Hm : exists X, tri_open B C A X /\ tri_open Q U P X).
                 { apply wedge_edges.
                   - replace (cross B C A) with (cross A B C)
                       by apply cross_cycle. exact Hd.
                   - replace (cross Q U P) with (cross P Q U)
                       by (rewrite cross_cycle; reflexivity). exact Hs.
                   - apply prod_pos_neg; [exact HaQ | exact HaUn].
                   - apply prod_neg; [exact HQUB | exact HQC]. }
                 destruct Hm as [X [Ht HsX]]. exists X. split.
                 --- destruct Ht as [H1 [H2 H3]]. repeat split; assumption.
                 --- destruct HsX as [H1 [H2 H3]]. repeat split; assumption.
              ** set (Mpt := convex_combination A U (1 / 2)).
                 assert (HMopen : tri_open A B C Mpt).
                 { repeat split; unfold Mpt; rewrite cross_combo.
                   - rewrite (cross_third_eq_first A B). lra.
                   - rewrite HaU0. rewrite <- (cross_cycle A B C). lra.
                   - rewrite (cross_third_eq_second C A). lra. }
                 assert (HpqM : 0 < cross P Q Mpt).
                 { unfold Mpt. rewrite cross_combo. lra. }
                 assert (HupM : 0 < cross U P Mpt).
                 { unfold Mpt. rewrite cross_combo.
                   rewrite (cross_third_eq_first U P). lra. }
                 assert (HquM : cross Q U Mpt = 0).
                 { unfold Mpt. rewrite cross_combo. rewrite Hqe.
                   rewrite (cross_third_eq_second Q U). ring. }
                 assert (HquP : 0 < cross Q U P).
                 { replace (cross Q U P) with (cross P Q U)
                     by (rewrite cross_cycle; reflexivity). exact Hs. }
                 apply (nudge_meet A B C P Q U Mpt P Hd HMopen).
                 --- apply Rlt_le. exact HpqM.
                 --- rewrite HquM. apply Rle_refl.
                 --- apply Rlt_le. exact HupM.
                 --- rewrite (cross_third_eq_first P Q). apply Rle_refl.
                 --- apply Rlt_le. exact HquP.
                 --- rewrite (cross_third_eq_second U P). apply Rle_refl.
                 --- intros Hz. exfalso. apply (Rlt_not_eq 0 _ HpqM).
                     symmetry. exact Hz.
                 --- intros _. exact HquP.
                 --- intros Hz. exfalso. apply (Rlt_not_eq 0 _ HupM).
                     symmetry. exact Hz.
      * apply Rnot_lt_le in HbU.
        left. unfold some_outer. right. right. left. repeat split.
        -- apply Rlt_le. exact HbP.
        -- apply Rlt_le. exact HbQ.
        -- exact HbU.
    + apply Rnot_lt_le in HQC.
      left. apply some_outer_qu. repeat split; [exact HQA | apply Rlt_le; exact HQUB | exact HQC].
Qed.
