(* NetTopologySuite.Proofs.TrianglePairClip
   Exact intersection of two CCW triangles by three half-plane clips,
   and the I∩I DE-9IM entry. The separating-edge campaign (sat_iff)
   is a follow-up letter. I∩B, B∩I, B∩B are T1b. Exterior cells are T1c.
   topic: relate
   claimId: tri-de9im-a
   witness: ii_nonempty_iff
   secondary witness: ConvexClipComplete.clip_correct
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7), human-reviewed.
   License: BSD-3-Clause *)

From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex RingArea979 Centroid
  DE9IM ConvexClip ConvexClipPoly ConvexClipComplete TrianglePairCommon.
Local Open Scope R_scope.

Definition Dim2 : DimValue := Some 2%nat.
Definition DimF : DimValue := None.

Definition poly_area2 (ps : list Point) : R := signed_area2 ps.


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

(* Five-arm fill samples live in TrianglePairAgree, full project only.
   Stating them here would import RelateMatrixTriangle and
   GeneralTriangleSeparation. Not Admitted. The pairs below are the
   concrete check, including the swapped nest (0,0)(4,0)(0,4) against
   (0,0)(4,0)(1,1). *)

Definition fxA0 : Point := mkPoint 0 0.
Definition fxA1 : Point := mkPoint 1 0.
Definition fxA2 : Point := mkPoint 0 1.

Lemma ii_entry_fixtures :
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


(* Assumptions: sig_not_dec, sig_forall_dec, functional_extensionality_dep. *)
Print Assumptions tri_ccw_supports.
Print Assumptions tri_inter_correct.
Print Assumptions cross_ooo.
Print Assumptions signed_area2_pair0.
Print Assumptions signed_area2_single0.
Print Assumptions signed_area2_nil0.
Print Assumptions signed_area2_open3.
Print Assumptions signed_area2_open2.
Print Assumptions signed_area2_peel.
Print Assumptions chain_supports_prefix.
Print Assumptions signed_area2_fan.
Print Assumptions fan_area_ge0.
Print Assumptions poly_area2_ge0.
Print Assumptions cross_le_fan.
Print Assumptions cross_dot_zero.
Print Assumptions hull_on_line.
Print Assumptions three_on_line.
Print Assumptions wpt_const.
Print Assumptions in_hull_const.
Print Assumptions in_hull_dup_head.
Print Assumptions chain_supports_fewer.
Print Assumptions verts_on_first_edge.
Print Assumptions area_drop_dup.
Print Assumptions supports_drop_dup.
Print Assumptions flat_hull_len.
Print Assumptions flat_hull.
Print Assumptions ccw_edge_distinct.
Print Assumptions fan_pos_triple.
Print Assumptions area_pos_triple.
Print Assumptions cross_centroid3.
Print Assumptions centroid3_combo.
Print Assumptions centroid3_in_hull.
Print Assumptions sum3_zero.
Print Assumptions edge_slack_centroid.
Print Assumptions tri_open_centroid.
Print Assumptions tri_inter_supports.
Print Assumptions nudge_closed.
Print Assumptions cross_nudge.
Print Assumptions vertex_in_tri.
Print Assumptions ii_nonempty_iff.
Print Assumptions cross_tri_le.
Print Assumptions tri_open_closed.
Print Assumptions outer3_disjoint.
Print Assumptions meet_contained.
Print Assumptions some_outer_disjoint.
Print Assumptions ii_entry_dim2_witness.
Print Assumptions ii_entry_dimF_outer.
Print Assumptions strict3_outer.
Print Assumptions ii_entry_separated.
Print Assumptions ii_entry_fixtures.
