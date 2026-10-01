(* NetTopologySuite.Proofs.TinSurfaceVertex
   Angular topology of an internal TIN vertex.
   A counter-clockwise cycle of vectors covers every direction:
   fan_next steps around the cycle, and the last step closes on the first.
   An internal vertex whose spokes form such a cycle is a metric interior
   point. The metric interior is the cell interior, and the metric
   boundary is the cell boundary.
   Fixture: fan_centre_interior_fixtures.
   topic: relate
   claimId: tri-de9im-t4
   witness: tin_interior_eq
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7).
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra Lia List Bool PeanoNat.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex ConvexClip
  TrianglePairCommon TrianglePairEdge TrianglePairBound
  TrianglePairExterior TrianglePairTin TrianglePairTinSurface
  TinSurfaceTopo.
Local Open Scope R_scope.
Definition origin : Point := mkPoint 0 0.
Definition vcross (U V : Point) : R := px U * py V - py U * px V.
Lemma vcross_antisym : forall U V, vcross V U = - vcross U V.
Proof. intros. unfold vcross. ring. Qed.
Lemma vcross_zero_r : forall U, vcross U origin = 0.
Proof. intros. unfold vcross, origin. simpl. ring. Qed.
Lemma vcross_neg : forall U D,
  vcross U (mkPoint (- px D) (- py D)) = - vcross U D.
Proof. intros. unfold vcross. simpl. ring. Qed.
Lemma vsum_cross : forall U V W D,
  vcross V W * vcross U D + vcross W U * vcross V D +
  vcross U V * vcross W D = 0.
Proof. intros. unfold vcross. ring. Qed.
Lemma no_strict_left : forall U V W D,
  0 < vcross V W -> 0 <= vcross W U -> 0 < vcross U V ->
  ~ (0 < vcross U D /\ 0 < vcross V D /\ 0 < vcross W D).
Proof.
intros U V W D Ha Hb Hc [Hu [Hv Hw]].
pose proof (vsum_cross U V W D) as H0.
assert (0 < vcross V W * vcross U D + vcross W U * vcross V D
+ vcross U V * vcross W D). { apply Rplus_lt_0_compat.
- apply Rplus_lt_le_0_compat. + apply Rmult_lt_0_compat; assumption.
+ apply Rmult_le_pos; [exact Hb | apply Rlt_le; exact Hv].
- apply Rmult_lt_0_compat; assumption. } lra. Qed.
Fixpoint consec (vs : list Point) : Prop :=
  match vs with
  | [] => True
  | u :: rest =>
      match rest with
      | [] => True
      | v :: _ => 0 < vcross u v /\ consec rest
      end
  end.
Definition ccw_cycle (vs : list Point) : Prop :=
  match vs with
  | u :: v :: w :: rest =>
      consec (u :: v :: w :: rest) /\
      0 < vcross (last (v :: w :: rest) u) u
  | _ => False
  end.
Definition fan_next (vs : list Point) (i : nat) : Point :=
  match vs with
  | [] => origin
  | d :: _ => nth (Nat.modulo (S i) (length vs)) vs d
  end.
Lemma ccw_len : forall vs, ccw_cycle vs -> (3 <= length vs)%nat.
Proof.
intros [|u [|v [|w rest]]] Hc; simpl in Hc; try contradiction; simpl; lia.
Qed.
Lemma ccw_drop : forall u v w x rest,
  ccw_cycle (u :: v :: w :: x :: rest) -> 0 < vcross u w ->
  ccw_cycle (u :: w :: x :: rest).
Proof.
intros u v w x rest Hc Huw. destruct Hc as [Hcons Hcl]. simpl in Hcons.
destruct Hcons as [_ Htail]. simpl in Htail.
destruct Htail as [_ Hrest]. split. - split; [exact Huw | exact Hrest].
- exact Hcl. Qed.
Lemma not_all_pos : forall vs D,
  ccw_cycle vs -> ~ (forall P, In P vs -> 0 < vcross P D).
Proof.
intros vs D Hc Hall. remember (length vs) as n eqn:En.
revert vs D Hc Hall En. induction n as [|n IH]; intros vs D Hc Hall En.
- destruct vs; simpl in En; try lia. simpl in Hc. contradiction.
- destruct vs as [|u [|v [|w rest]]]; simpl in Hc; try contradiction.
destruct rest as [|x rest'].
+ destruct Hc as [Hcons Hcl]. simpl in Hcons.
destruct Hcons as [Huv Ht]. destruct Ht as [Hvw _].
apply (no_strict_left u v w D Hvw). * apply Rlt_le. exact Hcl.
* exact Huv. * split; [apply Hall; simpl; tauto|].
split; [apply Hall; simpl; tauto| apply Hall; simpl; tauto].
+ destruct (Rlt_dec 0 (vcross u w)) as [Huw|Huw].
* apply (IH (u :: w :: x :: rest') D).
-- apply (ccw_drop u v w x rest'); [exact Hc | exact Huw].
-- intros P Hin. apply Hall.
destruct Hin as [->|[->|Hin]]; simpl; tauto. -- simpl in En. simpl. lia.
* apply Rnot_lt_le in Huw. destruct Hc as [Hcons _]. simpl in Hcons.
destruct Hcons as [Huv Ht]. destruct Ht as [Hvw _].
apply (no_strict_left u v w D Hvw). -- rewrite vcross_antisym. lra.
-- exact Huv. -- split; [apply Hall; simpl; tauto|].
split; [apply Hall; simpl; tauto| apply Hall; simpl; tauto]. Qed.
Lemma not_all_neg : forall vs D,
  ccw_cycle vs -> ~ (forall P, In P vs -> vcross P D < 0).
Proof.
intros vs D Hc Hall.
apply (not_all_pos vs (mkPoint (- px D) (- py D)) Hc).
intros P Hin. rewrite vcross_neg.
assert (Hlt : vcross P D < 0) by (apply Hall; exact Hin). lra. Qed.
Lemma consec_nth : forall vs i,
  consec vs -> (S i < length vs)%nat ->
  0 < vcross (nth i vs origin) (nth (S i) vs origin).
Proof.
induction vs as [|u vs IH]; intros i Hc Hi; simpl in Hi; try lia.
destruct vs as [|v rest]; simpl in Hi; try lia.
simpl in Hc. destruct Hc as [Huv Hrest]. destruct i. - simpl. exact Huv.
- apply IH. exact Hrest. simpl. lia. Qed.
Lemma fan_next_succ : forall vs i d,
  (S i < length vs)%nat -> fan_next vs i = nth (S i) vs d.
Proof.
intros vs i d Hi. destruct vs as [|h rest]; [simpl in Hi; lia|].
unfold fan_next.
assert (Em : Nat.modulo (S i) (length (h :: rest)) = S i).
{ apply Nat.mod_small. exact Hi. }
rewrite Em. apply nth_indep. exact Hi. Qed.
Lemma fan_next_wrap : forall vs d,
  (1 <= length vs)%nat -> fan_next vs (length vs - 1) = nth O vs d.
Proof.
intros vs d Hlen. destruct vs as [|h rest]; [simpl in Hlen; lia|].
unfold fan_next.
assert (Em : Nat.modulo (S (length (h :: rest) - 1)) (length (h :: rest)) = O).
{ replace (S (length (h :: rest) - 1)) with (length (h :: rest)) by lia.
apply Nat.Div0.mod_same. } rewrite Em. simpl. reflexivity. Qed.
Lemma last_indep : forall (A : Type) (l : list A) (d d' : A),
  l <> [] -> last l d = last l d'.
Proof.
induction l as [|a l IH]; intros d d' Hne; [congruence|].
destruct l as [|b l]; [simpl; reflexivity|].
simpl. apply IH. discriminate. Qed.
Lemma nth_skip : forall (A : Type) (a : A) n (l : list A) (d : A),
  nth (S n) (a :: l) d = nth n l d.
Proof. intros. reflexivity. Qed.
Lemma last_nth : forall (A : Type) (l : list A) (d : A),
  l <> [] -> last l d = nth (length l - 1) l d.
Proof.
induction l as [|a l IH]; intros d Hne; [congruence|].
destruct l as [|b l]; [simpl; reflexivity|].
replace (length (a :: b :: l) - 1)%nat
with (S (length (b :: l) - 1)) by (simpl; lia).
rewrite nth_skip. simpl last. apply IH. discriminate. Qed.
Lemma cycle_closure : forall vs,
  ccw_cycle vs ->
  0 < vcross (nth (length vs - 1) vs origin) (fan_next vs (length vs - 1)).
Proof.
intros vs Hc.
assert (Hlen : (3 <= length vs)%nat) by (apply ccw_len; exact Hc).
rewrite (fan_next_wrap vs origin) by lia.
destruct vs as [|u [|v [|w rest]]]; simpl in Hc; try contradiction.
destruct Hc as [_ Hcl].
rewrite <- (last_nth Point (u :: v :: w :: rest) origin ltac:(discriminate)).
rewrite (last_indep Point (u :: v :: w :: rest) origin u ltac:(discriminate)).
simpl. exact Hcl. Qed.
Fixpoint first_le_at (vs : list Point) (D : Point) (i : nat) : option nat :=
  match vs with
  | [] => None
  | p :: rest =>
      if Rle_dec (vcross p D) 0 then Some i else first_le_at rest D (S i)
  end.
Definition first_le (vs : list Point) (D : Point) : option nat :=
  first_le_at vs D O.
Lemma first_le_at_spec : forall vs D i0 i,
  first_le_at vs D i0 = Some i ->
  exists d, i = (i0 + d)%nat /\ (d < length vs)%nat /\
    vcross (nth d vs origin) D <= 0 /\
    (forall k, (k < d)%nat -> 0 < vcross (nth k vs origin) D).
Proof.
induction vs as [|p rest IH]; intros D i0 i H; simpl in H; [discriminate|].
destruct (Rle_dec (vcross p D) 0) as [Hp|Hp].
- injection H as <-. exists O. split; [lia|]. split; [simpl; lia|].
split; [simpl; exact Hp|]. intros k Hk. lia.
- destruct (IH D (S i0) i H) as [d [Heq [Hd [Hc Hall]]]].
exists (S d). split; [lia|]. split; [simpl; lia|]. split; [simpl; exact Hc|].
intros k Hk. destruct k; [simpl; apply Rnot_le_lt; exact Hp|].
simpl. apply Hall. lia. Qed.
Lemma first_le_none : forall vs D,
  first_le vs D = None ->
  forall k, (k < length vs)%nat -> 0 < vcross (nth k vs origin) D.
Proof.
intros vs D. unfold first_le. assert (Hgen : forall i0,
first_le_at vs D i0 = None ->
forall k, (k < length vs)%nat -> 0 < vcross (nth k vs origin) D).
{ induction vs as [|p rest IH]; intros i0 Hnone k Hk; simpl in Hk; try lia.
simpl in Hnone.
destruct (Rle_dec (vcross p D) 0) as [Hp|Hp]; [discriminate|].
destruct k; [simpl; apply Rnot_le_lt; exact Hp|].
simpl. apply (IH (S i0) Hnone). simpl in Hk. lia. }
intros Hnone. apply (Hgen O Hnone). Qed.
Fixpoint last_ge_at (vs : list Point) (D : Point) (i : nat)
  (acc : option nat) : option nat :=
  match vs with
  | [] => acc
  | p :: rest =>
      if Rle_dec 0 (vcross p D)
      then last_ge_at rest D (S i) (Some i)
      else last_ge_at rest D (S i) acc
  end.
Definition last_ge (vs : list Point) (D : Point) : option nat :=
  last_ge_at vs D O None.
Lemma last_ge_at_spec : forall vs D i0 acc j,
  last_ge_at vs D i0 acc = Some j ->
  (exists d, j = (i0 + d)%nat /\ (d < length vs)%nat /\
     0 <= vcross (nth d vs origin) D /\
     (forall k, (d < k < length vs)%nat -> vcross (nth k vs origin) D < 0)) \/
  (exists a, acc = Some a /\ j = a /\
     (forall k, (k < length vs)%nat -> vcross (nth k vs origin) D < 0)).
Proof.
induction vs as [|p rest IH]; intros D i0 acc j H; simpl in H.
- right. exists j. split; [exact H|]. split; [reflexivity|].
intros k Hk. simpl in Hk. lia.
- destruct (Rle_dec 0 (vcross p D)) as [Hp|Hp].
+ destruct (IH D (S i0) (Some i0) j H) as [Hin|Hacc].
* destruct Hin as [d [Heq [Hd [Hc Hall]]]].
left. exists (S d). split; [lia|]. split; [simpl; lia|].
split; [simpl; exact Hc|]. intros k Hk.
destruct k; [simpl in Hk; lia|]. simpl. apply Hall. simpl in Hk. lia.
* destruct Hacc as [a [Ha [-> Hall]]].
injection Ha as <-. left. exists O. split; [lia|]. split; [simpl; lia|].
split; [simpl; exact Hp|]. intros k Hk.
destruct k; [simpl in Hk; lia|]. simpl. apply Hall. simpl in Hk. lia.
+ destruct (IH D (S i0) acc j H) as [Hin|Hacc].
* destruct Hin as [d [Heq [Hd [Hc Hall]]]].
left. exists (S d). split; [lia|]. split; [simpl; lia|].
split; [simpl; exact Hc|]. intros k Hk.
destruct k; [simpl; apply Rnot_le_lt; exact Hp|].
simpl. apply Hall. simpl in Hk. lia.
* destruct Hacc as [a [Ha [-> Hall]]].
right. exists a. split; [exact Ha|]. split; [reflexivity|].
intros k Hk. destruct k; [simpl; apply Rnot_le_lt; exact Hp|].
simpl. apply Hall. simpl in Hk. lia. Qed.
Lemma last_ge_spec : forall vs D j,
  last_ge vs D = Some j ->
  (j < length vs)%nat /\ 0 <= vcross (nth j vs origin) D /\
  (forall k, (j < k < length vs)%nat -> vcross (nth k vs origin) D < 0).
Proof.
intros vs D j H.
destruct (last_ge_at_spec vs D O None j H) as [Hin|Hacc].
- destruct Hin as [d [-> [Hd [Hc Hall]]]]. split; [exact Hd|].
split; [exact Hc|]. exact Hall.
- destruct Hacc as [a [Ha _]]. discriminate. Qed.
Lemma last_ge_acc_some : forall vs D i0 a,
  last_ge_at vs D i0 (Some a) <> None.
Proof.
induction vs as [|p rest IH]; intros D i0 a H; simpl in H.
- discriminate. - destruct (Rle_dec 0 (vcross p D)).
+ apply (IH D (S i0) i0). exact H. + apply (IH D (S i0) a). exact H.
Qed.
Lemma last_ge_none : forall vs D,
  last_ge vs D = None ->
  forall k, (k < length vs)%nat -> vcross (nth k vs origin) D < 0.
Proof.
intros vs D. unfold last_ge. assert (Hgen : forall i0,
last_ge_at vs D i0 None = None ->
forall k, (k < length vs)%nat -> vcross (nth k vs origin) D < 0).
{ induction vs as [|p rest IH]; intros i0 Hnone k Hk; simpl in Hk; try lia.
simpl in Hnone. destruct (Rle_dec 0 (vcross p D)) as [Hp|Hp].
- exfalso. apply (last_ge_acc_some rest D (S i0) i0). exact Hnone.
- destruct k; [simpl; apply Rnot_le_lt; exact Hp|].
simpl. apply (IH (S i0) Hnone). simpl in Hk. lia. }
intros Hnone. apply (Hgen O Hnone). Qed.
Lemma ccw_cycle_covers : forall vs D,
  ccw_cycle vs ->
  exists i, (i < length vs)%nat /\
    0 <= vcross (nth i vs origin) D /\
    vcross (fan_next vs i) D <= 0.
Proof.
intros vs D Hc. destruct (first_le vs D) as [i|] eqn:Hf.
- destruct (first_le_at_spec vs D O i Hf) as [d [Heq [Hd [Hle Hall]]]].
subst i. destruct d as [|d]. + destruct (last_ge vs D) as [j|] eqn:Hg.
* destruct (last_ge_spec vs D j Hg) as [Hj [Hge Hafter]].
exists j. split; [exact Hj|]. split; [exact Hge|].
destruct (Nat.eq_dec (S j) (length vs)) as [Hlast|Hmid].
-- assert (Ej : j = (length vs - 1)%nat) by lia. rewrite Ej.
rewrite (fan_next_wrap vs origin) by lia. exact Hle.
-- assert (Hs : (S j < length vs)%nat) by lia.
rewrite (fan_next_succ vs j origin Hs). apply Rlt_le. apply Hafter. lia.
* exfalso. apply (not_all_neg vs D Hc). intros P Hin.
destruct (In_nth vs P origin Hin) as [k [Hk Ek]].
rewrite <- Ek. apply (last_ge_none vs D Hg k Hk).
+ assert (Hs : (S d < length vs)%nat) by lia.
exists d. split; [lia|]. split. * apply Rlt_le. apply Hall. lia.
* rewrite (fan_next_succ vs d origin Hs). exact Hle.
- exfalso. apply (not_all_pos vs D Hc). intros P Hin.
destruct (In_nth vs P origin Hin) as [k [Hk Ek]].
rewrite <- Ek. apply (first_le_none vs D Hf k Hk). Qed.
Lemma vsub_refl : forall V, vsub V V = origin.
Proof. intros. unfold vsub, origin. simpl. f_equal; ring. Qed.
Lemma vcross_vsub : forall V P Y,
  vcross (vsub P V) (vsub Y V) = cross V P Y.
Proof. intros. unfold vcross, vsub, cross. simpl. ring. Qed.
Lemma nth_vsub : forall ps V i,
  nth i (map (fun P => vsub P V) ps) origin = vsub (nth i ps V) V.
Proof.
intros ps V i. rewrite <- (map_nth (fun P => vsub P V) ps V i).
rewrite vsub_refl. reflexivity. Qed.
Lemma fan_next_vsub : forall ps V i,
  ps <> [] ->
  fan_next (map (fun P => vsub P V) ps) i = vsub (fan_next ps i) V.
Proof.
intros [|h t] V i Hne; [contradiction|].
unfold fan_next. rewrite length_map. cbn [map].
rewrite <- (map_nth (fun P => vsub P V) (h :: t) h
(Nat.modulo (S i) (length (h :: t)))). cbn [map]. reflexivity. Qed.
Lemma ccw_consec : forall vs, ccw_cycle vs -> consec vs.
Proof.
intros [|u [|v [|w rest]]] Hc; simpl in Hc; try contradiction.
destruct Hc as [H _]. exact H. Qed.
Lemma ccw_at : forall ps V i,
  ccw_cycle (map (fun P => vsub P V) ps) ->
  (i < length ps)%nat ->
  0 < cross V (nth i ps V) (fan_next ps i).
Proof.
intros ps V i Hc Hi. rewrite <- vcross_vsub. assert (Hne : ps <> []).
{ destruct ps; [simpl in Hi; lia | discriminate]. }
rewrite <- (fan_next_vsub ps V i Hne). rewrite <- (nth_vsub ps V i).
set (vs := map (fun P => vsub P V) ps).
assert (Hlen : length vs = length ps) by (unfold vs; apply length_map).
destruct (Nat.eq_dec (S i) (length ps)) as [Hlast|Hmid].
- assert (Ei : i = (length vs - 1)%nat) by lia. rewrite Ei.
apply cycle_closure. exact Hc.
- assert (Hs : (S i < length vs)%nat) by lia.
rewrite (fan_next_succ vs i origin Hs).
apply consec_nth; [apply ccw_consec; exact Hc | exact Hs]. Qed.
Lemma cross_qv : forall V Q Y, cross Q V Y = - cross V Q Y.
Proof. intros. unfold cross. ring. Qed.
Lemma sector_ins : forall V P Q Y,
  0 < cross V P Q -> 0 <= cross V P Y -> cross V Q Y <= 0 ->
  0 < cross P Q Y ->
  in_tri V P Q Y /\ in_tri P Q V Y /\ in_tri Q V P Y.
Proof.
intros V P Q Y Hd Hp Hq Ho. split; [| split].
- apply (proj1 (tri_slack_hull V P Q Y Hd)).
split; [exact Hp|]. split; [apply Rlt_le; exact Ho|].
rewrite cross_qv. lra.
- apply (proj1 (tri_slack_hull P Q V Y (eq_ind _ (fun z => 0 < z) Hd _ (cross_cycle V P Q)))).
split; [apply Rlt_le; exact Ho|]. split; [rewrite cross_qv; lra | exact Hp].
- apply (proj1 (tri_slack_hull Q V P Y (eq_ind _ (fun z => 0 < z) Hd _ (cross_cycle2 V P Q)))).
split; [rewrite cross_qv; lra|]. split; [exact Hp | apply Rlt_le; exact Ho].
Qed.
Definition fan_tri (ts : list Tri) (V P Q : Point) : Prop :=
  In ((V, P), Q) ts \/ In ((P, Q), V) ts \/ In ((Q, V), P) ts.
Lemma sector_carrier : forall ts V P Q Y,
  0 < cross V P Q -> 0 <= cross V P Y -> cross V Q Y <= 0 ->
  0 < cross P Q Y -> fan_tri ts V P Q -> tin_carrier ts Y.
Proof.
intros ts V P Q Y Hd Hp Hq Ho [Ha|[Hb|Hc]];
destruct (sector_ins V P Q Y Hd Hp Hq Ho) as [H1 [H2 H3]].
- destruct (in_tri_open_or_bd V P Q Y Hd H1) as [Ho2|Hb2].
+ exists ((V, P), Q). split; [exact Ha|]. left. exact Ho2.
+ exists ((V, P), Q). split; [exact Ha|]. right. exact Hb2.
- assert (Hd2 : 0 < cross P Q V).
{ rewrite <- (cross_cycle V P Q). exact Hd. }
destruct (in_tri_open_or_bd P Q V Y Hd2 H2) as [Ho2|Hb2].
+ exists ((P, Q), V). split; [exact Hb|]. left. exact Ho2.
+ exists ((P, Q), V). split; [exact Hb|]. right. exact Hb2.
- assert (Hd3 : 0 < cross Q V P).
{ rewrite <- (cross_cycle2 V P Q). exact Hd. }
destruct (in_tri_open_or_bd Q V P Y Hd3 H3) as [Ho2|Hb2].
+ exists ((Q, V), P). split; [exact Hc|]. left. exact Ho2.
+ exists ((Q, V), P). split; [exact Hc|]. right. exact Hb2. Qed.
Lemma fan_rad : forall n ps V,
  (n <= length ps)%nat ->
  (forall i, (i < n)%nat -> 0 < cross V (nth i ps V) (fan_next ps i)) ->
  exists r, 0 < r /\ forall i, (i < n)%nat -> forall Y,
    dist V Y < r -> 0 < cross (nth i ps V) (fan_next ps i) Y.
Proof.
induction n as [|n IH]; intros ps V Hn Hpos.
- exists 1. split; [lra|]. intros i Hi. lia.
- destruct (IH ps V) as [r0 [Hr0 H0]]. + lia.
+ intros i Hi. apply Hpos. lia.
+ assert (Hc : 0 < cross (nth n ps V) (fan_next ps n) V).
{ rewrite <- (cross_cycle V (nth n ps V) (fan_next ps n)). apply Hpos. lia. }
destruct (slack_ball (nth n ps V) (fan_next ps n) V Hc) as [r1 [Hr1 H1]].
exists (Rmin r0 r1). split. * apply Rmin_pos; assumption.
* intros i Hi Y HY. destruct (Nat.eq_dec i n) as [->|Hne].
-- apply H1. eapply Rlt_le_trans; [exact HY | apply Rmin_r].
-- apply H0; [lia|]. eapply Rlt_le_trans; [exact HY | apply Rmin_l].
Qed.
Theorem int_vertex_interior : forall ts V ps,
  ccw_cycle (map (fun P => vsub P V) ps) ->
  (forall i, (i < length ps)%nat ->
     fan_tri ts V (nth i ps V) (fan_next ps i)) ->
  interior_pt (tin_carrier ts) V.
Proof.
intros ts V ps Hc Hfan. assert (Hlen : (3 <= length ps)%nat).
{ assert (Hm : (3 <= length (map (fun P => vsub P V) ps))%nat)
by (apply ccw_len; exact Hc). rewrite length_map in Hm. exact Hm. }
destruct (fan_rad (length ps) ps V ltac:(lia)) as [r [Hr HY]].
{ intros i Hi. apply ccw_at; assumption. }
exists r. split; [exact Hr|]. intros Y Hd.
destruct (ccw_cycle_covers (map (fun P => vsub P V) ps) (vsub Y V) Hc)
as [i [Hi [Hleft Hright]]]. rewrite length_map in Hi.
assert (Hne : ps <> []).
{ destruct ps; [simpl in Hlen; lia | discriminate]. }
rewrite (nth_vsub ps V i) in Hleft.
rewrite (fan_next_vsub ps V i Hne) in Hright.
rewrite vcross_vsub in Hleft. rewrite vcross_vsub in Hright.
assert (Harea : 0 < cross V (nth i ps V) (fan_next ps i)).
{ apply ccw_at; assumption. }
assert (Hout : 0 < cross (nth i ps V) (fan_next ps i) Y).
{ apply (HY i Hi Y Hd). }
apply (sector_carrier ts V (nth i ps V) (fan_next ps i) Y
Harea Hleft Hright Hout). apply Hfan. exact Hi. Qed.
Definition owns_dir_b (A B C P Q : Point) : bool :=
  (point_eqb P A && point_eqb Q B) ||
  (point_eqb P B && point_eqb Q C) ||
  (point_eqb P C && point_eqb Q A).
Lemma owns_dir_b_true : forall A B C P Q,
  owns_dir_b A B C P Q = true <-> owns_dir A B C P Q.
Proof.
intros. unfold owns_dir_b, owns_dir. split.
- intros H. apply orb_true_iff in H. destruct H as [H|H].
+ apply orb_true_iff in H. destruct H as [H|H];
apply andb_true_iff in H; destruct H as [H1 H2];
apply point_eqb_true in H1, H2. * left. split; assumption.
* right. left. split; assumption.
+ apply andb_true_iff in H. destruct H as [H1 H2].
apply point_eqb_true in H1, H2. right. right. split; assumption.
- intros [H|[H|H]]; destruct H as [-> ->]; apply orb_true_iff.
+ left. apply orb_true_iff. left.
apply andb_true_iff. split; apply point_eqb_refl.
+ left. apply orb_true_iff. right.
apply andb_true_iff. split; apply point_eqb_refl.
+ right. apply andb_true_iff. split; apply point_eqb_refl. Qed.
Lemma owns_vert : forall A B C P Q,
  owns_dir A B C P Q -> vert_edge A B C P Q.
Proof.
intros A B C P Q [[-> ->]|[[-> ->]|[-> ->]]].
- left. left. split; reflexivity.
- right. left. left. split; reflexivity.
- right. right. left. split; reflexivity. Qed.
Lemma not_both_owns : forall A B C P Q,
  0 < cross A B C -> owns_dir A B C P Q -> ~ owns_dir A B C Q P.
Proof.
intros A B C P Q Hd [[-> ->]|[[-> ->]|[-> ->]]]
[[Hq Hp]|[[Hq Hp]|[Hq Hp]]]; subst; unfold cross in Hd; lra. Qed.
Lemma edge_ne : forall A B C P Q,
  0 < cross A B C -> vert_edge A B C P Q -> P <> Q.
Proof.
intros A B C P Q Hd He. destruct (owns_or_rev A B C P Q He) as [Ho|Ho].
- apply (owns_dir_neq A B C P Q Hd Ho).
- apply not_eq_sym. apply (owns_dir_neq A B C Q P Hd Ho). Qed.
Lemma mid_open : forall P Q,
  P <> Q -> on_seg_open P Q (convex_combination P Q (1 / 2)).
Proof. intros. exists (1 / 2). split; [lra | reflexivity]. Qed.
Fixpoint dir_uses (ts : list Tri) (P Q : Point) : nat :=
  match ts with
  | [] => O
  | ((A, B), C) :: rest =>
      if owns_dir_b A B C P Q then S (dir_uses rest P Q)
      else dir_uses rest P Q
  end.
Lemma dir_owner : forall ts P Q,
  (1 <= dir_uses ts P Q)%nat ->
  exists A B C, In ((A, B), C) ts /\ owns_dir A B C P Q.
Proof.
induction ts as [|T rest IH]; intros P Q Hge; simpl in Hge; [lia|].
destruct T as [[A B] C]. destruct (owns_dir_b A B C P Q) eqn:Hb.
- exists A, B, C. split; [left; reflexivity|].
apply owns_dir_b_true. exact Hb.
- destruct (IH P Q Hge) as [D [E [F [Hin Ho]]]].
exists D, E, F. split; [right; exact Hin| exact Ho]. Qed.
Lemma dir_uses_in : forall ts A B C P Q,
  In ((A, B), C) ts -> owns_dir A B C P Q ->
  (1 <= dir_uses ts P Q)%nat.
Proof.
induction ts as [|T rest IH]; intros A B C P Q Hin Ho; simpl in Hin.
- contradiction.
- destruct T as [[D E] F]. simpl. destruct Hin as [Heq|Hin].
+ injection Heq as -> -> ->. apply owns_dir_b_true in Ho.
rewrite Ho. lia. + destruct (owns_dir_b D E F P Q); [lia|].
apply (IH A B C P Q); assumption. Qed.
Lemma dir_uses_le1 : forall ts P Q,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts -> P <> Q ->
  (dir_uses ts P Q <= 1)%nat.
Proof.
induction ts as [|T rest IH]; intros P Q Hpos Hsem Hne; simpl; [lia|].
destruct Hsem as [Hall Hrest]. destruct T as [[A B] C].
assert (Hposr : forall U, In U rest -> tri_pos U).
{ intros U HU. apply Hpos. right. exact HU. }
assert (HT : 0 < cross A B C).
{ pose proof (Hpos ((A, B), C) ltac:(left; reflexivity)) as Hp.
simpl in Hp. exact Hp. } destruct (owns_dir_b A B C P Q) eqn:Hb.
- assert (Hown : owns_dir A B C P Q) by (apply owns_dir_b_true; exact Hb).
assert (Hz : dir_uses rest P Q = O).
{ destruct (Nat.eq_dec (dir_uses rest P Q) O) as [Z|Nz]; [exact Z|].
assert (Hge : (1 <= dir_uses rest P Q)%nat) by lia.
destruct (dir_owner rest P Q Hge) as [D [E [F [Hin Ho]]]].
assert (Hps : tri_pair_sem ((A, B), C) ((D, E), F)).
{ apply Hall. exact Hin. } assert (HD : 0 < cross D E F).
{ apply Hposr in Hin. simpl in Hin. exact Hin. }
destruct (tri_eqb ((A, B), C) ((D, E), F)) eqn:Heq.
- exfalso. apply tri_eqb_true in Heq. rewrite Heq in Hps. simpl in Hps.
destruct Hps as [Hopen _]. apply Hopen.
exists (inner_pt D E F). split; apply inner_open; exact HD.
- exfalso. simpl in Hps. destruct Hps as [Hopen _].
destruct (same_dir_meet A B C D E F P Q
(convex_combination P Q (1 / 2)) HT HD Hown Ho (mid_open P Q Hne))
as [Y HY]. apply Hopen. exists Y. exact HY. } simpl. rewrite Hz. lia.
- simpl. apply (IH P Q Hposr Hrest Hne). Qed.
Lemma edge_uses_dirs : forall ts P Q,
  (forall T, In T ts -> tri_pos T) ->
  edge_uses ts P Q = (dir_uses ts P Q + dir_uses ts Q P)%nat.
Proof.
induction ts as [|T rest IH]; intros P Q Hpos; simpl; [reflexivity|].
destruct T as [[A B] C].
assert (Hposr : forall U, In U rest -> tri_pos U).
{ intros U HU. apply Hpos. right. exact HU. }
assert (HT : 0 < cross A B C).
{ pose proof (Hpos ((A, B), C) ltac:(left; reflexivity)) as Hp.
simpl in Hp. exact Hp. } specialize (IH P Q Hposr).
destruct (tri_edge_b ((A, B), C) P Q) eqn:Hb.
- assert (Hv : vert_edge A B C P Q).
{ apply (proj1 (tri_edge_b_true ((A, B), C) P Q) Hb). }
destruct (owns_or_rev A B C P Q Hv) as [Hf|Hr].
+ assert (Bf : owns_dir_b A B C P Q = true).
{ apply owns_dir_b_true. exact Hf. }
assert (Br : owns_dir_b A B C Q P = false).
{ destruct (owns_dir_b A B C Q P) eqn:E; [| reflexivity].
exfalso. apply (not_both_owns A B C P Q HT Hf).
apply owns_dir_b_true. exact E. }
simpl. rewrite Bf, Br. rewrite IH. lia.
+ assert (Br : owns_dir_b A B C Q P = true).
{ apply owns_dir_b_true. exact Hr. }
assert (Bf : owns_dir_b A B C P Q = false).
{ destruct (owns_dir_b A B C P Q) eqn:E; [| reflexivity].
exfalso. apply (not_both_owns A B C Q P HT Hr).
apply owns_dir_b_true. exact E. }
simpl. rewrite Bf, Br. rewrite IH. lia.
- assert (Bf : owns_dir_b A B C P Q = false).
{ destruct (owns_dir_b A B C P Q) eqn:E; [| reflexivity].
exfalso. apply (tri_edge_b_false A B C P Q Hb).
apply owns_vert. apply owns_dir_b_true. exact E. }
assert (Br : owns_dir_b A B C Q P = false).
{ destruct (owns_dir_b A B C Q P) eqn:E; [| reflexivity].
exfalso. apply (tri_edge_b_false A B C P Q Hb).
assert (Hv2 : vert_edge A B C Q P).
{ apply owns_vert. apply owns_dir_b_true. exact E. }
assert (Hflip : forall P0 Q0 R0 S0,
edge_id P0 Q0 R0 S0 -> edge_id Q0 P0 R0 S0).
{ intros P0 Q0 R0 S0 [[-> ->]|[-> ->]]; [right | left];
split; reflexivity. }
destruct Hv2 as [e|[e|e]]; [left | right; left | right; right];
apply Hflip; exact e. } simpl. rewrite Bf, Br. exact IH. Qed.
Lemma uses_le2 : forall ts P Q,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts -> P <> Q ->
  (edge_uses ts P Q <= 2)%nat.
Proof.
intros ts P Q Hpos Hsem Hne. rewrite (edge_uses_dirs ts P Q Hpos).
assert ((dir_uses ts P Q <= 1)%nat) by (apply dir_uses_le1; assumption).
assert ((dir_uses ts Q P <= 1)%nat).
{ apply dir_uses_le1; try assumption. apply not_eq_sym. exact Hne. }
lia. Qed.
Lemma incident_uses2 : forall ts A B C P Q X,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  In ((A, B), C) ts -> vert_edge A B C P Q -> on_seg P Q X ->
  ~ tin_bd_cells ts X -> edge_uses ts P Q = 2%nat.
Proof.
intros ts A B C P Q X Hpos Hsem Hin He Hs Hn.
assert (HT : 0 < cross A B C).
{ pose proof (Hpos ((A, B), C) Hin) as Hp. simpl in Hp. exact Hp. }
assert (Hpq : P <> Q) by (apply (edge_ne A B C P Q HT He)).
assert (Hge : (1 <= edge_uses ts P Q)%nat).
{ apply (uses_member ts ((A, B), C) P Q Hin).
apply tri_edge_b_true. exact He. }
assert (Hle : (edge_uses ts P Q <= 2)%nat).
{ apply uses_le2; assumption. }
destruct (Nat.eq_dec (edge_uses ts P Q) 1%nat) as [Heq|Hone].
- exfalso. apply Hn. exists P, Q.
split; [exact Hpq|]. split; [exact Heq| exact Hs]. - lia. Qed.
Lemma both_dirs : forall ts P Q,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts -> P <> Q ->
  edge_uses ts P Q = 2%nat -> (1 <= dir_uses ts P Q)%nat ->
  dir_uses ts P Q = 1%nat /\ dir_uses ts Q P = 1%nat.
Proof.
intros ts P Q Hpos Hsem Hne Hu Hge.
rewrite (edge_uses_dirs ts P Q Hpos) in Hu.
assert ((dir_uses ts P Q <= 1)%nat) by (apply dir_uses_le1; assumption).
assert ((dir_uses ts Q P <= 1)%nat).
{ apply dir_uses_le1; try assumption. apply not_eq_sym. exact Hne. }
lia. Qed.
Definition fwd_third (T : Tri) (V Q : Point) : option Point :=
  match T with
  | ((A, B), C) =>
      if point_eqb A V && point_eqb B Q then Some C
      else if point_eqb B V && point_eqb C Q then Some A
      else if point_eqb C V && point_eqb A Q then Some B
      else None
  end.
Fixpoint find_tri (ts : list Tri) (V Q : Point) : option Tri :=
  match ts with
  | [] => None
  | T :: rest =>
      match fwd_third T V Q with
      | Some _ => Some T
      | None => find_tri rest V Q
      end
  end.
Definition find_next (ts : list Tri) (V Q : Point) : option Point :=
  match find_tri ts V Q with
  | Some T => fwd_third T V Q
  | None => None
  end.
Lemma fwd_at_most : forall A B C V Q R,
  fwd_third ((A, B), C) V Q = Some R ->
  (A = V /\ B = Q /\ C = R) \/
  (B = V /\ C = Q /\ A = R) \/
  (C = V /\ A = Q /\ B = R).
Proof.
intros A B C V Q R H. unfold fwd_third in H.
destruct (point_eqb A V && point_eqb B Q) eqn:E1.
- apply andb_true_iff in E1. destruct E1 as [EA EB].
apply point_eqb_true in EA, EB. injection H as <-.
left. repeat split; auto.
- destruct (point_eqb B V && point_eqb C Q) eqn:E2.
+ apply andb_true_iff in E2. destruct E2 as [EB EC].
apply point_eqb_true in EB, EC. injection H as <-.
right. left. repeat split; auto.
+ destruct (point_eqb C V && point_eqb A Q) eqn:E3; [| discriminate].
apply andb_true_iff in E3. destruct E3 as [EC EA].
apply point_eqb_true in EC, EA. injection H as <-.
right. right. repeat split; auto. Qed.
Lemma fwd_owns : forall A B C V Q R,
  fwd_third ((A, B), C) V Q = Some R -> owns_dir A B C V Q.
Proof.
intros A B C V Q R H.
destruct (fwd_at_most A B C V Q R H) as [[-> [-> ->]]|[[-> [-> ->]]|[-> [-> ->]]]].
- left. split; reflexivity. - right. left. split; reflexivity.
- right. right. split; reflexivity. Qed.
Lemma fwd_rev_owns : forall A B C V Q R,
  fwd_third ((A, B), C) V Q = Some R -> owns_dir A B C R V.
Proof.
intros A B C V Q R H.
destruct (fwd_at_most A B C V Q R H) as [[-> [-> ->]]|[[-> [-> ->]]|[-> [-> ->]]]].
- right. right. split; reflexivity. - left. split; reflexivity.
- right. left. split; reflexivity. Qed.
Lemma fwd_cross : forall A B C V Q R,
  0 < cross A B C -> fwd_third ((A, B), C) V Q = Some R ->
  0 < cross V Q R.
Proof.
intros A B C V Q R Hd H. destruct (fwd_at_most A B C V Q R H)
as [[EA [EB EC]]|[[EA [EB EC]]|[EA [EB EC]]]].
- rewrite <- EA, <- EB, <- EC. exact Hd.
- rewrite <- EA, <- EB, <- EC. rewrite <- (cross_cycle A B C). exact Hd.
- rewrite <- EA, <- EB, <- EC. rewrite <- (cross_cycle2 A B C). exact Hd.
Qed.
Lemma fwd_fan : forall ts A B C V Q R,
  In ((A, B), C) ts -> fwd_third ((A, B), C) V Q = Some R ->
  fan_tri ts V Q R.
Proof.
intros ts A B C V Q R Hin H.
destruct (fwd_at_most A B C V Q R H) as [[-> [-> ->]]|[[-> [-> ->]]|[-> [-> ->]]]].
- left. exact Hin. - right. right. exact Hin. - right. left. exact Hin.
Qed.
Lemma owns_fwd_some : forall A B C V Q,
  0 < cross A B C -> owns_dir A B C V Q ->
  exists R, fwd_third ((A, B), C) V Q = Some R.
Proof.
intros A B C V Q Hd [[-> ->]|[[-> ->]|[-> ->]]].
- exists C. unfold fwd_third. rewrite !point_eqb_refl. simpl. reflexivity.
- exists A. unfold fwd_third. destruct (point_eqb A B) eqn:EAB.
+ apply point_eqb_true in EAB. subst A. unfold cross in Hd. lra.
+ rewrite point_eqb_refl. simpl. rewrite !point_eqb_refl. simpl. reflexivity.
- exists B. unfold fwd_third. destruct (point_eqb A C) eqn:EAC.
+ apply point_eqb_true in EAC. subst A. unfold cross in Hd. lra.
+ destruct (point_eqb B C && point_eqb C A) eqn:E2.
* apply andb_true_iff in E2. destruct E2 as [EBC _].
apply point_eqb_true in EBC. subst B. unfold cross in Hd. lra.
* rewrite point_eqb_refl. simpl. rewrite point_eqb_refl. simpl. reflexivity.
Qed.
Lemma find_tri_in : forall ts V Q T,
  find_tri ts V Q = Some T -> In T ts.
Proof.
induction ts as [|U rest IH]; intros V Q T H; simpl in H; [discriminate|].
destruct (fwd_third U V Q). - injection H as ->. left. reflexivity.
- right. apply (IH V Q T H). Qed.
Lemma find_tri_fwd : forall ts V Q T,
  find_tri ts V Q = Some T -> exists R, fwd_third T V Q = Some R.
Proof.
induction ts as [|U rest IH]; intros V Q T H; simpl in H; [discriminate|].
destruct (fwd_third U V Q) eqn:E.
- injection H as ->. exists p. exact E. - apply (IH V Q T H). Qed.
Lemma find_next_tri : forall ts V Q R,
  find_next ts V Q = Some R ->
  exists T, In T ts /\ fwd_third T V Q = Some R.
Proof.
intros ts V Q R H. unfold find_next in H.
destruct (find_tri ts V Q) as [T|] eqn:Hf; [| discriminate].
exists T. split; [apply (find_tri_in ts V Q T Hf) | exact H]. Qed.
Lemma find_next_cross : forall ts V Q R,
  (forall T, In T ts -> tri_pos T) ->
  find_next ts V Q = Some R -> 0 < cross V Q R.
Proof.
intros ts V Q R Hpos H.
destruct (find_next_tri ts V Q R H) as [T [Hin Hf]].
destruct T as [[A B] C]. assert (HT : 0 < cross A B C).
{ apply Hpos in Hin. simpl in Hin. exact Hin. }
apply (fwd_cross A B C V Q R HT Hf). Qed.
Lemma find_next_rev : forall ts V Q R,
  find_next ts V Q = Some R -> (1 <= dir_uses ts R V)%nat.
Proof.
intros ts V Q R H.
destruct (find_next_tri ts V Q R H) as [[[A B] C] [Hin Hf]].
apply (dir_uses_in ts A B C R V Hin). apply (fwd_rev_owns A B C V Q R Hf).
Qed.
Lemma dir_uses_ge2 : forall ts A B C D E F P Q,
  In ((A, B), C) ts -> In ((D, E), F) ts ->
  ((A, B), C) <> ((D, E), F) ->
  owns_dir A B C P Q -> owns_dir D E F P Q ->
  (2 <= dir_uses ts P Q)%nat.
Proof.
induction ts as [|T rest IH]; intros A B C D E F P Q Hin1 Hin2 Hneq Ho1 Ho2;
simpl in Hin1, Hin2; try contradiction.
destruct T as [[G K] I]. destruct Hin1 as [E1|Hin1]; destruct Hin2 as [E2|Hin2].
- congruence. - injection E1 as -> -> ->. simpl.
apply owns_dir_b_true in Ho1. rewrite Ho1.
assert (Hge : (1 <= dir_uses rest P Q)%nat).
{ apply (dir_uses_in rest D E F P Q Hin2 Ho2). } lia.
- injection E2 as -> -> ->. simpl.
apply owns_dir_b_true in Ho2. rewrite Ho2.
assert (Hge : (1 <= dir_uses rest P Q)%nat).
{ apply (dir_uses_in rest A B C P Q Hin1 Ho1). } lia.
- simpl. destruct (owns_dir_b G K I P Q).
+ apply le_S. apply (IH A B C D E F P Q); assumption.
+ apply (IH A B C D E F P Q); assumption. Qed.
Lemma fwd_spoke_unique : forall A B C V Q1 Q2 R1 R2,
  0 < cross A B C ->
  fwd_third ((A, B), C) V Q1 = Some R1 ->
  fwd_third ((A, B), C) V Q2 = Some R2 -> Q1 = Q2.
Proof.
intros A B C V Q1 Q2 R1 R2 Hd H1 H2.
destruct (fwd_at_most A B C V Q1 R1 H1) as [a|[a|a]];
destruct (fwd_at_most A B C V Q2 R2 H2) as [b|[b|b]];
destruct a as [Ea [Eb Ec]]; destruct b as [Fa [Fb Fc]]; subst;
try reflexivity; unfold cross in Hd; lra. Qed.
Lemma succ_inj : forall ts V Q1 Q2 R,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  find_next ts V Q1 = Some R -> find_next ts V Q2 = Some R -> Q1 = Q2.
Proof.
intros ts V Q1 Q2 R Hpos Hsem H1 H2.
destruct (point_eqb Q1 Q2) eqn:Eq; [apply point_eqb_true; exact Eq|].
exfalso.
destruct (find_next_tri ts V Q1 R H1) as [[[A B] C] [Hin1 Hf1]].
destruct (find_next_tri ts V Q2 R H2) as [[[D E] F] [Hin2 Hf2]].
assert (HT : 0 < cross A B C).
{ apply Hpos in Hin1. simpl in Hin1. exact Hin1. }
assert (Hne : Q1 <> Q2).
{ intros Heq. subst Q2. rewrite point_eqb_refl in Eq. discriminate. }
assert (Htr : ((A, B), C) <> ((D, E), F)).
{ intros Heq. apply Hne. rewrite <- Heq in Hf2.
apply (fwd_spoke_unique A B C V Q1 Q2 R R HT Hf1 Hf2). }
assert (Ho1 : owns_dir A B C R V) by (apply (fwd_rev_owns A B C V Q1 R Hf1)).
assert (Ho2 : owns_dir D E F R V) by (apply (fwd_rev_owns D E F V Q2 R Hf2)).
assert (Hge : (2 <= dir_uses ts R V)%nat).
{ apply (dir_uses_ge2 ts A B C D E F R V Hin1 Hin2 Htr Ho1 Ho2). }
assert (Hrv : R <> V) by (apply (owns_dir_neq A B C R V HT Ho1)).
assert (Hle : (dir_uses ts R V <= 1)%nat).
{ apply dir_uses_le1; assumption. } lia. Qed.
Lemma drop_shorter : forall T ts,
  In T ts -> (length (drop_tri T ts) < length ts)%nat.
Proof.
induction ts as [|U rest IH]; intros Hin; [contradiction|].
simpl. destruct (tri_eqb T U) eqn:Heq.
- assert (Hle : (length (drop_tri T rest) <= length rest)%nat).
{ clear. induction rest as [|V rest IH2]; simpl; [lia|].
destruct (tri_eqb T V); simpl.
- apply Nat.le_trans with (length rest); [exact IH2 | lia].
- apply le_n_S. exact IH2. } simpl. lia. - destruct Hin as [->|Hin].
+ rewrite tri_eqb_refl in Heq. discriminate.
+ assert (Hs : (length (drop_tri T rest) < length rest)%nat)
by (apply IH; exact Hin). simpl. lia. Qed.
Lemma find_tri_drop : forall T ts V Q U,
  find_tri ts V Q = Some U -> tri_eqb T U = false ->
  find_tri (drop_tri T ts) V Q = Some U.
Proof.
induction ts as [|W rest IH]; intros V Q U H Hf; simpl in H; [discriminate|].
simpl. destruct (tri_eqb T W) eqn:Heq.
- destruct (fwd_third W V Q) eqn:Hw.
+ injection H as ->. apply tri_eqb_true in Heq. subst T.
rewrite tri_eqb_refl in Hf. discriminate. + apply (IH V Q U H Hf).
- destruct (fwd_third W V Q) eqn:Hw. + simpl. rewrite Hw. exact H.
+ simpl. rewrite Hw. apply (IH V Q U H Hf). Qed.
Lemma find_tri_owns : forall ts A B C V Q,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  In ((A, B), C) ts -> owns_dir A B C V Q ->
  find_tri ts V Q = Some ((A, B), C).
Proof.
induction ts as [|T rest IH]; intros A B C V Q Hpos Hsem Hin Ho;
simpl in Hin; [contradiction|]. destruct Hsem as [Hall Hrest].
assert (Hposr : forall U, In U rest -> tri_pos U).
{ intros U HU. apply Hpos. right. exact HU. }
assert (HT : 0 < cross A B C).
{ pose proof (Hpos ((A, B), C) (match Hin with
| or_introl Heq => or_introl Heq
| or_intror Hr => or_intror Hr end)) as Hp. simpl in Hp. exact Hp. }
assert (Hne : V <> Q) by (apply (owns_dir_neq A B C V Q HT Ho)).
simpl. destruct (fwd_third T V Q) eqn:Hf.
- destruct T as [[D E] F]. destruct Hin as [Heq|Hin].
+ rewrite <- Heq. reflexivity. + exfalso.
assert (Hdo : owns_dir D E F V Q).
{ apply (fwd_owns D E F V Q p). exact Hf. }
simpl. apply owns_dir_b_true in Hdo. apply owns_dir_b_true in Ho.
assert (Hge : (2 <= dir_uses (((D, E), F) :: rest) V Q)%nat).
{ simpl. rewrite Hdo. assert ((1 <= dir_uses rest V Q)%nat).
{ apply (dir_uses_in rest A B C V Q Hin). apply owns_dir_b_true. exact Ho. }
lia. } assert ((dir_uses (((D, E), F) :: rest) V Q <= 1)%nat).
{ apply dir_uses_le1; [exact Hpos | split; assumption | exact Hne]. }
lia. - destruct Hin as [Heq|Hin]. + exfalso. rewrite Heq in Hf.
destruct (owns_fwd_some A B C V Q HT Ho) as [R HR]. congruence.
+ apply (IH A B C V Q Hposr Hrest Hin Ho). Qed.
Lemma fwd_exists : forall ts V R,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  ~ tin_bd_cells ts V -> (1 <= dir_uses ts R V)%nat ->
  exists S, find_next ts V R = Some S.
Proof.
intros ts V R Hpos Hsem Hn Hge.
destruct (dir_owner ts R V Hge) as [A [B [C [Hin Ho]]]].
assert (HT : 0 < cross A B C).
{ apply Hpos in Hin. simpl in Hin. exact Hin. }
assert (Hrv : R <> V) by (apply (owns_dir_neq A B C R V HT Ho)).
assert (Hu : edge_uses ts R V = 2%nat).
{ apply (incident_uses2 ts A B C R V V Hpos Hsem Hin).
- apply owns_vert. exact Ho. - apply (proj2 (seg_ends R V)).
- exact Hn. }
destruct (both_dirs ts R V Hpos Hsem Hrv Hu Hge) as [_ Hfwd].
assert (Hge2 : (1 <= dir_uses ts V R)%nat) by (rewrite Hfwd; lia).
destruct (dir_owner ts V R Hge2) as [D [E [F [Hin2 Ho2]]]].
assert (HT2 : 0 < cross D E F).
{ apply Hpos in Hin2. simpl in Hin2. exact Hin2. }
assert (Hf : find_tri ts V R = Some ((D, E), F)).
{ apply (find_tri_owns ts D E F V R Hpos Hsem Hin2 Ho2). }
destruct (owns_fwd_some D E F V R HT2 Ho2) as [S HS].
exists S. unfold find_next. rewrite Hf. exact HS. Qed.
Fixpoint iter_sp (ts : list Tri) (V : Point) (n : nat) (p : Point) : Point :=
  match n with
  | O => p
  | S k =>
      match find_next ts V (iter_sp ts V k p) with
      | Some r => r
      | None => iter_sp ts V k p
      end
  end.
Lemma iter_next_eq : forall ts V k p r,
  find_next ts V (iter_sp ts V k p) = Some r ->
  iter_sp ts V (S k) p = r.
Proof. intros. simpl. rewrite H. reflexivity. Qed.
Lemma orbit_live : forall ts V P,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  ~ tin_bd_cells ts V ->
  (exists R, find_next ts V P = Some R) ->
  forall n, find_next ts V (iter_sp ts V n P) =
            Some (iter_sp ts V (S n) P).
Proof.
intros ts V P Hpos Hsem Hn Hex n. induction n as [|n IH].
- destruct Hex as [R HR]. simpl. rewrite HR. reflexivity.
- destruct (fwd_exists ts V (iter_sp ts V (S n) P) Hpos Hsem Hn)
as [r Hr]. + apply (find_next_rev ts V (iter_sp ts V n P)). exact IH.
+ rewrite (iter_next_eq ts V (S n) P r Hr). exact Hr. Qed.
Lemma anchor : forall ts A B C V,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  In ((A, B), C) ts -> (V = A \/ V = B \/ V = C) ->
  exists P R, find_next ts V P = Some R /\ 0 < cross V P R.
Proof.
intros ts A B C V Hpos Hsem Hin HV. assert (HT : 0 < cross A B C).
{ apply Hpos in Hin. simpl in Hin. exact Hin. }
destruct HV as [HA|[HB|HC]]; subst V.
- assert (Hf : fwd_third ((A, B), C) A B = Some C).
{ unfold fwd_third. rewrite !point_eqb_refl. simpl. reflexivity. }
assert (Ho : owns_dir A B C A B) by (left; split; reflexivity).
assert (Ht : find_tri ts A B = Some ((A, B), C)).
{ apply find_tri_owns; assumption. } exists B, C. split.
+ unfold find_next. rewrite Ht. exact Hf. + exact HT.
- assert (Hf : fwd_third ((A, B), C) B C = Some A).
{ unfold fwd_third. destruct (point_eqb A B) eqn:E.
- apply point_eqb_true in E. subst A. unfold cross in HT. lra.
- rewrite point_eqb_refl. simpl. rewrite !point_eqb_refl.
simpl. reflexivity. }
assert (Ho : owns_dir A B C B C) by (right; left; split; reflexivity).
assert (Ht : find_tri ts B C = Some ((A, B), C)).
{ apply find_tri_owns; assumption. } exists C, A. split.
+ unfold find_next. rewrite Ht. exact Hf.
+ rewrite <- (cross_cycle A B C). exact HT.
- assert (Hf : fwd_third ((A, B), C) C A = Some B).
{ unfold fwd_third. destruct (point_eqb A C) eqn:E1.
- apply point_eqb_true in E1. subst A. unfold cross in HT. lra.
- destruct (point_eqb B C && point_eqb C A) eqn:E2.
+ apply andb_true_iff in E2. destruct E2 as [EB _].
apply point_eqb_true in EB. subst B. unfold cross in HT. lra.
+ rewrite point_eqb_refl. simpl. rewrite point_eqb_refl.
simpl. reflexivity. }
assert (Ho : owns_dir A B C C A) by (right; right; split; reflexivity).
assert (Ht : find_tri ts C A = Some ((A, B), C)).
{ apply find_tri_owns; assumption. } exists A, B. split.
+ unfold find_next. rewrite Ht. exact Hf.
+ rewrite <- (cross_cycle2 A B C). exact HT. Qed.
Lemma steps_le : forall n ts V (p : nat -> Point) k,
  (length ts <= n)%nat -> (forall T, In T ts -> tri_pos T) ->
  (forall j, (j < k)%nat -> exists U,
      find_tri ts V (p j) = Some U /\
      fwd_third U V (p j) = Some (p (S j))) ->
  (forall i j, (i < j)%nat -> (j < k)%nat -> p i <> p j) ->
  (k <= length ts)%nat.
Proof.
induction n as [|n IH]; intros ts V p k Hlen Hpos Hstep Hsep.
- destruct ts; [| simpl in Hlen; lia]. destruct k; [lia|].
destruct (Hstep O ltac:(lia)) as [U [Hf _]]. simpl in Hf. discriminate.
- destruct k as [|k]; [lia|].
destruct (Hstep O ltac:(lia)) as [T [Hf _]].
assert (Hin : In T ts) by (apply (find_tri_in ts V (p O) T Hf)).
apply drop_shorter in Hin.
assert (Hk : (k <= length (drop_tri T ts))%nat).
{ apply (IH (drop_tri T ts) V (fun j => p (S j)) k); [lia| | |].
- intros U HU. apply Hpos. exact (proj1 (drop_in T ts U HU)).
- intros j Hj. destruct (Hstep (S j) ltac:(lia)) as [U [HfU Hfwd]].
exists U. split; [| exact Hfwd]. destruct (tri_eqb T U) eqn:Eb.
+ exfalso. apply tri_eqb_true in Eb. subst U. destruct T as [[A B] C].
destruct (find_tri_fwd ts V (p O) ((A, B), C) Hf) as [R1 F1].
destruct (find_tri_fwd ts V (p (S j)) ((A, B), C) HfU) as [R2 F2].
apply (Hsep O (S j) ltac:(lia) ltac:(lia)). pose proof (Hpos ((A, B), C)
(find_tri_in ts V (p O) ((A, B), C) Hf)) as Hp. simpl in Hp.
apply (fwd_spoke_unique A B C V (p O) (p (S j)) R1 R2 Hp F1 F2).
+ apply find_tri_drop; [exact HfU| exact Eb].
- intros i j Hi Hj. apply Hsep; lia. } lia. Qed.
Lemma iter_back : forall ts V P d i,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  (forall n, find_next ts V (iter_sp ts V n P) =
             Some (iter_sp ts V (S n) P)) ->
  iter_sp ts V (i + d) P = iter_sp ts V i P -> iter_sp ts V d P = P.
Proof.
intros ts V P d i Hpos Hsem Hlive.
induction i as [|i IH]; intros Heq; [exact Heq|].
apply IH. rewrite (Nat.add_succ_l i d) in Heq.
apply (succ_inj ts V (iter_sp ts V (i + d)%nat P) (iter_sp ts V i P)
(iter_sp ts V (S (i + d)) P) Hpos Hsem).
- rewrite (Hlive (i + d)%nat). reflexivity.
- rewrite (Hlive i). rewrite Heq. reflexivity. Qed.
Fixpoint hit_at (f : nat -> bool) (fuel : nat) : option nat :=
  match fuel with
  | O => None
  | S fuel' =>
      match hit_at f fuel' with
      | Some m0 => Some m0
      | None => if f (S fuel') then Some (S fuel') else None
      end
  end.
Lemma hit_step : forall f n,
  hit_at f (S n) =
  match hit_at f n with
  | Some m => Some m
  | None => if f (S n) then Some (S n) else None
  end.
Proof. intros. reflexivity. Qed.
Lemma period_hits : forall ts V P,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  (forall n, find_next ts V (iter_sp ts V n P) =
             Some (iter_sp ts V (S n) P)) ->
  exists m, (0 < m <= length ts)%nat /\ iter_sp ts V m P = P.
Proof.
intros ts V P Hpos Hsem Hlive.
set (f := fun k => point_eqb (iter_sp ts V k P) P).
assert (Hnone : forall fuel, hit_at f fuel = None ->
forall k, (0 < k <= fuel)%nat -> iter_sp ts V k P <> P).
{ induction fuel as [|fuel IH]; intros Hn k Hk; [lia|].
rewrite (hit_step f fuel) in Hn. case_eq (hit_at f fuel).
- intros m0 Em. rewrite Em in Hn. discriminate Hn.
- intros Em. rewrite Em in Hn. destruct (f (S fuel)) eqn:Eb.
+ discriminate Hn. + destruct (Nat.eq_dec k (S fuel)) as [->|Hk2].
* intros Heq. unfold f in Eb. rewrite Heq in Eb.
rewrite point_eqb_refl in Eb. discriminate Eb.
* apply IH; [exact Em|lia]. }
assert (Hsome : forall fuel m, hit_at f fuel = Some m ->
(0 < m <= fuel)%nat /\ iter_sp ts V m P = P).
{ induction fuel as [|fuel IH]; intros m H; [discriminate|].
rewrite (hit_step f fuel) in H. case_eq (hit_at f fuel).
- intros m0 Em. rewrite Em in H. injection H. intros ->.
destruct (IH m Em) as [Hm He]. split; [lia| exact He].
- intros Em. rewrite Em in H. destruct (f (S fuel)) eqn:Eb.
+ injection H. intros Heq. subst m. unfold f in Eb.
apply point_eqb_true in Eb. split; [lia| exact Eb]. + discriminate H. }
destruct (hit_at f (length ts)) as [m|] eqn:Hp.
- destruct (Hsome (length ts) m Hp) as [Hm He]. exists m. split; assumption.
- exfalso. set (L := length ts).
assert (Hsep : forall i j, (i < j)%nat -> (j <= L)%nat ->
iter_sp ts V i P <> iter_sp ts V j P).
{ intros i j Hi Hj Heq. apply (Hnone L Hp (j - i)%nat); [lia|].
apply (iter_back ts V P (j - i)%nat i Hpos Hsem Hlive).
replace j with (i + (j - i))%nat in Heq by lia. symmetry. exact Heq. }
assert (Hstep : forall j, (j < S L)%nat -> exists U,
find_tri ts V (iter_sp ts V j P) = Some U /\
fwd_third U V (iter_sp ts V j P) = Some (iter_sp ts V (S j) P)).
{ intros j Hj. destruct (find_tri ts V (iter_sp ts V j P)) as [U|] eqn:Hf.
- assert (Hl := Hlive j). unfold find_next in Hl. rewrite Hf in Hl.
exists U. split; [reflexivity| exact Hl].
- assert (Hl := Hlive j). unfold find_next in Hl. rewrite Hf in Hl.
discriminate. } assert ((S L <= L)%nat).
{ apply (steps_le L ts V (fun j => iter_sp ts V j P) (S L));
[unfold L; lia| exact Hpos| exact Hstep|].
intros i j Hi Hj. apply Hsep; lia. } unfold L in *. lia. Qed.
Fixpoint nlist (f : nat -> Point) (n : nat) : list Point :=
  match n with O => [] | S k => f O :: nlist (fun i => f (S i)) k end.
Lemma nlist_len : forall n f, length (nlist f n) = n.
Proof. induction n as [|n IH]; intros; simpl; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma nlist_nth : forall n f i d, (i < n)%nat -> nth i (nlist f n) d = f i.
Proof.
induction n as [|n IH]; intros f i d Hi; [lia|].
destruct i; simpl; [reflexivity| apply (IH (fun j => f (S j))); lia].
Qed.
Lemma ccw_from : forall ps,
  (3 <= length ps)%nat ->
  (forall i, (S i < length ps)%nat ->
     0 < vcross (nth i ps origin) (nth (S i) ps origin)) ->
  0 < vcross (nth ((length ps - 1)%nat) ps origin) (nth O ps origin) ->
  ccw_cycle ps.
Proof.
intros ps Hlen Hall Hcl.
destruct ps as [|u [|v [|w rest]]]; simpl in Hlen; try lia. split.
- assert (Hc : forall qs, (forall i, (S i < length qs)%nat ->
0 < vcross (nth i qs origin) (nth (S i) qs origin)) -> consec qs).
{ induction qs as [|a qs IH]; intros H; [exact I|].
destruct qs as [|b qs]; [exact I|]. split. - apply (H O). simpl. lia.
- apply IH. intros i Hi. apply (H (S i)). simpl in *. lia. }
apply Hc. exact Hall.
- assert (Hu : nth O (u :: v :: w :: rest) origin = u) by reflexivity.
rewrite Hu in Hcl.
rewrite (last_nth Point (v :: w :: rest) u ltac:(discriminate)).
cbn [length].
assert (Hn : ((S (S (length rest)) - 1) < S (S (length rest)))%nat) by lia.
rewrite (nth_indep (v :: w :: rest) u origin Hn).
replace ((S (S (length rest)) - 1)%nat) with (S (length rest)) by lia.
cbn [length] in Hcl.
replace ((S (S (S (length rest))) - 1)%nat) with (S (S (length rest))) in Hcl by lia.
rewrite (nth_skip Point u (S (length rest)) (v :: w :: rest) origin) in Hcl.
exact Hcl. Qed.
Lemma internal_vert_interior : forall ts V,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  internal_vert ts V -> interior_pt (tin_carrier ts) V.
Proof.
intros ts V Hpos Hsem [Hv Hnb]. destruct Hv as [[[A B] C] [Hin HV]].
destruct (anchor ts A B C V Hpos Hsem Hin HV) as [P [R [Hf _]]].
assert (Hlive : forall n,
find_next ts V (iter_sp ts V n P) = Some (iter_sp ts V (S n) P)).
{ apply (orbit_live ts V P Hpos Hsem Hnb). exists R. exact Hf. }
destruct (period_hits ts V P Hpos Hsem Hlive) as [m [Hm Heq]].
assert (Hge : (3 <= m)%nat). { destruct m as [|[|[|m']]]. - lia.
- exfalso. assert (Hc0 : 0 < cross V P P).
{ apply (find_next_cross ts V P P Hpos).
assert (E0 : iter_sp ts V O P = P) by reflexivity. rewrite <- E0.
rewrite (Hlive O). rewrite Heq. reflexivity. } unfold cross in Hc0. lra.
- exfalso. assert (H1 : 0 < cross V P (iter_sp ts V 1 P)).
{ apply (find_next_cross ts V P (iter_sp ts V 1 P) Hpos). apply (Hlive O). }
assert (H2 : 0 < cross V (iter_sp ts V 1 P) P).
{ apply (find_next_cross ts V (iter_sp ts V 1 P) P Hpos).
rewrite (Hlive 1%nat). rewrite Heq. reflexivity. }
assert (cross V (iter_sp ts V 1 P) P = - cross V P (iter_sp ts V 1 P))
by (unfold cross; ring). lra. - lia. }
set (ps := nlist (fun k => iter_sp ts V k P) m).
apply (int_vertex_interior ts V ps). - apply ccw_from.
+ rewrite length_map. unfold ps. rewrite nlist_len. exact Hge.
+ intros i Hi.
rewrite length_map in Hi. unfold ps in Hi. rewrite nlist_len in Hi.
rewrite (nth_vsub ps V i). rewrite (nth_vsub ps V (S i)). rewrite vcross_vsub.
unfold ps. rewrite (nlist_nth m (fun k => iter_sp ts V k P) i V) by lia.
rewrite (nlist_nth m (fun k => iter_sp ts V k P) (S i) V) by lia.
apply (find_next_cross ts V (iter_sp ts V i P) (iter_sp ts V (S i) P) Hpos).
apply (Hlive i). + rewrite length_map.
rewrite (nth_vsub ps V ((length ps - 1)%nat)). rewrite (nth_vsub ps V O).
rewrite vcross_vsub. unfold ps. rewrite nlist_len.
rewrite (nlist_nth m (fun k => iter_sp ts V k P) ((m - 1)%nat) V) by lia.
rewrite (nlist_nth m (fun k => iter_sp ts V k P) O V) by lia. simpl.
apply (find_next_cross ts V (iter_sp ts V ((m - 1)%nat) P) P Hpos).
rewrite (Hlive ((m - 1)%nat)).
replace (S ((m - 1)%nat)) with m by lia. rewrite Heq. reflexivity.
- intros i Hi. unfold ps in Hi. rewrite nlist_len in Hi. unfold ps.
rewrite (nlist_nth m (fun k => iter_sp ts V k P) i V Hi).
destruct (Nat.eq_dec (S i) m) as [Hlast|Hmid].
+ replace i with ((m - 1)%nat) by lia.
assert (Ei : fan_next (nlist (fun k => iter_sp ts V k P) m) ((m - 1)%nat) =
fan_next (nlist (fun k => iter_sp ts V k P) m)
((length (nlist (fun k => iter_sp ts V k P) m) - 1)%nat)).
{ rewrite nlist_len. reflexivity. } rewrite Ei.
rewrite (fan_next_wrap (nlist (fun k => iter_sp ts V k P) m) V)
by (rewrite nlist_len; lia).
rewrite (nlist_nth m (fun k => iter_sp ts V k P) O V) by lia. simpl.
destruct (find_next_tri ts V (iter_sp ts V ((m - 1)%nat) P) P)
as [[[D E] F] [HinT HfT]]. { rewrite (Hlive ((m - 1)%nat)).
replace (S ((m - 1)%nat)) with m by lia. rewrite Heq. reflexivity. }
apply (fwd_fan ts D E F V (iter_sp ts V ((m - 1)%nat) P) P HinT HfT).
+ assert (Hs : (S i < m)%nat) by lia.
rewrite (fan_next_succ (nlist (fun k => iter_sp ts V k P) m) i V)
by (rewrite nlist_len; exact Hs).
rewrite (nlist_nth m (fun k => iter_sp ts V k P) (S i) V Hs).
destruct (find_next_tri ts V (iter_sp ts V i P) (iter_sp ts V (S i) P))
as [[[D E] F] [HinT HfT]]. { apply (Hlive i). }
apply (fwd_fan ts D E F V (iter_sp ts V i P) (iter_sp ts V (S i) P) HinT HfT).
Qed.
Theorem tin_interior_eq : forall ts X,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  interior_pt (tin_carrier ts) X <-> tin_int_cells ts X.
Proof.
intros ts X Hpos Hsem. split. - intros Hint.
destruct (proj1 (proj1 (tin_surface ts X Hpos Hsem))
(interior_in _ _ Hint)) as [Hi|Hb]. + exact Hi.
+ exfalso. apply (interior_not_boundary (tin_carrier ts) X Hint).
apply bd_edge_boundary; assumption. - intros [Ho|[Hs|Hv]].
+ destruct Ho as [[[A B] C] [Hin Hopen]].
apply (open_tri_interior ts A B C X Hin Hopen).
+ apply int_edge_interior; assumption.
+ apply internal_vert_interior; assumption. Qed.
Theorem tin_boundary_eq : forall ts X,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  boundary_pt (tin_carrier ts) X <-> tin_bd_cells ts X.
Proof.
intros ts X Hpos Hsem. split. - intros Hb.
destruct (proj1 (proj1 (tin_surface ts X Hpos Hsem))
(boundary_in_carrier ts X Hpos Hb)) as [Hi|Hbd].
+ exfalso. apply (interior_not_boundary (tin_carrier ts) X).
* apply (proj2 (tin_interior_eq ts X Hpos Hsem) Hi). * exact Hb.
+ exact Hbd. - apply bd_edge_boundary; assumption. Qed.
Lemma fan_centre_interior_fixtures : interior_pt (tin_carrier fan_ts) fanC.
Proof.
apply (proj2 (tin_interior_eq fan_ts fanC fan_tri_pos (proj1 tin_fan))).
exact fan_centre_int_cells_fixtures. Qed.
(* Assumptions: sig_not_dec, sig_forall_dec, functional_extensionality_dep. *)
Print Assumptions vcross_antisym.
Print Assumptions vcross_zero_r.
Print Assumptions vcross_neg.
Print Assumptions vsum_cross.
Print Assumptions no_strict_left.
Print Assumptions ccw_len.
Print Assumptions ccw_drop.
Print Assumptions not_all_pos.
Print Assumptions not_all_neg.
Print Assumptions consec_nth.
Print Assumptions fan_next_succ.
Print Assumptions fan_next_wrap.
Print Assumptions last_indep.
Print Assumptions nth_skip.
Print Assumptions last_nth.
Print Assumptions cycle_closure.
Print Assumptions first_le_at_spec.
Print Assumptions first_le_none.
Print Assumptions last_ge_at_spec.
Print Assumptions last_ge_spec.
Print Assumptions last_ge_acc_some.
Print Assumptions last_ge_none.
Print Assumptions ccw_cycle_covers.
Print Assumptions vsub_refl.
Print Assumptions vcross_vsub.
Print Assumptions nth_vsub.
Print Assumptions fan_next_vsub.
Print Assumptions ccw_consec.
Print Assumptions ccw_at.
Print Assumptions cross_qv.
Print Assumptions sector_ins.
Print Assumptions sector_carrier.
Print Assumptions fan_rad.
Print Assumptions int_vertex_interior.
Print Assumptions owns_dir_b_true.
Print Assumptions owns_vert.
Print Assumptions not_both_owns.
Print Assumptions edge_ne.
Print Assumptions mid_open.
Print Assumptions dir_owner.
Print Assumptions dir_uses_in.
Print Assumptions dir_uses_le1.
Print Assumptions edge_uses_dirs.
Print Assumptions uses_le2.
Print Assumptions incident_uses2.
Print Assumptions both_dirs.
Print Assumptions fwd_at_most.
Print Assumptions fwd_owns.
Print Assumptions fwd_rev_owns.
Print Assumptions fwd_cross.
Print Assumptions fwd_fan.
Print Assumptions owns_fwd_some.
Print Assumptions find_tri_in.
Print Assumptions find_tri_fwd.
Print Assumptions find_next_tri.
Print Assumptions find_next_cross.
Print Assumptions find_next_rev.
Print Assumptions dir_uses_ge2.
Print Assumptions fwd_spoke_unique.
Print Assumptions succ_inj.
Print Assumptions drop_shorter.
Print Assumptions find_tri_drop.
Print Assumptions find_tri_owns.
Print Assumptions fwd_exists.
Print Assumptions iter_next_eq.
Print Assumptions orbit_live.
Print Assumptions anchor.
Print Assumptions steps_le.
Print Assumptions iter_back.
Print Assumptions hit_step.
Print Assumptions period_hits.
Print Assumptions nlist_len.
Print Assumptions nlist_nth.
Print Assumptions ccw_from.
Print Assumptions internal_vert_interior.
Print Assumptions tin_interior_eq.
Print Assumptions tin_boundary_eq.
Print Assumptions fan_centre_interior_fixtures.
