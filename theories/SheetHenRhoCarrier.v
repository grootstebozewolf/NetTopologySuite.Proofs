(* ============================================================================
   NetTopologySuite.Proofs.SheetHenRhoCarrier
   ----------------------------------------------------------------------------
   Letter 2 slice: decisions, supports, carrier finiteness.
   SheetHenRho.v is the Require Export umbrella. claimId: none.
   Does not remint 0007-forall-bag. 3-axiom host.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List PeanoNat Bool Permutation ZArith.
From NTS.Proofs Require Import
  Distance Polynomial CircleChart SheetHenCookCore SheetHenCircEgg
  SheetHenBag ChartLineQuadratic HostCircChordOracle Atan2.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* -------------------------------------------------------------------------- *)
(* Real and point decisions. Req_EM_T is the dedup.                            *)
(* -------------------------------------------------------------------------- *)
Definition req_b (x y : R) : bool := if Req_EM_T x y then true else false.
Definition rle_b (x y : R) : bool := if Rle_dec x y then true else false.
Definition pt_eqb (p q : Point) : bool :=
  req_b (px p) (px q) && req_b (py p) (py q).
Lemma pt_eq_coords : forall p q, px p = px q -> py p = py q -> p = q.
Proof. intros [x1 y1] [x2 y2] Hx Hy. simpl in Hx, Hy. subst. reflexivity. Qed.
Lemma pt_eqb_true : forall p q, pt_eqb p q = true <-> p = q.
Proof.
  intros [x1 y1] [x2 y2]. unfold pt_eqb, req_b. simpl.
  destruct (Req_EM_T x1 x2) as [Hx|Hx]; destruct (Req_EM_T y1 y2) as [Hy|Hy];
    simpl; split; intro H.
  - subst. reflexivity.
  - reflexivity.
  - discriminate.
  - inversion H. congruence.
  - discriminate.
  - inversion H. congruence.
  - discriminate.
  - inversion H. congruence.
Qed.
Lemma req_b_true : forall x y, req_b x y = true <-> x = y.
Proof.
  intros x y. unfold req_b. destruct (Req_EM_T x y) as [E|N]; simpl; split; intro H.
  - exact E.
  - reflexivity.
  - discriminate.
  - congruence.
Qed.
Lemma rle_b_true : forall x y, rle_b x y = true <-> x <= y.
Proof.
  intros x y. unfold rle_b. destruct (Rle_dec x y) as [E|N]; simpl; split; intro H.
  - exact E.
  - reflexivity.
  - discriminate.
  - congruence.
Qed.
Fixpoint dedup (ps : list Point) : list Point :=
  match ps with
  | nil => nil
  | p :: tl =>
      let d := dedup tl in
      if existsb (pt_eqb p) d then d else p :: d
  end.
Lemma dedup_In : forall p ps, In p (dedup ps) <-> In p ps.
Proof.
  intros p ps. induction ps as [|q tl IH]; simpl; [tauto|].
  destruct (existsb (pt_eqb q) (dedup tl)) eqn:Eb.
  - rewrite IH. split; intro H.
    + right. exact H.
    + destruct H as [->|H]; [| exact H].
      apply existsb_exists in Eb. destruct Eb as [q' [Hin Hb]].
      apply pt_eqb_true in Hb. subst q'. apply IH. exact Hin.
  - simpl. rewrite IH. reflexivity.
Qed.
Lemma dedup_NoDup : forall ps, NoDup (dedup ps).
Proof.
  induction ps as [|p tl IH]; simpl; [constructor|].
  destruct (existsb (pt_eqb p) (dedup tl)) eqn:Eb.
  - exact IH.
  - constructor; [| exact IH].
    intro Hin.
    assert (E : existsb (pt_eqb p) (dedup tl) = true).
    { apply existsb_exists. exists p. split; [exact Hin|].
      apply pt_eqb_true. reflexivity. }
    congruence.
Qed.
Lemma dedup_filter_length : forall (k1 k2 : Point -> bool) (l : list Point),
  (forall p, k1 p = true -> k2 p = true) ->
  (length (dedup (filter k1 l)) <= length (dedup (filter k2 l)))%nat.
Proof.
  intros k1 k2 l Hk.
  apply NoDup_incl_length.
  - apply dedup_NoDup.
  - intros p Hin.
    rewrite dedup_In in Hin. apply filter_In in Hin. destruct Hin as [Hin Hb].
    rewrite dedup_In. apply filter_In. split; [exact Hin|]. apply Hk. exact Hb.
Qed.
(* -------------------------------------------------------------------------- *)
(* Supports, canonical order, unordered pairs.                                 *)
(* -------------------------------------------------------------------------- *)
Definition chord_eqb (a b : ChordEgg) : bool :=
  pt_eqb (ce_p0 a) (ce_p0 b) && pt_eqb (ce_p1 a) (ce_p1 b).
Definition circ_eqb (a b : CircularEgg) : bool :=
  pt_eqb (circ_o a) (circ_o b) && req_b (circ_r a) (circ_r b) &&
  req_b (circ_theta0 a) (circ_theta0 b) && req_b (circ_sweep a) (circ_sweep b).
Definition support_eqb (s1 s2 : BagSupport) : bool :=
  match s1, s2 with
  | SuppChord a, SuppChord b => chord_eqb a b
  | SuppCircle a, SuppCircle b => circ_eqb a b
  | _, _ => false
  end.
Lemma support_eqb_refl : forall s, support_eqb s s = true.
Proof.
  intros [c|c]; simpl.
  - unfold chord_eqb. apply andb_true_intro. split; apply pt_eqb_true; reflexivity.
  - unfold circ_eqb.
    apply andb_true_intro. split.
    + apply andb_true_intro. split.
      * apply andb_true_intro. split.
        -- apply pt_eqb_true. reflexivity.
        -- apply req_b_true. reflexivity.
      * apply req_b_true. reflexivity.
    + apply req_b_true. reflexivity.
Qed.
Lemma support_eqb_true : forall s1 s2, support_eqb s1 s2 = true <-> s1 = s2.
Proof.
  intros s1 s2. split; intro H.
  - destruct s1 as [a|a]; destruct s2 as [b|b]; simpl in H; try discriminate.
    + destruct a as [p0 p1], b as [q0 q1]. unfold chord_eqb in H. simpl in H.
      apply andb_prop in H. destruct H as [Hp Hq].
      apply pt_eqb_true in Hp, Hq. subst. reflexivity.
    + destruct a as [o r t s], b as [o' r' t' s']. unfold circ_eqb in H. simpl in H.
      apply andb_prop in H. destruct H as [H Hr].
      apply andb_prop in H. destruct H as [H Ht].
      apply andb_prop in H. destruct H as [Ho Hs].
      apply pt_eqb_true in Ho. apply req_b_true in Hs, Ht, Hr. subst. reflexivity.
  - subst s2. apply support_eqb_refl.
Qed.
Fixpoint supports_of (pcs : list BagPiece) : list BagSupport :=
  match pcs with
  | nil => nil
  | pc :: tl =>
      let s := bp_support pc in
      let rest := supports_of tl in
      if existsb (support_eqb s) rest then rest else s :: rest
  end.
Lemma supports_NoDup : forall pcs, NoDup (supports_of pcs).
Proof.
  induction pcs as [|pc tl IH]; simpl; [constructor|].
  destruct (existsb (support_eqb (bp_support pc)) (supports_of tl)) eqn:Eb.
  - exact IH.
  - constructor; [| exact IH].
    intro Hin.
    assert (E : existsb (support_eqb (bp_support pc)) (supports_of tl) = true).
    { apply existsb_exists. exists (bp_support pc).
      split; [exact Hin| apply support_eqb_refl]. }
    congruence.
Qed.
Lemma supports_in : forall pcs s,
  In s (supports_of pcs) <-> exists pc, In pc pcs /\ bp_support pc = s.
Proof.
  induction pcs as [|pc tl IH]; intros s; simpl.
  - split; [tauto| intros [pc [[] _]]].
  - destruct (existsb (support_eqb (bp_support pc)) (supports_of tl)) eqn:Eb.
    + rewrite IH. split.
      * intros [pc0 [Hin Hs]]. exists pc0. split; [right; exact Hin| exact Hs].
      * intros [pc0 [[->|Hin] Hs]].
        -- apply existsb_exists in Eb. destruct Eb as [s0 [Hin0 Heq]].
           apply support_eqb_true in Heq. rewrite <- Heq in Hin0.
           rewrite Hs in Hin0. apply (proj1 (IH s)) in Hin0. exact Hin0.
        -- exists pc0. split; [exact Hin| exact Hs].
    + simpl. rewrite IH. split.
      * intros [Heq|[pc0 [Hin Hs]]].
        -- exists pc. split; [left; reflexivity| exact Heq].
        -- exists pc0. split; [right; exact Hin| exact Hs].
      * intros [pc0 [[->|Hin] Hs]].
        -- left. exact Hs.
        -- right. exists pc0. split; [exact Hin| exact Hs].
Qed.
Definition support_reals (s : BagSupport) : list R :=
  match s with
  | SuppChord c =>
      [0; px (ce_p0 c); py (ce_p0 c); px (ce_p1 c); py (ce_p1 c)]
  | SuppCircle c =>
      [1; px (circ_o c); py (circ_o c); circ_r c; circ_theta0 c; circ_sweep c]
  end.
Lemma support_reals_inj : forall s1 s2,
  support_reals s1 = support_reals s2 -> s1 = s2.
Proof.
  intros [c1|c1] [c2|c2] H; simpl in H; try discriminate.
  - destruct c1 as [[x0 y0] [x1 y1]], c2 as [[u0 v0] [u1 v1]].
    simpl in H. inversion H. reflexivity.
  - destruct c1 as [[ox oy] r th sw], c2 as [[ux uy] r2 th2 sw2].
    simpl in H. inversion H. reflexivity.
Qed.
Fixpoint rlex_le (xs ys : list R) : bool :=
  match xs, ys with
  | nil, _ => true
  | _ :: _, nil => false
  | x :: xs', y :: ys' =>
      if Req_EM_T x y then rlex_le xs' ys' else if Rle_dec x y then true else false
  end.
Lemma rlex_refl : forall xs, rlex_le xs xs = true.
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity|].
  destruct (Req_EM_T x x) as [_|N]; [exact IH| congruence].
Qed.
Lemma rlex_eq : forall xs ys,
  rlex_le xs ys = true -> rlex_le ys xs = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] Hx Hy; simpl in *; try discriminate; try reflexivity.
  destruct (Req_EM_T x y) as [E|Nx]; destruct (Req_EM_T y x) as [E'|Ny].
  - subst. f_equal. apply IH; assumption.
  - subst. congruence.
  - subst. congruence.
  - destruct (Rle_dec x y) as [Hxy|Hxy]; destruct (Rle_dec y x) as [Hyx|Hyx];
      simpl in Hx, Hy; try discriminate. lra.
Qed.
Lemma rlex_total : forall xs ys, rlex_le xs ys = true \/ rlex_le ys xs = true.
Proof.
  induction xs as [|x xs IH]; intros [|y ys]; simpl; auto.
  destruct (Req_EM_T x y) as [E|Nx]; destruct (Req_EM_T y x) as [E'|Ny].
  - subst. apply IH.
  - subst. congruence.
  - subst. congruence.
  - destruct (Rle_dec x y) as [Hxy|Hxy]; destruct (Rle_dec y x) as [Hyx|Hyx]; simpl; auto. lra.
Qed.
Definition canon2 (s1 s2 : BagSupport) : BagSupport * BagSupport :=
  if rlex_le (support_reals s1) (support_reals s2) then (s1, s2) else (s2, s1).
Lemma canon_swap : forall s1 s2, canon2 s1 s2 = canon2 s2 s1.
Proof.
  intros s1 s2. unfold canon2.
  set (a := support_reals s1). set (b := support_reals s2).
  destruct (rlex_le a b) eqn:Hab; destruct (rlex_le b a) eqn:Hba.
  - assert (E : a = b) by (apply rlex_eq; assumption).
    apply support_reals_inj in E. subst. reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (rlex_total a b) as [H|H]; congruence.
Qed.
Fixpoint pair_sum (ss : list BagSupport) (f : BagSupport -> BagSupport -> nat) : nat :=
  match ss with
  | nil => 0%nat
  | s :: tl =>
      Nat.add (fold_right Nat.add 0%nat (map (f s) tl)) (pair_sum tl f)
  end.
Lemma sumN_perm : forall (A : Type) (g : A -> nat) l l',
  Permutation l l' ->
  fold_right Nat.add 0%nat (map g l) = fold_right Nat.add 0%nat (map g l').
Proof.
  intros A g l l' HP. induction HP; simpl.
  - reflexivity.
  - f_equal. exact IHHP.
  - rewrite Nat.add_assoc, Nat.add_assoc.
    rewrite (Nat.add_comm (g x) (g y)). reflexivity.
  - rewrite IHHP1, IHHP2. reflexivity.
Qed.
Lemma pair_sum_perm : forall ss ss' f,
  Permutation ss ss' ->
  (forall a b, f a b = f b a) ->
  pair_sum ss f = pair_sum ss' f.
Proof.
  intros ss ss' f HP. revert f. induction HP; intros f Hsym.
  - reflexivity.
  - simpl. rewrite IHHP by exact Hsym.
    erewrite sumN_perm; [reflexivity| exact HP].
  - simpl. rewrite (Hsym y x). lia.
  - rewrite IHHP1, IHHP2 by exact Hsym. reflexivity.
Qed.
Lemma pair_sum_le : forall ss f g,
  (forall a b, (f a b <= g a b)%nat) ->
  (pair_sum ss f <= pair_sum ss g)%nat.
Proof.
  intros ss f g Hle. induction ss as [|s tl IH]; simpl; [lia|].
  apply Nat.add_le_mono; [| exact IH].
  clear IH. induction tl as [|b tl IHb]; simpl; [lia|].
  apply Nat.add_le_mono; [apply Hle| exact IHb].
Qed.
Lemma dedup_length_le : forall ps, (length (dedup ps) <= length ps)%nat.
Proof.
  intro ps. apply NoDup_incl_length; [apply dedup_NoDup|].
  intro p. rewrite dedup_In. exact (fun H => H).
Qed.
(* -------------------------------------------------------------------------- *)
(* Angle reduction and the line-parameter quadratic.                           *)
(* -------------------------------------------------------------------------- *)
Lemma IZR_pos_INR : forall p, IZR (Z.pos p) = INR (Pos.to_nat p).
Proof. intro p. apply eq_sym, INR_IPR. Qed.
Lemma cos_period_Z : forall x (k : Z), cos (x + 2 * IZR k * PI) = cos x.
Proof.
  intros x k. destruct k as [|p|p].
  - replace (IZR Z0) with 0 by reflexivity.
    replace (x + 2 * 0 * PI) with x by ring. reflexivity.
  - rewrite (IZR_pos_INR p). apply cos_period.
  - rewrite IZR_NEG, (IZR_pos_INR p).
    set (n := Pos.to_nat p).
    assert (E : (x + 2 * (- INR n) * PI) + 2 * INR n * PI = x) by ring.
    pose proof (cos_period (x + 2 * (- INR n) * PI) n) as Hc.
    rewrite E in Hc. symmetry. exact Hc.
Qed.
Lemma sin_period_Z : forall x (k : Z), sin (x + 2 * IZR k * PI) = sin x.
Proof.
  intros x k. destruct k as [|p|p].
  - replace (IZR Z0) with 0 by reflexivity.
    replace (x + 2 * 0 * PI) with x by ring. reflexivity.
  - rewrite (IZR_pos_INR p). apply sin_period.
  - rewrite IZR_NEG, (IZR_pos_INR p).
    set (n := Pos.to_nat p).
    assert (E : (x + 2 * (- INR n) * PI) + 2 * INR n * PI = x) by ring.
    pose proof (sin_period (x + 2 * (- INR n) * PI) n) as Hs.
    rewrite E in Hs. symmetry. exact Hs.
Qed.
Definition reduce_angle (alpha : R) : R :=
  let n := Int_part ((alpha + PI) / (2 * PI)) in
  let s := alpha - 2 * PI * IZR n in
  if Req_EM_T s (- PI) then PI else s.
Lemma reduce_angle_spec : forall alpha,
  - PI < reduce_angle alpha <= PI /\
  cos (reduce_angle alpha) = cos alpha /\
  sin (reduce_angle alpha) = sin alpha.
Proof.
  intro alpha. unfold reduce_angle.
  set (x := (alpha + PI) / (2 * PI)).
  set (n := Int_part x).
  set (s := alpha - 2 * PI * IZR n).
  pose proof PI_RGT_0 as Hp.
  pose proof (base_Int_part x) as [Hle Hgt]. fold n in Hle, Hgt.
  assert (Hs : s = PI * (2 * (x - IZR n) - 1)).
  { unfold s, x. field. lra. }
  assert (Hslo : - PI <= s).
  { rewrite Hs. assert (0 <= 2 * (x - IZR n)) by lra. nra. }
  assert (Hshi : s < PI).
  { rewrite Hs. assert (2 * (x - IZR n) - 1 < 1) by lra. nra. }
  assert (Hcos : cos s = cos alpha).
  { unfold s. rewrite <- (cos_period_Z alpha (- n)%Z).
    replace (alpha + 2 * IZR (- n)%Z * PI) with (alpha - 2 * PI * IZR n).
    - reflexivity.
    - rewrite opp_IZR. ring. }
  assert (Hsin : sin s = sin alpha).
  { unfold s. rewrite <- (sin_period_Z alpha (- n)%Z).
    replace (alpha + 2 * IZR (- n)%Z * PI) with (alpha - 2 * PI * IZR n).
    - reflexivity.
    - rewrite opp_IZR. ring. }
  destruct (Req_EM_T s (- PI)) as [Heq|Hne].
  - split; [lra|]. rewrite Heq in Hcos, Hsin.
    rewrite cos_neg, cos_PI in Hcos. rewrite sin_neg, sin_PI in Hsin.
    split; [rewrite cos_PI; exact Hcos| rewrite sin_PI; rewrite <- Hsin; ring].
  - split; [lra| split; [exact Hcos| exact Hsin]].
Qed.
Lemma reduce_angle_period : forall alpha, exists k : Z,
  alpha = reduce_angle alpha + 2 * PI * IZR k.
Proof.
  intro alpha. unfold reduce_angle.
  set (x := (alpha + PI) / (2 * PI)).
  set (n := Int_part x).
  set (s := alpha - 2 * PI * IZR n).
  destruct (Req_EM_T s (- PI)) as [Heq|Hne].
  - exists (n - 1)%Z.
    assert (E : IZR (n - 1) = IZR n - 1).
    { replace (n - 1)%Z with (n + Z.opp 1)%Z by lia.
      rewrite plus_IZR, opp_IZR. ring. }
    rewrite E. unfold s in Heq. lra.
  - exists n. unfold s. ring.
Qed.
Lemma atan2_sin_cos : forall alpha,
  - PI < alpha <= PI -> atan2 (sin alpha) (cos alpha) = alpha.
Proof.
  intros alpha Hrng.
  assert (Hne : ~ (cos alpha = 0 /\ sin alpha = 0)).
  { intros [Hc Hs]. pose proof (sin2_cos2 alpha) as H. unfold Rsqr in H. nra. }
  assert (Hr1 : sqrt (cos alpha * cos alpha + sin alpha * sin alpha) = 1).
  { replace (cos alpha * cos alpha + sin alpha * sin alpha)
      with (Rsqr (sin alpha) + Rsqr (cos alpha)) by (unfold Rsqr; ring).
    rewrite sin2_cos2. apply sqrt_1. }
  symmetry. apply atan2_unique; try assumption.
  - rewrite Hr1. field.
  - rewrite Hr1. field.
Qed.
Definition ceil_Z (x : R) : Z :=
  let n := Int_part x in if Req_EM_T x (IZR n) then n else (n + 1)%Z.
Lemma ceil_bounds : forall x, x <= IZR (ceil_Z x) /\ IZR (ceil_Z x) < x + 1.
Proof.
  intro x. unfold ceil_Z. set (n := Int_part x).
  destruct (base_Int_part x) as [Hle Hlt]. fold n in Hle, Hlt.
  destruct (Req_EM_T x (IZR n)) as [E|N].
  - rewrite E. split; lra.
  - rewrite plus_IZR. split; lra.
Qed.
Lemma quadratic_at_most_two : forall a b c x y z,
  quadratic a b c x = 0 -> quadratic a b c y = 0 -> quadratic a b c z = 0 ->
  a <> 0 -> x = y \/ x = z \/ y = z.
Proof.
  intros a b c x y z Hx Hy Hz Ha.
  destruct (Req_EM_T x y) as [E|Nxy]; [left; exact E|].
  destruct (Req_EM_T x z) as [E|Nxz]; [right; left; exact E|].
  right; right.
  pose proof (quadratic_sum_two_roots a b c x y Hx Hy Ha Nxy) as Hxy.
  pose proof (quadratic_sum_two_roots a b c x z Hx Hz Ha Nxz) as Hxz.
  apply (Rmult_eq_reg_l a); [| exact Ha].
  replace (a * y) with (a * (x + y) - a * x) by ring.
  replace (a * z) with (a * (x + z) - a * x) by ring.
  rewrite Hxy, Hxz. ring.
Qed.
Lemma quad_formula : forall a b c x,
  a <> 0 -> quadratic a b c x = 0 ->
  let d := discriminant a b c in
  x = (- b + sqrt d) / (2 * a) \/ x = (- b - sqrt d) / (2 * a).
Proof.
  intros a b c x Ha Hx d.
  assert (Hs := discriminant_nonneg_for_real_roots_helper a b c x Ha Hx).
  assert (Hnn := discriminant_real_root_implies_nonneg a b c x Ha Hx).
  fold d in Hs, Hnn.
  assert (Hs2 := sqrt_sqrt _ Hnn).
  assert (Hprod : (2 * a * x + b - sqrt d) * (2 * a * x + b + sqrt d) = 0).
  { replace ((2 * a * x + b - sqrt d) * (2 * a * x + b + sqrt d))
      with ((2 * a * x + b) * (2 * a * x + b) - sqrt d * sqrt d) by ring.
    rewrite Hs, Hs2. unfold d, discriminant. ring. }
  assert (Ha2 : 2 * a <> 0) by nra.
  destruct (Rmult_integral _ _ Hprod) as [Hp|Hm].
  - left. assert (Ex : 2 * a * x = - b + sqrt d) by lra.
    apply (Rmult_eq_reg_l (2 * a)); [| exact Ha2].
    replace (2 * a * ((- b + sqrt d) / (2 * a))) with (- b + sqrt d) by (field; exact Ha).
    exact Ex.
  - right. assert (Ex : 2 * a * x = - b - sqrt d) by lra.
    apply (Rmult_eq_reg_l (2 * a)); [| exact Ha2].
    replace (2 * a * ((- b - sqrt d) / (2 * a))) with (- b - sqrt d) by (field; exact Ha).
    exact Ex.
Qed.
Definition cross2 (ax ay bx by_ : R) : R := ax * by_ - ay * bx.
Definition on_line (c : ChordEgg) (p : Point) : Prop := exists t, p = chord_eval c t.
Definition on_circle_carrier (c : CircularEgg) (p : Point) : Prop :=
  dist_sq (circ_o c) p = circ_r c * circ_r c.
Lemma chord_eval_lin : forall c t,
  px (chord_eval c t) = px (ce_p0 c) + t * chord_dx c /\
  py (chord_eval c t) = py (ce_p0 c) + t * chord_dy c.
Proof.
  intros [[x0 y0] [x1 y1]] t. unfold chord_eval, chord_dx, chord_dy. cbn.
  split; ring.
Qed.
Lemma circ_eval_carrier : forall c t, on_circle_carrier c (circ_eval c t).
Proof.
  intros c t. unfold on_circle_carrier, dist_sq, circ_eval. cbn.
  pose proof (sin2_cos2 (circ_theta0 c + t * circ_sweep c)) as H.
  unfold Rsqr in H. nra.
Qed.
Theorem line_line_le_1 : forall a b p q,
  cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b) <> 0 ->
  on_line a p -> on_line b p -> on_line a q -> on_line b q -> p = q.
Proof.
  intros a b p q Hcr [tp Hp] [sp Hp2] [tq Hq] [sq Hq2].
  destruct (chord_eval_lin a tp) as [Apx Apy]. rewrite <- Hp in Apx, Apy.
  destruct (chord_eval_lin a tq) as [Aqx Aqy]. rewrite <- Hq in Aqx, Aqy.
  destruct (chord_eval_lin b sp) as [Bpx Bpy]. rewrite <- Hp2 in Bpx, Bpy.
  destruct (chord_eval_lin b sq) as [Bqx Bqy]. rewrite <- Hq2 in Bqx, Bqy.
  assert (Dx : px p - px q = (tp - tq) * chord_dx a) by lra.
  assert (Dy : py p - py q = (tp - tq) * chord_dy a) by lra.
  assert (Ex : px p - px q = (sp - sq) * chord_dx b) by lra.
  assert (Ey : py p - py q = (sp - sq) * chord_dy b) by lra.
  assert (Hc : (tp - tq) * cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b) = 0).
  { unfold cross2.
    replace ((tp - tq) * (chord_dx a * chord_dy b - chord_dy a * chord_dx b))
      with ((px p - px q) * chord_dy b - (py p - py q) * chord_dx b).
    - rewrite Ex, Ey. ring.
    - rewrite Dx, Dy. ring. }
  destruct (Rmult_integral _ _ Hc) as [Hdt|Hbad].
  - assert (E : tp = tq) by lra. rewrite Hp, Hq, E. reflexivity.
  - exfalso. apply Hcr. exact Hbad.
Qed.
Definition lc_qa (s : ChordEgg) : R :=
  chord_dx s * chord_dx s + chord_dy s * chord_dy s.
Definition lc_qb (s : ChordEgg) (c : CircularEgg) : R :=
  2 * (chord_dx s * (px (ce_p0 s) - px (circ_o c)) +
       chord_dy s * (py (ce_p0 s) - py (circ_o c))).
Definition lc_qc (s : ChordEgg) (c : CircularEgg) : R :=
  let ax := px (ce_p0 s) - px (circ_o c) in
  let ay := py (ce_p0 s) - py (circ_o c) in
  ax * ax + ay * ay - circ_r c * circ_r c.
Lemma lc_param_root : forall s c t,
  quadratic (lc_qa s) (lc_qb s c) (lc_qc s c) t =
  dist_sq (circ_o c) (chord_eval s t) - circ_r c * circ_r c.
Proof.
  intros s c t. destruct (chord_eval_lin s t) as [Hx Hy].
  unfold quadratic, lc_qa, lc_qb, lc_qc, dist_sq. rewrite Hx, Hy. ring.
Qed.
Lemma lc_qa_nondeg : forall s, chord_nondeg s -> lc_qa s <> 0.
Proof.
  intros s Hnd. unfold lc_qa, chord_nondeg in *.
  destruct (Req_EM_T (chord_dx s) 0) as [Zx|Nx].
  - destruct (Req_EM_T (chord_dy s) 0) as [Zy|Ny].
    + exfalso. apply Hnd. rewrite Zx, Zy. reflexivity.
    + rewrite Zx. nra.
  - nra.
Qed.
Theorem line_circle_le_2 : forall s c p q u,
  chord_nondeg s ->
  on_line s p -> on_circle_carrier c p ->
  on_line s q -> on_circle_carrier c q ->
  on_line s u -> on_circle_carrier c u ->
  p = q \/ p = u \/ q = u.
Proof.
  intros s c p q u Hnd [tp Hp] Cp [tq Hq] Cq [tu Hu] Cu.
  pose proof (lc_qa_nondeg s Hnd) as Hqa.
  assert (Rp : quadratic (lc_qa s) (lc_qb s c) (lc_qc s c) tp = 0).
  { rewrite lc_param_root. rewrite <- Hp. unfold on_circle_carrier in Cp. lra. }
  assert (Rq : quadratic (lc_qa s) (lc_qb s c) (lc_qc s c) tq = 0).
  { rewrite lc_param_root. rewrite <- Hq. unfold on_circle_carrier in Cq. lra. }
  assert (Ru : quadratic (lc_qa s) (lc_qb s c) (lc_qc s c) tu = 0).
  { rewrite lc_param_root. rewrite <- Hu. unfold on_circle_carrier in Cu. lra. }
  destruct (quadratic_at_most_two _ _ _ tp tq tu Rp Rq Ru Hqa) as [E|[E|E]].
  - left. rewrite Hp, Hq, E. reflexivity.
  - right. left. rewrite Hp, Hu, E. reflexivity.
  - right. right. rewrite Hq, Hu, E. reflexivity.
Qed.
Theorem chart_qf_roots_le_2 : forall ox oy qx qy s0x s0y dx dy t1 t2 t3,
  zeta_qa qx qy s0x s0y dx dy <> 0 ->
  crs dx dy (zeta_abs_x ox oy qx qy t1 - s0x) (zeta_abs_y ox oy qx qy t1 - s0y) = 0 ->
  crs dx dy (zeta_abs_x ox oy qx qy t2 - s0x) (zeta_abs_y ox oy qx qy t2 - s0y) = 0 ->
  crs dx dy (zeta_abs_x ox oy qx qy t3 - s0x) (zeta_abs_y ox oy qx qy t3 - s0y) = 0 ->
  t1 = t2 \/ t1 = t3 \/ t2 = t3.
Proof.
  intros ox oy qx qy s0x s0y dx dy t1 t2 t3 Ha H1 H2 H3.
  apply (quadratic_at_most_two (zeta_qa qx qy s0x s0y dx dy)
    (zeta_qb ox oy qx qy dx dy) (zeta_qc ox oy qx qy s0x s0y dx dy) t1 t2 t3).
  - unfold quadratic, zeta_qf.
    pose proof (line_chart_quadratic ox oy qx qy s0x s0y dx dy t1) as E.
    rewrite H1, Rmult_0_l in E. symmetry. exact E.
  - unfold quadratic, zeta_qf.
    pose proof (line_chart_quadratic ox oy qx qy s0x s0y dx dy t2) as E.
    rewrite H2, Rmult_0_l in E. symmetry. exact E.
  - unfold quadratic, zeta_qf.
    pose proof (line_chart_quadratic ox oy qx qy s0x s0y dx dy t3) as E.
    rewrite H3, Rmult_0_l in E. symmetry. exact E.
  - exact Ha.
Qed.
Theorem chart_disc_geometric : forall ox oy qx qy s0x s0y dx dy,
  zeta_qb ox oy qx qy dx dy * zeta_qb ox oy qx qy dx dy
  - 4 * zeta_qa qx qy s0x s0y dx dy * zeta_qc ox oy qx qy s0x s0y dx dy
  = 4 * ((dx * dx + dy * dy) * dot (ox - qx) (oy - qy) (ox - qx) (oy - qy)
         - crs dx dy (ox - s0x) (oy - s0y) * crs dx dy (ox - s0x) (oy - s0y)).
Proof. intros. apply disc_identity. Qed.
Theorem line_circle_hits_le_2 : forall c s p1 p2 p3 t1 u1 t2 u2 t3 u3,
  circ_chord_host_scope c s ->
  on_circ c t1 p1 -> on_chord s u1 p1 ->
  on_circ c t2 p2 -> on_chord s u2 p2 ->
  on_circ c t3 p3 -> on_chord s u3 p3 ->
  p1 = p2 \/ p1 = p3 \/ p2 = p3.
Proof.
  intros c s p1 p2 p3 t1 u1 t2 u2 t3 u3 Hs A1 B1 A2 B2 A3 B3.
  destruct (I_ok_circ_chord_hit_sound c s p1 t1 u1
    (I_ok_circ_chord_hit_complete c s p1 t1 u1 Hs A1 B1)) as [S1 C1].
  destruct (I_ok_circ_chord_hit_sound c s p2 t2 u2
    (I_ok_circ_chord_hit_complete c s p2 t2 u2 Hs A2 B2)) as [S2 C2].
  destruct (I_ok_circ_chord_hit_sound c s p3 t3 u3
    (I_ok_circ_chord_hit_complete c s p3 t3 u3 Hs A3 B3)) as [S3 C3].
  apply (line_circle_le_2 s c p1 p2 p3).
  - apply Hs.
  - exists u1. exact (proj2 C1).
  - rewrite (proj2 S1). apply circ_eval_carrier.
  - exists u2. exact (proj2 C2).
  - rewrite (proj2 S2). apply circ_eval_carrier.
  - exists u3. exact (proj2 C3).
  - rewrite (proj2 S3). apply circ_eval_carrier.
Qed.
(* -------------------------------------------------------------------------- *)
(* Circle × circle, via the radical line. Inlined; ArcArcCircles is not host. *)
(* -------------------------------------------------------------------------- *)
Definition radical_axis_ux (O1 O2 : Point) : R := (px O2 - px O1) / dist O1 O2.
Definition radical_axis_uy (O1 O2 : Point) : R := (py O2 - py O1) / dist O1 O2.
Definition radical_axis_a (O1 O2 : Point) (r1 r2 : R) : R :=
  (dist O1 O2 * dist O1 O2 + r1 * r1 - r2 * r2) / (2 * dist O1 O2).
Definition radical_axis_h (O1 O2 : Point) (r1 r2 : R) : R :=
  sqrt (r1 * r1 - radical_axis_a O1 O2 r1 r2 * radical_axis_a O1 O2 r1 r2).
Definition radical_point_plus (O1 O2 : Point) (r1 r2 : R) : Point :=
  mkPoint (px O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_ux O1 O2
                  - radical_axis_h O1 O2 r1 r2 * radical_axis_uy O1 O2)
          (py O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_uy O1 O2
                  + radical_axis_h O1 O2 r1 r2 * radical_axis_ux O1 O2).
Definition radical_point_minus (O1 O2 : Point) (r1 r2 : R) : Point :=
  mkPoint (px O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_ux O1 O2
                  + radical_axis_h O1 O2 r1 r2 * radical_axis_uy O1 O2)
          (py O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_uy O1 O2
                  - radical_axis_h O1 O2 r1 r2 * radical_axis_ux O1 O2).
Theorem two_circles_radical_point_unique :
  forall (O1 O2 : Point) (r1 r2 : R) (X : Point),
    0 < dist O1 O2 ->
    dist_sq O1 X = r1 * r1 ->
    dist_sq O2 X = r2 * r2 ->
    X = radical_point_plus O1 O2 r1 r2 \/ X = radical_point_minus O1 O2 r1 r2.
Proof.
  intros O1 O2 r1 r2 X Hdpos HX1 HX2.
  unfold radical_point_plus, radical_point_minus,
         radical_axis_a, radical_axis_h, radical_axis_ux, radical_axis_uy.
  unfold radical_axis_a.
  set (d := dist O1 O2) in *.
  assert (Hd_ne : d <> 0) by lra.
  set (o1x := px O1). set (o1y := py O1).
  set (o2x := px O2). set (o2y := py O2).
  assert (Hdd : d * d = (o2x - o1x) * (o2x - o1x) + (o2y - o1y) * (o2y - o1y)).
  { unfold d, dist. rewrite sqrt_sqrt; [| apply dist_sq_nonneg].
    unfold dist_sq, o1x, o1y, o2x, o2y. ring. }
  set (ux := (o2x - o1x) / d). set (uy := (o2y - o1y) / d).
  assert (Hdux : d * ux = o2x - o1x) by (unfold ux; field; exact Hd_ne).
  assert (Hduy : d * uy = o2y - o1y) by (unfold uy; field; exact Hd_ne).
  assert (Hunit : ux * ux + uy * uy = 1).
  { assert (Heq : d * d * (ux * ux + uy * uy) = d * d).
    { transitivity ((d * ux) * (d * ux) + (d * uy) * (d * uy)); [ring|].
      rewrite Hdux, Hduy, Hdd. ring. }
    apply (Rmult_eq_reg_l (d * d)); [| nra]. ring_simplify. lra. }
  set (a := (d * d + r1 * r1 - r2 * r2) / (2 * d)).
  set (s1 := (px X - o1x) * ux + (py X - o1y) * uy).
  set (s2 := (py X - o1y) * ux - (px X - o1x) * uy).
  assert (Hdecomp_x : s1 * ux - s2 * uy = px X - o1x).
  { unfold s1, s2. transitivity ((px X - o1x) * (ux * ux + uy * uy)); [ring|].
    rewrite Hunit. ring. }
  assert (Hdecomp_y : s1 * uy + s2 * ux = py X - o1y).
  { unfold s1, s2. transitivity ((py X - o1y) * (ux * ux + uy * uy)); [ring|].
    rewrite Hunit. ring. }
  assert (HXeq1 : (px X - o1x) * (px X - o1x) + (py X - o1y) * (py X - o1y) = r1 * r1)
    by (unfold o1x, o1y; rewrite <- HX1; unfold dist_sq; ring).
  assert (Hpyth1 : (s1 * ux - s2 * uy) * (s1 * ux - s2 * uy)
                   + (s1 * uy + s2 * ux) * (s1 * uy + s2 * ux)
                   = (s1 * s1 + s2 * s2) * (ux * ux + uy * uy)) by ring.
  rewrite Hdecomp_x, Hdecomp_y, Hunit in Hpyth1.
  assert (Hsum1 : s1 * s1 + s2 * s2 = r1 * r1) by nra.
  assert (HY1eq : px X - o2x = (s1 - d) * ux - s2 * uy).
  { replace ((s1 - d) * ux - s2 * uy) with ((s1 * ux - s2 * uy) - d * ux) by ring.
    rewrite Hdecomp_x, Hdux. ring. }
  assert (HY2eq : py X - o2y = (s1 - d) * uy + s2 * ux).
  { replace ((s1 - d) * uy + s2 * ux) with ((s1 * uy + s2 * ux) - d * uy) by ring.
    rewrite Hdecomp_y, Hduy. ring. }
  assert (HYeq2 : (px X - o2x) * (px X - o2x) + (py X - o2y) * (py X - o2y) = r2 * r2)
    by (unfold o2x, o2y; rewrite <- HX2; unfold dist_sq; ring).
  assert (Hpyth2 : ((s1 - d) * ux - s2 * uy) * ((s1 - d) * ux - s2 * uy)
                   + ((s1 - d) * uy + s2 * ux) * ((s1 - d) * uy + s2 * ux)
                   = ((s1 - d) * (s1 - d) + s2 * s2) * (ux * ux + uy * uy)) by ring.
  rewrite Hunit in Hpyth2. rewrite <- HY1eq, <- HY2eq in Hpyth2.
  assert (Hsum2 : (s1 - d) * (s1 - d) + s2 * s2 = r2 * r2) by nra.
  assert (Hs1a : s1 = a).
  { assert (Hkey : 2 * s1 * d - d * d = r1 * r1 - r2 * r2) by nra.
    unfold a. apply (Rmult_eq_reg_l (2 * d)); [| nra]. field_simplify; nra. }
  assert (Hs2sq : s2 * s2 = r1 * r1 - a * a) by nra.
  assert (Hh2nn : 0 <= r1 * r1 - a * a) by nra.
  assert (Hhh : sqrt (r1 * r1 - a * a) * sqrt (r1 * r1 - a * a) = r1 * r1 - a * a)
    by (apply sqrt_sqrt; exact Hh2nn).
  set (h := sqrt (r1 * r1 - a * a)) in *.
  assert (Hs2h : (s2 - h) * (s2 + h) = 0) by nra.
  destruct (Rmult_integral _ _ Hs2h) as [Hplus|Hminus].
  - left. assert (Hs2eq : s2 = h) by lra.
    rewrite Hs1a, Hs2eq in Hdecomp_x, Hdecomp_y.
    apply pt_eq_coords; cbn [px py]; lra.
  - right. assert (Hs2eq : s2 = - h) by lra.
    rewrite Hs1a, Hs2eq in Hdecomp_x, Hdecomp_y.
    apply pt_eq_coords; cbn [px py]; lra.
Qed.
Theorem circle_circle_le_2 : forall (O1 O2 : Point) (r1 r2 : R) (X Y Z : Point),
  0 < dist O1 O2 ->
  dist_sq O1 X = r1 * r1 -> dist_sq O2 X = r2 * r2 ->
  dist_sq O1 Y = r1 * r1 -> dist_sq O2 Y = r2 * r2 ->
  dist_sq O1 Z = r1 * r1 -> dist_sq O2 Z = r2 * r2 ->
  X = Y \/ X = Z \/ Y = Z.
Proof.
  intros O1 O2 r1 r2 X Y Z Hd HX1 HX2 HY1 HY2 HZ1 HZ2.
  assert (HX : X = radical_point_plus O1 O2 r1 r2 \/ X = radical_point_minus O1 O2 r1 r2)
    by (apply two_circles_radical_point_unique; assumption).
  assert (HY : Y = radical_point_plus O1 O2 r1 r2 \/ Y = radical_point_minus O1 O2 r1 r2)
    by (apply two_circles_radical_point_unique; assumption).
  assert (HZ : Z = radical_point_plus O1 O2 r1 r2 \/ Z = radical_point_minus O1 O2 r1 r2)
    by (apply two_circles_radical_point_unique; assumption).
  destruct HX as [HX|HX]; destruct HY as [HY|HY]; destruct HZ as [HZ|HZ];
    subst; auto.
Qed.
Print Assumptions pt_eq_coords.
Print Assumptions pt_eqb_true.
Print Assumptions req_b_true.
Print Assumptions rle_b_true.
Print Assumptions dedup_In.
Print Assumptions dedup_NoDup.
Print Assumptions dedup_filter_length.
Print Assumptions support_eqb_refl.
Print Assumptions support_eqb_true.
Print Assumptions supports_NoDup.
Print Assumptions supports_in.
Print Assumptions support_reals_inj.
Print Assumptions rlex_refl.
Print Assumptions rlex_eq.
Print Assumptions rlex_total.
Print Assumptions canon_swap.
Print Assumptions sumN_perm.
Print Assumptions pair_sum_perm.
Print Assumptions pair_sum_le.
Print Assumptions dedup_length_le.
Print Assumptions IZR_pos_INR.
Print Assumptions cos_period_Z.
Print Assumptions sin_period_Z.
Print Assumptions reduce_angle_spec.
Print Assumptions reduce_angle_period.
Print Assumptions atan2_sin_cos.
Print Assumptions ceil_bounds.
Print Assumptions quadratic_at_most_two.
Print Assumptions quad_formula.
Print Assumptions chord_eval_lin.
Print Assumptions circ_eval_carrier.
Print Assumptions line_line_le_1.
Print Assumptions lc_param_root.
Print Assumptions lc_qa_nondeg.
Print Assumptions line_circle_le_2.
Print Assumptions chart_qf_roots_le_2.
Print Assumptions chart_disc_geometric.
Print Assumptions line_circle_hits_le_2.
Print Assumptions two_circles_radical_point_unique.
Print Assumptions circle_circle_le_2.
