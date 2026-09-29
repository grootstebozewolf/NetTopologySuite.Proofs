(* ============================================================================
   NetTopologySuite.Proofs.SheetHenRho
   ----------------------------------------------------------------------------
   ∀-bag letter 2 of 6. ρ and finiteness. claimId: none.
   Does not remint 0007-forall-bag and does not steal its witness.
   Does not redefine SheetHenBag objects. Does not touch
   LeftoverBagTermArm, LoopDischarged, or circ_leftover_bag_term_forall.
   Strict decrease and termination are letter 3.
   ρ is the sum, over Leibniz-distinct support pairs, of the length of
   an explicit candidate list deduplicated with Req_EM_T. A pair is
   counted once (triple point). Line×line contributes at most one
   point, line×circle at most two (host Hit iff incidence, C1
   quadratic), circle×circle at most two (radical line). Geometrically
   equal carriers contribute only the overlap-interval endpoints.
   rho_candidates_complete: a common window point that is not a vertex
   of both families is in that list, by class (transverse carriers from
   the finiteness roots; equal carriers only when the point is an
   overlap endpoint). #892's two half-turns contribute 0.
   3-axiom host. No Admitted / Axiom / Parameter.
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
(* -------------------------------------------------------------------------- *)
(* Explicit candidates. Overlap uses the convex hull of window-endpoint keys. *)
(* -------------------------------------------------------------------------- *)
Definition chord_dd (c : ChordEgg) : R :=
  chord_dx c * chord_dx c + chord_dy c * chord_dy c.
Definition quad_roots (a b c : R) : list R :=
  if req_b a 0 then nil
  else let d := discriminant a b c in
       if Rlt_dec d 0 then nil
       else if req_b d 0 then [(- b) / (2 * a)]
       else [(- b + sqrt d) / (2 * a); (- b - sqrt d) / (2 * a)].
Definition line_circle_pts (s : ChordEgg) (c : CircularEgg) : list Point :=
  if req_b (lc_qa s) 0 then if req_b (lc_qc s c) 0 then [ce_p0 s] else nil
  else map (chord_eval s) (quad_roots (lc_qa s) (lc_qb s c) (lc_qc s c)).
Definition cramer_t (a b : ChordEgg) : R :=
  cross2 (px (ce_p0 b) - px (ce_p0 a)) (py (ce_p0 b) - py (ce_p0 a))
         (chord_dx b) (chord_dy b)
  / cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b).
Definition line_line_pts (a b : ChordEgg) : list Point :=
  if req_b (cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b)) 0
  then nil else [chord_eval a (cramer_t a b)].
Definition same_line_b (a b : ChordEgg) : bool :=
  let dax := chord_dx a in let day := chord_dy a in
  let dbx := chord_dx b in let dby := chord_dy b in
  let vx := px (ce_p0 b) - px (ce_p0 a) in
  let vy := py (ce_p0 b) - py (ce_p0 a) in
  if negb (req_b dax 0 && req_b day 0) then
    req_b (cross2 dax day dbx dby) 0 && req_b (cross2 dax day vx vy) 0
  else if negb (req_b dbx 0 && req_b dby 0) then req_b (cross2 dbx dby vx vy) 0
  else pt_eqb (ce_p0 a) (ce_p0 b).
Definition same_circle_b (a b : CircularEgg) : bool :=
  pt_eqb (circ_o a) (circ_o b) && req_b (circ_r a * circ_r a) (circ_r b * circ_r b).
Definition on_both_b (c1 c2 : CircularEgg) (p : Point) : bool :=
  req_b (dist_sq (circ_o c1) p) (circ_r c1 * circ_r c1) &&
  req_b (dist_sq (circ_o c2) p) (circ_r c2 * circ_r c2).
Definition circle_circle_pts (c1 c2 : CircularEgg) : list Point :=
  if rle_b (dist (circ_o c1) (circ_o c2)) 0 then nil
  else filter (on_both_b c1 c2)
    [radical_point_plus (circ_o c1) (circ_o c2) (circ_r c1) (circ_r c2);
     radical_point_minus (circ_o c1) (circ_o c2) (circ_r c1) (circ_r c2)].
Definition align_k (target src : R) : Z :=
  Int_part ((target - src) / (2 * PI) + / 2).
Definition key_param (ref src : BagSupport) (t : R) : R :=
  match ref, src with
  | SuppChord rc, SuppChord sc =>
      if req_b (chord_dd rc) 0 then 0 else
      ((px (chord_eval sc t) - px (ce_p0 rc)) * chord_dx rc +
       (py (chord_eval sc t) - py (ce_p0 rc)) * chord_dy rc) / chord_dd rc
  | SuppCircle rc, SuppCircle sc =>
      let phase := if rle_b 0 (circ_r rc * circ_r sc) then 0 else PI in
      let kk := align_k (circ_theta0 rc) (circ_theta0 sc + phase) in
      circ_theta0 sc + t * circ_sweep sc + phase + 2 * PI * IZR kk
  | _, _ => 0
  end.
Definition point_of_key (ref : BagSupport) (k : R) : Point :=
  match ref with
  | SuppChord rc => if req_b (chord_dd rc) 0 then ce_p0 rc else chord_eval rc k
  | SuppCircle rc =>
      if req_b (circ_sweep rc) 0 then circ_eval rc 0
      else circ_eval rc ((k - circ_theta0 rc) / circ_sweep rc)
  end.
Definition piece_keys (ref src : BagSupport) (pc : BagPiece) : list R :=
  if support_eqb (bp_support pc) src then
    [key_param ref src (win_lo (bp_window pc)); key_param ref src (win_hi (bp_window pc))]
  else nil.
Definition all_keys (ref src : BagSupport) (pcs : list BagPiece) : list R :=
  flat_map (piece_keys ref src) pcs.
Fixpoint rmin_list (xs : list R) : R :=
  match xs with
  | nil => 0
  | x :: tl => match tl with nil => x | _ => Rmin x (rmin_list tl) end
  end.
Fixpoint rmax_list (xs : list R) : R :=
  match xs with
  | nil => 0
  | x :: tl => match tl with nil => x | _ => Rmax x (rmax_list tl) end
  end.
Definition overlap_pts (pcs : list BagPiece) (s1 s2 : BagSupport) : list Point :=
  match all_keys s1 s1 pcs, all_keys s1 s2 pcs with
  | k1 :: ks1, k2 :: ks2 =>
      let lo := Rmax (rmin_list (k1 :: ks1)) (rmin_list (k2 :: ks2)) in
      let hi := Rmin (rmax_list (k1 :: ks1)) (rmax_list (k2 :: ks2)) in
      if rle_b lo hi then dedup [point_of_key s1 lo; point_of_key s1 hi] else nil
  | _, _ => nil
  end.
Theorem overlap_endpoints_le_2 : forall pcs s1 s2,
  (length (overlap_pts pcs s1 s2) <= 2)%nat.
Proof.
  intros pcs s1 s2. unfold overlap_pts.
  destruct (all_keys s1 s1 pcs) as [|k1 ks1]; [simpl; lia|].
  destruct (all_keys s1 s2 pcs) as [|k2 ks2]; [simpl; lia|].
  destruct (rle_b (Rmax (rmin_list (k1 :: ks1)) (rmin_list (k2 :: ks2)))
                  (Rmin (rmax_list (k1 :: ks1)) (rmax_list (k2 :: ks2)))).
  - eapply Nat.le_trans; [apply dedup_length_le|]. cbn. lia.
  - cbn. lia.
Qed.
Definition raw_pts (pcs : list BagPiece) (s1 s2 : BagSupport) : list Point :=
  match s1, s2 with
  | SuppChord a, SuppChord b =>
      if same_line_b a b then overlap_pts pcs s1 s2 else line_line_pts a b
  | SuppChord a, SuppCircle c => line_circle_pts a c
  | SuppCircle c, SuppChord a => line_circle_pts a c
  | SuppCircle a, SuppCircle b =>
      if same_circle_b a b then overlap_pts pcs s1 s2 else circle_circle_pts a b
  end.
Lemma rmin_lb : forall xs y, In y xs -> rmin_list xs <= y.
Proof.
  induction xs as [|x tl IH]; intros y Hin; simpl in Hin; [contradiction|].
  destruct tl as [|z tl]; simpl.
  - destruct Hin as [->|[]]; lra.
  - destruct Hin as [->|Hin]; [apply Rmin_l|].
    apply Rle_trans with (rmin_list (z :: tl)); [apply Rmin_r| apply IH; exact Hin].
Qed.
Lemma rmin_in : forall xs, xs <> nil -> In (rmin_list xs) xs.
Proof.
  induction xs as [|x tl IH]; intros Hn; [congruence|].
  destruct tl as [|z tl]; simpl; [left; reflexivity|].
  destruct (Rle_dec x (rmin_list (z :: tl))) as [Hx|Hx].
  - rewrite Rmin_left by exact Hx. left. reflexivity.
  - rewrite Rmin_right by (apply Rlt_le, Rnot_le_lt; exact Hx).
    right. apply IH. discriminate.
Qed.
Lemma rmax_ub : forall xs y, In y xs -> y <= rmax_list xs.
Proof.
  induction xs as [|x tl IH]; intros y Hin; simpl in Hin; [contradiction|].
  destruct tl as [|z tl]; simpl.
  - destruct Hin as [->|[]]; lra.
  - destruct Hin as [->|Hin]; [apply Rmax_l|].
    apply Rle_trans with (rmax_list (z :: tl)); [apply IH; exact Hin| apply Rmax_r].
Qed.
Lemma rmax_in : forall xs, xs <> nil -> In (rmax_list xs) xs.
Proof.
  induction xs as [|x tl IH]; intros Hn; [congruence|].
  destruct tl as [|z tl]; simpl; [left; reflexivity|].
  destruct (Rle_dec (rmax_list (z :: tl)) x) as [Hx|Hx].
  - rewrite Rmax_left by exact Hx. left. reflexivity.
  - rewrite Rmax_right by (apply Rlt_le, Rnot_le_lt; exact Hx).
    right. apply IH. discriminate.
Qed.
Lemma key_affine : forall ref src lo hi u,
  key_param ref src (lo + u * (hi - lo)) =
  key_param ref src lo + u * (key_param ref src hi - key_param ref src lo).
Proof.
  intros ref src lo hi u. destruct ref as [rc|rc]; destruct src as [sc|sc]; simpl; try ring.
  - destruct (req_b (chord_dd rc) 0) eqn:Ed; [ring|].
    assert (Hd : chord_dd rc <> 0).
    { intro Z. unfold req_b in Ed. destruct (Req_EM_T (chord_dd rc) 0); congruence. }
    field. exact Hd.
Qed.
Lemma key_between : forall ref src lo hi u, 0 <= u <= 1 ->
  Rmin (key_param ref src lo) (key_param ref src hi) <=
  key_param ref src (lo + u * (hi - lo)) <=
  Rmax (key_param ref src lo) (key_param ref src hi).
Proof.
  intros ref src lo hi u Hu. rewrite key_affine.
  set (x := key_param ref src lo). set (y := key_param ref src hi).
  destruct (Rle_dec x y) as [Hxy|Hxy].
  - rewrite Rmin_left, Rmax_right by exact Hxy. split; nra.
  - assert (Hyx : y <= x) by lra. rewrite Rmin_right, Rmax_left by exact Hyx. split; nra.
Qed.
Lemma split_ends : forall pc u h, piece_realizes pc ->
  bp_support (fst (split_piece pc u h)) = bp_support pc /\
  bp_support (snd (split_piece pc u h)) = bp_support pc /\
  win_lo (bp_window (fst (split_piece pc u h))) = win_lo (bp_window pc) /\
  win_hi (bp_window (fst (split_piece pc u h))) = win_abs (bp_window pc) u /\
  win_lo (bp_window (snd (split_piece pc u h))) = win_abs (bp_window pc) u /\
  win_hi (bp_window (snd (split_piece pc u h))) = win_hi (bp_window pc).
Proof.
  intros [[src dst egg] sup w prov] u h Hr.
  destruct sup as [c|c]; destruct egg as [ch|ci|cl|co|nu];
    unfold piece_realizes in Hr; simpl in Hr; try contradiction.
  - subst ch. simpl. repeat split; reflexivity.
  - subst ci. simpl. repeat split; reflexivity.
Qed.
Lemma piece_key_end : forall ref src pc,
  bp_support pc = src ->
  In (key_param ref src (win_lo (bp_window pc))) (piece_keys ref src pc) /\
  In (key_param ref src (win_hi (bp_window pc))) (piece_keys ref src pc).
Proof.
  intros ref src pc Hs. unfold piece_keys. rewrite Hs, support_eqb_refl. simpl. auto.
Qed.
Lemma in_all_of : forall ref src pcs pc k,
  In pc pcs -> In k (piece_keys ref src pc) -> In k (all_keys ref src pcs).
Proof.
  intros. unfold all_keys. apply in_flat_map. exists pc. split; assumption.
Qed.
Lemma old_key_in_new : forall ref s pcs i j a b ti tj h k,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_realizes a -> piece_realizes b ->
  In k (all_keys ref s pcs) ->
  In k (all_keys ref s (progress_pieces pcs i j a b ti tj h)).
Proof.
  intros ref s pcs i j a b ti tj h k Hi Hj Hij Hra Hrb Hin.
  apply in_flat_map in Hin. destruct Hin as [pc [Hpc Hk]].
  destruct (In_nth_error _ _ Hpc) as [idx Hidx].
  destruct (split_ends a ti h Hra) as [Sa1 [Sa2 [La1 [La2 [La3 La4]]]]].
  destruct (split_ends b tj h Hrb) as [Sb1 [Sb2 [Lb1 [Lb2 [Lb3 Lb4]]]]].
  destruct (Nat.eq_dec idx i) as [->|Ni].
  - assert (Epc : pc = a) by (rewrite Hidx in Hi; inversion Hi; reflexivity). subst pc.
    unfold piece_keys in Hk. destruct (support_eqb (bp_support a) s) eqn:Eb;
      simpl in Hk; [| contradiction].
    destruct Hk as [Ek|[Ek|[]]].
    + apply (in_all_of _ _ _ (fst (split_piece a ti h))).
      * unfold progress_pieces, cooked_four. apply in_or_app. left. simpl. left. reflexivity.
      * unfold piece_keys. rewrite Sa1, Eb. simpl. left. rewrite La1. exact Ek.
    + apply (in_all_of _ _ _ (snd (split_piece a ti h))).
      * unfold progress_pieces, cooked_four. apply in_or_app. left. simpl. right. left. reflexivity.
      * unfold piece_keys. rewrite Sa2, Eb. simpl. right. left. rewrite La4. exact Ek.
  - destruct (Nat.eq_dec idx j) as [->|Nj].
    + assert (Epc : pc = b) by (rewrite Hidx in Hj; inversion Hj; reflexivity). subst pc.
      unfold piece_keys in Hk. destruct (support_eqb (bp_support b) s) eqn:Eb;
        simpl in Hk; [| contradiction].
      destruct Hk as [Ek|[Ek|[]]].
      * apply (in_all_of _ _ _ (fst (split_piece b tj h))).
        -- unfold progress_pieces, cooked_four. apply in_or_app. left. simpl. right. right. left. reflexivity.
        -- unfold piece_keys. rewrite Sb1, Eb. simpl. left. rewrite Lb1. exact Ek.
      * apply (in_all_of _ _ _ (snd (split_piece b tj h))).
        -- unfold progress_pieces, cooked_four. apply in_or_app. left. simpl. right. right. right. left. reflexivity.
        -- unfold piece_keys. rewrite Sb2, Eb. simpl. right. left. rewrite Lb4. exact Ek.
    + apply (in_all_of _ _ _ pc); [| exact Hk].
      unfold progress_pieces. apply in_or_app. right.
      apply (drop_pair_keeps i j pcs idx pc); assumption.
Qed.
Lemma parent_bound : forall ref s pcs pc u h k,
  In pc pcs -> piece_realizes pc -> 0 <= u <= 1 ->
  In k (piece_keys ref s (fst (split_piece pc u h)) ++
        piece_keys ref s (snd (split_piece pc u h))) ->
  match all_keys ref s pcs with
  | nil => False
  | _ => rmin_list (all_keys ref s pcs) <= k /\ k <= rmax_list (all_keys ref s pcs)
  end.
Proof.
  intros ref s pcs pc u h k Hin Hr Hu Hk. apply in_app_or in Hk. destruct Hk as [Hk|Hk].
  - unfold piece_keys in Hk.
    destruct (support_eqb (bp_support (fst (split_piece pc u h))) s) eqn:Eb;
      simpl in Hk; [| contradiction].
    destruct (split_ends pc u h Hr) as [S1 [_ [L1 [Mid [_ _]]]]].
    apply support_eqb_true in Eb. rewrite S1 in Eb.
    destruct (piece_key_end ref s pc Eb) as [Ilo Ihi].
    assert (Alo : In (key_param ref s (win_lo (bp_window pc))) (all_keys ref s pcs))
      by (apply in_all_of with pc; assumption).
    assert (Ahi : In (key_param ref s (win_hi (bp_window pc))) (all_keys ref s pcs))
      by (apply in_all_of with pc; assumption).
    destruct (all_keys ref s pcs) as [|? ?] eqn:E; [simpl in Alo; contradiction|].
    destruct Hk as [Ek|[Ek|[]]].
    + rewrite <- Ek, L1. split; [apply rmin_lb; exact Alo| apply rmax_ub; exact Alo].
    + rewrite <- Ek, Mid.
      assert (Hb := key_between ref s (win_lo (bp_window pc)) (win_hi (bp_window pc)) u Hu).
      replace (win_lo (bp_window pc) + u * (win_hi (bp_window pc) - win_lo (bp_window pc)))
        with (win_abs (bp_window pc) u) in Hb by (unfold win_abs; ring).
      destruct Hb as [Hlo Hhi]. split.
      * apply Rle_trans with (Rmin (key_param ref s (win_lo (bp_window pc)))
                                   (key_param ref s (win_hi (bp_window pc)))); [| exact Hlo].
        apply Rmin_glb; [apply rmin_lb; exact Alo| apply rmin_lb; exact Ahi].
      * apply Rle_trans with (Rmax (key_param ref s (win_lo (bp_window pc)))
                                   (key_param ref s (win_hi (bp_window pc)))); [exact Hhi|].
        apply Rmax_lub; [apply rmax_ub; exact Alo| apply rmax_ub; exact Ahi].
  - unfold piece_keys in Hk.
    destruct (support_eqb (bp_support (snd (split_piece pc u h))) s) eqn:Eb;
      simpl in Hk; [| contradiction].
    destruct (split_ends pc u h Hr) as [_ [S2 [_ [_ [Mid Hhi]]]]].
    apply support_eqb_true in Eb. rewrite S2 in Eb.
    destruct (piece_key_end ref s pc Eb) as [Ilo Ihi].
    assert (Alo : In (key_param ref s (win_lo (bp_window pc))) (all_keys ref s pcs))
      by (apply in_all_of with pc; assumption).
    assert (Ahi : In (key_param ref s (win_hi (bp_window pc))) (all_keys ref s pcs))
      by (apply in_all_of with pc; assumption).
    destruct (all_keys ref s pcs) as [|? ?] eqn:E; [simpl in Alo; contradiction|].
    destruct Hk as [Ek|[Ek|[]]].
    + rewrite <- Ek, Mid.
      assert (Hb := key_between ref s (win_lo (bp_window pc)) (win_hi (bp_window pc)) u Hu).
      replace (win_lo (bp_window pc) + u * (win_hi (bp_window pc) - win_lo (bp_window pc)))
        with (win_abs (bp_window pc) u) in Hb by (unfold win_abs; ring).
      destruct Hb as [Hblo Hbhi]. split.
      * apply Rle_trans with (Rmin (key_param ref s (win_lo (bp_window pc)))
                                   (key_param ref s (win_hi (bp_window pc)))); [| exact Hblo].
        apply Rmin_glb; [apply rmin_lb; exact Alo| apply rmin_lb; exact Ahi].
      * apply Rle_trans with (Rmax (key_param ref s (win_lo (bp_window pc)))
                                   (key_param ref s (win_hi (bp_window pc)))); [exact Hbhi|].
        apply Rmax_lub; [apply rmax_ub; exact Alo| apply rmax_ub; exact Ahi].
    + rewrite <- Ek, Hhi. split; [apply rmin_lb; exact Ahi| apply rmax_ub; exact Ahi].
Qed.
Lemma new_key_bound : forall ref s pcs i j a b ti tj h k,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_realizes a -> piece_realizes b -> 0 <= ti <= 1 -> 0 <= tj <= 1 ->
  In k (all_keys ref s (progress_pieces pcs i j a b ti tj h)) ->
  match all_keys ref s pcs with
  | nil => False
  | _ => rmin_list (all_keys ref s pcs) <= k /\ k <= rmax_list (all_keys ref s pcs)
  end.
Proof.
  intros ref s pcs i j a b ti tj h k Hi Hj Hij Hra Hrb Hti Htj Hin.
  apply in_flat_map in Hin. destruct Hin as [pc [Hpc Hk]].
  unfold progress_pieces in Hpc. apply in_app_or in Hpc. destruct Hpc as [H4|Hdrop].
  - unfold cooked_four in H4. simpl in H4.
    destruct H4 as [<-|[<-|[<-|[<-|[]]]]].
    + apply (parent_bound ref s pcs a ti h k (nth_error_In _ _ Hi) Hra Hti).
      apply in_or_app. left. exact Hk.
    + apply (parent_bound ref s pcs a ti h k (nth_error_In _ _ Hi) Hra Hti).
      apply in_or_app. right. exact Hk.
    + apply (parent_bound ref s pcs b tj h k (nth_error_In _ _ Hj) Hrb Htj).
      apply in_or_app. left. exact Hk.
    + apply (parent_bound ref s pcs b tj h k (nth_error_In _ _ Hj) Hrb Htj).
      apply in_or_app. right. exact Hk.
  - assert (Hold : In k (all_keys ref s pcs)).
    { apply in_all_of with pc; [| exact Hk]. exact (filter_idx_In _ _ _ _ _ Hdrop). }
    destruct (all_keys ref s pcs) as [|? ?] eqn:E; [simpl in Hold; contradiction|].
    split; [apply rmin_lb; exact Hold| apply rmax_ub; exact Hold].
Qed.
Lemma hull_progress : forall ref s pcs i j a b ti tj h,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_realizes a -> piece_realizes b -> 0 <= ti <= 1 -> 0 <= tj <= 1 ->
  let ks := all_keys ref s pcs in
  let ks' := all_keys ref s (progress_pieces pcs i j a b ti tj h) in
  rmin_list ks = rmin_list ks' /\ rmax_list ks = rmax_list ks' /\
  (ks = nil <-> ks' = nil).
Proof.
  intros ref s pcs i j a b ti tj h Hi Hj Hij Hra Hrb Hti Htj ks ks'.
  assert (Hold : forall k, In k ks -> In k ks').
  { intros k Hk. apply old_key_in_new with (i:=i) (j:=j) (a:=a) (b:=b) (ti:=ti) (tj:=tj) (h:=h); assumption. }
  assert (Hnew : forall k, In k ks' ->
    match ks with nil => False | _ => rmin_list ks <= k /\ k <= rmax_list ks end).
  { intros k Hk. apply new_key_bound with (i:=i) (j:=j) (a:=a) (b:=b) (ti:=ti) (tj:=tj) (h:=h); assumption. }
  destruct ks as [|x xs] eqn:Eks.
  - assert (N : ks' = nil).
    { destruct ks' as [|y ys]; [reflexivity|]. exfalso. apply (Hnew y). left. reflexivity. }
    rewrite N. simpl. split; [reflexivity| split; [reflexivity| tauto]].
  - assert (Hin : In (rmin_list (x :: xs)) ks') by (apply Hold, rmin_in; discriminate).
    assert (Hne' : ks' <> nil) by (intro Z; rewrite Z in Hin; simpl in Hin; contradiction).
    assert (Hrm : rmin_list ks' <= rmin_list (x :: xs)) by (apply rmin_lb; exact Hin).
    assert (Hrm2 : rmin_list (x :: xs) <= rmin_list ks').
    { pose proof (rmin_in ks' Hne') as Hm. destruct (Hnew _ Hm) as [H1 _]. exact H1. }
    assert (HinM : In (rmax_list (x :: xs)) ks') by (apply Hold, rmax_in; discriminate).
    assert (HrM : rmax_list (x :: xs) <= rmax_list ks') by (apply rmax_ub; exact HinM).
    assert (HrM2 : rmax_list ks' <= rmax_list (x :: xs)).
    { pose proof (rmax_in ks' Hne') as Hm. destruct (Hnew _ Hm) as [_ H2]. exact H2. }
    split; [lra| split; [lra| split; [intro; discriminate| intro Z; rewrite Z in Hne'; congruence]]].
Qed.

Lemma overlap_eq : forall pcs pcs' s1 s2,
  rmin_list (all_keys s1 s1 pcs) = rmin_list (all_keys s1 s1 pcs') ->
  rmax_list (all_keys s1 s1 pcs) = rmax_list (all_keys s1 s1 pcs') ->
  (all_keys s1 s1 pcs = nil <-> all_keys s1 s1 pcs' = nil) ->
  rmin_list (all_keys s1 s2 pcs) = rmin_list (all_keys s1 s2 pcs') ->
  rmax_list (all_keys s1 s2 pcs) = rmax_list (all_keys s1 s2 pcs') ->
  (all_keys s1 s2 pcs = nil <-> all_keys s1 s2 pcs' = nil) ->
  overlap_pts pcs s1 s2 = overlap_pts pcs' s1 s2.
Proof.
  intros pcs pcs' s1 s2 R1 X1 N1 R2 X2 N2. unfold overlap_pts.
  destruct (all_keys s1 s1 pcs) eqn:A, (all_keys s1 s1 pcs') eqn:B.
  - reflexivity.
  - exfalso. assert (E : r :: l = nil) by (apply (proj1 N1); reflexivity). discriminate.
  - exfalso. assert (E : r :: l = nil) by (apply (proj2 N1); reflexivity). discriminate.
  - destruct (all_keys s1 s2 pcs) eqn:C, (all_keys s1 s2 pcs') eqn:D.
    + reflexivity.
    + exfalso. assert (E : r1 :: l1 = nil) by (apply (proj1 N2); reflexivity). discriminate.
    + exfalso. assert (E : r1 :: l1 = nil) by (apply (proj2 N2); reflexivity). discriminate.
    + rewrite R1, X1, R2, X2. reflexivity.
Qed.

Lemma raw_progress : forall pcs i j a b ti tj h s1 s2,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_realizes a -> piece_realizes b -> 0 <= ti <= 1 -> 0 <= tj <= 1 ->
  raw_pts (progress_pieces pcs i j a b ti tj h) s1 s2 = raw_pts pcs s1 s2.
Proof.
  intros pcs i j a b ti tj h s1 s2 Hi Hj Hij Hra Hrb Hti Htj.
  destruct (hull_progress s1 s1 pcs i j a b ti tj h Hi Hj Hij Hra Hrb Hti Htj) as [M1 [X1 N1]].
  destruct (hull_progress s1 s2 pcs i j a b ti tj h Hi Hj Hij Hra Hrb Hti Htj) as [M2 [X2 N2]].
  destruct s1 as [c1|c1]; destruct s2 as [c2|c2]; simpl.
  - destruct (same_line_b c1 c2).
    + symmetry. apply overlap_eq; assumption.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (same_circle_b c1 c2).
    + symmetry. apply overlap_eq; assumption.
    + reflexivity.
Qed.
Definition chord_param (c : ChordEgg) (p : Point) : R :=
  ((px p - px (ce_p0 c)) * chord_dx c + (py p - py (ce_p0 c)) * chord_dy c) / chord_dd c.
Definition in_window_chord_b (c : ChordEgg) (w : Window) (p : Point) : bool :=
  if req_b (chord_dd c) 0 then pt_eqb p (ce_p0 c) && rle_b (win_lo w) (win_hi w)
  else let t := chord_param c p in
       (pt_eqb p (chord_eval c t) && rle_b (win_lo w) t) && rle_b t (win_hi w).
Lemma chord_eval_deg : forall c t, chord_dd c = 0 -> chord_eval c t = ce_p0 c.
Proof.
  intros c t Hz. destruct (chord_eval_lin c t) as [Hx Hy].
  destruct (sum_of_squares_zero _ _ Hz) as [Dx Dy].
  apply pt_eq_coords; [rewrite Hx, Dx | rewrite Hy, Dy]; ring.
Qed.
Lemma chord_param_eval : forall c t, chord_dd c <> 0 -> chord_param c (chord_eval c t) = t.
Proof.
  intros c t Hd. destruct (chord_eval_lin c t) as [Hx Hy].
  unfold chord_param, chord_dd in *. rewrite Hx, Hy.
  apply (Rmult_eq_reg_r (chord_dx c * chord_dx c + chord_dy c * chord_dy c)).
  - unfold Rdiv. rewrite Rmult_assoc, (Rinv_l _ Hd), Rmult_1_r. ring.
  - exact Hd.
Qed.
Lemma in_window_chord_spec : forall c w p,
  in_window_chord_b c w p = true <-> window_pts (SuppChord c) w p.
Proof.
  intros c w p. unfold in_window_chord_b, window_pts, support_at.
  destruct (req_b (chord_dd c) 0) eqn:Hd.
  - apply req_b_true in Hd. split.
    + intro H. apply andb_prop in H. destruct H as [Hp Hlo].
      apply pt_eqb_true in Hp. apply rle_b_true in Hlo.
      exists (win_lo w). split; [split; [apply Rle_refl | exact Hlo] |].
      rewrite (chord_eval_deg c (win_lo w) Hd). exact Hp.
    + intros [t [Ht Hp]]. apply andb_true_intro. split.
      * apply pt_eqb_true. rewrite Hp, (chord_eval_deg c t Hd). reflexivity.
      * apply rle_b_true. destruct Ht as [H1 H2]. lra.
  - split.
    + intro H. apply andb_prop in H. destruct H as [H1 Ht2].
      apply andb_prop in H1. destruct H1 as [Hp Ht1].
      exists (chord_param c p). split; [split; apply rle_b_true; assumption |].
      apply pt_eqb_true in Hp. exact Hp.
    + intros [u [Hu Hp]].
      assert (Hdd : chord_dd c <> 0).
      { intro Z. unfold req_b in Hd. destruct (Req_EM_T (chord_dd c) 0); congruence. }
      assert (Et : chord_param c p = u) by (rewrite Hp; apply chord_param_eval; exact Hdd).
      apply andb_true_intro. split; [apply andb_true_intro; split |].
      * apply pt_eqb_true. rewrite Et. exact Hp.
      * apply rle_b_true. rewrite Et. exact (proj1 Hu).
      * apply rle_b_true. rewrite Et. exact (proj2 Hu).
Qed.
Lemma lattice_in : forall t0 sig lo hi (m : Z), 0 < sig ->
  lo <= t0 + IZR m * sig /\ t0 + IZR m * sig <= hi ->
  let n := ceil_Z ((lo - t0) / sig) in
  lo <= t0 + IZR n * sig /\ t0 + IZR n * sig <= hi.
Proof.
  intros t0 sig lo hi m Hs [Hlo Hhi] n.
  set (x := (lo - t0) / sig).
  destruct (ceil_bounds x) as [Hcx Hcy].
  assert (Hx : x <= IZR m).
  { unfold x. eapply Rmult_le_reg_l; [exact Hs |].
    replace (sig * ((lo - t0) / sig)) with (lo - t0) by (field; lra). lra. }
  assert (Hnm : (n <= m)%Z).
  { unfold n. destruct (Z_le_gt_dec (ceil_Z x) m) as [Hle|Hgt]; [exact Hle| exfalso].
    assert (E : IZR (m + 1) <= IZR (ceil_Z x)) by (apply IZR_le; lia).
    rewrite plus_IZR in E. change (IZR 1) with 1 in E. lra. }
  assert (Ein : IZR n <= IZR m) by (apply IZR_le; exact Hnm).
  assert (Elo : lo = t0 + x * sig) by (unfold x; field; lra).
  split.
  - rewrite Elo. apply Rplus_le_compat_l. apply Rmult_le_compat_r; [lra |].
    unfold n. exact Hcx.
  - apply Rle_trans with (t0 + IZR m * sig); [| exact Hhi].
    apply Rplus_le_compat_l. apply Rmult_le_compat_r; lra.
Qed.
Lemma atan_reduce : forall r alpha, r <> 0 ->
  (if rle_b 0 r then atan2 (r * sin alpha) (r * cos alpha)
   else atan2 (- (r * sin alpha)) (- (r * cos alpha))) = reduce_angle alpha.
Proof.
  intros r alpha Hr. destruct (reduce_angle_spec alpha) as [Hrng [Hc Hs]].
  set (beta := reduce_angle alpha).
  assert (Hb : atan2 (sin beta) (cos beta) = beta) by (apply atan2_sin_cos; exact Hrng).
  destruct (rle_b 0 r) eqn:Hrle.
  - apply rle_b_true in Hrle. assert (Hpos : 0 < r) by lra.
    rewrite <- Hc, <- Hs. unfold beta.
    rewrite (atan2_pos_scale r (sin (reduce_angle alpha)) (cos (reduce_angle alpha)) Hpos).
    fold beta. exact Hb.
  - assert (Hneg : r < 0).
    { apply Rnot_le_lt. intro Hle. apply rle_b_true in Hle. rewrite Hle in Hrle. discriminate. }
    replace (- (r * sin alpha)) with ((- r) * sin alpha) by ring.
    replace (- (r * cos alpha)) with ((- r) * cos alpha) by ring.
    assert (Hpos : 0 < - r) by lra.
    rewrite <- Hc, <- Hs. unfold beta.
    rewrite (atan2_pos_scale (- r) (sin (reduce_angle alpha)) (cos (reduce_angle alpha)) Hpos).
    fold beta. exact Hb.
Qed.
Lemma circ_eval_abs_shift : forall c t (d : Z), circ_sweep c <> 0 ->
  circ_eval c (t + IZR d * (2 * PI / Rabs (circ_sweep c))) = circ_eval c t.
Proof.
  intros c t d Hs. unfold circ_eval. set (sw := circ_sweep c) in *.
  assert (Hnz : sw <> 0) by exact Hs. apply pt_eq_coords; cbn.
  - replace (circ_theta0 c + (t + IZR d * (2 * PI / Rabs sw)) * sw)
      with (circ_theta0 c + t * sw + IZR d * (2 * PI / Rabs sw) * sw) by ring.
    destruct (Rle_dec 0 sw) as [Hp|Hn].
    + rewrite (Rabs_pos_eq sw Hp).
      replace (IZR d * (2 * PI / sw) * sw) with (2 * IZR d * PI) by (field; exact Hnz).
      rewrite cos_period_Z. reflexivity.
    +       assert (Hlt : sw < 0) by (apply Rnot_le_lt; exact Hn).
      rewrite (Rabs_left sw Hlt).
      replace (IZR d * (2 * PI / - sw) * sw) with (2 * (- IZR d) * PI) by (field; exact Hnz).
      replace (circ_theta0 c + t * sw + 2 * (- IZR d) * PI)
        with (circ_theta0 c + t * sw + 2 * IZR (- d) * PI) by (rewrite opp_IZR; ring).
      rewrite cos_period_Z. reflexivity.
  - replace (circ_theta0 c + (t + IZR d * (2 * PI / Rabs sw)) * sw)
      with (circ_theta0 c + t * sw + IZR d * (2 * PI / Rabs sw) * sw) by ring.
    destruct (Rle_dec 0 sw) as [Hp|Hn].
    + rewrite (Rabs_pos_eq sw Hp).
      replace (IZR d * (2 * PI / sw) * sw) with (2 * IZR d * PI) by (field; exact Hnz).
      rewrite sin_period_Z. reflexivity.
    +       assert (Hlt : sw < 0) by (apply Rnot_le_lt; exact Hn).
      rewrite (Rabs_left sw Hlt).
      replace (IZR d * (2 * PI / - sw) * sw) with (2 * (- IZR d) * PI) by (field; exact Hnz).
      replace (circ_theta0 c + t * sw + 2 * (- IZR d) * PI)
        with (circ_theta0 c + t * sw + 2 * IZR (- d) * PI) by (rewrite opp_IZR; ring).
      rewrite sin_period_Z. reflexivity.
Qed.
Lemma circ_rep_true : forall c w p t,
  circ_r c <> 0 -> circ_sweep c <> 0 -> win_lo w <= t <= win_hi w -> p = circ_eval c t ->
  let lo := win_lo w in let hi := win_hi w in
  let r := circ_r c in let sw := circ_sweep c in
  let vx := px p - px (circ_o c) in let vy := py p - py (circ_o c) in
  let ang := if rle_b 0 r then atan2 vy vx else atan2 (- vy) (- vx) in
  let t0 := (ang - circ_theta0 c) / sw in
  let sig := 2 * PI / Rabs sw in
  let ts := t0 + IZR (ceil_Z ((lo - t0) / sig)) * sig in
  (rle_b lo ts && rle_b ts hi) && pt_eqb p (circ_eval c ts) = true.
Proof.
  intros c w p t Hr Hs Ht Hp. cbv zeta.
  set (lo := win_lo w). set (hi := win_hi w). set (r := circ_r c). set (sw := circ_sweep c).
  set (vx := px p - px (circ_o c)). set (vy := py p - py (circ_o c)).
  set (alpha := circ_theta0 c + t * sw).
  assert (Hvx : vx = r * cos alpha).
  { unfold vx, alpha, r, sw. rewrite Hp. unfold circ_eval. cbn. ring. }
  assert (Hvy : vy = r * sin alpha).
  { unfold vy, alpha, r, sw. rewrite Hp. unfold circ_eval. cbn. ring. }
  set (ang := if rle_b 0 r then atan2 vy vx else atan2 (- vy) (- vx)).
  assert (Hang : ang = reduce_angle alpha).
  { unfold ang. rewrite Hvx, Hvy. apply atan_reduce. exact Hr. }
  destruct (reduce_angle_period alpha) as [k Hk]. rewrite <- Hang in Hk.
  assert (Esw : t * sw = ang - circ_theta0 c + 2 * PI * IZR k).
  { replace (t * sw) with (alpha - circ_theta0 c) by (unfold alpha; ring).
    rewrite Hk. ring. }
  assert (Et : t = (ang - circ_theta0 c) / sw + IZR k * (2 * PI) / sw).
  { apply (Rmult_eq_reg_r sw); [| exact Hs]. unfold Rdiv. rewrite Rmult_plus_distr_r.
    rewrite !Rmult_assoc, !(Rinv_l sw Hs), !Rmult_1_r. rewrite Esw. ring. }
  set (t0 := (ang - circ_theta0 c) / sw). set (sig := 2 * PI / Rabs sw).
  assert (Hsig : 0 < sig).
  { unfold sig. apply Rdiv_lt_0_compat; [pose proof PI_RGT_0; lra | apply Rabs_pos_lt; exact Hs]. }
  assert (Hm : exists m : Z, t = t0 + IZR m * sig).
  { destruct (Rle_dec 0 sw) as [Hp0|Hn].
    - exists k. unfold t0, sig. rewrite (Rabs_pos_eq sw Hp0), Et.
      replace (IZR k * (2 * PI) / sw) with (IZR k * (2 * PI / sw)) by (field; exact Hs).
      ring.
    - assert (Hlt : sw < 0) by (apply Rnot_le_lt; exact Hn).
      exists (- k)%Z. unfold t0, sig. rewrite (Rabs_left sw Hlt), Et, opp_IZR.
      replace (IZR k * (2 * PI) / sw) with (- IZR k * (2 * PI / - sw)) by (field; exact Hs).
      ring. }
  destruct Hm as [m Hm].
  set (n := ceil_Z ((lo - t0) / sig)). set (ts := t0 + IZR n * sig).
  assert (Hin : lo <= ts /\ ts <= hi).
  { unfold ts, n. pose proof (lattice_in t0 sig lo hi m Hsig) as HL.
    rewrite <- Hm in HL. specialize (HL Ht). cbv zeta in HL. exact HL. }
  assert (Ets : ts = t + IZR (n - m) * sig).
  { unfold ts. rewrite Hm.
    replace (IZR n) with (IZR m + IZR (n - m)).
    - ring.
    - replace (n - m)%Z with (n + Z.opp m)%Z by lia. rewrite plus_IZR, opp_IZR. ring. }
  assert (Ev : circ_eval c ts = circ_eval c t).
  { rewrite Ets. unfold sig, sw. apply circ_eval_abs_shift. exact Hs. }
  apply andb_true_intro. split.
  - apply andb_true_intro. split; apply rle_b_true; tauto.
  - apply pt_eqb_true. rewrite Ev. exact Hp.
Qed.
Definition in_window_circ_b (c : CircularEgg) (w : Window) (p : Point) : bool :=
  let lo := win_lo w in let hi := win_hi w in
  let r := circ_r c in let sw := circ_sweep c in
  let vx := px p - px (circ_o c) in let vy := py p - py (circ_o c) in
  if negb (req_b (vx * vx + vy * vy) (r * r)) then false
  else if req_b r 0 then rle_b lo hi
  else if req_b sw 0 then pt_eqb p (circ_eval c lo) && rle_b lo hi
  else
    let ang := if rle_b 0 r then atan2 vy vx else atan2 (- vy) (- vx) in
    let t0 := (ang - circ_theta0 c) / sw in
    let sig := 2 * PI / Rabs sw in
    let ts := t0 + IZR (ceil_Z ((lo - t0) / sig)) * sig in
    (rle_b lo ts && rle_b ts hi) && pt_eqb p (circ_eval c ts).
Lemma in_window_circ_spec : forall c w p,
  in_window_circ_b c w p = true <-> window_pts (SuppCircle c) w p.
Proof.
  intros c w p. split.
  - intro Hb. unfold in_window_circ_b in Hb. cbv zeta in Hb.
    destruct (negb (req_b ((px p - px (circ_o c)) * (px p - px (circ_o c)) +
                           (py p - py (circ_o c)) * (py p - py (circ_o c)))
                          (circ_r c * circ_r c))) eqn:Hd; [discriminate|].
    apply negb_false_iff in Hd. apply req_b_true in Hd.
    destruct (req_b (circ_r c) 0) eqn:Hr.
    + apply req_b_true in Hr. apply rle_b_true in Hb.
      exists (win_lo w). split; [split; [apply Rle_refl| exact Hb]|].
      rewrite Hr in Hd. replace (0 * 0) with 0 in Hd by ring.
      destruct (sum_of_squares_zero _ _ Hd) as [Zx Zy].
      apply pt_eq_coords; unfold circ_eval; cbn; rewrite Hr.
      * assert (Ex : px p = px (circ_o c)) by lra. rewrite Ex. ring.
      * assert (Ey : py p = py (circ_o c)) by lra. rewrite Ey. ring.
    + destruct (req_b (circ_sweep c) 0) eqn:Hs.
      * apply andb_prop in Hb. destruct Hb as [Hp0 Hle].
        apply pt_eqb_true in Hp0. apply rle_b_true in Hle.
        exists (win_lo w). split; [split; [apply Rle_refl| exact Hle]| exact Hp0].
      * apply andb_prop in Hb. destruct Hb as [Hrng Hp0].
        apply andb_prop in Hrng. destruct Hrng as [Hlo Hhi].
        apply rle_b_true in Hlo. apply rle_b_true in Hhi. apply pt_eqb_true in Hp0.
        match type of Hlo with _ <= ?ts => exists ts end.
        split; [split; [exact Hlo| exact Hhi]| exact Hp0].
  - intros [t [Ht Hp]]. unfold support_at in Hp. unfold in_window_circ_b. cbv zeta.
    assert (Hon : (px p - px (circ_o c)) * (px p - px (circ_o c)) +
                  (py p - py (circ_o c)) * (py p - py (circ_o c)) =
                  circ_r c * circ_r c).
    { rewrite Hp. replace ((px (circ_eval c t) - px (circ_o c)) *
                           (px (circ_eval c t) - px (circ_o c)) +
                           (py (circ_eval c t) - py (circ_o c)) *
                           (py (circ_eval c t) - py (circ_o c)))
        with (dist_sq (circ_o c) (circ_eval c t)) by (unfold dist_sq; ring).
      apply circ_eval_carrier. }
    rewrite Hon.
    assert (Ereq : req_b (circ_r c * circ_r c) (circ_r c * circ_r c) = true)
      by (apply req_b_true; reflexivity).
    rewrite Ereq. cbn [negb].
    destruct (req_b (circ_r c) 0) eqn:Hr.
    + apply rle_b_true. destruct Ht as [H1 H2]. lra.
    + destruct (req_b (circ_sweep c) 0) eqn:Hs.
      * apply req_b_true in Hs. apply andb_true_intro. split.
        -- apply pt_eqb_true. rewrite Hp. unfold circ_eval.
           apply pt_eq_coords; cbn; rewrite Hs;
           replace (circ_theta0 c + t * 0) with (circ_theta0 c + win_lo w * 0) by ring;
           reflexivity.
        -- apply rle_b_true. destruct Ht as [H1 H2]. lra.
      * assert (Hr0 : circ_r c <> 0).
        { intro Z. apply (proj2 (req_b_true _ _)) in Z. rewrite Hr in Z. discriminate. }
        assert (Hs0 : circ_sweep c <> 0).
        { intro Z. apply (proj2 (req_b_true _ _)) in Z. rewrite Hs in Z. discriminate. }
        apply (circ_rep_true c w p t Hr0 Hs0 Ht Hp).
Qed.
Definition in_window_b (s : BagSupport) (w : Window) (p : Point) : bool :=
  match s with
  | SuppChord c => in_window_chord_b c w p
  | SuppCircle c => in_window_circ_b c w p
  end.
Lemma in_window_spec : forall s w p, in_window_b s w p = true <-> window_pts s w p.
Proof.
  intros [c|c]; [apply in_window_chord_spec| apply in_window_circ_spec].
Qed.
Definition in_image_b (pcs : list BagPiece) (s : BagSupport) (p : Point) : bool :=
  existsb (fun pc => support_eqb (bp_support pc) s && in_window_b s (bp_window pc) p) pcs.
Lemma in_image_spec : forall pcs s p,
  in_image_b pcs s p = true <-> support_image pcs s p.
Proof.
  intros pcs s p. unfold in_image_b, support_image. split.
  - intro H. apply existsb_exists in H. destruct H as [pc [Hin Hb]].
    apply andb_prop in Hb. destruct Hb as [Hs Hw].
    exists pc. split; [exact Hin|]. split; [apply support_eqb_true; exact Hs|].
    apply in_window_spec. exact Hw.
  - intros [pc [Hin [Hs Hw]]]. apply existsb_exists. exists pc. split; [exact Hin|].
    apply andb_true_intro. split; [apply support_eqb_true; exact Hs|].
    apply in_window_spec. exact Hw.
Qed.
Definition endpoint_b (pc : BagPiece) (p : Point) : bool :=
  pt_eqb p (support_at (bp_support pc) (win_lo (bp_window pc))) ||
  pt_eqb p (support_at (bp_support pc) (win_hi (bp_window pc))).
Lemma endpoint_spec : forall pc p, endpoint_b pc p = true <-> piece_endpoint pc p.
Proof.
  intros pc p. unfold endpoint_b, piece_endpoint. split.
  - intro H. apply orb_prop in H. destruct H as [H|H]; apply pt_eqb_true in H; [left|right]; exact H.
  - intros [H|H]; apply orb_true_intro; [left|right]; apply pt_eqb_true; exact H.
Qed.
Definition vertex_b (pcs : list BagPiece) (s : BagSupport) (p : Point) : bool :=
  existsb (fun pc => support_eqb (bp_support pc) s && endpoint_b pc p) pcs.
Lemma vertex_spec : forall pcs s p, vertex_b pcs s p = true <-> family_vertex pcs s p.
Proof.
  intros pcs s p. unfold vertex_b, family_vertex. split.
  - intro H. apply existsb_exists in H. destruct H as [pc [Hin Hb]].
    apply andb_prop in Hb. destruct Hb as [Hs He].
    exists pc. split; [exact Hin|]. split; [apply support_eqb_true; exact Hs|].
    apply endpoint_spec. exact He.
  - intros [pc [Hin [Hs He]]]. apply existsb_exists. exists pc. split; [exact Hin|].
    apply andb_true_intro. split; [apply support_eqb_true; exact Hs|].
    apply endpoint_spec. exact He.
Qed.
Definition keep_b (pcs : list BagPiece) (s1 s2 : BagSupport) (p : Point) : bool :=
  (in_image_b pcs s1 p && in_image_b pcs s2 p) &&
  negb (vertex_b pcs s1 p && vertex_b pcs s2 p).
Definition counted (pcs : list BagPiece) (s1 s2 : BagSupport) : list Point :=
  let '(a, b) := canon2 s1 s2 in dedup (filter (keep_b pcs a b) (raw_pts pcs a b)).
Lemma counted_sym : forall pcs s1 s2, counted pcs s1 s2 = counted pcs s2 s1.
Proof. intros. unfold counted. rewrite canon_swap. reflexivity. Qed.
Definition rho_pcs (pcs : list BagPiece) : nat :=
  pair_sum (supports_of pcs) (fun x y => length (counted pcs x y)).
Definition rho (b : SheetBag) : nat :=
  match b with BagLive _ pcs => rho_pcs pcs | BagDeclined _ => 0%nat end.
Lemma supports_progress_perm : forall pcs i j a b ti tj h,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_realizes a -> piece_realizes b ->
  Permutation (supports_of (progress_pieces pcs i j a b ti tj h)) (supports_of pcs).
Proof.
  intros pcs i j a b ti tj h Hi Hj Hij Hra Hrb.
  apply NoDup_Permutation; try apply supports_NoDup. intro s. rewrite !supports_in. split.
  - intros [pc [Hin Hs]]. unfold progress_pieces in Hin. apply in_app_or in Hin.
    destruct Hin as [Hf|Hk].
    + unfold cooked_four in Hf. simpl in Hf.
      destruct Hf as [<-|[<-|[<-|[<-|[]]]]].
      * destruct (split_ends a ti h Hra) as [Ea _]. exists a.
        split; [exact (nth_error_In _ _ Hi)|]. rewrite <- Ea. exact Hs.
      * destruct (split_ends a ti h Hra) as [_ [Ea _]]. exists a.
        split; [exact (nth_error_In _ _ Hi)|]. rewrite <- Ea. exact Hs.
      * destruct (split_ends b tj h Hrb) as [Eb _]. exists b.
        split; [exact (nth_error_In _ _ Hj)|]. rewrite <- Eb. exact Hs.
      * destruct (split_ends b tj h Hrb) as [_ [Eb _]]. exists b.
        split; [exact (nth_error_In _ _ Hj)|]. rewrite <- Eb. exact Hs.
    + exists pc. split; [exact (filter_idx_In _ _ _ _ _ Hk)| exact Hs].
  - intros [pc [Hin Hs]]. destruct (In_nth_error _ _ Hin) as [k Hk].
    destruct (Nat.eq_dec k i) as [->|Hki].
    + assert (Epc : pc = a) by (rewrite Hk in Hi; inversion Hi; reflexivity). subst pc.
      destruct (split_ends a ti h Hra) as [Ea _].
      exists (fst (split_piece a ti h)). split.
      * unfold progress_pieces. apply in_or_app. left. unfold cooked_four. simpl. left. reflexivity.
      * rewrite Ea. exact Hs.
    + destruct (Nat.eq_dec k j) as [->|Hkj].
      * assert (Epc : pc = b) by (rewrite Hk in Hj; inversion Hj; reflexivity). subst pc.
        destruct (split_ends b tj h Hrb) as [Eb _].
        exists (fst (split_piece b tj h)). split.
        { unfold progress_pieces. apply in_or_app. left. unfold cooked_four.
          simpl. right. right. left. reflexivity. }
        rewrite Eb. exact Hs.
      * exists pc. split.
        { unfold progress_pieces. apply in_or_app. right.
          apply (drop_pair_keeps i j pcs k pc); assumption. }
        exact Hs.
Qed.
Lemma keep_step : forall pcs i j a b p0 ti tj h s1 s2 p,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_wf a -> piece_wf b ->
  I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p0 ti tj) ->
  progress_hit pcs a b (IHit p0 ti tj) ->
  keep_b (progress_pieces pcs i j a b ti tj h) s1 s2 p = true ->
  keep_b pcs s1 s2 p = true.
Proof.
  intros pcs i j a b p0 ti tj h s1 s2 p Hi Hj Hij Hwfa Hwfb Hok Hpr Hkeep.
  unfold progress_hit in Hpr.
  set (pcs' := progress_pieces pcs i j a b ti tj h) in *.
  unfold keep_b in Hkeep. apply andb_prop in Hkeep. destruct Hkeep as [Himg Hneg].
  apply andb_prop in Himg. destruct Himg as [Hi1 Hi2]. apply negb_true_iff in Hneg.
  apply andb_true_intro. split.
  - apply andb_true_intro. split; apply in_image_spec;
      apply (proj2 (progress_preserves_support_image pcs i j a b p0 ti tj h _ p
        Hi Hj Hij Hwfa Hwfb Hok)); apply in_image_spec; assumption.
  - apply negb_true_iff.
    destruct (vertex_b pcs s1 p && vertex_b pcs s2 p) eqn:Ev; [| reflexivity].
    exfalso. apply andb_prop in Ev. destruct Ev as [V1b V2b].
    apply vertex_spec in V1b. apply vertex_spec in V2b.
    assert (N1 : family_vertex pcs' s1 p)
      by (eapply progress_vertices_mono; eassumption).
    assert (N2 : family_vertex pcs' s2 p)
      by (eapply progress_vertices_mono; eassumption).
    destruct (progress_vertices_only_adds pcs i j a b p0 ti tj h s1 p Hi Hj Hwfa Hwfb Hok N1)
      as [_| Heq].
    + assert (Bad : vertex_b pcs' s1 p && vertex_b pcs' s2 p = true)
        by (apply andb_true_intro; split; apply vertex_spec; assumption).
      rewrite Bad in Hneg. discriminate.
    + assert (Bad : vertex_b pcs' s1 p && vertex_b pcs' s2 p = true)
        by (apply andb_true_intro; split; apply vertex_spec; assumption).
      subst p. rewrite Bad in Hneg. discriminate.
Qed.
Theorem rho_step_nonincreasing : forall b b', bag_step b b' -> (rho b' <= rho b)%nat.
Proof.
  intros b b' [Hp|Hd].
  - destruct Hp as [sh pcs i j a b0 p ti tj h Hi Hj Hij Hwfa Hwfb Hok Hpr].
    simpl. set (pcs' := progress_pieces pcs i j a b0 ti tj h). unfold rho_pcs.
    destruct (hit_param_in_unit a b0 p ti tj (proj1 Hwfa) (proj1 Hwfb) Hok) as [Hti Htj].
    assert (Hperm : Permutation (supports_of pcs') (supports_of pcs)).
    { apply (supports_progress_perm pcs i j a b0 ti tj h Hi Hj Hij (proj1 Hwfa) (proj1 Hwfb)). }
    assert (Hsym : forall x y, length (counted pcs' x y) = length (counted pcs' y x)).
    { intros x y. f_equal. apply counted_sym. }
    rewrite (pair_sum_perm _ _ _ Hperm Hsym). apply pair_sum_le. intros x y.
    unfold counted. destruct (canon2 x y) as [u v].
    assert (Er : raw_pts pcs' u v = raw_pts pcs u v).
    { apply (raw_progress pcs i j a b0 ti tj h u v Hi Hj Hij (proj1 Hwfa) (proj1 Hwfb) Hti Htj). }
    rewrite Er. apply dedup_filter_length. intros q Hq.
    apply (keep_step pcs i j a b0 p ti tj h u v q); assumption.
  - destruct Hd; simpl; [apply Nat.le_0_l| apply Nat.le_refl].
Qed.
(* -------------------------------------------------------------------------- *)
(* Completeness: a common window point is a candidate, by class.              *)
(* Equal carriers list overlap endpoints only, not the open interval.        *)
(* -------------------------------------------------------------------------- *)
Lemma image_on_line : forall pcs c p,
  support_image pcs (SuppChord c) p -> on_line c p.
Proof.
  intros pcs c p [pc [_ [_ [t [_ Hp]]]]].
  unfold support_at in Hp. exists t. exact Hp.
Qed.
Lemma image_on_circle : forall pcs c p,
  support_image pcs (SuppCircle c) p -> on_circle_carrier c p.
Proof.
  intros pcs c p [pc [_ [_ [t [_ Hp]]]]].
  unfold support_at in Hp. rewrite Hp. apply circ_eval_carrier.
Qed.
Lemma cross_zero_same_line : forall a b p,
  on_line a p -> on_line b p ->
  cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b) = 0 ->
  same_line_b a b = true.
Proof.
  intros a b p [ta Ha] [tb Hb] Hcr.
  destruct (chord_eval_lin a ta) as [Ax Ay]. rewrite <- Ha in Ax, Ay.
  destruct (chord_eval_lin b tb) as [Bx By]. rewrite <- Hb in Bx, By.
  assert (Dx : px (ce_p0 b) - px (ce_p0 a) = ta * chord_dx a - tb * chord_dx b) by lra.
  assert (Dy : py (ce_p0 b) - py (ce_p0 a) = ta * chord_dy a - tb * chord_dy b) by lra.
  assert (Hcda : cross2 (chord_dx a) (chord_dy a)
                        (px (ce_p0 b) - px (ce_p0 a))
                        (py (ce_p0 b) - py (ce_p0 a)) = 0).
  { unfold cross2. rewrite Dx, Dy.
    replace (chord_dx a * (ta * chord_dy a - tb * chord_dy b)
             - chord_dy a * (ta * chord_dx a - tb * chord_dx b))
      with (- tb * (chord_dx a * chord_dy b - chord_dy a * chord_dx b)) by ring.
    unfold cross2 in Hcr. rewrite Hcr. ring. }
  assert (Hcdv : cross2 (chord_dx b) (chord_dy b)
                        (px (ce_p0 b) - px (ce_p0 a))
                        (py (ce_p0 b) - py (ce_p0 a)) = 0).
  { unfold cross2. rewrite Dx, Dy.
    replace (chord_dx b * (ta * chord_dy a - tb * chord_dy b)
             - chord_dy b * (ta * chord_dx a - tb * chord_dx b))
      with (- ta * (chord_dx a * chord_dy b - chord_dy a * chord_dx b)) by ring.
    unfold cross2 in Hcr. rewrite Hcr. ring. }
  unfold same_line_b. cbn zeta.
  destruct (req_b (chord_dx a) 0 && req_b (chord_dy a) 0) eqn:Eda; simpl.
  - destruct (req_b (chord_dx b) 0 && req_b (chord_dy b) 0) eqn:Edb; simpl.
    + apply andb_prop in Eda. destruct Eda as [Eax Eay].
      apply req_b_true in Eax. apply req_b_true in Eay.
      apply andb_prop in Edb. destruct Edb as [Ebx Eby].
      apply req_b_true in Ebx. apply req_b_true in Eby.
      assert (Hdda : chord_dd a = 0) by (unfold chord_dd; rewrite Eax, Eay; ring).
      assert (Hddb : chord_dd b = 0) by (unfold chord_dd; rewrite Ebx, Eby; ring).
      apply pt_eqb_true.
      rewrite <- (chord_eval_deg a ta Hdda).
      rewrite <- (chord_eval_deg b tb Hddb).
      rewrite <- Ha, <- Hb. reflexivity.
    + apply req_b_true. exact Hcdv.
  - apply andb_true_intro. split; apply req_b_true; [exact Hcr| exact Hcda].
Qed.
Lemma not_same_cross : forall a b p,
  on_line a p -> on_line b p -> same_line_b a b = false ->
  cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b) <> 0.
Proof.
  intros a b p Ha Hb Hs Hz.
  assert (E : same_line_b a b = true) by (apply (cross_zero_same_line a b p); assumption).
  congruence.
Qed.
Lemma cramer_param : forall a b t s,
  cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b) <> 0 ->
  chord_eval a t = chord_eval b s ->
  t = cramer_t a b.
Proof.
  intros a b t s Hcr Heq.
  destruct (chord_eval_lin a t) as [Ax Ay].
  destruct (chord_eval_lin b s) as [Bx By].
  assert (Ex : px (chord_eval a t) = px (chord_eval b s)) by (rewrite Heq; reflexivity).
  assert (Ey : py (chord_eval a t) = py (chord_eval b s)) by (rewrite Heq; reflexivity).
  rewrite Ax, Bx in Ex. rewrite Ay, By in Ey.
  assert (Dx : t * chord_dx a - s * chord_dx b = px (ce_p0 b) - px (ce_p0 a)) by lra.
  assert (Dy : t * chord_dy a - s * chord_dy b = py (ce_p0 b) - py (ce_p0 a)) by lra.
  assert (Hc : t * cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b)
               = cross2 (px (ce_p0 b) - px (ce_p0 a)) (py (ce_p0 b) - py (ce_p0 a))
                        (chord_dx b) (chord_dy b)).
  { unfold cross2. rewrite <- Dx, <- Dy. ring. }
  unfold cramer_t.
  apply (Rmult_eq_reg_l (cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b)));
    [| exact Hcr].
  replace (cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b) *
           (cross2 (px (ce_p0 b) - px (ce_p0 a)) (py (ce_p0 b) - py (ce_p0 a))
                   (chord_dx b) (chord_dy b)
            / cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b)))
    with (cross2 (px (ce_p0 b) - px (ce_p0 a)) (py (ce_p0 b) - py (ce_p0 a))
                 (chord_dx b) (chord_dy b)) by (field; exact Hcr).
  rewrite <- Hc. ring.
Qed.
Lemma line_line_in_raw : forall a b p,
  on_line a p -> on_line b p -> same_line_b a b = false ->
  In p (line_line_pts a b).
Proof.
  intros a b p Ha Hb Hs.
  pose proof (not_same_cross a b p Ha Hb Hs) as Hcr.
  unfold line_line_pts.
  destruct (req_b (cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b)) 0) eqn:Ec.
  - apply req_b_true in Ec. contradiction.
  - destruct Ha as [t Ht]. destruct Hb as [s Hs2].
    assert (Et : t = cramer_t a b).
    { apply (cramer_param a b t s); [exact Hcr| rewrite <- Ht, <- Hs2; reflexivity]. }
    simpl. left. rewrite Ht, Et. reflexivity.
Qed.
Lemma quad_root_in : forall a b c x,
  a <> 0 -> quadratic a b c x = 0 -> In x (quad_roots a b c).
Proof.
  intros a b c x Ha Hx. unfold quad_roots.
  destruct (req_b a 0) eqn:Ea.
  - apply req_b_true in Ea. contradiction.
  - set (d := discriminant a b c).
    assert (Hnn : 0 <= d).
    { unfold d. apply (discriminant_real_root_implies_nonneg a b c x Ha Hx). }
    destruct (Rlt_dec d 0) as [Hlt|Hge]; [exfalso; lra|].
    pose proof (quad_formula a b c x Ha Hx) as Hf. cbv zeta in Hf. fold d in Hf.
    destruct (req_b d 0) eqn:Ed.
    + apply req_b_true in Ed.
      destruct Hf as [Hx1|Hx2].
      * simpl. left. rewrite Hx1, Ed, sqrt_0.
        replace (- b + 0) with (- b) by ring. reflexivity.
      * simpl. left. rewrite Hx2, Ed, sqrt_0.
        replace (- b - 0) with (- b) by ring. reflexivity.
    + destruct Hf as [Hx1|Hx2].
      * rewrite Hx1. simpl. left. reflexivity.
      * rewrite Hx2. simpl. right. left. reflexivity.
Qed.
Lemma line_circle_in_pts : forall s c p,
  on_line s p -> on_circle_carrier c p -> In p (line_circle_pts s c).
Proof.
  intros s c p [t Ht] Hc. unfold line_circle_pts.
  destruct (req_b (lc_qa s) 0) eqn:Eqa.
  - apply req_b_true in Eqa.
    destruct (sum_of_squares_zero _ _ Eqa) as [Dx Dy].
    assert (Hdd : chord_dd s = 0) by (unfold chord_dd; rewrite Dx, Dy; ring).
    assert (Hp0 : p = ce_p0 s) by (rewrite Ht; apply chord_eval_deg; exact Hdd).
    assert (Hqc0 : lc_qc s c = dist_sq (circ_o c) (ce_p0 s) - circ_r c * circ_r c).
    { unfold lc_qc, dist_sq. cbn zeta. ring. }
    assert (Hqc : lc_qc s c = 0).
    { rewrite Hp0 in Hc. unfold on_circle_carrier in Hc. rewrite Hqc0. lra. }
    destruct (req_b (lc_qc s c) 0) eqn:Eqc.
    + simpl. left. symmetry. exact Hp0.
    + assert (Et : req_b (lc_qc s c) 0 = true) by (apply req_b_true; exact Hqc).
      congruence.
  - assert (Hqa : lc_qa s <> 0).
    { intro Hz. assert (Eb : req_b (lc_qa s) 0 = true) by (apply req_b_true; exact Hz).
      congruence. }
    assert (Hq : quadratic (lc_qa s) (lc_qb s c) (lc_qc s c) t = 0).
    { rewrite lc_param_root. rewrite <- Ht. unfold on_circle_carrier in Hc. lra. }
    rewrite Ht. apply in_map. apply quad_root_in; assumption.
Qed.
Lemma same_circle_carriers : forall a b,
  same_circle_b a b = true ->
  circ_o a = circ_o b /\ circ_r a * circ_r a = circ_r b * circ_r b.
Proof.
  intros a b H. unfold same_circle_b in H. apply andb_prop in H. destruct H as [Ho Hr].
  split; [apply pt_eqb_true; exact Ho| apply req_b_true; exact Hr].
Qed.
Lemma circle_circle_le_2_excludes_same : forall a b,
  same_circle_b a b = true -> ~ (0 < dist (circ_o a) (circ_o b)).
Proof.
  intros a b H Hd. destruct (same_circle_carriers a b H) as [Ho _].
  rewrite Ho, dist_refl in Hd. lra.
Qed.
Lemma distinct_circles_positive : forall a b p,
  same_circle_b a b = false ->
  on_circle_carrier a p -> on_circle_carrier b p ->
  0 < dist (circ_o a) (circ_o b).
Proof.
  intros a b p Hs Ha Hb.
  destruct (Rle_dec (dist (circ_o a) (circ_o b)) 0) as [Hle|Hgt].
  - assert (Hz : dist (circ_o a) (circ_o b) = 0).
    { pose proof (dist_nonneg (circ_o a) (circ_o b)). lra. }
    apply dist_eq_zero_iff in Hz. destruct Hz as [Hx Hy].
    assert (Eo : circ_o a = circ_o b) by (apply pt_eq_coords; assumption).
    assert (Er : circ_r a * circ_r a = circ_r b * circ_r b).
    { unfold on_circle_carrier in Ha, Hb. rewrite Eo in Ha. lra. }
    assert (Es : same_circle_b a b = true).
    { unfold same_circle_b. apply andb_true_intro. split.
      - apply pt_eqb_true. exact Eo.
      - apply req_b_true. exact Er. }
    congruence.
  - pose proof (dist_nonneg (circ_o a) (circ_o b)). lra.
Qed.
Lemma circle_circle_in_pts : forall a b p,
  same_circle_b a b = false ->
  on_circle_carrier a p -> on_circle_carrier b p ->
  In p (circle_circle_pts a b).
Proof.
  intros a b p Hs Ha Hb.
  pose proof (distinct_circles_positive a b p Hs Ha Hb) as Hd.
  unfold circle_circle_pts.
  destruct (rle_b (dist (circ_o a) (circ_o b)) 0) eqn:Eb.
  - apply rle_b_true in Eb. lra.
  - apply filter_In. split.
    + destruct (two_circles_radical_point_unique (circ_o a) (circ_o b)
                 (circ_r a) (circ_r b) p Hd Ha Hb) as [Hp|Hp].
      * left. symmetry. exact Hp.
      * right. left. symmetry. exact Hp.
    + unfold on_both_b. apply andb_true_intro. split; apply req_b_true; assumption.
Qed.
Lemma keep_of_images : forall pcs s1 s2 p,
  support_image pcs s1 p -> support_image pcs s2 p ->
  ~ (family_vertex pcs s1 p /\ family_vertex pcs s2 p) ->
  keep_b pcs s1 s2 p = true.
Proof.
  intros pcs s1 s2 p I1 I2 Nv. unfold keep_b.
  apply andb_true_intro. split.
  - apply andb_true_intro. split; apply in_image_spec; assumption.
  - apply negb_true_iff.
    destruct (vertex_b pcs s1 p && vertex_b pcs s2 p) eqn:Ev; [| reflexivity].
    exfalso. apply andb_prop in Ev. destruct Ev as [A B].
    apply Nv. split; apply vertex_spec; assumption.
Qed.
Lemma raw_in_of_class : forall pcs u v p,
  support_image pcs u p -> support_image pcs v p ->
  match u, v with
  | SuppChord a, SuppChord b =>
      same_line_b a b = false \/ In p (overlap_pts pcs (SuppChord a) (SuppChord b))
  | SuppCircle a, SuppCircle b =>
      same_circle_b a b = false \/ In p (overlap_pts pcs (SuppCircle a) (SuppCircle b))
  | _, _ => True
  end ->
  In p (raw_pts pcs u v).
Proof.
  intros pcs u v p Iu Iv Hclass.
  destruct u as [a|a]; destruct v as [b|b]; simpl in Hclass; unfold raw_pts.
  - destruct (same_line_b a b) eqn:Esl.
    + destruct Hclass as [Hs|Hover]; [congruence| exact Hover].
    + apply line_line_in_raw.
      * apply (image_on_line pcs a). exact Iu.
      * apply (image_on_line pcs b). exact Iv.
      * exact Esl.
  - apply line_circle_in_pts.
    + apply (image_on_line pcs a). exact Iu.
    + apply (image_on_circle pcs b). exact Iv.
  - apply line_circle_in_pts.
    + apply (image_on_line pcs b). exact Iv.
    + apply (image_on_circle pcs a). exact Iu.
  - destruct (same_circle_b a b) eqn:Esc.
    + destruct Hclass as [Hs|Hover]; [congruence| exact Hover].
    + apply circle_circle_in_pts.
      * exact Esc.
      * apply (image_on_circle pcs a). exact Iu.
      * apply (image_on_circle pcs b). exact Iv.
Qed.
Theorem rho_candidates_complete : forall pcs s1 s2 p,
  s1 <> s2 ->
  support_image pcs s1 p ->
  support_image pcs s2 p ->
  ~ (family_vertex pcs s1 p /\ family_vertex pcs s2 p) ->
  (forall a b, canon2 s1 s2 = (SuppChord a, SuppChord b) ->
     same_line_b a b = false \/ In p (overlap_pts pcs (SuppChord a) (SuppChord b))) ->
  (forall a b, canon2 s1 s2 = (SuppCircle a, SuppCircle b) ->
     same_circle_b a b = false \/ In p (overlap_pts pcs (SuppCircle a) (SuppCircle b))) ->
  In p (counted pcs s1 s2).
Proof.
  intros pcs s1 s2 p _ I1 I2 Nv Hline Hcirc.
  unfold counted.
  destruct (canon2 s1 s2) as [u v] eqn:Ec.
  assert (Huv : (u = s1 /\ v = s2) \/ (u = s2 /\ v = s1)).
  { unfold canon2 in Ec.
    destruct (rlex_le (support_reals s1) (support_reals s2)); inversion Ec; auto. }
  assert (Iu : support_image pcs u p).
  { destruct Huv as [[-> ->]|[-> ->]]; assumption. }
  assert (Iv : support_image pcs v p).
  { destruct Huv as [[-> ->]|[-> ->]]; assumption. }
  assert (Hk : keep_b pcs u v p = true).
  { apply keep_of_images; [exact Iu| exact Iv|].
    intros [A B]. apply Nv. destruct Huv as [[-> ->]|[-> ->]]; split; assumption. }
  assert (Hin : In p (raw_pts pcs u v)).
  { apply raw_in_of_class; [exact Iu| exact Iv|].
    destruct u as [a|a]; destruct v as [b|b]; simpl.
    - apply Hline. reflexivity.
    - exact I.
    - exact I.
    - apply Hcirc. reflexivity. }
  rewrite dedup_In. apply filter_In. split; assumption.
Qed.
(* -------------------------------------------------------------------------- *)
(* #892 CCW full-circle halves: two +π turns, Leibniz-distinct supports on    *)
(* one circle. Overlap is the shared antipode, a hen of both families, so ρ   *)
(* of the pair is 0. circle_circle_le_2's 0 < dist excludes this pair.        *)
(* -------------------------------------------------------------------------- *)
Lemma int_part_on_unit : forall x, 0 <= x < 1 -> Int_part x = 0%Z.
Proof.
  intros x Hx. destruct (base_Int_part x) as [Hle Hlt].
  assert (Hlt1 : IZR (Int_part x) < IZR 1) by lra.
  apply lt_IZR in Hlt1.
  assert (Hgt : IZR (-1) < IZR (Int_part x)) by lra.
  apply lt_IZR in Hgt. lia.
Qed.
Lemma align_k_same : forall a, align_k a a = 0%Z.
Proof.
  intro a. unfold align_k.
  pose proof PI_RGT_0 as Hpi.
  assert (Hp : PI <> 0) by lra.
  assert (H2 : 2 * PI <> 0) by nra.
  assert (E : (a - a) / (2 * PI) + / 2 = / 2).
  { apply (Rmult_eq_reg_l (2 * PI)); [| exact H2].
    replace (2 * PI * ((a - a) / (2 * PI) + / 2)) with ((a - a) + PI) by (field; exact Hp).
    replace (2 * PI * (/ 2)) with PI by field.
    ring. }
  rewrite E. apply int_part_on_unit. split.
  - apply Rlt_le. apply Rinv_0_lt_compat. lra.
  - apply (Rmult_lt_reg_l 2); [lra|]. replace (2 * (/ 2)) with 1 by field. lra.
Qed.
Lemma align_k_zero_pi : align_k 0 PI = 0%Z.
Proof.
  unfold align_k.
  pose proof PI_RGT_0 as Hpi.
  assert (Hp : PI <> 0) by lra.
  assert (H2 : 2 * PI <> 0) by nra.
  assert (E : (0 - PI) / (2 * PI) + / 2 = 0).
  { apply (Rmult_eq_reg_l (2 * PI)); [| exact H2].
    replace (2 * PI * ((0 - PI) / (2 * PI) + / 2)) with ((0 - PI) + PI) by (field; exact Hp).
    replace (2 * PI * 0) with 0 by ring.
    ring. }
  rewrite E. apply int_part_on_unit. lra.
Qed.
Definition iso_half_fst : CircularEgg := mkCircularEgg (mkPoint 0 0) 5 0 PI.
Definition iso_half_snd : CircularEgg := mkCircularEgg (mkPoint 0 0) 5 PI PI.
Lemma iso_halves_leibniz_distinct : iso_half_fst <> iso_half_snd.
Proof.
  intro H. unfold iso_half_fst, iso_half_snd in H. inversion H.
  pose proof PI_RGT_0. lra.
Qed.
Lemma iso_supports_distinct :
  SuppCircle iso_half_fst <> SuppCircle iso_half_snd.
Proof.
  intro H. inversion H. pose proof PI_RGT_0. lra.
Qed.
Lemma iso_same_circle : same_circle_b iso_half_fst iso_half_snd = true.
Proof.
  unfold same_circle_b, iso_half_fst, iso_half_snd. cbn.
  apply andb_true_intro. split; [apply pt_eqb_true; reflexivity| apply req_b_true; ring].
Qed.
Lemma iso_halves_not_transverse :
  ~ (0 < dist (circ_o iso_half_fst) (circ_o iso_half_snd)).
Proof. apply circle_circle_le_2_excludes_same. apply iso_same_circle. Qed.
Definition iso_half_pc (src dst : nat) (c : CircularEgg) : BagPiece :=
  mkBagPiece (mkChicken src dst (MkCirc (window_circ c (mkWindow 0 1))))
             (SuppCircle c) (mkWindow 0 1) nil.
Definition iso_half_pcs : list BagPiece :=
  [iso_half_pc 0 1 iso_half_fst; iso_half_pc 1 0 iso_half_snd].
Lemma iso_key_fst : forall t,
  key_param (SuppCircle iso_half_fst) (SuppCircle iso_half_fst) t = t * PI.
Proof.
  intro t. unfold key_param, iso_half_fst. cbn.
  assert (Eb : rle_b 0 (5 * 5) = true) by (apply rle_b_true; lra).
  rewrite Eb. cbv beta iota zeta.
  replace (0 + 0) with 0 by ring.
  rewrite align_k_same. replace (IZR 0) with 0 by reflexivity. ring.
Qed.
Lemma iso_key_snd : forall t,
  key_param (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) t = PI + t * PI.
Proof.
  intro t. unfold key_param, iso_half_fst, iso_half_snd. cbn.
  assert (Eb : rle_b 0 (5 * 5) = true) by (apply rle_b_true; lra).
  rewrite Eb. cbv beta iota zeta.
  replace (PI + 0) with PI by ring.
  rewrite align_k_zero_pi. replace (IZR 0) with 0 by reflexivity. ring.
Qed.
Lemma circ_eqb_refl : forall c, circ_eqb c c = true.
Proof.
  intro c. unfold circ_eqb, pt_eqb.
  repeat (apply andb_true_intro; split); apply req_b_true; reflexivity.
Qed.
Lemma iso_circ_swap_false : circ_eqb iso_half_snd iso_half_fst = false.
Proof.
  unfold circ_eqb, iso_half_snd, iso_half_fst. cbn.
  assert (E : req_b PI 0 = false).
  { destruct (req_b PI 0) eqn:Eb; [| reflexivity].
    apply req_b_true in Eb. pose proof PI_RGT_0. lra. }
  rewrite E.
  destruct (pt_eqb (mkPoint 0 0) (mkPoint 0 0));
    destruct (req_b 5 5); destruct (req_b PI PI); reflexivity.
Qed.
Lemma iso_circ_ord_false : circ_eqb iso_half_fst iso_half_snd = false.
Proof.
  unfold circ_eqb, iso_half_fst, iso_half_snd. cbn.
  assert (E : req_b 0 PI = false).
  { destruct (req_b 0 PI) eqn:Eb; [| reflexivity].
    apply req_b_true in Eb. pose proof PI_RGT_0. lra. }
  rewrite E.
  destruct (pt_eqb (mkPoint 0 0) (mkPoint 0 0));
    destruct (req_b 5 5); destruct (req_b PI PI); reflexivity.
Qed.
Lemma iso_keys_fst :
  all_keys (SuppCircle iso_half_fst) (SuppCircle iso_half_fst) iso_half_pcs = [0; PI].
Proof.
  Opaque key_param.
  unfold all_keys, iso_half_pcs, piece_keys, iso_half_pc. cbn.
  rewrite circ_eqb_refl. rewrite iso_circ_swap_false. cbn.
  rewrite iso_key_fst, iso_key_fst.
  replace (0 * PI) with 0 by ring. replace (1 * PI) with PI by ring. reflexivity.
  Transparent key_param.
Qed.
Lemma iso_keys_snd :
  all_keys (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) iso_half_pcs = [PI; 2 * PI].
Proof.
  Opaque key_param.
  unfold all_keys, iso_half_pcs, piece_keys, iso_half_pc. cbn.
  rewrite iso_circ_ord_false. rewrite circ_eqb_refl. cbn.
  rewrite iso_key_snd, iso_key_snd.
  replace (PI + 0 * PI) with PI by ring.
  replace (PI + 1 * PI) with (2 * PI) by ring. reflexivity.
  Transparent key_param.
Qed.
Lemma iso_antipode : point_of_key (SuppCircle iso_half_fst) PI = mkPoint (-5) 0.
Proof.
  unfold point_of_key, iso_half_fst. cbn [circ_sweep circ_theta0 circ_o circ_r px py].
  destruct (req_b PI 0) eqn:E.
  - apply req_b_true in E. pose proof PI_RGT_0. lra.
  - unfold circ_eval. cbn [circ_o circ_r circ_theta0 circ_sweep px py].
    assert (Hp : PI <> 0). { pose proof PI_RGT_0. lra. }
    replace (0 + ((PI - 0) / PI) * PI) with PI by (field; exact Hp).
    rewrite cos_PI, sin_PI. apply (f_equal2 mkPoint); ring.
Qed.
Lemma dedup_dup : forall p, dedup [p; p] = [p].
Proof.
  intro p.
  assert (E : pt_eqb p p = true) by (apply pt_eqb_true; reflexivity).
  simpl. rewrite E. reflexivity.
Qed.
Lemma iso_overlap_pts :
  overlap_pts iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) =
  [mkPoint (-5) 0].
Proof.
  unfold overlap_pts. rewrite iso_keys_fst, iso_keys_snd. cbn [rmin_list rmax_list].
  assert (A : Rmin 0 PI = 0). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  assert (B : Rmax 0 PI = PI). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  assert (C : Rmin PI (2 * PI) = PI). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  assert (D : Rmax PI (2 * PI) = 2 * PI). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  rewrite A, B, C, D. rewrite B, C.
  assert (E : rle_b PI PI = true) by (apply rle_b_true; lra).
  rewrite E. rewrite iso_antipode. apply dedup_dup.
Qed.
Lemma iso_antipode_end_fst :
  support_at (SuppCircle iso_half_fst) 1 = mkPoint (-5) 0.
Proof.
  unfold support_at, circ_eval, iso_half_fst. cbn.
  replace (0 + 1 * PI) with PI by ring.
  rewrite cos_PI, sin_PI. apply (f_equal2 mkPoint); ring.
Qed.
Lemma iso_antipode_start_snd :
  support_at (SuppCircle iso_half_snd) 0 = mkPoint (-5) 0.
Proof.
  unfold support_at, circ_eval, iso_half_snd. cbn.
  replace (PI + 0 * PI) with PI by ring.
  rewrite cos_PI, sin_PI. apply (f_equal2 mkPoint); ring.
Qed.
Lemma iso_half_overlap_are_hens : forall p,
  In p (overlap_pts iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd)) ->
  family_vertex iso_half_pcs (SuppCircle iso_half_fst) p /\
  family_vertex iso_half_pcs (SuppCircle iso_half_snd) p.
Proof.
  intros p Hin.
  assert (Hin' : In p [mkPoint (-5) 0]).
  { exact (eq_rect _ (fun l => In p l) Hin _ iso_overlap_pts). }
  destruct Hin' as [<-|[]]. split.
  - exists (iso_half_pc 0 1 iso_half_fst). split; [simpl; auto|]. split; [reflexivity|].
    unfold piece_endpoint, iso_half_pc. cbn. right. symmetry. apply iso_antipode_end_fst.
  - exists (iso_half_pc 1 0 iso_half_snd). split; [simpl; auto|]. split; [reflexivity|].
    unfold piece_endpoint, iso_half_pc. cbn. left. symmetry. apply iso_antipode_start_snd.
Qed.
Lemma iso_keep_antipode :
  keep_b iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd)
         (mkPoint (-5) 0) = false.
Proof.
  unfold keep_b.
  assert (Hin : In (mkPoint (-5) 0)
      (overlap_pts iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd))).
  { assert (Hin0 : In (mkPoint (-5) 0) [mkPoint (-5) 0]).
    { unfold In. left. reflexivity. }
    apply (eq_rect _ (fun l => In (mkPoint (-5) 0) l) Hin0 _ (eq_sym iso_overlap_pts)). }
  assert (V : vertex_b iso_half_pcs (SuppCircle iso_half_fst) (mkPoint (-5) 0) &&
              vertex_b iso_half_pcs (SuppCircle iso_half_snd) (mkPoint (-5) 0) = true).
  { apply andb_true_intro. split; apply vertex_spec; apply iso_half_overlap_are_hens; exact Hin. }
  rewrite V. destruct (in_image_b iso_half_pcs (SuppCircle iso_half_fst) (mkPoint (-5) 0) &&
                       in_image_b iso_half_pcs (SuppCircle iso_half_snd) (mkPoint (-5) 0));
    reflexivity.
Qed.
Lemma iso_halves_raw_overlap :
  raw_pts iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) =
  overlap_pts iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd).
Proof. unfold raw_pts. rewrite iso_same_circle. reflexivity. Qed.
Lemma iso_canon :
  canon2 (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) =
  (SuppCircle iso_half_fst, SuppCircle iso_half_snd).
Proof.
  unfold canon2. unfold support_reals, iso_half_fst, iso_half_snd. cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  unfold rlex_le.
  destruct (Req_EM_T 1 1) as [_|N1]; [| congruence].
  destruct (Req_EM_T 0 0) as [_|N0]; [| congruence].
  destruct (Req_EM_T 0 0) as [_|N0b]; [| congruence].
  destruct (Req_EM_T 5 5) as [_|N5]; [| congruence].
  destruct (Req_EM_T 0 PI) as [Bad|Npi].
  - pose proof PI_RGT_0. lra.
  - destruct (Rle_dec 0 PI) as [_|Hle]; [| pose proof PI_RGT_0; lra]. reflexivity.
Qed.
Lemma iso_half_counted_nil :
  counted iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) = [].
Proof.
  unfold counted. rewrite iso_canon. cbn [fst snd].
  rewrite iso_halves_raw_overlap, iso_overlap_pts.
  cbn. rewrite iso_keep_antipode. reflexivity.
Qed.
Lemma iso_supports :
  supports_of iso_half_pcs = [SuppCircle iso_half_fst; SuppCircle iso_half_snd].
Proof.
  unfold iso_half_pcs, supports_of, iso_half_pc. cbn.
  rewrite iso_circ_ord_false. reflexivity.
Qed.
Lemma iso_half_pair_rho_zero : rho_pcs iso_half_pcs = 0%nat.
Proof.
  unfold rho_pcs. rewrite iso_supports. cbn.
  rewrite iso_half_counted_nil. reflexivity.
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
Print Assumptions overlap_endpoints_le_2.
Print Assumptions rmin_lb.
Print Assumptions rmin_in.
Print Assumptions rmax_ub.
Print Assumptions rmax_in.
Print Assumptions key_affine.
Print Assumptions key_between.
Print Assumptions split_ends.
Print Assumptions piece_key_end.
Print Assumptions in_all_of.
Print Assumptions old_key_in_new.
Print Assumptions parent_bound.
Print Assumptions new_key_bound.
Print Assumptions hull_progress.
Print Assumptions overlap_eq.
Print Assumptions raw_progress.
Print Assumptions chord_eval_deg.
Print Assumptions chord_param_eval.
Print Assumptions in_window_chord_spec.
Print Assumptions lattice_in.
Print Assumptions atan_reduce.
Print Assumptions circ_eval_abs_shift.
Print Assumptions circ_rep_true.
Print Assumptions in_window_circ_spec.
Print Assumptions in_window_spec.
Print Assumptions in_image_spec.
Print Assumptions endpoint_spec.
Print Assumptions vertex_spec.
Print Assumptions counted_sym.
Print Assumptions supports_progress_perm.
Print Assumptions keep_step.
Print Assumptions rho_step_nonincreasing.
Print Assumptions image_on_line.
Print Assumptions image_on_circle.
Print Assumptions cross_zero_same_line.
Print Assumptions not_same_cross.
Print Assumptions cramer_param.
Print Assumptions line_line_in_raw.
Print Assumptions quad_root_in.
Print Assumptions line_circle_in_pts.
Print Assumptions same_circle_carriers.
Print Assumptions circle_circle_le_2_excludes_same.
Print Assumptions distinct_circles_positive.
Print Assumptions circle_circle_in_pts.
Print Assumptions keep_of_images.
Print Assumptions raw_in_of_class.
Print Assumptions rho_candidates_complete.
Print Assumptions int_part_on_unit.
Print Assumptions align_k_same.
Print Assumptions align_k_zero_pi.
Print Assumptions iso_halves_leibniz_distinct.
Print Assumptions iso_supports_distinct.
Print Assumptions iso_same_circle.
Print Assumptions iso_halves_not_transverse.
Print Assumptions iso_key_fst.
Print Assumptions iso_key_snd.
Print Assumptions circ_eqb_refl.
Print Assumptions iso_circ_swap_false.
Print Assumptions iso_circ_ord_false.
Print Assumptions iso_keys_fst.
Print Assumptions iso_keys_snd.
Print Assumptions iso_antipode.
Print Assumptions dedup_dup.
Print Assumptions iso_overlap_pts.
Print Assumptions iso_antipode_end_fst.
Print Assumptions iso_antipode_start_snd.
Print Assumptions iso_half_overlap_are_hens.
Print Assumptions iso_keep_antipode.
Print Assumptions iso_halves_raw_overlap.
Print Assumptions iso_canon.
Print Assumptions iso_half_counted_nil.
Print Assumptions iso_supports.
Print Assumptions iso_half_pair_rho_zero.
