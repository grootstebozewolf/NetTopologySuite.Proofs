(* ============================================================================
   NetTopologySuite.Proofs.LipInt
   ----------------------------------------------------------------------------
   A 3-axiom integral for Lipschitz integrands. int_a^b f is the limit
   of dyadic Riemann sums, which are Cauchy at an explicit rate; existence
   is R_complete. No RiemannInt and no mean-value theorem.
   The construction is the owner's (verified on Coq 8.18). This file is
   that development, retargeted From Stdlib, plus sin_lip.
   claimId: none.
   No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted port, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia.
Local Open Scope R_scope.

Lemma pow2_pos : forall n, 0 < 2 ^ n.
Proof. intro n. apply pow_lt. lra. Qed.

Lemma pow2_S : forall n, 2 ^ S n = 2 * 2 ^ n.
Proof. reflexivity. Qed.

Section Lint.
Variable f : R -> R.
Variables lo hi L : R.
Hypothesis HL : 0 <= L.
Hypothesis Hlip : forall x y, lo <= x <= hi -> lo <= y <= hi ->
  Rabs (f x - f y) <= L * Rabs (x - y).

Fixpoint D (k : nat) (a b : R) : R :=
  match k with
  | O => (b - a) * f a
  | S k' => D k' a ((a + b) / 2) + D k' ((a + b) / 2) b
  end.

Lemma D_step : forall k a b, lo <= a -> a <= b -> b <= hi ->
  Rabs (D (S k) a b - D k a b) <= L * (b - a) * (b - a) / 2 ^ (k + 2).
Proof.
  induction k as [|k IH]; intros a b Ha Hab Hb.
  - cbn [D]. set (m := (a + b) / 2).
    replace ((m - a) * f a + (b - m) * f m - (b - a) * f a)
      with ((b - a) / 2 * (f m - f a)) by (unfold m; field).
    rewrite Rabs_mult, (Rabs_right ((b - a) / 2)) by lra.
    assert (H := Hlip m a ltac:(unfold m; lra) ltac:(lra)).
    replace (Rabs (m - a)) with ((b - a) / 2) in H
      by (unfold m; rewrite Rabs_right; [field | lra]).
    replace (2 ^ (0 + 2)) with 4 by (simpl; ring).
    apply Rle_trans with ((b - a) / 2 * (L * ((b - a) / 2))).
    + apply Rmult_le_compat_l; lra.
    + right. field.
  - set (m := (a + b) / 2).
    assert (E : D (S (S k)) a b - D (S k) a b
              = (D (S k) a m - D k a m) + (D (S k) m b - D k m b))
      by (cbn [D]; fold m; ring).
    rewrite E.
    eapply Rle_trans; [apply Rabs_triang|].
    pose proof (IH a m Ha ltac:(unfold m; lra) ltac:(unfold m; lra)) as H1.
    pose proof (IH m b ltac:(unfold m; lra) ltac:(unfold m; lra) Hb) as H2.
    eapply Rle_trans; [apply Rplus_le_compat; [exact H1 | exact H2]|].
    replace (S k + 2)%nat with (S (k + 2)) by lia. rewrite pow2_S.
    pose proof (pow2_pos (k + 2)).
    right. unfold m. field. lra.
Qed.

Lemma D_tail : forall p k a b, lo <= a -> a <= b -> b <= hi ->
  Rabs (D (k + p) a b - D k a b)
  <= L * (b - a) * (b - a) * (/ 2 ^ (k + 1) - / 2 ^ (k + p + 1)).
Proof.
  induction p as [|p IH]; intros k a b Ha Hab Hb.
  - rewrite Nat.add_0_r, Rminus_diag, Rabs_R0, Rminus_diag. lra.
  - replace (k + S p)%nat with (S (k + p)) by lia.
    replace (D (S (k + p)) a b - D k a b)
      with ((D (S (k + p)) a b - D (k + p) a b) + (D (k + p) a b - D k a b)) by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    pose proof (D_step (k + p) a b Ha Hab Hb) as H1.
    pose proof (IH k a b Ha Hab Hb) as H2.
    eapply Rle_trans; [apply Rplus_le_compat; [exact H1 | exact H2]|].
    replace (S (k + p) + 1)%nat with (S (k + p + 1)) by lia.
    replace (k + p + 2)%nat with (S (k + p + 1)) by lia.
    rewrite pow2_S.
    pose proof (pow2_pos (k + p + 1)). pose proof (pow2_pos (k + 1)).
    right. field. split; lra.
Qed.

Lemma D_tail_le : forall n k a b, (k <= n)%nat -> lo <= a -> a <= b -> b <= hi ->
  Rabs (D n a b - D k a b) <= L * (b - a) * (b - a) / 2 ^ (k + 1).
Proof.
  intros n k a b Hkn Ha Hab Hb.
  replace n with (k + (n - k))%nat by lia.
  eapply Rle_trans; [apply D_tail; assumption|].
  pose proof (pow2_pos (k + (n - k) + 1)). pose proof (pow2_pos (k + 1)).
  assert (0 <= L * (b - a) * (b - a)) by (apply Rmult_le_pos; [apply Rmult_le_pos|]; lra).
  assert (0 < / 2 ^ (k + (n - k) + 1)) by (apply Rinv_0_lt_compat; lra).
  unfold Rdiv. apply Rmult_le_compat_l; [lra|]. lra.
Qed.

Lemma D_cauchy : forall a b, lo <= a -> a <= b -> b <= hi ->
  Cauchy_crit (fun n => D n a b).
Proof.
  intros a b Ha Hab Hb eps Heps.
  set (C := L * (b - a) * (b - a)).
  assert (HC : 0 <= C) by (unfold C; apply Rmult_le_pos; [apply Rmult_le_pos|]; lra).
  destruct (pow_lt_1_zero (/ 2) ltac:(rewrite Rabs_right; lra) (eps / (C + 1))
              ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
  exists N. intros n m Hn Hm. unfold R_dist.
  specialize (HN N (le_n N)). rewrite pow_inv, Rabs_right in HN
    by (apply Rle_ge, Rlt_le, Rinv_0_lt_compat, pow2_pos).
  pose proof (D_tail_le n N a b Hn Ha Hab Hb) as H1.
  pose proof (D_tail_le m N a b Hm Ha Hab Hb) as H2. fold C in H1, H2.
  replace (D n a b - D m a b) with ((D n a b - D N a b) - (D m a b - D N a b)) by ring.
  eapply Rle_lt_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp.
  pose proof (pow2_pos N). pose proof (pow2_pos (N + 1)).
  replace (N + 1)%nat with (S N) in H1, H2 by lia. rewrite pow2_S in H1, H2.
  assert (Hk : C / 2 ^ N <= C * (eps / (C + 1))).
  { unfold Rdiv. apply Rmult_le_compat_l; [lra|]. lra. }
  assert (C * (eps / (C + 1)) < eps).
  { unfold Rdiv. apply Rlt_le_trans with ((C + 1) * (eps * / (C + 1))).
    - apply Rmult_lt_compat_r; [apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra] | lra].
    - right. field. lra. }
  assert (C / (2 * 2 ^ N) + C / (2 * 2 ^ N) = C / 2 ^ N) by (field; lra).
  lra.
Qed.

(* The integral, and its defining property. *)
Definition lint (a b : R) (Ha : lo <= a) (Hab : a <= b) (Hb : b <= hi) : R :=
  proj1_sig (R_complete _ (D_cauchy a b Ha Hab Hb)).

Theorem lint_cv : forall a b Ha Hab Hb, Un_cv (fun n => D n a b) (lint a b Ha Hab Hb).
Proof. intros. unfold lint. destruct (R_complete _ _) as [l Hl]. exact Hl. Qed.

(* Proof-irrelevant: any two proofs give the same value. *)
Theorem lint_pi : forall a b Ha Hab Hb Ha' Hab' Hb',
  lint a b Ha Hab Hb = lint a b Ha' Hab' Hb'.
Proof. intros. eapply UL_sequence; apply lint_cv. Qed.

(* Explicit, computable error bound for the k-th dyadic sum. *)
Theorem lint_error : forall k a b Ha Hab Hb,
  Rabs (lint a b Ha Hab Hb - D k a b) <= L * (b - a) * (b - a) / 2 ^ (k + 1).
Proof.
  intros k a b Ha Hab Hb.
  set (l := lint a b Ha Hab Hb). set (B := L * (b - a) * (b - a) / 2 ^ (k + 1)).
  destruct (Rle_dec (Rabs (l - D k a b)) B) as [H|H]; [exact H|]. exfalso.
  apply Rnot_le_lt in H.
  destruct (lint_cv a b Ha Hab Hb (Rabs (l - D k a b) - B) ltac:(lra)) as [N HN].
  specialize (HN (max N k) (Nat.le_max_l N k)). unfold R_dist in HN. fold l in HN.
  pose proof (D_tail_le (max N k) k a b (Nat.le_max_r N k) Ha Hab Hb) as Ht. fold B in Ht.
  assert (Rabs (l - D k a b) <= Rabs (D (max N k) a b - l) + Rabs (D (max N k) a b - D k a b)).
  { replace (l - D k a b) with (- (D (max N k) a b - l) + (D (max N k) a b - D k a b)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. lra. }
  lra.
Qed.
End Lint.


(* ---------- Fresnel C(X) = int_0^X cos(t^2) dt, 3-axiom ---------- *)

(* Stdlib's PI2_1 (Ratan) pulls classic; pi2_int (Rtrigo1) does not. *)
Lemma PI_ge_1 : 1 <= PI.
Proof. pose proof pi2_int. unfold PI. lra. Qed.

Lemma sin_le_id_small : forall a, 0 <= a -> a <= 1 -> sin a <= a.
Proof.
  intros a H0 H1. pose proof PI_ge_1.
  destruct (sin_bound a 0 H0 ltac:(lra)) as [_ Hu].
  eapply Rle_trans; [exact Hu|].
  unfold sin_approx, sin_term. cbn [sum_f_R0 Nat.mul Nat.add].
  rewrite !INR_IZR_INZ. cbn.
  assert (0 <= a * a) by nra. assert (a * a <= 1) by nra.
  assert (0 <= a * (a * a)) by nra.
  nra.
Qed.

Lemma abs_sin_le : forall z, Rabs (sin z) <= Rabs z.
Proof.
  assert (Hpos : forall a, 0 <= a -> Rabs (sin a) <= a).
  { intros a Ha. pose proof PI_ge_1. destruct (Rle_dec a 1) as [H1|H1].
    - rewrite Rabs_right.
      + apply sin_le_id_small; lra.
      + apply Rle_ge, sin_ge_0; lra.
    - pose proof (SIN_bound a). apply Rabs_le. lra. }
  intro z. destruct (Rle_dec 0 z) as [Hz|Hz].
  - rewrite (Rabs_right z) by lra. apply Hpos. exact Hz.
  - assert (Hw : 0 <= - z) by lra. specialize (Hpos (- z) Hw).
    rewrite sin_neg, Rabs_Ropp in Hpos. rewrite (Rabs_left z) by lra. exact Hpos.
Qed.

Lemma cos_lip : forall u v, Rabs (cos u - cos v) <= Rabs (u - v).
Proof.
  intros u v. rewrite form2.
  rewrite !Rabs_mult.
  replace (Rabs (-2)) with 2 by (rewrite Rabs_left; lra).
  pose proof (abs_sin_le ((u - v) / 2)) as H1.
  pose proof (SIN_bound ((u + v) / 2)) as H2.
  assert (Rabs (sin ((u + v) / 2)) <= 1) by (apply Rabs_le; lra).
  assert (Rabs ((u - v) / 2) = Rabs (u - v) / 2).
  { unfold Rdiv. rewrite Rabs_mult, (Rabs_right (/ 2)) by lra. reflexivity. }
  pose proof (Rabs_pos (sin ((u - v) / 2))). pose proof (Rabs_pos (sin ((u + v) / 2))).
  nra.
Qed.

Lemma sin_lip : forall u v, Rabs (sin u - sin v) <= Rabs (u - v).
Proof.
  intros u v. rewrite form4.
  rewrite !Rabs_mult.
  replace (Rabs 2) with 2 by (rewrite Rabs_right; lra).
  pose proof (abs_sin_le ((u - v) / 2)) as H1.
  pose proof (COS_bound ((u + v) / 2)) as H2.
  assert (Rabs (cos ((u + v) / 2)) <= 1) by (apply Rabs_le; lra).
  assert (Rabs ((u - v) / 2) = Rabs (u - v) / 2).
  { unfold Rdiv. rewrite Rabs_mult, (Rabs_right (/ 2)) by lra. reflexivity. }
  pose proof (Rabs_pos (sin ((u - v) / 2))).
  pose proof (Rabs_pos (cos ((u + v) / 2))).
  nra.
Qed.

Lemma cos_sq_lip : forall X x y, 0 <= x <= X -> 0 <= y <= X ->
  Rabs (cos (x * x) - cos (y * y)) <= (2 * X) * Rabs (x - y).
Proof.
  intros X x y Hx Hy.
  eapply Rle_trans; [apply cos_lip|].
  replace (x * x - y * y) with ((x - y) * (x + y)) by ring.
  rewrite Rabs_mult, (Rabs_right (x + y)) by lra.
  pose proof (Rabs_pos (x - y)). nra.
Qed.

Section Fresnel.
Variable X : R.
Hypothesis HX : 0 <= X.

Definition fresnel_C : R :=
  lint (fun t => cos (t * t)) 0 X (2 * X) ltac:(lra)
       (fun x y Hx Hy => cos_sq_lip X x y Hx Hy)
       0 X (Rle_refl 0) HX (Rle_refl X).

(* Computable enclosure: the k-th dyadic sum is within 2 X^3 / 2^(k+1). *)
Theorem fresnel_C_error : forall k,
  Rabs (fresnel_C - D (fun t => cos (t * t)) k 0 X) <= 2 * X * (X - 0) * (X - 0) / 2 ^ (k + 1).
Proof. intro k. unfold fresnel_C. apply lint_error. Qed.
End Fresnel.

(* Dyadic sums, independent of the Lipschitz witness. D is this sum. *)
Fixpoint dyadic (g : R -> R) (k : nat) (a b : R) : R :=
  match k with
  | O => (b - a) * g a
  | S k' => dyadic g k' a ((a + b) / 2) + dyadic g k' ((a + b) / 2) b
  end.

Fixpoint sum_left (g : R -> R) (n : nat) (a h : R) : R :=
  match n with
  | O => 0
  | S n' => h * g a + sum_left g n' (a + h) h
  end.

Lemma seq_ext :
  forall (u v : nat -> R) l, (forall n, u n = v n) -> Un_cv u l -> Un_cv v l.
Proof.
  intros u v l Heq H eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N. intros n Hn. rewrite <- Heq. apply HN. exact Hn.
Qed.

Lemma seq_S : forall (u : nat -> R) l, Un_cv u l -> Un_cv (fun n => u (S n)) l.
Proof.
  intros u l H eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N. intros n Hn. apply HN. lia.
Qed.

Lemma seq_const : forall c, Un_cv (fun _ : nat => c) c.
Proof.
  intros c eps Heps. exists 0%nat. intros n _.
  unfold R_dist. rewrite Rminus_diag, Rabs_R0. exact Heps.
Qed.

Lemma seq_le :
  forall (u v : nat -> R) lu lv,
    (forall n, u n <= v n) -> Un_cv u lu -> Un_cv v lv -> lu <= lv.
Proof.
  intros u v lu lv Hle Hu Hv.
  destruct (Rle_dec lu lv) as [Hle'|Hgt]; [exact Hle'|].
  apply Rnot_le_lt in Hgt.
  set (eps := (lu - lv) / 2).
  assert (He : 0 < eps) by (unfold eps; lra).
  destruct (Hu eps He) as [N1 HN1].
  destruct (Hv eps He) as [N2 HN2].
  set (n := Nat.max N1 N2).
  specialize (HN1 n (Nat.le_max_l _ _)).
  specialize (HN2 n (Nat.le_max_r _ _)).
  unfold R_dist in HN1, HN2.
  apply Rabs_def2 in HN1. apply Rabs_def2 in HN2.
  pose proof (Hle n). unfold eps in HN1, HN2. lra.
Qed.

Lemma D_dyadic : forall g k a b, D g k a b = dyadic g k a b.
Proof.
  intros g k.
  induction k as [|k IH]; intros a b; simpl.
  - reflexivity.
  - rewrite IH, IH. reflexivity.
Qed.

Lemma lint_cv_dyadic :
  forall g lo hi L HL Hlip a b Ha Hab Hb,
    Un_cv (fun n => dyadic g n a b)
      (lint g lo hi L HL Hlip a b Ha Hab Hb).
Proof.
  intros g lo hi L HL Hlip a b Ha Hab Hb.
  apply seq_ext with (u := fun n => D g n a b).
  - intro n. apply D_dyadic.
  - apply lint_cv.
Qed.

Lemma dyadic_ext_on :
  forall g h k a b,
    a <= b ->
    (forall x, a <= x <= b -> g x = h x) ->
    dyadic g k a b = dyadic h k a b.
Proof.
  intros g h k.
  induction k as [|k IH]; intros a b Hab Heq; simpl.
  - rewrite Heq by lra. reflexivity.
  - set (m := (a + b) / 2).
    assert (Ham : a <= m) by (unfold m; lra).
    assert (Hmb : m <= b) by (unfold m; lra).
    rewrite (IH a m Ham).
    2:{ intros x Hx. apply Heq. unfold m in Hx. lra. }
    rewrite (IH m b Hmb).
    2:{ intros x Hx. apply Heq. unfold m in Hx. lra. }
    reflexivity.
Qed.

Lemma dyadic_zero_width : forall g k a, dyadic g k a a = 0.
Proof.
  intros g k. induction k as [|k IH]; intros a; simpl.
  - ring.
  - replace ((a + a) / 2) with a by field.
    rewrite !IH. ring.
Qed.

Lemma dyadic_const :
  forall c k a b, a <= b -> dyadic (fun _ => c) k a b = (b - a) * c.
Proof.
  intros c k. induction k as [|k IH]; intros a b Hab; simpl.
  - reflexivity.
  - set (m := (a + b) / 2).
    rewrite (IH a m), (IH m b) by (unfold m; lra).
    unfold m. ring.
Qed.

Lemma dyadic_opp :
  forall g k a b, dyadic (fun x => - g x) k a b = - dyadic g k a b.
Proof.
  intros g k. induction k as [|k IH]; intros a b; simpl.
  - ring.
  - rewrite IH, IH. ring.
Qed.

Lemma dyadic_plus :
  forall g h k a b,
    dyadic (fun x => g x + h x) k a b = dyadic g k a b + dyadic h k a b.
Proof.
  intros g h k. induction k as [|k IH]; intros a b; simpl.
  - ring.
  - rewrite IH, IH. ring.
Qed.

Lemma dyadic_scal :
  forall g c k a b, dyadic (fun x => c * g x) k a b = c * dyadic g k a b.
Proof.
  intros g c k. induction k as [|k IH]; intros a b; simpl.
  - ring.
  - rewrite IH, IH. ring.
Qed.

Lemma dyadic_abs_bound :
  forall g M k a b,
    a <= b ->
    (forall x, a <= x <= b -> Rabs (g x) <= M) ->
    Rabs (dyadic g k a b) <= M * (b - a).
Proof.
  intros g M k.
  induction k as [|k IH]; intros a b Hab HM; simpl.
  - rewrite Rabs_mult, (Rabs_right (b - a)) by lra.
    rewrite (Rmult_comm M (b - a)).
    apply Rmult_le_compat_l; [lra | apply HM; lra].
  - set (m := (a + b) / 2).
    eapply Rle_trans; [apply Rabs_triang|].
    eapply Rle_trans.
    + apply Rplus_le_compat.
      * apply IH; [unfold m; lra|].
        intros x Hx. apply HM. unfold m in Hx. lra.
      * apply IH; [unfold m; lra|].
        intros x Hx. apply HM. unfold m in Hx. lra.
    + unfold m. lra.
Qed.

Lemma dyadic_mono :
  forall g h k a b,
    a <= b ->
    (forall x, a <= x <= b -> g x <= h x) ->
    dyadic g k a b <= dyadic h k a b.
Proof.
  intros g h k.
  induction k as [|k IH]; intros a b Hab Hle; simpl.
  - apply Rmult_le_compat_l; [lra | apply Hle; lra].
  - set (m := (a + b) / 2).
    apply Rplus_le_compat; apply IH; try (unfold m; lra); intros x Hx; apply Hle;
      unfold m in Hx; lra.
Qed.

Lemma lint_irrel :
  forall g lo hi L1 L2 HL1 Hlip1 HL2 Hlip2 a b Ha1 Hab1 Hb1 Ha2 Hab2 Hb2,
    lint g lo hi L1 HL1 Hlip1 a b Ha1 Hab1 Hb1 =
    lint g lo hi L2 HL2 Hlip2 a b Ha2 Hab2 Hb2.
Proof.
  intros.
  apply UL_sequence with (fun n => dyadic g n a b); apply lint_cv_dyadic.
Qed.

Lemma lint_window_eq :
  forall g lo hi lo' hi' L HL Hlip HL' Hlip' a b Ha Hab Hb Ha' Hab' Hb',
    lo = lo' -> hi = hi' ->
    lint g lo hi L HL Hlip a b Ha Hab Hb =
    lint g lo' hi' L HL' Hlip' a b Ha' Hab' Hb'.
Proof.
  intros g lo hi lo' hi' L HL Hlip HL' Hlip' a b Ha Hab Hb Ha' Hab' Hb' Elo Ehi.
  subst lo' hi'. apply lint_irrel.
Qed.

Lemma lint_point :
  forall g lo hi L HL Hlip a Ha Hab Hb,
    lint g lo hi L HL Hlip a a Ha Hab Hb = 0.
Proof.
  intros.
  apply UL_sequence with (fun n => dyadic g n a a).
  - apply lint_cv_dyadic.
  - eapply seq_ext.
    + intro n. symmetry. apply dyadic_zero_width.
    + apply seq_const.
Qed.

Lemma lint_const :
  forall c lo hi L (HL : 0 <= L) Hlip a b Ha Hab Hb,
    lint (fun _ : R => c) lo hi L HL Hlip a b Ha Hab Hb = (b - a) * c.
Proof.
  intros.
  apply UL_sequence with (fun n => dyadic (fun _ : R => c) n a b).
  - apply lint_cv_dyadic.
  - eapply seq_ext.
    + intro n. symmetry. apply dyadic_const. exact Hab.
    + apply seq_const.
Qed.

Lemma lint_ext :
  forall g h lo hi L HL Hlipg Hlih a b Ha Hab Hb Ha2 Hab2 Hb2,
    (forall x, a <= x <= b -> g x = h x) ->
    lint g lo hi L HL Hlipg a b Ha Hab Hb =
    lint h lo hi L HL Hlih a b Ha2 Hab2 Hb2.
Proof.
  intros g h lo hi L HL Hlipg Hlih a b Ha Hab Hb Ha2 Hab2 Hb2 Heq.
  apply UL_sequence with (fun n => dyadic g n a b).
  - apply lint_cv_dyadic.
  - apply seq_ext with (u := fun n => dyadic h n a b).
    + intro n. symmetry. apply dyadic_ext_on; [exact Hab | exact Heq].
    + apply lint_cv_dyadic.
Qed.

Lemma lint_mono :
  forall g h lo hi Lg Hg HLg Hlipg HHg Hlih a b Ha Hab Hb Ha2 Hab2 Hb2,
    (forall x, a <= x <= b -> g x <= h x) ->
    lint g lo hi Lg HLg Hlipg a b Ha Hab Hb <=
    lint h lo hi Hg HHg Hlih a b Ha2 Hab2 Hb2.
Proof.
  intros g h lo hi Lg Hg HLg Hlipg HHg Hlih a b Ha Hab Hb Ha2 Hab2 Hb2 Hle.
  apply seq_le with (u := fun n => dyadic g n a b) (v := fun n => dyadic h n a b).
  - intro n. apply dyadic_mono; [exact Hab | exact Hle].
  - apply lint_cv_dyadic.
  - apply lint_cv_dyadic.
Qed.

Lemma lint_abs :
  forall g lo hi L HL Hlip a b Ha Hab Hb M,
    (forall x, a <= x <= b -> Rabs (g x) <= M) ->
    Rabs (lint g lo hi L HL Hlip a b Ha Hab Hb) <= M * (b - a).
Proof.
  intros g lo hi L HL Hlip a b Ha Hab Hb M HM.
  set (I := lint g lo hi L HL Hlip a b Ha Hab Hb).
  assert (Hup : I <= M * (b - a)).
  { apply seq_le with (u := fun n => dyadic g n a b) (v := fun _ => M * (b - a)).
    - intro n. eapply Rle_trans; [apply Rle_abs|]. apply dyadic_abs_bound; auto.
    - apply lint_cv_dyadic.
    - apply seq_const. }
  assert (Hlow : - (M * (b - a)) <= I).
  { apply seq_le with (u := fun _ => - (M * (b - a))) (v := fun n => dyadic g n a b).
    - intro n.
      assert (Hbnd : Rabs (dyadic g n a b) <= M * (b - a))
        by (apply dyadic_abs_bound; auto).
      apply Rle_trans with (- Rabs (dyadic g n a b)).
      + apply Ropp_le_contravar. exact Hbnd.
      + apply Rle_trans with (- - dyadic g n a b).
        * apply Ropp_le_contravar. rewrite <- Rabs_Ropp. apply Rle_abs.
        * right. rewrite Ropp_involutive. reflexivity.
    - apply seq_const.
    - apply lint_cv_dyadic. }
  apply Rabs_le. lra.
Qed.

Lemma lint_opp :
  forall g lo hi L HL Hlip Ho a b Ha Hab Hb Ha2 Hab2 Hb2,
    lint (fun x => - g x) lo hi L HL Ho a b Ha Hab Hb =
    - lint g lo hi L HL Hlip a b Ha2 Hab2 Hb2.
Proof.
  intros.
  apply UL_sequence with (fun n => dyadic (fun x => - g x) n a b).
  - apply lint_cv_dyadic.
  - eapply seq_ext.
    + intro n. symmetry. apply dyadic_opp.
    + (* - dyadic converges to - lint *)
      assert (Hcv := lint_cv_dyadic g lo hi L HL Hlip a b Ha2 Hab2 Hb2).
      unfold Un_cv in *. intros eps Heps.
      destruct (Hcv eps Heps) as [N HN].
      exists N. intros n Hn. specialize (HN n Hn).
      unfold R_dist in *.
      replace (- dyadic g n a b - - lint g lo hi L HL Hlip a b Ha2 Hab2 Hb2)
        with (- (dyadic g n a b - lint g lo hi L HL Hlip a b Ha2 Hab2 Hb2)) by ring.
      rewrite Rabs_Ropp. exact HN.
Qed.

Lemma lint_scal :
  forall g c lo hi Ls Lg (HLs : 0 <= Ls) (HLg : 0 <= Lg) Hlip Hs a b
    Ha Hab Hb Ha2 Hab2 Hb2,
    lint (fun x => c * g x) lo hi Ls HLs Hs a b Ha Hab Hb =
    c * lint g lo hi Lg HLg Hlip a b Ha2 Hab2 Hb2.
Proof.
  intros.
  apply UL_sequence with (fun n => dyadic (fun x => c * g x) n a b).
  - apply lint_cv_dyadic.
  - eapply seq_ext.
    + intro n. symmetry. apply dyadic_scal.
    + assert (Hcv := lint_cv_dyadic g lo hi Lg HLg Hlip a b Ha2 Hab2 Hb2).
      unfold Un_cv in *. intros eps Heps.
      destruct (Req_EM_T c 0) as [->|Hc].
      * exists 0%nat. intros n _. unfold R_dist.
        replace (0 * dyadic g n a b - 0 * lint g lo hi Lg HLg Hlip a b Ha2 Hab2 Hb2)
          with 0 by ring.
        rewrite Rabs_R0. exact Heps.
      * assert (Hcpos : 0 < Rabs c).
        { apply Rabs_pos_lt. exact Hc. }
        destruct (Hcv (eps / Rabs c) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
        exists N. intros n Hn. specialize (HN n Hn). unfold R_dist in *.
        replace (c * dyadic g n a b - c * lint g lo hi Lg HLg Hlip a b Ha2 Hab2 Hb2)
          with (c * (dyadic g n a b - lint g lo hi Lg HLg Hlip a b Ha2 Hab2 Hb2)) by ring.
        rewrite Rabs_mult.
        apply Rlt_le_trans with (Rabs c * (eps / Rabs c)).
        -- apply Rmult_lt_compat_l; [exact Hcpos | exact HN].
        -- assert (Rabs c * (eps / Rabs c) = eps) by (field; lra).
           rewrite H. apply Rle_refl.
Qed.

Lemma lint_plus :
  forall g h lo hi Lg Hg L HLg Hlipg HHg Hlih HL Hlip a b
    Hag Habg Hbg Hah Habh Hbh Ha Hab Hb,
    lint (fun x => g x + h x) lo hi L HL Hlip a b Ha Hab Hb =
    lint g lo hi Lg HLg Hlipg a b Hag Habg Hbg +
    lint h lo hi Hg HHg Hlih a b Hah Habh Hbh.
Proof.
  intros.
  apply UL_sequence with (fun n => dyadic (fun x => g x + h x) n a b).
  - apply lint_cv_dyadic.
  - eapply seq_ext.
    + intro n. symmetry. apply dyadic_plus.
    + apply CV_plus; apply lint_cv_dyadic.
Qed.

(* Oriented integral. a and b may be in either order.
   int_a^b = - int_b^a, and the value ignores the Lipschitz witness. *)
Definition int_seg (g : R -> R) (L a b : R) (HL : 0 <= L)
  (Hlip : forall x y,
      Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
      Rabs (g x - g y) <= L * Rabs (x - y)) : R :=
  match Rle_dec a b with
  | left Hab =>
      lint g (Rmin a b) (Rmax a b) L HL Hlip a b
        (Rmin_l a b) Hab (Rmax_r a b)
  | right Hn =>
      - lint g (Rmin a b) (Rmax a b) L HL Hlip b a
          (Rmin_r a b) (Rlt_le b a (Rnot_le_lt a b Hn)) (Rmax_l a b)
  end.

Lemma int_seg_pi :
  forall g L a b HL Hlip HL' Hlip',
    int_seg g L a b HL Hlip = int_seg g L a b HL' Hlip'.
Proof.
  intros g L a b HL Hlip HL' Hlip'.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab|Hn].
  - apply lint_irrel.
  - f_equal. apply lint_irrel.
Qed.

Lemma int_seg_ext :
  forall g h L a b HL Hlipg Hlih,
    (forall x, Rmin a b <= x <= Rmax a b -> g x = h x) ->
    int_seg g L a b HL Hlipg = int_seg h L a b HL Hlih.
Proof.
  intros g h L a b HL Hlipg Hlih Heq.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab|Hn].
  - apply lint_ext. intros x Hx. apply Heq.
    destruct Hx as [Hxa Hxb].
    split.
    + eapply Rle_trans; [apply Rmin_l | exact Hxa].
    + eapply Rle_trans; [exact Hxb | apply Rmax_r].
  - f_equal. apply lint_ext. intros x Hx.
    apply Heq.
    destruct Hx as [Hxb Hxa].
    split.
    + eapply Rle_trans; [apply Rmin_r | exact Hxb].
    + eapply Rle_trans; [exact Hxa | apply Rmax_l].
Qed.

Lemma int_seg_point : forall g L a HL Hlip, int_seg g L a a HL Hlip = 0.
Proof.
  intros. unfold int_seg.
  destruct (Rle_dec a a) as [Hab|Hn].
  - apply lint_point.
  - exfalso. apply Hn. apply Rle_refl.
Qed.

Lemma int_seg_swap :
  forall g L a b HL Hlip Hlip',
    int_seg g L a b HL Hlip = - int_seg g L b a HL Hlip'.
Proof.
  intros g L a b HL Hlip Hlip'.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab|Hn]; destruct (Rle_dec b a) as [Hba|Hnba].
  - assert (Heq : a = b) by (apply Rle_antisym; assumption).
    subst b.
    rewrite lint_point, lint_point. ring.
  - ring_simplify. apply lint_window_eq; [apply Rmin_comm | apply Rmax_comm].
  - apply Ropp_eq_compat. apply lint_window_eq; [apply Rmin_comm | apply Rmax_comm].
  - exfalso.
    apply (Rlt_irrefl a).
    apply Rlt_trans with b.
    + apply Rnot_le_lt. exact Hnba.
    + apply Rnot_le_lt. exact Hn.
Qed.

Lemma int_seg_opp :
  forall g L a b HL Hlip Ho,
    int_seg (fun x => - g x) L a b HL Ho = - int_seg g L a b HL Hlip.
Proof.
  intros g L a b HL Hlip Ho.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab|Hn].
  - rewrite (lint_opp g (Rmin a b) (Rmax a b) L HL Hlip Ho a b
      (Rmin_l a b) Hab (Rmax_r a b) (Rmin_l a b) Hab (Rmax_r a b)).
    reflexivity.
  - rewrite (lint_opp g (Rmin a b) (Rmax a b) L HL Hlip Ho b a
      (Rmin_r a b) (Rlt_le b a (Rnot_le_lt a b Hn)) (Rmax_l a b)
      (Rmin_r a b) (Rlt_le b a (Rnot_le_lt a b Hn)) (Rmax_l a b)).
    ring.
Qed.

Lemma int_seg_scal :
  forall g c L Lg a b (HL : 0 <= L) (HLg : 0 <= Lg) Hlip Hs,
    int_seg (fun x => c * g x) L a b HL Hs =
    c * int_seg g Lg a b HLg Hlip.
Proof.
  intros.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab|Hn].
  - rewrite (lint_scal g c (Rmin a b) (Rmax a b) L Lg HL HLg Hlip Hs a b
      (Rmin_l a b) Hab (Rmax_r a b) (Rmin_l a b) Hab (Rmax_r a b)).
    reflexivity.
  - rewrite (lint_scal g c (Rmin a b) (Rmax a b) L Lg HL HLg Hlip Hs b a
      (Rmin_r a b) (Rlt_le b a (Rnot_le_lt a b Hn)) (Rmax_l a b)
      (Rmin_r a b) (Rlt_le b a (Rnot_le_lt a b Hn)) (Rmax_l a b)).
    ring.
Qed.

Lemma int_seg_plus :
  forall g h Lg Hg L a b HLg Hlipg HHg Hlih HL Hlip,
    int_seg (fun x => g x + h x) L a b HL Hlip =
    int_seg g Lg a b HLg Hlipg + int_seg h Hg a b HHg Hlih.
Proof.
  intros.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab|Hn].
  - rewrite (lint_plus g h (Rmin a b) (Rmax a b) Lg Hg L HLg Hlipg HHg Hlih HL Hlip
      a b (Rmin_l a b) Hab (Rmax_r a b) (Rmin_l a b) Hab (Rmax_r a b)
      (Rmin_l a b) Hab (Rmax_r a b)).
    reflexivity.
  - set (Hba := Rlt_le b a (Rnot_le_lt a b Hn)).
    rewrite (lint_plus g h (Rmin a b) (Rmax a b) Lg Hg L HLg Hlipg HHg Hlih HL Hlip
      b a (Rmin_r a b) Hba (Rmax_l a b) (Rmin_r a b) Hba (Rmax_l a b)
      (Rmin_r a b) Hba (Rmax_l a b)).
    ring.
Qed.

Lemma int_seg_abs :
  forall g L a b HL Hlip M,
    a <= b ->
    (forall x, a <= x <= b -> Rabs (g x) <= M) ->
    Rabs (int_seg g L a b HL Hlip) <= M * (b - a).
Proof.
  intros g L a b HL Hlip M Hab HM.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab'|Hn]; [|exfalso; apply Hn; exact Hab].
  eapply Rle_trans.
  - apply lint_abs. exact HM.
  - right. reflexivity.
Qed.

(* The dyadic sequence does not depend on the window or the Lipschitz
   witness, so neither does the limit. *)
Lemma lint_irrel_gen :
  forall g lo hi L HL Hlip lo' hi' L' HL' Hlip' a b Ha Hab Hb Ha' Hab' Hb',
    lint g lo hi L HL Hlip a b Ha Hab Hb =
    lint g lo' hi' L' HL' Hlip' a b Ha' Hab' Hb'.
Proof.
  intros.
  apply UL_sequence with (fun n => dyadic g n a b); apply lint_cv_dyadic.
Qed.

Lemma int_seg_L :
  forall g L L' a b HL HL' Hlip Hlip',
    int_seg g L a b HL Hlip = int_seg g L' a b HL' Hlip'.
Proof.
  intros g L L' a b HL HL' Hlip Hlip'.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab|Hn].
  - apply lint_irrel_gen.
  - f_equal. apply lint_irrel_gen.
Qed.

Lemma dyadic_S :
  forall g k a b,
    dyadic g (S k) a b =
    dyadic g k a ((a + b) / 2) + dyadic g k ((a + b) / 2) b.
Proof. reflexivity. Qed.

Lemma dyadic_step_loc :
  forall g L k a b,
    0 <= L -> a <= b ->
    (forall x y, a <= x <= b -> a <= y <= b ->
       Rabs (g x - g y) <= L * Rabs (x - y)) ->
    Rabs (dyadic g (S k) a b - dyadic g k a b)
      <= L * (b - a) * (b - a) / 2 ^ (k + 2).
Proof.
  intros g L k a b HL Hab Hlip.
  rewrite <- !D_dyadic.
  apply (D_step g a b L Hlip k a b (Rle_refl a) Hab (Rle_refl b)).
Qed.

(* Splitting the level-(S k) sum at b on the left of the midpoint
   is the level-k gap on each half, plus one refinement step. *)
Lemma dyadic_gap_left :
  forall g k a b c,
    let m := (a + c) / 2 in
    let mbc := (b + c) / 2 in
    dyadic g (S k) a c - dyadic g (S k) a b - dyadic g (S k) b c =
    (dyadic g k a m - dyadic g k a b - dyadic g k b m)
    - (dyadic g k b mbc - dyadic g k b m - dyadic g k m mbc)
    + (dyadic g k m c - dyadic g k m mbc - dyadic g k mbc c)
    + (dyadic g k a b - dyadic g (S k) a b).
Proof.
  intros g k a b c m mbc. unfold m, mbc.
  rewrite !dyadic_S. ring.
Qed.

Lemma dyadic_gap_right :
  forall g k a b c,
    let m := (a + c) / 2 in
    let mab := (a + b) / 2 in
    let mbc := (b + c) / 2 in
    dyadic g (S k) a c - dyadic g (S k) a b - dyadic g (S k) b c =
    (dyadic g k m c - dyadic g k m b - dyadic g k b c)
    + (dyadic g k b c - dyadic g (S k) b c)
    + (dyadic g k a m - dyadic g k a mab - dyadic g k mab m)
    - (dyadic g k mab b - dyadic g k mab m - dyadic g k m b).
Proof.
  intros g k a b c m mab mbc. unfold m, mab, mbc.
  rewrite !dyadic_S. ring.
Qed.

Lemma pow_7_4_ge1 : forall k, 1 <= (7 / 4) ^ k.
Proof.
  induction k as [|k IH]; simpl; [lra|].
  apply Rle_trans with (1 * (7 / 4) ^ k); [|apply Rmult_le_compat_r; lra].
  lra.
Qed.

Lemma seven_eighth_ge_inv2 : forall k, / 2 ^ k <= (7 / 8) ^ k.
Proof.
  intro k.
  assert (H74 : 1 <= (7 / 4) ^ k) by apply pow_7_4_ge1.
  assert (Hpos : 0 < 2 ^ k) by apply pow2_pos.
  apply Rmult_le_reg_r with (2 ^ k); [exact Hpos|].
  rewrite Rinv_l; [|lra].
  apply Rle_trans with ((7 / 4) ^ k); [exact H74|].
  right. rewrite <- Rpow_mult_distr.
  replace (7 / 4) with (7 / 8 * 2) by field. reflexivity.
Qed.

Lemma gap_coef :
  forall k,
    3 / 2 * (7 / 8) ^ k + / 2 ^ (k + 2) <= 7 / 4 * (7 / 8) ^ k.
Proof.
  intro k.
  assert (Hr : 0 <= (7 / 8) ^ k).
  { apply pow_le. lra. }
  assert (Hge : / 2 ^ k <= (7 / 8) ^ k) by apply seven_eighth_ge_inv2.
  assert (H2 : 2 ^ (k + 2) = 4 * 2 ^ k).
  { replace (k + 2)%nat with (S (S k)) by lia. simpl. ring. }
  assert (Hinv : / 2 ^ (k + 2) = / 4 * / 2 ^ k).
  { rewrite H2. field. pose proof (pow2_pos k). lra. }
  rewrite Hinv.
  apply Rle_trans with (3 / 2 * (7 / 8) ^ k + / 4 * (7 / 8) ^ k).
  - apply Rplus_le_compat_l. apply Rmult_le_compat_l; [lra | exact Hge].
  - right. field.
Qed.

Lemma sqr_le_mono : forall p q, 0 <= p -> p <= q -> p * p <= q * q.
Proof.
  intros p q Hp Hpq. apply Rmult_le_compat; assumption.
Qed.

Lemma Rabs_lin4 : forall a b c d,
  Rabs (a + b + c + d) <= Rabs a + Rabs b + Rabs c + Rabs d.
Proof.
  intros a b c d.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat; [|apply Rle_refl].
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat; [|apply Rle_refl].
  apply Rabs_triang.
Qed.

Lemma Rabs_gap_left : forall a b c d,
  Rabs (a - b + c + d) <= Rabs a + Rabs b + Rabs c + Rabs d.
Proof.
  intros a b c d.
  replace (a - b + c + d) with (a + (- b) + c + d) by ring.
  eapply Rle_trans; [apply Rabs_lin4|].
  rewrite Rabs_Ropp. apply Rle_refl.
Qed.

Lemma Rabs_gap_right : forall a b c d,
  Rabs (a + b + c - d) <= Rabs a + Rabs b + Rabs c + Rabs d.
Proof.
  intros a b c d.
  replace (a + b + c - d) with (a + b + c + (- d)) by ring.
  eapply Rle_trans; [apply Rabs_lin4|].
  rewrite Rabs_Ropp. apply Rle_refl.
Qed.

(* |D_k(a,c) - D_k(a,b) - D_k(b,c)| decays geometrically, uniformly
   in the split. The three half-interval gaps plus one refinement
   step are absorbed by (7/8)^(k+1). *)
Lemma dyadic_gap_bound :
  forall k g L a b c,
    0 <= L -> a <= b -> b <= c ->
    (forall x y, a <= x <= c -> a <= y <= c ->
       Rabs (g x - g y) <= L * Rabs (x - y)) ->
    Rabs (dyadic g k a c - dyadic g k a b - dyadic g k b c)
      <= 2 * (7 / 8) ^ k * L * (c - a) * (c - a).
Proof.
  induction k as [|k IH]; intros g L a b c HL Hab Hbc Hlip.
  - simpl. unfold dyadic.
    replace ((c - a) * g a - (b - a) * g a - (c - b) * g b)
      with ((c - b) * (g a - g b)) by ring.
    rewrite Rabs_mult, (Rabs_right (c - b)) by lra.
    assert (Hgy : Rabs (g a - g b) <= L * (b - a)).
    { replace (b - a) with (Rabs (a - b)).
      - apply Hlip; lra.
      - rewrite Rabs_left1; lra. }
    apply Rle_trans with ((c - b) * (L * (b - a))).
    + apply Rmult_le_compat_l; [lra | exact Hgy].
    + replace ((c - b) * (L * (b - a))) with (L * ((c - b) * (b - a))) by ring.
      apply Rle_trans with (L * ((c - a) * (c - a))).
      * apply Rmult_le_compat_l; [exact HL|]. nra.
      * assert (0 <= (c - a) * (c - a)) by nra.
        replace (2 * (7 / 8) ^ 0) with 2 by (simpl; field).
        nra.
  - set (m := (a + c) / 2).
    assert (Ham : a <= m) by (unfold m; lra).
    assert (Hmc : m <= c) by (unfold m; lra).
    assert (Hlen : 0 <= c - a) by lra.
    assert (Hsq : (m - a) * (m - a) = (c - a) * (c - a) / 4).
    { unfold m. field. }
    destruct (Rle_dec b m) as [Hbm|Hnb].
    + set (mbc := (b + c) / 2).
      assert (Hord : b <= mbc /\ m <= mbc /\ mbc <= c) by (unfold mbc, m; lra).
      assert (Hsub : (mbc - b) * (mbc - b) <= (c - a) * (c - a) / 4).
      { assert (Hlenb : mbc - b = (c - b) / 2) by (unfold mbc; field).
        assert (Hsqb : (mbc - b) * (mbc - b) <= ((c - a) / 2) * ((c - a) / 2)).
        { apply sqr_le_mono; lra. }
        replace (((c - a) / 2) * ((c - a) / 2)) with ((c - a) * (c - a) / 4)
          in Hsqb by field.
        exact Hsqb. }
      assert (Hba : (b - a) * (b - a) <= (c - a) * (c - a)).
      { apply sqr_le_mono; lra. }
      rewrite dyadic_gap_left. fold m mbc.
      eapply Rle_trans; [apply Rabs_gap_left|].
      eapply Rle_trans.
      * apply Rplus_le_compat.
        -- apply Rplus_le_compat.
           ++ apply Rplus_le_compat.
              ** apply IH; [exact HL | exact Hab | exact Hbm |].
                 intros x y Hx Hy. apply Hlip; unfold m in Hx, Hy; lra.
              ** apply IH; [exact HL | exact Hbm | exact (proj1 (proj2 Hord)) |].
                 intros x y Hx Hy. apply Hlip; unfold mbc, m in Hx, Hy; lra.
           ++ apply IH; [exact HL | exact (proj1 (proj2 Hord)) | exact (proj2 (proj2 Hord)) |].
              intros x y Hx Hy. apply Hlip; unfold m, mbc in Hx, Hy; lra.
        -- rewrite Rabs_minus_sym.
           apply dyadic_step_loc; [exact HL | exact Hab |].
           intros x y Hx Hy. apply Hlip; lra.
      * assert (Hrec :
          2 * (7 / 8) ^ k * L * ((m - a) * (m - a))
          + 2 * (7 / 8) ^ k * L * ((mbc - b) * (mbc - b))
          + 2 * (7 / 8) ^ k * L * ((c - m) * (c - m))
          + L * (b - a) * (b - a) / 2 ^ (k + 2)
          <= 2 * (7 / 8) ^ S k * L * (c - a) * (c - a)).
        { assert (Hc := gap_coef k).
          assert (Hcm : (c - m) * (c - m) = (c - a) * (c - a) / 4).
          { unfold m. field. }
          rewrite Hsq, Hcm.
          apply Rle_trans with
            ((3 / 2 * (7 / 8) ^ k + / 2 ^ (k + 2)) * (L * (c - a) * (c - a))).
          - assert (0 <= L * (c - a) * (c - a)) by (repeat apply Rmult_le_pos; lra).
            assert (0 <= (7 / 8) ^ k) by (apply pow_le; lra).
            replace (2 * (7 / 8) ^ k * L * ((c - a) * (c - a) / 4))
              with ((7 / 8) ^ k * (L * (c - a) * (c - a)) / 2) by field.
            assert (Hshort :
              2 * (7 / 8) ^ k * L * ((mbc - b) * (mbc - b))
              <= (7 / 8) ^ k * (L * (c - a) * (c - a)) / 2).
            { apply Rle_trans with
                (2 * (7 / 8) ^ k * L * ((c - a) * (c - a) / 4)).
              { apply Rmult_le_compat_l; [repeat apply Rmult_le_pos; try lra; apply pow_le; lra | exact Hsub]. }
              { right. field. } }
            assert (Hstep :
              L * (b - a) * (b - a) / 2 ^ (k + 2)
              <= / 2 ^ (k + 2) * (L * ((c - a) * (c - a)))).
            { unfold Rdiv.
              replace (L * (b - a) * (b - a) * / 2 ^ (k + 2))
                with (/ 2 ^ (k + 2) * (L * ((b - a) * (b - a)))) by ring.
              apply Rmult_le_compat_l.
              { apply Rlt_le, Rinv_0_lt_compat, pow2_pos. }
              { apply Rmult_le_compat_l; [exact HL | exact Hba]. } }
            nra.
          - apply Rle_trans with
              ((7 / 4 * (7 / 8) ^ k) * (L * (c - a) * (c - a))).
            { apply Rmult_le_compat_r.
              { repeat apply Rmult_le_pos; lra. }
              { exact Hc. } }
            { right. simpl. field. } }
        eapply Rle_trans; [|exact Hrec]. right. ring.
    + assert (Hmb : m <= b).
      { apply Rlt_le. apply Rnot_le_lt. exact Hnb. }
      set (mab := (a + b) / 2).
      set (mbc := (b + c) / 2).
      assert (Hord : a <= mab /\ mab <= m /\ m <= b /\ b <= mbc /\ mbc <= c).
      { unfold mab, mbc, m. nra. }
      assert (Hsub : (b - mab) * (b - mab) <= (c - a) * (c - a) / 4).
      { assert (Hsqb : (b - mab) * (b - mab) <= ((c - a) / 2) * ((c - a) / 2)).
        { apply sqr_le_mono. { unfold mab; lra. } unfold mab; lra. }
        replace (((c - a) / 2) * ((c - a) / 2)) with ((c - a) * (c - a) / 4)
          in Hsqb by field.
        exact Hsqb. }
      assert (Hcb : (c - b) * (c - b) <= (c - a) * (c - a)).
      { apply sqr_le_mono; lra. }
      rewrite dyadic_gap_right. fold m mab mbc.
      eapply Rle_trans; [apply Rabs_gap_right|].
      eapply Rle_trans.
      * apply Rplus_le_compat.
        -- apply Rplus_le_compat.
           ++ apply Rplus_le_compat.
              ** apply IH; [exact HL | exact Hmb | exact Hbc |].
                 intros x y Hx Hy. apply Hlip; unfold m in Hx, Hy; lra.
              ** rewrite Rabs_minus_sym.
                 apply dyadic_step_loc; [exact HL | exact Hbc |].
                 intros x y Hx Hy. apply Hlip; lra.
           ++ apply IH; [exact HL | exact (proj1 Hord) | exact (proj1 (proj2 Hord)) |].
              intros x y Hx Hy. apply Hlip; unfold m, mab in Hx, Hy; lra.
        -- apply IH; [exact HL | exact (proj1 (proj2 Hord)) | exact Hmb |].
           intros x y Hx Hy. apply Hlip; unfold mab, m in Hx, Hy; lra.
      * assert (Hrec :
          2 * (7 / 8) ^ k * L * ((c - m) * (c - m))
          + L * (c - b) * (c - b) / 2 ^ (k + 2)
          + 2 * (7 / 8) ^ k * L * ((m - a) * (m - a))
          + 2 * (7 / 8) ^ k * L * ((b - mab) * (b - mab))
          <= 2 * (7 / 8) ^ S k * L * (c - a) * (c - a)).
        { assert (Hc := gap_coef k).
          assert (Hcm : (c - m) * (c - m) = (c - a) * (c - a) / 4).
          { unfold m. field. }
          rewrite Hsq, Hcm.
          apply Rle_trans with
            ((3 / 2 * (7 / 8) ^ k + / 2 ^ (k + 2)) * (L * (c - a) * (c - a))).
          - assert (0 <= (7 / 8) ^ k) by (apply pow_le; lra).
            replace (2 * (7 / 8) ^ k * L * ((c - a) * (c - a) / 4))
              with ((7 / 8) ^ k * (L * (c - a) * (c - a)) / 2) by field.
            assert (Hshort :
              2 * (7 / 8) ^ k * L * ((b - mab) * (b - mab))
              <= (7 / 8) ^ k * (L * (c - a) * (c - a)) / 2).
            { apply Rle_trans with
                (2 * (7 / 8) ^ k * L * ((c - a) * (c - a) / 4)).
              { apply Rmult_le_compat_l; [repeat apply Rmult_le_pos; try lra; apply pow_le; lra | exact Hsub]. }
              { right. field. } }
            assert (Hstep :
              L * (c - b) * (c - b) / 2 ^ (k + 2)
              <= / 2 ^ (k + 2) * (L * ((c - a) * (c - a)))).
            { unfold Rdiv.
              replace (L * (c - b) * (c - b) * / 2 ^ (k + 2))
                with (/ 2 ^ (k + 2) * (L * ((c - b) * (c - b)))) by ring.
              apply Rmult_le_compat_l.
              { apply Rlt_le, Rinv_0_lt_compat, pow2_pos. }
              { apply Rmult_le_compat_l; [exact HL | exact Hcb]. } }
            nra.
          - apply Rle_trans with
              ((7 / 4 * (7 / 8) ^ k) * (L * (c - a) * (c - a))).
            { apply Rmult_le_compat_r.
              { repeat apply Rmult_le_pos; lra. }
              { exact Hc. } }
            { right. simpl. field. } }
        eapply Rle_trans; [|exact Hrec]. right. ring.
Qed.

Lemma seq_scale_0 :
  forall (u : nat -> R) (c : R), Un_cv u 0 -> Un_cv (fun n => c * u n) 0.
Proof.
  intros u c Hu eps Heps.
  destruct (Req_EM_T c 0) as [->|Hc].
  - exists 0%nat. intros n _. unfold R_dist. rewrite Rmult_0_l, Rminus_0_r, Rabs_R0.
    exact Heps.
  - assert (Hcpos : 0 < Rabs c) by (apply Rabs_pos_lt; exact Hc).
    destruct (Hu (eps / Rabs c) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn). unfold R_dist in *.
    rewrite Rminus_0_r in HN. rewrite Rminus_0_r.
    rewrite Rabs_mult.
    apply Rlt_le_trans with (Rabs c * (eps / Rabs c)).
    + apply Rmult_lt_compat_l; [exact Hcpos | exact HN].
    + right. field. lra.
Qed.

Lemma seq_abs_cv :
  forall (u : nat -> R) l, Un_cv u l -> Un_cv (fun n => Rabs (u n)) (Rabs l).
Proof.
  intros u l Hu eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn). unfold R_dist in *.
  apply Rle_lt_trans with (Rabs (u n - l)); [apply Rabs_triang_inv2 | exact HN].
Qed.

Lemma cv_bound_0 :
  forall (u v : nat -> R) l,
    Un_cv u l ->
    (forall n, Rabs (u n) <= v n) ->
    Un_cv v 0 ->
    l = 0.
Proof.
  intros u v l Hu Hle Hv.
  assert (Habs : Un_cv (fun n => Rabs (u n)) (Rabs l)) by (apply seq_abs_cv; exact Hu).
  assert (Hle0 : Rabs l <= 0).
  { apply seq_le with (u := fun n => Rabs (u n)) (v := v); assumption. }
  assert (0 <= Rabs l) by apply Rabs_pos.
  assert (Hz : Rabs l = 0) by lra.
  destruct (Rle_dec 0 l) as [Hp|Hn].
  - rewrite (Rabs_right l) in Hz by lra. exact Hz.
  - apply Rnot_le_lt in Hn. rewrite (Rabs_left l) in Hz by lra. lra.
Qed.

Lemma pow78_to_0 : Un_cv (fun n => (7 / 8) ^ n) 0.
Proof.
  intros eps Heps.
  destruct (pow_lt_1_zero (7 / 8) ltac:(rewrite Rabs_right; lra) eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn). unfold R_dist.
  rewrite Rminus_0_r. rewrite Rabs_right by (apply Rle_ge, pow_le; lra).
  rewrite Rabs_right in HN by (apply Rle_ge, pow_le; lra). exact HN.
Qed.

Lemma lint_add :
  forall g lo hi L (HL : 0 <= L) Hlip a b c Ha Hab Hbi Hac Hc Hbc,
    lint g lo hi L HL Hlip a c Ha Hac Hc =
    lint g lo hi L HL Hlip a b Ha Hab Hbi +
    lint g lo hi L HL Hlip b c (Rle_trans _ _ _ Ha Hab) Hbc Hc.
Proof.
  intros g lo hi L HL Hlip a b c Ha Hab Hbi Hac Hc Hbc.
  set (gap := fun k =>
    dyadic g k a c - dyadic g k a b - dyadic g k b c).
  assert (Hcv : Un_cv gap
    (lint g lo hi L HL Hlip a c Ha Hac Hc -
     lint g lo hi L HL Hlip a b Ha Hab Hbi -
     lint g lo hi L HL Hlip b c (Rle_trans _ _ _ Ha Hab) Hbc Hc)).
  { unfold gap.
    apply CV_minus.
    - apply CV_minus; apply lint_cv_dyadic.
    - apply lint_cv_dyadic. }
  assert (Hbd : forall k, Rabs (gap k) <=
      2 * (7 / 8) ^ k * L * (c - a) * (c - a)).
  { intro k. unfold gap. apply dyadic_gap_bound; [exact HL | exact Hab | exact Hbc |].
    intros x y Hx Hy. apply Hlip; lra. }
  assert (H0 : Un_cv (fun k => 2 * (7 / 8) ^ k * L * (c - a) * (c - a)) 0).
  { apply seq_ext with (u := fun k => (2 * L * (c - a) * (c - a)) * (7 / 8) ^ k).
    - intro k. ring.
    - apply seq_scale_0. apply pow78_to_0. }
  assert (He : lint g lo hi L HL Hlip a c Ha Hac Hc -
               lint g lo hi L HL Hlip a b Ha Hab Hbi -
               lint g lo hi L HL Hlip b c (Rle_trans _ _ _ Ha Hab) Hbc Hc = 0).
  { apply cv_bound_0 with
      (u := gap)
      (v := fun k => 2 * (7 / 8) ^ k * L * (c - a) * (c - a));
      assumption. }
  lra.
Qed.

Lemma int_seg_add :
  forall g L a b c (HL : 0 <= L)
    (Hlipac : forall x y,
        Rmin a c <= x <= Rmax a c -> Rmin a c <= y <= Rmax a c ->
        Rabs (g x - g y) <= L * Rabs (x - y))
    (Hlipab : forall x y,
        Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
        Rabs (g x - g y) <= L * Rabs (x - y))
    (Hlipbc : forall x y,
        Rmin b c <= x <= Rmax b c -> Rmin b c <= y <= Rmax b c ->
        Rabs (g x - g y) <= L * Rabs (x - y)),
    a <= b -> b <= c ->
    int_seg g L a c HL Hlipac =
    int_seg g L a b HL Hlipab + int_seg g L b c HL Hlipbc.
Proof.
  intros g L a b c HL Hlipac Hlipab Hlipbc Hab Hbc.
  assert (Hac0 : a <= c) by lra.
  assert (Hlip : forall x y, a <= x <= c -> a <= y <= c ->
            Rabs (g x - g y) <= L * Rabs (x - y)).
  { intros x y Hx Hy. apply Hlipac.
    - split; [apply Rle_trans with a; [apply Rmin_l | exact (proj1 Hx)]
             | apply Rle_trans with c; [exact (proj2 Hx) | apply Rmax_r]].
    - split; [apply Rle_trans with a; [apply Rmin_l | exact (proj1 Hy)]
             | apply Rle_trans with c; [exact (proj2 Hy) | apply Rmax_r]]. }
  unfold int_seg.
  destruct (Rle_dec a c) as [Hac|Hnac]; [|exfalso; apply Hnac; exact Hac0].
  destruct (Rle_dec a b) as [Hab'|Hnab]; [|exfalso; apply Hnab; exact Hab].
  destruct (Rle_dec b c) as [Hbc'|Hnbc]; [|exfalso; apply Hnbc; exact Hbc].
  rewrite <- (lint_irrel_gen g a c L HL Hlip (Rmin a c) (Rmax a c) L HL Hlipac
    a c (Rle_refl a) Hac (Rle_refl c) (Rmin_l a c) Hac (Rmax_r a c)).
  rewrite (lint_add g a c L HL Hlip a b c
    (Rle_refl a) Hab (Rle_trans _ _ _ Hbc (Rle_refl c))
    Hac (Rle_refl c) Hbc').
  apply f_equal2; apply lint_irrel_gen.
Qed.

Lemma int_seg_abs_sym :
  forall g L a b HL Hlip M,
    (forall x, Rmin a b <= x <= Rmax a b -> Rabs (g x) <= M) ->
    Rabs (int_seg g L a b HL Hlip) <= M * Rabs (b - a).
Proof.
  intros g L a b HL Hlip M HM.
  destruct (Rle_dec a b) as [Hab|Hba].
  - rewrite (Rabs_right (b - a)) by lra.
    apply int_seg_abs; [exact Hab|].
    intros x Hx. apply HM.
    split; [apply Rle_trans with a; [apply Rmin_l | exact (proj1 Hx)]
           | apply Rle_trans with b; [exact (proj2 Hx) | apply Rmax_r]].
  - assert (Hlt : b <= a) by (apply Rlt_le, Rnot_le_lt; exact Hba).
    assert (Hlip' : forall x y,
        Rmin b a <= x <= Rmax b a -> Rmin b a <= y <= Rmax b a ->
        Rabs (g x - g y) <= L * Rabs (x - y)).
    { intros x y Hx Hy.
      rewrite (Rmin_comm b a), (Rmax_comm b a) in Hx, Hy.
      apply Hlip; assumption. }
    rewrite (int_seg_swap g L a b HL Hlip Hlip').
    rewrite Rabs_Ropp. rewrite (Rabs_left1 (b - a)) by lra.
    replace (- (b - a)) with (a - b) by ring.
    apply int_seg_abs; [exact Hlt|].
    intros x Hx. apply HM.
    split; [apply Rle_trans with b; [apply Rmin_r | exact (proj1 Hx)]
           | apply Rle_trans with a; [exact (proj2 Hx) | apply Rmax_l]].
Qed.

Print Assumptions lint_error.
Print Assumptions cos_lip.
Print Assumptions fresnel_C.
Print Assumptions fresnel_C_error.
