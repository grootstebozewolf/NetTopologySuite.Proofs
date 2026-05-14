(* ============================================================================
   NetTopologySuite.Proofs.Real
   ----------------------------------------------------------------------------
   Small real-number facts that every downstream module re-derives in passing.
   Pulled out here so they have one canonical name.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Lemma R_zero_le_one : 0 <= 1. Proof. lra. Qed.
Lemma R_one_minus_zero : 1 - 0 = 1. Proof. lra. Qed.
Lemma R_one_minus_one : 1 - 1 = 0. Proof. lra. Qed.

Lemma sq_nonneg' : forall x : R, 0 <= x * x.
Proof. intros x. pose proof (Rle_0_sqr x). unfold Rsqr in *. lra. Qed.

Lemma sq_pos_if_nonzero : forall x : R, x <> 0 -> 0 < x * x.
Proof.
  intros x H. pose proof (Rle_0_sqr x). unfold Rsqr in *.
  destruct (Req_dec (x * x) 0) as [Heq | Hne]; [|lra].
  exfalso. apply H. apply Rsqr_0_uniq. unfold Rsqr. exact Heq.
Qed.

Lemma sq_eq_zero_iff : forall x : R, x * x = 0 <-> x = 0.
Proof.
  intros x. split.
  - intros H. apply Rsqr_0_uniq. unfold Rsqr. exact H.
  - intros H. rewrite H. ring.
Qed.

Lemma sq_neg : forall x : R, (- x) * (- x) = x * x.
Proof. intros x. ring. Qed.

Lemma cube_neg : forall x : R, (- x) * (- x) * (- x) = - (x * x * x).
Proof. intros x. ring. Qed.

Lemma sum_two_squares_nonneg : forall a b : R, 0 <= a * a + b * b.
Proof. intros a b. pose proof (sq_nonneg' a). pose proof (sq_nonneg' b). lra. Qed.

Lemma sum_two_squares_zero_iff : forall a b : R,
  a * a + b * b = 0 <-> a = 0 /\ b = 0.
Proof.
  intros a b. split.
  - intros H. pose proof (sq_nonneg' a). pose proof (sq_nonneg' b).
    assert (a * a = 0) by lra. assert (b * b = 0) by lra.
    split; apply sq_eq_zero_iff; assumption.
  - intros [Ha Hb]. rewrite Ha, Hb. ring.
Qed.

Lemma Rmult_le_one : forall a b : R,
  0 <= a -> a <= 1 -> 0 <= b -> b <= 1 -> a * b <= 1.
Proof. intros. nra. Qed.

Lemma Rmult_nonneg_nonneg : forall a b : R,
  0 <= a -> 0 <= b -> 0 <= a * b.
Proof. intros. nra. Qed.

Lemma Rmult_nonneg_nonpos_le_zero : forall a b : R,
  0 <= a -> b <= 0 -> a * b <= 0.
Proof. intros. nra. Qed.

Lemma Rmult_pos_pos : forall a b : R, 0 < a -> 0 < b -> 0 < a * b.
Proof. intros. nra. Qed.

Lemma Rmult_self_le : forall a : R, 0 <= a -> a <= 1 -> a * a <= a.
Proof. intros a Ha Ha1. nra. Qed.

Lemma Rabs_sq : forall x : R, Rabs x * Rabs x = x * x.
Proof.
  intros x. destruct (Rle_or_lt 0 x) as [H | H].
  - rewrite Rabs_right; lra.
  - rewrite Rabs_left; [ring | lra].
Qed.

Lemma Rabs_nonneg : forall x : R, 0 <= Rabs x.
Proof. apply Rabs_pos. Qed.

Lemma Rabs_zero_iff : forall x : R, Rabs x = 0 <-> x = 0.
Proof.
  intros x. split.
  - intros H. destruct (Req_dec x 0) as [Heq | Hne]; [exact Heq |].
    exfalso. pose proof (Rabs_pos_lt x Hne). lra.
  - intros H. rewrite H. apply Rabs_R0.
Qed.

Lemma sub_neg : forall a b : R, - (a - b) = b - a.
Proof. intros. ring. Qed.

Lemma sub_sub_self : forall a b : R, a - (a - b) = b.
Proof. intros. ring. Qed.

Lemma mul_sub_distrib : forall a b c : R, a * (b - c) = a * b - a * c.
Proof. intros. ring. Qed.

Lemma add_sub_assoc : forall a b c : R, a + b - c = a + (b - c).
Proof. intros. ring. Qed.

Lemma Rmax_l_le : forall a b : R, a <= Rmax a b.
Proof. apply Rmax_l. Qed.
Lemma Rmax_r_le : forall a b : R, b <= Rmax a b.
Proof. apply Rmax_r. Qed.
Lemma Rmin_l_le : forall a b : R, Rmin a b <= a.
Proof. apply Rmin_l. Qed.
Lemma Rmin_r_le : forall a b : R, Rmin a b <= b.
Proof. apply Rmin_r. Qed.
Lemma Rmin_le_Rmax : forall a b : R, Rmin a b <= Rmax a b.
Proof.
  intros a b. pose proof (Rmin_l a b). pose proof (Rmax_l a b). lra.
Qed.

Lemma double_sq : forall x : R, (2 * x) * (2 * x) = 4 * (x * x).
Proof. intros. ring. Qed.

Lemma quotient_two_sq : forall x : R, (x / 2) * (x / 2) = (x * x) / 4.
Proof. intros. field. Qed.

Lemma neg_div_two : forall x : R, - (x / 2) = (- x) / 2.
Proof. intros. field. Qed.

Lemma half_plus_half : forall x : R, x / 2 + x / 2 = x.
Proof. intros. field. Qed.

Lemma R_zero_lt_two : (0 < 2).
Proof. lra. Qed.

Lemma R_two_neq_zero : (2 <> 0).
Proof. lra. Qed.

Lemma Rmult_sign : forall a b : R, a * b > 0 -> (a > 0 /\ b > 0) \/ (a < 0 /\ b < 0).
Proof.
  intros a b H.
  destruct (Rtotal_order a 0) as [Ha | [Ha | Ha]].
  - destruct (Rtotal_order b 0) as [Hb | [Hb | Hb]].
    + right. split; assumption.
    + subst. nra.
    + nra.
  - subst. nra.
  - destruct (Rtotal_order b 0) as [Hb | [Hb | Hb]].
    + nra.
    + subst. nra.
    + left. split; assumption.
Qed.

Lemma Rplus_pos_of_pos : forall a b : R, 0 < a -> 0 <= b -> 0 < a + b.
Proof. intros. lra. Qed.

Lemma Rplus_nonneg : forall a b : R, 0 <= a -> 0 <= b -> 0 <= a + b.
Proof. intros. lra. Qed.

Lemma Rsub_self_eq_zero : forall a : R, a - a = 0.
Proof. intros. ring. Qed.

Lemma Rmult_zero_l_iff : forall a b : R, a * b = 0 -> a = 0 \/ b = 0.
Proof. apply Rmult_integral. Qed.

Lemma Rmult_pos_iff : forall a b : R, a > 0 -> (a * b > 0 <-> b > 0).
Proof.
  intros a b Ha. split.
  - intros H. nra.
  - intros H. nra.
Qed.

Lemma Rabs_eq_abs : forall x : R, Rabs (- x) = Rabs x.
Proof. apply Rabs_Ropp. Qed.

Lemma sq_abs : forall x : R, Rabs x * Rabs x = x * x.
Proof. apply Rabs_sq. Qed.

Lemma sq_le_iff_abs_le : forall x t,
  0 <= t -> (x * x <= t * t <-> Rabs x <= t).
Proof.
  intros x t Ht. split.
  - intros H. apply Rsqr_incr_0_var.
    + unfold Rsqr. rewrite Rabs_sq. exact H.
    + exact Ht.
  - intros H. rewrite <- (Rabs_sq x).
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact H | exact H].
Qed.

Lemma R_eq_implies_diff_zero : forall a b : R, a = b -> a - b = 0.
Proof. intros. lra. Qed.

Lemma R_diff_zero_implies_eq : forall a b : R, a - b = 0 -> a = b.
Proof. intros. lra. Qed.
