(* ============================================================================
   NetTopologySuite.Proofs.Polynomial
   ----------------------------------------------------------------------------
   Linear and quadratic polynomials over R, their roots and basic properties.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real.
Open Scope R_scope.

Definition linear (a b x : R) : R := a * x + b.
Definition quadratic (a b c x : R) : R := a * x * x + b * x + c.

Lemma linear_value_at_zero : forall a b, linear a b 0 = b.
Proof. intros. unfold linear. ring. Qed.

Lemma linear_root_when_a_nonzero : forall a b,
  a <> 0 -> linear a b (- b / a) = 0.
Proof. intros a b H. unfold linear. field. exact H. Qed.

Lemma linear_constant_when_a_zero : forall b x, linear 0 b x = b.
Proof. intros. unfold linear. ring. Qed.

Lemma linear_monotone_when_a_pos : forall a b x y,
  a > 0 -> x <= y -> linear a b x <= linear a b y.
Proof. intros. unfold linear. nra. Qed.

Lemma linear_antimonotone_when_a_neg : forall a b x y,
  a < 0 -> x <= y -> linear a b y <= linear a b x.
Proof. intros. unfold linear. nra. Qed.

Lemma quadratic_at_zero : forall a b c, quadratic a b c 0 = c.
Proof. intros. unfold quadratic. ring. Qed.

Lemma quadratic_at_one : forall a b c, quadratic a b c 1 = a + b + c.
Proof. intros. unfold quadratic. ring. Qed.

Lemma quadratic_value_neg : forall a b c x,
  quadratic a b c (- x) = a * x * x - b * x + c.
Proof. intros. unfold quadratic. ring. Qed.

Lemma quadratic_sum_two_roots : forall a b c x y,
  quadratic a b c x = 0 ->
  quadratic a b c y = 0 ->
  a <> 0 ->
  x <> y ->
  a * (x + y) = - b.
Proof.
  intros a b c x y Hx Hy Ha Hne.
  (* (a x² + b x + c) - (a y² + b y + c) = 0 *)
  assert (a * (x - y) * (x + y) + b * (x - y) = 0).
  { unfold quadratic in *. nra. }
  assert (a * (x + y) + b = 0).
  { assert (x - y <> 0) by lra.
    apply (Rmult_eq_reg_l (x - y)); [|lra].
    rewrite Rmult_0_r. nra. }
  lra.
Qed.

Definition discriminant (a b c : R) : R := b * b - 4 * a * c.

Lemma discriminant_at_zero_c : forall a b, discriminant a b 0 = b * b.
Proof. intros. unfold discriminant. ring. Qed.

Lemma discriminant_when_b_zero : forall a c, discriminant a 0 c = - (4 * a * c).
Proof. intros. unfold discriminant. ring. Qed.

Lemma discriminant_nonneg_for_real_roots_helper : forall a b c x,
  a <> 0 ->
  quadratic a b c x = 0 ->
  (2 * a * x + b) * (2 * a * x + b) = discriminant a b c.
Proof.
  intros a b c x Ha Hx. unfold quadratic, discriminant in *. nra.
Qed.

Lemma discriminant_real_root_implies_nonneg : forall a b c x,
  a <> 0 ->
  quadratic a b c x = 0 ->
  0 <= discriminant a b c.
Proof.
  intros a b c x Ha Hx.
  pose proof (discriminant_nonneg_for_real_roots_helper a b c x Ha Hx).
  rewrite <- H. apply sq_nonneg'.
Qed.

Lemma quadratic_value_nonneg_when_a_pos_and_disc_le_0 : forall a b c x,
  a > 0 ->
  discriminant a b c <= 0 ->
  0 <= 4 * a * quadratic a b c x.
Proof.
  intros a b c x Ha Hdisc. unfold quadratic, discriminant in *.
  (* 4a(ax² + bx + c) = (2ax + b)² + (4ac - b²) = (2ax+b)² - disc >= -disc >= 0 *)
  pose proof (sq_nonneg' (2 * a * x + b)). nra.
Qed.

Lemma quadratic_complete_square : forall a b c x,
  a <> 0 ->
  4 * a * quadratic a b c x =
  (2 * a * x + b) * (2 * a * x + b) - discriminant a b c.
Proof.
  intros. unfold quadratic, discriminant. ring.
Qed.

Lemma linear_eq_zero_iff : forall a b x,
  a <> 0 -> (linear a b x = 0 <-> x = - b / a).
Proof.
  intros a b x Ha. unfold linear. split; intros H.
  - field_simplify_eq; [|exact Ha]. nra.
  - rewrite H. field. exact Ha.
Qed.

Lemma quadratic_factor_difference_of_roots : forall a x y z,
  a * (z - x) * (z - y) = a * z * z - a * (x + y) * z + a * x * y.
Proof. intros. ring. Qed.

Lemma sum_of_squares_zero : forall a b : R, a * a + b * b = 0 -> a = 0 /\ b = 0.
Proof. intros. apply sum_two_squares_zero_iff. exact H. Qed.

Lemma linear_minus_b_a_zero : forall a b,
  a <> 0 -> a * (- b / a) + b = 0.
Proof. intros a b Ha. field. exact Ha. Qed.

Lemma quadratic_a_zero_is_linear : forall b c x,
  quadratic 0 b c x = b * x + c.
Proof. intros. unfold quadratic. ring. Qed.

Lemma discriminant_completes_quad_id : forall a b c,
  4 * a * c + discriminant a b c = b * b.
Proof. intros. unfold discriminant. ring. Qed.

Lemma quadratic_neg_a : forall a b c x,
  quadratic (- a) b c x = - quadratic a (- b) (- c) x + 0.
Proof. intros. unfold quadratic. ring. Qed.
