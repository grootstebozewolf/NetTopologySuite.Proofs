(* ============================================================================
   NetTopologySuite.Proofs.Atan2RatanBridge
   ----------------------------------------------------------------------------
   JTS Math.atan2 / NTS Angle.  claimId: none.

   Category C bridge: the historical quadrant body of atan2, built on
   Stdlib Ratan.atan, equals the 3-axiom Atan2.atan2.  Downstream
   statements that still mention `atan` rewrite through atan2_eq_ratan.
   This file pulls Classical_Prop.classic via Ratan and stays on
   docs/audit-exceptions.txt.  No Axiom, Parameter, or Admitted.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Atan2.
Local Open Scope R_scope.

(* Historical JTS quadrant form.  Range (-PI, PI], origin 0. *)
Definition atan2_ratan (y x : R) : R :=
  if Rlt_dec 0 x then atan (y / x)
  else if Rlt_dec x 0 then
         (if Rle_dec 0 y then atan (y / x) + PI else atan (y / x) - PI)
  else
         (if Rlt_dec 0 y then PI / 2
          else if Rlt_dec y 0 then - (PI / 2)
          else 0).

Lemma cos_atan_ratio : forall x y : R, x <> 0 ->
  cos (atan (y / x)) = Rabs x / sqrt (x * x + y * y).
Proof.
  intros x y Hx. rewrite cos_atan. unfold Rsqr.
  assert (Hxx : 0 < x * x) by (destruct (Rdichotomy x 0 Hx); nra).
  assert (E : 1 + y / x * (y / x) = (x * x + y * y) / (x * x))
    by (field; exact Hx).
  rewrite E, sqrt_div_alt by exact Hxx.
  assert (Hs : sqrt (x * x) = Rabs x).
  { replace (x * x) with (Rsqr x) by (unfold Rsqr; ring). apply sqrt_Rsqr_abs. }
  rewrite Hs.
  assert (Hr : 0 < sqrt (x * x + y * y)) by (apply sqrt_lt_R0; nra).
  assert (Ha : Rabs x <> 0) by (apply Rabs_no_R0; exact Hx).
  field. split; [ lra | exact Ha ].
Qed.

Lemma sin_atan_ratio : forall x y : R, x <> 0 ->
  sin (atan (y / x)) = y / x * (Rabs x / sqrt (x * x + y * y)).
Proof.
  intros x y Hx.
  rewrite <- (cos_atan_ratio x y Hx).
  rewrite sin_atan, cos_atan.
  assert (Hpos : 0 < sqrt (1 + Rsqr (y / x))).
  { apply sqrt_lt_R0. assert (0 <= Rsqr (y / x)) by apply Rle_0_sqr. lra. }
  field. lra.
Qed.

Lemma cos_atan2_ratan : forall x y : R, ~ (x = 0 /\ y = 0) ->
  cos (atan2_ratan y x) = x / sqrt (x * x + y * y).
Proof.
  intros x y Hxy. assert (Hr := atan2_r_pos x y Hxy).
  unfold atan2_ratan.
  destruct (Rlt_dec 0 x) as [Hx|Hx].
  - rewrite cos_atan_ratio by lra. rewrite (Rabs_right x) by lra. reflexivity.
  - destruct (Rlt_dec x 0) as [Hx2|Hx2].
    + destruct (Rle_dec 0 y) as [Hy|Hy].
      * rewrite neg_cos, cos_atan_ratio by lra.
        rewrite (Rabs_left x) by lra. field. lra.
      * rewrite cos_minus, cos_PI, sin_PI.
        rewrite cos_atan_ratio by lra.
        rewrite (Rabs_left x) by lra. field. lra.
    + assert (x = 0) by lra. subst x.
      destruct (Rlt_dec 0 y) as [Hy|Hy].
      * rewrite cos_PI2. field. lra.
      * destruct (Rlt_dec y 0) as [Hy2|Hy2].
        -- rewrite cos_neg, cos_PI2. field. lra.
        -- exfalso. apply Hxy. split; [ reflexivity | lra ].
Qed.

Lemma sin_atan2_ratan : forall x y : R, ~ (x = 0 /\ y = 0) ->
  sin (atan2_ratan y x) = y / sqrt (x * x + y * y).
Proof.
  intros x y Hxy. assert (Hr := atan2_r_pos x y Hxy).
  unfold atan2_ratan.
  destruct (Rlt_dec 0 x) as [Hx|Hx].
  - rewrite sin_atan_ratio by lra. rewrite (Rabs_right x) by lra. field. lra.
  - destruct (Rlt_dec x 0) as [Hx2|Hx2].
    + destruct (Rle_dec 0 y) as [Hy|Hy].
      * rewrite neg_sin, sin_atan_ratio by lra.
        rewrite (Rabs_left x) by lra. field. lra.
      * rewrite sin_minus, cos_PI, sin_PI.
        rewrite sin_atan_ratio by lra.
        rewrite (Rabs_left x) by lra. field. lra.
    + assert (x = 0) by lra. subst x.
      assert (Hyy : sqrt (0 * 0 + y * y) = Rabs y).
      { replace (0 * 0 + y * y) with (Rsqr y) by (unfold Rsqr; ring).
        apply sqrt_Rsqr_abs. }
      destruct (Rlt_dec 0 y) as [Hy|Hy].
      * rewrite sin_PI2, Hyy, (Rabs_right y) by lra. field. lra.
      * destruct (Rlt_dec y 0) as [Hy2|Hy2].
        -- rewrite sin_neg, sin_PI2, Hyy, (Rabs_left y) by lra. field. lra.
        -- exfalso. apply Hxy. split; [ reflexivity | lra ].
Qed.

Lemma div_nonpos_of_neg_denom : forall x y : R, x < 0 -> 0 <= y -> y / x <= 0.
Proof.
  intros x y Hx Hy. unfold Rdiv.
  assert (/ x < 0) by (apply Rinv_lt_0_compat; exact Hx). nra.
Qed.

Lemma div_pos_of_neg_neg : forall x y : R, x < 0 -> y < 0 -> 0 < y / x.
Proof.
  intros x y Hx Hy. unfold Rdiv.
  assert (/ x < 0) by (apply Rinv_lt_0_compat; exact Hx). nra.
Qed.

Lemma atan_le_0 : forall t : R, t <= 0 -> atan t <= 0.
Proof.
  intros t Ht. destruct (Req_dec t 0) as [E|E].
  - subst; rewrite atan_0; lra.
  - rewrite <- atan_0. apply Rlt_le, atan_increasing. lra.
Qed.

Lemma atan_gt_0 : forall t : R, 0 < t -> 0 < atan t.
Proof.
  intros t Ht. rewrite <- atan_0. apply atan_increasing. lra.
Qed.

Lemma atan2_ratan_range : forall x y : R, ~ (x = 0 /\ y = 0) ->
  - PI < atan2_ratan y x <= PI.
Proof.
  intros x y H. pose proof PI_RGT_0 as HPI. unfold atan2_ratan.
  destruct (Rlt_dec 0 x) as [Hx|Hx].
  - pose proof (atan_bound (y / x)); lra.
  - destruct (Rlt_dec x 0) as [Hx2|Hx2].
    + destruct (Rle_dec 0 y) as [Hy|Hy].
      * pose proof (atan_bound (y / x)).
        assert (atan (y / x) <= 0) by (apply atan_le_0, div_nonpos_of_neg_denom; lra).
        lra.
      * pose proof (atan_bound (y / x)).
        assert (0 < atan (y / x)) by (apply atan_gt_0, div_pos_of_neg_neg; lra).
        lra.
    + assert (x = 0) by lra. subst x.
      destruct (Rlt_dec 0 y) as [Hy|Hy].
      * lra.
      * destruct (Rlt_dec y 0) as [Hy2|Hy2].
        -- lra.
        -- exfalso. apply H. split; [ reflexivity | lra ].
Qed.

Lemma atan2_ratan_origin : atan2_ratan 0 0 = 0.
Proof.
  unfold atan2_ratan.
  destruct (Rlt_dec 0 0) as [H|H]; [lra|].
  destruct (Rlt_dec 0 0) as [H0|H0]; [lra|].
  destruct (Rlt_dec 0 0) as [Hy|Hy]; [lra|].
  destruct (Rlt_dec 0 0) as [Hy2|Hy2]; [lra|].
  reflexivity.
Qed.

Theorem atan2_eq_ratan : forall y x : R, atan2 y x = atan2_ratan y x.
Proof.
  intros y x.
  destruct (Req_dec x 0) as [Hx|Hx]; destruct (Req_dec y 0) as [Hy|Hy].
  - subst. rewrite atan2_origin, atan2_ratan_origin. reflexivity.
  - assert (Hne : ~ (x = 0 /\ y = 0)) by (subst x; lra).
    apply eq_sym. apply (atan2_unique x y (atan2_ratan y x)).
    + exact Hne.
    + apply atan2_ratan_range. exact Hne.
    + apply cos_atan2_ratan. exact Hne.
    + apply sin_atan2_ratan. exact Hne.
  - assert (Hne : ~ (x = 0 /\ y = 0)) by (subst y; lra).
    apply eq_sym. apply (atan2_unique x y (atan2_ratan y x)).
    + exact Hne.
    + apply atan2_ratan_range. exact Hne.
    + apply cos_atan2_ratan. exact Hne.
    + apply sin_atan2_ratan. exact Hne.
  - assert (Hne : ~ (x = 0 /\ y = 0)) by lra.
    apply eq_sym. apply (atan2_unique x y (atan2_ratan y x)).
    + exact Hne.
    + apply atan2_ratan_range. exact Hne.
    + apply cos_atan2_ratan. exact Hne.
    + apply sin_atan2_ratan. exact Hne.
Qed.

Lemma atan2_pos_x_eq_atan : forall y x : R, 0 < x ->
  atan2 y x = atan (y / x).
Proof.
  intros y x Hx. rewrite atan2_eq_ratan. unfold atan2_ratan.
  destruct (Rlt_dec 0 x) as [_|H]; [reflexivity | lra].
Qed.

Print Assumptions atan2_eq_ratan.
