(* ============================================================================
   NetTopologySuite.Proofs.MetricCircleSmoke
   ----------------------------------------------------------------------------
   Circle instance of lip_speed_is_curve_length. The speed of
   t ↦ O + r·(cos t, sin t) is the constant r (r ≥ 0). The LipInt
   primitive's increment is a metric length, and curve_length_unique
   identifies it with arc_r_theta_is_curve_length. That minted theorem
   stays the witness of r·(b−a). This file is claimId none.

   Deferrals, named: clothoid and NURBS instances are later files.
   Leibniz is not used.

   WITNESS topic: metric · claimId: none
   No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis1.
From NTS.Proofs Require Import Distance LipInt CurveLength ArcRectifiable MetricSpeed.
Local Open Scope R_scope.

Section Circle.
Variable O : Point.
Variable r a b : R.
Hypothesis Hr : 0 <= r.
Hypothesis Hab : a <= b.

Definition cgx (t : R) : R := px O + r * cos t.
Definition cgy (t : R) : R := py O + r * sin t.
Definition cvx (t : R) : R := - r * sin t.
Definition cvy (t : R) : R := r * cos t.

Lemma circle_vx_lip : forall x y, a <= x <= b -> a <= y <= b ->
  Rabs (cvx x - cvx y) <= r * Rabs (x - y).
Proof.
  intros x y _ _. unfold cvx.
  replace ((- r * sin x) - (- r * sin y)) with (- r * (sin x - sin y)) by ring.
  rewrite Rabs_mult, Rabs_Ropp. rewrite (Rabs_pos_eq r Hr).
  apply Rmult_le_compat_l; [exact Hr | apply sin_lip].
Qed.

Lemma circle_vy_lip : forall x y, a <= x <= b -> a <= y <= b ->
  Rabs (cvy x - cvy y) <= r * Rabs (x - y).
Proof.
  intros x y _ _. unfold cvy.
  replace (r * cos x - r * cos y) with (r * (cos x - cos y)) by ring.
  rewrite Rabs_mult. rewrite (Rabs_pos_eq r Hr).
  apply Rmult_le_compat_l; [exact Hr | apply cos_lip].
Qed.

Lemma circle_gx_deriv : forall t, a <= t <= b -> derivable_pt_lim cgx t (cvx t).
Proof.
  intros t _. unfold cgx, cvx.
  replace (- r * sin t) with (0 + r * (- sin t)) by ring.
  apply derivable_pt_lim_ext with
    (f := plus_fct (fct_cte (px O)) (mult_real_fct r cos)).
  - intros z. unfold plus_fct, fct_cte, mult_real_fct. ring.
  - apply derivable_pt_lim_plus.
    + apply derivable_pt_lim_const.
    + apply derivable_pt_lim_scal. apply derivable_pt_lim_cos.
Qed.

Lemma circle_gy_deriv : forall t, a <= t <= b -> derivable_pt_lim cgy t (cvy t).
Proof.
  intros t _. unfold cgy, cvy.
  replace (r * cos t) with (0 + r * cos t) by ring.
  apply derivable_pt_lim_ext with
    (f := plus_fct (fct_cte (py O)) (mult_real_fct r sin)).
  - intros z. unfold plus_fct, fct_cte, mult_real_fct. ring.
  - apply derivable_pt_lim_plus.
    + apply derivable_pt_lim_const.
    + apply derivable_pt_lim_scal. apply derivable_pt_lim_sin.
Qed.

Lemma circle_gamma : forall t, gamma cgx cgy t = circle_pt O r t.
Proof. intros t. unfold gamma, cgx, cgy, circle_pt. reflexivity. Qed.

Theorem circle_speed_primitive_agrees :
  speedF cvx cvy a b r r Hr Hr circle_vx_lip circle_vy_lip b
  - speedF cvx cvy a b r r Hr Hr circle_vx_lip circle_vy_lip a
  = r * (b - a).
Proof.
  destruct (lip_speed_is_curve_length cgx cgy cvx cvy a b r r Hab Hr Hr
              circle_vx_lip circle_vy_lip circle_gx_deriv circle_gy_deriv)
    as [_ Hlen].
  assert (Harc := arc_r_theta_is_curve_length O r a b Hr Hab).
  assert (Hlen' : is_curve_length (circle_param O r) a b
            (speedF cvx cvy a b r r Hr Hr circle_vx_lip circle_vy_lip b
             - speedF cvx cvy a b r r Hr Hr circle_vx_lip circle_vy_lip a)).
  { apply is_curve_length_ext with (g1 := gamma cgx cgy).
    - intros t. rewrite circle_gamma. unfold circle_param. reflexivity.
    - exact Hlen. }
  apply (curve_length_unique (circle_param O r) a b
           (speedF cvx cvy a b r r Hr Hr circle_vx_lip circle_vy_lip b
            - speedF cvx cvy a b r r Hr Hr circle_vx_lip circle_vy_lip a)
           (r * (b - a))); [exact Hlen' | exact Harc].
Qed.

End Circle.

Print Assumptions circle_vx_lip.
Print Assumptions circle_vy_lip.
Print Assumptions circle_gx_deriv.
Print Assumptions circle_gy_deriv.
Print Assumptions circle_gamma.
Print Assumptions circle_speed_primitive_agrees.
