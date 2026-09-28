(* ============================================================================
   NetTopologySuite.Proofs.Atan2Ivt
   ----------------------------------------------------------------------------
   S1a (#770 build order, step 1). Minimal two-argument arctangent on the
   3-axiom atan3 of AtanIvt, by the half-angle form

     atan2 y x := 2 · atan3 (y / (r + x)),   r = sqrt (x² + y²).

   Only to turn the chart pole direction into θ₀. Not a remint of
   Atan2.atan2 (Stdlib atan, Category C); do not import both.

     atan2_polar   r + x ≠ 0  ⇒  x = r·cos(atan2 y x) ∧ y = r·sin(atan2 y x)
     atan2_unique  0 < r, -π < θ < π  ⇒  atan2 (r·sin θ) (r·cos θ) = θ

   No branch. r + x = 0 is the closed negative x-axis (and the origin):
   that is the half-angle cut, and no lemma here says anything there.
   Range on the rest of the plane is (-π, π).

   No Admitted. No Axiom. No Parameter.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import AtanIvt.
Local Open Scope R_scope.

Definition atan2 (y x : R) : R :=
  2 * atan3 (y / (sqrt (x * x + y * y) + x)).

Lemma atan2_polar : forall x y,
  sqrt (x * x + y * y) + x <> 0 ->
  x = sqrt (x * x + y * y) * cos (atan2 y x) /\
  y = sqrt (x * x + y * y) * sin (atan2 y x).
Proof.
  intros x y Hs.
  unfold atan2. rewrite cos_2_atan3, sin_2_atan3.
  set (r := sqrt (x * x + y * y)) in *.
  set (s := r + x) in *.
  assert (Hr0 : 0 <= r) by (unfold r; apply sqrt_pos).
  assert (Hr2 : r * r = x * x + y * y).
  { unfold r. apply sqrt_sqrt. nra. }
  assert (Hrne : r <> 0).
  { intro E. rewrite E in Hr2.
    assert (x = 0) by nra. apply Hs. unfold s. lra. }
  assert (Hden : s * s + y * y = 2 * r * s) by (unfold s; nra).
  assert (Hnum : s * s - y * y = 2 * x * s) by (unfold s; nra).
  split.
  - replace ((1 - y / s * (y / s)) / (1 + y / s * (y / s)))
      with ((s * s - y * y) / (s * s + y * y)) by (field; split; nra).
    rewrite Hden, Hnum. field. split; assumption.
  - replace (2 * (y / s) / (1 + y / s * (y / s)))
      with (2 * y * s / (s * s + y * y)) by (field; split; nra).
    rewrite Hden. field. split; assumption.
Qed.

Lemma atan2_unique : forall r t,
  0 < r ->
  -PI < t < PI ->
  atan2 (r * sin t) (r * cos t) = t.
Proof.
  intros r t Hr Ht.
  set (h := t / 2).
  assert (Hth : t = 2 * h) by (unfold h; field).
  assert (Hh : -(PI/2) < h < PI/2) by (unfold h; lra).
  assert (Hc : 0 < cos h) by (apply cos_gt_0; lra).
  assert (Hsq : sqrt (r * cos t * (r * cos t) + r * sin t * (r * sin t)) = r).
  { replace (r * cos t * (r * cos t) + r * sin t * (r * sin t))
      with (r * r * (sin t * sin t + cos t * cos t)) by ring.
    rewrite (Rplus_comm (sin t * sin t)).
    pose proof (sin2_cos2 t) as E. unfold Rsqr in E.
    rewrite (Rplus_comm (cos t * cos t)), E, Rmult_1_r.
    apply sqrt_square. lra. }
  unfold atan2. rewrite Hsq.
  replace (r * sin t / (r + r * cos t)) with (tan h).
  - rewrite atan3_tan by exact Hh. unfold h. field.
  - rewrite Hth, sin_2a, cos_2a_cos. unfold tan.
    replace (r + r * (2 * cos h * cos h - 1)) with (2 * r * (cos h * cos h))
      by ring.
    field. split; lra.
Qed.

Print Assumptions atan2_polar.
Print Assumptions atan2_unique.
