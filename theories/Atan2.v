(* ============================================================================
   NetTopologySuite.Proofs.Atan2
   ----------------------------------------------------------------------------
   JTS Math.atan2 / NTS Angle.  claimId: none.

   Option-A arc primitives, foundation 1/N: two-argument arctangent
   `atan2 : R -> R -> R` with the JTS/`Math.atan2(y, x)` quadrant convention
   and range (-PI, PI].  Origin gives 0.

   Built from AtanIvt.atan3 (IVT root of sin t - u * cos t on (-PI/2, PI/2))
   and Stdlib IVT only — no Ratan.atan:

     r = sqrt (x*x + y*y)
     atan2 y x = 2 * atan3 (y / (r + x))    when r + x > 0
               = PI                           when y = 0 and x < 0
               = 0                            at the origin.

   Load-bearing characterisations, for (x,y) <> (0,0):

     cos (atan2 y x) = x / r,   sin (atan2 y x) = y / r,

   plus atan2_unique on (-PI, PI].  The old Ratan quadrant body is
   Atan2RatanBridge.atan2_ratan.  Refs #64, #771.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import AtanIvt.
Local Open Scope R_scope.

(* JTS Math.atan2(y, x): angle of the vector (x, y), range (-PI, PI].
   First argument is y (the ordinate), second is x (the abscissa). *)
Definition atan2 (y x : R) : R :=
  let r := sqrt (x * x + y * y) in
  if Rlt_dec 0 (r + x) then 2 * atan3 (y / (r + x))
  else if Rlt_dec x 0 then PI
  else 0.

(* The radius is strictly positive away from the origin. *)
Lemma atan2_r_pos : forall x y : R,
  ~ (x = 0 /\ y = 0) -> 0 < sqrt (x * x + y * y).
Proof.
  intros x y H. apply sqrt_lt_R0.
  destruct (Req_dec x 0) as [Hx0|Hx0].
  - subst x. assert (Hy : y <> 0) by (intro Hy0; apply H; split; [ reflexivity | exact Hy0 ]).
    destruct (Rdichotomy y 0 Hy); nra.
  - destruct (Rdichotomy x 0 Hx0); nra.
Qed.

Lemma atan2_r_sq : forall x y : R,
  sqrt (x * x + y * y) * sqrt (x * x + y * y) = x * x + y * y.
Proof.
  intros x y. apply sqrt_sqrt. nra.
Qed.

Lemma atan2_r_abs_x : forall x y : R,
  Rabs x <= sqrt (x * x + y * y).
Proof.
  intros x y.
  rewrite <- (sqrt_Rsqr_abs x).
  apply sqrt_le_1.
  - apply Rle_0_sqr.
  - nra.
  - unfold Rsqr. nra.
Qed.

Lemma atan2_r_plus_x_nonneg : forall x y : R,
  0 <= sqrt (x * x + y * y) + x.
Proof.
  intros x y.
  pose proof (atan2_r_abs_x x y) as Ha.
  destruct (Rle_or_lt 0 x) as [Hx|Hx].
  - apply Rplus_le_le_0_compat; [apply sqrt_pos | exact Hx].
  - assert (Rabs x = - x) by (apply Rabs_left; exact Hx).
    nra.
Qed.

Lemma atan2_r_plus_x_zero : forall x y : R,
  sqrt (x * x + y * y) + x = 0 -> y = 0 /\ x <= 0.
Proof.
  intros x y H.
  pose proof (atan2_r_plus_x_nonneg x y) as Hnn.
  assert (Hr : sqrt (x * x + y * y) = - x) by lra.
  assert (Hx : x <= 0) by (pose proof (sqrt_pos (x * x + y * y)); lra).
  assert (Hsq : (- x) * (- x) = x * x + y * y).
  { rewrite <- Hr. apply atan2_r_sq. }
  assert (y * y = 0) by nra.
  split; [|exact Hx].
  destruct (Req_dec y 0) as [Hy|Hy]; [exact Hy|].
  destruct (Rdichotomy y 0 Hy); nra.
Qed.

(* Half-angle algebra: (1-t^2)/(1+t^2) = x/r and 2t/(1+t^2) = y/r
   for t = y/(r+x). *)
Lemma atan2_half_ratios : forall x y r : R,
  0 < r ->
  0 < r + x ->
  r * r = x * x + y * y ->
  (1 - (y / (r + x)) * (y / (r + x)))
    / (1 + (y / (r + x)) * (y / (r + x))) = x / r /\
  (2 * (y / (r + x)))
    / (1 + (y / (r + x)) * (y / (r + x))) = y / r.
Proof.
  intros x y r Hr Hrx Hr2.
  assert (Hrx0 : r + x <> 0) by lra.
  assert (Hr0 : r <> 0) by lra.
  set (d := r + x).
  assert (Hnum : d * d - y * y = 2 * x * d).
  { unfold d.
    replace ((r + x) * (r + x)) with (r * r + 2 * r * x + x * x) by ring.
    rewrite Hr2. ring. }
  assert (Hden : d * d + y * y = 2 * r * d).
  { unfold d.
    replace ((r + x) * (r + x) + y * y)
      with (r * r + 2 * r * x + x * x + y * y) by ring.
    replace (2 * r * (r + x)) with (2 * (r * r) + 2 * r * x) by ring.
    rewrite Hr2. ring. }
  assert (Hd0 : d <> 0) by (unfold d; exact Hrx0).
  assert (Hdd : d * d + y * y <> 0).
  { rewrite Hden. unfold d. nra. }
  split.
  - replace ((1 - (y / d) * (y / d)) / (1 + (y / d) * (y / d)))
      with ((d * d - y * y) / (d * d + y * y)) by (field; split; assumption).
    rewrite Hnum, Hden. field. split; [exact Hr0 | exact Hd0].
  - replace ((2 * (y / d)) / (1 + (y / d) * (y / d)))
      with ((2 * y * d) / (d * d + y * y)) by (field; split; assumption).
    rewrite Hden. field. split; [exact Hr0 | exact Hd0].
Qed.

(* ---- Headline 1: cosine characterisation. ------------------------------- *)
Theorem cos_atan2 : forall x y : R, ~ (x = 0 /\ y = 0) ->
  cos (atan2 y x) = x / sqrt (x * x + y * y).
Proof.
  intros x y Hxy.
  set (r := sqrt (x * x + y * y)).
  assert (Hr : 0 < r) by (apply atan2_r_pos; exact Hxy).
  assert (Hr2 : r * r = x * x + y * y) by (unfold r; apply atan2_r_sq).
  unfold atan2. fold r.
  destruct (Rlt_dec 0 (r + x)) as [Hsum|Hsum].
  - rewrite cos_2_atan3.
    apply (proj1 (atan2_half_ratios x y r Hr Hsum Hr2)).
  - assert (Hnn : 0 <= r + x) by (unfold r; apply atan2_r_plus_x_nonneg).
    assert (Hz : r + x = 0) by lra.
    destruct (atan2_r_plus_x_zero x y Hz) as [Hy Hx].
    assert (Hxlt : x < 0).
    { destruct Hx as [Hlt|Heq]; [exact Hlt|].
      subst x. exfalso. apply Hxy. split; [reflexivity | exact Hy]. }
    destruct (Rlt_dec x 0) as [_|Hnot]; [|lra].
    subst y. rewrite cos_PI.
    assert (Hrabs : r = - x).
    { unfold r. replace (x * x + 0 * 0) with (x * x) by ring.
      replace (x * x) with (Rsqr x) by (unfold Rsqr; ring).
      rewrite sqrt_Rsqr_abs. rewrite Rabs_left; lra. }
    rewrite Hrabs. field. lra.
Qed.

(* ---- Headline 2: sine characterisation. --------------------------------- *)
Theorem sin_atan2 : forall x y : R, ~ (x = 0 /\ y = 0) ->
  sin (atan2 y x) = y / sqrt (x * x + y * y).
Proof.
  intros x y Hxy.
  set (r := sqrt (x * x + y * y)).
  assert (Hr : 0 < r) by (apply atan2_r_pos; exact Hxy).
  assert (Hr2 : r * r = x * x + y * y) by (unfold r; apply atan2_r_sq).
  unfold atan2. fold r.
  destruct (Rlt_dec 0 (r + x)) as [Hsum|Hsum].
  - rewrite sin_2_atan3.
    apply (proj2 (atan2_half_ratios x y r Hr Hsum Hr2)).
  - assert (Hnn : 0 <= r + x) by (unfold r; apply atan2_r_plus_x_nonneg).
    assert (Hz : r + x = 0) by lra.
    destruct (atan2_r_plus_x_zero x y Hz) as [Hy Hx].
    assert (Hxlt : x < 0).
    { destruct Hx as [Hlt|Heq]; [exact Hlt|].
      subst x. exfalso. apply Hxy. split; [reflexivity | exact Hy]. }
    destruct (Rlt_dec x 0) as [_|Hnot]; [|lra].
    subst y. rewrite sin_PI. field. lra.
Qed.

(* ---- Pythagorean corollary: atan2 lands on the unit circle scaled by r. -- *)
Corollary atan2_on_circle : forall x y : R, ~ (x = 0 /\ y = 0) ->
  let r := sqrt (x * x + y * y) in
  (r * cos (atan2 y x) = x) /\ (r * sin (atan2 y x) = y).
Proof.
  intros x y Hxy. assert (Hr := atan2_r_pos x y Hxy). simpl.
  rewrite cos_atan2, sin_atan2 by exact Hxy. split; field; lra.
Qed.

Lemma atan2_origin : atan2 0 0 = 0.
Proof.
  unfold atan2.
  replace (sqrt (0 * 0 + 0 * 0)) with 0.
  2: { replace (0 * 0 + 0 * 0) with 0 by ring. symmetry. apply sqrt_0. }
  destruct (Rlt_dec 0 (0 + 0)) as [H|H]; [lra|].
  destruct (Rlt_dec 0 0) as [H0|H0]; [lra|].
  reflexivity.
Qed.

Lemma atan2_pos_x_axis : forall x : R, 0 < x -> atan2 0 x = 0.
Proof.
  intros x Hx. unfold atan2.
  assert (Hr : sqrt (x * x + 0 * 0) = x).
  { replace (x * x + 0 * 0) with (Rsqr x) by (unfold Rsqr; ring).
    rewrite sqrt_Rsqr_abs. rewrite Rabs_right; lra. }
  rewrite Hr.
  destruct (Rlt_dec 0 (x + x)) as [H|H]; [|lra].
  replace (0 / (x + x)) with 0 by (field; lra).
  rewrite atan3_0. ring.
Qed.

Lemma atan2_neg_x_axis : forall x : R, x < 0 -> atan2 0 x = PI.
Proof.
  intros x Hx. unfold atan2.
  assert (Hr : sqrt (x * x + 0 * 0) = - x).
  { replace (x * x + 0 * 0) with (Rsqr x) by (unfold Rsqr; ring).
    rewrite sqrt_Rsqr_abs. rewrite Rabs_left; lra. }
  rewrite Hr.
  destruct (Rlt_dec 0 (- x + x)) as [H|H]; [lra|].
  destruct (Rlt_dec x 0) as [Hx'|Hx']; [reflexivity|lra].
Qed.

Lemma atan3_m1 : atan3 (-1) = - (PI / 4).
Proof.
  symmetry. apply atan3_unique.
  - pose proof PI_RGT_0. lra.
  - rewrite sin_neg, cos_neg, sin_PI4, cos_PI4. ring.
Qed.

Lemma atan2_pos_y_axis : forall y : R, 0 < y -> atan2 y 0 = PI / 2.
Proof.
  intros y Hy. unfold atan2.
  assert (Hr : sqrt (0 * 0 + y * y) = y).
  { replace (0 * 0 + y * y) with (Rsqr y) by (unfold Rsqr; ring).
    rewrite sqrt_Rsqr_abs. rewrite Rabs_right; lra. }
  rewrite Hr.
  destruct (Rlt_dec 0 (y + 0)) as [H|H]; [|lra].
  replace (y / (y + 0)) with 1 by (field; lra).
  rewrite atan3_1. lra.
Qed.

Lemma atan2_neg_y_axis : forall y : R, y < 0 -> atan2 y 0 = - (PI / 2).
Proof.
  intros y Hy. unfold atan2.
  assert (Hr : sqrt (0 * 0 + y * y) = - y).
  { replace (0 * 0 + y * y) with (Rsqr y) by (unfold Rsqr; ring).
    rewrite sqrt_Rsqr_abs. rewrite Rabs_left; lra. }
  rewrite Hr.
  destruct (Rlt_dec 0 (- y + 0)) as [H|H]; [|lra].
  replace (y / (- y + 0)) with (-1) by (field; lra).
  rewrite atan3_m1. lra.
Qed.

(* ---- atan2 lands in the principal range (-PI, PI]. --------------------- *)
Theorem atan2_range : forall x y : R, ~ (x = 0 /\ y = 0) ->
  - PI < atan2 y x <= PI.
Proof.
  intros x y Hxy. pose proof PI_RGT_0 as HPI.
  set (r := sqrt (x * x + y * y)).
  unfold atan2. fold r.
  destruct (Rlt_dec 0 (r + x)) as [Hsum|Hsum].
  - destruct (atan3_spec (y / (r + x))) as [Hb _].
    destruct Hb as [Hlo Hhi]. lra.
  - assert (Hnn : 0 <= r + x) by (unfold r; apply atan2_r_plus_x_nonneg).
    assert (Hz : r + x = 0) by lra.
    destruct (atan2_r_plus_x_zero x y Hz) as [Hy Hx].
    assert (Hxlt : x < 0).
    { destruct Hx as [Hlt|Heq]; [exact Hlt|].
      subst x. exfalso. apply Hxy. split; [reflexivity | exact Hy]. }
    destruct (Rlt_dec x 0) as [_|Hnot]; [|lra].
    lra.
Qed.

Lemma cos_eq_1_two_pi : forall t : R,
  - (2 * PI) < t < 2 * PI -> cos t = 1 -> t = 0.
Proof.
  intros t Ht Hc.
  replace t with (2 * (t / 2)) in Hc by field.
  rewrite cos_2a_sin in Hc.
  assert (Hs0 : sin (t / 2) = 0).
  { assert (Hsq : sin (t / 2) * sin (t / 2) = 0) by lra.
    apply Rmult_integral in Hsq. destruct Hsq as [H|H]; exact H. }
  assert (Hr : - PI < t / 2 < PI) by lra.
  destruct (Rtotal_order (t / 2) 0) as [Hn|[Hz|Hp]].
  - pose proof (sin_gt_0 (- (t / 2)) ltac:(lra) ltac:(lra)) as Hpos.
    rewrite sin_neg in Hpos. lra.
  - lra.
  - pose proof (sin_gt_0 (t / 2) Hp ltac:(lra)) as Hpos. lra.
Qed.

Theorem atan2_unique : forall x y a : R,
  ~ (x = 0 /\ y = 0) ->
  - PI < a <= PI ->
  cos a = x / sqrt (x * x + y * y) ->
  sin a = y / sqrt (x * x + y * y) ->
  a = atan2 y x.
Proof.
  intros x y a Hne Ha Hc Hs.
  set (b := atan2 y x).
  pose proof (atan2_range x y Hne) as Hb.
  pose proof (cos_atan2 x y Hne) as Hc2.
  pose proof (sin_atan2 x y Hne) as Hs2.
  assert (Hr : 0 < sqrt (x * x + y * y)) by (apply atan2_r_pos; exact Hne).
  assert (Hr2 : sqrt (x * x + y * y) * sqrt (x * x + y * y) = x * x + y * y)
    by apply atan2_r_sq.
  assert (Hcd : cos (a - b) = 1).
  { set (r := sqrt (x * x + y * y)) in *.
    assert (Hr0 : r <> 0) by lra.
    rewrite cos_minus. fold b in Hc2, Hs2. rewrite Hc, Hs, Hc2, Hs2.
    replace (x / r * (x / r) + y / r * (y / r))
      with ((x * x + y * y) / (r * r)) by (field; exact Hr0).
    rewrite Hr2.
    assert (Hsum : x * x + y * y <> 0) by nra.
    field. exact Hsum. }
  assert (Hopen : - (2 * PI) < a - b < 2 * PI).
  { pose proof PI_RGT_0. unfold b. lra. }
  assert (Heq : a - b = 0) by (apply cos_eq_1_two_pi; assumption).
  apply (Rplus_eq_reg_r (- b)).
  replace (a + - b) with (a - b) by ring.
  rewrite Heq. ring.
Qed.

Lemma sin_pos_principal : forall a : R,
  - PI < a <= PI -> 0 < sin a -> 0 < a.
Proof.
  intros a Ha Hs.
  destruct (Rle_lt_dec a 0) as [Hle|Hgt].
  - exfalso.
    destruct Hle as [Hlt|Heq].
    + pose proof (sin_lt_0_var a ltac:(lra) Hlt). lra.
    + subst a. rewrite sin_0 in Hs. lra.
  - exact Hgt.
Qed.

Lemma atan2_pos_iff : forall y x : R,
  ~ (x = 0 /\ y = 0) ->
  (0 < atan2 y x) <-> (0 < y \/ (y = 0 /\ x < 0)).
Proof.
  intros y x Hne. split.
  - intros Hp.
    pose proof (sin_atan2 x y Hne) as Hs.
    pose proof (cos_atan2 x y Hne) as Hc.
    pose proof (atan2_r_pos x y Hne) as Hr.
    pose proof (atan2_range x y Hne) as Hb.
    pose proof PI_RGT_0 as HPI.
    destruct (Rtotal_order y 0) as [Hy|[Hy|Hy]].
    + exfalso.
      assert (Hsn : sin (atan2 y x) < 0).
      { rewrite Hs. unfold Rdiv.
        assert (0 < / sqrt (x * x + y * y)) by (apply Rinv_0_lt_compat; exact Hr).
        nra. }
      destruct Hb as [_ Hhi].
      destruct Hhi as [Hlt|Heq].
      * pose proof (sin_gt_0 (atan2 y x) Hp Hlt) as Hpos.
        apply (Rlt_irrefl 0).
        apply Rlt_trans with (r2 := sin (atan2 y x)); [exact Hpos | exact Hsn].
      * rewrite Heq, sin_PI in Hsn.
        apply (Rlt_irrefl 0). exact Hsn.
    + subst y. right. split; [reflexivity|].
      assert (Hsz : sin (atan2 0 x) = 0).
      { rewrite Hs. field. apply Rgt_not_eq. exact Hr. }
      destruct Hb as [_ Hhi].
      assert (Ha : atan2 0 x = PI).
      { destruct Hhi as [Hlt|Heq]; [|exact Heq].
        pose proof (sin_gt_0 (atan2 0 x) Hp Hlt) as Hpos.
        rewrite Hsz in Hpos.
        exfalso. exact (Rlt_irrefl 0 Hpos). }
      assert (Hc1 : x / sqrt (x * x + 0 * 0) = -1).
      { rewrite <- Hc, Ha, cos_PI. reflexivity. }
      assert (Hxneg : x = - sqrt (x * x + 0 * 0)).
      { apply (Rmult_eq_reg_r (/ sqrt (x * x + 0 * 0))).
        - unfold Rdiv in Hc1. rewrite Hc1.
          field. apply Rgt_not_eq. exact Hr.
        - apply Rinv_neq_0_compat. apply Rgt_not_eq. exact Hr. }
      rewrite Hxneg.
      apply Ropp_lt_gt_0_contravar. exact Hr.
    + left. exact Hy.
  - intros [Hy|[Hy Hx]].
    + pose proof (sin_atan2 x y Hne) as Hs.
      pose proof (atan2_r_pos x y Hne) as Hr.
      pose proof (atan2_range x y Hne) as Hb.
      assert (Hsp : 0 < sin (atan2 y x)).
      { rewrite Hs. unfold Rdiv.
        assert (0 < / sqrt (x * x + y * y)) by (apply Rinv_0_lt_compat; exact Hr).
        nra. }
      apply sin_pos_principal; assumption.
    + subst y. rewrite (atan2_neg_x_axis x Hx). pose proof PI_RGT_0. lra.
Qed.

Lemma cos_pos_below_half_pi : forall a : R,
  0 < a <= PI -> 0 < cos a -> a < PI / 2.
Proof.
  intros a Ha Hc.
  destruct (Rlt_dec a (PI / 2)) as [H|H]; [exact H|].
  exfalso.
  assert (Hle : PI / 2 <= a) by lra.
  pose proof (cos_decr_1 (PI / 2) a ltac:(pose proof PI_RGT_0; lra) ltac:(pose proof PI_RGT_0; lra)
                          ltac:(pose proof PI_RGT_0; lra) ltac:(lra) Hle) as Hd.
  rewrite cos_PI2 in Hd. lra.
Qed.

Lemma atan2_open_first_quadrant : forall x y : R,
  0 < x -> 0 < y -> 0 < atan2 y x < PI / 2.
Proof.
  intros x y Hx Hy.
  assert (Hne : ~ (x = 0 /\ y = 0)) by lra.
  pose proof (cos_atan2 x y Hne) as Hc.
  pose proof (sin_atan2 x y Hne) as Hs.
  pose proof (atan2_r_pos x y Hne) as Hr.
  pose proof (atan2_range x y Hne) as Hb.
  pose proof PI_RGT_0 as HPI.
  assert (Hcp : 0 < cos (atan2 y x)).
  { rewrite Hc. unfold Rdiv.
    assert (0 < / sqrt (x * x + y * y)) by (apply Rinv_0_lt_compat; exact Hr). nra. }
  assert (Hsp : 0 < sin (atan2 y x)).
  { rewrite Hs. unfold Rdiv.
    assert (0 < / sqrt (x * x + y * y)) by (apply Rinv_0_lt_compat; exact Hr). nra. }
  assert (Hpos : 0 < atan2 y x) by (apply sin_pos_principal; assumption).
  assert (Hlt : atan2 y x < PI).
  { destruct (Req_dec (atan2 y x) PI) as [E|E]; [|lra].
    rewrite E, sin_PI in Hsp. lra. }
  split; [exact Hpos|].
  apply cos_pos_below_half_pi; [lra|exact Hcp].
Qed.

Lemma atan2_diag_PI4 : forall x : R, 0 < x -> atan2 x x = PI / 4.
Proof.
  intros x Hx.
  assert (Hne : ~ (x = 0 /\ x = 0)) by lra.
  assert (Hr : sqrt (x * x + x * x) = x * sqrt 2).
  { replace (x * x + x * x) with (Rsqr x * 2) by (unfold Rsqr; ring).
    rewrite (sqrt_mult_alt (Rsqr x) 2 (Rle_0_sqr x)).
    rewrite sqrt_Rsqr_abs. rewrite Rabs_right by lra. ring. }
  assert (Hs20 : sqrt 2 <> 0).
  { apply Rgt_not_eq. apply sqrt_lt_R0. lra. }
  assert (Hx0 : x <> 0) by lra.
  apply eq_sym. apply (atan2_unique x x (PI / 4)).
  - exact Hne.
  - pose proof PI_RGT_0. lra.
  - rewrite cos_PI4, Hr. field. split; [exact Hs20 | exact Hx0].
  - rewrite sin_PI4, Hr. field. split; [exact Hs20 | exact Hx0].
Qed.

Lemma atan2_neg_diag : forall x : R, 0 < x -> atan2 (- x) x = - (PI / 4).
Proof.
  intros x Hx.
  assert (Hne : ~ (x = 0 /\ - x = 0)) by lra.
  assert (Hr : sqrt (x * x + (- x) * (- x)) = x * sqrt 2).
  { replace (x * x + (- x) * (- x)) with (Rsqr x * 2) by (unfold Rsqr; ring).
    rewrite (sqrt_mult_alt (Rsqr x) 2 (Rle_0_sqr x)).
    rewrite sqrt_Rsqr_abs. rewrite Rabs_right by lra. ring. }
  assert (Hs20 : sqrt 2 <> 0).
  { apply Rgt_not_eq. apply sqrt_lt_R0. lra. }
  assert (Hx0 : x <> 0) by lra.
  apply eq_sym. apply (atan2_unique x (- x) (- (PI / 4))).
  - exact Hne.
  - pose proof PI_RGT_0. lra.
  - rewrite cos_neg, cos_PI4, Hr. field. split; [exact Hs20 | exact Hx0].
  - rewrite sin_neg, sin_PI4, Hr. field. split; [exact Hs20 | exact Hx0].
Qed.

Lemma atan2_pos_scale : forall k y x : R, 0 < k ->
  atan2 (k * y) (k * x) = atan2 y x.
Proof.
  intros k y x Hk.
  unfold atan2.
  replace (sqrt (k * x * (k * x) + k * y * (k * y)))
    with (k * sqrt (x * x + y * y)).
  2: {
    replace (k * x * (k * x) + k * y * (k * y))
      with (k * k * (x * x + y * y)) by ring.
    rewrite (sqrt_mult_alt (k * k) (x * x + y * y)).
    2: { nra. }
    rewrite (sqrt_square k) by lra. ring.
  }
  set (r := sqrt (x * x + y * y)).
  replace (k * r + k * x) with (k * (r + x)) by ring.
  destruct (Rlt_dec 0 (k * (r + x))) as [Hp|Hp].
  - assert (Hq : 0 < r + x) by (apply (Rmult_lt_reg_l k); lra).
    destruct (Rlt_dec 0 (r + x)) as [_|Hno]; [|lra].
    replace (k * y / (k * (r + x))) with (y / (r + x)) by (field; lra).
    reflexivity.
  - assert (Hle : r + x <= 0).
    { apply Rnot_lt_le in Hp.
      apply (Rmult_le_reg_l k (r + x) 0); [exact Hk|].
      replace (k * 0) with 0 by ring. exact Hp. }
    destruct (Rlt_dec 0 (r + x)) as [Hq|Hq]; [lra|].
    destruct (Rlt_dec (k * x) 0) as [Hkx|Hkx];
      destruct (Rlt_dec x 0) as [Hx|Hx];
      try reflexivity; exfalso; nra.
Qed.

Print Assumptions atan2.
Print Assumptions atan3.
Print Assumptions cos_atan2.
Print Assumptions sin_atan2.
Print Assumptions atan2_unique.
