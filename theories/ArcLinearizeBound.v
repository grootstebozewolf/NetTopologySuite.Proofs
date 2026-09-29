(* ============================================================================
   NetTopologySuite.Proofs.ArcLinearizeBound
   ----------------------------------------------------------------------------
   Chord deviation of one uniform step of ArcLinearize.

   For step φ with 0 < φ ≤ 2π and |Δθ| ≤ n·φ, every point of the egg
   between samples k/n and (k+1)/n lies within
     r · (1 − cos(φ/2))
   of the chord segment joining those samples. When φ is at most the
   sagitta step 2·acos(1 − d/r), that quantity is at most d.

   This is the inequality deferred under the name chord_approx_error_bound
   in ArcChordApprox. Hot-pixel transport of the bound is not this file.
   claimId: none. 3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia Field Psatz List.
From NTS.Proofs Require Import Distance SheetHenCircEgg Atan2 ArcLinearize.
Local Open Scope R_scope.

Definition clamp11 (x : R) : R := Rmax (-1) (Rmin 1 x).

Definition dev_to_step (r d : R) : R :=
  let c := clamp11 (1 - d / r) in
  2 * atan2 (sqrt (1 - c * c)) c.

Definition effective_step (ang dev : option R) (r : R) : option R :=
  match ang, dev with
  | None, None => None
  | Some a, None => if Rle_dec a 0 then None else Some a
  | None, Some dv =>
      if Rle_dec dv 0 then None
      else if Rle_dec r 0 then None
      else Some (dev_to_step r dv)
  | Some a, Some dv =>
      if Rle_dec a 0 then None
      else if Rle_dec dv 0 then None
      else if Rle_dec r 0 then None
      else Some (Rmin a (dev_to_step r dv))
  end.

Definition seg_at (a b : Point) (lam : R) : Point :=
  mkPoint ((1 - lam) * px a + lam * px b)
          ((1 - lam) * py a + lam * py b).

Definition on_seg (a b q : Point) : Prop :=
  exists lam, 0 <= lam <= 1 /\ q = seg_at a b lam.

Definition sub_delta (c : CircularEgg) (n : nat) : R :=
  circ_sweep c / (2 * INR n).

Definition sub_mid (c : CircularEgg) (n k : nat) : R :=
  lin_angle c (INR k / INR n) + sub_delta c n.

(* -------------------------------------------------------------------------- *)
(* Step from a deviation, and the rejection of non-positive parameters.      *)
(* -------------------------------------------------------------------------- *)

Lemma clamp11_bounds : forall x, -1 <= clamp11 x <= 1.
Proof.
  intros x. unfold clamp11. split.
  - apply Rmax_l.
  - apply Rmax_lub; [lra | apply Rmin_l].
Qed.

Lemma clamp11_id : forall x, -1 <= x <= 1 -> clamp11 x = x.
Proof.
  intros x Hx. unfold clamp11.
  rewrite Rmin_right by lra. rewrite Rmax_right by lra. reflexivity.
Qed.

Lemma clamp_gap_nonneg : forall c, -1 <= c <= 1 -> 0 <= 1 - c * c.
Proof. intros c Hc. nra. Qed.

Lemma dev_half_cos : forall r d,
  0 < r -> cos (dev_to_step r d / 2) = clamp11 (1 - d / r).
Proof.
  intros r d Hr.
  set (c := clamp11 (1 - d / r)).
  unfold dev_to_step. fold c.
  replace (2 * atan2 (sqrt (1 - c * c)) c / 2)
    with (atan2 (sqrt (1 - c * c)) c) by field.
  set (y := sqrt (1 - c * c)).
  assert (Hc : -1 <= c <= 1) by (apply clamp11_bounds).
  assert (Hy : 0 <= 1 - c * c) by (apply clamp_gap_nonneg; exact Hc).
  assert (Hne : ~ (c = 0 /\ y = 0)).
  { intros [Hc0 Hy0].
    assert (Hy2 : y * y = 0) by nra.
    unfold y in Hy2. rewrite sqrt_sqrt in Hy2 by exact Hy. nra. }
  rewrite (cos_atan2 c y Hne).
  assert (Hrad : sqrt (c * c + y * y) = 1).
  { unfold y. rewrite sqrt_sqrt by exact Hy.
    replace (c * c + (1 - c * c)) with (1 * 1) by ring.
    rewrite sqrt_square by lra. reflexivity. }
  rewrite Hrad. field.
Qed.

Lemma atan2_nonneg_ord : forall y x,
  ~ (x = 0 /\ y = 0) -> 0 <= y -> 0 <= atan2 y x.
Proof.
  intros y x Hne Hy.
  pose proof (sin_atan2 x y Hne) as Hs.
  pose proof (atan2_range x y Hne) as Hb.
  pose proof (atan2_r_pos x y Hne) as Hr.
  assert (Hsn : 0 <= sin (atan2 y x)).
  { rewrite Hs. unfold Rdiv.
    assert (0 < / sqrt (x * x + y * y)) by (apply Rinv_0_lt_compat; exact Hr).
    nra. }
  destruct (Rle_lt_dec 0 (atan2 y x)) as [Hnn|Hneg]; [exact Hnn|].
  exfalso.
  pose proof (sin_lt_0_var (atan2 y x) ltac:(lra) Hneg) as Hlt.
  lra.
Qed.

Lemma dev_to_step_range : forall r d,
  0 < r -> 0 <= dev_to_step r d <= 2 * PI.
Proof.
  intros r d Hr.
  set (c := clamp11 (1 - d / r)).
  set (y := sqrt (1 - c * c)).
  assert (Hc : -1 <= c <= 1) by apply clamp11_bounds.
  assert (Hy : 0 <= y) by (unfold y; apply sqrt_pos).
  assert (Hne : ~ (c = 0 /\ y = 0)).
  { intros [Hc0 Hy0].
    assert (Hy2 : y * y = 0) by nra.
    unfold y in Hy2. rewrite sqrt_sqrt in Hy2
      by (apply clamp_gap_nonneg; exact Hc). nra. }
  unfold dev_to_step. fold c. fold y.
  pose proof (atan2_range c y Hne) as Hb.
  pose proof (atan2_nonneg_ord y c Hne Hy) as Hnn.
  pose proof PI_RGT_0 as HPI.
  split; lra.
Qed.

Lemma dev_to_step_pos : forall r d,
  0 < r -> 0 < d -> 0 < dev_to_step r d.
Proof.
  intros r d Hr Hd.
  set (c := clamp11 (1 - d / r)).
  set (y := sqrt (1 - c * c)).
  assert (Hc1 : c < 1).
  { unfold c, clamp11.
    assert (Hraw : 1 - d / r < 1).
    { assert (0 < d / r).
      { unfold Rdiv. apply Rmult_lt_0_compat; [exact Hd|].
        apply Rinv_0_lt_compat. exact Hr. }
      lra. }
    assert (Hmin : Rmin 1 (1 - d / r) < 1).
    { rewrite Rmin_right by lra. exact Hraw. }
    destruct (Rle_dec (Rmin 1 (1 - d / r)) (-1)) as [Hle|Hgt].
    - rewrite Rmax_left by exact Hle. lra.
    - rewrite Rmax_right by lra. exact Hmin. }
  assert (Hc : -1 <= c <= 1) by apply clamp11_bounds.
  assert (Hy0 : 0 <= 1 - c * c) by (apply clamp_gap_nonneg; exact Hc).
  assert (Hne : ~ (c = 0 /\ y = 0)).
  { intros [Hc0 HyZ].
    assert (Hy2 : y * y = 0) by nra.
    unfold y in Hy2. rewrite sqrt_sqrt in Hy2 by exact Hy0. nra. }
  unfold dev_to_step. fold c. fold y.
  assert (Hpos : 0 < atan2 y c).
  { destruct (Req_dec y 0) as [Hy|Hy].
    - assert (Hc2 : c * c = 1).
      { assert (Hyy : y * y = 0) by (rewrite Hy; ring).
        unfold y in Hyy. rewrite sqrt_sqrt in Hyy by exact Hy0. lra. }
      assert (Hcneg : c = -1).
      { assert (E : (c - 1) * (c + 1) = 0).
        { replace ((c - 1) * (c + 1)) with (c * c - 1) by ring. lra. }
        apply Rmult_integral in E. destruct E as [E|E]; lra. }
      rewrite Hcneg, Hy. rewrite atan2_neg_x_axis by lra.
      pose proof PI_RGT_0. lra.
    - apply atan2_pos_iff; [exact Hne|].
      left. apply Rnot_le_lt. intros Hle.
      assert (y = 0) by (pose proof (sqrt_pos (1 - c * c)); unfold y in *; lra).
      contradiction. }
  pose proof PI_RGT_0. lra.
Qed.

Theorem chord_sagitta_le_dev : forall r d step,
  0 <= r -> 0 <= d ->
  0 <= step <= 2 * PI ->
  (r = 0 \/ 0 < r /\ step <= dev_to_step r d) ->
  r * (1 - cos (step / 2)) <= d.
Proof.
  intros r d step Hr Hd Hstep [Hz| [Hrp Hle]].
  - subst r. rewrite Rmult_0_l. exact Hd.
  - destruct (Rle_dec d (2 * r)) as [Hsmall|Hbig].
    + assert (Harg : -1 <= 1 - d / r <= 1).
      { assert (0 <= d / r).
        { unfold Rdiv. apply Rmult_le_pos; [exact Hd|].
          apply Rlt_le, Rinv_0_lt_compat. exact Hrp. }
        assert (d / r <= 2).
        { apply Rmult_le_reg_r with (r := r); [exact Hrp|].
          unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra. lra. }
        lra. }
      assert (Hc : cos (dev_to_step r d / 2) = 1 - d / r).
      { rewrite dev_half_cos by exact Hrp. rewrite clamp11_id by exact Harg.
        reflexivity. }
      assert (Hrng : 0 <= dev_to_step r d <= 2 * PI)
        by (apply dev_to_step_range; exact Hrp).
      assert (Hcos : cos (dev_to_step r d / 2) <= cos (step / 2)).
      { pose proof PI_RGT_0 as Hp. apply cos_decr_1; nra. }
      assert (Hgap : 1 - cos (step / 2) <= d / r) by lra.
      apply Rmult_le_reg_l with (r := / r).
      * apply Rinv_0_lt_compat. exact Hrp.
      * apply Rle_trans with (d / r).
        -- replace (/ r * (r * (1 - cos (step / 2))))
             with (1 - cos (step / 2)) by (field; lra).
           exact Hgap.
        -- unfold Rdiv. rewrite Rmult_comm. apply Rle_refl.
    + assert (Htwo : r * (1 - cos (step / 2)) <= 2 * r).
      { pose proof (COS_bound (step / 2)) as Hb. nra. }
      lra.
Qed.

Lemma effective_reject_angle : forall a r,
  a <= 0 -> effective_step (Some a) None r = None.
Proof.
  intros a r Ha. unfold effective_step.
  destruct (Rle_dec a 0) as [_|H]; [reflexivity|lra].
Qed.

Lemma effective_reject_dev : forall dv r,
  dv <= 0 -> effective_step None (Some dv) r = None.
Proof.
  intros dv r Hd. unfold effective_step.
  destruct (Rle_dec dv 0) as [_|H]; [reflexivity|lra].
Qed.

Lemma effective_reject_radius : forall dv r,
  0 < dv -> r <= 0 -> effective_step None (Some dv) r = None.
Proof.
  intros dv r Hd Hr. unfold effective_step.
  destruct (Rle_dec dv 0) as [H|H]; [lra|].
  destruct (Rle_dec r 0) as [_|H2]; [reflexivity|lra].
Qed.

Lemma effective_step_pos : forall ang dev r s,
  effective_step ang dev r = Some s -> 0 < s.
Proof.
  intros ang dev r s Hs. destruct ang as [a|], dev as [dv|]; simpl in Hs.
  - destruct (Rle_dec a 0); [discriminate|].
    destruct (Rle_dec dv 0); [discriminate|].
    destruct (Rle_dec r 0); [discriminate|].
    injection Hs as <-.
    assert (0 < dev_to_step r dv) by (apply dev_to_step_pos; lra).
    destruct (Rle_dec a (dev_to_step r dv)).
    + rewrite Rmin_left by assumption. lra.
    + rewrite Rmin_right by lra. assumption.
  - destruct (Rle_dec a 0); [discriminate|]. injection Hs as <-. lra.
  - destruct (Rle_dec dv 0); [discriminate|].
    destruct (Rle_dec r 0); [discriminate|].
    injection Hs as <-. apply dev_to_step_pos; lra.
  - discriminate.
Qed.

Lemma effective_step_le_dev : forall a dv r s,
  0 < r -> 0 < dv ->
  effective_step (Some a) (Some dv) r = Some s ->
  s <= dev_to_step r dv.
Proof.
  intros a dv r s Hr Hd Hs. simpl in Hs.
  destruct (Rle_dec a 0); [discriminate|].
  destruct (Rle_dec dv 0); [discriminate|].
  destruct (Rle_dec r 0); [discriminate|].
  injection Hs as <-. apply Rmin_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* One uniform step stays inside the sagitta of the step angle.              *)
(* -------------------------------------------------------------------------- *)

Lemma half_le_step : forall sweep step n,
  (n <> 0)%nat ->
  0 <= step ->
  Rabs sweep <= INR n * step ->
  Rabs sweep / (2 * INR n) <= step / 2.
Proof.
  intros sweep step n Hn Hs Hle.
  assert (HnR : 0 < INR n) by (apply lt_0_INR; lia).
  apply Rmult_le_reg_r with (r := 2 * INR n); [lra|].
  replace (Rabs sweep / (2 * INR n) * (2 * INR n)) with (Rabs sweep)
    by (field; lra).
  replace (step / 2 * (2 * INR n)) with (INR n * step) by field.
  exact Hle.
Qed.

Lemma half_le_right_angle : forall sweep n,
  (2 <= n)%nat ->
  Rabs sweep <= 2 * PI ->
  0 <= Rabs sweep / (2 * INR n) <= PI / 2.
Proof.
  intros sweep n Hn Hsw.
  assert (HnR : 0 < INR n) by (apply lt_0_INR; lia).
  pose proof PI_RGT_0 as HPI.
  split.
  - unfold Rdiv. apply Rmult_le_pos; [apply Rabs_pos|].
    apply Rlt_le, Rinv_0_lt_compat. lra.
  - assert (H1 : Rabs sweep / (2 * INR n) <= (2 * PI) / (2 * INR n)).
    { apply Rmult_le_compat_r; [|exact Hsw].
      apply Rlt_le, Rinv_0_lt_compat. lra. }
    assert (H2 : (2 * PI) / (2 * INR n) = PI / INR n) by (field; lra).
    assert (H3 : PI / INR n <= PI / 2).
    { apply Rmult_le_reg_r with (r := 2 * INR n); [lra|].
      replace (PI / INR n * (2 * INR n)) with (2 * PI) by (field; lra).
      replace (PI / 2 * (2 * INR n)) with (INR n * PI) by field.
      apply Rmult_le_compat_r; [lra|].
      replace 2 with (INR 2).
      - apply le_INR. exact Hn.
      - simpl. lra. }
    lra.
Qed.

Lemma succ_frac : forall n k,
  (n <> 0)%nat ->
  INR (S k) / INR n = INR k / INR n + 1 / INR n.
Proof.
  intros n k Hn. rewrite S_INR. field. apply not_0_INR. exact Hn.
Qed.

Lemma sub_window : forall n k t,
  (n <> 0)%nat -> (k < n)%nat ->
  INR k / INR n <= t <= INR (S k) / INR n ->
  Rabs (t - (INR k / INR n + 1 / (2 * INR n))) <= 1 / (2 * INR n).
Proof.
  intros n k t Hn Hk Ht.
  rewrite (succ_frac n k Hn) in Ht.
  assert (HnR : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hh : 0 < 1 / (2 * INR n)) by (unfold Rdiv; apply Rmult_lt_0_compat;
    [lra|apply Rinv_0_lt_compat; lra]).
  apply Rabs_le. split.
  - assert (Hlow : INR k / INR n + 1 / (2 * INR n) - 1 / (2 * INR n)
                    <= t) by lra.
    replace (INR k / INR n + 1 / (2 * INR n) - 1 / (2 * INR n))
      with (INR k / INR n) in Hlow by ring.
    lra.
  - assert (Hhi : t <= INR k / INR n + 1 / INR n) by lra.
    assert (Hhalf : 1 / INR n = 1 / (2 * INR n) + 1 / (2 * INR n)) by (field; lra).
    lra.
Qed.

Lemma local_offset_bound : forall c n k t,
  (2 <= n)%nat -> (k < n)%nat ->
  Rabs (circ_sweep c) <= 2 * PI ->
  INR k / INR n <= t <= INR (S k) / INR n ->
  let psi := lin_angle c t - sub_mid c n k in
  let delta := sub_delta c n in
  Rabs psi <= Rabs delta /\ Rabs delta <= PI / 2 /\
  lin_angle c t = sub_mid c n k + psi.
Proof.
  intros c n k t Hn Hk Hsw Ht psi delta.
  assert (Hn0 : (n <> 0)%nat) by lia.
  assert (Hwin := sub_window n k t Hn0 Hk Ht).
  unfold psi, delta, sub_mid, sub_delta.
  assert (Hpsi : lin_angle c t - (lin_angle c (INR k / INR n) +
            circ_sweep c / (2 * INR n))
          = (t - (INR k / INR n + 1 / (2 * INR n))) * circ_sweep c).
  { unfold lin_angle. field. apply not_0_INR. exact Hn0. }
  assert (Habs : Rabs (circ_sweep c / (2 * INR n)) =
                 Rabs (circ_sweep c) / (2 * INR n)).
  { unfold Rdiv. rewrite Rabs_mult.
    rewrite Rabs_inv by (assert (0 < INR n) by (apply lt_0_INR; lia); lra).
    rewrite (Rabs_right (2 * INR n))
      by (assert (0 < INR n) by (apply lt_0_INR; lia); lra).
    reflexivity. }
  split.
  - rewrite Hpsi. rewrite Rabs_mult. rewrite Habs. unfold Rdiv.
    unfold Rdiv in Hwin.
    apply Rle_trans with ((1 * / (2 * INR n)) * Rabs (circ_sweep c)).
    + apply Rmult_le_compat_r; [apply Rabs_pos|exact Hwin].
    + apply Req_le. ring.
  - split.
    + rewrite Habs. apply half_le_right_angle; assumption.
    + unfold lin_angle. ring.
Qed.

Lemma cos_abs_mono : forall x y,
  Rabs x <= Rabs y -> Rabs y <= PI / 2 -> cos y <= cos x.
Proof.
  intros x y Hxy Hy.
  assert (Hx : Rabs x <= PI / 2) by lra.
  pose proof PI_RGT_0 as HPI.
  assert (Hcx : cos x = cos (Rabs x)).
  { destruct (Rle_dec 0 x) as [Hp|Hn].
    - rewrite (Rabs_right x) by lra. reflexivity.
    - rewrite (Rabs_left x) by lra. rewrite cos_neg. reflexivity. }
  assert (Hcy : cos y = cos (Rabs y)).
  { destruct (Rle_dec 0 y) as [Hp|Hn].
    - rewrite (Rabs_right y) by lra. reflexivity.
    - rewrite (Rabs_left y) by lra. rewrite cos_neg. reflexivity. }
  rewrite Hcx, Hcy.
  apply cos_decr_1.
  - apply Rabs_pos.
  - lra.
  - apply Rabs_pos.
  - lra.
  - exact Hxy.
Qed.

(* The sample at local offset psi, written in the bisector frame. *)
Lemma eval_frame : forall c mid psi,
  px (circ_o c) + circ_r c * cos (mid + psi) =
    px (circ_o c) + circ_r c * cos psi * cos mid
                  - circ_r c * sin psi * sin mid /\
  py (circ_o c) + circ_r c * sin (mid + psi) =
    py (circ_o c) + circ_r c * cos psi * sin mid
                  + circ_r c * sin psi * cos mid.
Proof.
  intros c mid psi.
  rewrite cos_plus, sin_plus. split; ring.
Qed.

Definition frame_foot (c : CircularEgg) (mid psi delta : R) : Point :=
  mkPoint
    (px (circ_o c) + circ_r c * cos delta * cos mid
                   - circ_r c * sin psi * sin mid)
    (py (circ_o c) + circ_r c * cos delta * sin mid
                   + circ_r c * sin psi * cos mid).

Lemma frame_foot_at_end : forall c mid delta,
  frame_foot c mid delta delta =
  mkPoint (px (circ_o c) + circ_r c * cos (mid + delta))
          (py (circ_o c) + circ_r c * sin (mid + delta)) /\
  frame_foot c mid (- delta) (- delta) =
  mkPoint (px (circ_o c) + circ_r c * cos (mid - delta))
          (py (circ_o c) + circ_r c * sin (mid - delta)).
Proof.
  intros c mid delta. unfold frame_foot. split.
  - apply (f_equal2 mkPoint).
    + rewrite cos_plus. ring.
    + rewrite sin_plus. ring.
  - apply (f_equal2 mkPoint).
    + replace (mid - delta) with (mid + - delta) by ring.
      rewrite cos_plus. rewrite cos_neg, sin_neg. ring.
    + replace (mid - delta) with (mid + - delta) by ring.
      rewrite sin_plus. rewrite cos_neg, sin_neg. ring.
Qed.

Lemma sin_abs_small : forall x,
  Rabs x <= PI / 2 -> Rabs (sin x) = sin (Rabs x).
Proof.
  intros x Hx.
  pose proof PI_RGT_0 as HPI.
  destruct (Rle_dec 0 x) as [Hp|Hn].
  - rewrite (Rabs_right x) by lra.
    assert (Hx1 : x <= PI / 2).
    { rewrite (Rabs_right x) in Hx by lra. exact Hx. }
    assert (Hs : 0 <= sin x) by (apply sin_ge_0; lra).
    apply Rle_ge in Hs.
    rewrite (Rabs_right (sin x)) by exact Hs.
    reflexivity.
  - assert (Hxlt : x < 0) by lra.
    assert (Hx1 : - x <= PI / 2).
    { rewrite (Rabs_left x) in Hx by exact Hxlt. exact Hx. }
    assert (Hs : 0 <= sin (- x)) by (apply sin_ge_0; lra).
    assert (Hle : sin x <= 0).
    { apply Ropp_le_cancel. rewrite Ropp_0, <- sin_neg. exact Hs. }
    rewrite (Rabs_left x) by exact Hxlt.
    rewrite sin_neg.
    rewrite (Rabs_left1 (sin x)) by exact Hle.
    reflexivity.
Qed.

Lemma frame_dist_sq : forall c mid psi delta,
  let p := mkPoint (px (circ_o c) + circ_r c * cos (mid + psi))
                   (py (circ_o c) + circ_r c * sin (mid + psi)) in
  dist_sq p (frame_foot c mid psi delta) =
    (circ_r c * (cos psi - cos delta)) * (circ_r c * (cos psi - cos delta)).
Proof.
  intros c mid psi delta p. unfold p, dist_sq, frame_foot. cbn.
  assert (Hdx :
    (px (circ_o c) + circ_r c * cos (mid + psi)) -
    (px (circ_o c) + circ_r c * cos delta * cos mid
                    - circ_r c * sin psi * sin mid)
    = circ_r c * cos mid * (cos psi - cos delta)).
  { rewrite cos_plus. ring. }
  assert (Hdy :
    (py (circ_o c) + circ_r c * sin (mid + psi)) -
    (py (circ_o c) + circ_r c * cos delta * sin mid
                    + circ_r c * sin psi * cos mid)
    = circ_r c * sin mid * (cos psi - cos delta)).
  { rewrite sin_plus. ring. }
  rewrite Hdx, Hdy.
  pose proof (sin2_cos2 mid) as Hid. unfold Rsqr in Hid.
  replace
    (circ_r c * cos mid * (cos psi - cos delta) *
     (circ_r c * cos mid * (cos psi - cos delta)) +
     circ_r c * sin mid * (cos psi - cos delta) *
     (circ_r c * sin mid * (cos psi - cos delta)))
    with ((circ_r c * (cos psi - cos delta)) *
          (circ_r c * (cos psi - cos delta)) *
          (cos mid * cos mid + sin mid * sin mid)) by ring.
  replace (cos mid * cos mid + sin mid * sin mid) with 1.
  - ring.
  - rewrite <- Hid. ring.
Qed.

Lemma sin_small_eq0 : forall x,
  Rabs x <= PI / 2 -> sin x = 0 -> x = 0.
Proof.
  intros x Hx Hs.
  pose proof PI_RGT_0 as HPI.
  assert (Ha : sin (Rabs x) = 0).
  { rewrite <- (sin_abs_small x Hx). rewrite Hs. apply Rabs_R0. }
  destruct (Req_dec (Rabs x) 0) as [Hz|Hnz].
  - destruct (Req_dec x 0) as [Hx0|Hnx].
    + exact Hx0.
    + pose proof (Rabs_pos_lt x Hnx) as Hpos. lra.
  - assert (Hpos : 0 < Rabs x).
    { apply Rnot_le_lt. intros Hle. apply Hnz.
      apply Rle_antisym; [exact Hle|apply Rabs_pos]. }
    assert (Hlt : Rabs x < PI) by lra.
    pose proof (sin_gt_0 (Rabs x) Hpos Hlt) as Hg. lra.
Qed.

Lemma sin_ratio_in_unit : forall psi delta,
  Rabs psi <= Rabs delta ->
  Rabs delta <= PI / 2 ->
  sin delta = 0 \/
  sin delta <> 0 /\ Rabs (sin psi / sin delta) <= 1.
Proof.
  intros psi delta Hle Hpi.
  pose proof PI_RGT_0 as HPI.
  destruct (Req_dec (sin delta) 0) as [Hz|Hnz]; [left; exact Hz|right].
  split; [exact Hnz|].
  assert (Hspsi : Rabs (sin psi) = sin (Rabs psi))
    by (apply sin_abs_small; lra).
  assert (Hsdel : Rabs (sin delta) = sin (Rabs delta))
    by (apply sin_abs_small; lra).
  assert (Hsin : sin (Rabs psi) <= sin (Rabs delta)).
  { pose proof (Rabs_pos psi) as Hp.
    pose proof (Rabs_pos delta) as Hd.
    apply sin_incr_1; lra. }
  unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_inv by exact Hnz.
  apply Rmult_le_reg_r with (r := Rabs (sin delta)).
  - apply Rabs_pos_lt. exact Hnz.
  - rewrite Rmult_assoc. rewrite Rinv_l by (apply Rabs_no_R0; exact Hnz).
    rewrite Rmult_1_r, Rmult_1_l. rewrite Hspsi, Hsdel. exact Hsin.
Qed.

Lemma foot_convex : forall c mid psi delta,
  Rabs psi <= Rabs delta ->
  Rabs delta <= PI / 2 ->
  on_seg
    (mkPoint (px (circ_o c) + circ_r c * cos (mid - delta))
             (py (circ_o c) + circ_r c * sin (mid - delta)))
    (mkPoint (px (circ_o c) + circ_r c * cos (mid + delta))
             (py (circ_o c) + circ_r c * sin (mid + delta)))
    (frame_foot c mid psi delta).
Proof.
  intros c mid psi delta Hle Hpi.
  destruct (sin_ratio_in_unit psi delta Hle Hpi) as [Hz|[Hnz Hratio]].
  - assert (Hd0 : delta = 0) by (apply sin_small_eq0; assumption).
    assert (Hp0 : psi = 0).
    { assert (Hzabs : Rabs psi = 0).
      { apply Rle_antisym; [|apply Rabs_pos].
        rewrite Hd0 in Hle. rewrite Rabs_R0 in Hle. exact Hle. }
      destruct (Req_dec psi 0) as [H0|Hn0].
      - exact H0.
      - pose proof (Rabs_pos_lt psi Hn0) as Hpos. lra. }
    subst psi delta.
    exists 0. split; [lra|].
    unfold seg_at, frame_foot. cbn.
    rewrite sin_0, cos_0.
    replace (mid - 0) with mid by ring.
    apply (f_equal2 mkPoint); ring.
  - set (lam := (sin psi / sin delta + 1) / 2).
    assert (Hspan : -1 <= sin psi / sin delta <= 1).
    { destruct (Rle_dec 0 (sin psi / sin delta)) as [Hp|Hn].
      - rewrite (Rabs_right (sin psi / sin delta)) in Hratio by lra. lra.
      - rewrite (Rabs_left (sin psi / sin delta)) in Hratio by lra. lra. }
    assert (Hlam : 0 <= lam <= 1) by (unfold lam; lra).
    exists lam. split; [exact Hlam|].
    unfold seg_at, frame_foot, lam. cbn.
    rewrite cos_plus, sin_plus, cos_minus, sin_minus.
    apply (f_equal2 mkPoint); field; exact Hnz.
Qed.

Lemma sample_angle_start : forall c n k,
  (n <> 0)%nat ->
  lin_angle c (INR k / INR n) = sub_mid c n k - sub_delta c n.
Proof.
  intros c n k _. unfold sub_mid, sub_delta. ring.
Qed.

Lemma sample_angle_end : forall c n k,
  (n <> 0)%nat ->
  lin_angle c (INR (S k) / INR n) = sub_mid c n k + sub_delta c n.
Proof.
  intros c n k Hn.
  unfold sub_mid, sub_delta, lin_angle.
  rewrite (succ_frac n k Hn). field. apply not_0_INR. exact Hn.
Qed.

Lemma nth_at_angle : forall c n k ang,
  (2 <= n)%nat -> (k <= n)%nat ->
  ang = lin_angle c (INR k / INR n) ->
  nth k (lin_pts c n) (circ_start c) =
  mkPoint (px (circ_o c) + circ_r c * cos ang)
          (py (circ_o c) + circ_r c * sin ang).
Proof.
  intros c n k ang Hn Hk Hang.
  destruct (lin_vertex_on_arc c n k Hn Hk) as [Heq _].
  cbn zeta in Heq. rewrite Heq. unfold circ_eval.
  unfold lin_angle in Hang. rewrite <- Hang. reflexivity.
Qed.

Theorem chord_approx_error_bound : forall c step n k t,
  (2 <= n)%nat ->
  (k < n)%nat ->
  0 <= circ_r c ->
  0 < step <= 2 * PI ->
  Rabs (circ_sweep c) <= 2 * PI ->
  Rabs (circ_sweep c) <= INR n * step ->
  INR k / INR n <= t <= INR (S k) / INR n ->
  exists q,
    on_seg (nth k (lin_pts c n) (circ_start c))
           (nth (S k) (lin_pts c n) (circ_start c)) q /\
    dist (circ_eval c t) q <= circ_r c * (1 - cos (step / 2)).
Proof.
  intros c step n k t Hn Hk Hr Hstep Hcircle Hcount Ht.
  assert (Hn0 : (n <> 0)%nat) by lia.
  assert (HkS : (S k <= n)%nat) by lia.
  set (mid := sub_mid c n k).
  set (delta := sub_delta c n).
  set (psi := lin_angle c t - mid).
  destruct (local_offset_bound c n k t Hn Hk Hcircle Ht) as [Hpsi [Hdh _]].
  fold mid in Hpsi. fold mid in Hdh. fold delta in Hpsi. fold delta in Hdh.
  fold psi in Hpsi.
  set (q := frame_foot c mid psi delta).
  assert (Hstart : nth k (lin_pts c n) (circ_start c) =
    mkPoint (px (circ_o c) + circ_r c * cos (mid - delta))
            (py (circ_o c) + circ_r c * sin (mid - delta))).
  { apply nth_at_angle; [exact Hn|lia|].
    rewrite (sample_angle_start c n k Hn0). unfold mid, delta. reflexivity. }
  assert (Hend : nth (S k) (lin_pts c n) (circ_start c) =
    mkPoint (px (circ_o c) + circ_r c * cos (mid + delta))
            (py (circ_o c) + circ_r c * sin (mid + delta))).
  { apply nth_at_angle; [exact Hn|exact HkS|].
    rewrite (sample_angle_end c n k Hn0). unfold mid, delta. reflexivity. }
  assert (Hon0 := foot_convex c mid psi delta Hpsi Hdh).
  rewrite <- Hstart, <- Hend in Hon0.
  exists q. split; [exact Hon0|].
  assert (Hpt : circ_eval c t =
    mkPoint (px (circ_o c) + circ_r c * cos (mid + psi))
            (py (circ_o c) + circ_r c * sin (mid + psi))).
  { unfold circ_eval. unfold psi, mid. replace (sub_mid c n k + (lin_angle c t - sub_mid c n k))
      with (lin_angle c t) by ring.
    unfold lin_angle. reflexivity. }
  assert (Hsq := frame_dist_sq c mid psi delta).
  assert (Hgap : 0 <= cos psi - cos delta).
  { pose proof (cos_abs_mono psi delta Hpsi Hdh) as Hc. lra. }
  assert (Hlen : dist (circ_eval c t) q =
    circ_r c * (cos psi - cos delta)).
  { rewrite Hpt. unfold q, dist. rewrite Hsq.
    rewrite sqrt_square.
    - reflexivity.
    - apply Rmult_le_pos; [exact Hr|exact Hgap]. }
  assert (Habs : Rabs delta <= step / 2).
  { unfold delta, sub_delta.
    replace (Rabs (circ_sweep c / (2 * INR n)))
      with (Rabs (circ_sweep c) / (2 * INR n)).
    - apply half_le_step; [exact Hn0 | lra | exact Hcount].
    - unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_inv.
      rewrite (Rabs_right (2 * INR n))
        by (assert (0 < INR n) by (apply lt_0_INR; lia); lra).
      reflexivity. }
  rewrite Hlen.
  assert (Hone : cos psi <= 1) by (pose proof (COS_bound psi); lra).
  assert (Hle1 : circ_r c * (cos psi - cos delta)
                 <= circ_r c * (1 - cos delta)) by nra.
  apply Rle_trans with (circ_r c * (1 - cos delta)); [exact Hle1|].
  apply Rmult_le_compat_l; [exact Hr|].
  assert (Hmono : cos (step / 2) <= cos (Rabs delta)).
  { pose proof PI_RGT_0 as HPI.
    apply cos_decr_1.
    - apply Rabs_pos.
    - lra.
    - lra.
    - lra.
    - exact Habs. }
  assert (Heven : cos (Rabs delta) = cos delta).
  { destruct (Rle_dec 0 delta) as [Hp|Hnneg].
    - rewrite (Rabs_right delta) by lra. reflexivity.
    - rewrite (Rabs_left delta) by lra. apply cos_neg. }
  lra.
Qed.

(* Assumptions: each block stays inside the 3-axiom allowlist. *)
Print Assumptions clamp11_bounds.
Print Assumptions clamp11_id.
Print Assumptions clamp_gap_nonneg.
Print Assumptions dev_half_cos.
Print Assumptions atan2_nonneg_ord.
Print Assumptions dev_to_step_range.
Print Assumptions dev_to_step_pos.
Print Assumptions chord_sagitta_le_dev.
Print Assumptions effective_reject_angle.
Print Assumptions effective_reject_dev.
Print Assumptions effective_reject_radius.
Print Assumptions effective_step_pos.
Print Assumptions effective_step_le_dev.
Print Assumptions half_le_step.
Print Assumptions half_le_right_angle.
Print Assumptions succ_frac.
Print Assumptions sub_window.
Print Assumptions local_offset_bound.
Print Assumptions cos_abs_mono.
Print Assumptions eval_frame.
Print Assumptions frame_foot_at_end.
Print Assumptions sin_abs_small.
Print Assumptions frame_dist_sq.
Print Assumptions sin_small_eq0.
Print Assumptions sin_ratio_in_unit.
Print Assumptions foot_convex.
Print Assumptions sample_angle_start.
Print Assumptions sample_angle_end.
Print Assumptions nth_at_angle.
Print Assumptions chord_approx_error_bound.
