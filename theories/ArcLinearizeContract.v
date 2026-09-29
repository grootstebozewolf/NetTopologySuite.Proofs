(* ============================================================================
   NetTopologySuite.Proofs.ArcLinearizeContract
   ----------------------------------------------------------------------------
   Generic linearization contract, and its arc instance.

   Linearizes γ revγ pts θ n tol packages the six facts a densifier owes
   its consumer: vertices on the curve, exact ends, a monotone parameter,
   Hausdorff distance at most tol, reversal swapping γ(t) with γ(1−t),
   and n ≥ 2. arc_linearizes is that contract for circ_eval at
   n = subdiv_n step Δθ and tol = r·(1 − cos(step/2)).

   Both Hausdorff directions are named for a later contract to wrap:
   `arc_curve_near_polyline` (curve → polyline, via
   `chord_approx_error_bound`) and `arc_polyline_near_curve` (polyline →
   curve). A chord point lies inside the circle, at least r·cos(δ) from
   the centre, so its distance to the arc is r − |q − O|.

   claimId: 0007-arc-linearize. witness: 0007-arc-linearize.
   3-axiom host. No Admitted / Axiom / Parameter. No RiemannInt.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia Field Psatz List PeanoNat ZArith.
From NTS.Proofs Require Import
  Distance SheetHenCircEgg Atan2 Linearise ArcLinearize ArcLinearizeBound.
Local Open Scope R_scope.

Definition curve_shape (g : R -> Point) : Shape :=
  fun p => exists t, 0 <= t <= 1 /\ p = g t.

Definition poly_shape (pts : list Point) : Shape :=
  fun q => exists k lam d,
    (S k < length pts)%nat /\
    0 <= lam <= 1 /\
    q = seg_at (nth k pts d) (nth (S k) pts d) lam.

Record Linearizes
    (g rev_g : R -> Point) (pts : list Point) (theta : nat -> R)
    (n : nat) (tol : R) : Prop :=
  Build_Linearizes {
    lz_n : (2 <= n)%nat;
    lz_length : length pts = S n;
    lz_on_curve : forall k, (k <= n)%nat ->
      nth k pts (g 0) = g (INR k / INR n);
    lz_exact_start : nth 0 pts (g 0) = g 0;
    lz_exact_end : nth n pts (g 0) = g 1;
    lz_param_mono : forall i j, (i <= j)%nat -> (j <= n)%nat ->
      INR i / INR n <= INR j / INR n /\
      0 <= (theta j - theta i) * (theta n - theta 0%nat);
    lz_hausdorff : hausdorff_le (curve_shape g) (poly_shape pts) tol;
    lz_reverse_fun : forall t, rev_g t = g (1 - t);
    lz_reverse_pts : forall k, (k <= n)%nat ->
      nth k (rev pts) (g 0) = rev_g (INR k / INR n)
  }.

Definition radial_at (c : CircularEgg) (ang : R) : Point :=
  mkPoint (px (circ_o c) + circ_r c * cos ang)
          (py (circ_o c) + circ_r c * sin ang).

Definition chord_mu (lam : R) : R := 2 * lam - 1.

Definition chord_s2 (delta mu : R) : R :=
  cos delta * cos delta + mu * mu * sin delta * sin delta.

Lemma point_eq : forall p q, px p = px q -> py p = py q -> p = q.
Proof. intros [] [] Hx Hy. cbn in Hx, Hy. subst. reflexivity. Qed.

Lemma seg_at_same : forall p lam, seg_at p p lam = p.
Proof.
  intros p lam. unfold seg_at. destruct p as [x y]. cbn.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma radial_at_eval : forall c t, radial_at c (lin_angle c t) = circ_eval c t.
Proof. intros c t. unfold radial_at, circ_eval, lin_angle. reflexivity. Qed.

Lemma radial_at_dist : forall c ang,
  0 <= circ_r c -> dist (circ_o c) (radial_at c ang) = circ_r c.
Proof.
  intros c ang Hr. unfold dist, radial_at, dist_sq. cbn.
  pose proof (sin2_cos2 ang) as Hs. unfold Rsqr in Hs.
  replace (_ * _ + _ * _) with (circ_r c * circ_r c) by nra.
  apply sqrt_square. exact Hr.
Qed.

Lemma dist_sq_zero_eq : forall p q, dist_sq p q = 0 -> p = q.
Proof.
  intros [a b] [u v] H. unfold dist_sq in H. cbn in H.
  pose proof (sqr_nonneg (a - u)) as Hu.
  pose proof (sqr_nonneg (b - v)) as Hv.
  assert (a - u = 0).
  { apply Rsqr_0_uniq. unfold Rsqr. lra. }
  assert (b - v = 0).
  { apply Rsqr_0_uniq. unfold Rsqr. lra. }
  apply point_eq; cbn; lra.
Qed.

Lemma quarter_cos_nonneg : forall a, Rabs a <= PI / 2 -> 0 <= cos a.
Proof.
  intros a Ha.
  pose proof PI_RGT_0 as HPI.
  assert (He : cos a = cos (Rabs a)).
  { destruct (Rle_dec 0 a) as [Hp|Hn].
    - rewrite Rabs_right by lra. reflexivity.
    - rewrite Rabs_left by lra. rewrite cos_neg. reflexivity. }
  rewrite He, <- cos_PI2. apply cos_decr_1.
  - apply Rabs_pos.
  - lra.
  - lra.
  - lra.
  - exact Ha.
Qed.

Lemma cos_lt_0_past_quarter : forall a, PI / 2 < a <= PI -> cos a < 0.
Proof.
  intros a Ha.
  pose proof PI_RGT_0 as HPI.
  assert (Hs : sin (a - PI / 2) = - cos a).
  { rewrite sin_minus, cos_PI2, sin_PI2. ring. }
  assert (0 < sin (a - PI / 2)) by (apply sin_gt_0; lra).
  lra.
Qed.

Lemma cos_nonneg_principal_quarter : forall a,
  - PI < a <= PI -> 0 <= cos a -> Rabs a <= PI / 2.
Proof.
  intros a Hr Hc.
  pose proof PI_RGT_0 as HPI.
  destruct (Rle_lt_dec 0 a) as [Hp|Hn].
  - rewrite Rabs_right by lra.
    destruct (Rle_lt_dec a (PI / 2)) as [Hle|Hgt]; [exact Hle|].
    assert (cos a < 0) by (apply cos_lt_0_past_quarter; lra). lra.
  - rewrite Rabs_left by lra.
    destruct (Rle_lt_dec (- a) (PI / 2)) as [Hle|Hgt]; [exact Hle|].
    assert (Hneg : cos (- a) < 0) by (apply cos_lt_0_past_quarter; lra).
    rewrite cos_neg in Hneg. lra.
Qed.

Lemma chord_mu_bound : forall lam, 0 <= lam <= 1 -> Rabs (chord_mu lam) <= 1.
Proof. intros lam H. unfold chord_mu. apply Rabs_le. lra. Qed.

Lemma chord_offset : forall c mid delta lam,
  let q := seg_at (radial_at c (mid - delta)) (radial_at c (mid + delta)) lam in
  px q - px (circ_o c) =
    circ_r c * (cos delta * cos mid - chord_mu lam * sin delta * sin mid) /\
  py q - py (circ_o c) =
    circ_r c * (cos delta * sin mid + chord_mu lam * sin delta * cos mid).
Proof.
  intros c mid delta lam q. unfold q, chord_mu, seg_at, radial_at. cbn.
  rewrite cos_minus, sin_minus, cos_plus, sin_plus. split; ring.
Qed.

Lemma chord_center_sq : forall c mid delta lam,
  dist_sq (circ_o c)
    (seg_at (radial_at c (mid - delta)) (radial_at c (mid + delta)) lam) =
  circ_r c * circ_r c * chord_s2 delta (chord_mu lam).
Proof.
  intros c mid delta lam.
  unfold dist_sq, seg_at, radial_at, chord_s2, chord_mu. cbn.
  rewrite cos_minus, sin_minus, cos_plus, sin_plus.
  pose proof (sin2_cos2 mid) as Hm. unfold Rsqr in Hm.
  assert (Hs : sin mid ^ 2 = sin mid * sin mid) by (simpl; ring).
  assert (Hc : cos mid ^ 2 = cos mid * cos mid) by (simpl; ring).
  assert (Hsm : sin mid * sin mid = 1 - cos mid * cos mid).
  { apply (Rplus_eq_reg_l (cos mid * cos mid)).
    replace (cos mid * cos mid + sin mid * sin mid)
      with (sin mid * sin mid + cos mid * cos mid) by ring.
    rewrite Hm. ring. }
  ring_simplify. rewrite Hs, Hc, Hsm. ring.
Qed.

Lemma s2_bounds : forall delta mu,
  Rabs delta <= PI / 2 -> Rabs mu <= 1 ->
  0 <= cos delta /\
  cos delta * cos delta <= chord_s2 delta mu <= 1.
Proof.
  intros delta mu Hd Hmu.
  assert (Hc : 0 <= cos delta) by (apply quarter_cos_nonneg; exact Hd).
  assert (Hmu2 : mu * mu <= 1).
  { pose proof (Rsqr_abs mu) as Hs. unfold Rsqr in Hs.
    assert (Rabs mu * Rabs mu <= 1).
    { apply Rle_trans with (1 * 1).
      - apply Rmult_le_compat; try apply Rabs_pos; lra.
      - lra. }
    lra. }
  pose proof (sin2_cos2 delta) as Hid. unfold Rsqr in Hid.
  unfold chord_s2. split; [exact Hc|]. nra.
Qed.

Lemma sub_delta_abs : forall c n,
  (n <> 0)%nat ->
  Rabs (sub_delta c n) = Rabs (circ_sweep c) / (2 * INR n).
Proof.
  intros c n Hn. unfold sub_delta, Rdiv.
  assert (0 < INR n) by (apply lt_0_INR; lia).
  rewrite Rabs_mult.
  rewrite Rabs_inv by lra.
  rewrite (Rabs_right (2 * INR n)) by lra.
  reflexivity.
Qed.

Lemma abs_cos0_quarter : forall a,
  Rabs a <= PI / 2 -> cos a = 0 -> Rabs a = PI / 2.
Proof.
  intros a Ha Hc.
  pose proof PI_RGT_0 as HPI.
  assert (Hz : cos (Rabs a) = 0).
  { destruct (Rle_dec 0 a) as [Hp|Hn].
    - rewrite Rabs_right by lra. exact Hc.
    - rewrite Rabs_left by lra. rewrite cos_neg. exact Hc. }
  destruct (Rle_lt_or_eq_dec (Rabs a) (PI / 2) Ha) as [Hlt|Heq].
  - exfalso.
    assert (Hltc : cos (PI / 2) < cos (Rabs a)).
    { apply cos_diff_pos_quarter; [apply Rabs_pos|exact Hlt|lra]. }
    rewrite cos_PI2, Hz in Hltc. lra.
  - exact Heq.
Qed.

Lemma sagitta_le_step : forall r delta step,
  0 <= r -> Rabs delta <= step / 2 -> step / 2 <= PI ->
  r * (1 - cos delta) <= r * (1 - cos (step / 2)).
Proof.
  intros r delta step Hr Hdel Hpi.
  pose proof PI_RGT_0 as HPI.
  assert (Hstep : 0 <= step / 2).
  { pose proof (Rabs_pos delta). lra. }
  assert (Heven : cos delta = cos (Rabs delta)).
  { destruct (Rle_dec 0 delta) as [Hp|Hn].
    - rewrite Rabs_right by lra. reflexivity.
    - rewrite Rabs_left by lra. rewrite cos_neg. reflexivity. }
  assert (Hmono : cos (step / 2) <= cos (Rabs delta)).
  { apply cos_decr_1.
    - apply Rabs_pos.
    - lra.
    - exact Hstep.
    - exact Hpi.
    - exact Hdel. }
  nra.
Qed.

Lemma chord_phi_le_delta : forall delta mu,
  Rabs delta <= PI / 2 -> Rabs mu <= 1 ->
  0 < chord_s2 delta mu ->
  Rabs (atan2 (mu * sin delta) (cos delta)) <= Rabs delta.
Proof.
  intros delta mu Hd Hmu Hs.
  destruct (s2_bounds delta mu Hd Hmu) as [Hc [Hlo Hhi]].
  set (x := cos delta). set (y := mu * sin delta).
  set (s := sqrt (chord_s2 delta mu)).
  set (phi := atan2 y x).
  assert (Hs2 : chord_s2 delta mu = x * x + y * y) by (unfold chord_s2, x, y; ring).
  assert (Hne : ~ (x = 0 /\ y = 0)).
  { intros [Hx Hy]. apply Rlt_not_le in Hs. apply Hs.
    rewrite Hs2, Hx, Hy. lra. }
  assert (Hspos : 0 < s).
  { unfold s. apply sqrt_lt_R0. exact Hs. }
  assert (Hsle : s <= 1).
  { unfold s. rewrite <- sqrt_1. apply sqrt_le_1; lra. }
  assert (Hxle : x <= s).
  { rewrite <- (sqrt_square x) by exact Hc. unfold s. rewrite Hs2.
    apply sqrt_le_1; [nra|nra|nra]. }
  assert (Hcphi : cos phi = x / s).
  { unfold phi. rewrite (cos_atan2 x y Hne). unfold s. rewrite <- Hs2.
    reflexivity. }
  assert (Hcos : 0 <= cos phi).
  { rewrite Hcphi. apply Rmult_le_pos; [exact Hc|].
    apply Rlt_le, Rinv_0_lt_compat. exact Hspos. }
  pose proof (atan2_range x y Hne) as Hrng.
  assert (Hqu : Rabs phi <= PI / 2).
  { unfold phi. apply cos_nonneg_principal_quarter; [exact Hrng|exact Hcos]. }
  assert (Hge : cos (Rabs delta) <= cos (Rabs phi)).
  { assert (Hdiv : x <= x / s).
    { apply Rmult_le_reg_r with (r := s); [exact Hspos|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
      apply Rle_trans with (x * 1).
      + apply Rmult_le_compat_l; [exact Hc|exact Hsle].
      + lra. }
    assert (Heven : cos (Rabs phi) = cos phi).
    { destruct (Rle_dec 0 phi) as [Hp|Hn].
      - rewrite Rabs_right by lra. reflexivity.
      - rewrite Rabs_left by lra. apply cos_neg. }
    assert (Hde : cos (Rabs delta) = x).
    { unfold x. destruct (Rle_dec 0 delta) as [Hp|Hn].
      - rewrite Rabs_right by lra. reflexivity.
      - rewrite Rabs_left by lra. apply cos_neg. }
    lra. }
  apply cos_abs_le_inv.
  - split; [apply Rabs_pos|exact Hd].
  - split; [apply Rabs_pos|exact Hqu].
  - exact Hge.
Qed.

Lemma scaled_ray_dist : forall ox oy dx dy r s,
  0 <= r -> 0 < s -> s <= 1 ->
  dx * dx + dy * dy = (r * s) * (r * s) ->
  dist (mkPoint (ox + dx) (oy + dy))
       (mkPoint (ox + dx / s) (oy + dy / s)) = r * (1 - s).
Proof.
  intros ox oy dx dy r s Hr Hs Hs1 Hid.
  unfold dist, dist_sq. cbn.
  assert (Hx : (ox + dx) - (ox + dx / s) = - (dx * (1 - s) / s)) by (field; lra).
  assert (Hy : (oy + dy) - (oy + dy / s) = - (dy * (1 - s) / s)) by (field; lra).
  rewrite Hx, Hy.
  replace ((- (dx * (1 - s) / s)) * (- (dx * (1 - s) / s)) +
           (- (dy * (1 - s) / s)) * (- (dy * (1 - s) / s)))
    with ((dx * dx + dy * dy) * ((1 - s) * (1 - s)) / (s * s)) by (field; lra).
  rewrite Hid.
  replace ((r * s) * (r * s) * ((1 - s) * (1 - s)) / (s * s))
    with ((r * (1 - s)) * (r * (1 - s))) by (field; lra).
  apply sqrt_square. nra.
Qed.

Lemma chord_local_near : forall c mid delta lam,
  0 <= circ_r c ->
  Rabs delta <= PI / 2 ->
  0 <= lam <= 1 ->
  exists ang,
    Rabs (ang - mid) <= Rabs delta /\
    dist (seg_at (radial_at c (mid - delta)) (radial_at c (mid + delta)) lam)
         (radial_at c ang)
    <= circ_r c * (1 - cos delta).
Proof.
  intros c mid delta lam Hr Hdel Hlam.
  set (mu := chord_mu lam).
  set (s2 := chord_s2 delta mu).
  set (q := seg_at (radial_at c (mid - delta)) (radial_at c (mid + delta)) lam).
  assert (Hmu : Rabs mu <= 1) by (unfold mu; apply chord_mu_bound; exact Hlam).
  destruct (s2_bounds delta mu Hdel Hmu) as [Hc [Hlo Hhi]].
  destruct (Req_dec s2 0) as [Hz|Hnz].
  - exists mid. split.
    + replace (mid - mid) with 0 by ring. rewrite Rabs_R0. apply Rabs_pos.
    + assert (Hc0 : cos delta = 0).
      { assert (cos delta * cos delta = 0) by (unfold s2, chord_s2 in Hz; nra).
        nra. }
      assert (Hq : q = circ_o c).
      { apply eq_sym. apply dist_sq_zero_eq.
        transitivity (circ_r c * circ_r c * chord_s2 delta (chord_mu lam)).
        - exact (chord_center_sq c mid delta lam).
        - unfold s2, mu in Hz. nra. }
      fold q. rewrite Hq. rewrite radial_at_dist by exact Hr.
      rewrite Hc0. lra.
  - assert (Hnn : 0 <= s2).
    { pose proof (sqr_nonneg (cos delta)) as Hcs.
      pose proof (sqr_nonneg (mu * sin delta)) as Hms.
      unfold s2, chord_s2. lra. }
    assert (Hs2 : 0 < s2).
    { destruct (Rle_lt_or_eq_dec 0 s2 Hnn) as [Hlt|Heq]; [exact Hlt|].
      exfalso. apply Hnz. symmetry. exact Heq. }
    set (x := cos delta). set (y := mu * sin delta).
    set (s := sqrt s2). set (phi := atan2 y x).
    assert (Hphi : Rabs phi <= Rabs delta).
    { unfold phi, x, y, s2, mu. apply chord_phi_le_delta; assumption. }
    set (ang := mid + phi).
    set (dx := circ_r c * (cos delta * cos mid - mu * sin delta * sin mid)).
    set (dy := circ_r c * (cos delta * sin mid + mu * sin delta * cos mid)).
    assert (Hsdef : s * s = s2).
    { unfold s. apply sqrt_sqrt. exact Hnn. }
    assert (Hspos : 0 < s) by (unfold s; apply sqrt_lt_R0; exact Hs2).
    assert (Hxle : x <= s).
    { rewrite <- (sqrt_square x) by exact Hc. unfold s.
      apply sqrt_le_1.
      - apply sqr_nonneg.
      - exact Hnn.
      - unfold s2, x. exact Hlo. }
    assert (Hne : ~ (x = 0 /\ y = 0)).
    { intros [Hx0 Hy0]. apply Hnz. unfold s2, chord_s2, x, y, mu in *. nra. }
    assert (Hcphi : cos phi = x / s).
    { unfold phi. rewrite (cos_atan2 x y Hne).
      replace (sqrt (x * x + y * y)) with s.
      - reflexivity.
      - unfold s, s2, chord_s2, x, y. f_equal. ring. }
    assert (Hsphi : sin phi = y / s).
    { unfold phi. rewrite (sin_atan2 x y Hne).
      replace (sqrt (x * x + y * y)) with s.
      - reflexivity.
      - unfold s, s2, chord_s2, x, y. f_equal. ring. }
    assert (Hpt : radial_at c ang =
      mkPoint (px (circ_o c) + dx / s) (py (circ_o c) + dy / s)).
    { apply point_eq; cbn.
      - unfold radial_at, ang. rewrite (proj1 (eval_frame c mid phi)).
        rewrite Hcphi, Hsphi. unfold dx, x, y. field. lra.
      - unfold radial_at, ang. rewrite (proj2 (eval_frame c mid phi)).
        rewrite Hcphi, Hsphi. unfold dy, x, y. field. lra. }
    assert (Hqpt : q = mkPoint (px (circ_o c) + dx) (py (circ_o c) + dy)).
    { apply point_eq; cbn.
      - unfold q, dx, seg_at, radial_at, mu, chord_mu. cbn.
        rewrite cos_minus, cos_plus. ring.
      - unfold q, dy, seg_at, radial_at, mu, chord_mu. cbn.
        rewrite sin_minus, sin_plus. ring. }
    assert (Hsum : dx * dx + dy * dy = (circ_r c * s) * (circ_r c * s)).
    { assert (Hds : dist_sq (circ_o c) q =
        circ_r c * circ_r c * s2).
      { transitivity (circ_r c * circ_r c * chord_s2 delta (chord_mu lam)).
        - exact (chord_center_sq c mid delta lam).
        - unfold s2, mu. reflexivity. }
      rewrite Hqpt in Hds. unfold dist_sq in Hds. cbn in Hds.
      replace (px (circ_o c) + dx - px (circ_o c)) with dx in Hds by ring.
      replace (py (circ_o c) + dy - py (circ_o c)) with dy in Hds by ring.
      rewrite <- Hsdef in Hds. nra. }
    assert (Hsle1 : s <= 1).
    { unfold s. rewrite <- sqrt_1. apply sqrt_le_1.
      - exact Hnn.
      - lra.
      - unfold s2. exact Hhi. }
    assert (Hlen : dist q (radial_at c ang) = circ_r c * (1 - s)).
    { rewrite Hqpt, Hpt.
      apply scaled_ray_dist; [exact Hr|exact Hspos|exact Hsle1|exact Hsum]. }
    exists ang. split.
    + unfold ang. replace (mid + phi - mid) with phi by ring. exact Hphi.
    + rewrite Hlen. nra.
Qed.

Lemma signed_offset_span : forall delta phi sweep n,
  (n <> 0)%nat ->
  sweep <> 0 ->
  delta = sweep / (2 * INR n) ->
  Rabs phi <= Rabs delta ->
  0 <= (delta + phi) / sweep <= / INR n.
Proof.
  intros delta phi sweep n Hn Hsweep Hdelta Hphi.
  assert (Hds : delta / sweep = / (2 * INR n)).
  { rewrite Hdelta. field. split; [apply not_0_INR; exact Hn|exact Hsweep]. }
  assert (Habs : Rabs (phi / sweep) <= Rabs (delta / sweep)).
  { unfold Rdiv. rewrite !Rabs_mult, !Rabs_inv by exact Hsweep.
    apply Rmult_le_compat_r; [|exact Hphi].
    apply Rlt_le, Rinv_0_lt_compat, Rabs_pos_lt. exact Hsweep. }
  assert (Hboth : - Rabs (delta / sweep) <= phi / sweep <= Rabs (delta / sweep)).
  { pose proof (Rabs_pos (delta / sweep)) as Hdp.
    destruct (Rle_dec 0 (phi / sweep)) as [Hp|Hneg].
    - rewrite (Rabs_right (phi / sweep)) in Habs by lra. split; lra.
    - assert (Hnlt : phi / sweep < 0) by lra.
      rewrite (Rabs_left (phi / sweep)) in Habs by exact Hnlt. split; lra. }
  assert (Hpos : delta / sweep = Rabs (delta / sweep)).
  { rewrite Hds. rewrite Rabs_right.
    - reflexivity.
    - apply Rle_ge, Rlt_le, Rinv_0_lt_compat.
      assert (0 < INR n) by (apply lt_0_INR; lia). lra. }
  assert (Htwo : / INR n = / (2 * INR n) + / (2 * INR n)).
  { field. apply not_0_INR. exact Hn. }
  replace ((delta + phi) / sweep) with (delta / sweep + phi / sweep) by (field; exact Hsweep).
  lra.
Qed.

Lemma offset_in_unit : forall n k sweep delta phi,
  (2 <= n)%nat ->
  (k < n)%nat ->
  sweep <> 0 ->
  delta = sweep / (2 * INR n) ->
  Rabs phi <= Rabs delta ->
  0 <= INR k / INR n + (delta + phi) / sweep <= 1.
Proof.
  intros n k sweep delta phi Hn Hk Hsweep Hdelta Hphi.
  assert (Hn0 : (n <> 0)%nat) by lia.
  destruct (signed_offset_span delta phi sweep n Hn0 Hsweep Hdelta Hphi) as [H0 H1].
  assert (Hpos : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hbase : 0 <= INR k / INR n).
  { unfold Rdiv. apply Rmult_le_pos; [apply pos_INR|].
    apply Rlt_le, Rinv_0_lt_compat. exact Hpos. }
  assert (Htop : INR k / INR n + / INR n <= 1).
  { replace (/ INR n) with (1 / INR n) by (unfold Rdiv; field; apply not_0_INR; exact Hn0).
    rewrite <- (succ_frac n k Hn0).
    apply Rmult_le_reg_r with (r := INR n); [exact Hpos|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l
      by (apply not_0_INR; exact Hn0).
    apply le_INR. lia. }
  lra.
Qed.

Theorem chord_point_near_arc : forall c step n k lam,
  (2 <= n)%nat ->
  (k < n)%nat ->
  0 <= circ_r c ->
  0 < step <= 2 * PI ->
  Rabs (circ_sweep c) <= 2 * PI ->
  Rabs (circ_sweep c) <= INR n * step ->
  0 <= lam <= 1 ->
  exists t,
    0 <= t <= 1 /\
    dist (seg_at (nth k (lin_pts c n) (circ_start c))
                 (nth (S k) (lin_pts c n) (circ_start c)) lam)
         (circ_eval c t)
    <= circ_r c * (1 - cos (step / 2)).
Proof.
  intros c step n k lam Hn Hk Hr Hstep Hcircle Hcount Hlam.
  assert (Hn0 : (n <> 0)%nat) by lia.
  set (mid := sub_mid c n k).
  set (delta := sub_delta c n).
  assert (Hdpi : Rabs delta <= PI / 2).
  { unfold delta. rewrite (sub_delta_abs c n Hn0).
    exact (proj2 (half_le_right_angle (circ_sweep c) n Hn Hcircle)). }
  assert (Hdstep : Rabs delta <= step / 2).
  { unfold delta. rewrite (sub_delta_abs c n Hn0).
    apply half_le_step; [exact Hn0|lra|exact Hcount]. }
  assert (Ha : nth k (lin_pts c n) (circ_start c) = radial_at c (mid - delta)).
  { unfold radial_at. apply nth_at_angle; [exact Hn|lia|].
    rewrite (sample_angle_start c n k Hn0). unfold mid, delta. reflexivity. }
  assert (Hb : nth (S k) (lin_pts c n) (circ_start c) = radial_at c (mid + delta)).
  { unfold radial_at. apply nth_at_angle; [exact Hn|lia|].
    rewrite (sample_angle_end c n k Hn0). unfold mid, delta. reflexivity. }
  assert (Hsag : circ_r c * (1 - cos delta) <= circ_r c * (1 - cos (step / 2))).
  { apply sagitta_le_step; [exact Hr|exact Hdstep|].
    pose proof PI_RGT_0 as HPI. lra. }
  destruct (Req_dec (circ_sweep c) 0) as [Hz|Hnz].
  - exists (INR k / INR n).
    split; [apply frac_in_unit; lia|].
    assert (Hd0 : delta = 0).
    { unfold delta, sub_delta. rewrite Hz. field. apply not_0_INR. exact Hn0. }
    assert (Hjoin : nth (S k) (lin_pts c n) (circ_start c) =
                    nth k (lin_pts c n) (circ_start c)).
    { rewrite Ha, Hb, Hd0. apply f_equal. ring. }
    rewrite Hjoin, (seg_at_same _ lam), Ha.
    replace (mid - delta) with (lin_angle c (INR k / INR n))
      by (rewrite (sample_angle_start c n k Hn0); unfold mid, delta; reflexivity).
    rewrite radial_at_eval, dist_self.
    pose proof (COS_bound (step / 2)) as Hbnd. nra.
  - destruct (chord_local_near c mid delta lam Hr Hdpi Hlam) as [ang [Hang Hnear]].
    set (phi := ang - mid).
    assert (Hphi : Rabs phi <= Rabs delta) by (unfold phi; exact Hang).
    assert (Hdeq : delta = circ_sweep c / (2 * INR n)) by (unfold delta, sub_delta; reflexivity).
    set (t := INR k / INR n + (delta + phi) / circ_sweep c).
    assert (Ht : 0 <= t <= 1).
    { unfold t. apply offset_in_unit; assumption. }
    exists t. split; [exact Ht|].
    assert (Hangt : lin_angle c t = ang).
    { unfold t, phi, mid, sub_mid, delta, sub_delta, lin_angle.
      field_simplify_eq; try ring.
      split; [apply not_0_INR; exact Hn0 | exact Hnz]. }
    rewrite Ha, Hb, <- (radial_at_eval c t), Hangt.
    apply Rle_trans with (circ_r c * (1 - cos delta)); [exact Hnear|exact Hsag].
Qed.

Lemma int_part_nonneg : forall x, 0 <= x -> (0 <= Int_part x)%Z.
Proof.
  intros x Hx. unfold Int_part.
  destruct (archimed x) as [Hgt _].
  assert (0 < up x)%Z by (apply lt_IZR; lra).
  lia.
Qed.

Lemma param_bin : forall n t,
  (2 <= n)%nat -> 0 <= t <= 1 ->
  exists k, (k < n)%nat /\ INR k / INR n <= t <= INR (S k) / INR n.
Proof.
  intros n t Hn Ht.
  assert (Hn0 : (n <> 0)%nat) by lia.
  assert (Hpos : 0 < INR n) by (apply lt_0_INR; lia).
  destruct (Req_dec t 1) as [Ht1|Ht1].
  - exists (n - 1)%nat. split; [lia|]. subst t. split.
    + apply Rmult_le_reg_r with (r := INR n); [exact Hpos|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l
        by (apply not_0_INR; exact Hn0).
      rewrite minus_INR, INR_1 by lia. lra.
    + assert (E : S (n - 1) = n) by lia. rewrite E.
      replace (INR n / INR n) with 1 by (field; apply not_0_INR; exact Hn0).
      lra.
  - assert (Htlt : t < 1) by lra.
    set (x := t * INR n).
    assert (Hx : 0 <= x < INR n).
    { unfold x. split.
      - apply Rmult_le_pos; lra.
      - assert (t * INR n < 1 * INR n)
          by (apply Rmult_lt_compat_r; [exact Hpos|exact Htlt]).
        lra. }
    set (z := Int_part x).
    assert (Hz0 : (0 <= z)%Z) by (unfold z; apply int_part_nonneg; lra).
    assert (Hzlt : (z < Z.of_nat n)%Z).
    { destruct (base_Int_part x) as [Hle _]. fold z in Hle.
      apply lt_IZR. rewrite <- INR_IZR_INZ. lra. }
    set (k := Z.to_nat z).
    assert (Hk : (k < n)%nat).
    { unfold k. rewrite <- (Nat2Z.id n).
      apply Z2Nat.inj_lt; [exact Hz0|apply Nat2Z.is_nonneg|exact Hzlt]. }
    exists k. split; [exact Hk|].
    destruct (base_Int_part x) as [Hle Hgt]. fold z in Hle, Hgt.
    assert (Hiz : IZR z = INR k) by (unfold k; apply izr_to_nat; exact Hz0).
    assert (Hspan : INR k <= x < INR k + 1) by lra.
    split.
    + apply Rmult_le_reg_r with (r := INR n); [exact Hpos|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply not_0_INR; exact Hn0).
      unfold x in Hspan. lra.
    + apply Rmult_le_reg_r with (r := INR n); [exact Hpos|].
      rewrite (succ_frac n k Hn0).
      assert (E : (INR k / INR n + 1 / INR n) * INR n = INR k + 1)
        by (field; apply not_0_INR; exact Hn0).
      rewrite E. unfold x in Hspan. lra.
Qed.

Theorem arc_curve_near_polyline : forall c step n,
  (2 <= n)%nat ->
  0 <= circ_r c ->
  0 < step <= 2 * PI ->
  Rabs (circ_sweep c) <= 2 * PI ->
  Rabs (circ_sweep c) <= INR n * step ->
  within_eps (curve_shape (circ_eval c)) (poly_shape (lin_pts c n))
    (circ_r c * (1 - cos (step / 2))).
Proof.
  intros c step n Hn Hr Hstep Hcircle Hcount p [t [Ht Hp]].
  destruct (param_bin n t Hn Ht) as [k [Hk Hbin]].
  destruct (chord_approx_error_bound c step n k t Hn Hk Hr Hstep Hcircle Hcount Hbin)
    as [q [Hon Hdist]].
  exists q. split.
  - destruct Hon as [lam [Hlam Hq]].
    exists k, lam, (circ_start c). split; [|split].
    + rewrite lin_pts_length by lia. lia.
    + exact Hlam.
    + exact Hq.
  - rewrite Hp. exact Hdist.
Qed.

Theorem arc_polyline_near_curve : forall c step n,
  (2 <= n)%nat ->
  0 <= circ_r c ->
  0 < step <= 2 * PI ->
  Rabs (circ_sweep c) <= 2 * PI ->
  Rabs (circ_sweep c) <= INR n * step ->
  within_eps (poly_shape (lin_pts c n)) (curve_shape (circ_eval c))
    (circ_r c * (1 - cos (step / 2))).
Proof.
  intros c step n Hn Hr Hstep Hcircle Hcount q [k [lam [d [Hk [Hlam Hq]]]]].
  assert (Hkn : (k < n)%nat).
  { rewrite lin_pts_length in Hk by lia. lia. }
  assert (Ha : nth k (lin_pts c n) d = nth k (lin_pts c n) (circ_start c)).
  { apply nth_indep. rewrite lin_pts_length by lia. lia. }
  assert (Hb : nth (S k) (lin_pts c n) d =
               nth (S k) (lin_pts c n) (circ_start c)).
  { apply nth_indep. rewrite lin_pts_length by lia. lia. }
  destruct (chord_point_near_arc c step n k lam Hn Hkn Hr Hstep Hcircle Hcount Hlam)
    as [t [Ht Hdist]].
  exists (circ_eval c t). split; [exists t; split; [exact Ht|reflexivity]|].
  rewrite Hq, Ha, Hb. exact Hdist.
Qed.

Theorem arc_linearize_hausdorff : forall c step n,
  (2 <= n)%nat ->
  0 <= circ_r c ->
  0 < step <= 2 * PI ->
  Rabs (circ_sweep c) <= 2 * PI ->
  Rabs (circ_sweep c) <= INR n * step ->
  hausdorff_le (curve_shape (circ_eval c)) (poly_shape (lin_pts c n))
    (circ_r c * (1 - cos (step / 2))).
Proof.
  intros c step n Hn Hr Hstep Hcircle Hcount.
  split.
  - apply arc_curve_near_polyline; assumption.
  - apply arc_polyline_near_curve; assumption.
Qed.

Theorem arc_linearizes : forall c step,
  0 <= circ_r c ->
  0 < step <= 2 * PI ->
  Rabs (circ_sweep c) <= 2 * PI ->
  let n := subdiv_n step (circ_sweep c) in
  Linearizes (circ_eval c) (circ_eval (rev_egg c)) (lin_pts c n)
    (lin_theta c n) n (circ_r c * (1 - cos (step / 2))).
Proof.
  intros c step Hr Hstep Hsw.
  cbn zeta.
  set (n := subdiv_n step (circ_sweep c)).
  destruct (subdiv_n_ok step (circ_sweep c) ltac:(lra)) as [Hn2 [Hs [Hcover _]]].
  apply Build_Linearizes.
  - exact Hn2.
  - apply lin_pts_length. lia.
  - intros k Hk.
    destruct (lin_vertex_on_arc c n k Hn2 Hk) as [Heq _].
    cbn zeta in Heq. exact Heq.
  - exact (lin_endpoint_start c n Hn2).
  - unfold circ_end. exact (lin_endpoint_end c n Hn2).
  - intros i j Hij Hjn. split.
    + assert (Hpos : 0 < INR n) by (apply lt_0_INR; lia).
      apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; exact Hpos|].
      apply le_INR. exact Hij.
    + destruct (Rle_dec 0 (circ_sweep c)) as [Hp|Hneg].
      * pose proof (lin_theta_mono_pos c n i j ltac:(lia) Hij Hjn Hp) as Hm.
        pose proof (lin_sweep_total c n ltac:(lia)) as Htot.
        rewrite Htot. apply Rmult_le_pos; lra.
      * assert (Hsle : circ_sweep c <= 0) by lra.
        pose proof (lin_theta_mono_neg c n i j ltac:(lia) Hij Hjn Hsle) as Hm.
        pose proof (lin_sweep_total c n ltac:(lia)) as Htot.
        rewrite Htot.
        assert (Hprod : 0 <= (lin_theta c n i - lin_theta c n j) * (- circ_sweep c))
          by (apply Rmult_le_pos; lra).
        replace ((lin_theta c n j - lin_theta c n i) * circ_sweep c)
          with ((lin_theta c n i - lin_theta c n j) * (- circ_sweep c)) by ring.
        exact Hprod.
  - apply arc_linearize_hausdorff; try assumption.
  - intros t. apply rev_egg_eval.
  - intros k Hk.
    rewrite rev_egg_eval, (frac_complement n k ltac:(lia) Hk).
    assert (Hlen : (k < length (rev (lin_pts c n)))%nat).
    { rewrite length_rev, lin_pts_length by lia. lia. }
    rewrite (@nth_indep Point (rev (lin_pts c n)) k
              (circ_eval c 0) (circ_start c) Hlen).
    rewrite (nth_rev_lin c n k Hn2 Hk).
    destruct (lin_vertex_on_arc c n (n - k)%nat Hn2 ltac:(lia)) as [Heq _].
    cbn zeta in Heq. exact Heq.
Qed.

(* Assumptions: each block stays inside the 3-axiom allowlist. *)
Print Assumptions point_eq.
Print Assumptions seg_at_same.
Print Assumptions radial_at_eval.
Print Assumptions radial_at_dist.
Print Assumptions dist_sq_zero_eq.
Print Assumptions quarter_cos_nonneg.
Print Assumptions cos_lt_0_past_quarter.
Print Assumptions cos_nonneg_principal_quarter.
Print Assumptions chord_mu_bound.
Print Assumptions chord_offset.
Print Assumptions chord_center_sq.
Print Assumptions s2_bounds.
Print Assumptions sub_delta_abs.
Print Assumptions abs_cos0_quarter.
Print Assumptions sagitta_le_step.
Print Assumptions chord_phi_le_delta.
Print Assumptions scaled_ray_dist.
Print Assumptions chord_local_near.
Print Assumptions signed_offset_span.
Print Assumptions offset_in_unit.
Print Assumptions chord_point_near_arc.
Print Assumptions int_part_nonneg.
Print Assumptions param_bin.
Print Assumptions arc_curve_near_polyline.
Print Assumptions arc_polyline_near_curve.
Print Assumptions arc_linearize_hausdorff.
Print Assumptions arc_linearizes.
