(* ============================================================================
   NetTopologySuite.Proofs.MetricSpeed
   ----------------------------------------------------------------------------
   Generic metric length of a C1 plane curve: the length is the LipInt
   primitive of the speed.

     γ(t) = (gx t, gy t),   γ'(t) = (vx t, vy t),
     speed t = sqrt (vx t² + vy t²),
     is_curve_length γ a b (speedF b − speedF a).

   speedF is lipF of speed on [a, b] (claim 0001-lint-ftc). The chord
   bound is the projection of the increment onto the unit chord: FTC-2
   (lip_ftc + deriv_zero_const on compact subintervals of (a, b), then
   continuity at the endpoints) gives Δγ = ∫ γ', and Cauchy–Schwarz
   bounds the directional derivative by the speed. The least half is the
   same projection onto the unit tangent at the left endpoint, with the
   Lipschitz constant of γ' turning the defect into O(h²). No Heine–Cantor:
   the modulus is the Lipschitz constant. No MVT, no Rolle, no RiemannInt.

   lint_leibniz is not used. It differentiates a parameter under a fixed
   domain [0, 1]. The length here is a variable-limit integral, so the
   primitive's derivative is lip_ftc. Clothoid d/dL stays lint_leibniz
   and is not this letter.

   Deferrals, named:
     * two-sided derivable_pt_lim is assumed on the closed interval
       [a, b], the RealMonotone shape. A curve that is only one-sided
       at its endpoints is applied on a compact subinterval of the open
       domain, where the two-sided hypothesis holds.
     * per-type files (arc, clothoid, NURBS) instantiate this section;
       only the circle smoke is in this letter.
     * an equality-form mean value (Δγ = γ'(c) Δt) is not proved.

   WITNESS topic: metric · claimId: 0001-metric-speed
   · witness: lip_speed_is_curve_length
   board: ADR-0001
   Not a remint of 0001-lint-ftc (that witness is lipint_ftc). Not a
   remint of 508-c (speed_integral_is_curve_length): that pack takes
   uniform continuity, an increment squeeze, and chord-rate tightness
   as premises. This file proves the chord and the rate from a
   Lipschitz derivative.
   No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import Distance LipInt LipIntFTC RealMonotone CurveLength ArcLength ArcRectifiable.
Local Open Scope R_scope.

Lemma abs_lt_all_eq0 :
  forall d : R, (forall eps : R, 0 < eps -> Rabs d < eps) -> d = 0.
Proof.
  intros d H.
  destruct (Req_EM_T d 0) as [->|Hn]; [reflexivity|].
  specialize (H (Rabs d) (Rabs_pos_lt _ Hn)). lra.
Qed.

Lemma derivable_pt_lim_cont :
  forall (f : R -> R) (x l eps : R),
    derivable_pt_lim f x l -> 0 < eps ->
    exists delta : R, 0 < delta /\
      forall h : R, Rabs h < delta -> Rabs (f (x + h) - f x) < eps.
Proof.
  intros f x l eps Hd Heps.
  destruct (Hd 1%R Rlt_0_1) as [d0 Hd0].
  assert (Hdpos : 0 < d0) by apply cond_pos.
  set (B := Rabs l + 1).
  assert (HB : 0 < B).
  { unfold B. apply Rplus_le_lt_0_compat; [apply Rabs_pos | exact Rlt_0_1]. }
  assert (Hstep : 0 < eps / B) by (apply Rdiv_lt_0_compat; assumption).
  set (delta := Rmin d0 (eps / B)).
  assert (Hdelta : 0 < delta) by (apply Rmin_pos; assumption).
  exists delta. split; [exact Hdelta|].
  intros h Hh.
  destruct (Req_EM_T h 0) as [->|Hnz].
  - rewrite Rplus_0_r, Rminus_diag, Rabs_R0. exact Heps.
  - assert (Habsd : Rabs h < d0).
    { eapply Rlt_le_trans; [exact Hh | unfold delta; apply Rmin_l]. }
    assert (HabsB : Rabs h < eps / B).
    { eapply Rlt_le_trans; [exact Hh | unfold delta; apply Rmin_r]. }
    specialize (Hd0 h Hnz Habsd).
    set (q := (f (x + h) - f x) / h).
    assert (Hq : Rabs q < B).
    { unfold q.
      replace ((f (x + h) - f x) / h)
        with (l + ((f (x + h) - f x) / h - l)) by ring.
      eapply Rle_lt_trans; [apply Rabs_triang |].
      unfold B. apply Rplus_lt_compat_l. exact Hd0. }
    assert (E : Rabs (f (x + h) - f x) = Rabs q * Rabs h).
    { unfold q, Rdiv. rewrite Rabs_mult, Rabs_inv.
      rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rabs_no_R0; exact Hnz).
      reflexivity. }
    rewrite E.
    apply Rlt_trans with (B * Rabs h).
    + apply Rmult_lt_compat_r; [apply Rabs_pos_lt; exact Hnz | exact Hq].
    + replace eps with (B * (eps / B)).
      * apply Rmult_lt_compat_l; [exact HB | exact HabsB].
      * unfold Rdiv. field. exact (Rgt_not_eq _ _ HB).
Qed.

Lemma deriv_pt_sub :
  forall (f g : R -> R) (x lf lg : R),
    derivable_pt_lim f x lf ->
    derivable_pt_lim g x lg ->
    derivable_pt_lim (fun z => f z - g z) x (lf - lg).
Proof.
  intros f g x lf lg Hf Hg.
  eapply derivable_pt_lim_ext.
  - intros z. unfold minus_fct. reflexivity.
  - apply derivable_pt_lim_minus; assumption.
Qed.

Lemma sqr_le_nonneg :
  forall x y : R, 0 <= x -> 0 <= y -> x * x <= y * y -> x <= y.
Proof.
  intros x y Hx Hy H.
  rewrite <- (sqrt_square x Hx), <- (sqrt_square y Hy).
  apply sqrt_le_1; [apply Rle_0_sqr | apply Rle_0_sqr | exact H].
Qed.

Lemma dot_le_norms :
  forall a b c d,
    a * c + b * d <= sqrt (a * a + b * b) * sqrt (c * c + d * d).
Proof.
  intros a b c d.
  set (dot := a * c + b * d).
  set (n1 := a * a + b * b).
  set (n2 := c * c + d * d).
  assert (Hn1 : 0 <= n1) by (unfold n1; apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (Hn2 : 0 <= n2) by (unfold n2; apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  destruct (Rle_dec 0 dot) as [Hp|Hn].
  - apply Rle_trans with (sqrt (dot * dot)).
    + rewrite (sqrt_square dot Hp). apply Rle_refl.
    + apply sqr_le_nonneg.
      * apply sqrt_pos.
      * apply Rmult_le_pos; apply sqrt_pos.
      * rewrite (sqrt_sqrt (dot * dot)) by apply Rle_0_sqr.
        replace ((sqrt n1 * sqrt n2) * (sqrt n1 * sqrt n2))
          with ((sqrt n1 * sqrt n1) * (sqrt n2 * sqrt n2)) by ring.
        rewrite (sqrt_sqrt n1 Hn1), (sqrt_sqrt n2 Hn2).
        apply Rminus_le. unfold dot, n1, n2.
        assert (Hs : 0 <= (a * d - b * c) * (a * d - b * c)) by apply Rle_0_sqr.
        apply Ropp_le_contravar in Hs. rewrite Ropp_0 in Hs.
        replace ((a * c + b * d) * (a * c + b * d)
                 - (a * a + b * b) * (c * c + d * d))
          with (- ((a * d - b * c) * (a * d - b * c))) by ring.
        exact Hs.
  - apply Rle_trans with 0.
    + apply Rlt_le, Rnot_le_lt. exact Hn.
    + apply Rmult_le_pos; apply sqrt_pos.
Qed.

Lemma norm_triangle :
  forall x1 y1 x2 y2,
    sqrt (x1 * x1 + y1 * y1) <=
    sqrt ((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2))
    + sqrt (x2 * x2 + y2 * y2).
Proof.
  intros x1 y1 x2 y2.
  set (dx := x1 - x2). set (dy := y1 - y2).
  set (A := sqrt (dx * dx + dy * dy)).
  set (B := sqrt (x2 * x2 + y2 * y2)).
  assert (HA : 0 <= A) by apply sqrt_pos.
  assert (HB : 0 <= B) by apply sqrt_pos.
  apply sqr_le_nonneg.
  - apply sqrt_pos.
  - apply Rplus_le_le_0_compat; assumption.
  - assert (EA : A * A = dx * dx + dy * dy).
    { unfold A. apply sqrt_sqrt. apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
    assert (EB : B * B = x2 * x2 + y2 * y2).
    { unfold B. apply sqrt_sqrt. apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
    assert (Hcs : x2 * dx + y2 * dy <= A * B).
    { replace (x2 * dx + y2 * dy) with (dx * x2 + dy * y2) by ring.
      unfold A, B. apply dot_le_norms. }
    rewrite (sqrt_sqrt (x1 * x1 + y1 * y1))
      by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
    replace (x1 * x1 + y1 * y1)
      with ((x2 + dx) * (x2 + dx) + (y2 + dy) * (y2 + dy)).
    2: { unfold dx, dy. ring. }
    replace ((x2 + dx) * (x2 + dx) + (y2 + dy) * (y2 + dy))
      with (A * A + B * B + 2 * (x2 * dx + y2 * dy)).
    2: { rewrite EA, EB. ring. }
    replace ((A + B) * (A + B)) with (A * A + B * B + 2 * (A * B)) by ring.
    apply Rplus_le_compat_l. apply Rmult_le_compat_l; [lra | exact Hcs].
Qed.

Lemma norm_abs_diff :
  forall x1 y1 x2 y2,
    Rabs (sqrt (x1 * x1 + y1 * y1) - sqrt (x2 * x2 + y2 * y2))
    <= sqrt ((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)).
Proof.
  intros x1 y1 x2 y2.
  apply Rabs_le. split.
  - assert (H := norm_triangle x2 y2 x1 y1).
    replace ((x2 - x1) * (x2 - x1)) with ((x1 - x2) * (x1 - x2)) in H by ring.
    replace ((y2 - y1) * (y2 - y1)) with ((y1 - y2) * (y1 - y2)) in H by ring.
    lra.
  - assert (H := norm_triangle x1 y1 x2 y2). lra.
Qed.

Lemma norm_le_l1 :
  forall dx dy, sqrt (dx * dx + dy * dy) <= Rabs dx + Rabs dy.
Proof.
  intros dx dy.
  apply sqr_le_nonneg.
  - apply sqrt_pos.
  - apply Rplus_le_le_0_compat; apply Rabs_pos.
  - rewrite (sqrt_sqrt (dx * dx + dy * dy))
      by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
    assert (Ex : Rabs dx * Rabs dx = dx * dx).
    { pose proof (Rsqr_abs dx) as H. unfold Rsqr in H. symmetry. exact H. }
    assert (Ey : Rabs dy * Rabs dy = dy * dy).
    { pose proof (Rsqr_abs dy) as H. unfold Rsqr in H. symmetry. exact H. }
    replace ((Rabs dx + Rabs dy) * (Rabs dx + Rabs dy))
      with (Rabs dx * Rabs dx + Rabs dy * Rabs dy + 2 * Rabs dx * Rabs dy) by ring.
    rewrite Ex, Ey.
    assert (Hnn : 0 <= 2 * Rabs dx * Rabs dy).
    { apply Rmult_le_pos.
      - apply Rmult_le_pos; [apply Rlt_le; exact Rlt_0_2 | apply Rabs_pos].
      - apply Rabs_pos. }
    rewrite <- (Rplus_0_r (dx * dx + dy * dy)) at 1.
    apply Rplus_le_compat_l. exact Hnn.
Qed.

Lemma lip_clip_seg :
  forall (f : R -> R) (A B L s t : R)
    (Hlip : forall x y, A <= x <= B -> A <= y <= B ->
              Rabs (f x - f y) <= L * Rabs (x - y)),
    A <= s <= B -> A <= t <= B ->
    forall x y,
      Rmin s t <= x <= Rmax s t ->
      Rmin s t <= y <= Rmax s t ->
      Rabs (f x - f y) <= L * Rabs (x - y).
Proof.
  intros f A B L s t Hlip Hs Ht x y Hx Hy.
  apply Hlip.
  - split.
    + apply Rle_trans with (Rmin s t); [| exact (proj1 Hx)].
      apply Rmin_glb; [exact (proj1 Hs) | exact (proj1 Ht)].
    + apply Rle_trans with (Rmax s t); [exact (proj2 Hx) |].
      apply Rmax_lub; [exact (proj2 Hs) | exact (proj2 Ht)].
  - split.
    + apply Rle_trans with (Rmin s t); [| exact (proj1 Hy)].
      apply Rmin_glb; [exact (proj1 Hs) | exact (proj1 Ht)].
    + apply Rle_trans with (Rmax s t); [exact (proj2 Hy) |].
      apply Rmax_lub; [exact (proj2 Hs) | exact (proj2 Ht)].
Qed.

Lemma int_seg_const :
  forall c L a b (HL : 0 <= L)
    (Hlip : forall x y,
       Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
       Rabs ((fun _ : R => c) x - (fun _ : R => c) y) <= L * Rabs (x - y)),
    a <= b ->
    int_seg (fun _ : R => c) L a b HL Hlip = (b - a) * c.
Proof.
  intros c L a b HL Hlip Hab.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab'|Hn]; [| exfalso; exact (Hn Hab)].
  apply lint_const.
Qed.

Lemma int_seg_mono :
  forall (g h : R -> R) Lg Hg a b
    (HLg : 0 <= Lg) (HHg : 0 <= Hg) Hlipg Hlih,
    a <= b ->
    (forall x, a <= x <= b -> g x <= h x) ->
    int_seg g Lg a b HLg Hlipg <= int_seg h Hg a b HHg Hlih.
Proof.
  intros g h Lg Hg a b HLg HHg Hlipg Hlih Hab Hle.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab'|Hn]; [| exfalso; exact (Hn Hab)].
  apply lint_mono. exact Hle.
Qed.

Lemma const_lip :
  forall (c L a b : R), 0 <= L ->
    forall x y,
      Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
      Rabs ((fun _ : R => c) x - (fun _ : R => c) y) <= L * Rabs (x - y).
Proof.
  intros c L a b HL x y _ _.
  rewrite Rminus_diag, Rabs_R0.
  apply Rmult_le_pos; [exact HL | apply Rabs_pos].
Qed.

Lemma int_seg_nonneg :
  forall (g : R -> R) L a b (HL : 0 <= L) Hlip,
    a <= b ->
    (forall x, a <= x <= b -> 0 <= g x) ->
    0 <= int_seg g L a b HL Hlip.
Proof.
  intros g L a b HL Hlip Hab Hle.
  assert (Hmono : int_seg (fun _ : R => 0) L a b HL (const_lip 0 L a b HL)
                  <= int_seg g L a b HL Hlip).
  { apply int_seg_mono; [exact Hab | exact Hle]. }
  rewrite (int_seg_const 0 L a b HL (const_lip 0 L a b HL) Hab) in Hmono.
  replace ((b - a) * 0) with 0 in Hmono by ring.
  exact Hmono.
Qed.

Lemma rmin3_pos :
  forall x y z, 0 < x -> 0 < y -> 0 < z -> 0 < Rmin x (Rmin y z).
Proof.
  intros x y z Hx Hy Hz.
  apply Rmin_pos; [exact Hx | apply Rmin_pos; assumption].
Qed.

Lemma rmin3_le1 : forall x y z, Rmin x (Rmin y z) <= x.
Proof. intros. apply Rmin_l. Qed.

Lemma rmin3_le2 : forall x y z, Rmin x (Rmin y z) <= y.
Proof. intros. eapply Rle_trans; [apply Rmin_r | apply Rmin_l]. Qed.

Lemma rmin3_le3 : forall x y z, Rmin x (Rmin y z) <= z.
Proof. intros. eapply Rle_trans; [apply Rmin_r | apply Rmin_r]. Qed.

Lemma half_order : forall d, 0 < d -> 0 < d / 2 /\ d / 2 < d.
Proof. intros d Hd. nra. Qed.

Lemma left_shift_le :
  forall a x d, a < x -> 0 < d -> d <= x - a ->
    a < a + d / 2 /\ a + d / 2 <= x.
Proof. intros. nra. Qed.

Lemma both_shift_le :
  forall a b d, a < b -> 0 < d -> d <= b - a ->
    a < a + d / 2 /\ a + d / 2 <= b - d / 2 /\ b - d / 2 < b.
Proof. intros. nra. Qed.

Lemma slack_le_eps :
  forall eps L h,
    0 < eps -> 0 <= L -> 0 <= h -> h < eps / (2 * L + 1) ->
    2 * L * h * h <= eps * h.
Proof.
  intros eps L h Heps HL Hh Hhsmall.
  destruct (Req_EM_T h 0) as [->|Hnz].
  - ring_simplify. apply Rle_refl.
  - assert (Hhpos : 0 < h).
    { apply Rnot_le_lt. intro Hbad. apply Hnz. apply Rle_antisym; assumption. }
    assert (Hden : 0 < 2 * L + 1).
    { apply Rplus_le_lt_0_compat.
      - apply Rmult_le_pos; [apply Rlt_le; exact Rlt_0_2 | exact HL].
      - exact Rlt_0_1. }
    assert (Hlt : h * (2 * L + 1) < eps).
    { apply Rmult_lt_compat_r with (r := 2 * L + 1) in Hhsmall; [| exact Hden].
      replace (eps / (2 * L + 1) * (2 * L + 1)) with eps in Hhsmall
        by (field; exact (Rgt_not_eq _ _ Hden)).
      exact Hhsmall. }
    assert (H2Lh : 2 * L * h < eps).
    { assert (Hsum : 2 * L * h + h < eps).
      { replace (2 * L * h + h) with (h * (2 * L + 1)) by ring. exact Hlt. }
      apply Rlt_trans with (2 * L * h + h); [| exact Hsum].
      rewrite <- (Rplus_0_r (2 * L * h)) at 1.
      apply Rplus_lt_compat_l. exact Hhpos. }
    apply Rmult_le_compat_r; [exact Hh | apply Rlt_le; exact H2Lh].
Qed.

Section C1Speed.
Variables gx gy vx vy : R -> R.
Variables a b Lx Ly : R.
Hypothesis Hab : a <= b.
Hypothesis HLx : 0 <= Lx.
Hypothesis HLy : 0 <= Ly.
Hypothesis Hlipx : forall x y, a <= x <= b -> a <= y <= b ->
  Rabs (vx x - vx y) <= Lx * Rabs (x - y).
Hypothesis Hlipy : forall x y, a <= x <= b -> a <= y <= b ->
  Rabs (vy x - vy y) <= Ly * Rabs (x - y).
Hypothesis Hderx : forall t, a <= t <= b -> derivable_pt_lim gx t (vx t).
Hypothesis Hdery : forall t, a <= t <= b -> derivable_pt_lim gy t (vy t).

Lemma HLs : 0 <= Lx + Ly.
Proof. apply Rplus_le_le_0_compat; assumption. Qed.

Definition gamma (t : R) : Point := mkPoint (gx t) (gy t).

Definition speed (t : R) : R := sqrt (vx t * vx t + vy t * vy t).

Definition Gx (t : R) : R := lipF vx a b Lx HLx Hlipx t.
Definition Gy (t : R) : R := lipF vy a b Ly HLy Hlipy t.

Lemma speed_lip : forall x y, a <= x <= b -> a <= y <= b ->
  Rabs (speed x - speed y) <= (Lx + Ly) * Rabs (x - y).
Proof.
  intros x y Hx Hy.
  eapply Rle_trans; [apply norm_abs_diff|].
  eapply Rle_trans; [apply norm_le_l1|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [apply Hlipx | apply Hlipy]; assumption.
  - right. ring.
Qed.

Definition speedF (t : R) : R := lipF speed a b (Lx + Ly) HLs speed_lip t.

Lemma Gx_at_left : Gx a = 0.
Proof.
  unfold Gx.
  rewrite (lipF_lint vx a b Lx HLx Hlipx a (Rle_refl a) Hab).
  apply lint_point.
Qed.

Lemma Gy_at_left : Gy a = 0.
Proof.
  unfold Gy.
  rewrite (lipF_lint vy a b Ly HLy Hlipy a (Rle_refl a) Hab).
  apply lint_point.
Qed.

Lemma speedF_at_left : speedF a = 0.
Proof.
  unfold speedF.
  rewrite (lipF_lint speed a b (Lx + Ly) HLs speed_lip a (Rle_refl a) Hab).
  apply lint_point.
Qed.

Lemma Gx_deriv : forall t, a < t < b -> derivable_pt_lim Gx t (vx t).
Proof. intros t Ht. unfold Gx. apply lip_ftc. exact Ht. Qed.

Lemma Gy_deriv : forall t, a < t < b -> derivable_pt_lim Gy t (vy t).
Proof. intros t Ht. unfold Gy. apply lip_ftc. exact Ht. Qed.

Lemma Gx_match_open :
  forall p q, a < p -> p <= q -> q < b -> gx q - Gx q = gx p - Gx p.
Proof.
  intros p q Hp Hpq Hq.
  apply (deriv_zero_const (fun z => gx z - Gx z) (fun _ => 0) p q q p).
  - intros t Ht.
    eapply derivable_pt_lim_ext.
    + intros z. unfold minus_fct. reflexivity.
    + replace 0 with (vx t - vx t) by ring.
      apply derivable_pt_lim_minus.
      * apply Hderx. lra.
      * apply Gx_deriv. lra.
  - intros t Ht. reflexivity.
  - lra.
  - lra.
Qed.

Lemma Gy_match_open :
  forall p q, a < p -> p <= q -> q < b -> gy q - Gy q = gy p - Gy p.
Proof.
  intros p q Hp Hpq Hq.
  apply (deriv_zero_const (fun z => gy z - Gy z) (fun _ => 0) p q q p).
  - intros t Ht.
    eapply derivable_pt_lim_ext.
    + intros z. unfold minus_fct. reflexivity.
    + replace 0 with (vy t - vy t) by ring.
      apply derivable_pt_lim_minus.
      * apply Hdery. lra.
      * apply Gy_deriv. lra.
  - intros t Ht. reflexivity.
  - lra.
  - lra.
Qed.

Lemma gx_cont :
  forall x eps, a <= x <= b -> 0 < eps ->
    exists delta, 0 < delta /\
      forall h, Rabs h < delta -> Rabs (gx (x + h) - gx x) < eps.
Proof.
  intros x eps Hx Heps.
  apply derivable_pt_lim_cont with (l := vx x); [apply Hderx; exact Hx | exact Heps].
Qed.

Lemma gy_cont :
  forall x eps, a <= x <= b -> 0 < eps ->
    exists delta, 0 < delta /\
      forall h, Rabs h < delta -> Rabs (gy (x + h) - gy x) < eps.
Proof.
  intros x eps Hx Heps.
  apply derivable_pt_lim_cont with (l := vy x); [apply Hdery; exact Hx | exact Heps].
Qed.

Lemma Gx_cont :
  forall x eps, a <= x <= b -> 0 < eps ->
    exists delta, 0 < delta /\
      forall y, a <= y <= b -> Rabs (y - x) < delta ->
        Rabs (Gx y - Gx x) < eps.
Proof.
  intros x eps Hx Heps. unfold Gx. apply lipF_continuous; assumption.
Qed.

Lemma Gy_cont :
  forall x eps, a <= x <= b -> 0 < eps ->
    exists delta, 0 < delta /\
      forall y, a <= y <= b -> Rabs (y - x) < delta ->
        Rabs (Gy y - Gy x) < eps.
Proof.
  intros x eps Hx Heps. unfold Gy. apply lipF_continuous; assumption.
Qed.

Lemma abs_pair_lt :
  forall A B C D eps,
    Rabs A < eps / 4 -> Rabs B < eps / 4 ->
    Rabs C < eps / 4 -> Rabs D < eps / 4 ->
    Rabs (A - B + (C - D)) < eps.
Proof.
  intros A B C D eps HA HB HC HD.
  eapply Rle_lt_trans; [apply Rabs_triang|].
  eapply Rle_lt_trans.
  - apply Rplus_le_compat; apply Rabs_triang.
  - rewrite !Rabs_Ropp.
    apply Rlt_le_trans with (eps / 4 + eps / 4 + (eps / 4 + eps / 4)).
    + apply Rplus_lt_compat; apply Rplus_lt_compat; assumption.
    + replace (eps / 4 + eps / 4 + (eps / 4 + eps / 4)) with eps by field.
      apply Rle_refl.
Qed.

Lemma coord_Gx_closed : forall x, a <= x <= b -> gx x - gx a = Gx x.
Proof.
  intros x Hx.
  assert (Heq : gx x - Gx x = gx a - Gx a); [| rewrite Gx_at_left in Heq; lra].
  destruct (Req_EM_T x a) as [->|Hxa]; [reflexivity|].
  assert (Hax : a < x) by lra.
  apply Rminus_diag_uniq. apply abs_lt_all_eq0. intros eps Heps.
  assert (H4 : 0 < eps / 4) by nra.
  destruct (gx_cont a (eps / 4) (conj (Rle_refl a) Hab) H4) as [dg [Hdg Hg]].
  destruct (Gx_cont a (eps / 4) (conj (Rle_refl a) Hab) H4) as [dG [HdG HG]].
  destruct (Rle_lt_dec b x) as [Hbx|Hxb].
  - assert (Exb : x = b) by lra. subst x.
    assert (Hablt : a < b) by lra.
    destruct (gx_cont b (eps / 4) (conj Hab (Rle_refl b)) H4) as [dg2 [Hdg2 Hg2]].
    destruct (Gx_cont b (eps / 4) (conj Hab (Rle_refl b)) H4) as [dG2 [HdG2 HG2]].
    set (d := Rmin (Rmin dg dG) (Rmin (Rmin dg2 dG2) (b - a))).
    assert (Hd : 0 < d).
    { apply Rmin_pos; [apply Rmin_pos; assumption |].
      apply Rmin_pos; [apply Rmin_pos; assumption | lra]. }
    assert (Hd_le : d <= b - a).
    { eapply Rle_trans; [apply Rmin_r | apply Rmin_r]. }
    assert (Hd_dg : d <= dg).
    { eapply Rle_trans; [apply Rmin_l | apply Rmin_l]. }
    assert (Hd_dG : d <= dG).
    { eapply Rle_trans; [apply Rmin_l | apply Rmin_r]. }
    assert (Hd_dg2 : d <= dg2).
    { eapply Rle_trans; [apply Rmin_r | eapply Rle_trans; [apply Rmin_l | apply Rmin_l]]. }
    assert (Hd_dG2 : d <= dG2).
    { eapply Rle_trans; [apply Rmin_r | eapply Rle_trans; [apply Rmin_l | apply Rmin_r]]. }
    destruct (half_order d Hd) as [Hhalf Hhalflt].
    destruct (both_shift_le a b d Hablt Hd Hd_le) as [Hpgt [Hpq Hqlt]].
    set (p := a + d / 2). set (q := b - d / 2).
    assert (Hmatch : gx q - Gx q = gx p - Gx p).
    { apply Gx_match_open.
      - unfold p. exact Hpgt.
      - unfold p, q. exact Hpq.
      - unfold q. exact Hqlt. }
    assert (Hnn : 0 <= d / 2) by (apply Rlt_le; exact Hhalf).
    assert (Hgp : Rabs (gx p - gx a) < eps / 4).
    { assert (Ep : a + (p - a) = p) by (unfold p; ring).
      rewrite <- Ep. apply Hg.
      replace (p - a) with (d / 2) by (unfold p; ring).
      rewrite (Rabs_pos_eq (d / 2) Hnn).
      eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dg]. }
    assert (HGp : Rabs (Gx p - Gx a) < eps / 4).
    { apply HG.
      - split.
        + apply Rlt_le. unfold p. exact Hpgt.
        + apply Rle_trans with q; [unfold p, q; exact Hpq |].
          apply Rle_trans with b; [apply Rlt_le; unfold q; exact Hqlt | apply Rle_refl].
      - replace (p - a) with (d / 2) by (unfold p; ring).
        rewrite (Rabs_pos_eq (d / 2) Hnn).
        eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dG]. }
    assert (Hgq : Rabs (gx b - gx q) < eps / 4).
    { rewrite Rabs_minus_sym.
      assert (Eq : b + (q - b) = q) by (unfold q; ring).
      rewrite <- Eq. apply Hg2.
      replace (q - b) with (- (d / 2)) by (unfold q; ring).
      rewrite Rabs_Ropp, (Rabs_pos_eq (d / 2) Hnn).
      eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dg2]. }
    assert (HGq : Rabs (Gx b - Gx q) < eps / 4).
    { rewrite Rabs_minus_sym. apply HG2.
      - split.
        + apply Rle_trans with p; [apply Rlt_le; unfold p; exact Hpgt | unfold p, q; exact Hpq].
        + apply Rlt_le. unfold q. exact Hqlt.
      - replace (q - b) with (- (d / 2)) by (unfold q; ring).
        rewrite Rabs_Ropp, (Rabs_pos_eq (d / 2) Hnn).
        eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dG2]. }
    replace ((gx b - Gx b) - (gx a - Gx a))
      with (((gx b - gx q) - (Gx b - Gx q)) + ((gx p - gx a) - (Gx p - Gx a))).
    + apply abs_pair_lt; assumption.
    + set (gp := gx p). set (Gp := Gx p).
      set (gq := gx q). set (Gq := Gx q).
      set (gb := gx b). set (Gb := Gx b).
      set (ga := gx a). set (Ga := Gx a).
      assert (E : gp - Gp = gq - Gq).
      { unfold gp, Gp, gq, Gq. symmetry. exact Hmatch. }
      apply (Rplus_eq_compat_l Gp) in E.
      replace (Gp + (gp - Gp)) with gp in E by ring.
      rewrite E. ring.
  - set (d := Rmin dg (Rmin dG (x - a))).
    assert (Hd : 0 < d) by (apply rmin3_pos; lra).
    assert (Hd_dg : d <= dg) by apply rmin3_le1.
    assert (Hd_dG : d <= dG) by apply rmin3_le2.
    assert (Hd_x : d <= x - a) by apply rmin3_le3.
    destruct (half_order d Hd) as [Hhalf Hhalflt].
    destruct (left_shift_le a x d Hax Hd Hd_x) as [Hpgt Hpx].
    set (p := a + d / 2).
    assert (Hnn : 0 <= d / 2) by (apply Rlt_le; exact Hhalf).
    assert (Hmatch : gx x - Gx x = gx p - Gx p).
    { apply Gx_match_open.
      - unfold p. exact Hpgt.
      - unfold p. exact Hpx.
      - exact Hxb. }
    assert (Hgp : Rabs (gx p - gx a) < eps / 4).
    { assert (Ep : a + (p - a) = p) by (unfold p; ring).
      rewrite <- Ep. apply Hg.
      replace (p - a) with (d / 2) by (unfold p; ring).
      rewrite (Rabs_pos_eq (d / 2) Hnn).
      eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dg]. }
    assert (HGp : Rabs (Gx p - Gx a) < eps / 4).
    { apply HG.
      - split; [apply Rlt_le; unfold p; exact Hpgt |].
        apply Rle_trans with x; [unfold p; exact Hpx | exact (proj2 Hx)].
      - replace (p - a) with (d / 2) by (unfold p; ring).
        rewrite (Rabs_pos_eq (d / 2) Hnn).
        eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dG]. }
    replace ((gx x - Gx x) - (gx a - Gx a))
      with ((gx p - gx a) - (Gx p - Gx a)).
    + eapply Rle_lt_trans; [apply Rabs_triang|].
      rewrite Rabs_Ropp.
      apply Rlt_trans with (eps / 4 + eps / 4).
      * apply Rplus_lt_compat; assumption.
      * replace (eps / 4 + eps / 4) with (eps / 2) by field.
        assert (Hhalfeps : eps / 2 < eps) by nra.
        exact Hhalfeps.
    + rewrite Hmatch. ring.
Qed.

Lemma coord_Gy_closed : forall x, a <= x <= b -> gy x - gy a = Gy x.
Proof.
  intros x Hx.
  assert (Heq : gy x - Gy x = gy a - Gy a); [| rewrite Gy_at_left in Heq; lra].
  destruct (Req_EM_T x a) as [->|Hxa]; [reflexivity|].
  assert (Hax : a < x) by lra.
  apply Rminus_diag_uniq. apply abs_lt_all_eq0. intros eps Heps.
  assert (H4 : 0 < eps / 4) by nra.
  destruct (gy_cont a (eps / 4) (conj (Rle_refl a) Hab) H4) as [dg [Hdg Hg]].
  destruct (Gy_cont a (eps / 4) (conj (Rle_refl a) Hab) H4) as [dG [HdG HG]].
  destruct (Rle_lt_dec b x) as [Hbx|Hxb].
  - assert (Exb : x = b) by lra. subst x.
    assert (Hablt : a < b) by lra.
    destruct (gy_cont b (eps / 4) (conj Hab (Rle_refl b)) H4) as [dg2 [Hdg2 Hg2]].
    destruct (Gy_cont b (eps / 4) (conj Hab (Rle_refl b)) H4) as [dG2 [HdG2 HG2]].
    set (d := Rmin (Rmin dg dG) (Rmin (Rmin dg2 dG2) (b - a))).
    assert (Hd : 0 < d).
    { apply Rmin_pos; [apply Rmin_pos; assumption |].
      apply Rmin_pos; [apply Rmin_pos; assumption | lra]. }
    assert (Hd_le : d <= b - a).
    { eapply Rle_trans; [apply Rmin_r | apply Rmin_r]. }
    assert (Hd_dg : d <= dg).
    { eapply Rle_trans; [apply Rmin_l | apply Rmin_l]. }
    assert (Hd_dG : d <= dG).
    { eapply Rle_trans; [apply Rmin_l | apply Rmin_r]. }
    assert (Hd_dg2 : d <= dg2).
    { eapply Rle_trans; [apply Rmin_r | eapply Rle_trans; [apply Rmin_l | apply Rmin_l]]. }
    assert (Hd_dG2 : d <= dG2).
    { eapply Rle_trans; [apply Rmin_r | eapply Rle_trans; [apply Rmin_l | apply Rmin_r]]. }
    destruct (half_order d Hd) as [Hhalf Hhalflt].
    destruct (both_shift_le a b d Hablt Hd Hd_le) as [Hpgt [Hpq Hqlt]].
    set (p := a + d / 2). set (q := b - d / 2).
    assert (Hmatch : gy q - Gy q = gy p - Gy p).
    { apply Gy_match_open.
      - unfold p. exact Hpgt.
      - unfold p, q. exact Hpq.
      - unfold q. exact Hqlt. }
    assert (Hnn : 0 <= d / 2) by (apply Rlt_le; exact Hhalf).
    assert (Hgp : Rabs (gy p - gy a) < eps / 4).
    { assert (Ep : a + (p - a) = p) by (unfold p; ring).
      rewrite <- Ep. apply Hg.
      replace (p - a) with (d / 2) by (unfold p; ring).
      rewrite (Rabs_pos_eq (d / 2) Hnn).
      eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dg]. }
    assert (HGp : Rabs (Gy p - Gy a) < eps / 4).
    { apply HG.
      - split.
        + apply Rlt_le. unfold p. exact Hpgt.
        + apply Rle_trans with q; [unfold p, q; exact Hpq |].
          apply Rle_trans with b; [apply Rlt_le; unfold q; exact Hqlt | apply Rle_refl].
      - replace (p - a) with (d / 2) by (unfold p; ring).
        rewrite (Rabs_pos_eq (d / 2) Hnn).
        eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dG]. }
    assert (Hgq : Rabs (gy b - gy q) < eps / 4).
    { rewrite Rabs_minus_sym.
      assert (Eq : b + (q - b) = q) by (unfold q; ring).
      rewrite <- Eq. apply Hg2.
      replace (q - b) with (- (d / 2)) by (unfold q; ring).
      rewrite Rabs_Ropp, (Rabs_pos_eq (d / 2) Hnn).
      eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dg2]. }
    assert (HGq : Rabs (Gy b - Gy q) < eps / 4).
    { rewrite Rabs_minus_sym. apply HG2.
      - split.
        + apply Rle_trans with p; [apply Rlt_le; unfold p; exact Hpgt | unfold p, q; exact Hpq].
        + apply Rlt_le. unfold q. exact Hqlt.
      - replace (q - b) with (- (d / 2)) by (unfold q; ring).
        rewrite Rabs_Ropp, (Rabs_pos_eq (d / 2) Hnn).
        eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dG2]. }
    replace ((gy b - Gy b) - (gy a - Gy a))
      with (((gy b - gy q) - (Gy b - Gy q)) + ((gy p - gy a) - (Gy p - Gy a))).
    + apply abs_pair_lt; assumption.
    + set (gp := gy p). set (Gp := Gy p).
      set (gq := gy q). set (Gq := Gy q).
      set (gb := gy b). set (Gb := Gy b).
      set (ga := gy a). set (Ga := Gy a).
      assert (E : gp - Gp = gq - Gq).
      { unfold gp, Gp, gq, Gq. symmetry. exact Hmatch. }
      apply (Rplus_eq_compat_l Gp) in E.
      replace (Gp + (gp - Gp)) with gp in E by ring.
      rewrite E. ring.
  - set (d := Rmin dg (Rmin dG (x - a))).
    assert (Hd : 0 < d) by (apply rmin3_pos; lra).
    assert (Hd_dg : d <= dg) by apply rmin3_le1.
    assert (Hd_dG : d <= dG) by apply rmin3_le2.
    assert (Hd_x : d <= x - a) by apply rmin3_le3.
    destruct (half_order d Hd) as [Hhalf Hhalflt].
    destruct (left_shift_le a x d Hax Hd Hd_x) as [Hpgt Hpx].
    set (p := a + d / 2).
    assert (Hnn : 0 <= d / 2) by (apply Rlt_le; exact Hhalf).
    assert (Hmatch : gy x - Gy x = gy p - Gy p).
    { apply Gy_match_open.
      - unfold p. exact Hpgt.
      - unfold p. exact Hpx.
      - exact Hxb. }
    assert (Hgp : Rabs (gy p - gy a) < eps / 4).
    { assert (Ep : a + (p - a) = p) by (unfold p; ring).
      rewrite <- Ep. apply Hg.
      replace (p - a) with (d / 2) by (unfold p; ring).
      rewrite (Rabs_pos_eq (d / 2) Hnn).
      eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dg]. }
    assert (HGp : Rabs (Gy p - Gy a) < eps / 4).
    { apply HG.
      - split; [apply Rlt_le; unfold p; exact Hpgt |].
        apply Rle_trans with x; [unfold p; exact Hpx | exact (proj2 Hx)].
      - replace (p - a) with (d / 2) by (unfold p; ring).
        rewrite (Rabs_pos_eq (d / 2) Hnn).
        eapply Rlt_le_trans; [exact Hhalflt | exact Hd_dG]. }
    replace ((gy x - Gy x) - (gy a - Gy a))
      with ((gy p - gy a) - (Gy p - Gy a)).
    + eapply Rle_lt_trans; [apply Rabs_triang|].
      rewrite Rabs_Ropp.
      apply Rlt_trans with (eps / 4 + eps / 4).
      * apply Rplus_lt_compat; assumption.
      * replace (eps / 4 + eps / 4) with (eps / 2) by field.
        assert (Hhalfeps : eps / 2 < eps) by nra.
        exact Hhalfeps.
    + rewrite Hmatch. ring.
Qed.

Lemma Gx_diff_seg :
  forall s t (Hs : a <= s <= b) (Ht : a <= t <= b), s <= t ->
    Gx t - Gx s =
    int_seg vx Lx s t HLx (lip_clip_seg vx a b Lx s t Hlipx Hs Ht).
Proof.
  intros s t Hs Ht Hst.
  unfold Gx.
  rewrite <- (lipPrim_chasles vx a b Lx HLx Hlipx s t Hs Ht).
  rewrite (lipPrim_as_seg vx a b Lx HLx Hlipx s t Hs Ht).
  apply int_seg_pi.
Qed.

Lemma Gy_diff_seg :
  forall s t (Hs : a <= s <= b) (Ht : a <= t <= b), s <= t ->
    Gy t - Gy s =
    int_seg vy Ly s t HLy (lip_clip_seg vy a b Ly s t Hlipy Hs Ht).
Proof.
  intros s t Hs Ht Hst.
  unfold Gy.
  rewrite <- (lipPrim_chasles vy a b Ly HLy Hlipy s t Hs Ht).
  rewrite (lipPrim_as_seg vy a b Ly HLy Hlipy s t Hs Ht).
  apply int_seg_pi.
Qed.

Lemma coord_x_increment :
  forall s t, a <= s -> s <= t -> t <= b -> gx t - gx s = Gx t - Gx s.
Proof.
  intros s t Hs Hst Ht.
  assert (Exs := coord_Gx_closed s (conj Hs (Rle_trans s t b Hst Ht))).
  assert (Ext := coord_Gx_closed t (conj (Rle_trans a s t Hs Hst) Ht)).
  lra.
Qed.

Lemma coord_y_increment :
  forall s t, a <= s -> s <= t -> t <= b -> gy t - gy s = Gy t - Gy s.
Proof.
  intros s t Hs Hst Ht.
  assert (Eys := coord_Gy_closed s (conj Hs (Rle_trans s t b Hst Ht))).
  assert (Eyt := coord_Gy_closed t (conj (Rle_trans a s t Hs Hst) Ht)).
  lra.
Qed.

Lemma speedF_diff :
  forall s t (Hs : a <= s <= b) (Ht : a <= t <= b), s <= t ->
    speedF t - speedF s =
    int_seg speed (Lx + Ly) s t HLs
      (lip_clip_seg speed a b (Lx + Ly) s t speed_lip Hs Ht).
Proof.
  intros s t Hs Ht Hst.
  unfold speedF.
  rewrite <- (lipPrim_chasles speed a b (Lx + Ly) HLs speed_lip s t Hs Ht).
  rewrite (lipPrim_as_seg speed a b (Lx + Ly) HLs speed_lip s t Hs Ht).
  apply int_seg_pi.
Qed.

Lemma scale_vx_on :
  forall c s t (Hs : a <= s <= b) (Ht : a <= t <= b) (Hc : Rabs c <= 1) x y,
    Rmin s t <= x <= Rmax s t -> Rmin s t <= y <= Rmax s t ->
    Rabs (c * vx x - c * vx y) <= Lx * Rabs (x - y).
Proof.
  intros c s t Hs Ht Hc x y Hx Hy.
  replace (c * vx x - c * vx y) with (c * (vx x - vx y)) by ring.
  rewrite Rabs_mult.
  assert (Hvx := lip_clip_seg vx a b Lx s t Hlipx Hs Ht x y Hx Hy).
  assert (H1 : Rabs c * Rabs (vx x - vx y) <= 1 * Rabs (vx x - vx y)).
  { apply Rmult_le_compat_r; [apply Rabs_pos | exact Hc]. }
  rewrite Rmult_1_l in H1.
  eapply Rle_trans; [exact H1 | exact Hvx].
Qed.

Lemma scale_vy_on :
  forall c s t (Hs : a <= s <= b) (Ht : a <= t <= b) (Hc : Rabs c <= 1) x y,
    Rmin s t <= x <= Rmax s t -> Rmin s t <= y <= Rmax s t ->
    Rabs (c * vy x - c * vy y) <= Ly * Rabs (x - y).
Proof.
  intros c s t Hs Ht Hc x y Hx Hy.
  replace (c * vy x - c * vy y) with (c * (vy x - vy y)) by ring.
  rewrite Rabs_mult.
  assert (Hvy := lip_clip_seg vy a b Ly s t Hlipy Hs Ht x y Hx Hy).
  assert (H1 : Rabs c * Rabs (vy x - vy y) <= 1 * Rabs (vy x - vy y)).
  { apply Rmult_le_compat_r; [apply Rabs_pos | exact Hc]. }
  rewrite Rmult_1_l in H1.
  eapply Rle_trans; [exact H1 | exact Hvy].
Qed.

Lemma dir_on :
  forall c1 c2 s t (Hs : a <= s <= b) (Ht : a <= t <= b)
    (Hc1 : Rabs c1 <= 1) (Hc2 : Rabs c2 <= 1) x y,
    Rmin s t <= x <= Rmax s t -> Rmin s t <= y <= Rmax s t ->
    Rabs ((c1 * vx x + c2 * vy x) - (c1 * vx y + c2 * vy y))
      <= (Lx + Ly) * Rabs (x - y).
Proof.
  intros c1 c2 s t Hs Ht Hc1 Hc2 x y Hx Hy.
  replace ((c1 * vx x + c2 * vy x) - (c1 * vx y + c2 * vy y))
    with ((c1 * vx x - c1 * vx y) + (c2 * vy x - c2 * vy y)) by ring.
  eapply Rle_trans; [apply Rabs_triang |].
  eapply Rle_trans.
  - apply Rplus_le_compat.
    + apply (scale_vx_on c1 s t Hs Ht Hc1 x y Hx Hy).
    + apply (scale_vy_on c2 s t Hs Ht Hc2 x y Hx Hy).
  - replace (Lx * Rabs (x - y) + Ly * Rabs (x - y))
      with ((Lx + Ly) * Rabs (x - y)) by ring.
    apply Rle_refl.
Qed.

Lemma abs_le_1_of_unit :
  forall u v, u * u + v * v = 1 -> Rabs u <= 1 /\ Rabs v <= 1.
Proof.
  intros u v H.
  assert (Hu : u * u <= 1).
  { assert (0 <= v * v) by apply Rle_0_sqr. lra. }
  assert (Hv : v * v <= 1).
  { assert (0 <= u * u) by apply Rle_0_sqr. lra. }
  split.
  - apply sqr_le_nonneg; [apply Rabs_pos | apply Rle_0_1 |].
    assert (Eabs : Rabs u * Rabs u = u * u).
    { pose proof (Rsqr_abs u) as E. unfold Rsqr in E. symmetry. exact E. }
    rewrite Eabs. replace (1 * 1) with 1 by ring. exact Hu.
  - apply sqr_le_nonneg; [apply Rabs_pos | apply Rle_0_1 |].
    assert (Eabs : Rabs v * Rabs v = v * v).
    { pose proof (Rsqr_abs v) as E. unfold Rsqr in E. symmetry. exact E. }
    rewrite Eabs. replace (1 * 1) with 1 by ring. exact Hv.
Qed.

Lemma int_affine :
  forall s t c1 c2
    (Hs : a <= s <= b) (Ht : a <= t <= b)
    (Hc1 : Rabs c1 <= 1) (Hc2 : Rabs c2 <= 1),
    s <= t ->
    int_seg (fun u => c1 * vx u + c2 * vy u) (Lx + Ly) s t HLs
      (dir_on c1 c2 s t Hs Ht Hc1 Hc2)
    = c1 * (gx t - gx s) + c2 * (gy t - gy s).
Proof.
  intros s t c1 c2 Hs Ht Hc1 Hc2 Hst.
  assert (Ex : gx t - gx s =
            int_seg vx Lx s t HLx (lip_clip_seg vx a b Lx s t Hlipx Hs Ht)).
  { rewrite (coord_x_increment s t (proj1 Hs) Hst (proj2 Ht)).
    apply (Gx_diff_seg s t Hs Ht Hst). }
  assert (Ey : gy t - gy s =
            int_seg vy Ly s t HLy (lip_clip_seg vy a b Ly s t Hlipy Hs Ht)).
  { rewrite (coord_y_increment s t (proj1 Hs) Hst (proj2 Ht)).
    apply (Gy_diff_seg s t Hs Ht Hst). }
  rewrite Ex, Ey.
  rewrite <- (int_seg_scal vx c1 Lx Lx s t HLx HLx
                (lip_clip_seg vx a b Lx s t Hlipx Hs Ht)
                (scale_vx_on c1 s t Hs Ht Hc1)).
  rewrite <- (int_seg_scal vy c2 Ly Ly s t HLy HLy
                (lip_clip_seg vy a b Ly s t Hlipy Hs Ht)
                (scale_vy_on c2 s t Hs Ht Hc2)).
  rewrite <- (int_seg_plus
                (fun u => c1 * vx u) (fun u => c2 * vy u)
                Lx Ly (Lx + Ly) s t
                HLx (scale_vx_on c1 s t Hs Ht Hc1)
                HLy (scale_vy_on c2 s t Hs Ht Hc2)
                HLs (dir_on c1 c2 s t Hs Ht Hc1 Hc2)).
  reflexivity.
Qed.

Lemma speed_ge_dir :
  forall c1 c2 u, c1 * c1 + c2 * c2 = 1 ->
    c1 * vx u + c2 * vy u <= speed u.
Proof.
  intros c1 c2 u Hu.
  unfold speed.
  assert (H := dot_le_norms c1 c2 (vx u) (vy u)).
  replace (sqrt (c1 * c1 + c2 * c2)) with 1 in H.
  - rewrite Rmult_1_l in H. exact H.
  - rewrite Hu. symmetry. exact sqrt_1.
Qed.

Lemma chord_le_speed :
  forall s t, a <= s -> s <= t -> t <= b ->
    dist (gamma s) (gamma t) <= speedF t - speedF s.
Proof.
  intros s t Hs Hst Ht.
  assert (Hs' : a <= s <= b).
  { split; [exact Hs | apply Rle_trans with t; assumption]. }
  assert (Ht' : a <= t <= b).
  { split; [apply Rle_trans with s; assumption | exact Ht]. }
  rewrite (speedF_diff s t Hs' Ht' Hst).
  set (d := dist (gamma s) (gamma t)).
  destruct (Req_EM_T d 0) as [Hz|Hnz].
  - rewrite Hz. apply int_seg_nonneg; [exact Hst |].
    intros u _. unfold speed. apply sqrt_pos.
  - assert (Hdpos : 0 < d).
    { apply Rnot_le_lt. intro Hle. apply Hnz.
      apply Rle_antisym; [exact Hle | unfold d; apply dist_nonneg]. }
    set (dx := gx t - gx s). set (dy := gy t - gy s).
    assert (Hsq : d * d = dx * dx + dy * dy).
    { unfold d. rewrite dist_mul_self.
      unfold dx, dy, gamma, dist_sq. simpl. ring. }
    set (ux := dx / d). set (uy := dy / d).
    assert (Hden : d <> 0) by (apply Rgt_not_eq; exact Hdpos).
    assert (Hunit : ux * ux + uy * uy = 1).
    { unfold ux, uy.
      replace (dx / d * (dx / d) + dy / d * (dy / d))
        with ((dx * dx + dy * dy) / (d * d)) by (field; exact Hden).
      rewrite <- Hsq. field. exact Hden. }
    assert (Hdot : ux * dx + uy * dy = d).
    { unfold ux, uy.
      replace (dx / d * dx + dy / d * dy)
        with ((dx * dx + dy * dy) / d) by (field; exact Hden).
      rewrite <- Hsq. field. exact Hden. }
    destruct (abs_le_1_of_unit ux uy Hunit) as [Hux Huy].
    assert (Eaff := int_affine s t ux uy Hs' Ht' Hux Huy Hst).
    unfold dx, dy in *.
    assert (Hmono :
        int_seg (fun u => ux * vx u + uy * vy u) (Lx + Ly) s t HLs
          (dir_on ux uy s t Hs' Ht' Hux Huy)
        <= int_seg speed (Lx + Ly) s t HLs
          (lip_clip_seg speed a b (Lx + Ly) s t speed_lip Hs' Ht')).
    { apply int_seg_mono; [exact Hst |].
      intros u Hu. apply speed_ge_dir. exact Hunit. }
    rewrite <- Hdot. rewrite <- Eaff. exact Hmono.
Qed.

Lemma neg_of_abs :
  forall z M, Rabs z <= M -> - M <= z.
Proof.
  intros z M HM.
  apply Rle_trans with (- Rabs z).
  - apply Ropp_le_contravar. exact HM.
  - destruct (Rle_dec 0 z) as [Hp|Hn].
    + rewrite (Rabs_pos_eq z Hp). lra.
    + assert (Hz : z <= 0) by (apply Rlt_le, Rnot_le_lt; exact Hn).
      rewrite (Rabs_left1 z Hz). lra.
Qed.

Lemma speed_tight :
  forall eps, 0 < eps ->
    exists delta, 0 < delta /\
      forall s t, a <= s -> s <= t -> t <= b -> t - s < delta ->
        speedF t - speedF s - dist (gamma s) (gamma t) <= eps * (t - s).
Proof.
  intros eps Heps.
  set (Ls := Lx + Ly).
  set (delta := eps / (2 * Ls + 1)).
  assert (Hden : 0 < 2 * Ls + 1).
  { apply Rplus_le_lt_0_compat.
    - unfold Ls. apply Rmult_le_pos; [apply Rlt_le; exact Rlt_0_2 | exact HLs].
    - exact Rlt_0_1. }
  assert (Hdlt : 0 < delta).
  { unfold delta. apply Rdiv_lt_0_compat; assumption. }
  exists delta. split; [exact Hdlt |].
  intros s t Hs Hst Ht Hgap.
  set (h := t - s).
  assert (Hh : 0 <= h) by (unfold h; lra).
  assert (Hsmall : h < delta) by (unfold h; exact Hgap).
  assert (Hs' : a <= s <= b).
  { split; [exact Hs | apply Rle_trans with t; assumption]. }
  assert (Ht' : a <= t <= b).
  { split; [apply Rle_trans with s; assumption | exact Ht]. }
  rewrite (speedF_diff s t Hs' Ht' Hst).
  assert (Hslack : 2 * Ls * h * h <= eps * h).
  { apply slack_le_eps; [exact Heps | unfold Ls; exact HLs | exact Hh |].
    unfold delta in Hsmall. exact Hsmall. }
  destruct (Req_EM_T h 0) as [Hz|Hnz].
  - assert (Est : s = t) by (unfold h in Hz; lra). subst t.
    replace (dist (gamma s) (gamma s)) with 0 by (symmetry; apply dist_refl).
    rewrite int_seg_point. rewrite Hz.
    replace (eps * 0) with 0 by ring.
    replace (0 - 0) with 0 by ring.
    apply Rle_refl.
  - set (sig := speed s).
    assert (Hup : forall u, s <= u <= t -> speed u <= sig + Ls * h).
    { intros u Hu.
      assert (Hlip := speed_lip u s
                 (conj (Rle_trans a s u Hs (proj1 Hu))
                       (Rle_trans u t b (proj2 Hu) Ht)) Hs').
      assert (Hdiff : speed u - sig <= Ls * Rabs (u - s)).
      { unfold sig. eapply Rle_trans; [apply Rle_abs | exact Hlip]. }
      assert (Hun : 0 <= u - s) by lra.
      rewrite (Rabs_pos_eq (u - s) Hun) in Hdiff.
      assert (Huh : u - s <= h) by (unfold h; lra).
      assert (Hscale : Ls * (u - s) <= Ls * h).
      { apply Rmult_le_compat_l; [unfold Ls; exact HLs | exact Huh]. }
      unfold Ls in *. lra. }
    assert (Hint_up :
        int_seg speed Ls s t HLs
          (lip_clip_seg speed a b Ls s t speed_lip Hs' Ht')
        <= (sig + Ls * h) * h).
    { assert (Hc : int_seg (fun _ : R => sig + Ls * h) Ls s t HLs
                     (const_lip (sig + Ls * h) Ls s t HLs)
                   = h * (sig + Ls * h)).
      { rewrite (int_seg_const (sig + Ls * h) Ls s t HLs
                  (const_lip (sig + Ls * h) Ls s t HLs) Hst).
        unfold h. ring. }
      rewrite Rmult_comm.
      rewrite <- Hc.
      apply int_seg_mono; [exact Hst |].
      intros u Hu. apply Hup. exact Hu. }
    destruct (Req_EM_T sig 0) as [Hzero|Hnzs].
    + assert (Hdist : 0 <= dist (gamma s) (gamma t)) by apply dist_nonneg.
      assert (Hint_le : int_seg speed Ls s t HLs
                 (lip_clip_seg speed a b Ls s t speed_lip Hs' Ht')
               <= Ls * h * h).
      { eapply Rle_trans; [exact Hint_up |]. rewrite Hzero. unfold Ls. nra. }
      assert (Hnegd : - dist (gamma s) (gamma t) <= 0).
      { rewrite <- Ropp_0. apply Ropp_le_contravar. exact Hdist. }
      assert (Hsum : int_seg speed Ls s t HLs
                 (lip_clip_seg speed a b Ls s t speed_lip Hs' Ht')
                 - dist (gamma s) (gamma t) <= Ls * h * h).
      { eapply Rle_trans.
        - apply Rplus_le_compat; [exact Hint_le | exact Hnegd].
        - rewrite Rplus_0_r. apply Rle_refl. }
      eapply Rle_trans; [exact Hsum |].
      eapply Rle_trans; [| exact Hslack].
      rewrite <- (Rplus_0_r (Ls * h * h)) at 1.
      replace (2 * Ls * h * h) with (Ls * h * h + Ls * h * h) by ring.
      apply Rplus_le_compat_l.
      apply Rmult_le_pos; [apply Rmult_le_pos; [unfold Ls; exact HLs | exact Hh] | exact Hh].
    + assert (Hsig : 0 < sig).
      { apply Rnot_le_lt. intro Hle. apply Hnzs.
        apply Rle_antisym; [exact Hle | unfold sig, speed; apply sqrt_pos]. }
      set (ux := vx s / sig). set (uy := vy s / sig).
      assert (Hunit : ux * ux + uy * uy = 1).
      { unfold ux, uy.
        assert (Hsq : vx s * vx s + vy s * vy s = sig * sig).
        { symmetry. unfold sig, speed. apply sqrt_sqrt.
          apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
        assert (Hnzsig : sig <> 0) by (apply Rgt_not_eq; exact Hsig).
        replace (vx s / sig * (vx s / sig) + vy s / sig * (vy s / sig))
          with ((vx s * vx s + vy s * vy s) / (sig * sig))
          by (field; exact Hnzsig).
        rewrite Hsq. field. exact Hnzsig. }
      destruct (abs_le_1_of_unit ux uy Hunit) as [Hux Huy].
      assert (E0 : ux * vx s + uy * vy s = sig).
      { unfold ux, uy.
        assert (Hnzsig : sig <> 0) by (apply Rgt_not_eq; exact Hsig).
        replace (vx s / sig * vx s + vy s / sig * vy s)
          with ((vx s * vx s + vy s * vy s) / sig) by (field; exact Hnzsig).
        assert (Hsq : vx s * vx s + vy s * vy s = sig * sig).
        { symmetry. unfold sig, speed. apply sqrt_sqrt.
          apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
        rewrite Hsq. field. exact Hnzsig. }
      assert (Hlow_pt : forall u, s <= u <= t ->
                 sig - Ls * h <= ux * vx u + uy * vy u).
      { intros u Hu.
        assert (Herr := dir_on ux uy s t Hs' Ht' Hux Huy u s).
        assert (Hus : Rmin s t <= u <= Rmax s t).
        { split.
          - eapply Rle_trans; [apply Rmin_l | exact (proj1 Hu)].
          - eapply Rle_trans; [exact (proj2 Hu) | apply Rmax_r]. }
        assert (Hss : Rmin s t <= s <= Rmax s t).
        { split; [apply Rmin_l | apply Rmax_l]. }
        specialize (Herr Hus Hss).
        rewrite E0 in Herr.
        assert (Hstep : Rabs (u - s) <= h).
        { rewrite (Rabs_pos_eq (u - s)) by lra. unfold h. lra. }
        assert (Hbound : Rabs ((ux * vx u + uy * vy u) - sig) <= Ls * h).
        { eapply Rle_trans; [exact Herr |].
          apply Rmult_le_compat_l; [unfold Ls; exact HLs | exact Hstep]. }
        assert (Hneg := neg_of_abs _ _ Hbound).
        apply Rplus_le_compat_l with (r := sig) in Hneg.
        replace (sig + - (Ls * h)) with (sig - Ls * h) in Hneg by ring.
        replace (sig + ((ux * vx u + uy * vy u) - sig))
          with (ux * vx u + uy * vy u) in Hneg by ring.
        exact Hneg. }
      assert (Eaff := int_affine s t ux uy Hs' Ht' Hux Huy Hst).
      assert (Hlow_int :
          h * (sig - Ls * h)
          <= int_seg (fun u => ux * vx u + uy * vy u) Ls s t HLs
               (dir_on ux uy s t Hs' Ht' Hux Huy)).
      { assert (Hc : int_seg (fun _ : R => sig - Ls * h) Ls s t HLs
                       (const_lip (sig - Ls * h) Ls s t HLs)
                     = h * (sig - Ls * h)).
        { rewrite (int_seg_const _ Ls s t HLs
                    (const_lip (sig - Ls * h) Ls s t HLs) Hst).
          unfold h. ring. }
        rewrite <- Hc. apply int_seg_mono; [exact Hst | exact Hlow_pt]. }
      assert (Hdot_le : ux * (gx t - gx s) + uy * (gy t - gy s)
                        <= dist (gamma s) (gamma t)).
      { assert (Hcs := dot_le_norms ux uy (gx t - gx s) (gy t - gy s)).
        replace (sqrt (ux * ux + uy * uy)) with 1 in Hcs.
        - rewrite Rmult_1_l in Hcs.
          eapply Rle_trans; [exact Hcs |].
          unfold gamma, dist. right.
          unfold dist_sq. simpl.
          replace ((gx s - gx t) * (gx s - gx t))
            with ((gx t - gx s) * (gx t - gx s)) by ring.
          replace ((gy s - gy t) * (gy s - gy t))
            with ((gy t - gy s) * (gy t - gy s)) by ring.
          reflexivity.
        - rewrite Hunit. symmetry. exact sqrt_1. }
      assert (Hdist_ge : h * (sig - Ls * h) <= dist (gamma s) (gamma t)).
      { eapply Rle_trans; [exact Hlow_int |].
        unfold Ls. rewrite Eaff. exact Hdot_le. }
      assert (Hgap_int : int_seg speed Ls s t HLs
                 (lip_clip_seg speed a b Ls s t speed_lip Hs' Ht')
                 - dist (gamma s) (gamma t)
               <= (sig + Ls * h) * h - h * (sig - Ls * h)).
      { apply Rplus_le_compat.
        - exact Hint_up.
        - apply Ropp_le_contravar. exact Hdist_ge. }
      assert (Hcancel : (sig + Ls * h) * h - h * (sig - Ls * h) = 2 * Ls * h * h)
        by ring.
      rewrite Hcancel in Hgap_int.
      eapply Rle_trans; [exact Hgap_int | exact Hslack].
Qed.

(* WITNESS {"claimId":"0001-metric-speed","topic":"metric","lemma":"lip_speed_is_curve_length","title":"C1 speed integral is the metric length","file":"theories/MetricSpeed.v","witness":"lip_speed_is_curve_length","board":"ADR-0001"} *)
Theorem lip_speed_is_curve_length :
  speedF b - speedF a =
    int_seg speed (Lx + Ly) a b HLs
      (lip_clip_seg speed a b (Lx + Ly) a b speed_lip
         (conj (Rle_refl a) Hab) (conj Hab (Rle_refl b))) /\
  is_curve_length gamma a b (speedF b - speedF a).
Proof.
  split.
  - apply (speedF_diff a b (conj (Rle_refl a) Hab) (conj Hab (Rle_refl b)) Hab).
  - apply curve_length_of_primitive.
    + intros s t Hs Hst Ht. apply chord_le_speed; assumption.
    + exact speed_tight.
    + exact Hab.
Qed.

End C1Speed.

(* Print Assumptions: every Lemma and Theorem in this file. *)
Print Assumptions abs_lt_all_eq0.
Print Assumptions derivable_pt_lim_cont.
Print Assumptions deriv_pt_sub.
Print Assumptions sqr_le_nonneg.
Print Assumptions dot_le_norms.
Print Assumptions norm_triangle.
Print Assumptions norm_abs_diff.
Print Assumptions norm_le_l1.
Print Assumptions lip_clip_seg.
Print Assumptions int_seg_const.
Print Assumptions int_seg_mono.
Print Assumptions const_lip.
Print Assumptions int_seg_nonneg.
Print Assumptions rmin3_pos.
Print Assumptions rmin3_le1.
Print Assumptions rmin3_le2.
Print Assumptions rmin3_le3.
Print Assumptions half_order.
Print Assumptions left_shift_le.
Print Assumptions both_shift_le.
Print Assumptions slack_le_eps.
Print Assumptions HLs.
Print Assumptions speed_lip.
Print Assumptions Gx_at_left.
Print Assumptions Gy_at_left.
Print Assumptions speedF_at_left.
Print Assumptions Gx_deriv.
Print Assumptions Gy_deriv.
Print Assumptions Gx_match_open.
Print Assumptions Gy_match_open.
Print Assumptions gx_cont.
Print Assumptions gy_cont.
Print Assumptions Gx_cont.
Print Assumptions Gy_cont.
Print Assumptions abs_pair_lt.
Print Assumptions coord_Gx_closed.
Print Assumptions coord_Gy_closed.
Print Assumptions Gx_diff_seg.
Print Assumptions Gy_diff_seg.
Print Assumptions coord_x_increment.
Print Assumptions coord_y_increment.
Print Assumptions speedF_diff.
Print Assumptions scale_vx_on.
Print Assumptions scale_vy_on.
Print Assumptions dir_on.
Print Assumptions abs_le_1_of_unit.
Print Assumptions int_affine.
Print Assumptions speed_ge_dir.
Print Assumptions chord_le_speed.
Print Assumptions neg_of_abs.
Print Assumptions speed_tight.
Print Assumptions lip_speed_is_curve_length.
