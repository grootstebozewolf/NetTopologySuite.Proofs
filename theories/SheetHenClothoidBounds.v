(* ============================================================================
   NetTopologySuite.Proofs.SheetHenClothoidBounds
   ----------------------------------------------------------------------------
   Fresnel integral bounds for the host clothoid. The parameterisation
   is OUR choice, not an ISO formula (stated in SheetHenClothoidCore):
     phi(s) = phi0 + sigma * s^2 / (2 * A^2)
     P(s)   = LOCATION + integral_0^s (cos phi(u), sin phi(u)) du
     gamma(t) = P(sd + t * (ed - sd))
   Cx and Cy are the unit-frame integrals of cos(u^2/2) and sin(u^2/2),
   taken in LipInt (dyadic Riemann sums). No RiemannInt.
   No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia Ranalysis1 FunctionalExtensionality.
From NTS.Proofs Require Import SheetHenClothoidCore LipInt.
Local Open Scope R_scope.

Definition fresnel_angle (u : R) : R := u * u / 2.
Definition fresnel_cx_integrand (u : R) : R := cos (fresnel_angle u).
Definition fresnel_cy_integrand (u : R) : R := sin (fresnel_angle u).

Lemma PI2_bounds : 7 / 8 <= PI / 2 <= 7 / 4.
Proof.
  pose proof pi2_int as H.
  assert (PI / 2 = PI2) by (unfold PI; field).
  lra.
Qed.

Lemma half_le_PI2 : 1 / 2 <= PI / 2.
Proof. pose proof PI2_bounds. lra. Qed.

Lemma half_lt_PI : 1 / 2 < PI.
Proof.
  pose proof PI2_bounds as H.
  assert (PI = 2 * (PI / 2)) by (unfold PI; field).
  lra.
Qed.

Lemma PI_ge_half_arg : forall z, 0 <= z <= 1 / 2 -> 0 <= z <= PI.
Proof. intros z Hz. pose proof half_lt_PI. lra. Qed.

Lemma angle_in_half : forall z, 0 <= z <= 1 / 2 -> - PI / 2 <= z <= PI / 2.
Proof. intros z Hz. pose proof half_le_PI2. lra. Qed.

Lemma cos_approx_1 : forall a, cos_approx a 1 = 1 - a * a / 2.
Proof. intro a. unfold cos_approx, cos_term. simpl. field. Qed.

Lemma cos_approx_2 : forall a,
  cos_approx a 2 = 1 - a * a / 2 + a * a * a * a / 24.
Proof. intro a. unfold cos_approx, cos_term. simpl. field. Qed.

Lemma sin_approx_1 : forall a, sin_approx a 1 = a - a * a * a / 6.
Proof. intro a. unfold sin_approx, sin_term. simpl. field. Qed.

Lemma cos_ge_quad : forall z, - PI / 2 <= z -> z <= PI / 2 ->
  1 - z * z / 2 <= cos z.
Proof.
  intros z Hlo Hhi.
  destruct (cos_bound z 0 Hlo Hhi) as [Hb _].
  rewrite cos_approx_1 in Hb. exact Hb.
Qed.

Lemma cos_le_quart : forall z, - PI / 2 <= z -> z <= PI / 2 ->
  cos z <= 1 - z * z / 2 + z * z * z * z / 24.
Proof.
  intros z Hlo Hhi.
  destruct (cos_bound z 0 Hlo Hhi) as [_ Hb].
  rewrite cos_approx_2 in Hb. exact Hb.
Qed.

Lemma sin_ge_cubic : forall z, 0 <= z <= PI -> z - z * z * z / 6 <= sin z.
Proof.
  intros z Hz.
  destruct (sin_bound z 0 (proj1 Hz) (proj2 Hz)) as [Hb _].
  rewrite sin_approx_1 in Hb. exact Hb.
Qed.

Lemma sin_le_arg : forall z, 0 <= z -> sin z <= z.
Proof.
  intros z Hz.
  apply Rle_trans with (Rabs (sin z)); [apply Rle_abs |].
  eapply Rle_trans; [apply abs_sin_le |].
  rewrite (Rabs_right z) by lra. apply Rle_refl.
Qed.

Lemma cos_nonincreasing : forall p q,
  0 <= q -> q <= p -> p <= PI / 2 -> cos p <= cos q.
Proof.
  intros p q Hq0 Hqp Hp.
  cut (cos p - cos q <= 0); [lra|].
  rewrite form2.
  assert (Hpi : PI / 2 <= PI).
  { pose proof PI2_bounds as Hb.
    assert (PI = 2 * (PI / 2)) by (unfold PI; field). lra. }
  assert (Hs1 : 0 <= sin ((p - q) / 2)).
  { apply sin_ge_0; [lra|]. lra. }
  assert (Hs2 : 0 <= sin ((p + q) / 2)).
  { apply sin_ge_0; [lra|]. lra. }
  nra.
Qed.

Lemma fresnel_angle_lip : forall s x y,
  Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
  Rabs (fresnel_angle x - fresnel_angle y) <= Rabs s * Rabs (x - y).
Proof.
  intros s x y Hx Hy.
  unfold fresnel_angle, Rdiv.
  replace (x * x * / 2 - y * y * / 2) with ((x - y) * (x + y) * / 2) by ring.
  rewrite !Rabs_mult.
  rewrite (Rabs_right (/ 2)) by lra.
  assert (Hxy : Rabs (x + y) <= 2 * Rabs s).
  { eapply Rle_trans; [apply Rabs_triang|].
    pose proof (cloth_window_abs s x Hx) as Hx'.
    pose proof (cloth_window_abs s y Hy) as Hy'. nra. }
  apply Rle_trans with (Rabs (x - y) * (2 * Rabs s) * / 2).
  - apply Rmult_le_compat_r; [lra|].
    apply Rmult_le_compat_l; [apply Rabs_pos | exact Hxy].
  - right. field.
Qed.

Lemma fresnel_cx_lip : forall s x y,
  Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
  Rabs (fresnel_cx_integrand x - fresnel_cx_integrand y)
    <= Rabs s * Rabs (x - y).
Proof.
  intros s x y Hx Hy. unfold fresnel_cx_integrand.
  eapply Rle_trans; [apply cos_lip | apply fresnel_angle_lip; assumption].
Qed.

Lemma fresnel_cy_lip : forall s x y,
  Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
  Rabs (fresnel_cy_integrand x - fresnel_cy_integrand y)
    <= Rabs s * Rabs (x - y).
Proof.
  intros s x y Hx Hy. unfold fresnel_cy_integrand.
  eapply Rle_trans; [apply sin_lip | apply fresnel_angle_lip; assumption].
Qed.

Lemma fresnel_cx_lip_unit : forall a b,
  0 <= a -> a <= b -> b <= 1 ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (fresnel_cx_integrand x - fresnel_cx_integrand y)
      <= 1 * Rabs (x - y).
Proof.
  intros a b Ha Hab Hb x y Hx Hy.
  rewrite (Rmin_left a b) in Hx, Hy by exact Hab.
  rewrite (Rmax_right a b) in Hx, Hy by exact Hab.
  unfold fresnel_cx_integrand.
  eapply Rle_trans; [apply cos_lip|].
  unfold fresnel_angle, Rdiv.
  replace (x * x * / 2 - y * y * / 2) with ((x - y) * (x + y) * / 2) by ring.
  rewrite !Rabs_mult. rewrite (Rabs_right (/ 2)) by lra.
  assert (Hxy : Rabs (x + y) <= 2).
  { eapply Rle_trans; [apply Rabs_triang|].
    rewrite (Rabs_right x), (Rabs_right y) by lra. lra. }
  apply Rle_trans with (Rabs (x - y) * 2 * / 2).
  - apply Rmult_le_compat_r; [lra|].
    apply Rmult_le_compat_l; [apply Rabs_pos | exact Hxy].
  - right. field.
Qed.

Lemma fresnel_cy_lip_unit : forall a b,
  0 <= a -> a <= b -> b <= 1 ->
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (fresnel_cy_integrand x - fresnel_cy_integrand y)
      <= 1 * Rabs (x - y).
Proof.
  intros a b Ha Hab Hb x y Hx Hy.
  rewrite (Rmin_left a b) in Hx, Hy by exact Hab.
  rewrite (Rmax_right a b) in Hx, Hy by exact Hab.
  unfold fresnel_cy_integrand.
  eapply Rle_trans; [apply sin_lip|].
  unfold fresnel_angle, Rdiv.
  replace (x * x * / 2 - y * y * / 2) with ((x - y) * (x + y) * / 2) by ring.
  rewrite !Rabs_mult. rewrite (Rabs_right (/ 2)) by lra.
  assert (Hxy : Rabs (x + y) <= 2).
  { eapply Rle_trans; [apply Rabs_triang|].
    rewrite (Rabs_right x), (Rabs_right y) by lra. lra. }
  apply Rle_trans with (Rabs (x - y) * 2 * / 2).
  - apply Rmult_le_compat_r; [lra|].
    apply Rmult_le_compat_l; [apply Rabs_pos | exact Hxy].
  - right. field.
Qed.

Definition cloth_Cx (s : R) : R :=
  int_seg fresnel_cx_integrand (Rabs s) 0 s (Rabs_pos s) (fresnel_cx_lip s).

Definition cloth_Cy (s : R) : R :=
  int_seg fresnel_cy_integrand (Rabs s) 0 s (Rabs_pos s) (fresnel_cy_lip s).

Lemma cloth_Cx_0 : cloth_Cx 0 = 0.
Proof. unfold cloth_Cx. apply int_seg_point. Qed.

Lemma cloth_Cy_0 : cloth_Cy 0 = 0.
Proof. unfold cloth_Cy. apply int_seg_point. Qed.

(* ---------- oriented-integral algebra used by the bounds ---------- *)

Lemma int_seg_mono : forall g h Lg Lh a b HLg Hlipg HLh Hlih,
  a <= b ->
  (forall x, a <= x <= b -> g x <= h x) ->
  int_seg g Lg a b HLg Hlipg <= int_seg h Lh a b HLh Hlih.
Proof.
  intros g h Lg Lh a b HLg Hlipg HLh Hlih Hab Hle.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hok|Hbad]; [|exfalso; apply Hbad; exact Hab].
  apply lint_mono. intros x Hx. apply Hle. exact Hx.
Qed.

Lemma const_lip : forall (c L a b : R) (HL : 0 <= L) x y,
  Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
  Rabs ((fun _ : R => c) x - (fun _ : R => c) y) <= L * Rabs (x - y).
Proof.
  intros. cbn. rewrite Rminus_diag, Rabs_R0.
  apply Rmult_le_pos; [exact HL | apply Rabs_pos].
Qed.

Lemma int_seg_const_val : forall c L a b HL Hlip, a <= b ->
  int_seg (fun _ : R => c) L a b HL Hlip = (b - a) * c.
Proof.
  intros c L a b HL Hlip Hab.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hok|Hbad]; [|exfalso; apply Hbad; exact Hab].
  apply lint_const.
Qed.

Lemma int_seg_ge_const : forall g L a b HL Hlip m,
  a <= b ->
  (forall x, a <= x <= b -> m <= g x) ->
  m * (b - a) <= int_seg g L a b HL Hlip.
Proof.
  intros g L a b HL Hlip m Hab Hm.
  assert (Hc : int_seg (fun _ : R => m) L a b HL (const_lip m L a b HL)
              = (b - a) * m).
  { apply int_seg_const_val. exact Hab. }
  assert (Hh : int_seg (fun _ : R => m) L a b HL (const_lip m L a b HL)
              <= int_seg g L a b HL Hlip).
  { apply int_seg_mono; [exact Hab|]. intros x Hx. apply Hm. exact Hx. }
  replace (m * (b - a)) with ((b - a) * m) by ring. lra.
Qed.

Lemma int_seg_le_const : forall g L a b HL Hlip M,
  a <= b ->
  (forall x, a <= x <= b -> g x <= M) ->
  int_seg g L a b HL Hlip <= M * (b - a).
Proof.
  intros g L a b HL Hlip M Hab HM.
  assert (Hc : int_seg (fun _ : R => M) L a b HL (const_lip M L a b HL)
              = (b - a) * M).
  { apply int_seg_const_val. exact Hab. }
  assert (Hh : int_seg g L a b HL Hlip
              <= int_seg (fun _ : R => M) L a b HL (const_lip M L a b HL)).
  { apply int_seg_mono; [exact Hab|]. intros x Hx. apply HM. exact Hx. }
  replace (M * (b - a)) with ((b - a) * M) by ring. lra.
Qed.

Lemma int_seg_eq_lim : forall g L a b HL Hlip l,
  a <= b ->
  Un_cv (fun k => dyadic g k a b) l ->
  int_seg g L a b HL Hlip = l.
Proof.
  intros g L a b HL Hlip l Hab Hcv.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hok|Hbad]; [|exfalso; apply Hbad; exact Hab].
  apply UL_sequence with (fun k => dyadic g k a b).
  - apply lint_cv_dyadic.
  - exact Hcv.
Qed.

Lemma cloth_Cx_diff : forall a b (Ha : 0 <= a) (Hab : a <= b) (Hb : b <= 1),
  cloth_Cx b - cloth_Cx a =
    int_seg fresnel_cx_integrand 1 a b Rle_0_1
      (fresnel_cx_lip_unit a b Ha Hab Hb).
Proof.
  intros a b Ha Hab Hb.
  unfold cloth_Cx.
  rewrite (int_seg_L fresnel_cx_integrand (Rabs b) 1 0 b
            (Rabs_pos b) Rle_0_1 (fresnel_cx_lip b)
            (fresnel_cx_lip_unit 0 b (Rle_refl 0) (Rle_trans _ _ _ Ha Hab) Hb)).
  rewrite (int_seg_L fresnel_cx_integrand (Rabs a) 1 0 a
            (Rabs_pos a) Rle_0_1 (fresnel_cx_lip a)
            (fresnel_cx_lip_unit 0 a (Rle_refl 0) Ha
               (Rle_trans _ _ _ Hab Hb))).
  rewrite (int_seg_add fresnel_cx_integrand 1 0 a b Rle_0_1
            (fresnel_cx_lip_unit 0 b (Rle_refl 0) (Rle_trans _ _ _ Ha Hab) Hb)
            (fresnel_cx_lip_unit 0 a (Rle_refl 0) Ha (Rle_trans _ _ _ Hab Hb))
            (fresnel_cx_lip_unit a b Ha Hab Hb) Ha Hab).
  ring.
Qed.

Lemma cloth_Cy_diff : forall a b (Ha : 0 <= a) (Hab : a <= b) (Hb : b <= 1),
  cloth_Cy b - cloth_Cy a =
    int_seg fresnel_cy_integrand 1 a b Rle_0_1
      (fresnel_cy_lip_unit a b Ha Hab Hb).
Proof.
  intros a b Ha Hab Hb.
  unfold cloth_Cy.
  rewrite (int_seg_L fresnel_cy_integrand (Rabs b) 1 0 b
            (Rabs_pos b) Rle_0_1 (fresnel_cy_lip b)
            (fresnel_cy_lip_unit 0 b (Rle_refl 0) (Rle_trans _ _ _ Ha Hab) Hb)).
  rewrite (int_seg_L fresnel_cy_integrand (Rabs a) 1 0 a
            (Rabs_pos a) Rle_0_1 (fresnel_cy_lip a)
            (fresnel_cy_lip_unit 0 a (Rle_refl 0) Ha
               (Rle_trans _ _ _ Hab Hb))).
  rewrite (int_seg_add fresnel_cy_integrand 1 0 a b Rle_0_1
            (fresnel_cy_lip_unit 0 b (Rle_refl 0) (Rle_trans _ _ _ Ha Hab) Hb)
            (fresnel_cy_lip_unit 0 a (Rle_refl 0) Ha (Rle_trans _ _ _ Hab Hb))
            (fresnel_cy_lip_unit a b Ha Hab Hb) Ha Hab).
  ring.
Qed.

(* ---------- dyadic sums of monomials ---------- *)

Fixpoint nsum (f : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S n' => nsum f n' + f n'
  end.

Lemma nsum_scale : forall c f n, nsum (fun i => c * f i) n = c * nsum f n.
Proof.
  intros c f n. induction n as [|n IH]; simpl; [|rewrite IH]; ring.
Qed.

Lemma nsum_succ : forall f n,
  nsum f (S n) = f O + nsum (fun i => f (S i)) n.
Proof.
  intros f n. induction n as [|n IH].
  - simpl. ring.
  - change (nsum f (S (S n))) with (nsum f (S n) + f (S n)).
    rewrite IH.
    change (nsum (fun i => f (S i)) (S n))
      with (nsum (fun i => f (S i)) n + f (S n)).
    ring.
Qed.

Lemma nsum_sq6 : forall n,
  6 * nsum (fun i => INR i * INR i) n =
  INR n * (INR n - 1) * (2 * INR n - 1).
Proof.
  induction n as [|n IH].
  - unfold nsum. rewrite INR_0. ring.
  - cbn [nsum]. rewrite Rmult_plus_distr_l, IH.
    replace (INR (S n)) with (INR n + 1) by (rewrite S_INR; ring).
    ring.
Qed.

Lemma nsum_sq : forall n,
  nsum (fun i => INR i * INR i) n =
  INR n * (INR n - 1) * (2 * INR n - 1) / 6.
Proof.
  intro n. apply (Rmult_eq_reg_l 6); [|lra].
  rewrite nsum_sq6. field.
Qed.

Lemma nsum_pow6_42 : forall n,
  42 * nsum (fun i => INR i ^ 6) (S n) =
  INR n * INR (S n) * (2 * INR n + 1) *
    (3 * INR n ^ 4 + 6 * INR n ^ 3 - 3 * INR n + 1).
Proof.
  induction n as [|n IH].
  - cbn. ring.
  - change (nsum (fun i => INR i ^ 6) (S (S n)))
      with (nsum (fun i => INR i ^ 6) (S n) + INR (S n) ^ 6).
    rewrite Rmult_plus_distr_l, IH.
    replace (INR (S n)) with (INR n + 1) by (rewrite S_INR; ring).
    replace (INR (S (S n))) with (INR n + 2) by (rewrite !S_INR; ring).
    ring.
Qed.

Lemma nsum_ext : forall f g n, (forall i, f i = g i) -> nsum f n = nsum g n.
Proof.
  intros f g n Heq. induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH, Heq. reflexivity.
Qed.

Lemma sum_left_at : forall g n a h,
  sum_left g n a h = h * nsum (fun i => g (a + INR i * h)) n.
Proof.
  intros g n. induction n as [|n IH]; intros a h.
  - simpl. ring.
  - change (sum_left g (S n) a h) with (h * g a + sum_left g n (a + h) h).
    rewrite IH.
    rewrite (nsum_succ (fun i => g (a + INR i * h))).
    replace (a + INR O * h) with a by (rewrite INR_0; ring).
    rewrite Rmult_plus_distr_l.
    apply f_equal2; [ring|].
    apply f_equal.
    apply nsum_ext. intro i. f_equal. rewrite S_INR. ring.
Qed.

Lemma sum_left_split : forall g n m a h,
  sum_left g (Nat.add n m) a h =
  sum_left g n a h + sum_left g m (a + INR n * h) h.
Proof.
  intros g n. induction n as [|n IH]; intros m a h.
  - cbn. replace (a + 0 * h) with a by ring.
    rewrite Rplus_0_l. reflexivity.
  - cbn [Nat.add sum_left]. rewrite IH.
    replace (a + h + INR n * h) with (a + INR (S n) * h)
      by (rewrite S_INR; ring).
    ring.
Qed.

Lemma INR_pow2 : forall k, INR (Nat.pow 2 k) = 2 ^ k.
Proof.
  induction k as [|k IH].
  - simpl. reflexivity.
  - cbn [Nat.pow]. rewrite mult_INR, IH. simpl. ring.
Qed.

Lemma INR_pow2_ge1 : forall k, 1 <= INR (Nat.pow 2 k).
Proof.
  induction k as [|k IH].
  - simpl. lra.
  - cbn [Nat.pow]. rewrite mult_INR. change (INR 2) with 2. lra.
Qed.

Lemma dyadic_as_sum : forall g k a b,
  dyadic g k a b =
  sum_left g (Nat.pow 2 k) a ((b - a) / INR (Nat.pow 2 k)).
Proof.
  intros g k. induction k as [|k IH]; intros a b.
  - simpl. field.
  - cbn [dyadic Nat.pow].
    set (n := Nat.pow 2 k).
    set (m := (a + b) / 2).
    set (h := (b - a) / INR (Nat.mul 2 n)).
    assert (Hn : INR n <> 0).
    { unfold n. apply Rgt_not_eq. pose proof (INR_pow2_ge1 k). lra. }
    assert (E1 : (m - a) / INR n = h).
    { unfold m, h. rewrite mult_INR. change (INR 2) with 2. field. exact Hn. }
    assert (E2 : (b - m) / INR n = h).
    { unfold m, h. rewrite mult_INR. change (INR 2) with 2. field. exact Hn. }
    assert (Em : a + INR n * h = m).
    { unfold m, h. rewrite mult_INR. change (INR 2) with 2. field. exact Hn. }
    unfold n in E1, E2, Em, h.
    rewrite (IH a m), (IH m b), E1, E2, <- Em.
    rewrite <- (sum_left_split g (Nat.pow 2 k) (Nat.pow 2 k) a h).
    replace (Nat.add (Nat.pow 2 k) (Nat.pow 2 k))
      with (Nat.mul 2 (Nat.pow 2 k)) by lia.
    reflexivity.
Qed.

Lemma dyadic_sq : forall k s,
  dyadic (fun u => u * u) k 0 s =
  s ^ 3 * (INR (Nat.pow 2 k) - 1) * (2 * INR (Nat.pow 2 k) - 1)
    / (6 * INR (Nat.pow 2 k) ^ 2).
Proof.
  intros k s.
  rewrite dyadic_as_sum.
  set (N := INR (Nat.pow 2 k)).
  set (h := (s - 0) / N).
  rewrite sum_left_at.
  assert (HN : N <> 0).
  { unfold N. pose proof (INR_pow2_ge1 k). lra. }
  assert (Es : nsum (fun i => (0 + INR i * h) * (0 + INR i * h)) (Nat.pow 2 k)
               = nsum (fun i => (h * h) * (INR i * INR i)) (Nat.pow 2 k)).
  { apply nsum_ext. intro i. ring. }
  assert (E : nsum (fun i => (h * h) * (INR i * INR i)) (Nat.pow 2 k)
              = h * h * (N * (N - 1) * (2 * N - 1) / 6)).
  { rewrite nsum_scale, nsum_sq. unfold N. ring. }
  rewrite Es, E. unfold h. field. exact HN.
Qed.

Lemma pow6_num : forall N,
  (N - 1) * (2 * N - 1) *
    (3 * (N - 1) ^ 4 + 6 * (N - 1) ^ 3 - 3 * (N - 1) + 1) - 6 * N ^ 6
  = -21 * N ^ 5 + 21 * N ^ 4 - 7 * N ^ 2 + 1.
Proof. intros N. ring. Qed.

Lemma pow6_closed_form : forall s N h,
  N <> 0 -> h = s / N ->
  h * (h ^ 6 * ((N - 1) * N * (2 * (N - 1) + 1) *
    (3 * (N - 1) ^ 4 + 6 * (N - 1) ^ 3 - 3 * (N - 1) + 1) / 42))
  = s ^ 7 * (N - 1) * (2 * N - 1) *
      (3 * (N - 1) ^ 4 + 6 * (N - 1) ^ 3 - 3 * (N - 1) + 1)
      / (42 * N ^ 6).
Proof. intros s N h HN Eh. subst h. field. exact HN. Qed.

Lemma dyadic_pow6 : forall k s,
  dyadic (fun u => u ^ 6) k 0 s =
  s ^ 7 * (INR (Nat.pow 2 k) - 1) * (2 * INR (Nat.pow 2 k) - 1) *
    (3 * (INR (Nat.pow 2 k) - 1) ^ 4 + 6 * (INR (Nat.pow 2 k) - 1) ^ 3
       - 3 * (INR (Nat.pow 2 k) - 1) + 1)
    / (42 * INR (Nat.pow 2 k) ^ 6).
Proof.
  intros k s.
  rewrite dyadic_as_sum.
  set (N := INR (Nat.pow 2 k)).
  set (h := (s - 0) / N).
  set (m := Nat.pred (Nat.pow 2 k)).
  assert (HS : Nat.pow 2 k = S m).
  { unfold m. rewrite Nat.succ_pred. reflexivity.
    intro Hz. pose proof (INR_pow2_ge1 k) as H1.
    rewrite Hz in H1. simpl in H1. lra. }
  rewrite HS. rewrite sum_left_at.
  assert (HN : N <> 0).
  { unfold N. pose proof (INR_pow2_ge1 k). lra. }
  assert (Hm : INR m = N - 1).
  { unfold N. rewrite HS. rewrite S_INR. ring. }
  assert (E0 : nsum (fun i => (0 + INR i * h) ^ 6) (S m)
               = nsum (fun i => (INR i * h) ^ 6) (S m)).
  { apply nsum_ext. intro i. ring. }
  rewrite E0.
  assert (En : nsum (fun i => (INR i * h) ^ 6) (S m)
               = h ^ 6 * nsum (fun i => INR i ^ 6) (S m)).
  { rewrite <- (nsum_scale (h ^ 6) (fun i => INR i ^ 6) (S m)).
    apply nsum_ext. intro i. rewrite Rpow_mult_distr. ring. }
  rewrite En.
  assert (En6 : nsum (fun i => INR i ^ 6) (S m) =
            INR m * INR (S m) * (2 * INR m + 1) *
              (3 * INR m ^ 4 + 6 * INR m ^ 3 - 3 * INR m + 1) / 42).
  { apply (Rmult_eq_reg_l 42); [|lra]. rewrite nsum_pow6_42. field. }
  rewrite En6, Hm.
  assert (HN' : N = INR (S m)).
  { unfold N. rewrite HS. reflexivity. }
  rewrite <- HN'. unfold h.
  replace (s - 0) with s by ring.
  apply pow6_closed_form; [exact HN | reflexivity].
Qed.

Lemma cv_inv_pow2 : Un_cv (fun k => / INR (Nat.pow 2 k)) 0.
Proof.
  intros eps Heps.
  assert (H12 : Rabs (/ 2) < 1) by (rewrite Rabs_right; lra).
  destruct (pow_lt_1_zero (/ 2) H12 eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  unfold R_dist. rewrite Rminus_0_r, INR_pow2.
  rewrite <- (pow_inv 2 n) by lra. exact HN.
Qed.

Lemma sq_err : forall k s, 0 <= s ->
  Rabs (dyadic (fun u => u * u) k 0 s - s ^ 3 / 3)
    <= s ^ 3 / (2 * INR (Nat.pow 2 k)).
Proof.
  intros k s Hs.
  rewrite dyadic_sq.
  set (N := INR (Nat.pow 2 k)).
  assert (HN : 1 <= N) by (unfold N; apply INR_pow2_ge1).
  assert (E : s ^ 3 * (N - 1) * (2 * N - 1) / (6 * N ^ 2) - s ^ 3 / 3
              = s ^ 3 * (1 - 3 * N) / (6 * N ^ 2)).
  { field. lra. }
  rewrite E.
  replace (s ^ 3 * (1 - 3 * N) / (6 * N ^ 2))
    with (- (s ^ 3 * (3 * N - 1) / (6 * N ^ 2))) by (field; lra).
  rewrite Rabs_Ropp.
  assert (Hnn : 0 <= s ^ 3 * (3 * N - 1) / (6 * N ^ 2)).
  { unfold Rdiv. apply Rmult_le_pos.
    - apply Rmult_le_pos; [apply pow_le; exact Hs | nra].
    - apply Rlt_le, Rinv_0_lt_compat. nra. }
  rewrite (Rabs_pos_eq _ Hnn).
  apply Rle_trans with (s ^ 3 * (3 * N) / (6 * N ^ 2)).
  - apply Rmult_le_compat_r.
    + apply Rlt_le, Rinv_0_lt_compat. nra.
    + apply Rmult_le_compat_l; nra.
  - right. field. lra.
Qed.

Lemma dyadic_sq_cv : forall s, 0 <= s ->
  Un_cv (fun k => dyadic (fun u => u * u) k 0 s) (s ^ 3 / 3).
Proof.
  intros s Hs eps Heps.
  destruct (Req_dec s 0) as [->|Hnz].
  - exists O. intros n _. unfold R_dist.
    rewrite dyadic_zero_width. replace (0 ^ 3 / 3) with 0 by field.
    rewrite Rminus_diag, Rabs_R0. exact Heps.
  - assert (Hsp : 0 < s) by lra.
    assert (Hden : 0 < eps * 2 / s ^ 3).
    { apply Rdiv_lt_0_compat; [|apply pow_lt; exact Hsp].
      apply Rmult_lt_0_compat; [exact Heps | lra]. }
    destruct (cv_inv_pow2 (eps * 2 / s ^ 3) Hden) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn). unfold R_dist in *.
    rewrite Rminus_0_r in HN.
    assert (Hinv : 0 <= / INR (Nat.pow 2 n)).
    { apply Rlt_le, Rinv_0_lt_compat. pose proof (INR_pow2_ge1 n). lra. }
    rewrite (Rabs_pos_eq _ Hinv) in HN.
    eapply Rle_lt_trans; [apply sq_err; exact Hs|].
    replace (s ^ 3 / (2 * INR (Nat.pow 2 n)))
      with (s ^ 3 / 2 * / INR (Nat.pow 2 n)).
    2:{ field. pose proof (INR_pow2_ge1 n). lra. }
    replace eps with (s ^ 3 / 2 * (eps * 2 / s ^ 3)) by (field; lra).
    apply Rmult_lt_compat_l; [apply Rdiv_lt_0_compat; [apply pow_lt; exact Hsp | lra] | exact HN].
Qed.

Lemma pow6_err : forall k s, 0 <= s ->
  Rabs (dyadic (fun u => u ^ 6) k 0 s - s ^ 7 / 7)
    <= 2 * s ^ 7 / INR (Nat.pow 2 k).
Proof.
  intros k s Hs.
  rewrite dyadic_pow6.
  set (N := INR (Nat.pow 2 k)).
  set (Q := 3 * (N - 1) ^ 4 + 6 * (N - 1) ^ 3 - 3 * (N - 1) + 1).
  assert (HN : 1 <= N) by (unfold N; apply INR_pow2_ge1).
  assert (E : s ^ 7 * (N - 1) * (2 * N - 1) * Q / (42 * N ^ 6) - s ^ 7 / 7
              = s ^ 7 * ((N - 1) * (2 * N - 1) * Q - 6 * N ^ 6) / (42 * N ^ 6)).
  { unfold Q. field. lra. }
  rewrite E.
  replace ((N - 1) * (2 * N - 1) * Q - 6 * N ^ 6)
    with (-21 * N ^ 5 + 21 * N ^ 4 - 7 * N ^ 2 + 1).
  2:{ unfold Q. rewrite <- pow6_num. ring. }
  set (num := -21 * N ^ 5 + 21 * N ^ 4 - 7 * N ^ 2 + 1).
  assert (Hnum : Rabs num <= 50 * N ^ 5).
  { unfold num.
    replace (-21 * N ^ 5 + 21 * N ^ 4 - 7 * N ^ 2 + 1)
      with (-21 * N ^ 5 + 21 * N ^ 4 + -7 * N ^ 2 + 1) by ring.
    eapply Rle_trans.
    - apply (Rabs_lin4 ((-21) * N ^ 5) (21 * N ^ 4) ((-7) * N ^ 2) 1).
    - assert (Ha : Rabs ((-21) * N ^ 5) = 21 * N ^ 5).
      { rewrite Rabs_mult.
        assert (H21 : Rabs (-21) = 21) by (rewrite Rabs_left; lra).
        rewrite H21.
        rewrite (Rabs_pos_eq (N ^ 5)); [reflexivity|apply pow_le; lra]. }
      assert (Hb : Rabs (21 * N ^ 4) = 21 * N ^ 4).
      { apply Rabs_pos_eq. apply Rmult_le_pos; [lra|apply pow_le; lra]. }
      assert (Hc : Rabs ((-7) * N ^ 2) = 7 * N ^ 2).
      { rewrite Rabs_mult.
        assert (H7 : Rabs (-7) = 7) by (rewrite Rabs_left; lra).
        rewrite H7.
        rewrite (Rabs_pos_eq (N ^ 2)); [reflexivity|apply pow_le; lra]. }
      rewrite Ha, Hb, Hc.
      rewrite (Rabs_pos_eq 1) by lra.
      assert (H4 : N ^ 4 <= N ^ 5) by (apply Rle_pow; [exact HN|lia]).
      assert (H2 : N ^ 2 <= N ^ 5) by (apply Rle_pow; [exact HN|lia]).
      assert (H0 : 1 <= N ^ 5).
      { rewrite <- (pow_O N). apply Rle_pow; [exact HN|lia]. }
      apply Rle_trans with (21 * N ^ 5 + 21 * N ^ 5 + 7 * N ^ 5 + N ^ 5).
      + apply Rplus_le_compat; [apply Rplus_le_compat; [apply Rplus_le_compat|]|].
        * apply Rle_refl.
        * apply Rmult_le_compat_l; [lra|exact H4].
        * apply Rmult_le_compat_l; [lra|exact H2].
        * exact H0.
      + right. ring. }
  unfold Rdiv.
  rewrite Rabs_mult.
  assert (Hden : 0 <= / (42 * N ^ 6)).
  { apply Rlt_le, Rinv_0_lt_compat.
    apply Rmult_lt_0_compat; [lra|apply pow_lt; lra]. }
  rewrite (Rabs_pos_eq _ Hden).
  rewrite Rabs_mult.
  assert (Hs7 : 0 <= s ^ 7) by (apply pow_le; exact Hs).
  rewrite (Rabs_pos_eq _ Hs7).
  apply Rle_trans with (s ^ 7 * (50 * N ^ 5) * / (42 * N ^ 6)).
  - apply Rmult_le_compat_r; [exact Hden|].
    apply Rmult_le_compat_l; [exact Hs7|exact Hnum].
  - apply Rle_trans with (2 * s ^ 7 * / N).
    + replace (s ^ 7 * (50 * N ^ 5) * / (42 * N ^ 6))
        with ((50 / 42) * (s ^ 7 * / N)).
      2:{ field. lra. }
      replace (2 * s ^ 7 * / N) with (2 * (s ^ 7 * / N)) by ring.
      apply Rmult_le_compat_r.
      * apply Rmult_le_pos; [exact Hs7|].
        apply Rlt_le, Rinv_0_lt_compat. lra.
      * unfold Rdiv. lra.
    + unfold N. apply Rle_refl.
Qed.

Lemma dyadic_pow6_cv : forall s, 0 <= s ->
  Un_cv (fun k => dyadic (fun u => u ^ 6) k 0 s) (s ^ 7 / 7).
Proof.
  intros s Hs eps Heps.
  destruct (Req_dec s 0) as [->|Hnz].
  - exists O. intros n _. unfold R_dist.
    rewrite dyadic_zero_width. replace (0 ^ 7 / 7) with 0 by field.
    rewrite Rminus_diag, Rabs_R0. exact Heps.
  - assert (Hsp : 0 < s) by lra.
    assert (Hden : 0 < eps / (2 * s ^ 7)).
    { apply Rdiv_lt_0_compat.
      - exact Heps.
      - apply Rmult_lt_0_compat; [lra|apply pow_lt; exact Hsp]. }
    destruct (cv_inv_pow2 (eps / (2 * s ^ 7)) Hden) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn). unfold R_dist in *.
    rewrite Rminus_0_r in HN.
    assert (Hinv : 0 <= / INR (Nat.pow 2 n)).
    { apply Rlt_le, Rinv_0_lt_compat. pose proof (INR_pow2_ge1 n). lra. }
    rewrite (Rabs_pos_eq _ Hinv) in HN.
    eapply Rle_lt_trans; [apply pow6_err; exact Hs|].
    replace (2 * s ^ 7 / INR (Nat.pow 2 n))
      with ((2 * s ^ 7) * / INR (Nat.pow 2 n)).
    2:{ unfold Rdiv. field. pose proof (INR_pow2_ge1 n). lra. }
    replace eps with ((2 * s ^ 7) * (eps / (2 * s ^ 7))) by (field; lra).
    apply Rmult_lt_compat_l.
    + apply Rmult_lt_0_compat; [lra|apply pow_lt; exact Hsp].
    + exact HN.
Qed.

Lemma sq_lip : forall s (Hs : 0 <= s) x y,
  Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
  Rabs (x * x - y * y) <= (2 * s) * Rabs (x - y).
Proof.
  intros s Hs x y Hx Hy.
  rewrite (Rmin_left 0 s) in Hx, Hy by lra.
  rewrite (Rmax_right 0 s) in Hx, Hy by lra.
  replace (x * x - y * y) with ((x - y) * (x + y)) by ring.
  rewrite Rabs_mult.
  assert (Hxy : Rabs (x + y) <= 2 * s).
  { eapply Rle_trans; [apply Rabs_triang|].
    rewrite (Rabs_right x), (Rabs_right y) by lra. lra. }
  apply Rle_trans with (Rabs (x - y) * (2 * s)).
  - apply Rmult_le_compat_l; [apply Rabs_pos | exact Hxy].
  - right. ring.
Qed.

Lemma two_s_nonneg : forall s, 0 <= s -> 0 <= 2 * s.
Proof. intros. lra. Qed.

Lemma int_sq : forall s (Hs : 0 <= s),
  int_seg (fun u => u * u) (2 * s) 0 s (two_s_nonneg s Hs) (sq_lip s Hs)
    = s ^ 3 / 3.
Proof.
  intros s Hs.
  apply int_seg_eq_lim; [exact Hs | apply dyadic_sq_cv; exact Hs].
Qed.

Lemma pow6_L_nonneg : forall s, 0 <= s -> 0 <= 6 * s ^ 5.
Proof. intros s Hs. apply Rmult_le_pos; [lra|]. apply pow_le. exact Hs. Qed.

Lemma pow6_lip : forall s (Hs : 0 <= s) x y,
  Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
  Rabs (x ^ 6 - y ^ 6) <= (6 * s ^ 5) * Rabs (x - y).
Proof.
  intros s Hs x y Hx Hy.
  rewrite (Rmin_left 0 s) in Hx, Hy by lra.
  rewrite (Rmax_right 0 s) in Hx, Hy by lra.
  replace (x ^ 6 - y ^ 6) with
    ((x - y) * (x ^ 5 + x ^ 4 * y + x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3
                + x * y ^ 4 + y ^ 5)) by ring.
  rewrite Rabs_mult.
  assert (Hterm : Rabs (x ^ 5 + x ^ 4 * y + x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3
                         + x * y ^ 4 + y ^ 5) <= 6 * s ^ 5).
  { assert (Hx5 : x ^ 5 <= s ^ 5) by (apply pow_incr; lra).
    assert (Hy5 : y ^ 5 <= s ^ 5) by (apply pow_incr; lra).
    assert (Ht : forall p q, 0 <= p -> p <= s -> 0 <= q -> q <= s ->
                  p ^ 4 * q <= s ^ 5 /\ p ^ 3 * q ^ 2 <= s ^ 5 /\
                  p ^ 2 * q ^ 3 <= s ^ 5 /\ p * q ^ 4 <= s ^ 5).
    { intros p q Hp0 Hp Hq0 Hq. repeat split.
      - apply Rle_trans with (s ^ 4 * s); [|right; ring].
        apply Rmult_le_compat; try apply pow_le; try lra; try apply pow_incr; lra.
      - apply Rle_trans with (s ^ 3 * s ^ 2); [|right; ring].
        apply Rmult_le_compat; try apply pow_le; try lra; try apply pow_incr; lra.
      - apply Rle_trans with (s ^ 2 * s ^ 3); [|right; ring].
        apply Rmult_le_compat; try apply pow_le; try lra; try apply pow_incr; lra.
      - apply Rle_trans with (s * s ^ 4); [|right; ring].
        apply Rmult_le_compat; try apply pow_le; try lra; try apply pow_incr; lra. }
    destruct (Ht x y) as [Hxy1 [Hxy2 [Hxy3 Hxy4]]]; try lra.
    eapply Rle_trans; [apply Rabs_triang|].
    eapply Rle_trans; [apply Rplus_le_compat; [apply Rabs_triang|apply Rle_refl]|].
    eapply Rle_trans; [apply Rplus_le_compat;
      [apply Rplus_le_compat; [apply Rabs_triang|apply Rle_refl]|apply Rle_refl]|].
    eapply Rle_trans; [apply Rplus_le_compat; [apply Rplus_le_compat;
      [apply Rplus_le_compat; [apply Rabs_triang|apply Rle_refl]|apply Rle_refl]
      |apply Rle_refl]|].
    eapply Rle_trans; [apply Rplus_le_compat; [apply Rplus_le_compat;
      [apply Rplus_le_compat; [apply Rplus_le_compat; [apply Rabs_triang|apply Rle_refl]
        |apply Rle_refl]|apply Rle_refl]|apply Rle_refl]|].
    assert (Hp5 : 0 <= x ^ 5) by (apply pow_le; lra).
    assert (Hq5 : 0 <= y ^ 5) by (apply pow_le; lra).
    assert (Hp4 : 0 <= x ^ 4 * y).
    { apply Rmult_le_pos; [apply pow_le; lra|lra]. }
    assert (Hp3 : 0 <= x ^ 3 * y ^ 2).
    { apply Rmult_le_pos; [apply pow_le; lra|apply pow_le; lra]. }
    assert (Hp2 : 0 <= x ^ 2 * y ^ 3).
    { apply Rmult_le_pos; [apply pow_le; lra|apply pow_le; lra]. }
    assert (Hp1 : 0 <= x * y ^ 4).
    { apply Rmult_le_pos; [lra|apply pow_le; lra]. }
    rewrite (Rabs_pos_eq (x ^ 5) Hp5),
            (Rabs_pos_eq (x ^ 4 * y) Hp4),
            (Rabs_pos_eq (x ^ 3 * y ^ 2) Hp3),
            (Rabs_pos_eq (x ^ 2 * y ^ 3) Hp2),
            (Rabs_pos_eq (x * y ^ 4) Hp1),
            (Rabs_pos_eq (y ^ 5) Hq5).
    apply Rle_trans with (s ^ 5 + s ^ 5 + s ^ 5 + s ^ 5 + s ^ 5 + s ^ 5);
      [|right; ring].
    apply Rplus_le_compat; [apply Rplus_le_compat; [apply Rplus_le_compat;
      [apply Rplus_le_compat; [apply Rplus_le_compat|]|]|]|].
    - exact Hx5.
    - exact Hxy1.
    - exact Hxy2.
    - exact Hxy3.
    - exact Hxy4.
    - exact Hy5. }
  apply Rle_trans with (Rabs (x - y) * (6 * s ^ 5)).
  - apply Rmult_le_compat_l; [apply Rabs_pos | exact Hterm].
  - right. ring.
Qed.

Lemma int_pow6 : forall s (Hs : 0 <= s),
  int_seg (fun u => u ^ 6) (6 * s ^ 5) 0 s (pow6_L_nonneg s Hs) (pow6_lip s Hs)
    = s ^ 7 / 7.
Proof.
  intros s Hs.
  apply int_seg_eq_lim; [exact Hs | apply dyadic_pow6_cv; exact Hs].
Qed.

Lemma angle_as_sq : forall u, fresnel_angle u = / 2 * (u * u).
Proof. intro u. unfold fresnel_angle, Rdiv. ring. Qed.

Lemma angle_scale_lip : forall s (Hs : 0 <= s) x y,
  Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
  Rabs (/ 2 * (x * x) - / 2 * (y * y)) <= Rabs s * Rabs (x - y).
Proof.
  intros s Hs x y Hx Hy.
  replace (/ 2 * (x * x) - / 2 * (y * y)) with (/ 2 * (x * x - y * y)) by ring.
  rewrite Rabs_mult, (Rabs_right (/ 2)) by lra.
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [lra | apply (sq_lip s Hs); assumption].
  - rewrite (Rabs_right s) by lra. right. field.
Qed.

Lemma int_fresnel_angle : forall s (Hs : 0 <= s),
  int_seg fresnel_angle (Rabs s) 0 s (Rabs_pos s) (fresnel_angle_lip s)
    = s ^ 3 / 6.
Proof.
  intros s Hs.
  rewrite (int_seg_ext fresnel_angle (fun u => / 2 * (u * u)) (Rabs s) 0 s
            (Rabs_pos s) (fresnel_angle_lip s) (angle_scale_lip s Hs)).
  2:{ intros x _. apply angle_as_sq. }
  rewrite (int_seg_scal (fun u => u * u) (/ 2) (Rabs s) (2 * s) 0 s
            (Rabs_pos s) (two_s_nonneg s Hs) (sq_lip s Hs) (angle_scale_lip s Hs)).
  rewrite (int_sq s Hs). field.
Qed.

(* ---------- the fixture bounds ---------- *)

Lemma angle_01 : forall u, 0 <= u <= 1 -> 0 <= fresnel_angle u <= 1 / 2.
Proof. intros u Hu. unfold fresnel_angle. nra. Qed.

Lemma one_minus_sq_7_8 : forall z, 0 <= z -> z <= 1 / 2 -> 7 / 8 <= 1 - z * z / 2.
Proof.
  intros z Hz0 Hz.
  assert (z * z <= (1 / 2) * (1 / 2)) by (apply Rmult_le_compat; lra).
  assert (z * z / 2 <= ((1 / 2) * (1 / 2)) / 2).
  { unfold Rdiv. apply Rmult_le_compat_r; [lra|]. exact H. }
  assert (((1 / 2) * (1 / 2)) / 2 = 1 / 8) by field. lra.
Qed.

Lemma one_minus_sq_4919 : forall z, 0 <= z -> z <= 9 / 50 ->
  4919 / 5000 <= 1 - z * z / 2.
Proof.
  intros z Hz0 Hz.
  assert (z * z <= (9 / 50) * (9 / 50)) by (apply Rmult_le_compat; lra).
  assert (z * z / 2 <= ((9 / 50) * (9 / 50)) / 2).
  { unfold Rdiv. apply Rmult_le_compat_r; [lra|]. exact H. }
  assert (((9 / 50) * (9 / 50)) / 2 = 81 / 5000) by field. lra.
Qed.

Lemma angle_le_9_50 : forall u, 0 <= u -> u <= 3 / 5 -> fresnel_angle u <= 9 / 50.
Proof.
  intros u H0 H1. unfold fresnel_angle.
  assert (u * u <= (3 / 5) * (3 / 5)) by (apply Rmult_le_compat; lra).
  assert (u * u / 2 <= ((3 / 5) * (3 / 5)) / 2).
  { unfold Rdiv. apply Rmult_le_compat_r; [lra|]. exact H. }
  assert (((3 / 5) * (3 / 5)) / 2 = 9 / 50) by field. lra.
Qed.

Lemma cloth_Cx_mono_01 : forall a b, 0 <= a -> a <= b -> b <= 1 ->
  cloth_Cx a <= cloth_Cx b.
Proof.
  intros a b Ha Hab Hb.
  pose proof (cloth_Cx_diff a b Ha Hab Hb) as E.
  assert (Hpos : 0 * (b - a) <= int_seg fresnel_cx_integrand 1 a b Rle_0_1
            (fresnel_cx_lip_unit a b Ha Hab Hb)).
  { apply int_seg_ge_const; [exact Hab|]. intros x Hx.
    unfold fresnel_cx_integrand. apply cos_ge_0.
    - pose proof (angle_in_half (fresnel_angle x)).
      assert (0 <= x <= 1) by lra. destruct (angle_01 x H0) as [H1 H2].
      pose proof half_le_PI2. lra.
    - pose proof half_le_PI2. assert (0 <= x <= 1) by lra.
      destruct (angle_01 x H0) as [_ H2]. lra. }
  replace (0 * (b - a)) with 0 in Hpos by ring. lra.
Qed.

Lemma cloth_Cy_mono_01 : forall a b, 0 <= a -> a <= b -> b <= 1 ->
  cloth_Cy a <= cloth_Cy b.
Proof.
  intros a b Ha Hab Hb.
  pose proof (cloth_Cy_diff a b Ha Hab Hb) as E.
  assert (Hpos : 0 * (b - a) <= int_seg fresnel_cy_integrand 1 a b Rle_0_1
            (fresnel_cy_lip_unit a b Ha Hab Hb)).
  { apply int_seg_ge_const; [exact Hab|]. intros x Hx.
    unfold fresnel_cy_integrand. apply sin_ge_0.
    - assert (0 <= x <= 1) by lra. apply (proj1 (angle_01 x H)).
    - assert (0 <= x <= 1) by lra.
      apply (proj2 (PI_ge_half_arg (fresnel_angle x) (angle_01 x H))). }
  replace (0 * (b - a)) with 0 in Hpos by ring. lra.
Qed.

Lemma cloth_Cx_le_1 : cloth_Cx 1 <= 1.
Proof.
  unfold cloth_Cx.
  assert (H : int_seg fresnel_cx_integrand (Rabs 1) 0 1 (Rabs_pos 1) (fresnel_cx_lip 1)
              <= 1 * (1 - 0)).
  { apply int_seg_le_const; [lra|]. intros x _.
    apply (proj2 (COS_bound (fresnel_angle x))). }
  nra.
Qed.

Lemma cloth_Cx_ge_7_8 : 7 / 8 <= cloth_Cx 1.
Proof.
  unfold cloth_Cx.
  assert (H : 7 / 8 * (1 - 0) <=
    int_seg fresnel_cx_integrand (Rabs 1) 0 1 (Rabs_pos 1) (fresnel_cx_lip 1)).
  { apply int_seg_ge_const; [lra|]. intros u Hu.
    assert (Hu01 : 0 <= u <= 1) by lra.
    apply Rle_trans with (1 - fresnel_angle u * fresnel_angle u / 2).
    - apply one_minus_sq_7_8.
      + apply (proj1 (angle_01 u Hu01)).
      + apply (proj2 (angle_01 u Hu01)).
    - apply cos_ge_quad; apply (angle_in_half (fresnel_angle u) (angle_01 u Hu01)). }
  nra.
Qed.

Lemma cloth_Cy_le_cube : forall s, 0 <= s -> s <= 1 -> cloth_Cy s <= s * s * s / 6.
Proof.
  intros s Hs0 Hs1.
  unfold cloth_Cy.
  assert (Hle : int_seg fresnel_cy_integrand (Rabs s) 0 s (Rabs_pos s) (fresnel_cy_lip s)
              <= int_seg fresnel_angle (Rabs s) 0 s (Rabs_pos s) (fresnel_angle_lip s)).
  { apply int_seg_mono; [exact Hs0|]. intros u Hu.
    unfold fresnel_cy_integrand. apply sin_le_arg.
    unfold fresnel_angle. nra. }
  rewrite (int_fresnel_angle s Hs0) in Hle.
  replace (s * s * s / 6) with (s ^ 3 / 6) by field. exact Hle.
Qed.

Lemma cloth_Cy_le_sixth : cloth_Cy 1 <= 1 / 6.
Proof.
  replace (1 / 6) with (1 * 1 * 1 / 6) by field.
  apply cloth_Cy_le_cube; lra.
Qed.

Lemma cloth_Cy_three_fifth_le : cloth_Cy (3 / 5) <= 27 / 750.
Proof.
  apply Rle_trans with ((3 / 5) * (3 / 5) * (3 / 5) / 6).
  - apply cloth_Cy_le_cube; lra.
  - nra.
Qed.

Lemma sixth_scale_lip : forall x y,
  Rmin 0 1 <= x <= Rmax 0 1 -> Rmin 0 1 <= y <= Rmax 0 1 ->
  Rabs (/ 48 * x ^ 6 - / 48 * y ^ 6) <= (1 / 8) * Rabs (x - y).
Proof.
  intros x y Hx Hy.
  replace (/ 48 * x ^ 6 - / 48 * y ^ 6) with (/ 48 * (x ^ 6 - y ^ 6)) by ring.
  rewrite Rabs_mult, (Rabs_right (/ 48)) by lra.
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [lra|].
    apply (pow6_lip 1 Rle_0_1 x y Hx Hy).
  - right. field.
Qed.

Lemma eighth_nonneg : 0 <= 1 / 8.
Proof. lra. Qed.

Lemma nine_eighth_nonneg : 0 <= 9 / 8.
Proof. lra. Qed.

Lemma low_lip : forall x y,
  Rmin 0 1 <= x <= Rmax 0 1 -> Rmin 0 1 <= y <= Rmax 0 1 ->
  Rabs ((fresnel_angle x - x ^ 6 / 48) - (fresnel_angle y - y ^ 6 / 48))
    <= (9 / 8) * Rabs (x - y).
Proof.
  intros x y Hx Hy.
  replace ((fresnel_angle x - x ^ 6 / 48) - (fresnel_angle y - y ^ 6 / 48))
    with ((fresnel_angle x - fresnel_angle y) + (/ 48 * y ^ 6 - / 48 * x ^ 6))
    by (unfold fresnel_angle, Rdiv; ring).
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite (Rabs_minus_sym (/ 48 * y ^ 6) (/ 48 * x ^ 6)).
  apply Rle_trans with (Rabs 1 * Rabs (x - y) + (1 / 8) * Rabs (x - y)).
  - apply Rplus_le_compat.
    + apply (fresnel_angle_lip 1 x y Hx Hy).
    + apply sixth_scale_lip; assumption.
  - rewrite (Rabs_right 1) by lra. right. field.
Qed.

Lemma opp_sixth_lip : forall x y,
  Rmin 0 1 <= x <= Rmax 0 1 -> Rmin 0 1 <= y <= Rmax 0 1 ->
  Rabs ((fun t => - (/ 48 * t ^ 6)) x - (fun t => - (/ 48 * t ^ 6)) y)
    <= (1 / 8) * Rabs (x - y).
Proof.
  intros x y Hx Hy. cbn.
  match goal with
  | |- Rabs ?d <= _ =>
      assert (E : d = - (/ 48 * x ^ 6 - / 48 * y ^ 6)) by (unfold Rdiv; ring)
  end.
  rewrite E. rewrite Rabs_Ropp.
  apply sixth_scale_lip; assumption.
Qed.

Lemma low_as_sum_lip : forall x y,
  Rmin 0 1 <= x <= Rmax 0 1 -> Rmin 0 1 <= y <= Rmax 0 1 ->
  Rabs ((fun t => fresnel_angle t + - (/ 48 * t ^ 6)) x -
        (fun t => fresnel_angle t + - (/ 48 * t ^ 6)) y)
    <= (9 / 8) * Rabs (x - y).
Proof.
  intros x y Hx Hy. cbn.
  match goal with
  | |- Rabs ?d <= _ =>
      assert (E : d =
        (fresnel_angle x - x ^ 6 / 48) - (fresnel_angle y - y ^ 6 / 48))
        by (unfold fresnel_angle, Rdiv; cbn; ring)
  end.
  rewrite E. apply low_lip; assumption.
Qed.

Lemma int_low_1 :
  int_seg (fun u => fresnel_angle u - u ^ 6 / 48) (9 / 8) 0 1
    nine_eighth_nonneg low_lip = 55 / 336.
Proof.
  assert (Eext : int_seg (fun u => fresnel_angle u - u ^ 6 / 48) (9 / 8) 0 1
            nine_eighth_nonneg low_lip
          = int_seg (fun t => fresnel_angle t + - (/ 48 * t ^ 6)) (9 / 8) 0 1
              nine_eighth_nonneg low_as_sum_lip).
  { apply int_seg_ext. intros x _. unfold fresnel_angle, Rdiv. ring. }
  rewrite Eext.
  rewrite (int_seg_plus fresnel_angle (fun t => - (/ 48 * t ^ 6))
            (Rabs 1) (1 / 8) (9 / 8) 0 1
            (Rabs_pos 1) (fresnel_angle_lip 1)
            eighth_nonneg opp_sixth_lip
            nine_eighth_nonneg low_as_sum_lip).
  rewrite (int_seg_opp (fun t => / 48 * t ^ 6) (1 / 8) 0 1
            eighth_nonneg sixth_scale_lip opp_sixth_lip).
  rewrite (int_seg_scal (fun u => u ^ 6) (/ 48) (1 / 8) (6 * 1 ^ 5) 0 1
            eighth_nonneg (pow6_L_nonneg 1 Rle_0_1)
            (pow6_lip 1 Rle_0_1) sixth_scale_lip).
  rewrite (int_fresnel_angle 1 Rle_0_1).
  rewrite (int_pow6 1 Rle_0_1).
  field.
Qed.

Lemma cloth_Cy_ge_55_336 : 55 / 336 <= cloth_Cy 1.
Proof.
  unfold cloth_Cy.
  assert (Hle : int_seg (fun u => fresnel_angle u - u ^ 6 / 48) (9 / 8) 0 1
                  nine_eighth_nonneg low_lip
              <= int_seg fresnel_cy_integrand (Rabs 1) 0 1
                  (Rabs_pos 1) (fresnel_cy_lip 1)).
  { apply int_seg_mono; [lra|]. intros u Hu.
    unfold fresnel_cy_integrand.
    assert (Hz : 0 <= fresnel_angle u <= PI).
    { assert (Hu01 : 0 <= u <= 1) by exact Hu.
      split.
      - apply (proj1 (angle_01 u Hu01)).
      - apply (proj2 (PI_ge_half_arg _ (angle_01 u Hu01))). }
    apply Rle_trans with
      (fresnel_angle u -
       fresnel_angle u * fresnel_angle u * fresnel_angle u / 6).
    - right. unfold fresnel_angle. field.
    - apply sin_ge_cubic. exact Hz. }
  rewrite int_low_1 in Hle. exact Hle.
Qed.

Lemma cloth_Cx_three_fifth_gt : 1 / 2 < cloth_Cx (3 / 5).
Proof.
  unfold cloth_Cx.
  assert (H : 4919 / 5000 * (3 / 5 - 0) <=
    int_seg fresnel_cx_integrand (Rabs (3 / 5)) 0 (3 / 5)
      (Rabs_pos (3 / 5)) (fresnel_cx_lip (3 / 5))).
  { apply int_seg_ge_const; [lra|]. intros u Hu.
    assert (Hu35 : 0 <= u <= 3 / 5) by lra.
    apply Rle_trans with (1 - fresnel_angle u * fresnel_angle u / 2).
    - apply one_minus_sq_4919.
      + unfold fresnel_angle. nra.
      + apply angle_le_9_50; lra.
    - apply cos_ge_quad.
      + pose proof half_le_PI2. unfold fresnel_angle. nra.
      + apply Rle_trans with (1 / 2); [|apply half_le_PI2].
        apply Rle_trans with (9 / 50); [apply angle_le_9_50; lra|lra]. }
  assert (1 / 2 < 4919 / 5000 * (3 / 5 - 0)).
  { assert (4919 / 5000 * (3 / 5 - 0) = 14757 / 25000) by field.
    assert (1 / 2 = 12500 / 25000) by field. lra. }
  lra.
Qed.

Lemma cloth_Cx_half_lt : cloth_Cx (1 / 2) < 1 / 2.
Proof.
  assert (Ha : 0 <= 1 / 4) by lra.
  assert (Hab : 1 / 4 <= 1 / 2) by lra.
  assert (Hb : 1 / 2 <= 1) by lra.
  assert (H0 : 0 <= 0) by lra.
  pose proof (cloth_Cx_diff (1 / 4) (1 / 2) Ha Hab Hb) as E.
  assert (H1 : cloth_Cx (1 / 4) <= 1 / 4).
  { unfold cloth_Cx.
    assert (int_seg fresnel_cx_integrand (Rabs (1 / 4)) 0 (1 / 4)
              (Rabs_pos (1 / 4)) (fresnel_cx_lip (1 / 4)) <= 1 * (1 / 4 - 0)).
    { apply int_seg_le_const; [lra|]. intros x _.
      apply (proj2 (COS_bound (fresnel_angle x))). }
    nra. }
  assert (Hcos : cos (1 / 32) <= 1 - 1 / 2048 + 1 / 25165824).
  { apply Rle_trans with (1 - (1 / 32) * (1 / 32) / 2
                          + (1 / 32) * (1 / 32) * (1 / 32) * (1 / 32) / 24).
    - apply cos_le_quart.
      + pose proof half_le_PI2. lra.
      + apply Rle_trans with (1 / 2); [lra | apply half_le_PI2].
    - assert ((1 / 32) * (1 / 32) / 2 = 1 / 2048) by field.
      assert ((1 / 32) * (1 / 32) * (1 / 32) * (1 / 32) / 24 = 1 / 25165824) by field.
      lra. }
  assert (H2 : int_seg fresnel_cx_integrand 1 (1 / 4) (1 / 2) Rle_0_1
                (fresnel_cx_lip_unit (1 / 4) (1 / 2) Ha Hab Hb)
              <= cos (1 / 32) * (1 / 2 - 1 / 4)).
  { apply int_seg_le_const; [exact Hab|]. intros u Hu.
    assert (Huq : 1 / 4 <= u <= 1 / 2) by lra.
    unfold fresnel_cx_integrand.
    apply cos_nonincreasing.
    - lra.
    - assert (fresnel_angle (1 / 4) = 1 / 32) by (unfold fresnel_angle; field).
      assert (fresnel_angle (1 / 4) <= fresnel_angle u).
      { unfold fresnel_angle. nra. }
      lra.
    - apply Rle_trans with (1 / 2); [|apply half_le_PI2].
      assert (fresnel_angle u <= 1 / 8).
      { unfold fresnel_angle. nra. }
      lra. }
  assert (cloth_Cx (1 / 4) +
          int_seg fresnel_cx_integrand 1 (1 / 4) (1 / 2) Rle_0_1
            (fresnel_cx_lip_unit (1 / 4) (1 / 2) Ha Hab Hb)
          <= 1 / 4 + (1 / 4) * (1 - 1 / 2048 + 1 / 25165824)).
  { apply Rplus_le_compat; [exact H1|].
    apply Rle_trans with ((1 / 4) * cos (1 / 32)).
    + eapply Rle_trans; [exact H2|]. right. field.
    + apply Rmult_le_compat_l; [lra | exact Hcos]. }
  assert (1 / 4 + (1 / 4) * (1 - 1 / 2048 + 1 / 25165824)
          = 50319361 / 100663296) by field.
  assert (1 / 2 = 50331648 / 100663296) by field.
  lra.
Qed.

Lemma cloth_Cx_cont_on : forall x, 1 / 2 <= x <= 3 / 5 -> continuity_pt cloth_Cx x.
Proof.
  intros x Hx.
  unfold continuity_pt, continue_in, limit1_in, limit_in.
  intros eps Heps.
  exists (Rmin eps (1 / 4)). split.
  - apply Rmin_glb_lt; [exact Heps | lra].
  - intros y [_ Hd].
    unfold dist, R_met, Rdist in Hd.
    assert (Hy : Rabs (y - x) < 1 / 4).
    { eapply Rlt_le_trans; [exact Hd | apply Rmin_r]. }
    apply Rabs_def2 in Hy.
    assert (Hy01 : 0 <= y <= 1) by lra.
    assert (Hx01 : 0 <= x <= 1) by lra.
    assert (Hclose : Rabs (cloth_Cx y - cloth_Cx x) <= Rabs (y - x)).
    { destruct (Rle_dec x y) as [Hxy|Hyx].
      - rewrite (cloth_Cx_diff x y (proj1 Hx01) Hxy (proj2 Hy01)).
        eapply Rle_trans.
        + apply int_seg_abs; [exact Hxy|].
          intros t _. unfold fresnel_cx_integrand.
          destruct (COS_bound (fresnel_angle t)) as [Hlo Hhi].
          apply Rabs_le. split; [exact Hlo|exact Hhi].
        + assert (Hnn : 0 <= y - x).
          { replace 0 with (x + - x) by ring.
            apply Rplus_le_compat_r. exact Hxy. }
          rewrite (Rabs_right (y - x) (Rle_ge _ _ Hnn)).
          rewrite Rmult_1_l. apply Rle_refl.
      - assert (Hyx' : y <= x) by (apply Rlt_le, Rnot_le_lt; exact Hyx).
        replace (cloth_Cx y - cloth_Cx x) with
          (- (cloth_Cx x - cloth_Cx y)) by ring.
        rewrite (cloth_Cx_diff y x (proj1 Hy01) Hyx' (proj2 Hx01)).
        rewrite Rabs_Ropp.
        eapply Rle_trans.
        + apply int_seg_abs; [exact Hyx'|].
          intros t _. unfold fresnel_cx_integrand.
          destruct (COS_bound (fresnel_angle t)) as [Hlo Hhi].
          apply Rabs_le. split; [exact Hlo|exact Hhi].
        + assert (Hnp : y - x <= 0).
          { replace 0 with (x + - x) by ring.
            apply Rplus_le_compat_r. exact Hyx'. }
          rewrite (Rabs_left1 (y - x) Hnp).
          replace (- (y - x)) with (x - y) by ring.
          rewrite Rmult_1_l. apply Rle_refl. }
    eapply Rle_lt_trans; [exact Hclose|].
    eapply Rlt_le_trans; [exact Hd | apply Rmin_l].
Qed.

Lemma cloth_axis_gap_cont : forall a, 1 / 2 <= a <= 3 / 5 ->
  continuity_pt (fun t => cloth_Cx t - 1 / 2) a.
Proof.
  intros a Ha.
  unfold continuity_pt, continue_in, limit1_in, limit_in.
  intros eps Heps.
  pose proof (cloth_Cx_cont_on a Ha) as Hc.
  unfold continuity_pt, continue_in, limit1_in, limit_in in Hc.
  destruct (Hc eps Heps) as [alp [Halp Hclose]].
  exists alp. split; [exact Halp|].
  intros y [Hy Hd].
  unfold dist, R_met, Rdist in *.
  replace ((cloth_Cx y - 1 / 2) - (cloth_Cx a - 1 / 2))
    with (cloth_Cx y - cloth_Cx a) by ring.
  apply Hclose. split; [exact Hy|exact Hd].
Qed.
