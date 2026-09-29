(* ============================================================================
   NetTopologySuite.Proofs.LipIntLeibniz
   ----------------------------------------------------------------------------
   Differentiation under the integral sign for the 3-axiom dyadic integral.
   The domain of integration is fixed.  The integrand may depend on the
   parameter.  A uniform modulus
     |(g(τ, L+k) - g(τ, L))/k - h(τ, L)| ≤ K·|k|
   turns the parameter derivative into pint of h.  No MVT, Rolle,
   RiemannInt, or Coquelicot.

   Also the interior form of RealMonotone: f′ > 0 on (a, b) and continuity
   on [a, b] give strict increase, including at the endpoints where a
   one-sided FTC does not supply a two-sided derivative.

   claimId: none.  Headline witness name: lint_leibniz.
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import LipInt LipIntFTC RealMonotone.
Local Open Scope R_scope.

Lemma cv_abs_bound :
  forall (u : nat -> R) (l B : R),
    (forall n, Rabs (u n) <= B) -> Un_cv u l -> Rabs l <= B.
Proof.
  intros u l B HB Hcv.
  destruct (Rle_dec (Rabs l) B) as [Hle|Hlt]; [exact Hle|].
  apply Rnot_le_lt in Hlt.
  destruct (Hcv (Rabs l - B) ltac:(lra)) as [N HN].
  specialize (HN N (le_n N)). unfold R_dist in HN.
  assert (Rabs l <= Rabs (u N - l) + Rabs (u N)).
  { set (a := u N).
    assert (E : a + - (a - l) = l) by ring.
    apply Rle_trans with (Rabs (- (u N - l)) + Rabs (u N)).
    - rewrite <- E at 1. rewrite Rplus_comm. apply Rabs_triang.
    - rewrite Rabs_Ropp. apply Rle_refl. }
  specialize (HB N). lra.
Qed.

Lemma lint_le :
  forall g h lo hi Lg Hg HLg Hlipg HHg Hlih a b Ha Hab Hb Ha2 Hab2 Hb2,
    (forall x, a <= x <= b -> g x <= h x) ->
    lint g lo hi Lg HLg Hlipg a b Ha Hab Hb <=
    lint h lo hi Hg HHg Hlih a b Ha2 Hab2 Hb2.
Proof.
  intros. apply lint_mono; assumption.
Qed.

Lemma lint_abs_le :
  forall g lo hi L HL Hlip a b Ha Hab Hb M,
    (forall x, a <= x <= b -> Rabs (g x) <= M) ->
    Rabs (lint g lo hi L HL Hlip a b Ha Hab Hb) <= M * (b - a).
Proof.
  intros. apply lint_abs; assumption.
Qed.

Lemma lint_linear :
  forall (g h : R -> R) (c d lo hi Lg Hg Ls Ld L : R)
    (HLg : 0 <= Lg)
    (Hlipg : forall x y, lo <= x <= hi -> lo <= y <= hi ->
               Rabs (g x - g y) <= Lg * Rabs (x - y))
    (HHg : 0 <= Hg)
    (Hlih : forall x y, lo <= x <= hi -> lo <= y <= hi ->
               Rabs (h x - h y) <= Hg * Rabs (x - y))
    (HLs : 0 <= Ls)
    (Hsc : forall x y, lo <= x <= hi -> lo <= y <= hi ->
             Rabs (c * g x - c * g y) <= Ls * Rabs (x - y))
    (HLd : 0 <= Ld)
    (Hsd : forall x y, lo <= x <= hi -> lo <= y <= hi ->
             Rabs (d * h x - d * h y) <= Ld * Rabs (x - y))
    (HL : 0 <= L)
    (Hsum : forall x y, lo <= x <= hi -> lo <= y <= hi ->
              Rabs ((c * g x + d * h x) - (c * g y + d * h y))
                <= L * Rabs (x - y))
    (a b : R) (Ha : lo <= a) (Hab : a <= b) (Hb : b <= hi),
    lint (fun x => c * g x + d * h x) lo hi L HL Hsum a b Ha Hab Hb =
    c * lint g lo hi Lg HLg Hlipg a b Ha Hab Hb +
    d * lint h lo hi Hg HHg Hlih a b Ha Hab Hb.
Proof.
  intros.
  rewrite (lint_plus (fun x => c * g x) (fun x => d * h x)
             lo hi Ls Ld L HLs Hsc HLd Hsd HL Hsum
             a b Ha Hab Hb Ha Hab Hb Ha Hab Hb).
  rewrite (lint_scal g c lo hi Ls Lg HLs HLg Hlipg Hsc
             a b Ha Hab Hb Ha Hab Hb).
  rewrite (lint_scal h d lo hi Ld Hg HLd HHg Hlih Hsd
             a b Ha Hab Hb Ha Hab Hb).
  reflexivity.
Qed.

(* g τ L, τ ∈ [0,1].  lipg L is a Lipschitz constant in τ. *)
Definition pint (g : R -> R -> R) (lipg : R -> R)
  (Hnonneg : forall L, 0 <= lipg L)
  (Hlip : forall L x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
            Rabs (g x L - g y L) <= lipg L * Rabs (x - y))
  (L : R) : R :=
  lint (fun t => g t L) 0 1 (lipg L) (Hnonneg L)
    (fun x y Hx Hy => Hlip L x y Hx Hy)
    0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1).

Lemma pint_ext :
  forall g lipg Hn Hlip L,
    pint g lipg Hn Hlip L =
    lint (fun t => g t L) 0 1 (lipg L) (Hn L)
      (fun x y Hx Hy => Hlip L x y Hx Hy)
      0 1 (Rle_refl 0) Rle_0_1 (Rle_refl 1).
Proof. reflexivity. Qed.

Lemma dyadic_param_quot :
  forall (g0 g1 h : R -> R) (k : R) (n : nat),
    k <> 0 ->
    dyadic (fun t => (g1 t - g0 t) / k - h t) n 0 1 =
    (dyadic g1 n 0 1 - dyadic g0 n 0 1) / k - dyadic h n 0 1.
Proof.
  intros g0 g1 h k n Hk.
  rewrite (dyadic_ext_on
             (fun t => (g1 t - g0 t) / k - h t)
             (fun t => / k * (g1 t + - g0 t) + - h t)
             n 0 1 Rle_0_1).
  - rewrite (dyadic_plus (fun t => / k * (g1 t + - g0 t)) (fun t => - h t) n 0 1).
    rewrite (dyadic_scal (fun t => g1 t + - g0 t) (/ k) n 0 1).
    rewrite (dyadic_plus g1 (fun t => - g0 t) n 0 1).
    rewrite (dyadic_opp g0 n 0 1).
    rewrite (dyadic_opp h n 0 1).
    unfold Rdiv, Rminus. ring.
  - intros t _. unfold Rdiv, Rminus. ring.
Qed.

Lemma lint_leibniz :
  forall (g h : R -> R -> R) (lipg liph : R -> R)
    (Hng : forall L, 0 <= lipg L)
    (Hlg : forall L x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
             Rabs (g x L - g y L) <= lipg L * Rabs (x - y))
    (Hnh : forall L, 0 <= liph L)
    (Hlh : forall L x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
             Rabs (h x L - h y L) <= liph L * Rabs (x - y))
    (L K delta : R),
    0 < delta ->
    0 <= K ->
    (forall tau k, 0 <= tau <= 1 -> k <> 0 -> Rabs k < delta ->
       Rabs ((g tau (L + k) - g tau L) / k - h tau L) <= K * Rabs k) ->
    derivable_pt_lim (pint g lipg Hng Hlg) L (pint h liph Hnh Hlh L).
Proof.
  intros g h lipg liph Hng Hlg Hnh Hlh L K delta Hdelta HK Hmod eps Heps.
  set (step := Rmin delta (eps / (K + 1))).
  assert (Hstep : 0 < step).
  { apply Rmin_pos; [exact Hdelta|]. apply Rdiv_lt_0_compat; lra. }
  exists (mkposreal step Hstep).
  intros k Hk Hlt. cbn [pos] in Hlt.
  assert (Hkd : Rabs k < delta).
  { eapply Rlt_le_trans; [exact Hlt|]. apply Rmin_l. }
  assert (Hek : K * Rabs k < eps).
  { assert (Hkeps : Rabs k < eps / (K + 1)).
    { eapply Rlt_le_trans; [exact Hlt|]. apply Rmin_r. }
    assert (Hscale : K * (eps / (K + 1)) <= eps).
    { unfold Rdiv. apply Rle_trans with ((K + 1) * (eps * / (K + 1))).
      - apply Rmult_le_compat_r.
        + apply Rmult_le_pos; [lra|]. apply Rlt_le, Rinv_0_lt_compat. lra.
        + lra.
      - right. field. lra. }
    destruct (Req_dec K 0) as [HK0|HKpos].
    - rewrite HK0. lra.
    - apply Rlt_le_trans with (K * (eps / (K + 1))); [| exact Hscale].
      apply Rmult_lt_compat_l; [lra | exact Hkeps]. }
  set (err := fun t => (g t (L + k) - g t L) / k - h t L).
  assert (Herr : forall t, 0 <= t <= 1 -> Rabs (err t) <= K * Rabs k).
  { intros t Ht. unfold err. apply Hmod; assumption. }
  assert (Hdy : forall n,
            Rabs ((dyadic (fun t => g t (L + k)) n 0 1
                   - dyadic (fun t => g t L) n 0 1) / k
                  - dyadic (fun t => h t L) n 0 1)
            <= K * Rabs k).
  { intro n. rewrite <- (dyadic_param_quot (fun t => g t L)
                         (fun t => g t (L + k)) (fun t => h t L) k n Hk).
    eapply Rle_trans.
    - apply dyadic_abs_bound; [apply Rle_0_1|].
      intros x Hx. apply Herr. exact Hx.
    - right. ring. }
  assert (Hcv : Un_cv
            (fun n =>
               (dyadic (fun t => g t (L + k)) n 0 1
                - dyadic (fun t => g t L) n 0 1) / k
               - dyadic (fun t => h t L) n 0 1)
            ((pint g lipg Hng Hlg (L + k) - pint g lipg Hng Hlg L) / k
             - pint h liph Hnh Hlh L)).
  { unfold Rdiv. apply CV_minus.
    - apply CV_mult.
      + apply CV_minus; apply lint_cv_dyadic.
      + apply seq_const.
    - apply lint_cv_dyadic. }
  apply Rle_lt_trans with (K * Rabs k); [| exact Hek].
  apply cv_abs_bound with
    (u := fun n =>
            (dyadic (fun t => g t (L + k)) n 0 1
             - dyadic (fun t => g t L) n 0 1) / k
            - dyadic (fun t => h t L) n 0 1);
    assumption.
Qed.

(* A function with derivative f agrees with the dyadic primitive. *)
Lemma prim_eq_delta :
  forall (f g : R -> R) (lo hi Lf : R)
    (HL : 0 <= Lf)
    (Hlip : forall x y, lo <= x <= hi -> lo <= y <= hi ->
              Rabs (f x - f y) <= Lf * Rabs (x - y))
    (a b : R),
    lo < a < hi ->
    lo < b < hi ->
    (forall t, lo < t < hi -> derivable_pt_lim g t (f t)) ->
    g b - g a = lipPrim f lo hi Lf HL Hlip a b.
Proof.
  intros f g lo hi Lf HL Hlip a b Ha Hb Hg.
  set (m := Rmin a b). set (M := Rmax a b).
  assert (Hm : lo < m /\ m <= M /\ M < hi).
  { unfold m, M. split; [| split].
    - apply Rmin_glb_lt; [apply Ha | apply Hb].
    - apply Rle_trans with a; [apply Rmin_l | apply Rmax_l].
    - apply Rmax_lub_lt; [apply Ha | apply Hb]. }
  set (Dlt := fun t => lipPrim f lo hi Lf HL Hlip a t - (g t - g a)).
  assert (Hder : forall t, m <= t <= M -> derivable_pt_lim Dlt t 0).
  { intros t Ht.
    assert (Hin : lo < t < hi) by lra.
    assert (Hp : derivable_pt_lim (lipPrim f lo hi Lf HL Hlip a) t (f t)).
    { apply lipPrim_ftc.
      - split; lra.
      - exact Hin. }
    assert (Hg' : derivable_pt_lim (fun z => g z - g a) t (f t)).
    { replace (f t) with (f t - 0) by ring.
      apply derivable_pt_lim_minus; [apply Hg; exact Hin | apply derivable_pt_lim_const]. }
    assert (Hsub : derivable_pt_lim
              (minus_fct (lipPrim f lo hi Lf HL Hlip a) (fun z => g z - g a))
              t (f t - f t)).
    { apply derivable_pt_lim_minus; assumption. }
    replace 0 with (f t - f t) by ring.
    eapply derivable_pt_lim_ext; [| exact Hsub].
    intros z. unfold minus_fct, Dlt. reflexivity. }
  assert (Hz : forall t, m <= t <= M -> 0 = 0) by (intros; reflexivity).
  assert (HDa : Dlt a = 0).
  { unfold Dlt.
    assert (Ha_in : lo <= a <= hi) by lra.
    rewrite (lipPrim_as_seg f lo hi Lf HL Hlip a a Ha_in Ha_in).
    rewrite int_seg_point. ring. }
  assert (Heq : Dlt a = Dlt b).
  { apply (deriv_zero_const Dlt (fun _ => 0) m M a b).
    - exact Hder.
    - intros t Ht. reflexivity.
    - unfold m, M. split; [apply Rmin_l | apply Rmax_l].
    - unfold m, M. split; [apply Rmin_r | apply Rmax_r]. }
  unfold Dlt in Heq, HDa.
  lra.
Qed.

Lemma scaled_sin_lip :
  forall c x y,
    Rabs (- c * sin (c * x) - - c * sin (c * y)) <= (c * c) * Rabs (x - y).
Proof.
  intros c x y.
  replace (- c * sin (c * x) - - c * sin (c * y))
    with (- c * (sin (c * x) - sin (c * y))) by ring.
  rewrite Rabs_mult.
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [apply Rabs_pos|]. apply sin_lip.
  - rewrite Rabs_Ropp.
    replace (c * x - c * y) with (c * (x - y)) by ring.
    rewrite Rabs_mult.
    rewrite <- Rmult_assoc.
    replace (Rabs c * Rabs c) with (c * c).
    + apply Rle_refl.
    + rewrite <- Rabs_mult.
      rewrite Rabs_right; [reflexivity|].
      apply Rle_ge, Rle_0_sqr.
Qed.

Lemma cos_lin_deriv :
  forall c x, derivable_pt_lim (fun u => cos (c * u)) x (- c * sin (c * x)).
Proof.
  intros c x.
  assert (Hsc : derivable_pt_lim (mult_real_fct c id) x (c * 1)).
  { apply derivable_pt_lim_scal. apply derivable_pt_lim_id. }
  assert (Hinner : derivable_pt_lim (fun u => c * u) x (c * 1)).
  { eapply derivable_pt_lim_ext; [| exact Hsc].
    intros z. unfold mult_real_fct, id. ring. }
  assert (Hcomp : derivable_pt_lim (comp cos (fun u => c * u)) x
                    ((- sin (c * x)) * (c * 1))).
  { apply derivable_pt_lim_comp; [exact Hinner | apply derivable_pt_lim_cos]. }
  replace (- c * sin (c * x)) with ((- sin (c * x)) * (c * 1)) by ring.
  eapply derivable_pt_lim_ext; [| exact Hcomp].
  intros z. unfold comp. reflexivity.
Qed.

Lemma cos_param_increment :
  forall c a b,
    cos (c * b) - cos (c * a) =
    lipPrim (fun t => - c * sin (c * t))
      (Rmin a b - 1) (Rmax a b + 1) (c * c)
      (Rle_0_sqr c)
      (fun x y _ _ => scaled_sin_lip c x y)
      a b.
Proof.
  intros c a b.
  apply (prim_eq_delta (fun t => - c * sin (c * t)) (fun u => cos (c * u))
           (Rmin a b - 1) (Rmax a b + 1) (c * c)
           (Rle_0_sqr c)
           (fun x y _ _ => scaled_sin_lip c x y)
           a b).
  - split.
    + apply Rlt_le_trans with (Rmin a b); [| apply Rmin_l].
      assert (Rmin a b - 1 < Rmin a b) by lra. exact H.
    + apply Rle_lt_trans with (Rmax a b); [apply Rmax_l|]. lra.
  - split.
    + apply Rlt_le_trans with (Rmin a b); [| apply Rmin_r]. lra.
    + apply Rle_lt_trans with (Rmax a b); [apply Rmax_r|]. lra.
  - intros t _. apply cos_lin_deriv.
Qed.

Lemma quot_abs_div :
  forall A B k,
    k <> 0 ->
    Rabs (A / k - B) = Rabs (A - k * B) / Rabs k.
Proof.
  intros A B k Hk.
  replace (A / k - B) with ((A - k * B) / k) by (field; exact Hk).
  unfold Rdiv. rewrite Rabs_mult, Rabs_inv by exact Hk. reflexivity.
Qed.

Lemma cos_quot_modulus :
  forall c x k,
    k <> 0 ->
    Rabs ((cos (c * (x + k)) - cos (c * x)) / k - (- c * sin (c * x)))
      <= (c * c) * Rabs k.
Proof.
  intros c x k Hk.
  set (A := cos (c * (x + k)) - cos (c * x)).
  set (B := - c * sin (c * x)).
  set (f := fun t => - c * sin (c * t)).
  assert (Hinc := cos_param_increment c x (x + k)).
  assert (Hbound : Rabs (A - k * B) <= (c * c) * k * k).
  { destruct (Rle_dec x (x + k)) as [Hup|Hdown].
    - set (HL := Rle_0_sqr c).
      assert (Hlint :
        Rabs (lint f x (x + k) (c * c) HL
                (fun p q (_ : x <= p <= x + k) (_ : x <= q <= x + k) =>
                   scaled_sin_lip c p q)
                x (x + k) (Rle_refl x) Hup (Rle_refl (x + k))
              - ((x + k) - x) * f x)
        <= (c * c) * ((x + k) - x) * ((x + k) - x)).
      { apply lint_dev.
        - split; lra.
        - intros t Ht. rewrite Rabs_right by lra. lra. }
      assert (Heq :
        A = lint f x (x + k) (c * c) HL
              (fun p q (_ : x <= p <= x + k) (_ : x <= q <= x + k) =>
                 scaled_sin_lip c p q)
              x (x + k) (Rle_refl x) Hup (Rle_refl (x + k))).
      { unfold A. rewrite Hinc. unfold f.
        assert (Hwin_x : Rmin x (x + k) - 1 <= x <= Rmax x (x + k) + 1).
        { split.
          - apply Rle_trans with (Rmin x (x + k)); [lra | apply Rmin_l].
          - apply Rle_trans with (Rmax x (x + k)); [apply Rmax_l | lra]. }
        assert (Hwin_k : Rmin x (x + k) - 1 <= x + k <= Rmax x (x + k) + 1).
        { split.
          - apply Rle_trans with (Rmin x (x + k)); [lra | apply Rmin_r].
          - apply Rle_trans with (Rmax x (x + k)); [apply Rmax_r | lra]. }
        rewrite (lipPrim_as_seg (fun t => - c * sin (c * t))
                   (Rmin x (x + k) - 1) (Rmax x (x + k) + 1) (c * c)
                   (Rle_0_sqr c) (fun p q _ _ => scaled_sin_lip c p q)
                   x (x + k) Hwin_x Hwin_k).
        unfold int_seg.
        destruct (Rle_dec x (x + k)) as [Hab|Hbad];
          [| exfalso; apply Hbad; exact Hup].
        apply lint_irrel_gen. }
      rewrite <- Heq in Hlint. unfold B, f.
      replace ((x + k) - x) with k in Hlint by ring.
      exact Hlint.
    - assert (Hvu : x + k <= x).
      { apply Rlt_le. apply Rnot_le_lt. exact Hdown. }
      set (HL := Rle_0_sqr c).
      assert (Hlint :
        Rabs (lint f (x + k) x (c * c) HL
                (fun p q (_ : x + k <= p <= x) (_ : x + k <= q <= x) =>
                   scaled_sin_lip c p q)
                (x + k) x (Rle_refl (x + k)) Hvu (Rle_refl x)
              - (x - (x + k)) * f x)
        <= (c * c) * (x - (x + k)) * (x - (x + k))).
      { apply lint_dev.
        - split; lra.
        - intros t Ht. rewrite Rabs_left1 by lra. lra. }
      assert (Hswap :
        lipPrim f (Rmin x (x + k) - 1) (Rmax x (x + k) + 1) (c * c)
          (Rle_0_sqr c) (fun p q _ _ => scaled_sin_lip c p q) x (x + k)
        = - lipPrim f (Rmin (x + k) x - 1) (Rmax (x + k) x + 1) (c * c)
            (Rle_0_sqr c) (fun p q _ _ => scaled_sin_lip c p q) (x + k) x).
      { assert (Hxw : Rmin x (x + k) - 1 <= x <= Rmax x (x + k) + 1).
        { split.
          - apply Rle_trans with (Rmin x (x + k)); [lra | apply Rmin_l].
          - apply Rle_trans with (Rmax x (x + k)); [apply Rmax_l | lra]. }
        assert (Hkw : Rmin x (x + k) - 1 <= x + k <= Rmax x (x + k) + 1).
        { split.
          - apply Rle_trans with (Rmin x (x + k)); [lra | apply Rmin_r].
          - apply Rle_trans with (Rmax x (x + k)); [apply Rmax_r | lra]. }
        assert (Hxw2 : Rmin (x + k) x - 1 <= x <= Rmax (x + k) x + 1).
        { split.
          - apply Rle_trans with (Rmin (x + k) x); [lra | apply Rmin_r].
          - apply Rle_trans with (Rmax (x + k) x); [apply Rmax_r | lra]. }
        assert (Hkw2 : Rmin (x + k) x - 1 <= x + k <= Rmax (x + k) x + 1).
        { split.
          - apply Rle_trans with (Rmin (x + k) x); [lra | apply Rmin_l].
          - apply Rle_trans with (Rmax (x + k) x); [apply Rmax_l | lra]. }
        rewrite (lipPrim_as_seg f (Rmin x (x + k) - 1) (Rmax x (x + k) + 1)
                   (c * c) (Rle_0_sqr c) (fun p q _ _ => scaled_sin_lip c p q)
                   x (x + k) Hxw Hkw).
        rewrite (lipPrim_as_seg f (Rmin (x + k) x - 1) (Rmax (x + k) x + 1)
                   (c * c) (Rle_0_sqr c) (fun p q _ _ => scaled_sin_lip c p q)
                   (x + k) x Hkw2 Hxw2).
        apply int_seg_swap. }
      assert (Heq_fwd :
        cos (c * x) - cos (c * (x + k)) =
        lint f (x + k) x (c * c) HL
          (fun p q (_ : x + k <= p <= x) (_ : x + k <= q <= x) =>
             scaled_sin_lip c p q)
          (x + k) x (Rle_refl (x + k)) Hvu (Rle_refl x)).
      { replace (cos (c * x) - cos (c * (x + k)))
          with (- (cos (c * (x + k)) - cos (c * x))) by ring.
        rewrite Hinc. unfold f in Hswap. rewrite Hswap.
        assert (Hkw' : Rmin (x + k) x - 1 <= x + k <= Rmax (x + k) x + 1).
        { split.
          - apply Rle_trans with (Rmin (x + k) x); [lra | apply Rmin_l].
          - apply Rle_trans with (Rmax (x + k) x); [apply Rmax_l | lra]. }
        assert (Hxw' : Rmin (x + k) x - 1 <= x <= Rmax (x + k) x + 1).
        { split.
          - apply Rle_trans with (Rmin (x + k) x); [lra | apply Rmin_r].
          - apply Rle_trans with (Rmax (x + k) x); [apply Rmax_r | lra]. }
        rewrite (lipPrim_as_seg (fun t => - c * sin (c * t))
                   (Rmin (x + k) x - 1) (Rmax (x + k) x + 1) (c * c)
                   (Rle_0_sqr c) (fun p q _ _ => scaled_sin_lip c p q)
                   (x + k) x Hkw' Hxw').
        unfold int_seg.
        destruct (Rle_dec (x + k) x) as [Hab|Hbad];
          [| exfalso; apply Hbad; exact Hvu].
        rewrite Ropp_involutive. apply lint_irrel_gen. }
      rewrite <- Heq_fwd in Hlint.
      replace (x - (x + k)) with (- k) in Hlint by ring.
      unfold A, B, f in *.
      replace (cos (c * x) - cos (c * (x + k)) - (- k) * (- c * sin (c * x)))
        with (- (A - k * B)) in Hlint by (unfold A, B; ring).
      rewrite Rabs_Ropp in Hlint.
      replace (c * c * - k * - k) with (c * c * k * k) in Hlint by ring.
      exact Hlint. }
  assert (Hbound' : Rabs (A - k * B) <= (c * c) * (k * k)).
  { apply Rle_trans with ((c * c) * k * k); [exact Hbound |].
    right. ring. }
  assert (Ekk : k * k = Rabs k * Rabs k).
  { symmetry. rewrite <- Rabs_mult.
    apply Rabs_right. apply Rle_ge, Rle_0_sqr. }
  rewrite (quot_abs_div A B k Hk).
  unfold Rdiv. rewrite Ekk in Hbound'.
  apply Rle_trans with (((c * c) * (Rabs k * Rabs k)) * / Rabs k).
  - apply Rmult_le_compat_r.
    + apply Rlt_le. apply Rinv_0_lt_compat. apply Rabs_pos_lt. exact Hk.
    + exact Hbound'.
  - right. field. apply Rabs_no_R0. exact Hk.
Qed.

Lemma sin_as_cos :
  forall z, sin z = cos (PI / 2 - z).
Proof.
  intro z. rewrite cos_minus, cos_PI2, sin_PI2. ring.
Qed.

Lemma cos_as_sin :
  forall z, cos z = sin (PI / 2 - z).
Proof.
  intro z. rewrite sin_minus, sin_PI2, cos_PI2. ring.
Qed.

Lemma sin_quot_modulus :
  forall c x k,
    k <> 0 ->
    Rabs ((sin (c * (x + k)) - sin (c * x)) / k - c * cos (c * x))
      <= (c * c) * Rabs k.
Proof.
  intros c x k Hk.
  destruct (Req_dec c 0) as [Hc0|Hc].
  - subst c.
    rewrite !Rmult_0_l, !sin_0.
    replace ((0 - 0) / k - 0) with 0 by (field; exact Hk).
    rewrite Rabs_R0. apply Rle_refl.
  - set (c' := - c).
    set (x' := x - (PI / 2) * / c).
    assert (Hx' : c' * x' = PI / 2 - c * x).
    { unfold c', x'. field. exact Hc. }
    assert (Hxk : c' * (x' + k) = PI / 2 - c * (x + k)).
    { unfold c', x'. field. exact Hc. }
    assert (Hcos := cos_quot_modulus c' x' k Hk).
    replace (sin (c * (x + k))) with (cos (c' * (x' + k)))
      by (rewrite Hxk, sin_as_cos; reflexivity).
    replace (sin (c * x)) with (cos (c' * x'))
      by (rewrite Hx', sin_as_cos; reflexivity).
    replace (c * cos (c * x)) with (- c' * sin (c' * x')).
    + replace (c' * c') with (c * c) in Hcos by (unfold c'; ring). exact Hcos.
    + rewrite cos_as_sin. rewrite <- Hx'. unfold c'. ring.
Qed.

Definition seg_continuous (f : R -> R) (a b : R) : Prop :=
  forall t, a <= t <= b ->
    forall eps, 0 < eps ->
      exists delta, 0 < delta /\
        forall h, Rabs h < delta -> a <= t + h <= b ->
          Rabs (f (t + h) - f t) < eps.

Lemma deriv_pos_interior :
  forall f f' a b p q,
    (forall t, a < t < b -> derivable_pt_lim f t (f' t)) ->
    (forall t, a < t < b -> 0 < f' t) ->
    a < p -> p < q -> q < b ->
    f p < f q.
Proof.
  intros f f' a b p q Hd Hp Hap Hpq Hqb.
  apply (deriv_pos_strict_incr f f' p q p q).
  - intros t Ht. apply Hd. lra.
  - intros t Ht. apply Hp. lra.
  - lra.
  - exact Hpq.
  - lra.
Qed.

Lemma cont_not_above :
  forall f a b u,
    seg_continuous f a b ->
    a < u <= b ->
    (forall t, a < t < u -> f t < f u) ->
    f a <= f u.
Proof.
  intros f a b u Hc Hau Hincr.
  destruct (Rle_dec (f a) (f u)) as [Hle|Hgt]; [exact Hle|].
  assert (Hfu : f u < f a) by (apply Rnot_le_lt; exact Hgt).
  set (eps := f a - f u).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  destruct (Hc a ltac:(lra) eps Heps) as [delta [Hd Hdelta]].
  set (h := Rmin (delta / 2) ((u - a) / 2)).
  assert (Hh : 0 < h < delta /\ a + h < u).
  { split.
    - split; [apply Rmin_pos; lra |].
      apply Rle_lt_trans with (delta / 2); [apply Rmin_l | lra].
    - apply Rle_lt_trans with (a + (u - a) / 2).
      + apply Rplus_le_compat_l. apply Rmin_r.
      + replace (a + (u - a) / 2) with ((a + u) / 2) by field. lra. }
  assert (Hclose : Rabs (f (a + h) - f a) < eps).
  { apply Hdelta; [rewrite Rabs_right; lra | lra]. }
  assert (Hft : f u < f (a + h)).
  { unfold eps in Hclose. apply Rabs_def2 in Hclose. lra. }
  assert (Hlow : f (a + h) < f u).
  { apply Hincr. lra. }
  lra.
Qed.

Lemma cont_not_below :
  forall f a b v,
    seg_continuous f a b ->
    a <= v < b ->
    (forall t, v < t < b -> f v < f t) ->
    f v <= f b.
Proof.
  intros f a b v Hc Hvb Hincr.
  destruct (Rle_dec (f v) (f b)) as [Hle|Hgt]; [exact Hle|].
  assert (Hfb : f b < f v) by (apply Rnot_le_lt; exact Hgt).
  set (eps := f v - f b).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  destruct (Hc b ltac:(lra) eps Heps) as [delta [Hd Hdelta]].
  set (h := Rmin (delta / 2) ((b - v) / 2)).
  assert (Hh : 0 < h).
  { apply Rmin_pos; lra. }
  assert (Hhdelta : h < delta).
  { apply Rle_lt_trans with (delta / 2); [apply Rmin_l | lra]. }
  assert (Hclose : Rabs (f (b + - h) - f b) < eps).
  { apply Hdelta.
    - rewrite Rabs_Ropp. rewrite Rabs_right.
      + exact Hhdelta.
      + apply Rle_ge. apply Rlt_le. exact Hh.
    - split.
      + apply Rle_trans with (b - (b - v) / 2).
        * replace (b - (b - v) / 2) with ((b + v) / 2) by field.
          apply Rle_trans with v; [exact (proj1 Hvb) | lra].
        * apply Rplus_le_compat_l. apply Ropp_le_contravar. apply Rmin_r.
      + lra. }
  assert (Hft : f (b - h) < f v).
  { replace (b + - h) with (b - h) in Hclose by ring.
    unfold eps in Hclose. apply Rabs_def2 in Hclose. lra. }
  assert (Hhigh : f v < f (b - h)).
  { apply Hincr. split.
    - apply Rlt_le_trans with (b - (b - v) / 2).
      + replace (b - (b - v) / 2) with ((b + v) / 2) by field. lra.
      + apply Rplus_le_compat_l. apply Ropp_le_contravar. apply Rmin_r.
    - lra. }
  lra.
Qed.

Theorem deriv_pos_strict_incr_open :
  forall f f' a b x y,
    a < b ->
    (forall t, a < t < b -> derivable_pt_lim f t (f' t)) ->
    (forall t, a < t < b -> 0 < f' t) ->
    seg_continuous f a b ->
    a <= x -> x < y -> y <= b ->
    f x < f y.
Proof.
  intros f f' a b x y Hab Hd Hp Hc Hax Hxy Hyb.
  destruct (Rle_lt_dec x a) as [Hxa|Hax'].
  - assert (Hx : x = a) by lra.
    subst x.
    destruct (Rlt_dec y b) as [Hyb'|Hyb_eq].
    + set (u := (a + y) / 2).
      assert (Hu : a < u < y) by (unfold u; lra).
      assert (Hfu : f a <= f u).
      { apply (cont_not_above f a b u Hc); [lra|].
        intros t Ht. apply (deriv_pos_interior f f' a b t u); assumption || lra. }
      assert (Huy : f u < f y).
      { apply (deriv_pos_interior f f' a b u y); assumption || lra. }
      lra.
    + assert (Hy : y = b) by lra. subst y.
      set (u := a + (b - a) / 3).
      set (v := a + 2 * (b - a) / 3).
      assert (Huv : a < u /\ u < v /\ v < b) by (unfold u, v; lra).
      assert (Hau : f a <= f u).
      { apply (cont_not_above f a b u Hc); [lra|].
        intros t Ht. apply (deriv_pos_interior f f' a b t u); assumption || lra. }
      assert (Huvf : f u < f v).
      { apply (deriv_pos_interior f f' a b u v); assumption || lra. }
      assert (Hvb : f v <= f b).
      { apply (cont_not_below f a b v Hc); [lra|].
        intros t Ht. apply (deriv_pos_interior f f' a b v t); assumption || lra. }
      lra.
  - destruct (Rlt_dec y b) as [Hyb'|Hyeq].
    + apply (deriv_pos_interior f f' a b x y); assumption || lra.
    + assert (Hy : y = b) by lra. subst y.
      set (v := (x + b) / 2).
      assert (Hv : x < v < b) by (unfold v; lra).
      assert (Hxv : f x < f v).
      { apply (deriv_pos_interior f f' a b x v); assumption || lra. }
      assert (Hvb : f v <= f b).
      { apply (cont_not_below f a b v Hc); [lra|].
        intros t Ht. apply (deriv_pos_interior f f' a b v t); assumption || lra. }
      lra.
Qed.

Print Assumptions cv_abs_bound.
Print Assumptions lint_le.
Print Assumptions lint_abs_le.
Print Assumptions lint_linear.
Print Assumptions pint_ext.
Print Assumptions dyadic_param_quot.
Print Assumptions lint_leibniz.
Print Assumptions prim_eq_delta.
Print Assumptions scaled_sin_lip.
Print Assumptions cos_lin_deriv.
Print Assumptions cos_param_increment.
Print Assumptions quot_abs_div.
Print Assumptions cos_quot_modulus.
Print Assumptions sin_as_cos.
Print Assumptions cos_as_sin.
Print Assumptions sin_quot_modulus.
Print Assumptions deriv_pos_interior.
Print Assumptions cont_not_above.
Print Assumptions cont_not_below.
Print Assumptions deriv_pos_strict_incr_open.
