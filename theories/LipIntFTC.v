(* ============================================================================
   NetTopologySuite.Proofs.LipIntFTC
   ----------------------------------------------------------------------------
   Fundamental theorem for the 3-axiom Lipschitz dyadic integral.

   For f Lipschitz on [lo, hi], the primitive
     F(x) = lint f lo x
   (lipF below; 0 outside the interval, so the carrier is a total R -> R)
   satisfies, with no RiemannInt and no mean value theorem:

     * |F(x) - F(y)| <= M |x - y| when |f| <= M on the interval,
       and the explicit bound M = |f(lo)| + L |hi - lo|;
     * F is continuous along [lo, hi], and as a total function at each
       interior point;
     * derivable_pt_lim F x (f x) for lo < x < hi;
     * one-sided derivatives at the endpoints (derivable_pt_lim_right at
       lo, derivable_pt_lim_left at hi).

   lipPrim is the same primitive with an interior anchor. Its derivative
   is still f, which is the form the clothoid arc-length integral needs
   (anchor 0, Lipschitz window a neighbourhood of the station).

   Stdlib MVT / MVT_cor1 / MVT_cor2 / Rolle print Classical_Prop.classic,
   so none of them is used. The secant estimate is the dyadic Lipschitz
   bound: |int_x^{x+h} (f - f(x))| <= L h^2.

   Halley d/dL (ClothoidResidual H_deriv, H_fprime_pos) is not this
   theorem: that residual differentiates under the integral in the
   length parameter. H_mvt stays a premise for the same classic reason.
   claimId: none.
   No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import LipInt.
Local Open Scope R_scope.

Definition derivable_pt_lim_right (f : R -> R) (x l : R) : Prop :=
  forall eps : R, 0 < eps ->
    exists delta : R, 0 < delta /\
      forall h : R, 0 < h < delta ->
        Rabs ((f (x + h) - f x) / h - l) < eps.

Definition derivable_pt_lim_left (f : R -> R) (x l : R) : Prop :=
  forall eps : R, 0 < eps ->
    exists delta : R, 0 < delta /\
      forall h : R, 0 < h < delta ->
        Rabs ((f (x - h) - f x) / - h - l) < eps.

Section Prim.
Variable f : R -> R.
Variables lo hi L : R.
Hypothesis HL : 0 <= L.
Hypothesis Hlip : forall x y, lo <= x <= hi -> lo <= y <= hi ->
  Rabs (f x - f y) <= L * Rabs (x - y).

Lemma clip :
  forall p q x y,
    lo <= p <= hi -> lo <= q <= hi ->
    Rmin p q <= x <= Rmax p q ->
    Rmin p q <= y <= Rmax p q ->
    Rabs (f x - f y) <= L * Rabs (x - y).
Proof.
  intros p q x y Hp Hq Hx Hy.
  apply Hlip.
  - split.
    + apply Rle_trans with (Rmin p q); [| exact (proj1 Hx)].
      apply Rmin_glb; [exact (proj1 Hp) | exact (proj1 Hq)].
    + apply Rle_trans with (Rmax p q); [exact (proj2 Hx) |].
      apply Rmax_lub; [exact (proj2 Hp) | exact (proj2 Hq)].
  - split.
    + apply Rle_trans with (Rmin p q); [| exact (proj1 Hy)].
      apply Rmin_glb; [exact (proj1 Hp) | exact (proj1 Hq)].
    + apply Rle_trans with (Rmax p q); [exact (proj2 Hy) |].
      apply Rmax_lub; [exact (proj2 Hp) | exact (proj2 Hq)].
Qed.

Definition clip_on (p q : R) (Hp : lo <= p <= hi) (Hq : lo <= q <= hi)
  : forall x y,
      Rmin p q <= x <= Rmax p q ->
      Rmin p q <= y <= Rmax p q ->
      Rabs (f x - f y) <= L * Rabs (x - y) :=
  fun x y Hx Hy => clip p q x y Hp Hq Hx Hy.

(* F(x) = lint_lo^x f on the Lipschitz interval, else 0. *)
Definition lipF (x : R) : R :=
  match Rle_dec lo x with
  | left Hlox =>
      match Rle_dec x hi with
      | left Hxhi =>
          lint f lo hi L HL Hlip lo x (Rle_refl lo) Hlox Hxhi
      | right _ => 0
      end
  | right _ => 0
  end.

Lemma lipF_lint :
  forall x (Hlox : lo <= x) (Hxhi : x <= hi),
    lipF x = lint f lo hi L HL Hlip lo x (Rle_refl lo) Hlox Hxhi.
Proof.
  intros x Hlox Hxhi.
  unfold lipF.
  destruct (Rle_dec lo x) as [H1|H1]; [| exfalso; exact (H1 Hlox)].
  destruct (Rle_dec x hi) as [H2|H2]; [| exfalso; exact (H2 Hxhi)].
  apply lint_pi.
Qed.

Lemma lipF_as_seg :
  forall x (Hx : lo <= x <= hi),
    lipF x =
    int_seg f L lo x HL
      (clip_on lo x
         (conj (Rle_refl lo) (Rle_trans lo x hi (proj1 Hx) (proj2 Hx)))
         Hx).
Proof.
  intros x Hx.
  rewrite (lipF_lint x (proj1 Hx) (proj2 Hx)).
  unfold int_seg.
  destruct (Rle_dec lo x) as [Hok|Hbad]; [| exfalso; exact (Hbad (proj1 Hx))].
  apply lint_irrel_gen.
Qed.

(* Oriented primitive with an arbitrary anchor inside the window. *)
Definition lipPrim (anchor x : R) : R :=
  match Rle_dec lo anchor with
  | left Ha =>
      match Rle_dec anchor hi with
      | left Hb =>
          match Rle_dec lo x with
          | left Hx =>
              match Rle_dec x hi with
              | left Hy =>
                  int_seg f L anchor x HL
                    (clip_on anchor x (conj Ha Hb) (conj Hx Hy))
              | right _ => 0
              end
          | right _ => 0
          end
      | right _ => 0
      end
  | right _ => 0
  end.

Lemma lipPrim_as_seg :
  forall anchor x (Ha : lo <= anchor <= hi) (Hx : lo <= x <= hi),
    lipPrim anchor x =
    int_seg f L anchor x HL (clip_on anchor x Ha Hx).
Proof.
  intros anchor x Ha Hx.
  unfold lipPrim.
  destruct (Rle_dec lo anchor) as [A|A]; [| exfalso; exact (A (proj1 Ha))].
  destruct (Rle_dec anchor hi) as [B|B]; [| exfalso; exact (B (proj2 Ha))].
  destruct (Rle_dec lo x) as [C|C]; [| exfalso; exact (C (proj1 Hx))].
  destruct (Rle_dec x hi) as [D|D]; [| exfalso; exact (D (proj2 Hx))].
  apply int_seg_pi.
Qed.

Lemma lipPrim_chasles :
  forall anchor x,
    lo <= anchor <= hi -> lo <= x <= hi ->
    lipPrim anchor x = lipF x - lipF anchor.
Proof.
  intros anchor x Ha Hx.
  assert (Eanch : lipF anchor =
    int_seg f L lo anchor HL
      (clip_on lo anchor
         (conj (Rle_refl lo) (Rle_trans lo anchor hi (proj1 Ha) (proj2 Ha)))
         Ha)).
  { apply lipF_as_seg. }
  assert (Ex : lipF x =
    int_seg f L lo x HL
      (clip_on lo x
         (conj (Rle_refl lo) (Rle_trans lo x hi (proj1 Hx) (proj2 Hx)))
         Hx)).
  { apply lipF_as_seg. }
  assert (Ep : lipPrim anchor x =
    int_seg f L anchor x HL (clip_on anchor x Ha Hx)).
  { apply lipPrim_as_seg. }
  destruct (Rle_dec anchor x) as [Hax|Hxa].
  - assert (Hadd :=
      int_seg_add f L lo anchor x HL
        (clip_on lo x
           (conj (Rle_refl lo) (Rle_trans lo x hi (proj1 Hx) (proj2 Hx)))
           Hx)
        (clip_on lo anchor
           (conj (Rle_refl lo) (Rle_trans lo anchor hi (proj1 Ha) (proj2 Ha)))
           Ha)
        (clip_on anchor x Ha Hx)
        (proj1 Ha) Hax).
    lra.
  - assert (Hle : x <= anchor).
    { apply Rlt_le. apply Rnot_le_lt. exact Hxa. }
    assert (Hadd :=
      int_seg_add f L lo x anchor HL
        (clip_on lo anchor
           (conj (Rle_refl lo) (Rle_trans lo anchor hi (proj1 Ha) (proj2 Ha)))
           Ha)
        (clip_on lo x
           (conj (Rle_refl lo) (Rle_trans lo x hi (proj1 Hx) (proj2 Hx)))
           Hx)
        (clip_on x anchor Hx Ha)
        (proj1 Hx) Hle).
    assert (Hsw :=
      int_seg_swap f L anchor x HL
        (clip_on anchor x Ha Hx) (clip_on x anchor Hx Ha)).
    lra.
Qed.

Lemma lint_sub_const :
  forall (c : R)
    (Hlipd : forall x y, lo <= x <= hi -> lo <= y <= hi ->
        Rabs ((f x - c) - (f y - c)) <= L * Rabs (x - y))
    u v (Hu : lo <= u) (Huv : u <= v) (Hv : v <= hi),
    lint (fun t => f t - c) lo hi L HL Hlipd u v Hu Huv Hv =
    lint f lo hi L HL Hlip u v Hu Huv Hv - (v - u) * c.
Proof.
  intros c Hlipd u v Hu Huv Hv.
  apply UL_sequence with (fun n => dyadic (fun t => f t - c) n u v).
  - apply lint_cv_dyadic.
  - apply seq_ext with (u := fun n => dyadic f n u v - (v - u) * c).
    + intro n. symmetry.
      transitivity (dyadic (fun t => f t + (- c)) n u v).
      * apply dyadic_ext_on; [exact Huv |]. intros t _. ring.
      * rewrite (dyadic_plus f (fun _ : R => - c) n u v).
        rewrite (dyadic_const (- c) n u v Huv).
        rewrite <- Ropp_mult_distr_r.
        unfold Rminus. reflexivity.
    + apply CV_minus.
      * apply lint_cv_dyadic.
      * apply seq_const.
Qed.

Lemma lint_dev :
  forall x0 u v (Hu : lo <= u) (Huv : u <= v) (Hv : v <= hi),
    lo <= x0 <= hi ->
    (forall t, u <= t <= v -> Rabs (t - x0) <= v - u) ->
    Rabs (lint f lo hi L HL Hlip u v Hu Huv Hv - (v - u) * f x0)
      <= L * (v - u) * (v - u).
Proof.
  intros x0 u v Hu Huv Hv Hx0 Hnear.
  assert (Hlipd : forall a b, lo <= a <= hi -> lo <= b <= hi ->
      Rabs ((f a - f x0) - (f b - f x0)) <= L * Rabs (a - b)).
  { intros a b Ha Hb.
    replace ((f a - f x0) - (f b - f x0)) with (f a - f b) by ring.
    apply Hlip; assumption. }
  rewrite <- (lint_sub_const (f x0) Hlipd u v Hu Huv Hv).
  eapply Rle_trans.
  - apply lint_abs with (M := L * (v - u)).
    intros t Ht.
    assert (Htwin : lo <= t <= hi).
    { split.
      - apply Rle_trans with u; [exact Hu | exact (proj1 Ht)].
      - apply Rle_trans with v; [exact (proj2 Ht) | exact Hv]. }
    eapply Rle_trans.
    + apply Hlip; [exact Htwin | exact Hx0].
    + apply Rmult_le_compat_l; [exact HL | apply Hnear; exact Ht].
  - right. ring.
Qed.

Lemma lip_quot_eps :
  forall eps h, 0 < eps -> Rabs h < eps / (L + 1) -> L * Rabs h < eps.
Proof.
  intros eps h Heps Hh.
  assert (Hwide : (L + 1) * Rabs h < eps).
  { replace eps with ((L + 1) * (eps / (L + 1))).
    - apply Rmult_lt_compat_l; [lra | exact Hh].
    - field. lra. }
  eapply Rle_lt_trans; [| exact Hwide].
  apply Rmult_le_compat_r; [apply Rabs_pos | lra].
Qed.

Lemma lipF_secant :
  forall x h,
    lo <= x <= hi ->
    lo <= x + h <= hi ->
    h <> 0 ->
    Rabs ((lipF (x + h) - lipF x) / h - f x) <= L * Rabs h.
Proof.
  intros x h Hx Hh Hnz.
  destruct (Rle_dec 0 h) as [Hnn|Hneg].
  - assert (Hhpos : 0 < h) by lra.
    assert (Hle : x <= x + h) by lra.
    set (Hlo := Rle_trans lo lo x (Rle_refl lo) (proj1 Hx)).
    assert (Eadd : lipF (x + h) - lipF x =
        lint f lo hi L HL Hlip x (x + h) Hlo Hle (proj2 Hh)).
    { rewrite (lipF_lint (x + h) (proj1 Hh) (proj2 Hh)).
      rewrite (lipF_lint x (proj1 Hx) (proj2 Hx)).
      rewrite (lint_add f lo hi L HL Hlip lo x (x + h)
                 (Rle_refl lo) (proj1 Hx) (proj2 Hx)
                 (proj1 Hh) (proj2 Hh) Hle).
      unfold Hlo. ring. }
    assert (Hdev0 :
        Rabs (lint f lo hi L HL Hlip x (x + h) Hlo Hle (proj2 Hh)
              - ((x + h) - x) * f x)
        <= L * ((x + h) - x) * ((x + h) - x)).
    { apply lint_dev; [exact Hx |].
      intros t Ht. rewrite Rabs_right; lra. }
    assert (Hdev :
        Rabs (lint f lo hi L HL Hlip x (x + h) Hlo Hle (proj2 Hh) - h * f x)
        <= L * h * h).
    { replace ((x + h) - x) with h in Hdev0 by ring. exact Hdev0. }
    assert (Hq :
        (lipF (x + h) - lipF x) / h - f x =
        (lint f lo hi L HL Hlip x (x + h) Hlo Hle (proj2 Hh) - h * f x) / h).
    { rewrite Eadd. field. exact Hnz. }
    rewrite Hq. unfold Rdiv. rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (/ h));
      [| apply Rlt_le, Rinv_0_lt_compat; exact Hhpos].
    apply Rle_trans with ((L * h * h) * / h).
    + apply Rmult_le_compat_r.
      * apply Rlt_le, Rinv_0_lt_compat. exact Hhpos.
      * exact Hdev.
    + rewrite (Rabs_right h) by lra. right. field. lra.
  - assert (Hlt : h < 0) by (apply Rnot_le_lt; exact Hneg).
    assert (Hback : x + h <= x) by lra.
    set (Hlo := Rle_trans lo lo (x + h) (Rle_refl lo) (proj1 Hh)).
    assert (Eadd : lipF x - lipF (x + h) =
        lint f lo hi L HL Hlip (x + h) x Hlo Hback (proj2 Hx)).
    { rewrite (lipF_lint x (proj1 Hx) (proj2 Hx)).
      rewrite (lipF_lint (x + h) (proj1 Hh) (proj2 Hh)).
      rewrite (lint_add f lo hi L HL Hlip lo (x + h) x
                 (Rle_refl lo) (proj1 Hh) (proj2 Hh)
                 (proj1 Hx) (proj2 Hx) Hback).
      unfold Hlo. ring. }
    assert (Hdev :
        Rabs (lint f lo hi L HL Hlip (x + h) x Hlo Hback (proj2 Hx)
              - (x - (x + h)) * f x)
        <= L * (x - (x + h)) * (x - (x + h))).
    { apply lint_dev; [exact Hx |].
      intros t Ht. rewrite Rabs_left1; lra. }
    assert (Hq :
        (lipF (x + h) - lipF x) / h - f x =
        (lint f lo hi L HL Hlip (x + h) x Hlo Hback (proj2 Hx)
          - (x - (x + h)) * f x) / (x - (x + h))).
    { replace (lipF (x + h) - lipF x)
        with (- (lipF x - lipF (x + h))) by ring.
      rewrite Eadd. field. lra. }
    rewrite Hq. unfold Rdiv. rewrite Rabs_mult.
    assert (Hlen : 0 < x - (x + h)) by lra.
    rewrite (Rabs_pos_eq (/ (x - (x + h))));
      [| apply Rlt_le, Rinv_0_lt_compat; exact Hlen].
    apply Rle_trans with
      ((L * (x - (x + h)) * (x - (x + h))) * / (x - (x + h))).
    + apply Rmult_le_compat_r.
      * apply Rlt_le, Rinv_0_lt_compat. exact Hlen.
      * exact Hdev.
    + replace (x - (x + h)) with (Rabs h) by (rewrite Rabs_left; lra).
      right. field. apply Rabs_no_R0. exact Hnz.
Qed.

Lemma lip_ftc :
  forall x, lo < x < hi -> derivable_pt_lim lipF x (f x).
Proof.
  intros x Hx eps Heps.
  set (room := Rmin (x - lo) (hi - x)).
  set (delta := Rmin room (eps / (L + 1))).
  assert (Hroom : 0 < room) by (apply Rmin_pos; lra).
  assert (Hstep : 0 < eps / (L + 1)) by (apply Rdiv_lt_0_compat; lra).
  assert (Hd : 0 < delta) by (apply Rmin_pos; assumption).
  exists (mkposreal delta Hd).
  intros h Hnz Hh. cbn [pos] in Hh.
  assert (Hin : lo <= x + h <= hi).
  { assert (Habs : Rabs h < room).
    { eapply Rlt_le_trans; [exact Hh | unfold room; apply Rmin_l]. }
    destruct (Rabs_def2 _ _ Habs) as [HhiH HloH].
    split; apply Rlt_le.
    - assert (Hneg : -(x - lo) < h).
      { apply Rle_lt_trans with (- room); [| exact HloH].
        apply Ropp_le_contravar. unfold room. apply Rmin_l. }
      apply Rplus_lt_compat_l with (r := x) in Hneg.
      replace (x + - (x - lo)) with lo in Hneg by ring.
      exact Hneg.
    - assert (Hpos : h < hi - x).
      { apply Rlt_le_trans with room; [exact HhiH | unfold room; apply Rmin_r]. }
      apply Rplus_lt_compat_l with (r := x) in Hpos.
      replace (x + (hi - x)) with hi in Hpos by ring.
      exact Hpos. }
  assert (Hxin : lo <= x <= hi) by lra.
  eapply Rle_lt_trans.
  - apply (lipF_secant x h Hxin Hin Hnz).
  - apply lip_quot_eps; [exact Heps |].
    eapply Rlt_le_trans; [exact Hh | apply Rmin_r].
Qed.

Lemma lip_ftc_right :
  lo < hi -> derivable_pt_lim_right lipF lo (f lo).
Proof.
  intros Hlt eps Heps.
  set (delta := Rmin (hi - lo) (eps / (L + 1))).
  assert (Hstep : 0 < eps / (L + 1)) by (apply Rdiv_lt_0_compat; lra).
  assert (Hd : 0 < delta) by (apply Rmin_pos; lra).
  exists delta. split; [exact Hd |].
  intros h Hh.
  destruct Hh as [Hhpos Hhsmall].
  assert (Hspan : h < hi - lo).
  { eapply Rlt_le_trans; [exact Hhsmall | unfold delta; apply Rmin_l]. }
  assert (Hin : lo <= lo + h <= hi).
  { split; apply Rlt_le.
    - assert (Hhpos' := Hhpos).
      apply Rplus_lt_compat_l with (r := lo) in Hhpos'.
      replace (lo + 0) with lo in Hhpos' by ring.
      exact Hhpos'.
    - apply Rplus_lt_compat_l with (r := lo) in Hspan.
      replace (lo + (hi - lo)) with hi in Hspan by ring.
      exact Hspan. }
  assert (Hlo : lo <= lo <= hi) by (split; lra).
  eapply Rle_lt_trans.
  - apply lipF_secant; [exact Hlo | exact Hin | lra].
  - apply lip_quot_eps; [exact Heps |].
    assert (Hnn : 0 <= h) by (apply Rlt_le; exact Hhpos).
    rewrite (Rabs_pos_eq h Hnn).
    eapply Rlt_le_trans; [exact Hhsmall | unfold delta; apply Rmin_r].
Qed.

Lemma lip_ftc_left :
  lo < hi -> derivable_pt_lim_left lipF hi (f hi).
Proof.
  intros Hlt eps Heps.
  set (delta := Rmin (hi - lo) (eps / (L + 1))).
  assert (Hstep : 0 < eps / (L + 1)) by (apply Rdiv_lt_0_compat; lra).
  assert (Hd : 0 < delta) by (apply Rmin_pos; lra).
  exists delta. split; [exact Hd |].
  intros h Hh.
  destruct Hh as [Hhpos Hhsmall].
  assert (Hspan : h < hi - lo).
  { eapply Rlt_le_trans; [exact Hhsmall | unfold delta; apply Rmin_l]. }
  assert (Hin : lo <= hi - h <= hi).
  { split; apply Rlt_le.
    - assert (Hspan' := Hspan).
      apply Ropp_lt_contravar in Hspan'.
      apply Rplus_lt_compat_l with (r := hi) in Hspan'.
      replace (hi + - (hi - lo)) with lo in Hspan' by ring.
      replace (hi + - h) with (hi - h) in Hspan' by ring.
      exact Hspan'.
    - assert (Hhneg := Hhpos).
      apply Ropp_lt_contravar in Hhneg.
      apply Rplus_lt_compat_l with (r := hi) in Hhneg.
      replace (hi + - h) with (hi - h) in Hhneg by ring.
      replace (hi + - 0) with hi in Hhneg by ring.
      exact Hhneg. }
  assert (Hhi : lo <= hi <= hi) by (split; lra).
  assert (Hnz : - h <> 0).
  { intro Heq. apply Rplus_eq_compat_r with (r := h) in Heq.
    rewrite Rplus_opp_l, Rplus_0_l in Heq. lra. }
  eapply Rle_lt_trans.
  - replace (hi - h) with (hi + (- h)) by ring.
    apply (lipF_secant hi (- h) Hhi Hin Hnz).
  - apply lip_quot_eps; [exact Heps |].
    assert (Hnn : 0 <= h) by (apply Rlt_le; exact Hhpos).
    rewrite Rabs_Ropp, (Rabs_pos_eq h Hnn).
    eapply Rlt_le_trans; [exact Hhsmall | unfold delta; apply Rmin_r].
Qed.

Lemma lip_bounded :
  forall t, lo <= t <= hi ->
    Rabs (f t) <= Rabs (f lo) + L * (hi - lo).
Proof.
  intros t Ht.
  assert (Hgap : Rabs (f t - f lo) <= L * (hi - lo)).
  { eapply Rle_trans.
    - apply Hlip; [exact Ht | split; lra].
    - rewrite (Rabs_right (t - lo)) by lra.
      apply Rmult_le_compat_l; [exact HL | lra]. }
  replace (f t) with (f lo + (f t - f lo)) by ring.
  eapply Rle_trans; [apply Rabs_triang |].
  apply Rplus_le_compat_l. exact Hgap.
Qed.

Lemma lipF_lip :
  forall M x y,
    (forall t, lo <= t <= hi -> Rabs (f t) <= M) ->
    lo <= x <= hi -> lo <= y <= hi ->
    Rabs (lipF x - lipF y) <= M * Rabs (x - y).
Proof.
  intros M x y HM Hx Hy.
  destruct (Rle_dec x y) as [Hxy|Hyx].
  - set (Hlo := Rle_trans lo lo x (Rle_refl lo) (proj1 Hx)).
    assert (E : lipF y - lipF x =
        lint f lo hi L HL Hlip x y Hlo Hxy (proj2 Hy)).
    { rewrite (lipF_lint y (proj1 Hy) (proj2 Hy)).
      rewrite (lipF_lint x (proj1 Hx) (proj2 Hx)).
      rewrite (lint_add f lo hi L HL Hlip lo x y
                 (Rle_refl lo) (proj1 Hx) (proj2 Hx)
                 (proj1 Hy) (proj2 Hy) Hxy).
      unfold Hlo. ring. }
    rewrite Rabs_minus_sym. rewrite E.
    eapply Rle_trans.
    + apply lint_abs. intros t Ht. apply HM.
      split.
      * apply Rle_trans with x; [exact (proj1 Hx) | exact (proj1 Ht)].
      * apply Rle_trans with y; [exact (proj2 Ht) | exact (proj2 Hy)].
    + rewrite (Rabs_minus_sym x y).
      rewrite (Rabs_right (y - x)) by lra. right. ring.
  - assert (Hyx' : y <= x) by (apply Rlt_le, Rnot_le_lt; exact Hyx).
    set (Hlo := Rle_trans lo lo y (Rle_refl lo) (proj1 Hy)).
    assert (E : lipF x - lipF y =
        lint f lo hi L HL Hlip y x Hlo Hyx' (proj2 Hx)).
    { rewrite (lipF_lint x (proj1 Hx) (proj2 Hx)).
      rewrite (lipF_lint y (proj1 Hy) (proj2 Hy)).
      rewrite (lint_add f lo hi L HL Hlip lo y x
                 (Rle_refl lo) (proj1 Hy) (proj2 Hy)
                 (proj1 Hx) (proj2 Hx) Hyx').
      unfold Hlo. ring. }
    rewrite E.
    eapply Rle_trans.
    + apply lint_abs. intros t Ht. apply HM.
      split.
      * apply Rle_trans with y; [exact (proj1 Hy) | exact (proj1 Ht)].
      * apply Rle_trans with x; [exact (proj2 Ht) | exact (proj2 Hx)].
    + rewrite (Rabs_right (x - y)) by lra. right. ring.
Qed.

Lemma lipF_continuous :
  forall x eps,
    lo <= x <= hi -> 0 < eps ->
    exists delta : R, 0 < delta /\
      forall y, lo <= y <= hi -> Rabs (y - x) < delta ->
        Rabs (lipF y - lipF x) < eps.
Proof.
  intros x eps Hx Heps.
  set (M := Rabs (f lo) + L * (hi - lo)).
  assert (HM : forall t, lo <= t <= hi -> Rabs (f t) <= M).
  { intros t Ht. unfold M. apply lip_bounded. exact Ht. }
  assert (HMn : 0 <= M).
  { unfold M. apply Rplus_le_le_0_compat; [apply Rabs_pos |].
    apply Rmult_le_pos; [exact HL |].
    destruct Hx as [Hxlo Hxhi].
    assert (Hord : lo <= hi).
    { apply Rle_trans with x; [exact Hxlo | exact Hxhi]. }
    apply Rplus_le_compat_r with (r := - lo) in Hord.
    replace (lo + - lo) with 0 in Hord by ring.
    replace (hi + - lo) with (hi - lo) in Hord by ring.
    exact Hord. }
  assert (HM1 : 0 < M + 1) by (apply Rplus_le_lt_0_compat; [exact HMn | lra]).
  set (delta := eps / (M + 1)).
  assert (Hd : 0 < delta).
  { unfold delta. apply Rdiv_lt_0_compat; [exact Heps | exact HM1]. }
  exists delta. split; [exact Hd |].
  intros y Hy Hdist.
  assert (Hle : Rabs (lipF y - lipF x) <= (M + 1) * Rabs (y - x)).
  { eapply Rle_trans.
    - apply lipF_lip; [exact HM | exact Hy | exact Hx].
    - apply Rmult_le_compat_r; [apply Rabs_pos |].
      rewrite <- (Rplus_0_r M) at 1.
      apply Rplus_le_compat_l. apply Rlt_le. exact Rlt_0_1. }
  assert (Hlt : (M + 1) * Rabs (y - x) < eps).
  { replace eps with ((M + 1) * delta).
    - apply Rmult_lt_compat_l; [exact HM1 | exact Hdist].
    - unfold delta. field. exact (Rgt_not_eq _ _ HM1). }
  eapply Rle_lt_trans; [exact Hle | exact Hlt].
Qed.

Lemma lipF_continuous_interior :
  forall x eps, lo < x < hi -> 0 < eps ->
    exists delta : R, 0 < delta /\
      forall h, Rabs h < delta -> Rabs (lipF (x + h) - lipF x) < eps.
Proof.
  intros x eps Hx Heps.
  destruct (lipF_continuous x eps
              (conj (Rlt_le _ _ (proj1 Hx)) (Rlt_le _ _ (proj2 Hx))) Heps)
    as [d1 [Hd1 Hcont]].
  set (room := Rmin (x - lo) (hi - x)).
  assert (Hroom : 0 < room) by (apply Rmin_pos; lra).
  exists (Rmin d1 room).
  split; [apply Rmin_pos; assumption |].
  intros h Hh.
  assert (Hin : lo <= x + h <= hi).
  { assert (Habs : Rabs h < room).
    { eapply Rlt_le_trans; [exact Hh | unfold room; apply Rmin_r]. }
    destruct (Rabs_def2 _ _ Habs) as [HhiH HloH].
    split; apply Rlt_le.
    - assert (Hneg : -(x - lo) < h).
      { apply Rle_lt_trans with (- room); [| exact HloH].
        apply Ropp_le_contravar. unfold room. apply Rmin_l. }
      apply Rplus_lt_compat_l with (r := x) in Hneg.
      replace (x + - (x - lo)) with lo in Hneg by ring.
      exact Hneg.
    - assert (Hpos : h < hi - x).
      { apply Rlt_le_trans with room; [exact HhiH | unfold room; apply Rmin_r]. }
      apply Rplus_lt_compat_l with (r := x) in Hpos.
      replace (x + (hi - x)) with hi in Hpos by ring.
      exact Hpos. }
  apply Hcont; [exact Hin |].
  replace (x + h - x) with h by ring.
  eapply Rlt_le_trans; [exact Hh | apply Rmin_l].
Qed.

Lemma lipPrim_ftc :
  forall anchor x,
    lo <= anchor <= hi ->
    lo < x < hi ->
    derivable_pt_lim (lipPrim anchor) x (f x).
Proof.
  intros anchor x Ha Hx.
  assert (Hd : derivable_pt_lim lipF x (f x)) by (apply lip_ftc; exact Hx).
  assert (Hm : derivable_pt_lim (minus_fct lipF (fct_cte (lipF anchor))) x (f x)).
  { replace (f x) with (f x - 0) by ring.
    apply derivable_pt_lim_minus.
    - exact Hd.
    - apply derivable_pt_lim_const. }
  apply derivable_pt_lim_locally_ext with
      (f := minus_fct lipF (fct_cte (lipF anchor))) (a := lo) (b := hi).
  - exact Hx.
  - intros z Hz.
    unfold minus_fct, fct_cte.
    rewrite (lipPrim_chasles anchor z Ha).
    + ring.
    + split; lra.
  - exact Hm.
Qed.

End Prim.

Print Assumptions clip.
Print Assumptions lipF_lint.
Print Assumptions lipF_as_seg.
Print Assumptions lipPrim_as_seg.
Print Assumptions lipPrim_chasles.
Print Assumptions lint_sub_const.
Print Assumptions lint_dev.
Print Assumptions lip_quot_eps.
Print Assumptions lipF_secant.
Print Assumptions lip_ftc.
Print Assumptions lip_ftc_right.
Print Assumptions lip_ftc_left.
Print Assumptions lip_bounded.
Print Assumptions lipF_lip.
Print Assumptions lipF_continuous.
Print Assumptions lipF_continuous_interior.
Print Assumptions lipPrim_ftc.
