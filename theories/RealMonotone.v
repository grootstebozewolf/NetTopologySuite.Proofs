(* ============================================================================
   NetTopologySuite.Proofs.RealMonotone
   ----------------------------------------------------------------------------
   Interval monotonicity from the sign of a derivative, from Stdlib
   `completeness` (sup of the good set).  Not from `MVT` or `Rolle`.

   `MVT`, `MVT_cor1`, `MVT_cor2` and `Rolle` print `Classical_Prop.classic`.
   `completeness` and `R_complete` print only the corpus trio
   (sig_not_dec, sig_forall_dec, functional_extensionality_dep).

   Hypothesis shape: two-sided `derivable_pt_lim` on the closed interval,
   endpoints included (same shape as `ClothoidResidual.H_deriv`).  Pointwise
   `f' > 0` is strict increase; `f' = 0` is constancy; `f' >= 0` is
   non-strict increase (the last two by an `eps * id` perturbation).

   Equality-form MVT (`f b - f a = f' c * (b - a)`) is not proved.  The
   Halley residual only needs the strict-increase consequence.

   claimId: none
   No Admitted, no Axiom, no Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (Cursor cloud agent)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From Stdlib Require Import Ranalysis1.

Open Scope R_scope.

(* x in [a,b] at which f has already risen strictly above f(a) on (a,x]. *)
Definition incr_good (f : R -> R) (a b x : R) : Prop :=
  a <= x <= b /\ forall t, a < t <= x -> f a < f t.

Lemma incr_good_down :
  forall f a b x y, incr_good f a b x -> a <= y <= x -> incr_good f a b y.
Proof.
  intros f a b x y [[Hax Hxb] Hall] [Hay Hyx].
  split; [split; [exact Hay | apply Rle_trans with x; assumption] |].
  intros t [Hat Hty]. apply Hall. split; [exact Hat | apply Rle_trans with y; assumption].
Qed.

Lemma incr_good_stable :
  forall f a b x, ~~ incr_good f a b x -> incr_good f a b x.
Proof.
  intros f a b x Hdn.
  destruct (Rle_dec a x) as [Hax | Hax].
  - destruct (Rle_dec x b) as [Hxb | Hxb].
    + split; [split; assumption |].
      intros t Ht.
      destruct (Rlt_dec (f a) (f t)) as [Hlt | Hlt]; [exact Hlt |].
      exfalso. apply Hdn. intro Hg. apply Hlt. apply Hg. exact Ht.
    + exfalso. apply Hdn. intro Hg. apply Hxb. apply Hg.
  - exfalso. apply Hdn. intro Hg. apply Hax. apply Hg.
Qed.

(* A non-upper-bound sits strictly below some element.  Order is decidable,
   so the classical witness is only double-negated; stability of [incr_good]
   absorbs that. *)
Lemma not_ub_dn_above :
  forall (E : R -> Prop) (m : R),
    ~ is_upper_bound E m -> ~~ exists x, E x /\ m < x.
Proof.
  intros E m Hub Hex. apply Hub. intros x Hx.
  destruct (Rle_lt_dec x m) as [Hle | Hlt]; [exact Hle |].
  exfalso. apply Hex. exists x. split; assumption.
Qed.

Lemma incr_good_below_lub :
  forall f a b c t,
    is_lub (incr_good f a b) c -> a <= t < c -> incr_good f a b t.
Proof.
  intros f a b c t [Hub Hleast] [Hat Htc].
  apply incr_good_stable. intro Hn.
  assert (Hdn : ~~ exists x, incr_good f a b x /\ t < x).
  { apply not_ub_dn_above. intro Hubt.
    apply (Rlt_not_le c t); [exact Htc | apply Hleast; exact Hubt]. }
  apply Hdn. intros [x [Hx Htx]]. apply Hn.
  apply incr_good_down with x; [exact Hx | split; [exact Hat | apply Rlt_le, Htx]].
Qed.

Lemma quot_pos_right :
  forall (f : R -> R) (x l h : R),
    0 < h -> 0 < l ->
    Rabs ((f (x + h) - f x) / h - l) < l / 2 ->
    f x < f (x + h).
Proof.
  intros f x l h Hh Hl Habs.
  destruct (Rabs_def2 _ _ Habs) as [_ Hlo].
  set (q := (f (x + h) - f x) / h).
  assert (Hq : l / 2 < q) by (unfold q; lra).
  assert (Heq : f (x + h) - f x = q * h) by (unfold q; field; lra).
  assert (0 < q * h) by (apply Rmult_lt_0_compat; lra).
  lra.
Qed.

Lemma quot_pos_left :
  forall (f : R -> R) (x l h : R),
    0 < h -> 0 < l ->
    Rabs ((f (x - h) - f x) / (- h) - l) < l / 2 ->
    f (x - h) < f x.
Proof.
  intros f x l h Hh Hl Habs.
  destruct (Rabs_def2 _ _ Habs) as [_ Hlo].
  set (q := (f (x - h) - f x) / (- h)).
  assert (Hq : l / 2 < q) by (unfold q; lra).
  assert (Heq : f (x - h) - f x = q * (- h)) by (unfold q; field; lra).
  assert (0 < q * h) by (apply Rmult_lt_0_compat; lra).
  assert (q * (- h) = - (q * h)) by ring.
  lra.
Qed.

Lemma deriv_pos_right_rise :
  forall (f : R -> R) (x l d : R),
    derivable_pt_lim f x l -> 0 < l -> 0 < d ->
    exists h, 0 < h < d /\ forall t, x < t < x + h -> f x < f t.
Proof.
  intros f x l d Hd Hl Hdpos.
  assert (Hhalf : 0 < l / 2) by lra.
  destruct (Hd (l / 2) Hhalf) as [delta Hdelta].
  assert (Hdp : 0 < delta) by apply cond_pos.
  set (h := Rmin (delta / 2) (d / 2)).
  assert (Hh : 0 < h < d).
  { split.
    - apply Rmin_pos; lra.
    - apply Rle_lt_trans with (d / 2); [apply Rmin_r | lra]. }
  exists h. split; [exact Hh |].
  intros t [Hxt Hth].
  set (step := t - x).
  assert (Hs : 0 < step < delta).
  { unfold step. split; [lra |].
    apply Rlt_le_trans with h; [lra |].
    apply Rle_trans with (delta / 2); [apply Rmin_l | lra]. }
  assert (Hstep : Rabs ((f (x + step) - f x) / step - l) < l / 2).
  { apply Hdelta; [unfold step; lra |].
    rewrite Rabs_pos_eq by (unfold step; lra). exact (proj2 Hs). }
  replace t with (x + step) by (unfold step; lra).
  apply (quot_pos_right f x l step (proj1 Hs) Hl Hstep).
Qed.

Lemma deriv_pos_left_fall :
  forall (f : R -> R) (x l d : R),
    derivable_pt_lim f x l -> 0 < l -> 0 < d ->
    exists h, 0 < h < d /\ forall t, x - h < t < x -> f t < f x.
Proof.
  intros f x l d Hd Hl Hdpos.
  assert (Hhalf : 0 < l / 2) by lra.
  destruct (Hd (l / 2) Hhalf) as [delta Hdelta].
  assert (Hdp : 0 < delta) by apply cond_pos.
  set (h := Rmin (delta / 2) (d / 2)).
  assert (Hh : 0 < h < d).
  { split; [apply Rmin_pos; lra | apply Rle_lt_trans with (d / 2); [apply Rmin_r | lra]]. }
  exists h. split; [exact Hh |].
  intros t [Hth Htx].
  set (step := x - t).
  assert (Hs : 0 < step < delta).
  { unfold step. split; [lra | apply Rlt_le_trans with h; [lra | apply Rle_trans with (delta / 2); [apply Rmin_l | lra]]]. }
  assert (Hstep : Rabs ((f (x - step) - f x) / (- step) - l) < l / 2).
  { apply Hdelta; [unfold step; lra |].
    rewrite Rabs_Ropp, Rabs_pos_eq by (unfold step; lra). exact (proj2 Hs). }
  replace t with (x - step) by (unfold step; lra).
  apply (quot_pos_left f x l step (proj1 Hs) Hl Hstep).
Qed.

(* Sup of [incr_good]: the least point that has not yet been passed is b,
   and f has risen on the whole of (a,b]. *)
Lemma deriv_pos_lt_endpoints :
  forall (f f' : R -> R) (a b : R),
    a < b ->
    (forall t, a <= t <= b -> derivable_pt_lim f t (f' t)) ->
    (forall t, a <= t <= b -> 0 < f' t) ->
    f a < f b.
Proof.
  intros f f' a b Hab Hder Hpos.
  assert (Hbnd : bound (incr_good f a b)).
  { exists b. intros x [[_ Hxb] _]. exact Hxb. }
  assert (Hinhab : exists x, incr_good f a b x).
  { exists a. split; [split; lra |]. intros t Ht. exfalso. lra. }
  destruct (completeness (incr_good f a b) Hbnd Hinhab) as [c Hc].
  destruct Hc as [Hub Hleast].
  assert (Hc_le_b : c <= b).
  { apply Hleast. intros x [[_ Hxb] _]. exact Hxb. }
  assert (Ha_good : incr_good f a b a).
  { split; [split; lra |]. intros t Ht. exfalso. lra. }
  assert (Ha_lt_c : a < c).
  { destruct (deriv_pos_right_rise f a (f' a) (b - a)
        (Hder a ltac:(lra)) (Hpos a ltac:(lra)) ltac:(lra))
      as [h [Hh Hrise]].
    set (y := a + h / 2).
    assert (Hy : incr_good f a b y).
    { unfold y. split; [split; lra |]. intros t Ht. apply Hrise. lra. }
    apply Rlt_le_trans with y; [unfold y; lra | apply Hub; exact Hy]. }
  assert (Hfac : f a < f c).
  { destruct (Rlt_dec (f a) (f c)) as [Hlt | Hge]; [exact Hlt |].
    exfalso.
    assert (Hle : f c <= f a) by (apply Rnot_lt_le; exact Hge).
    destruct (deriv_pos_left_fall f c (f' c) (c - a)
        (Hder c ltac:(lra)) (Hpos c ltac:(lra)) ltac:(lra))
      as [h [Hh Hfall]].
    set (t := c - h / 2).
    assert (Ht : a < t < c) by (unfold t; lra).
    assert (Htg : incr_good f a b t).
    { apply incr_good_below_lub with c; [split; assumption | lra]. }
    assert (Hft : f a < f t) by (apply Htg; lra).
    assert (Htc : f t < f c) by (apply Hfall; unfold t; lra).
    lra. }
  assert (Hc_good : incr_good f a b c).
  { split; [split; lra |]. intros t Ht.
    destruct (Rle_lt_dec t c) as [Htc | Hct].
    - destruct (Req_dec t c) as [Heq | Hne].
      + subst t. exact Hfac.
      + assert (Htg : incr_good f a b t).
        { apply incr_good_below_lub with c; [split; assumption | lra]. }
        apply Htg. lra.
    - lra. }
  assert (Hc_eq : c = b).
  { destruct (Rlt_dec c b) as [Hlt | Hge].
    - exfalso.
      destruct (deriv_pos_right_rise f c (f' c) (b - c)
          (Hder c ltac:(lra)) (Hpos c ltac:(lra)) ltac:(lra))
        as [h [Hh Hrise]].
      set (y := c + h / 2).
      assert (Hy : incr_good f a b y).
      { unfold y. split; [split; lra |]. intros t Ht.
        destruct (Rle_lt_dec t c) as [Htc | Hct].
        - apply Hc_good. lra.
        - assert (Hft : f c < f t) by (apply Hrise; lra).
          lra. }
      assert (Hy_le : y <= c) by (apply Hub; exact Hy).
      unfold y in Hy_le. lra.
    - apply Rle_antisym; [exact Hc_le_b | apply Rnot_lt_le; exact Hge]. }
  subst c. apply Hc_good. lra.
Qed.

Theorem deriv_pos_strict_incr :
  forall (f f' : R -> R) (a b x y : R),
    (forall t, a <= t <= b -> derivable_pt_lim f t (f' t)) ->
    (forall t, a <= t <= b -> 0 < f' t) ->
    a <= x -> x < y -> y <= b ->
    f x < f y.
Proof.
  intros f f' a b x y Hder Hpos Hax Hxy Hyb.
  apply (deriv_pos_lt_endpoints f f' x y Hxy).
  - intros t Ht. apply Hder. lra.
  - intros t Ht. apply Hpos. lra.
Qed.

Lemma deriv_pt_add_linear :
  forall (f : R -> R) (x lf eps : R),
    derivable_pt_lim f x lf ->
    derivable_pt_lim (fun z => f z + eps * z) x (lf + eps).
Proof.
  intros f x lf eps Hd.
  assert (Hid : derivable_pt_lim (fun z : R => z) x 1).
  { eapply derivable_pt_lim_ext; [| apply derivable_pt_lim_id].
    intros z. unfold id. reflexivity. }
  assert (Hsum : derivable_pt_lim
           (plus_fct f (mult_real_fct eps (fun z : R => z))) x (lf + eps * 1)).
  { apply derivable_pt_lim_plus; [exact Hd | apply derivable_pt_lim_scal; exact Hid]. }
  replace (lf + eps) with (lf + eps * 1) by lra.
  eapply derivable_pt_lim_ext; [| exact Hsum].
  intros z. unfold plus_fct, mult_real_fct. ring.
Qed.

Lemma Rle_of_lt_all_pos :
  forall d : R, (forall eps, 0 < eps -> - eps < d) -> 0 <= d.
Proof.
  intros d H.
  destruct (Rle_lt_dec 0 d) as [Hle | Hlt]; [exact Hle |].
  specialize (H (- d) ltac:(lra)). lra.
Qed.

Theorem deriv_nonneg_incr :
  forall (f f' : R -> R) (a b x y : R),
    (forall t, a <= t <= b -> derivable_pt_lim f t (f' t)) ->
    (forall t, a <= t <= b -> 0 <= f' t) ->
    a <= x -> x <= y -> y <= b ->
    f x <= f y.
Proof.
  intros f f' a b x y Hder Hnn Hax Hxy Hyb.
  destruct (Rle_lt_dec y x) as [Hyx | Hlt].
  - assert (Heq : x = y) by lra. subst y. apply Rle_refl.
  - assert (0 <= f y - f x); [| lra].
    apply Rle_of_lt_all_pos. intros eta Heta.
    set (eps := eta / (y - x)).
    assert (Heps : 0 < eps).
    { unfold eps. apply Rmult_lt_0_compat; [exact Heta | apply Rinv_0_lt_compat; lra]. }
    assert (Hrise : f x + eps * x < f y + eps * y).
    { apply (deriv_pos_strict_incr (fun z => f z + eps * z)
               (fun t => f' t + eps) x y x y).
      - intros t Ht. apply deriv_pt_add_linear. apply Hder. lra.
      - intros t Ht. assert (0 <= f' t) by (apply Hnn; lra). lra.
      - lra. - exact Hlt. - lra. }
    assert (Hgap : - eps * (y - x) < f y - f x) by lra.
    unfold eps in Hgap.
    replace (- (eta / (y - x)) * (y - x)) with (- eta) in Hgap by (field; lra).
    exact Hgap.
Qed.

Lemma deriv_pt_opp :
  forall (f : R -> R) (x l : R),
    derivable_pt_lim f x l ->
    derivable_pt_lim (fun z => - f z) x (- l).
Proof.
  intros f x l Hd.
  eapply derivable_pt_lim_ext; [| apply derivable_pt_lim_opp; exact Hd].
  intros z. unfold opp_fct. reflexivity.
Qed.

Theorem deriv_zero_const :
  forall (f f' : R -> R) (a b x y : R),
    (forall t, a <= t <= b -> derivable_pt_lim f t (f' t)) ->
    (forall t, a <= t <= b -> f' t = 0) ->
    a <= x <= b -> a <= y <= b ->
    f x = f y.
Proof.
  intros f f' a b x y Hder Hz Hx Hy.
  assert (Hnn : forall t, a <= t <= b -> 0 <= f' t).
  { intros t Ht. rewrite Hz by exact Ht. apply Rle_refl. }
  assert (Hopp : forall t, a <= t <= b -> derivable_pt_lim (fun z => - f z) t (- f' t)).
  { intros t Ht. apply deriv_pt_opp. apply Hder. exact Ht. }
  assert (Hnn_opp : forall t, a <= t <= b -> 0 <= - f' t).
  { intros t Ht. rewrite Hz by exact Ht. rewrite Ropp_0. apply Rle_refl. }
  destruct (Rle_lt_dec x y) as [Hxy | Hyx].
  - assert (f x <= f y)
      by (apply deriv_nonneg_incr with (f' := f') (a := a) (b := b); assumption || lra).
    assert (- f x <= - f y)
      by (apply (deriv_nonneg_incr (fun z => - f z) (fun z => - f' z) a b x y);
          assumption || lra).
    lra.
  - assert (f y <= f x)
      by (apply deriv_nonneg_incr with (f' := f') (a := a) (b := b); assumption || lra).
    assert (- f y <= - f x)
      by (apply (deriv_nonneg_incr (fun z => - f z) (fun z => - f' z) a b y x);
          assumption || lra).
    lra.
Qed.

Print Assumptions incr_good_down.
Print Assumptions incr_good_stable.
Print Assumptions not_ub_dn_above.
Print Assumptions incr_good_below_lub.
Print Assumptions quot_pos_right.
Print Assumptions quot_pos_left.
Print Assumptions deriv_pos_right_rise.
Print Assumptions deriv_pos_left_fall.
Print Assumptions deriv_pos_lt_endpoints.
Print Assumptions deriv_pos_strict_incr.
Print Assumptions deriv_pt_add_linear.
Print Assumptions Rle_of_lt_all_pos.
Print Assumptions deriv_nonneg_incr.
Print Assumptions deriv_pt_opp.
Print Assumptions deriv_zero_const.
