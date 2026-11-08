(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_conservative
   ----------------------------------------------------------------------------
   CONSERVATIVE (outward-rounded) repair of the closed Liang-Barsky hot-pixel
   filter.  The round-to-nearest filter `b64_passes_through_hot_pixel_compute`
   is NOT complete off the grid (`PassesThrough_b64_c2_counterexample.v`,
   `c2_false`).

   ARCHITECTURE (one canonical proof):

        pure real division / interval lemmas   (sections 1-2)
                       |
        `dprims`: an ENCLOSURE CONTRACT on six directed primitives
        (sub/add/div, lower and upper): finite, enclosure, magnitude <= 2^(k+1)
                       |
        `g_touches_complete`   -- geometry completeness, proved ONCE, generically
                       |
          +------------+--------------------------+
          |                                       |
   `flocq_prims` (this file)            `exec_prims`
   Flocq mode_DN / mode_UP              round-to-nearest + pred/succ
   (b64_touches_cons, ...)              (PassesThrough_b64_executable.v)

   The contract is enclosure, NOT equality with Flocq's directed rounding:
   equality is false for the executable instance (`ex_sub_dn_not_flocq`).

   Exact spec `b64_passes_through_hot_pixel` is unchanged.  Construction (per
   axis): pixel bounds lo = cc - 1/2, hi = cc + 1/2 and numerators lo - c0,
   hi - c0 get lower and upper endpoints; the denominator c1 - c0 likewise;
   outward division by the SIGN of the denominator interval:
       b > 0 (bmin >= 2^-500):
         lower  DN( nmin / (0 <= nmin ? bmax : bmin) )
         upper  UP( nmax / (0 <= nmax ? bmin : bmax) )
       b < 0 (bmax <= -2^-500):
         lower  DN( nmax / (nmax <= 0 ? bmin : bmax) )
         upper  UP( nmin / (nmin <= 0 ? bmax : bmin) )
       otherwise: UNBOUNDED (cannot reject a touch).
   Axis lower = min(lower(p), lower(r)), upper = max(upper(p), upper(r));
   Tminus = max(0, ..), Tplus = min(1, ..), accept iff Tminus <= Tplus.
   Domain guard: a coordinate that is non-finite or has |c| > 2^500 makes the
   filter ACCEPT, so the theorem is unconditional; the 2^-500 denominator guard
   makes every directed division overflow-free.

   No Admitted / Axiom / Parameter.
   ========================================================================== *)
From Stdlib Require Import Reals ZArith Lra Lia Bool.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib B64_AbsErr
  HotPixel_b64 PassesThrough_b64_compute PassesThrough_b64_grid_core
  PassesThrough_b64_grid_bounds.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §0  Directed-rounding primitives and constants.                            *)
(* -------------------------------------------------------------------------- *)
Definition b64_minus_m (m : mode) (x y : binary64) : binary64 :=
  Binary.Bminus prec emax prec_gt_0_b64 prec_lt_emax_b64 default_nan_b64 m x y.
Definition b64_plus_m (m : mode) (x y : binary64) : binary64 :=
  Binary.Bplus prec emax prec_gt_0_b64 prec_lt_emax_b64 default_nan_b64 m x y.
Definition b64_div_m (m : mode) (x y : binary64) : binary64 :=
  Binary.Bdiv prec emax prec_gt_0_b64 prec_lt_emax_b64 default_nan_b64 m x y.

Local Notation rnd_m := (fun m => round radix2 (SpecFloat.fexp prec emax) (round_mode m)).

Lemma bp_Z : forall k : Z, (0 <= k)%Z -> bpow radix2 k = IZR (2 ^ k).
Proof. intros k Hk. rewrite <- IZR_Zpower by exact Hk. reflexivity. Qed.

Lemma Bfin_val_r : forall s m e (pf : _),
  B2R (Binary.B754_finite prec emax s m e pf)
    = IZR (cond_Zopp s (Z.pos m)) * bpow radix2 e.
Proof. intros. reflexivity. Qed.

(* 2^500, -2^500, 2^-500, -2^-500 as binary64 *)
Definition b64_p500  : binary64 := Binary.B754_finite prec emax false 4503599627370496 448 eq_refl.
Definition b64_m500  : binary64 := Binary.B754_finite prec emax true  4503599627370496 448 eq_refl.
Definition b64_pn500 : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-552) eq_refl.
Definition b64_mn500 : binary64 := Binary.B754_finite prec emax true  4503599627370496 (-552) eq_refl.

Lemma bpow_sum : forall a b : Z, bpow radix2 a * bpow radix2 b = bpow radix2 (a + b).
Proof. intros. rewrite <- bpow_plus. reflexivity. Qed.

Lemma B2R_p500 : B2R b64_p500 = bpow radix2 500.
Proof.
  unfold b64_p500. rewrite Bfin_val_r. cbn [cond_Zopp].
  replace (IZR (Z.pos 4503599627370496)) with (bpow radix2 52)
    by (rewrite bp_Z by lia; reflexivity).
  rewrite bpow_sum. reflexivity.
Qed.
Lemma B2R_m500 : B2R b64_m500 = - bpow radix2 500.
Proof.
  unfold b64_m500. rewrite Bfin_val_r. cbn [cond_Zopp].
  rewrite opp_IZR.
  replace (IZR 4503599627370496) with (bpow radix2 52)
    by (rewrite bp_Z by lia; reflexivity).
  rewrite <- Ropp_mult_distr_l, bpow_sum. reflexivity.
Qed.
Lemma B2R_pn500 : B2R b64_pn500 = bpow radix2 (-500).
Proof.
  unfold b64_pn500. rewrite Bfin_val_r. cbn [cond_Zopp].
  replace (IZR (Z.pos 4503599627370496)) with (bpow radix2 52)
    by (rewrite bp_Z by lia; reflexivity).
  rewrite bpow_sum. reflexivity.
Qed.
Lemma B2R_mn500 : B2R b64_mn500 = - bpow radix2 (-500).
Proof.
  unfold b64_mn500. rewrite Bfin_val_r. cbn [cond_Zopp].
  rewrite opp_IZR.
  replace (IZR 4503599627370496) with (bpow radix2 52)
    by (rewrite bp_Z by lia; reflexivity).
  rewrite <- Ropp_mult_distr_l, bpow_sum. reflexivity.
Qed.
Lemma fin_p500 : fin b64_p500 = true. Proof. reflexivity. Qed.
Lemma fin_m500 : fin b64_m500 = true. Proof. reflexivity. Qed.
Lemma fin_pn500 : fin b64_pn500 = true. Proof. reflexivity. Qed.
Lemma fin_mn500 : fin b64_mn500 = true. Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §1  Directed rounding: enclosure and magnitude (the no-overflow facts).    *)
(* -------------------------------------------------------------------------- *)
Lemma round_dn_le : forall z, rnd_m mode_DN z <= z.
Proof.
  intro z.
  exact (proj1 (proj2 (round_DN_pt radix2 (SpecFloat.fexp prec emax) z))).
Qed.
Lemma round_up_ge : forall z, z <= rnd_m mode_UP z.
Proof.
  intro z.
  exact (proj1 (proj2 (round_UP_pt radix2 (SpecFloat.fexp prec emax) z))).
Qed.

Lemma rnd_abs_le_bpow : forall (m : mode) (z : R) (e : Z),
  (3 - emax <= e + 1)%Z -> Rabs z <= bpow radix2 e ->
  Rabs (rnd_m m z) <= bpow radix2 e.
Proof.
  intros m z e He Hz.
  pose proof (generic_format_bpow_b64 e He) as Hfmt.
  pose proof (generic_format_opp _ _ _ Hfmt) as Hfmt_neg.
  apply Rabs_le_inv in Hz. apply Rabs_le. split.
  - rewrite <- (round_generic radix2 (SpecFloat.fexp prec emax)
                  (round_mode m) (- bpow radix2 e) Hfmt_neg).
    apply (round_le radix2 (SpecFloat.fexp prec emax) (round_mode m)). tauto.
  - rewrite <- (round_generic radix2 (SpecFloat.fexp prec emax)
                  (round_mode m) (bpow radix2 e) Hfmt).
    apply (round_le radix2 (SpecFloat.fexp prec emax) (round_mode m)). tauto.
Qed.

Lemma minus_m_ok : forall (m : mode) x y,
  fin x = true -> fin y = true ->
  Rabs (B2R x - B2R y) <= bpow radix2 1000 ->
  fin (b64_minus_m m x y) = true /\
  B2R (b64_minus_m m x y) = rnd_m m (B2R x - B2R y).
Proof.
  intros m x y Fx Fy Hb.
  pose proof (Binary.Bminus_correct prec emax prec_gt_0_b64 prec_lt_emax_b64
                default_nan_b64 m x y Fx Fy) as H.
  assert (Hlt : Rlt_bool (Rabs (rnd_m m (B2R x - B2R y))) (bpow radix2 emax) = true).
  { apply Rlt_bool_true.
    eapply Rle_lt_trans; [apply (rnd_abs_le_bpow m _ 1000); [unfold emax; lia | exact Hb]|].
    apply bpow_lt; unfold emax; lia. }
  unfold b64_minus_m. rewrite Hlt in H. destruct H as [H1 [H2 _]]. split; assumption.
Qed.

Lemma plus_m_ok : forall (m : mode) x y,
  fin x = true -> fin y = true ->
  Rabs (B2R x + B2R y) <= bpow radix2 1000 ->
  fin (b64_plus_m m x y) = true /\
  B2R (b64_plus_m m x y) = rnd_m m (B2R x + B2R y).
Proof.
  intros m x y Fx Fy Hb.
  pose proof (Binary.Bplus_correct prec emax prec_gt_0_b64 prec_lt_emax_b64
                default_nan_b64 m x y Fx Fy) as H.
  assert (Hlt : Rlt_bool (Rabs (rnd_m m (B2R x + B2R y))) (bpow radix2 emax) = true).
  { apply Rlt_bool_true.
    eapply Rle_lt_trans; [apply (rnd_abs_le_bpow m _ 1000); [unfold emax; lia | exact Hb]|].
    apply bpow_lt; unfold emax; lia. }
  unfold b64_plus_m. rewrite Hlt in H. destruct H as [H1 [H2 _]]. split; assumption.
Qed.

Lemma div_m_ok : forall (m : mode) x y,
  fin x = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
  fin (b64_div_m m x y) = true /\
  B2R (b64_div_m m x y) = rnd_m m (B2R x / B2R y).
Proof.
  intros m x y Fx Hy Hb.
  pose proof (Binary.Bdiv_correct prec emax prec_gt_0_b64 prec_lt_emax_b64
                default_nan_b64 m x y Hy) as H.
  assert (Hlt : Rlt_bool (Rabs (rnd_m m (B2R x / B2R y))) (bpow radix2 emax) = true).
  { apply Rlt_bool_true.
    eapply Rle_lt_trans; [apply (rnd_abs_le_bpow m _ 1004); [unfold emax; lia | exact Hb]|].
    apply bpow_lt; unfold emax; lia. }
  unfold b64_div_m. rewrite Hlt in H. destruct H as [H1 [H2 _]].
  split; [rewrite H2; exact Fx | exact H1].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Outward division, pure reals.  Denominator sign handled explicitly:    *)
(*     positive denominators and negative denominators use DIFFERENT          *)
(*     endpoint combinations.                                                 *)
(* -------------------------------------------------------------------------- *)
Lemma inv_neg_mono : forall x y : R, x <= y -> y < 0 -> / y <= / x.
Proof.
  intros x y Hxy Hy.
  assert (H : / (- x) <= / (- y)).
  { apply Rinv_le_contravar; lra. }
  rewrite !Rinv_opp in H. lra.
Qed.

(* b > 0 : 0 < bmin <= b <= bmax *)
Lemma lowP1 : forall bmin b bmax a amin,
  0 < bmin -> bmin <= b -> b <= bmax -> 0 <= amin -> amin <= a ->
  amin / bmax <= a / b.
Proof.
  intros bmin b bmax a amin Hm Hb1 Hb2 Ha Haa.
  assert (hb : 0 < b) by lra.
  assert (i1 : / bmax <= / b) by (apply Rinv_le_contravar; lra).
  assert (ip : 0 <= / b) by (apply Rlt_le, Rinv_0_lt_compat; exact hb).
  unfold Rdiv. eapply Rle_trans.
  - apply Rmult_le_compat_l; [exact Ha | exact i1].
  - apply Rmult_le_compat_r; [exact ip | exact Haa].
Qed.

Lemma lowP2 : forall bmin b bmax a amin,
  0 < bmin -> bmin <= b -> b <= bmax -> amin <= 0 -> amin <= a ->
  amin / bmin <= a / b.
Proof.
  intros bmin b bmax a amin Hm Hb1 Hb2 Ha Haa.
  assert (hb : 0 < b) by lra.
  assert (i2 : / b <= / bmin) by (apply Rinv_le_contravar; lra).
  assert (ip : 0 <= / b) by (apply Rlt_le, Rinv_0_lt_compat; exact hb).
  unfold Rdiv. eapply Rle_trans.
  - apply Rmult_le_compat_neg_l; [exact Ha | exact i2].
  - apply Rmult_le_compat_r; [exact ip | exact Haa].
Qed.

Lemma upP1 : forall bmin b bmax a amax,
  0 < bmin -> bmin <= b -> b <= bmax -> 0 <= amax -> a <= amax ->
  a / b <= amax / bmin.
Proof.
  intros bmin b bmax a amax Hm Hb1 Hb2 Ha Haa.
  assert (hb : 0 < b) by lra.
  assert (i2 : / b <= / bmin) by (apply Rinv_le_contravar; lra).
  assert (ip : 0 <= / b) by (apply Rlt_le, Rinv_0_lt_compat; exact hb).
  unfold Rdiv. eapply Rle_trans.
  - apply Rmult_le_compat_r; [exact ip | exact Haa].
  - apply Rmult_le_compat_l; [exact Ha | exact i2].
Qed.

Lemma upP2 : forall bmin b bmax a amax,
  0 < bmin -> bmin <= b -> b <= bmax -> amax <= 0 -> a <= amax ->
  a / b <= amax / bmax.
Proof.
  intros bmin b bmax a amax Hm Hb1 Hb2 Ha Haa.
  assert (hb : 0 < b) by lra.
  assert (i1 : / bmax <= / b) by (apply Rinv_le_contravar; lra).
  assert (ip : 0 <= / b) by (apply Rlt_le, Rinv_0_lt_compat; exact hb).
  unfold Rdiv. eapply Rle_trans.
  - apply Rmult_le_compat_r; [exact ip | exact Haa].
  - apply Rmult_le_compat_neg_l; [exact Ha | exact i1].
Qed.

(* b < 0 : bmin <= b <= bmax < 0 *)
Lemma lowN1 : forall bmin b bmax a amax,
  bmax < 0 -> bmin <= b -> b <= bmax -> amax <= 0 -> a <= amax ->
  amax / bmin <= a / b.
Proof.
  intros bmin b bmax a amax Hn Hb1 Hb2 Ha Haa.
  assert (hb : b < 0) by lra.
  assert (j2 : / b <= / bmin) by (apply inv_neg_mono; lra).
  assert (ineg : / b <= 0) by (apply Rlt_le, Rinv_lt_0_compat; exact hb).
  unfold Rdiv. eapply Rle_trans.
  - apply Rmult_le_compat_neg_l; [exact Ha | exact j2].
  - rewrite (Rmult_comm amax), (Rmult_comm a).
    apply Rmult_le_compat_neg_l; [exact ineg | exact Haa].
Qed.

Lemma lowN2 : forall bmin b bmax a amax,
  bmax < 0 -> bmin <= b -> b <= bmax -> 0 <= amax -> a <= amax ->
  amax / bmax <= a / b.
Proof.
  intros bmin b bmax a amax Hn Hb1 Hb2 Ha Haa.
  assert (hb : b < 0) by lra.
  assert (j1 : / bmax <= / b) by (apply inv_neg_mono; lra).
  assert (ineg : / b <= 0) by (apply Rlt_le, Rinv_lt_0_compat; exact hb).
  unfold Rdiv. eapply Rle_trans.
  - apply Rmult_le_compat_l; [exact Ha | exact j1].
  - rewrite (Rmult_comm amax), (Rmult_comm a).
    apply Rmult_le_compat_neg_l; [exact ineg | exact Haa].
Qed.

Lemma upN1 : forall bmin b bmax a amin,
  bmax < 0 -> bmin <= b -> b <= bmax -> amin <= 0 -> amin <= a ->
  a / b <= amin / bmax.
Proof.
  intros bmin b bmax a amin Hn Hb1 Hb2 Ha Haa.
  assert (hb : b < 0) by lra.
  assert (j1 : / bmax <= / b) by (apply inv_neg_mono; lra).
  assert (ineg : / b <= 0) by (apply Rlt_le, Rinv_lt_0_compat; exact hb).
  unfold Rdiv. apply Rle_trans with (amin * / b).
  - rewrite (Rmult_comm a), (Rmult_comm amin).
    apply Rmult_le_compat_neg_l; [exact ineg | exact Haa].
  - apply Rmult_le_compat_neg_l; [exact Ha | exact j1].
Qed.

Lemma upN2 : forall bmin b bmax a amin,
  bmax < 0 -> bmin <= b -> b <= bmax -> 0 <= amin -> amin <= a ->
  a / b <= amin / bmin.
Proof.
  intros bmin b bmax a amin Hn Hb1 Hb2 Ha Haa.
  assert (hb : b < 0) by lra.
  assert (j2 : / b <= / bmin) by (apply inv_neg_mono; lra).
  assert (ineg : / b <= 0) by (apply Rlt_le, Rinv_lt_0_compat; exact hb).
  unfold Rdiv. apply Rle_trans with (amin * / b).
  - rewrite (Rmult_comm a), (Rmult_comm amin).
    apply Rmult_le_compat_neg_l; [exact ineg | exact Haa].
  - apply Rmult_le_compat_l; [exact Ha | exact j2].
Qed.


(* -------------------------------------------------------------------------- *)
(* §3  Shared structural definitions and lemmas (primitive-independent).      *)
(* -------------------------------------------------------------------------- *)
Lemma Rabs_ge_pos : forall d : R, bpow radix2 (-500) <= d -> bpow radix2 (-500) <= Rabs d.
Proof. intros d H. rewrite Rabs_right; [exact H|]. pose proof (bpow_gt_0 radix2 (-500)). lra. Qed.
Lemma Rabs_ge_neg : forall d : R, d <= - bpow radix2 (-500) -> bpow radix2 (-500) <= Rabs d.
Proof. intros d H. rewrite Rabs_left; [lra|]. pose proof (bpow_gt_0 radix2 (-500)). lra. Qed.

Definition opt_min (a b : option binary64) : option binary64 :=
  match a, b with Some x, Some y => Some (b64_min x y) | _, _ => None end.
Definition opt_max (a b : option binary64) : option binary64 :=
  match a, b with Some x, Some y => Some (b64_max x y) | _, _ => None end.

(* Lower t-bound of the axis (None = no information = -infinity). *)
(* Magnitude arithmetic. *)
Lemma bpow_double_sum : forall k : Z, bpow radix2 k + bpow radix2 k = bpow radix2 (k + 1).
Proof.
  intro k. rewrite bpow_plus.
  replace (bpow radix2 1) with 2 by (simpl; lra). lra.
Qed.
Lemma half_le_500 : / 2 <= bpow radix2 500.
Proof.
  apply Rle_trans with (bpow radix2 0).
  - replace (bpow radix2 0) with 1 by reflexivity. lra.
  - apply bpow_le. lia.
Qed.
Lemma bpow_mono : forall a b : Z, (a <= b)%Z -> bpow radix2 a <= bpow radix2 b.
Proof. intros. apply bpow_le. assumption. Qed.
Lemma abs_sum_le : forall u v a b : R, Rabs u <= a -> Rabs v <= b -> Rabs (u + v) <= a + b.
Proof. intros. eapply Rle_trans; [apply Rabs_triang|]. lra. Qed.
Lemma abs_diff_le : forall u v a b : R, Rabs u <= a -> Rabs v <= b -> Rabs (u - v) <= a + b.
Proof.
  intros. unfold Rminus. eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp. lra.
Qed.

(* One directed step with magnitude bookkeeping. *)
Lemma dir_minus : forall (m : mode) x y (k : Z),
  fin x = true -> fin y = true -> (0 <= k <= 1000)%Z ->
  Rabs (B2R x - B2R y) <= bpow radix2 k ->
  fin (b64_minus_m m x y) = true /\
  B2R (b64_minus_m m x y) = rnd_m m (B2R x - B2R y) /\
  Rabs (B2R (b64_minus_m m x y)) <= bpow radix2 k.
Proof.
  intros m x y k Fx Fy Hk Hb. destruct Hk as [Hk0 Hk].
  destruct (minus_m_ok m x y Fx Fy
              (Rle_trans _ _ _ Hb (bpow_mono _ _ Hk))) as [F E].
  refine (conj F (conj E _)). rewrite E.
  apply rnd_abs_le_bpow; [unfold emax; lia | exact Hb].
Qed.

Lemma dir_plus : forall (m : mode) x y (k : Z),
  fin x = true -> fin y = true -> (0 <= k <= 1000)%Z ->
  Rabs (B2R x + B2R y) <= bpow radix2 k ->
  fin (b64_plus_m m x y) = true /\
  B2R (b64_plus_m m x y) = rnd_m m (B2R x + B2R y) /\
  Rabs (B2R (b64_plus_m m x y)) <= bpow radix2 k.
Proof.
  intros m x y k Fx Fy Hk Hb. destruct Hk as [Hk0 Hk].
  destruct (plus_m_ok m x y Fx Fy
              (Rle_trans _ _ _ Hb (bpow_mono _ _ Hk))) as [F E].
  refine (conj F (conj E _)). rewrite E.
  apply rnd_abs_le_bpow; [unfold emax; lia | exact Hb].
Qed.

(* Monotonicity of Rmin / Rmax in both arguments. *)
Lemma Rmin_mono : forall a b c d : R, a <= c -> b <= d -> Rmin a b <= Rmin c d.
Proof.
  intros a b c d H1 H2. apply Rmin_glb.
  - eapply Rle_trans; [apply Rmin_l | exact H1].
  - eapply Rle_trans; [apply Rmin_r | exact H2].
Qed.
Lemma Rmax_mono : forall a b c d : R, a <= c -> b <= d -> Rmax a b <= Rmax c d.
Proof.
  intros a b c d H1 H2. apply Rmax_lub.
  - eapply Rle_trans; [exact H1 | apply Rmax_l].
  - eapply Rle_trans; [exact H2 | apply Rmax_r].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The repaired touch and passes-through predicates.                      *)
(* -------------------------------------------------------------------------- *)
(* Domain guard: finite and |c| <= 2^500.  Outside it the filter ACCEPTS. *)
Definition b64_dom (v : binary64) : bool :=
  andb (andb (Binary.is_finite prec emax v) (b64_le b64_m500 v)) (b64_le v b64_p500).

Lemma dom_ok : forall v, b64_dom v = true ->
  fin v = true /\ Rabs (B2R v) <= bpow radix2 500.
Proof.
  intros v H. unfold b64_dom in H.
  apply Bool.andb_true_iff in H. destruct H as [H H2].
  apply Bool.andb_true_iff in H. destruct H as [Fv H1].
  split; [exact Fv|].
  apply b64ae_le_true in H1; [|exact fin_m500|exact Fv].
  apply b64ae_le_true in H2; [|exact Fv|exact fin_p500].
  rewrite B2R_m500 in H1. rewrite B2R_p500 in H2.
  apply Rabs_le. split; lra.
Qed.

Definition ub_max (acc : binary64) (o : option binary64) : binary64 :=
  match o with Some v => b64_max acc v | None => acc end.
Definition ub_min (acc : binary64) (o : option binary64) : binary64 :=
  match o with Some v => b64_min acc v | None => acc end.

Lemma ub_max_ok : forall acc o (A T : R),
  fin acc = true -> B2R acc <= A ->
  (match o with Some v => fin v = true /\ B2R v <= T | None => True end) ->
  fin (ub_max acc o) = true /\ B2R (ub_max acc o) <= Rmax A T.
Proof.
  intros acc o A T Fa Ha Ho. destruct o as [v|]; unfold ub_max.
  - destruct Ho as [Fv Hv]. split; [apply is_finite_b64_max; assumption|].
    rewrite (b64_max_B2R _ _ Fa Fv). apply Rmax_mono; assumption.
  - split; [exact Fa|]. eapply Rle_trans; [exact Ha | apply Rmax_l].
Qed.

Lemma ub_min_ok : forall acc o (A T : R),
  fin acc = true -> A <= B2R acc ->
  (match o with Some v => fin v = true /\ T <= B2R v | None => True end) ->
  fin (ub_min acc o) = true /\ Rmin A T <= B2R (ub_min acc o).
Proof.
  intros acc o A T Fa Ha Ho. destruct o as [v|]; unfold ub_min.
  - destruct Ho as [Fv Hv]. split; [apply is_finite_b64_min; assumption|].
    rewrite (b64_min_B2R _ _ Fa Fv). apply Rmin_mono; assumption.
  - split; [exact Fa|]. eapply Rle_trans; [apply Rmin_l | exact Ha].
Qed.


(* -------------------------------------------------------------------------- *)
(* §4-§5  Enclosure contract and the generic conservative filter (canonical). *)
(* -------------------------------------------------------------------------- *)
Record dprims := mkDP {
  sdn : binary64 -> binary64 -> binary64;
  sup : binary64 -> binary64 -> binary64;
  adn : binary64 -> binary64 -> binary64;
  aup : binary64 -> binary64 -> binary64;
  ddn : binary64 -> binary64 -> binary64;
  dup : binary64 -> binary64 -> binary64;
  sdn_ok : forall x y k, fin x = true -> fin y = true -> (0 <= k <= 1000)%Z ->
    Rabs (B2R x - B2R y) <= bpow radix2 k ->
    fin (sdn x y) = true /\ B2R (sdn x y) <= B2R x - B2R y /\
    Rabs (B2R (sdn x y)) <= bpow radix2 (k + 1);
  sup_ok : forall x y k, fin x = true -> fin y = true -> (0 <= k <= 1000)%Z ->
    Rabs (B2R x - B2R y) <= bpow radix2 k ->
    fin (sup x y) = true /\ B2R x - B2R y <= B2R (sup x y) /\
    Rabs (B2R (sup x y)) <= bpow radix2 (k + 1);
  adn_ok : forall x y k, fin x = true -> fin y = true -> (0 <= k <= 1000)%Z ->
    Rabs (B2R x + B2R y) <= bpow radix2 k ->
    fin (adn x y) = true /\ B2R (adn x y) <= B2R x + B2R y /\
    Rabs (B2R (adn x y)) <= bpow radix2 (k + 1);
  aup_ok : forall x y k, fin x = true -> fin y = true -> (0 <= k <= 1000)%Z ->
    Rabs (B2R x + B2R y) <= bpow radix2 k ->
    fin (aup x y) = true /\ B2R x + B2R y <= B2R (aup x y) /\
    Rabs (B2R (aup x y)) <= bpow radix2 (k + 1);
  ddn_ok : forall x y, fin x = true -> B2R y <> 0 ->
    Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
    fin (ddn x y) = true /\ B2R (ddn x y) <= B2R x / B2R y;
  dup_ok : forall x y, fin x = true -> B2R y <> 0 ->
    Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
    fin (dup x y) = true /\ B2R x / B2R y <= B2R (dup x y)
}.

Lemma div_abs_bound504 : forall n d : R,
  bpow radix2 (-500) <= Rabs d -> Rabs n <= bpow radix2 504 ->
  Rabs (n / d) <= bpow radix2 1004.
Proof.
  intros n d Hd Hn.
  assert (Hpos : 0 < bpow radix2 (-500)) by apply bpow_gt_0.
  assert (Hd0 : 0 < Rabs d) by lra.
  assert (Hne : d <> 0).
  { intro H. rewrite H, Rabs_R0 in Hd0. lra. }
  unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact Hne.
  assert (Hi : / Rabs d <= bpow radix2 500).
  { replace (bpow radix2 500) with (/ bpow radix2 (-500)).
    - apply Rinv_le_contravar; assumption.
    - replace (-500)%Z with (-(500))%Z by reflexivity.
      rewrite bpow_opp, Rinv_inv. reflexivity. }
  assert (Hi0 : 0 <= / Rabs d) by (apply Rlt_le, Rinv_0_lt_compat; exact Hd0).
  assert (Hn0 : 0 <= Rabs n) by apply Rabs_pos.
  eapply Rle_trans; [apply Rmult_le_compat; [exact Hn0 | exact Hi0 | exact Hn | exact Hi]|].
  rewrite bpow_sum. replace (504 + 500)%Z with 1004%Z by reflexivity. apply Rle_refl.
Qed.

Section Generic.
Variable P : dprims.

Definition g_lo_m (cc : binary64) := sdn P cc b64_half.
Definition g_lo_p (cc : binary64) := sup P cc b64_half.
Definition g_hi_m (cc : binary64) := adn P cc b64_half.
Definition g_hi_p (cc : binary64) := aup P cc b64_half.
Definition g_pmin (c0 cc : binary64) := sdn P (g_lo_m cc) c0.
Definition g_pmax (c0 cc : binary64) := sup P (g_lo_p cc) c0.
Definition g_rmin (c0 cc : binary64) := sdn P (g_hi_m cc) c0.
Definition g_rmax (c0 cc : binary64) := sup P (g_hi_p cc) c0.
Definition g_bmin (c0 c1 : binary64) := sdn P c1 c0.
Definition g_bmax (c0 c1 : binary64) := sup P c1 c0.

Definition g_q_lower (nmin nmax bmin bmax : binary64) : option binary64 :=
  if b64_le b64_pn500 bmin then
    Some (ddn P nmin (if b64_le b64_zero nmin then bmax else bmin))
  else if b64_le bmax b64_mn500 then
    Some (ddn P nmax (if b64_le nmax b64_zero then bmin else bmax))
  else None.

Definition g_q_upper (nmin nmax bmin bmax : binary64) : option binary64 :=
  if b64_le b64_pn500 bmin then
    Some (dup P nmax (if b64_le b64_zero nmax then bmin else bmax))
  else if b64_le bmax b64_mn500 then
    Some (dup P nmin (if b64_le nmin b64_zero then bmax else bmin))
  else None.

Definition g_axis_lo (c0 c1 cc : binary64) : option binary64 :=
  if b64_eqb c1 c0 then Some b64_zero
  else opt_min
         (g_q_lower (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
         (g_q_lower (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)).

Definition g_axis_hi (c0 c1 cc : binary64) : option binary64 :=
  if b64_eqb c1 c0 then Some b64_one
  else opt_max
         (g_q_upper (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
         (g_q_upper (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)).

Definition g_axis_guard (c0 c1 cc : binary64) : bool :=
  if b64_eqb c1 c0
  then andb (b64_le (g_lo_m cc) c0) (b64_le c0 (g_hi_p cc))
  else true.

Definition g_touches (P0 P1 C : BPoint) : bool :=
  if b64_dom (bx P0) && b64_dom (by_ P0) && b64_dom (bx P1) && b64_dom (by_ P1)
     && b64_dom (bx C) && b64_dom (by_ C)
  then
    g_axis_guard (bx P0) (bx P1) (bx C) && g_axis_guard (by_ P0) (by_ P1) (by_ C)
    && b64_le
         (ub_max (ub_max b64_zero (g_axis_lo (bx P0) (bx P1) (bx C)))
                 (g_axis_lo (by_ P0) (by_ P1) (by_ C)))
         (ub_min (ub_min b64_one (g_axis_hi (bx P0) (bx P1) (bx C)))
                 (g_axis_hi (by_ P0) (by_ P1) (by_ C)))
  else true.

Lemma g_q_lower_ok : forall nmin nmax bmin bmax a b,
  fin nmin = true -> fin nmax = true -> fin bmin = true -> fin bmax = true ->
  Rabs (B2R nmin) <= bpow radix2 504 -> Rabs (B2R nmax) <= bpow radix2 504 ->
  B2R nmin <= a -> a <= B2R nmax -> B2R bmin <= b -> b <= B2R bmax ->
  match g_q_lower nmin nmax bmin bmax with
  | Some v => fin v = true /\ B2R v <= a / b
  | None => True
  end.
Proof.
  intros nmin nmax bmin bmax a b Fn1 Fn2 Fb1 Fb2 Hn1 Hn2 Ha1 Ha2 Hb1 Hb2.
  pose proof (bpow_gt_0 radix2 (-500)) as Hl.
  unfold g_q_lower.
  destruct (b64_le b64_pn500 bmin) eqn:E1.
  - apply b64ae_le_true in E1; [|exact fin_pn500|exact Fb1]. rewrite B2R_pn500 in E1.
    destruct (b64_le b64_zero nmin) eqn:E2.
    + apply b64ae_le_true in E2; [|exact is_finite_b64_zero|exact Fn1].
      rewrite B2R_b64_zero in E2.
      assert (Hbm : bpow radix2 (-500) <= B2R bmax) by lra.
      destruct (ddn_ok P nmin bmax Fn1 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_pos _ Hbm) Hn1)) as [Fv Ev].
      cbn zeta. split; [exact Fv|]. eapply Rle_trans; [exact Ev|].
      apply (lowP1 (B2R bmin) b (B2R bmax) a (B2R nmin)); lra.
    + apply b64ae_le_false in E2; [|exact is_finite_b64_zero|exact Fn1].
      rewrite B2R_b64_zero in E2.
      destruct (ddn_ok P nmin bmin Fn1 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_pos _ E1) Hn1)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [exact Ev|].
      apply (lowP2 (B2R bmin) b (B2R bmax) a (B2R nmin)); lra.
  - destruct (b64_le bmax b64_mn500) eqn:E3; [|exact I].
    apply b64ae_le_true in E3; [|exact Fb2|exact fin_mn500]. rewrite B2R_mn500 in E3.
    destruct (b64_le nmax b64_zero) eqn:E4.
    + apply b64ae_le_true in E4; [|exact Fn2|exact is_finite_b64_zero].
      rewrite B2R_b64_zero in E4.
      assert (Hbm : B2R bmin <= - bpow radix2 (-500)) by lra.
      destruct (ddn_ok P nmax bmin Fn2 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_neg _ Hbm) Hn2)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [exact Ev|].
      apply (lowN1 (B2R bmin) b (B2R bmax) a (B2R nmax)); lra.
    + apply b64ae_le_false in E4; [|exact Fn2|exact is_finite_b64_zero].
      rewrite B2R_b64_zero in E4.
      destruct (ddn_ok P nmax bmax Fn2 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_neg _ E3) Hn2)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [exact Ev|].
      apply (lowN2 (B2R bmin) b (B2R bmax) a (B2R nmax)); lra.
Qed.

Lemma g_q_upper_ok : forall nmin nmax bmin bmax a b,
  fin nmin = true -> fin nmax = true -> fin bmin = true -> fin bmax = true ->
  Rabs (B2R nmin) <= bpow radix2 504 -> Rabs (B2R nmax) <= bpow radix2 504 ->
  B2R nmin <= a -> a <= B2R nmax -> B2R bmin <= b -> b <= B2R bmax ->
  match g_q_upper nmin nmax bmin bmax with
  | Some v => fin v = true /\ a / b <= B2R v
  | None => True
  end.
Proof.
  intros nmin nmax bmin bmax a b Fn1 Fn2 Fb1 Fb2 Hn1 Hn2 Ha1 Ha2 Hb1 Hb2.
  pose proof (bpow_gt_0 radix2 (-500)) as Hl.
  unfold g_q_upper.
  destruct (b64_le b64_pn500 bmin) eqn:E1.
  - apply b64ae_le_true in E1; [|exact fin_pn500|exact Fb1]. rewrite B2R_pn500 in E1.
    destruct (b64_le b64_zero nmax) eqn:E2.
    + apply b64ae_le_true in E2; [|exact is_finite_b64_zero|exact Fn2].
      rewrite B2R_b64_zero in E2.
      destruct (dup_ok P nmax bmin Fn2 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_pos _ E1) Hn2)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [|exact Ev].
      apply (upP1 (B2R bmin) b (B2R bmax) a (B2R nmax)); lra.
    + apply b64ae_le_false in E2; [|exact is_finite_b64_zero|exact Fn2].
      rewrite B2R_b64_zero in E2.
      assert (Hbm : bpow radix2 (-500) <= B2R bmax) by lra.
      destruct (dup_ok P nmax bmax Fn2 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_pos _ Hbm) Hn2)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [|exact Ev].
      apply (upP2 (B2R bmin) b (B2R bmax) a (B2R nmax)); lra.
  - destruct (b64_le bmax b64_mn500) eqn:E3; [|exact I].
    apply b64ae_le_true in E3; [|exact Fb2|exact fin_mn500]. rewrite B2R_mn500 in E3.
    destruct (b64_le nmin b64_zero) eqn:E4.
    + apply b64ae_le_true in E4; [|exact Fn1|exact is_finite_b64_zero].
      rewrite B2R_b64_zero in E4.
      destruct (dup_ok P nmin bmax Fn1 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_neg _ E3) Hn1)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [|exact Ev].
      apply (upN1 (B2R bmin) b (B2R bmax) a (B2R nmin)); lra.
    + apply b64ae_le_false in E4; [|exact Fn1|exact is_finite_b64_zero].
      rewrite B2R_b64_zero in E4.
      assert (Hbm : B2R bmin <= - bpow radix2 (-500)) by lra.
      destruct (dup_ok P nmin bmin Fn1 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_neg _ Hbm) Hn1)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [|exact Ev].
      apply (upN2 (B2R bmin) b (B2R bmax) a (B2R nmin)); lra.
Qed.


(* Everything the quotient lemmas need about one axis (magnitudes 2^504). *)
Lemma g_axis_facts : forall c0 c1 cc,
  fin c0 = true -> fin c1 = true -> fin cc = true ->
  Rabs (B2R c0) <= bpow radix2 500 -> Rabs (B2R c1) <= bpow radix2 500 ->
  Rabs (B2R cc) <= bpow radix2 500 ->
  let lo := B2R cc - / 2 in let hi := B2R cc + / 2 in
  fin (g_lo_m cc) = true /\ fin (g_lo_p cc) = true /\
  fin (g_hi_m cc) = true /\ fin (g_hi_p cc) = true /\
  B2R (g_lo_m cc) <= lo /\ lo <= B2R (g_lo_p cc) /\
  B2R (g_hi_m cc) <= hi /\ hi <= B2R (g_hi_p cc) /\
  fin (g_pmin c0 cc) = true /\ fin (g_pmax c0 cc) = true /\
  fin (g_rmin c0 cc) = true /\ fin (g_rmax c0 cc) = true /\
  B2R (g_pmin c0 cc) <= lo - B2R c0 /\ lo - B2R c0 <= B2R (g_pmax c0 cc) /\
  B2R (g_rmin c0 cc) <= hi - B2R c0 /\ hi - B2R c0 <= B2R (g_rmax c0 cc) /\
  Rabs (B2R (g_pmin c0 cc)) <= bpow radix2 504 /\
  Rabs (B2R (g_pmax c0 cc)) <= bpow radix2 504 /\
  Rabs (B2R (g_rmin c0 cc)) <= bpow radix2 504 /\
  Rabs (B2R (g_rmax c0 cc)) <= bpow radix2 504 /\
  fin (g_bmin c0 c1) = true /\ fin (g_bmax c0 c1) = true /\
  B2R (g_bmin c0 c1) <= B2R c1 - B2R c0 /\ B2R c1 - B2R c0 <= B2R (g_bmax c0 c1).
Proof.
  intros c0 c1 cc F0 F1 Fc H0 H1 Hc lo hi.
  destruct B2R_and_finite_b64_half as [Bh Fh].
  assert (Hh : Rabs (B2R b64_half) <= bpow radix2 500).
  { rewrite Bh, Rabs_right by lra. exact half_le_500. }
  assert (Hdb : forall z, Rabs z <= bpow radix2 500 + bpow radix2 500 ->
                          Rabs z <= bpow radix2 501).
  { intros z Hz. pose proof (bpow_double_sum 500) as D.
    replace (500 + 1)%Z with 501%Z in D by reflexivity. lra. }
  destruct (sdn_ok P cc b64_half 501 Fc Fh ltac:(lia)
              (Hdb _ (abs_diff_le _ _ _ _ Hc Hh))) as [Flm [Rlm Alm]].
  destruct (sup_ok P cc b64_half 501 Fc Fh ltac:(lia)
              (Hdb _ (abs_diff_le _ _ _ _ Hc Hh))) as [Flp [Rlp Alp]].
  destruct (adn_ok P cc b64_half 501 Fc Fh ltac:(lia)
              (Hdb _ (abs_sum_le _ _ _ _ Hc Hh))) as [Fhm [Rhm Ahm]].
  destruct (aup_ok P cc b64_half 501 Fc Fh ltac:(lia)
              (Hdb _ (abs_sum_le _ _ _ _ Hc Hh))) as [Fhp [Rhp Ahp]].
  rewrite Bh in Rlm, Rlp, Rhm, Rhp.
  replace (501 + 1)%Z with 502%Z in Alm, Alp, Ahm, Ahp by reflexivity.
  (* numerators: |lo_m - c0| <= 2^502 + 2^500 <= 2^503 *)
  assert (H503 : bpow radix2 502 + bpow radix2 500 <= bpow radix2 503).
  { pose proof (bpow_double_sum 502) as D.
    replace (502 + 1)%Z with 503%Z in D by reflexivity.
    pose proof (bpow_mono 500 502 ltac:(lia)). lra. }
  assert (Hst : forall z, Rabs z <= bpow radix2 502 + bpow radix2 500 ->
                          Rabs z <= bpow radix2 503).
  { intros z Hz. eapply Rle_trans; [exact Hz | exact H503]. }
  destruct (sdn_ok P (g_lo_m cc) c0 503 Flm F0 ltac:(lia)
              (Hst _ (abs_diff_le _ _ _ _ Alm H0))) as [Fpm [Rpm Apm]].
  destruct (sup_ok P (g_lo_p cc) c0 503 Flp F0 ltac:(lia)
              (Hst _ (abs_diff_le _ _ _ _ Alp H0))) as [Fpp [Rpp App]].
  destruct (sdn_ok P (g_hi_m cc) c0 503 Fhm F0 ltac:(lia)
              (Hst _ (abs_diff_le _ _ _ _ Ahm H0))) as [Frm [Rrm Arm]].
  destruct (sup_ok P (g_hi_p cc) c0 503 Fhp F0 ltac:(lia)
              (Hst _ (abs_diff_le _ _ _ _ Ahp H0))) as [Frp [Rrp Arp]].
  replace (503 + 1)%Z with 504%Z in Apm, App, Arm, Arp by reflexivity.
  assert (Hb : Rabs (B2R c1 - B2R c0) <= bpow radix2 501)
    by (apply Hdb; apply abs_diff_le; assumption).
  destruct (sdn_ok P c1 c0 501 F1 F0 ltac:(lia) Hb) as [Fbm [Rbm Abm]].
  destruct (sup_ok P c1 c0 501 F1 F0 ltac:(lia) Hb) as [Fbp [Rbp Abp]].
  unfold g_pmin, g_pmax, g_rmin, g_rmax, g_bmin, g_bmax, g_lo_m, g_lo_p, g_hi_m, g_hi_p in *.
  unfold lo, hi. repeat split; try assumption; lra.
Qed.

(* POLARITY, lower bound:  computed lower  <=  exact lower  (lb_tlo). *)
Lemma g_axis_lo_ok : forall c0 c1 cc,
  fin c0 = true -> fin c1 = true -> fin cc = true ->
  Rabs (B2R c0) <= bpow radix2 500 -> Rabs (B2R c1) <= bpow radix2 500 ->
  Rabs (B2R cc) <= bpow radix2 500 ->
  match g_axis_lo c0 c1 cc with
  | Some v => fin v = true /\
      B2R v <= lb_tlo (B2R c0) (B2R c1) (B2R cc - / 2) (B2R cc + / 2)
  | None => True
  end.
Proof.
  intros c0 c1 cc F0 F1 Fc H0 H1 Hc.
  unfold g_axis_lo.
  destruct (b64_eqb c1 c0) eqn:Eeq.
  - apply (proj1 (b64_eqb_true_iff_B2R _ _ F1 F0)) in Eeq.
    split; [exact is_finite_b64_zero|].
    unfold lb_tlo. destruct (Req_dec_T _ _) as [_|Hn]; [|exfalso; apply Hn; exact Eeq].
    rewrite B2R_b64_zero. lra.
  - assert (Hne : B2R c1 <> B2R c0).
    { intro H. apply (proj2 (b64_eqb_true_iff_B2R _ _ F1 F0)) in H.
      rewrite H in Eeq. discriminate. }
    destruct (g_axis_facts c0 c1 cc F0 F1 Fc H0 H1 Hc) as
      (_&_&_&_&_&_&_&_& Fpm&Fpp&Frm&Frp& Rpm&Rpp&Rrm&Rrp& Apm&App&Arm&Arp&
       Fbm&Fbp& Rbm&Rbp).
    unfold lb_tlo. destruct (Req_dec_T _ _) as [Hc'|_]; [exfalso; apply Hne; exact Hc'|].
    pose proof (g_q_lower_ok (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)
                  (B2R cc - / 2 - B2R c0) (B2R c1 - B2R c0)
                  Fpm Fpp Fbm Fbp Apm App Rpm Rpp Rbm Rbp) as Hp.
    pose proof (g_q_lower_ok (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)
                  (B2R cc + / 2 - B2R c0) (B2R c1 - B2R c0)
                  Frm Frp Fbm Fbp Arm Arp Rrm Rrp Rbm Rbp) as Hr.
    unfold opt_min.
    destruct (g_q_lower (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
      as [A|]; [|exact I].
    destruct (g_q_lower (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
      as [Bv|]; [|exact I].
    destruct Hp as [FA HA]. destruct Hr as [FB HB].
    split; [apply is_finite_b64_min; assumption|].
    rewrite (b64_min_B2R _ _ FA FB).
    apply Rmin_mono; assumption.
Qed.


(* POLARITY, upper bound:  exact upper (lb_thi)  <=  computed upper. *)
Lemma g_axis_hi_ok : forall c0 c1 cc,
  fin c0 = true -> fin c1 = true -> fin cc = true ->
  Rabs (B2R c0) <= bpow radix2 500 -> Rabs (B2R c1) <= bpow radix2 500 ->
  Rabs (B2R cc) <= bpow radix2 500 ->
  match g_axis_hi c0 c1 cc with
  | Some v => fin v = true /\
      lb_thi (B2R c0) (B2R c1) (B2R cc - / 2) (B2R cc + / 2) <= B2R v
  | None => True
  end.
Proof.
  intros c0 c1 cc F0 F1 Fc H0 H1 Hc.
  unfold g_axis_hi.
  destruct (b64_eqb c1 c0) eqn:Eeq.
  - apply (proj1 (b64_eqb_true_iff_B2R _ _ F1 F0)) in Eeq.
    destruct B2R_and_finite_b64_one as [B1 F1']. split; [exact F1'|].
    unfold lb_thi. destruct (Req_dec_T _ _) as [_|Hn]; [|exfalso; apply Hn; exact Eeq].
    rewrite B1. lra.
  - assert (Hne : B2R c1 <> B2R c0).
    { intro H. apply (proj2 (b64_eqb_true_iff_B2R _ _ F1 F0)) in H.
      rewrite H in Eeq. discriminate. }
    destruct (g_axis_facts c0 c1 cc F0 F1 Fc H0 H1 Hc) as
      (_&_&_&_&_&_&_&_& Fpm&Fpp&Frm&Frp& Rpm&Rpp&Rrm&Rrp& Apm&App&Arm&Arp&
       Fbm&Fbp& Rbm&Rbp).
    unfold lb_thi. destruct (Req_dec_T _ _) as [Hc'|_]; [exfalso; apply Hne; exact Hc'|].
    pose proof (g_q_upper_ok (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)
                  (B2R cc - / 2 - B2R c0) (B2R c1 - B2R c0)
                  Fpm Fpp Fbm Fbp Apm App Rpm Rpp Rbm Rbp) as Hp.
    pose proof (g_q_upper_ok (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)
                  (B2R cc + / 2 - B2R c0) (B2R c1 - B2R c0)
                  Frm Frp Fbm Fbp Arm Arp Rrm Rrp Rbm Rbp) as Hr.
    unfold opt_max.
    destruct (g_q_upper (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
      as [A|]; [|exact I].
    destruct (g_q_upper (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
      as [Bv|]; [|exact I].
    destruct Hp as [FA HA]. destruct Hr as [FB HB].
    split; [apply is_finite_b64_max; assumption|].
    rewrite (b64_max_B2R _ _ FA FB).
    apply Rmax_mono; assumption.
Qed.


(* The degenerate-axis guard accepts whenever the exact guard does. *)
Lemma g_axis_guard_ok : forall c0 c1 cc,
  fin c0 = true -> fin c1 = true -> fin cc = true ->
  Rabs (B2R c0) <= bpow radix2 500 -> Rabs (B2R c1) <= bpow radix2 500 ->
  Rabs (B2R cc) <= bpow radix2 500 ->
  lb_inslab (B2R c0) (B2R c1) (B2R cc - / 2) (B2R cc + / 2) = true ->
  g_axis_guard c0 c1 cc = true.
Proof.
  intros c0 c1 cc F0 F1 Fc H0 H1 Hc Hs.
  destruct (g_axis_facts c0 c1 cc F0 F1 Fc H0 H1 Hc) as
    (Flm&_&_&Fhp& Rlm&_&_&Rhp& _).
  unfold g_axis_guard.
  destruct (b64_eqb c1 c0) eqn:Eeq; [|reflexivity].
  apply (proj1 (b64_eqb_true_iff_B2R _ _ F1 F0)) in Eeq.
  unfold lb_inslab in Hs. destruct (Req_dec_T _ _) as [_|Hn]; [|exfalso; apply Hn; exact Eeq].
  apply Bool.andb_true_iff in Hs. destruct Hs as [Hs1 Hs2].
  apply Rle_bool_elim in Hs1. apply Rle_bool_elim in Hs2.
  apply Bool.andb_true_iff. split; apply b64_le_complete; try assumption; lra.
Qed.


(* COMPLETENESS of the repaired touch: every exact closed-pixel touch is accepted,
   for EVERY binary64 triple (out-of-domain inputs are accepted by definition). *)
Theorem g_touches_complete :
  forall P0 P1 C : BPoint,
    b64_liang_barsky_touches P0 P1 C = true ->
    g_touches P0 P1 C = true.
Proof.
  intros P0 P1 C Hs. unfold g_touches.
  destruct (b64_dom (bx P0) && b64_dom (by_ P0) && b64_dom (bx P1)
            && b64_dom (by_ P1) && b64_dom (bx C) && b64_dom (by_ C)) eqn:Ed;
    [|reflexivity].
  apply Bool.andb_true_iff in Ed; destruct Ed as [Ed Dcy_].
  apply Bool.andb_true_iff in Ed; destruct Ed as [Ed Dcx_].
  apply Bool.andb_true_iff in Ed; destruct Ed as [Ed Dy1_].
  apply Bool.andb_true_iff in Ed; destruct Ed as [Ed Dx1_].
  apply Bool.andb_true_iff in Ed; destruct Ed as [Dx0_ Dy0_].
  destruct (dom_ok _ Dcy_) as [Fcy Hcy]. destruct (dom_ok _ Dcx_) as [Fcx Hcx].
  destruct (dom_ok _ Dy1_) as [Fy1 Hy1]. destruct (dom_ok _ Dx1_) as [Fx1 Hx1].
  destruct (dom_ok _ Dy0_) as [Fy0 Hy0]. destruct (dom_ok _ Dx0_) as [Fx0 Hx0].
  unfold b64_liang_barsky_touches in Hs. cbv zeta in Hs.
  apply Bool.andb_true_iff in Hs. destruct Hs as [Hab Hcmp].
  apply Bool.andb_true_iff in Hab. destruct Hab as [HA HB].
  apply Rle_bool_elim in Hcmp.
  apply Bool.andb_true_iff. split.
  - apply Bool.andb_true_iff. split.
    + exact (g_axis_guard_ok _ _ _ Fx0 Fx1 Fcx Hx0 Hx1 Hcx HA).
    + exact (g_axis_guard_ok _ _ _ Fy0 Fy1 Fcy Hy0 Hy1 Hcy HB).
  - pose proof (g_axis_lo_ok _ _ _ Fx0 Fx1 Fcx Hx0 Hx1 Hcx) as Lx.
    pose proof (g_axis_lo_ok _ _ _ Fy0 Fy1 Fcy Hy0 Hy1 Hcy) as Ly.
    pose proof (g_axis_hi_ok _ _ _ Fx0 Fx1 Fcx Hx0 Hx1 Hcx) as Ux.
    pose proof (g_axis_hi_ok _ _ _ Fy0 Fy1 Fcy Hy0 Hy1 Hcy) as Uy.
    destruct (ub_max_ok b64_zero (g_axis_lo (bx P0) (bx P1) (bx C)) 0
                (lb_tlo (B2R (bx P0)) (B2R (bx P1))
                   (B2R (bx C) - / 2) (B2R (bx C) + / 2))
                is_finite_b64_zero ltac:(rewrite B2R_b64_zero; lra) Lx)
      as [F1 B1].
    destruct (ub_max_ok (ub_max b64_zero (g_axis_lo (bx P0) (bx P1) (bx C)))
                (g_axis_lo (by_ P0) (by_ P1) (by_ C))
                (Rmax 0 (lb_tlo (B2R (bx P0)) (B2R (bx P1))
                   (B2R (bx C) - / 2) (B2R (bx C) + / 2)))
                (lb_tlo (B2R (by_ P0)) (B2R (by_ P1))
                   (B2R (by_ C) - / 2) (B2R (by_ C) + / 2))
                F1 B1 Ly) as [F2 B2].
    destruct B2R_and_finite_b64_one as [Bone Fone].
    destruct (ub_min_ok b64_one (g_axis_hi (bx P0) (bx P1) (bx C)) 1
                (lb_thi (B2R (bx P0)) (B2R (bx P1))
                   (B2R (bx C) - / 2) (B2R (bx C) + / 2))
                Fone ltac:(rewrite Bone; lra) Ux) as [F3 B3].
    destruct (ub_min_ok (ub_min b64_one (g_axis_hi (bx P0) (bx P1) (bx C)))
                (g_axis_hi (by_ P0) (by_ P1) (by_ C))
                (Rmin 1 (lb_thi (B2R (bx P0)) (B2R (bx P1))
                   (B2R (bx C) - / 2) (B2R (bx C) + / 2)))
                (lb_thi (B2R (by_ P0)) (B2R (by_ P1))
                   (B2R (by_ C) - / 2) (B2R (by_ C) + / 2))
                F3 B3 Uy) as [F4 B4].
    apply b64_le_complete; [exact F2 | exact F4|].
    rewrite <- Rmax_assoc in B2. rewrite <- Rmin_assoc in B4.
    eapply Rle_trans; [exact B2|].
    eapply Rle_trans; [exact Hcmp | exact B4].
Qed.


End Generic.

(* -------------------------------------------------------------------------- *)
(* §6  Instance 1: Flocq directed rounding (mode_DN / mode_UP).               *)
(* -------------------------------------------------------------------------- *)
Lemma flocq_sdn_ok : forall x y k, fin x = true -> fin y = true ->
  (0 <= k <= 1000)%Z -> Rabs (B2R x - B2R y) <= bpow radix2 k ->
  fin (b64_minus_m mode_DN x y) = true /\
  B2R (b64_minus_m mode_DN x y) <= B2R x - B2R y /\
  Rabs (B2R (b64_minus_m mode_DN x y)) <= bpow radix2 (k + 1).
Proof.
  intros x y k Fx Fy Hk Hb. destruct (dir_minus mode_DN x y k Fx Fy Hk Hb) as [F [E A]].
  refine (conj F (conj _ _)).
  - rewrite E. apply round_dn_le.
  - eapply Rle_trans; [exact A | apply bpow_mono; lia].
Qed.
Lemma flocq_sup_ok : forall x y k, fin x = true -> fin y = true ->
  (0 <= k <= 1000)%Z -> Rabs (B2R x - B2R y) <= bpow radix2 k ->
  fin (b64_minus_m mode_UP x y) = true /\
  B2R x - B2R y <= B2R (b64_minus_m mode_UP x y) /\
  Rabs (B2R (b64_minus_m mode_UP x y)) <= bpow radix2 (k + 1).
Proof.
  intros x y k Fx Fy Hk Hb. destruct (dir_minus mode_UP x y k Fx Fy Hk Hb) as [F [E A]].
  refine (conj F (conj _ _)).
  - rewrite E. apply round_up_ge.
  - eapply Rle_trans; [exact A | apply bpow_mono; lia].
Qed.
Lemma flocq_adn_ok : forall x y k, fin x = true -> fin y = true ->
  (0 <= k <= 1000)%Z -> Rabs (B2R x + B2R y) <= bpow radix2 k ->
  fin (b64_plus_m mode_DN x y) = true /\
  B2R (b64_plus_m mode_DN x y) <= B2R x + B2R y /\
  Rabs (B2R (b64_plus_m mode_DN x y)) <= bpow radix2 (k + 1).
Proof.
  intros x y k Fx Fy Hk Hb. destruct (dir_plus mode_DN x y k Fx Fy Hk Hb) as [F [E A]].
  refine (conj F (conj _ _)).
  - rewrite E. apply round_dn_le.
  - eapply Rle_trans; [exact A | apply bpow_mono; lia].
Qed.
Lemma flocq_aup_ok : forall x y k, fin x = true -> fin y = true ->
  (0 <= k <= 1000)%Z -> Rabs (B2R x + B2R y) <= bpow radix2 k ->
  fin (b64_plus_m mode_UP x y) = true /\
  B2R x + B2R y <= B2R (b64_plus_m mode_UP x y) /\
  Rabs (B2R (b64_plus_m mode_UP x y)) <= bpow radix2 (k + 1).
Proof.
  intros x y k Fx Fy Hk Hb. destruct (dir_plus mode_UP x y k Fx Fy Hk Hb) as [F [E A]].
  refine (conj F (conj _ _)).
  - rewrite E. apply round_up_ge.
  - eapply Rle_trans; [exact A | apply bpow_mono; lia].
Qed.
Lemma flocq_ddn_ok : forall x y, fin x = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
  fin (b64_div_m mode_DN x y) = true /\
  B2R (b64_div_m mode_DN x y) <= B2R x / B2R y.
Proof.
  intros x y Fx Hy Hb. destruct (div_m_ok mode_DN x y Fx Hy Hb) as [F E].
  split; [exact F|]. rewrite E. apply round_dn_le.
Qed.
Lemma flocq_dup_ok : forall x y, fin x = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
  fin (b64_div_m mode_UP x y) = true /\
  B2R x / B2R y <= B2R (b64_div_m mode_UP x y).
Proof.
  intros x y Fx Hy Hb. destruct (div_m_ok mode_UP x y Fx Hy Hb) as [F E].
  split; [exact F|]. rewrite E. apply round_up_ge.
Qed.

Definition flocq_prims : dprims :=
  mkDP (b64_minus_m mode_DN) (b64_minus_m mode_UP)
       (b64_plus_m mode_DN) (b64_plus_m mode_UP)
       (b64_div_m mode_DN) (b64_div_m mode_UP)
       flocq_sdn_ok flocq_sup_ok flocq_adn_ok flocq_aup_ok
       flocq_ddn_ok flocq_dup_ok.

(* Canonical names for the Flocq-mode filter (instances of the generic proof). *)
Definition axis_lo (c0 c1 cc : binary64) : option binary64 := g_axis_lo flocq_prims c0 c1 cc.
Definition axis_hi (c0 c1 cc : binary64) : option binary64 := g_axis_hi flocq_prims c0 c1 cc.

Lemma axis_lo_ok : forall c0 c1 cc,
  fin c0 = true -> fin c1 = true -> fin cc = true ->
  Rabs (B2R c0) <= bpow radix2 500 -> Rabs (B2R c1) <= bpow radix2 500 ->
  Rabs (B2R cc) <= bpow radix2 500 ->
  match axis_lo c0 c1 cc with
  | Some v => fin v = true /\
      B2R v <= lb_tlo (B2R c0) (B2R c1) (B2R cc - / 2) (B2R cc + / 2)
  | None => True
  end.
Proof. intros. apply g_axis_lo_ok; assumption. Qed.

Lemma axis_hi_ok : forall c0 c1 cc,
  fin c0 = true -> fin c1 = true -> fin cc = true ->
  Rabs (B2R c0) <= bpow radix2 500 -> Rabs (B2R c1) <= bpow radix2 500 ->
  Rabs (B2R cc) <= bpow radix2 500 ->
  match axis_hi c0 c1 cc with
  | Some v => fin v = true /\
      lb_thi (B2R c0) (B2R c1) (B2R cc - / 2) (B2R cc + / 2) <= B2R v
  | None => True
  end.
Proof. intros. apply g_axis_hi_ok; assumption. Qed.

Definition b64_touches_cons (P0 P1 C : BPoint) : bool := g_touches flocq_prims P0 P1 C.

(* COMPLETENESS: every exact closed-pixel touch is accepted, for EVERY binary64
   triple (out-of-domain inputs are accepted by definition). *)
Theorem b64_touches_complete_cons :
  forall P0 P1 C : BPoint,
    b64_liang_barsky_touches P0 P1 C = true ->
    b64_touches_cons P0 P1 C = true.
Proof. intros. exact (g_touches_complete flocq_prims P0 P1 C H). Qed.

Definition b64_passes_through_hot_pixel_cons (P0 P1 C : BPoint) : bool :=
  b64_touches_cons P0 P1 C &&
  b64_touches_cons (b64_snap P0) (b64_snap P1) C.

Theorem b64_passes_through_complete_cons :
  forall P0 P1 C : BPoint,
    b64_passes_through_hot_pixel P0 P1 C = true ->
    b64_passes_through_hot_pixel_cons P0 P1 C = true.
Proof.
  intros P0 P1 C H. unfold b64_passes_through_hot_pixel in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  unfold b64_passes_through_hot_pixel_cons.
  apply Bool.andb_true_iff. split;
    apply b64_touches_complete_cons; assumption.
Qed.

Print Assumptions g_q_lower_ok.
Print Assumptions g_q_upper_ok.
Print Assumptions g_axis_lo_ok.
Print Assumptions g_axis_hi_ok.
Print Assumptions g_touches_complete.
Print Assumptions b64_passes_through_complete_cons.
