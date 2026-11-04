(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_ArcPoint
   ----------------------------------------------------------------------------
   S5: the reusable arc-point lemma (claimId: s5-b64-arc-point, witness:
   b64_arc_pt_err).  The binary64 point

     x = fl(cx + fl(r * b64_cos t)),   y = fl(cy + fl(r * b64_sin t))

   is, coordinate by coordinate, within arc_E Cm Rm of c + r (cos t, sin t)
   when |cx|, |cy| <= Cm, |r| <= Rm and sin_accept t (|t| <= 10).  arc_E
   carries every rounding: the trig error 2^-49 (b64_cos_err /
   b64_sin_err), the product and the sum (u |.| + e0 each), and is bounded
   by Rm / 2^48 + Cm / 2^53 + 2^-1073 (arc_E_le).

   Two consumer forms, for what S0 says exists (inventory T5, densify):
     b64_arc_pt_theta        the angle itself off by eta: + Rm eta per
                             coordinate (cos / sin are 1-Lipschitz)
     b64_arc_pt_near_circle  the computed vertex is within 3/2 arc_E Cm Rm of
                             the circle |p - c| = |r|, however t was
                             computed (atan2, sweep i/n, ...)
   b64_arc_pt_err_b states the extractable intake: |cx|, |cy|, |r| <= 2^998.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith Rgeom.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import LipInt.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly B64_Sin B64_Cos.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  The evaluator and its error budget.                                    *)
(* -------------------------------------------------------------------------- *)

Definition b64_arc_x (cx r t : binary64) : binary64 := b64_plus cx (b64_mult r (b64_cos t)).
Definition b64_arc_y (cy r t : binary64) : binary64 := b64_plus cy (b64_mult r (b64_sin t)).

Definition ap_delta : R := bpow radix2 (-49).

Definition arc_E (Cm Rm : R) : R :=
  Rm * ap_delta + (b64ae_u * (Rm * (1 + ap_delta)) + b64ae_e0)
  + (b64ae_u * (Cm + (Rm * (1 + ap_delta) * (1 + b64ae_u) + b64ae_e0)) + b64ae_e0).

Lemma ap_delta_val : ap_delta = / 562949953421312.
Proof. unfold ap_delta. cbn. reflexivity. Qed.

Lemma ap_delta_small : 0 < ap_delta <= / 1000.
Proof. rewrite ap_delta_val. lra. Qed.

Lemma arc_E_nonneg : forall Cm Rm, 0 <= Cm -> 0 <= Rm -> 0 <= arc_E Cm Rm.
Proof.
  intros Cm Rm HC HR. unfold arc_E.
  pose proof b64ae_u_small. pose proof b64ae_e0_small. pose proof ap_delta_small.
  assert (0 <= Rm * ap_delta) by (apply Rmult_le_pos; lra).
  assert (0 <= Rm * (1 + ap_delta)) by (apply Rmult_le_pos; lra).
  assert (0 <= Rm * (1 + ap_delta) * (1 + b64ae_u)) by (apply Rmult_le_pos; lra).
  assert (0 <= b64ae_u * (Rm * (1 + ap_delta))) by (apply Rmult_le_pos; lra).
  assert (0 <= b64ae_u * (Cm + (Rm * (1 + ap_delta) * (1 + b64ae_u) + b64ae_e0)))
    by (apply Rmult_le_pos; lra).
  lra.
Qed.

(* A closed, outward-rounded form of the budget. *)
Lemma arc_E_le : forall Cm Rm, 0 <= Cm -> 0 <= Rm ->
  arc_E Cm Rm <= Rm / 281474976710656 + Cm / 9007199254740992 + bpow radix2 (-1073).
Proof.
  intros Cm Rm HC HR. unfold arc_E.
  rewrite ap_delta_val, sp_u_val.
  replace (bpow radix2 (-1073)) with (4 * b64ae_e0).
  2:{ unfold b64ae_e0. change (-1073)%Z with (2 + (-1075))%Z. rewrite bpow_plus.
      replace (bpow radix2 2) with 4 by (cbn; lra). reflexivity. }
  pose proof b64ae_e0_small as [E0 E1].
  assert (/ 9007199254740992 * b64ae_e0 <= b64ae_e0) by nra.
  lra.
Qed.

(* One coordinate: fl(c + fl(r * s)) against c + r f, |s - f| <= 2^-49. *)
Lemma ap_coord : forall (c r s : binary64) (f Cm Rm : R),
  fin c = true -> fin r = true -> fin s = true ->
  Rabs (B2R c) <= Cm -> Rabs (B2R r) <= Rm -> Rabs f <= 1 ->
  Rabs (B2R s - f) <= ap_delta ->
  Cm + 2 * Rm + 1 <= bpow radix2 1000 ->
  fin (b64_plus c (b64_mult r s)) = true /\
  Rabs (B2R (b64_plus c (b64_mult r s)) - (B2R c + B2R r * f)) <= arc_E Cm Rm.
Proof.
  intros c r s f Cm Rm Fc Fr Fs Hc Hr Hf Hs Hg.
  pose proof b64ae_u_small as [U0 U1]. pose proof b64ae_e0_small as [E0 E1].
  pose proof ap_delta_small as [D0 D1].
  assert (C0 : 0 <= Cm) by (pose proof (Rabs_pos (B2R c)); lra).
  assert (R0 : 0 <= Rm) by (pose proof (Rabs_pos (B2R r)); lra).
  assert (Bs : Rabs (B2R s) <= 1 + ap_delta)
    by (pose proof (Rabs_triang_inv (B2R s) f); lra).
  assert (Bp : Rabs (B2R r * B2R s) <= Rm * (1 + ap_delta))
    by (apply b64ae_abs_mult_le; assumption).
  assert (K2 : (1 + ap_delta) * (1 + b64ae_u) <= 2) by nra.
  assert (R2 : Rm * ((1 + ap_delta) * (1 + b64ae_u)) <= Rm * 2)
    by (apply Rmult_le_compat_l; lra).
  assert (R1 : Rm * (1 + ap_delta) <= Rm * ((1 + ap_delta) * (1 + b64ae_u)))
    by (apply Rmult_le_compat_l; nra).
  destruct (b64ae_mult_err r s Fr Fs ltac:(lra)) as [Fp Ep].
  pose proof (b64ae_u_mul_le _ _ Bp) as Up.
  revert Fp Ep. generalize (b64_mult r s). intros p Fp Ep.
  assert (Bpp : Rabs (B2R p) <= Rm * (1 + ap_delta) * (1 + b64ae_u) + b64ae_e0).
  { pose proof (Rabs_triang_inv (B2R p) (B2R r * B2R s)).
    assert (Rabs (B2R r * B2R s) * (1 + b64ae_u) <= Rm * (1 + ap_delta) * (1 + b64ae_u))
      by (apply Rmult_le_compat_r; lra).
    lra. }
  assert (Bsum : Rabs (B2R c + B2R p)
                 <= Cm + (Rm * (1 + ap_delta) * (1 + b64ae_u) + b64ae_e0)).
  { eapply Rle_trans; [apply Rabs_triang|]. lra. }
  destruct (b64ae_plus_err c p Fc Fp ltac:(eapply Rle_trans; [exact Bsum|]; lra)) as [Fx Ex].
  pose proof (b64ae_u_mul_le _ _ Bsum) as Ux.
  split; [exact Fx|].
  revert Fx Ex. generalize (b64_plus c p). intros x Fx Ex.
  assert (Bt : Rabs (B2R r * (B2R s - f)) <= Rm * ap_delta)
    by (apply b64ae_abs_mult_le; assumption).
  replace (B2R x - (B2R c + B2R r * f))
    with ((B2R x - (B2R c + B2R p)) + (B2R p - B2R r * B2R s) + B2R r * (B2R s - f)) by ring.
  pose proof (Rabs_triang ((B2R x - (B2R c + B2R p)) + (B2R p - B2R r * B2R s))
                          (B2R r * (B2R s - f))) as T1.
  pose proof (Rabs_triang (B2R x - (B2R c + B2R p)) (B2R p - B2R r * B2R s)) as T2.
  unfold arc_E. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The arc-point lemma.                                                   *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"s5-b64-arc-point","topic":"numerics","lemma":"b64_arc_pt_err","title":"Binary64 arc point: fl(c + fl(r * b64_cos t)), fl(c + fl(r * b64_sin t)) is finite and within arc_E Cm Rm <= Rm/2^48 + Cm/2^53 + 2^-1073 of c + r (cos t, sin t) per coordinate, for |c| <= Cm, |r| <= Rm, |t| <= 10","file":"theories-flocq/B64_ArcPoint.v","witness":"b64_arc_pt_err","board":"ADR-0006"} *)
Theorem b64_arc_pt_err : forall (cx cy r t : binary64) (Cm Rm : R),
  sin_accept t = true -> fin cx = true -> fin cy = true -> fin r = true ->
  Rabs (B2R cx) <= Cm -> Rabs (B2R cy) <= Cm -> Rabs (B2R r) <= Rm ->
  Cm + 2 * Rm + 1 <= bpow radix2 1000 ->
  fin (b64_arc_x cx r t) = true /\ fin (b64_arc_y cy r t) = true /\
  Rabs (B2R (b64_arc_x cx r t) - (B2R cx + B2R r * cos (B2R t))) <= arc_E Cm Rm /\
  Rabs (B2R (b64_arc_y cy r t) - (B2R cy + B2R r * sin (B2R t))) <= arc_E Cm Rm.
Proof.
  intros cx cy r t Cm Rm Ht Fx Fy Fr Hx Hy Hr Hg.
  destruct (b64_cos_err t Ht) as [Fc Ec]. destruct (b64_sin_err t Ht) as [Fs Es].
  fold ap_delta in Ec, Es.
  assert (Hc1 : Rabs (cos (B2R t)) <= 1) by (apply Rabs_le; apply COS_bound).
  assert (Hs1 : Rabs (sin (B2R t)) <= 1) by (apply Rabs_le; apply SIN_bound).
  destruct (ap_coord cx r _ _ Cm Rm Fx Fr Fc Hx Hr Hc1 Ec Hg) as [FX EX].
  destruct (ap_coord cy r _ _ Cm Rm Fy Fr Fs Hy Hr Hs1 Es Hg) as [FY EY].
  unfold b64_arc_x, b64_arc_y. auto.
Qed.

(* The angle carried an error eta (e.g. atan2 + sweep i/n). *)
Corollary b64_arc_pt_theta : forall (cx cy r t : binary64) (Cm Rm theta eta : R),
  sin_accept t = true -> fin cx = true -> fin cy = true -> fin r = true ->
  Rabs (B2R cx) <= Cm -> Rabs (B2R cy) <= Cm -> Rabs (B2R r) <= Rm ->
  Cm + 2 * Rm + 1 <= bpow radix2 1000 ->
  Rabs (B2R t - theta) <= eta ->
  Rabs (B2R (b64_arc_x cx r t) - (B2R cx + B2R r * cos theta)) <= arc_E Cm Rm + Rm * eta /\
  Rabs (B2R (b64_arc_y cy r t) - (B2R cy + B2R r * sin theta)) <= arc_E Cm Rm + Rm * eta.
Proof.
  intros cx cy r t Cm Rm theta eta Ht Fx Fy Fr Hx Hy Hr Hg He.
  destruct (b64_arc_pt_err cx cy r t Cm Rm Ht Fx Fy Fr Hx Hy Hr Hg) as [_ [_ [EX EY]]].
  assert (Lc : Rabs (B2R r * (cos (B2R t) - cos theta)) <= Rm * eta).
  { apply b64ae_abs_mult_le; [exact Hr|]. eapply Rle_trans; [apply cos_lip | exact He]. }
  assert (Ls : Rabs (B2R r * (sin (B2R t) - sin theta)) <= Rm * eta).
  { apply b64ae_abs_mult_le; [exact Hr|]. eapply Rle_trans; [apply sin_lip | exact He]. }
  revert EX EY. generalize (B2R (b64_arc_x cx r t)) (B2R (b64_arc_y cy r t)). intros X Y EX EY.
  split.
  - replace (X - (B2R cx + B2R r * cos theta))
      with ((X - (B2R cx + B2R r * cos (B2R t))) + B2R r * (cos (B2R t) - cos theta)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra.
  - replace (Y - (B2R cy + B2R r * sin theta))
      with ((Y - (B2R cy + B2R r * sin (B2R t))) + B2R r * (sin (B2R t) - sin theta)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Consumer: densified vertices lie near the arc's circle.                *)
(* -------------------------------------------------------------------------- *)

Lemma ap_circle_radius : forall cx cy r t,
  dist_euc (cx + r * cos t) (cy + r * sin t) cx cy = Rabs r.
Proof.
  intros cx cy r t. unfold dist_euc.
  replace (Rsqr (cx + r * cos t - cx) + Rsqr (cy + r * sin t - cy)) with (Rsqr r).
  - apply sqrt_Rsqr_abs.
  - unfold Rsqr. pose proof (sin2_cos2 t) as H. unfold Rsqr in H.
    replace (r * r) with (r * r * (sin t * sin t + cos t * cos t)) by (rewrite H; ring).
    ring.
Qed.

Lemma ap_dist_box : forall x0 y0 x1 y1 E,
  Rabs (x0 - x1) <= E -> Rabs (y0 - y1) <= E -> dist_euc x0 y0 x1 y1 <= 3 / 2 * E.
Proof.
  intros x0 y0 x1 y1 E Hx Hy. unfold dist_euc.
  assert (E0 : 0 <= E) by (pose proof (Rabs_pos (x0 - x1)); lra).
  rewrite <- (sqrt_square (3 / 2 * E)) by lra.
  apply sqrt_le_1_alt.
  rewrite !Rsqr_abs with (x := x0 - x1), Rsqr_abs with (x := y0 - y1). unfold Rsqr.
  assert (Rabs (x0 - x1) * Rabs (x0 - x1) <= E * E)
    by (apply Rmult_le_compat; try apply Rabs_pos; assumption).
  assert (Rabs (y0 - y1) * Rabs (y0 - y1) <= E * E)
    by (apply Rmult_le_compat; try apply Rabs_pos; assumption).
  nra.
Qed.

Theorem b64_arc_pt_near_circle : forall (cx cy r t : binary64) (Cm Rm : R),
  sin_accept t = true -> fin cx = true -> fin cy = true -> fin r = true ->
  Rabs (B2R cx) <= Cm -> Rabs (B2R cy) <= Cm -> Rabs (B2R r) <= Rm ->
  Cm + 2 * Rm + 1 <= bpow radix2 1000 ->
  Rabs (dist_euc (B2R (b64_arc_x cx r t)) (B2R (b64_arc_y cy r t)) (B2R cx) (B2R cy)
        - Rabs (B2R r)) <= 3 / 2 * arc_E Cm Rm.
Proof.
  intros cx cy r t Cm Rm Ht Fx Fy Fr Hx Hy Hr Hg.
  destruct (b64_arc_pt_err cx cy r t Cm Rm Ht Fx Fy Fr Hx Hy Hr Hg) as [_ [_ [EX EY]]].
  revert EX EY. generalize (B2R (b64_arc_x cx r t)) (B2R (b64_arc_y cy r t)). intros X Y EX EY.
  set (qx := B2R cx + B2R r * cos (B2R t)). set (qy := B2R cy + B2R r * sin (B2R t)).
  assert (Dq : dist_euc qx qy (B2R cx) (B2R cy) = Rabs (B2R r)) by apply ap_circle_radius.
  assert (Dpq : dist_euc X Y qx qy <= 3 / 2 * arc_E Cm Rm) by (apply ap_dist_box; assumption).
  pose proof (triangle X Y (B2R cx) (B2R cy) qx qy) as T1.
  pose proof (triangle qx qy (B2R cx) (B2R cy) X Y) as T2.
  rewrite (distance_symm qx qy X Y) in T2.
  apply Rabs_le. split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Extractable intake.                                                    *)
(* -------------------------------------------------------------------------- *)

(* 2^998 and -2^998: |cx|, |cy|, |r| <= 2^998 gives 3 * 2^998 + 1 <= 2^1000. *)
Definition ap_cap : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (946) eq_refl.
Definition ap_mcap : binary64 :=
  Binary.B754_finite prec emax true 4503599627370496 (946) eq_refl.

Lemma ap_cap_R : B2R ap_cap = bpow radix2 998 /\ B2R ap_mcap = - bpow radix2 998.
Proof.
  replace (bpow radix2 998) with (IZR (Zpos 4503599627370496) * bpow radix2 946)
    by (replace 998%Z with (52 + 946)%Z by reflexivity; rewrite bpow_plus; reflexivity).
  unfold ap_cap, ap_mcap. cbn [Binary.B2R]. unfold F2R. cbn [Fnum Fexp cond_Zopp].
  split; [reflexivity|]. rewrite Ropp_mult_distr_l, <- opp_IZR. reflexivity.
Qed.

Definition ap_in (x : binary64) : bool := b64_le ap_mcap x && b64_le x ap_cap.

Lemma ap_in_ok : forall x, ap_in x = true ->
  fin x = true /\ Rabs (B2R x) <= bpow radix2 998.
Proof.
  intros x H.
  assert (Fx : fin x = true).
  { destruct x as [s|s|s pl Hpl|s m e Hb]; try reflexivity;
      unfold ap_in in H; destruct s; vm_compute in H; discriminate H. }
  split; [exact Fx|].
  unfold ap_in in H. apply andb_prop in H as [Hlo Hhi].
  destruct ap_cap_R as [Ec Em].
  apply b64ae_le_true in Hlo; [|reflexivity|exact Fx].
  apply b64ae_le_true in Hhi; [|exact Fx|reflexivity].
  rewrite Em in Hlo. rewrite Ec in Hhi. apply Rabs_le. split; lra.
Qed.

Definition arc_accept_b (cx cy r t : binary64) : bool :=
  ap_in cx && ap_in cy && ap_in r && sin_accept_b t.

Corollary b64_arc_pt_err_b : forall cx cy r t,
  arc_accept_b cx cy r t = true ->
  fin (b64_arc_x cx r t) = true /\ fin (b64_arc_y cy r t) = true /\
  Rabs (B2R (b64_arc_x cx r t) - (B2R cx + B2R r * cos (B2R t)))
    <= arc_E (bpow radix2 998) (bpow radix2 998) /\
  Rabs (B2R (b64_arc_y cy r t) - (B2R cy + B2R r * sin (B2R t)))
    <= arc_E (bpow radix2 998) (bpow radix2 998).
Proof.
  intros cx cy r t H. unfold arc_accept_b in H.
  apply andb_prop in H as [H Ht]. apply andb_prop in H as [H Hr].
  apply andb_prop in H as [Hx Hy].
  rewrite sin_accept_b_eq in Ht.
  destruct (ap_in_ok _ Hx) as [Fx Bx]. destruct (ap_in_ok _ Hy) as [Fy By].
  destruct (ap_in_ok _ Hr) as [Fr Br].
  apply (b64_arc_pt_err cx cy r t _ _ Ht Fx Fy Fr Bx By Br).
  replace 1000%Z with (2 + 998)%Z by reflexivity. rewrite bpow_plus.
  replace (bpow radix2 2) with 4 by (cbn; lra).
  assert (1 <= bpow radix2 998) by (apply Rle_trans with (bpow radix2 0);
                                     [cbn; lra | apply bpow_le; lia]).
  lra.
Qed.

Print Assumptions arc_E_le.
Print Assumptions ap_coord.
Print Assumptions b64_arc_pt_err.
Print Assumptions b64_arc_pt_theta.
Print Assumptions b64_arc_pt_near_circle.
Print Assumptions ap_in_ok.
Print Assumptions b64_arc_pt_err_b.
