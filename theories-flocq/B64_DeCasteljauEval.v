(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_DeCasteljauEval
   ----------------------------------------------------------------------------
   Extractable, guarded entry point for the binary64 de Casteljau evaluator of
   B64_DeCasteljau.v: the function the `B64_DECASTELJAU` oracle mode runs and
   that ports must match bit for bit.

   `dc_eval cs t` for control values cs (binary64, degree n = length cs - 1)
   and a parameter t:

     DC_DeclineEmpty       cs = []
     DC_DeclineDegree      length cs > 1001                (n > 1000)
     DC_DeclineNonfinite   t or some control is NaN / +-Inf
     DC_DeclineParam       t not in [0, 1]
     DC_DeclineGuard       some |control| > 2^500
     DC_Certified v        v = dcF (fl(1 - t)) t n cs

   (checks are made in exactly this order).  `dc_eval_certified` proves that a
   Certified v is finite and within the b64_decasteljau_err_fl bound
       ((1+kappa)^n - 1) M + 2^-1075 (3+2u) n (1+kappa)^n,
       kappa = dc_kappa (u + 2^-1075),
   of the exact de Casteljau value of the same controls, for every M with
   |b_i| <= M <= 2^500.  The two numeric caps (degree 1000, controls 2^500) are
   NOT the theorem's own hypotheses: they are conservative, decidable
   sufficient conditions for its overflow guard (M + E)*4 + 1 <= 2^1000
   (`dc_guard_ok`).

   The operation sequence is the proved one: s = fl(1 - t) (b64_minus), then
   per node fl( fl(s x) + fl(t y) ) -- two separately rounded multiplies and
   one rounded add.  Any port must not contract these into an FMA; an FMA
   variant would be a different theorem.

   Extractable: no is_finite match (the native-float extraction does not
   support it); finiteness is decided by comparison with +-DBL_MAX, which
   rejects NaN and both infinities.

   claimId: s1-b64-decasteljau-eval.  witness: dc_eval_certified.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia Psatz ZArith List Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib B64_AbsErr
  B64_Horner B64_HornerGamma B64_DeCasteljau.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  Constants (exact binary64 values; extraction overrides them with hex    *)
(*     literals, as for cm_cap).                                              *)
(* -------------------------------------------------------------------------- *)

(* 1, 2^500, -2^500, DBL_MAX = (2^53 - 1) 2^971, -DBL_MAX *)
Definition dc_one : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition dc_cap : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 448 eq_refl.
Definition dc_mcap : binary64 :=
  Binary.B754_finite prec emax true 4503599627370496 448 eq_refl.
Definition dc_fmax : binary64 :=
  Binary.B754_finite prec emax false 9007199254740991 971 eq_refl.
Definition dc_mfmax : binary64 :=
  Binary.B754_finite prec emax true 9007199254740991 971 eq_refl.

Lemma dc_consts_R :
  B2R dc_one = 1 /\ B2R dc_cap = bpow radix2 500 /\ B2R dc_mcap = - bpow radix2 500.
Proof.
  unfold dc_one, dc_cap, dc_mcap. cbn [Binary.B2R]. unfold F2R. cbn [Fnum Fexp cond_Zopp].
  replace (bpow radix2 500) with (IZR (Zpos 4503599627370496) * bpow radix2 448)
    by (replace 500%Z with (52 + 448)%Z by reflexivity; rewrite bpow_plus; reflexivity).
  split.
  - replace 1 with (bpow radix2 0) by reflexivity.
    replace 0%Z with (52 + -52)%Z by reflexivity. rewrite bpow_plus. reflexivity.
  - split; [reflexivity|]. rewrite Ropp_mult_distr_l, <- opp_IZR. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Comparison-based intake.                                               *)
(* -------------------------------------------------------------------------- *)

Lemma dc_le_fin : forall lo hi x, fin lo = true -> fin hi = true ->
  andb (b64_le lo x) (b64_le x hi) = true -> fin x = true /\ B2R lo <= B2R x <= B2R hi.
Proof.
  intros lo hi x Flo Fhi H.
  assert (Fx : fin x = true).
  { destruct x as [s|s|s pl Hpl|s m e Hb]; try reflexivity; exfalso;
      apply andb_prop in H as [H1 H2]; destruct lo as [sl|sl|sl pll Hl|sl ml el Hbl];
      try discriminate Flo; destruct hi as [sh|sh|sh plh Hh|sh mh eh Hbh]; try discriminate Fhi;
      destruct s, sl, sh; cbn in H1, H2; try discriminate H1; try discriminate H2. }
  split; [exact Fx|]. apply andb_prop in H as [H1 H2].
  split; [apply (b64ae_le_true _ _ Flo Fx H1) | apply (b64ae_le_true _ _ Fx Fhi H2)].
Qed.

Definition dc_fin_b (x : binary64) : bool := b64_le dc_mfmax x && b64_le x dc_fmax.

Lemma dc_fin_b_fin : forall x, dc_fin_b x = true -> fin x = true.
Proof. intros x H. exact (proj1 (dc_le_fin dc_mfmax dc_fmax x eq_refl eq_refl H)). Qed.

Definition dc_t_ok (t : binary64) : bool := b64_le hz_zero t && b64_le t dc_one.

Lemma dc_t_ok_R : forall t, dc_t_ok t = true -> fin t = true /\ 0 <= B2R t <= 1.
Proof.
  intros t H. destruct (dc_le_fin hz_zero dc_one t eq_refl eq_refl H) as [F [L U]].
  split; [exact F|]. destruct dc_consts_R as [H1 _]. rewrite H1 in U.
  cbn [hz_zero Binary.B2R] in L. lra.
Qed.

Definition dc_ctrl_ok (c : binary64) : bool := b64_le dc_mcap c && b64_le c dc_cap.

Lemma dc_ctrl_ok_R : forall c, dc_ctrl_ok c = true ->
  fin c = true /\ Rabs (B2R c) <= bpow radix2 500.
Proof.
  intros c H. destruct (dc_le_fin dc_mcap dc_cap c eq_refl eq_refl H) as [F [L U]].
  split; [exact F|]. destruct dc_consts_R as [_ [H2 H3]]. rewrite H2 in U. rewrite H3 in L.
  apply Rabs_le. split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The guarded evaluator.                                                 *)
(* -------------------------------------------------------------------------- *)

Inductive dc_outcome : Type :=
  | DC_Certified (v : binary64)
  | DC_DeclineEmpty
  | DC_DeclineDegree
  | DC_DeclineNonfinite
  | DC_DeclineParam
  | DC_DeclineGuard.

Definition dc_max_len : nat := 1001.

Definition dc_eval (cs : list binary64) (t : binary64) : dc_outcome :=
  match cs with
  | [] => DC_DeclineEmpty
  | _ :: _ =>
      if Nat.ltb dc_max_len (length cs) then DC_DeclineDegree
      else if negb (dc_fin_b t && forallb dc_fin_b cs) then DC_DeclineNonfinite
      else if negb (dc_t_ok t) then DC_DeclineParam
      else if negb (forallb dc_ctrl_ok cs) then DC_DeclineGuard
      else DC_Certified (dcF (b64_minus dc_one t) t (Nat.pred (length cs)) cs)
  end.

(* -------------------------------------------------------------------------- *)
(* §4  The caps imply the overflow guard of b64_decasteljau_err.              *)
(* -------------------------------------------------------------------------- *)

Lemma dc_u_tiny : b64ae_u <= / 1000000.
Proof.
  unfold b64ae_u. apply Rle_trans with (bpow radix2 (-20)).
  - apply bpow_le. lia.
  - cbn. lra.
Qed.

Lemma dc_e0_le_u : b64ae_e0 <= b64ae_u.
Proof. unfold b64ae_e0, b64ae_u. apply bpow_le. lia. Qed.

Lemma dc_INR_1000 : INR 1000 = 1000.
Proof. rewrite INR_IZR_INZ. reflexivity. Qed.

Lemma dc_P_big : 16384 <= bpow radix2 500.
Proof.
  apply Rle_trans with (bpow radix2 14).
  - cbn. lra.
  - apply bpow_le. lia.
Qed.

Lemma dc_guard_ok : forall n M, (n <= 1000)%nat -> 0 <= M -> M <= bpow radix2 500 ->
  (M + dc_iter (b64ae_u + b64ae_e0) M n 0) * 4 + 1 <= bpow radix2 1000.
Proof.
  intros n M Hn HM0 HM1.
  pose proof dc_u_tiny as Hu. pose proof dc_e0_le_u as He.
  pose proof b64ae_u_small as [Hu0 _]. pose proof b64ae_e0_small as [He0 He1].
  set (eta := b64ae_u + b64ae_e0).
  assert (Heta0 : 0 <= eta) by (unfold eta; lra).
  assert (Heta1 : eta <= 2 / 1000000) by (unfold eta; lra).
  set (k := dc_kappa eta).
  assert (Hk0 : 0 <= k) by (apply dc_kappa_nonneg; exact Heta0).
  assert (Hk1 : k <= / 2000).
  { unfold k, dc_kappa.
    assert ((1 + eta) * (2 * b64ae_u + b64ae_u * b64ae_u)
            <= (1 + 2 / 1000000) * (2 / 1000000 + / 1000000 * / 1000000)).
    { apply Rmult_le_compat; try lra. nra. nra. }
    lra. }
  assert (HnR : INR n <= 1000).
  { rewrite <- dc_INR_1000. apply le_INR. exact Hn. }
  assert (Hn0 : 0 <= INR n) by apply pos_INR.
  assert (Hnk : INR n * k <= / 2) by nra.
  assert (Hgam := dc_pow_gamma k n Hk0 ltac:(lra) ltac:(lra)).
  assert (Hq : INR n * k / (1 - INR n * k) <= 1).
  { apply (Rmult_le_reg_r (1 - INR n * k)); [lra|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (HPow : (1 + k) ^ n <= 2) by lra.
  assert (HPow0 : 0 <= (1 + k) ^ n) by (apply pow_le; lra).
  pose proof (dc_iter_closed eta M n 0 Heta0 HM0) as Hc.
  fold k in Hc.
  assert (Hrho : dc_rho <= 1).
  { unfold dc_rho. nra. }
  assert (Hrho0 := dc_rho_nonneg).
  assert (HT : dc_rho * INR n * (1 + k) ^ n <= 2000).
  { assert (dc_rho * INR n <= 1000) by nra. nra. }
  assert (HM : ((1 + k) ^ n - 1) * M <= M) by nra.
  assert (HE : dc_iter eta M n 0 <= M + 2000) by nra.
  pose proof dc_P_big as HP.
  assert (Hsq : bpow radix2 1000 = bpow radix2 500 * bpow radix2 500).
  { replace 1000%Z with (500 + 500)%Z by reflexivity. apply bpow_plus. }
  rewrite Hsq. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Soundness of the Certified outcome.                                    *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"s1-b64-decasteljau-eval","topic":"numerics","lemma":"dc_eval_certified","title":"The guarded extractable binary64 de Casteljau evaluator dc_eval (s = fl(1-t), per node fl(fl(s x)+fl(t y)), degree <= 1000, finite controls with |b_i| <= 2^500, t in [0,1]) returns Certified only with a finite value within ((1+kappa)^n-1) M + 2^-1075 (3+2u) n (1+kappa)^n of the exact de Casteljau value, kappa = dc_kappa(u + 2^-1075), for every M with |b_i| <= M <= 2^500; every other input declines with an explicit reason","file":"theories-flocq/B64_DeCasteljauEval.v","witness":"dc_eval_certified","board":"ADR-0006"} *)
Theorem dc_eval_certified : forall cs t v,
  dc_eval cs t = DC_Certified v ->
  exists n, length cs = S n /\ (n <= 1000)%nat /\
    v = dcF (b64_minus dc_one t) t n cs /\
    fin v = true /\
    forall M, 0 <= M -> M <= bpow radix2 500 ->
      Forall (fun c => Rabs (B2R c) <= M) cs ->
      Rabs (B2R v - dcR (1 - B2R t) (B2R t) n (map B2R cs))
      <= ((1 + dc_kappa (b64ae_u + b64ae_e0)) ^ n - 1) * M
         + dc_rho * INR n * (1 + dc_kappa (b64ae_u + b64ae_e0)) ^ n.
Proof.
  intros cs t v H. unfold dc_eval in H.
  destruct cs as [|c0 cs']; [discriminate|].
  set (cs := c0 :: cs') in *.
  destruct (Nat.ltb dc_max_len (length cs)) eqn:Hlen; [discriminate|].
  destruct (negb (dc_fin_b t && forallb dc_fin_b cs)) eqn:Hnf; [discriminate|].
  destruct (negb (dc_t_ok t)) eqn:Hpar; [discriminate|].
  destruct (negb (forallb dc_ctrl_ok cs)) eqn:Hg; [discriminate|].
  injection H as Hv.
  apply Nat.ltb_ge in Hlen. unfold dc_max_len in Hlen.
  apply negb_false_iff in Hnf. apply negb_false_iff in Hpar. apply negb_false_iff in Hg.
  apply andb_prop in Hnf as [Hft Hfc].
  rewrite forallb_forall in Hfc, Hg.
  destruct (dc_t_ok_R t Hpar) as [Ft [Ht0 Ht1]].
  assert (Hcs : forall c, In c cs -> fin c = true /\ Rabs (B2R c) <= bpow radix2 500).
  { intros c Hc. apply dc_ctrl_ok_R. apply Hg. exact Hc. }
  exists (Nat.pred (length cs)).
  assert (Hlen' : length cs = S (Nat.pred (length cs))) by (subst cs; reflexivity).
  assert (Hn : (Nat.pred (length cs) <= 1000)%nat) by (unfold dc_max_len in *; lia).
  refine (conj Hlen' (conj Hn (conj (eq_sym Hv) _))).
  set (n := Nat.pred (length cs)) in *.
  assert (Hmain : forall M, 0 <= M -> M <= bpow radix2 500 ->
      Forall (fun c => Rabs (B2R c) <= M) cs ->
      fin (dcF (b64_minus dc_one t) t n cs) = true /\
      Rabs (B2R (dcF (b64_minus dc_one t) t n cs)
            - dcR (1 - B2R t) (B2R t) n (map B2R cs))
      <= ((1 + dc_kappa (b64ae_u + b64ae_e0)) ^ n - 1) * M
         + dc_rho * INR n * (1 + dc_kappa (b64ae_u + b64ae_e0)) ^ n).
  { intros M HM0 HM1 HF.
    assert (HF2 : Forall (fun c => fin c = true /\ Rabs (B2R c) <= M) cs).
    { rewrite Forall_forall in HF |- *. intros c Hc. split; [|apply HF; exact Hc].
      apply (proj1 (Hcs c Hc)). }
    destruct dc_consts_R as [H1 _].
    apply (b64_decasteljau_err_fl n cs dc_one t M eq_refl H1 Hlen' HF2 Ft Ht0 Ht1 HM0
             (dc_guard_ok n M Hn HM0 HM1)). }
  assert (Hfin : fin (dcF (b64_minus dc_one t) t n cs) = true).
  { assert (HFall : Forall (fun c => Rabs (B2R c) <= bpow radix2 500) cs)
      by (rewrite Forall_forall; intros c Hc; exact (proj2 (Hcs c Hc))).
    exact (proj1 (Hmain (bpow radix2 500) (Rlt_le _ _ (bpow_gt_0 radix2 500))
                    (Rle_refl _) HFall)). }
  rewrite <- Hv. split; [exact Hfin|].
  intros M HM0 HM1 HF. exact (proj2 (Hmain M HM0 HM1 HF)).
Qed.

Print Assumptions dc_guard_ok.
Print Assumptions dc_eval_certified.
