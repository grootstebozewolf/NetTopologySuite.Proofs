(* ============================================================================
   NetTopologySuite.Proofs.TaggedIntegralApps
   ----------------------------------------------------------------------------
   Applications of TaggedIntegral: Lc is an antiderivative of 1/y, the
   window integral of 1/y and of y^theta y^(-theta-1), and the kernel
   integral  int_0^oo u^k e^(-a u) / k! du = a^(-(k+1)).
   Moved verbatim from the probe lane (docs/h1-vacuity/CleanIntegralQED.v Parts 7-9, from #1047); the Alpöge audit probes
   re-export it.  Allowlist-clean: every Print Assumptions shows at most the
   corpus trio (sig_not_dec, sig_forall_dec, functional_extensionality_dep).

   claimId: none
   No Admitted, no Axiom, no Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
   ============================================================================ *)
From Stdlib Require Import Reals Lra Psatz Lia List Factorial.
From NTS.Proofs Require Import ExpSeriesClean LogRpowClean TaggedIntegral.
Import ListNotations.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Part 7: the clean logarithm is an antiderivative of 1/y                *)
(* ===================================================================== *)

Lemma Lc_mult : forall x y, 0 < x -> 0 < y -> Lc (x * y) = Lc x + Lc y.
Proof.
  intros x y Hx Hy. apply exp_inj. rewrite exp_plus, !exp_Lc; [reflexivity|exact Hy|exact Hx|].
  apply Rmult_lt_0_compat; assumption.
Qed.

(* Lc'(y) = 1/y, from  h/(y+h) <= Lc(y+h) - Lc y <= h/y  (Lc z <= z - 1) *)
Theorem Lc_deriv : forall y, 0 < y -> derivable_pt_lim Lc y (/ y).
Proof.
  intros y Hy e He.
  assert (Hyy : 0 < y * y) by nra.
  set (d := Rmin (y / 2) (e * (y * y) / 2)).
  assert (Hd : 0 < d).
  { unfold d. apply Rmin_pos; [lra|]. apply Rdiv_lt_0_compat; [nra|lra]. }
  exists (mkposreal d Hd). intros h Hh Hhd. simpl in Hhd.
  assert (Hh1 : Rabs h < y / 2) by (eapply Rlt_le_trans; [exact Hhd|apply Rmin_l]).
  assert (Hh2 : Rabs h < e * (y * y) / 2) by (eapply Rlt_le_trans; [exact Hhd|apply Rmin_r]).
  pose proof (abs_lt_elim _ _ Hh1) as [Hh1a Hh1b].
  assert (Hyh : 0 < y + h) by lra.
  assert (Up : Lc (y + h) - Lc y <= h / y).
  { assert (E : Lc (y + h) = Lc y + Lc ((y + h) / y)).
    { rewrite <- Lc_mult by (try apply Rdiv_lt_0_compat; lra). f_equal. field. lra. }
    pose proof (Lc_le_sub1 ((y + h) / y) ltac:(apply Rdiv_lt_0_compat; lra)) as H.
    replace ((y + h) / y - 1) with (h / y) in H by (field; lra). lra. }
  assert (Lo : h / (y + h) <= Lc (y + h) - Lc y).
  { assert (E : Lc y = Lc (y + h) + Lc (y / (y + h))).
    { rewrite <- Lc_mult by (try apply Rdiv_lt_0_compat; lra). f_equal. field. lra. }
    pose proof (Lc_le_sub1 (y / (y + h)) ltac:(apply Rdiv_lt_0_compat; lra)) as H.
    replace (y / (y + h) - 1) with (- (h / (y + h))) in H by (field; lra). lra. }
  set (D := Lc (y + h) - Lc y) in *.
  set (w := D - h / y).
  set (P := y * (y + h)).
  assert (HP : 0 < P) by (unfold P; nra).
  assert (Hw1 : w <= 0) by (unfold w; lra).
  assert (Hw2 : - (h * h) <= w * P).
  { assert (E : (h / (y + h) - h / y) * P = - (h * h)) by (unfold P; field; lra).
    rewrite <- E. apply Rmult_le_compat_r; [lra|unfold w; lra]. }
  assert (HhP : Rabs h < e * P).
  { unfold P. pose proof (Rabs_pos h). nra. }
  replace (D / h - / y) with (w / h) by (unfold w; field; lra).
  unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
  assert (Hah : 0 < Rabs h) by (apply Rabs_pos_lt; exact Hh).
  rewrite (Rabs_left1 w) by exact Hw1.
  (* - w <= h^2 / P and h^2 = |h|^2 < e |h| P *)
  assert (Hsq : h * h = Rabs h * Rabs h) by (rewrite <- Rabs_mult; symmetry; apply Rabs_right; nra).
  apply (Rmult_lt_reg_r (Rabs h)); [exact Hah|].
  rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
  apply (Rmult_lt_reg_r P); [exact HP|]. nra.
Qed.

(* ===================================================================== *)
(* Part 8: the window integral of windowHyp_of_rpow                       *)
(* ===================================================================== *)

Lemma inv_Lip : forall Y B, 1 <= Y -> Lip (fun y => / y) Y B 1.
Proof.
  intros Y B HY x z Hx Hz.
  replace (/ x - / z) with ((z - x) * / (x * z)) by (field; lra).
  assert (Hxz : 1 <= x * z) by nra.
  assert (Hk : 0 < / (x * z)) by (apply Rinv_0_lt_compat; lra).
  assert (Ek : / (x * z) * (x * z) = 1) by (field; lra).
  rewrite Rabs_mult, (Rabs_right (/ (x * z))) by lra. rewrite (Rabs_minus_sym z x).
  pose proof (Rabs_pos (x - z)). nra.
Qed.

Lemma window_le : forall Y delta, 1 <= Y -> 0 <= delta -> Y <= rpc Y (1 + delta).
Proof.
  intros Y delta HY Hd. pose proof (rpc_mono_exp Y 1 (1 + delta) HY ltac:(lra)) as H.
  rewrite rpc_one in H by lra. exact H.
Qed.

(* int_Y^(Y^(1+delta)) dy / y = delta * log Y *)
Theorem window_integral : forall Y delta, 1 <= Y -> 0 <= delta ->
  RInt (fun y => / y) Y (rpc Y (1 + delta)) (delta * Lc Y).
Proof.
  intros Y delta HY Hd.
  replace (delta * Lc Y) with (Lc (rpc Y (1 + delta)) - Lc Y) by (rewrite Lc_rpc; ring).
  apply (tagged_ftc_lip Lc (fun y => / y) Y (rpc Y (1 + delta)) 1 (window_le Y delta HY Hd)).
  - intros x Hx. apply Lc_deriv. lra.
  - apply inv_Lip. exact HY.
Qed.

(* the integrand of windowHyp_of_rpow:  R y * y^(-theta-1)  with  R y = y^theta *)
Theorem window_integral_rpow : forall Y theta delta, 1 <= Y -> 0 <= delta ->
  RInt (fun y => rpc y theta * rpc y (- theta - 1)) Y (rpc Y (1 + delta)) (delta * Lc Y).
Proof.
  intros Y theta delta HY Hd.
  apply (RInt_ext (fun y => / y)); [|apply window_integral; assumption].
  intros y Hy. rewrite <- rpc_add. replace (theta + (- theta - 1)) with (-1) by ring.
  unfold rpc. replace (-1 * Lc y) with (- Lc y) by ring.
  rewrite exp_Ropp, exp_Lc by lra. reflexivity.
Qed.

(* y = e^u maps [Lc Y, (1+delta) Lc Y] onto [Y, Y^(1+delta)] *)
Lemma exp_window_map : forall Y delta u, 1 <= Y ->
  Lc Y <= u <= (1 + delta) * Lc Y -> Y <= exp u <= rpc Y (1 + delta).
Proof.
  intros Y delta u HY [H1 H2]. split.
  - rewrite <- (exp_Lc Y) at 1 by lra. apply exp_le_mono. exact H1.
  - unfold rpc. apply exp_le_mono. exact H2.
Qed.

(* the same value through the change of variables y = e^u:
   int_Y^(Y^(1+delta)) dy/y = int_(Lc Y)^((1+delta) Lc Y) 1 du *)
Theorem window_integral_by_cv : forall Y delta I, 1 <= Y -> 0 <= delta ->
  RInt (fun y => / y) Y (rpc Y (1 + delta)) I -> I = delta * Lc Y.
Proof.
  intros Y delta I HY Hd HI.
  assert (HL : 0 <= Lc Y) by (apply Lc_nonneg; exact HY).
  assert (HJ : RInt (fun u => / exp u * exp u) (Lc Y) ((1 + delta) * Lc Y) (delta * Lc Y)).
  { apply (RInt_ext (fun _ => 1)).
    - intros u _. field. apply Rgt_not_eq, exp_pos.
    - replace (delta * Lc Y) with (1 * ((1 + delta) * Lc Y - Lc Y)) by ring.
      apply RInt_const. nra. }
  apply (RInt_change_var (fun y => / y) Lc exp exp (Lc Y) ((1 + delta) * Lc Y)
           Y (rpc Y (1 + delta)) I (delta * Lc Y)).
  - apply exp_Lc. lra.
  - reflexivity.
  - intros u _. apply derivable_pt_lim_exp.
  - intros u Hu. apply exp_window_map; assumption.
  - intros y Hy. apply Lc_deriv. lra.
  - exact HI.
  - exact HJ.
Qed.

(* the change-of-variables identity of windowHypU_of_windowHyp, for a
   majorant R whose y-integrand has an antiderivative on the window:
   int_Y^(Y^(1+delta)) R y y^(-theta-1) dy
     = int_(Lc Y)^((1+delta) Lc Y) R(e^u) e^(-theta u) du *)
Theorem windowU_change_var : forall (Rm Fm : R -> R) theta Y delta I J,
  1 <= Y ->
  (forall y, Y <= y <= rpc Y (1 + delta) -> derivable_pt_lim Fm y (Rm y * rpc y (- theta - 1))) ->
  RInt (fun y => Rm y * rpc y (- theta - 1)) Y (rpc Y (1 + delta)) I ->
  RInt (fun u => Rm (exp u) * exp (- theta * u)) (Lc Y) ((1 + delta) * Lc Y) J ->
  I = J.
Proof.
  intros Rm Fm theta Y delta I J HY HF HI HJ.
  apply (RInt_change_var (fun y => Rm y * rpc y (- theta - 1)) Fm exp exp (Lc Y) ((1 + delta) * Lc Y)
           Y (rpc Y (1 + delta)) I J).
  - apply exp_Lc. lra.
  - reflexivity.
  - intros u _. apply derivable_pt_lim_exp.
  - intros u Hu. apply exp_window_map; assumption.
  - exact HF.
  - exact HI.
  - apply (RInt_ext (fun u => Rm (exp u) * exp (- theta * u))); [|exact HJ].
    intros u _. unfold rpc. rewrite Lc_exp. rewrite Rmult_assoc, <- exp_plus.
    f_equal. f_equal. ring.
Qed.

(* ===================================================================== *)
(* Part 9: kernel_integral                                                *)
(* ===================================================================== *)

(* P_k x = sum_(j <= k) x^j / j! *)
Definition Pk (k : nat) (x : R) : R := sum_f_R0 (fun j => x ^ j / INR (fact j)) k.

Lemma Pk_S : forall k x, Pk (S k) x = Pk k x + x ^ S k / INR (fact (S k)).
Proof. reflexivity. Qed.

Lemma Pk_O : forall x, Pk 0 x = 1.
Proof. intro x. unfold Pk. simpl. field. Qed.

Lemma Pk_at0 : forall k, Pk k 0 = 1.
Proof.
  induction k as [|k IH]; [apply Pk_O|]. rewrite Pk_S, IH. simpl. unfold Rdiv. ring.
Qed.

Lemma fact_ge1 : forall n, 1 <= INR (fact n).
Proof.
  intro n. pose proof (lt_O_fact n) as H. apply le_INR in H. simpl in H. exact H.
Qed.

Lemma div_fact_le : forall z n, 0 <= z -> z / INR (fact n) <= z.
Proof.
  intros z n Hz. pose proof (fact_ge1 n) as H1.
  assert (Hq : 0 < / INR (fact n)) by (apply Rinv_0_lt_compat; lra).
  assert (Eq : / INR (fact n) * INR (fact n) = 1) by (field; lra).
  unfold Rdiv. nra.
Qed.

Lemma Pk_nonneg : forall k x, 0 <= x -> 0 <= Pk k x.
Proof.
  induction k as [|k IH]; intros x Hx; [rewrite Pk_O; lra|].
  rewrite Pk_S. pose proof (IH x Hx). pose proof (fact_ge1 (S k)).
  assert (0 <= x ^ S k / INR (fact (S k)))
    by (apply Rmult_le_pos; [apply pow_le; exact Hx|left; apply Rinv_0_lt_compat; lra]).
  lra.
Qed.

(* P_k' = P_k - x^k / k! *)
Lemma Pk_deriv : forall k x, derivable_pt_lim (Pk k) x (Pk k x - x ^ k / INR (fact k)).
Proof.
  induction k as [|k IH]; intro x.
  - apply (dpl_ext (fun _ => 1) _ _ 0).
    + intro y. symmetry. apply Pk_O.
    + rewrite Pk_O. simpl. field.
    + apply derivable_pt_lim_const.
  - apply (dpl_ext (fun y => Pk k y + / INR (fact (S k)) * y ^ S k) _ _
             ((Pk k x - x ^ k / INR (fact k)) + / INR (fact (S k)) * (INR (S k) * x ^ pred (S k)))).
    + intro y. rewrite Pk_S. unfold Rdiv. ring.
    + rewrite Pk_S. cbn [pred]. rewrite fact_simpl, mult_INR.
      pose proof (fact_ge1 k). assert (INR (S k) <> 0) by (apply not_0_INR; lia).
      field. split; lra.
    + apply dpl_plus; [apply IH|]. apply dpl_scal. apply derivable_pt_lim_pow.
Qed.

(* e^x >= P_k x on [0, oo) *)
Lemma exp_ge_Pk : forall k x, 0 <= x -> Pk k x <= exp x.
Proof.
  induction k as [|k IH]; intros x Hx.
  - assert (H : exp 0 - Pk 0 0 <= exp x - Pk 0 x).
    { apply (deriv_nonneg_incr_mvt (fun z => exp z - Pk 0 z)
               (fun z => exp z - (Pk 0 z - z ^ 0 / INR (fact 0))) 0 x Hx).
      - intros z _. apply dpl_minus; [apply derivable_pt_lim_exp|apply Pk_deriv].
      - intros z _. rewrite Pk_O. simpl. pose proof (exp_pos z).
        replace (1 - 1 / 1) with 0 by field. lra. }
    rewrite exp_0, Pk_at0 in H. lra.
  - assert (H : exp 0 - Pk (S k) 0 <= exp x - Pk (S k) x).
    { apply (deriv_nonneg_incr_mvt (fun z => exp z - Pk (S k) z)
               (fun z => exp z - (Pk (S k) z - z ^ S k / INR (fact (S k)))) 0 x Hx).
      - intros z _. apply dpl_minus; [apply derivable_pt_lim_exp|apply Pk_deriv].
      - intros z Hz. rewrite Pk_S. pose proof (IH z (proj1 Hz)). lra. }
    rewrite exp_0, Pk_at0 in H. lra.
Qed.

Lemma Pk_le_poly : forall k x, 1 <= x -> Pk k x <= INR (S k) * x ^ k.
Proof.
  induction k as [|k IH]; intros x Hx.
  - rewrite Pk_O. simpl. lra.
  - rewrite Pk_S. pose proof (IH x Hx).
    assert (Hk : 1 <= x ^ k) by (apply pow_R1_Rle; exact Hx).
    assert (HSk : x ^ S k = x * x ^ k) by reflexivity.
    pose proof (div_fact_le (x ^ S k) (S k) ltac:(rewrite HSk; nra)).
    rewrite (S_INR (S k)). rewrite HSk in *. pose proof (pos_INR (S k)).
    assert (INR (S k) * x ^ k <= INR (S k) * (x * x ^ k)) by (apply Rmult_le_compat_l; nra).
    lra.
Qed.

(* e^(-x) P_k x <= (k+1) (k+1)! / x  for x >= 1 *)
Lemma exp_Pk_decay : forall k x, 1 <= x ->
  exp (- x) * Pk k x <= INR (S k) * INR (fact (S k)) / x.
Proof.
  intros k x Hx.
  set (C := INR (S k) * INR (fact (S k))).
  assert (HE : 0 < exp x) by apply exp_pos.
  assert (HF : 1 <= INR (fact (S k))) by apply fact_ge1.
  assert (HS : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (Hpow : x ^ S k <= INR (fact (S k)) * exp x).
  { pose proof (exp_ge_Pk (S k) x ltac:(lra)) as H. rewrite Pk_S in H.
    pose proof (Pk_nonneg k x ltac:(lra)).
    assert (E : x ^ S k = INR (fact (S k)) * (x ^ S k / INR (fact (S k)))) by (field; lra).
    rewrite E. apply Rmult_le_compat_l; lra. }
  assert (Key : Pk k x * x <= C * exp x).
  { pose proof (Pk_le_poly k x Hx).
    assert (E : x ^ S k = x * x ^ k) by reflexivity.
    assert (0 <= x ^ k) by (apply pow_le; lra).
    unfold C. nra. }
  replace (exp (- x) * Pk k x) with ((Pk k x * x) * (/ exp x * / x))
    by (rewrite exp_Ropp; field; split; lra).
  replace (C / x) with ((C * exp x) * (/ exp x * / x)) by (field; split; lra).
  apply Rmult_le_compat_r; [|exact Key].
  apply Rmult_le_pos; left; apply Rinv_0_lt_compat; lra.
Qed.

(* the kernel and its antiderivative *)
Definition gk (k : nat) (a u : R) : R := u ^ k * exp (- (a * u)) / INR (fact k).
Definition Gk (k : nat) (a u : R) : R := - / a ^ S k * (exp (- (a * u)) * Pk k (a * u)).

Lemma Gk_deriv : forall k a u, 0 < a -> derivable_pt_lim (Gk k a) u (gk k a u).
Proof.
  intros k a u Ha.
  assert (HE : derivable_pt_lim (fun v => exp (- (a * v))) u (exp (- (a * u)) * - a)).
  { apply (dpl_comp' (fun v => - (a * v)) exp u (- a) (exp (- (a * u)))).
    - apply dpl_opp. apply dpl_lin.
    - apply derivable_pt_lim_exp. }
  assert (HQ : derivable_pt_lim (fun v => Pk k (a * v)) u
                 ((Pk k (a * u) - (a * u) ^ k / INR (fact k)) * a)).
  { apply (dpl_comp' (fun v => a * v) (Pk k) u a). apply dpl_lin. apply Pk_deriv. }
  pose proof (dpl_scal (- / a ^ S k) _ u _ (dpl_mult _ _ u _ _ HE HQ)) as H.
  refine (dpl_ext _ _ u _ _ _ _ H); [intro y; reflexivity|].
  cbv beta. unfold gk. rewrite Rpow_mult_distr. replace (a ^ S k) with (a * a ^ k) by reflexivity.
  pose proof (fact_ge1 k). assert (a ^ k <> 0) by (apply pow_nonzero; lra).
  field. repeat split; lra.
Qed.

Lemma Gk_0 : forall k a, Gk k a 0 = - / a ^ S k.
Proof. intros k a. unfold Gk. rewrite Rmult_0_r, Ropp_0, exp_0, Pk_at0. ring. Qed.

(* the kernel has a bounded derivative on [0, T] *)
Lemma gk_deriv : forall k a u, derivable_pt_lim (gk k a) u
  ((INR k * u ^ pred k - a * u ^ k) * exp (- (a * u)) / INR (fact k)).
Proof.
  intros k a u.
  assert (HE : derivable_pt_lim (fun v => exp (- (a * v))) u (exp (- (a * u)) * - a)).
  { apply (dpl_comp' (fun v => - (a * v)) exp u (- a) (exp (- (a * u)))).
    - apply dpl_opp. apply dpl_lin.
    - apply derivable_pt_lim_exp. }
  pose proof (dpl_scal (/ INR (fact k)) _ u _ (dpl_mult _ _ u _ _ (derivable_pt_lim_pow u k) HE)) as H.
  pose proof (fact_ge1 k).
  refine (dpl_ext _ _ u _ _ _ _ H); [intro y; cbv beta; unfold gk; field; lra|].
  field. lra.
Qed.

Lemma gk_deriv_bound : forall k a T u, 0 < a -> 0 <= u <= T ->
  Rabs ((INR k * u ^ pred k - a * u ^ k) * exp (- (a * u)) / INR (fact k))
    <= INR k * T ^ pred k + a * T ^ k.
Proof.
  intros k a T u Ha Hu.
  pose proof (fact_ge1 k) as HK.
  assert (HA : 0 <= INR k * u ^ pred k <= INR k * T ^ pred k).
  { pose proof (pos_INR k). split; [apply Rmult_le_pos; [lra|apply pow_le; lra]|].
    apply Rmult_le_compat_l; [lra|apply pow_incr; lra]. }
  assert (HB : 0 <= a * u ^ k <= a * T ^ k).
  { split; [apply Rmult_le_pos; [lra|apply pow_le; lra]|].
    apply Rmult_le_compat_l; [lra|apply pow_incr; lra]. }
  assert (HE : 0 < exp (- (a * u)) <= 1).
  { split; [apply exp_pos|]. rewrite <- exp_0. apply exp_le_mono. nra. }
  set (X := exp (- (a * u)) / INR (fact k)).
  assert (HX : 0 < X <= 1).
  { unfold X. split; [apply Rdiv_lt_0_compat; lra|].
    apply (Rmult_le_reg_r (INR (fact k))); [lra|]. field_simplify; lra. }
  replace ((INR k * u ^ pred k - a * u ^ k) * exp (- (a * u)) / INR (fact k))
    with ((INR k * u ^ pred k - a * u ^ k) * X) by (unfold X, Rdiv; ring).
  apply abs_le_intro; nra.
Qed.

Lemma kernel_RInt : forall k a T, 0 < a -> 0 <= T ->
  RInt (gk k a) 0 T (Gk k a T - Gk k a 0).
Proof.
  intros k a T Ha HT.
  apply (tagged_ftc_c1 (Gk k a) (gk k a)
           (fun u => (INR k * u ^ pred k - a * u ^ k) * exp (- (a * u)) / INR (fact k))
           0 T (INR k * T ^ pred k + a * T ^ k) HT).
  - intros x _. apply Gk_deriv. exact Ha.
  - intros x _. apply gk_deriv.
  - intros x Hx. apply gk_deriv_bound; assumption.
Qed.

(* kernel_integral (LandauTheorems/kernelIntegral):
     int_0^oo u^k e^(-a u) / k! du = a^(-(k+1))   for a > 0 *)
Theorem kernel_integral : forall k a, 0 < a ->
  RIntInf (fun u => u ^ k * exp (- (a * u)) / INR (fact k)) 0 (/ a ^ S k).
Proof.
  intros k a Ha.
  assert (Hc : 0 < / a ^ S k) by (apply Rinv_0_lt_compat, pow_lt; exact Ha).
  replace (/ a ^ S k) with (0 - Gk k a 0) by (rewrite Gk_0; ring).
  apply (RIntInf_of_antideriv _ (Gk k a) 0 0).
  - intros T HT. exact (kernel_RInt k a T Ha HT).
  - intros e He.
    set (c := / a ^ S k) in *. set (C := INR (S k) * INR (fact (S k))).
    assert (HC : 0 < C).
    { unfold C. apply Rmult_lt_0_compat; [apply lt_0_INR; lia|pose proof (fact_ge1 (S k)); lra]. }
    assert (Hce : 0 <= c * C / e) by (apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; lra]).
    exists ((c * C / e + 1) / a). split; [apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra]|].
    intros T HT.
    assert (Hx : c * C / e + 1 <= a * T).
    { apply (Rmult_le_compat_l a) in HT; [|lra].
      replace (a * ((c * C / e + 1) / a)) with (c * C / e + 1) in HT by (field; lra). exact HT. }
    assert (Hx1 : 1 <= a * T) by lra.
    pose proof (exp_Pk_decay k (a * T) Hx1) as Hdec. fold C in Hdec.
    pose proof (Pk_nonneg k (a * T) ltac:(lra)) as HP. pose proof (exp_pos (- (a * T))) as HEp.
    unfold Gk. fold c. rewrite Rminus_0_r.
    rewrite Rabs_left1 by (assert (0 <= exp (- (a * T)) * Pk k (a * T)) by nra; nra).
    assert (HcC : c * C / (a * T) < e).
    { apply (Rmult_lt_reg_r (a * T)); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
      replace (c * C) with (c * C / e * e) by (field; lra). nra. }
    assert (Hb : c * (exp (- (a * T)) * Pk k (a * T)) <= c * (C / (a * T)))
      by (apply Rmult_le_compat_l; lra).
    unfold Rdiv in HcC, Hb. nra.
Qed.


Print Assumptions Lc_deriv.
Print Assumptions window_integral.
Print Assumptions window_integral_rpow.
Print Assumptions window_integral_by_cv.
Print Assumptions windowU_change_var.
Print Assumptions exp_ge_Pk.
Print Assumptions kernel_integral.
