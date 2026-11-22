(* ============================================================================
   NetTopologySuite.Proofs.LogRpowClean
   ----------------------------------------------------------------------------
   An allowlist-clean logarithm Lc (the inverse of exp, by the intermediate
   value theorem) and power rpc x a = exp (a Lc x), with their laws.
   Stdlib's ln and Rpower print Classical_Prop.classic; these do not.
   Moved verbatim from the probe lane (docs/h1-vacuity/AlpogeRealsQED2.v); the Alpöge audit probes
   re-export it.  Allowlist-clean: every Print Assumptions shows at most the
   corpus trio (sig_not_dec, sig_forall_dec, functional_extensionality_dep).

   claimId: none
   No Admitted, no Axiom, no Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
   ============================================================================ *)
From Stdlib Require Import Reals Lra Psatz List Factorial.
From NTS.Proofs Require Import ExpSeriesClean.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Part 0: an allowlist-clean logarithm and power                         *)
(* ===================================================================== *)

Lemma exp_inj : forall a b, exp a = exp b -> a = b.
Proof.
  intros a b H. destruct (Rtotal_order a b) as [Hl|[He|Hg]]; [|exact He|].
  - pose proof (exp_lt_mono a b Hl). lra.
  - pose proof (exp_lt_mono b a Hg). lra.
Qed.

Lemma exp_lt_inv' : forall a b, exp a < exp b -> a < b.
Proof.
  intros a b H. destruct (Rlt_le_dec a b) as [Hl|Hge]; [exact Hl|].
  pose proof (exp_le_mono b a Hge). lra.
Qed.

Lemma exp_le_inv' : forall a b, exp a <= exp b -> a <= b.
Proof.
  intros a b H. destruct (Rle_lt_dec a b) as [Hl|Hg]; [exact Hl|].
  pose proof (exp_lt_mono b a Hg). lra.
Qed.

Lemma exp_sub_const_cont : forall y, continuity (fun x => exp x - y).
Proof. intro y. apply continuity_minus; [exact (derivable_continuous exp derivable_exp)|apply continuity_const; intros a b; reflexivity]. Qed.

Lemma neg_inv_lt_self : forall y, 0 < y -> - / y < y.
Proof. intros y Hy. pose proof (Rinv_0_lt_compat y Hy). lra. Qed.

Lemma exp_neg_inv_sub_neg : forall y, 0 < y -> exp (- / y) - y < 0.
Proof.
  intros y Hy. rewrite exp_Ropp.
  assert (Hi : 0 < / y) by (apply Rinv_0_lt_compat; exact Hy).
  pose proof (exp_ge_1_plus (/ y) ltac:(lra)) as H1.
  assert (H2 : / y < exp (/ y)) by lra.
  assert (H3 : / exp (/ y) < / / y) by (apply Rinv_lt_contravar; [apply Rmult_lt_0_compat; [exact Hi|apply exp_pos]|exact H2]).
  rewrite Rinv_inv in H3. lra.
Qed.

Lemma exp_sub_self_pos : forall y, 0 < y -> 0 < exp y - y.
Proof. intros y Hy. pose proof (exp_ge_1_plus y ltac:(lra)). lra. Qed.

Definition Lc_pos (y : R) (H : 0 < y) : R :=
  proj1_sig (IVT (fun x => exp x - y) (- / y) y (exp_sub_const_cont y) (neg_inv_lt_self y H) (exp_neg_inv_sub_neg y H) (exp_sub_self_pos y H)).

Lemma exp_Lc_pos : forall y (H : 0 < y), exp (Lc_pos y H) = y.
Proof.
  intros y H. unfold Lc_pos.
  destruct (proj2_sig (IVT (fun x => exp x - y) (- / y) y (exp_sub_const_cont y) (neg_inv_lt_self y H) (exp_neg_inv_sub_neg y H) (exp_sub_self_pos y H))) as [_ Hz].
  cbv beta in Hz. lra.
Qed.

Definition Lc (y : R) : R := match Rlt_dec 0 y with left H => Lc_pos y H | right _ => 0 end.

Lemma exp_Lc : forall y, 0 < y -> exp (Lc y) = y.
Proof. intros y Hy. unfold Lc. destruct (Rlt_dec 0 y) as [H|H]; [apply exp_Lc_pos|contradiction]. Qed.

Lemma Lc_exp : forall x, Lc (exp x) = x.
Proof. intro x. apply exp_inj. apply exp_Lc. apply exp_pos. Qed.

Lemma Lc_1 : Lc 1 = 0.
Proof. rewrite <- exp_0. apply Lc_exp. Qed.

Lemma Lc_le_mono : forall x y, 0 < x -> x <= y -> Lc x <= Lc y.
Proof. intros x y Hx Hxy. apply exp_le_inv'. rewrite !exp_Lc by lra. exact Hxy. Qed.

Lemma Lc_nonneg : forall x, 1 <= x -> 0 <= Lc x.
Proof. intros x Hx. rewrite <- Lc_1. apply Lc_le_mono; lra. Qed.

Lemma Lc_le_sub1 : forall z, 0 < z -> Lc z <= z - 1.
Proof. intros z Hz. pose proof (add_one_le_exp (Lc z)). rewrite exp_Lc in H by exact Hz. lra. Qed.

Definition rpc (x a : R) : R := exp (a * Lc x).

Lemma rpc_pos : forall x a, 0 < rpc x a.
Proof. intros. apply exp_pos. Qed.

Lemma rpc_add : forall x a b, rpc x (a + b) = rpc x a * rpc x b.
Proof. intros. unfold rpc. rewrite <- exp_plus. f_equal. ring. Qed.

Lemma rpc_one : forall x, 0 < x -> rpc x 1 = x.
Proof. intros x Hx. unfold rpc. rewrite Rmult_1_l. apply exp_Lc. exact Hx. Qed.

Lemma Lc_rpc : forall x a, Lc (rpc x a) = a * Lc x.
Proof. intros. unfold rpc. apply Lc_exp. Qed.

Lemma rpc_mult : forall x a b, rpc (rpc x a) b = rpc x (a * b).
Proof. intros. unfold rpc at 1. rewrite Lc_rpc. unfold rpc. f_equal. ring. Qed.

Lemma rpc_mono_exp : forall x a b, 1 <= x -> a <= b -> rpc x a <= rpc x b.
Proof. intros x a b Hx Hab. unfold rpc. apply exp_le_mono. pose proof (Lc_nonneg x Hx). nra. Qed.

Lemma rpc_mono_base : forall a b c, 0 <= c -> 0 < a -> a <= b -> rpc a c <= rpc b c.
Proof. intros a b c Hc Ha Hab. unfold rpc. apply exp_le_mono. pose proof (Lc_le_mono a b Ha Hab). nra. Qed.

(* Real.log_le_rpow_div *)
Lemma Lc_le_rpc_div : forall y t, 0 < y -> 0 < t -> Lc y <= rpc y t / t.
Proof.
  intros y t Hy Ht. pose proof (Lc_le_sub1 (rpc y t) (rpc_pos y t)) as H. rewrite Lc_rpc in H.
  apply (Rmult_le_reg_r t); [exact Ht|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra.
Qed.

Print Assumptions exp_inj.
Print Assumptions exp_lt_inv'.
Print Assumptions exp_le_inv'.
Print Assumptions exp_sub_const_cont.
Print Assumptions neg_inv_lt_self.
Print Assumptions exp_neg_inv_sub_neg.
Print Assumptions exp_sub_self_pos.
Print Assumptions exp_Lc_pos.
Print Assumptions exp_Lc.
Print Assumptions Lc_exp.
Print Assumptions Lc_1.
Print Assumptions Lc_le_mono.
Print Assumptions Lc_nonneg.
Print Assumptions Lc_le_sub1.
Print Assumptions rpc_pos.
Print Assumptions rpc_add.
Print Assumptions rpc_one.
Print Assumptions Lc_rpc.
Print Assumptions rpc_mult.
Print Assumptions rpc_mono_exp.
Print Assumptions rpc_mono_base.
Print Assumptions Lc_le_rpc_div.
