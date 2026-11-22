(* ============================================================================
   NetTopologySuite.Proofs.ExpSeriesClean
   ----------------------------------------------------------------------------
   Facts about Stdlib's exp from its defining series E1 alone: monotonicity,
   1 + x <= exp x, (1 - y) exp y <= 1, exp (k L) = (exp L)^k.  Stdlib's
   exp_increasing / exp_ineq1_le print Classical_Prop.classic; these do not.
   Moved verbatim from the probe lane (docs/h1-vacuity/AlpogeRealsQED.v); the Alpöge audit probes
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
Local Open Scope R_scope.

(* ===================================================================== *)
(* Helpers                                                                *)
(* ===================================================================== *)

(* Stdlib's exp_increasing, exp_ineq1_le, ln and Rpower all depend on
   Classical_Prop.classic (Print Assumptions), which is NOT in the corpus
   allowlist.  The exp facts used below are re-derived from Stdlib's series
   E1 x N -> exp x (E1_cvg), growing_ineq and Rle_cv_lim, which stay within
   the allowlist. *)

Lemma e1_term_nonneg : forall x n, 0 <= x -> 0 <= / INR (fact n) * x ^ n.
Proof. intros x n Hx. apply Rmult_le_pos; [left; apply Rinv_0_lt_compat, INR_fact_lt_0|apply pow_le; exact Hx]. Qed.

Lemma E1_growing : forall x, 0 <= x -> Un_growing (E1 x).
Proof. intros x Hx n. unfold E1. rewrite tech5. pose proof (e1_term_nonneg x (S n) Hx). lra. Qed.

Lemma E1_le_exp : forall x n, 0 <= x -> E1 x n <= exp x.
Proof. intros x n Hx. exact (growing_ineq (E1 x) (exp x) (E1_growing x Hx) (E1_cvg x) n). Qed.

(* 1 + h <= exp h for h >= 0 *)
Lemma exp_ge_1_plus : forall h, 0 <= h -> 1 + h <= exp h.
Proof.
  intros h Hh. pose proof (E1_le_exp h 1 Hh) as H. unfold E1 in H. simpl in H.
  replace (/ 1 * 1 + / 1 * (h * 1)) with (1 + h) in H by field. exact H.
Qed.

Lemma exp_le_mono : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H. replace y with (x + (y - x)) by ring. rewrite exp_plus.
  pose proof (exp_ge_1_plus (y - x) ltac:(lra)). pose proof (exp_pos x). nra.
Qed.

Lemma exp_lt_mono : forall x y, x < y -> exp x < exp y.
Proof.
  intros x y H. replace y with (x + (y - x)) by ring. rewrite exp_plus.
  pose proof (exp_ge_1_plus (y - x) ltac:(lra)). pose proof (exp_pos x). nra.
Qed.

Lemma Un_cv_const : forall c, Un_cv (fun _ => c) c.
Proof. intros c eps He. exists 0%nat. intros n _. unfold R_dist. rewrite Rminus_diag, Rabs_R0. exact He. Qed.

(* (1 - y) exp y <= 1 for 0 <= y: partial-sum invariant
   (1-y) E1 y N + y^(N+1)/N! <= 1, then the limit. *)
Lemma exp_upper : forall y, 0 <= y -> (1 - y) * exp y <= 1.
Proof.
  intros y Hy.
  assert (Hinv : forall N, (1 - y) * E1 y N + y ^ (S N) / INR (fact N) <= 1).
  { induction N as [|N IH].
    - unfold E1. simpl. unfold Rdiv. rewrite ?Rinv_1. lra.
    - unfold E1 in *. rewrite tech5.
      assert (Hf : INR (fact N) <= INR (fact (S N))) by (apply le_INR, fact_le; lia).
      assert (Hf0 : 0 < INR (fact N)) by apply INR_fact_lt_0.
      assert (Hp : 0 <= y ^ (S N)) by (apply pow_le; exact Hy).
      assert (Hdiv : y ^ (S N) / INR (fact (S N)) <= y ^ (S N) / INR (fact N)).
      { unfold Rdiv. apply Rmult_le_compat_l; [exact Hp|]. apply Rinv_le_contravar; lra. }
      replace ((1 - y) * (sum_f_R0 (fun k : nat => / INR (fact k) * y ^ k) N + / INR (fact (S N)) * y ^ S N)
               + y ^ S (S N) / INR (fact (S N)))
        with ((1 - y) * sum_f_R0 (fun k : nat => / INR (fact k) * y ^ k) N + y ^ (S N) / INR (fact (S N)))
        by (simpl pow; field; lra).
      lra. }
  assert (Hle : forall N, (1 - y) * E1 y N <= 1).
  { intro N. pose proof (Hinv N).
    assert (0 <= y ^ (S N) / INR (fact N)).
    { unfold Rdiv. apply Rmult_le_pos; [apply pow_le; exact Hy|left; apply Rinv_0_lt_compat, INR_fact_lt_0]. }
    lra. }
  assert (Hcv : Un_cv (fun N => (1 - y) * E1 y N) ((1 - y) * exp y)).
  { apply (CV_mult (fun _ => 1 - y) (E1 y)); [apply Un_cv_const|apply E1_cvg]. }
  exact (@Rle_cv_lim _ (fun _ => 1) _ 1 Hle Hcv (Un_cv_const 1)).
Qed.

(* Real.add_one_le_exp, for every real x, within the allowlist *)
Lemma add_one_le_exp : forall x, 1 + x <= exp x.
Proof.
  intro x. destruct (Rle_lt_dec 0 x) as [H|H]; [exact (exp_ge_1_plus x H)|].
  destruct (Rle_lt_dec x (-1)) as [H1|H1]; [pose proof (exp_pos x); lra|].
  pose proof (exp_upper (- x) ltac:(lra)) as Hu.
  assert (Hm : exp (- x) * exp x = 1) by (rewrite <- exp_plus; replace (- x + x) with 0 by ring; apply exp_0).
  pose proof (exp_pos x). pose proof (exp_pos (- x)).
  replace (1 - - x) with (1 + x) in Hu by ring.
  assert (Hk : (1 + x) * exp (- x) * exp x <= 1 * exp x) by (apply Rmult_le_compat_r; lra).
  rewrite Rmult_assoc, Hm in Hk. lra.
Qed.

Lemma exp_INR_mult : forall (k : nat) L, exp (INR k * L) = exp L ^ k.
Proof.
  intros k L. induction k as [|k IH].
  - simpl. rewrite Rmult_0_l, exp_0. reflexivity.
  - rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, exp_plus, IH. simpl. ring.
Qed.

Lemma pow_le_mono : forall a b (k : nat), 0 <= a -> a <= b -> a ^ k <= b ^ k.
Proof. intros a b k Ha Hab. apply pow_incr. lra. Qed.

Print Assumptions e1_term_nonneg.
Print Assumptions E1_growing.
Print Assumptions E1_le_exp.
Print Assumptions exp_ge_1_plus.
Print Assumptions exp_le_mono.
Print Assumptions exp_lt_mono.
Print Assumptions Un_cv_const.
Print Assumptions exp_upper.
Print Assumptions add_one_le_exp.
Print Assumptions exp_INR_mult.
Print Assumptions pow_le_mono.
