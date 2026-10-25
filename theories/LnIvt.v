(* ============================================================================
   NetTopologySuite.Proofs.LnIvt
   ----------------------------------------------------------------------------
   3-axiom natural logarithm  ln3 : R -> R , the inverse of Stdlib exp on
   (0, +oo), built the way AtanIvt.atan3 is: an IVT root, made canonical by
   a uniqueness lemma.

     ln3 y := IVT root of  exp t - y  on  [-(/y), y]   for 0 < y
     ln3 y := 0                                         for y <= 0

   Why not Stdlib ln.  Stdlib ln_exp, exp_ln and derivable_pt_lim_ln print
   Classical_Prop.classic, and so do exp_increasing, exp_lt_inv, exp_inv
   and exp_ineq1 (all through MVT / positive_derivative).  From the exp
   and analysis side this file only uses exp_pos, exp_plus, exp_0,
   derivable_pt_lim_exp, derivable_exp, derivable_continuous(_pt), the exp
   series (exist_exp, sum_incr), IVT, Rlt_le_dec, Rtotal_order, and
   Ranalysis5 continuity_pt_recip_interv / derivable_pt_lim_recip_interv,
   all of which are 3-axiom (Print Assumptions below).

   Lemmas:
     exp_one_plus_lt_pos   1 + x < exp x for 0 < x (series partial sum)
     exp_increasing3       x < y -> exp x < exp y
     exp_le3, exp_lt_inv3, exp_inj3
     exp_ln3               0 < y -> exp (ln3 y) = y
     ln3_exp               ln3 (exp x) = x
     ln3_unique            exp a = y -> a = ln3 y
     ln3_nonpos            y <= 0 -> ln3 y = 0  (the total default)
     ln3_1, ln3_mult, ln3_inv
     ln3_increasing, ln3_le, ln3_lt_inv
     continuity_pt_ln3     0 < x -> continuity_pt ln3 x
     derivable_pt_lim_ln3  0 < x -> derivable_pt_lim ln3 x (/ x)

   Scope.  Exact reals only.  Not claimed: ln3 = Stdlib ln (that bridge
   would print classic), any float or libm log, a real power.  A power
   x^a := exp (a * ln3 x) is the next step for Snyder (7-9); not here.
   No Q twin: ln3 is transcendental.

   topic: foundations
   claimId: ln3-ivt (ticket #972)
   witness: exp_ln3
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis5.
From Stdlib Require Import Arith.Factorial.
Local Open Scope R_scope.

(* ---------- exp: 3-axiom lower bound and monotonicity ---------- *)

Lemma exp_one_plus_lt_pos (x : R) : 0 < x -> 1 + x < exp x.
Proof.
  intros Hx. set (An := fun N : nat => / INR (fact N) * x ^ N).
  assert (Hcv : Un_cv (fun n : nat => sum_f_R0 An n) (exp x)).
  { unfold exp, projT1. case (exist_exp x). intros l Hl. exact Hl. }
  assert (Hle : sum_f_R0 An 2 <= exp x).
  { apply sum_incr; [exact Hcv|]. intro n. unfold An. left.
    apply Rmult_lt_0_compat; [apply Rinv_0_lt_compat, INR_fact_lt_0 | apply pow_lt, Hx]. }
  cbn in Hle. unfold An in Hle. cbn in Hle.
  assert (0 < x * x) by nra. lra.
Qed.

Lemma exp_increasing3 (x y : R) : x < y -> exp x < exp y.
Proof.
  intros Hxy.
  replace y with (x + (y - x)) by ring. rewrite exp_plus.
  pose proof (exp_pos x). pose proof (exp_one_plus_lt_pos (y - x) ltac:(lra)).
  nra.
Qed.

Lemma exp_le3 (x y : R) : x <= y -> exp x <= exp y.
Proof.
  intros [H|H]; [left; apply exp_increasing3, H | subst; right; reflexivity].
Qed.

Lemma exp_lt_inv3 (x y : R) : exp x < exp y -> x < y.
Proof.
  intros H. destruct (Rlt_le_dec x y) as [Hl|Hg]; [exact Hl|].
  pose proof (exp_le3 y x Hg). lra.
Qed.

Lemma exp_inj3 (x y : R) : exp x = exp y -> x = y.
Proof.
  intros H. destruct (Rtotal_order x y) as [Hl|[He|Hg]]; [|exact He|].
  - pose proof (exp_increasing3 x y Hl). lra.
  - pose proof (exp_increasing3 y x Hg). lra.
Qed.

(* ---------- ln3 : IVT root of  exp t - y  on [-(/y), y] ---------- *)

Definition ln3_g (y t : R) : R := exp t - y.

Lemma ln3_g_cont (y : R) : continuity (ln3_g y).
Proof.
  unfold ln3_g. apply continuity_minus;
    [apply derivable_continuous, derivable_exp | apply continuity_const; intros ? ?; reflexivity].
Qed.

Lemma ln3_g_lo (y : R) : 0 < y -> ln3_g y (- / y) < 0.
Proof.
  intros Hy. unfold ln3_g.
  assert (Hi : 0 < / y) by (apply Rinv_0_lt_compat, Hy).
  pose proof (exp_one_plus_lt_pos (/ y) Hi) as He.
  pose proof (exp_pos (/ y)) as Hp.
  assert (E : exp (- / y) * exp (/ y) = 1)
    by (rewrite <- exp_plus; replace (- / y + / y) with 0 by ring; apply exp_0).
  assert (Hyi : y * / y = 1) by (field; lra).
  (* exp(-/y) * (1 + /y) < 1, and y * (1 + /y) = y + 1 > 1 *)
  pose proof (exp_pos (- / y)).
  assert (exp (- / y) * (1 + / y) < 1) by nra.
  nra.
Qed.

Lemma ln3_g_hi (y : R) : 0 < y -> 0 < ln3_g y y.
Proof. intros Hy. unfold ln3_g. pose proof (exp_one_plus_lt_pos y Hy). lra. Qed.

Local Lemma ln3_bracket_lt (y : R) : 0 < y -> - / y < y.
Proof. intros Hy. assert (0 < / y) by (apply Rinv_0_lt_compat, Hy). lra. Qed.

Definition ln3_pos (y : R) (Hy : 0 < y) : R :=
  proj1_sig (IVT (ln3_g y) (- / y) y (ln3_g_cont y) (ln3_bracket_lt y Hy)
                 (ln3_g_lo y Hy) (ln3_g_hi y Hy)).

Definition ln3 (y : R) : R :=
  match Rlt_le_dec 0 y with
  | left Hy => ln3_pos y Hy
  | right _ => 0
  end.

Lemma exp_ln3 (y : R) : 0 < y -> exp (ln3 y) = y.
Proof.
  intros Hy. unfold ln3. destruct (Rlt_le_dec 0 y) as [H|H]; [|exfalso; lra].
  unfold ln3_pos. destruct (IVT _ _ _ _ _ _ _) as [z Hz]; cbn. destruct Hz as [_ Hz].
  unfold ln3_g in Hz. lra.
Qed.

Lemma ln3_nonpos (y : R) : y <= 0 -> ln3 y = 0.
Proof.
  intros Hy. unfold ln3. destruct (Rlt_le_dec 0 y) as [H|H]; [exfalso; lra | reflexivity].
Qed.

Lemma ln3_unique (y a : R) : exp a = y -> a = ln3 y.
Proof.
  intros Ha. apply exp_inj3. rewrite exp_ln3; [exact Ha|]. rewrite <- Ha. apply exp_pos.
Qed.

Lemma ln3_exp (x : R) : ln3 (exp x) = x.
Proof. symmetry. apply ln3_unique. reflexivity. Qed.

Lemma ln3_1 : ln3 1 = 0.
Proof. symmetry. apply ln3_unique. apply exp_0. Qed.

Lemma ln3_mult (x y : R) : 0 < x -> 0 < y -> ln3 (x * y) = ln3 x + ln3 y.
Proof.
  intros Hx Hy. symmetry. apply ln3_unique.
  rewrite exp_plus, exp_ln3, exp_ln3; [reflexivity | exact Hy | exact Hx].
Qed.

Lemma ln3_inv (x : R) : 0 < x -> ln3 (/ x) = - ln3 x.
Proof.
  intros Hx. symmetry. apply ln3_unique.
  apply (Rmult_eq_reg_l (exp (ln3 x))); [|apply Rgt_not_eq, exp_pos].
  rewrite <- exp_plus. replace (ln3 x + - ln3 x) with 0 by ring.
  rewrite exp_0, exp_ln3 by exact Hx. field. lra.
Qed.

Lemma ln3_increasing (x y : R) : 0 < x -> x < y -> ln3 x < ln3 y.
Proof.
  intros Hx Hxy. apply exp_lt_inv3. rewrite !exp_ln3; lra.
Qed.

Lemma ln3_le (x y : R) : 0 < x -> x <= y -> ln3 x <= ln3 y.
Proof.
  intros Hx [H|H]; [left; apply ln3_increasing; assumption | subst; right; reflexivity].
Qed.

Lemma ln3_lt_inv (x y : R) : 0 < x -> 0 < y -> ln3 x < ln3 y -> x < y.
Proof.
  intros Hx Hy H. rewrite <- (exp_ln3 x Hx), <- (exp_ln3 y Hy).
  apply exp_increasing3, H.
Qed.

(* ---------- continuity and derivative 1/x (Ranalysis5 inverse kit) ---------- *)

Lemma continuity_pt_ln3 (x : R) : 0 < x -> continuity_pt ln3 x.
Proof.
  intros Hx.
  assert (Hlo : 0 < x / 2) by lra.
  apply (continuity_pt_recip_interv exp ln3 (ln3 (x / 2)) (ln3 (2 * x))).
  - apply ln3_increasing; lra.
  - intros a b _ Hab _. apply exp_increasing3, Hab.
  - intros z Hz _. rewrite exp_ln3 in Hz by exact Hlo.
    unfold comp, id. apply exp_ln3. lra.
  - intros z Hz1 Hz2. rewrite exp_ln3 in Hz1 by exact Hlo.
    rewrite exp_ln3 in Hz2 by lra.
    split; apply ln3_le; lra.
  - intros a _. apply derivable_continuous_pt, derivable_exp.
  - rewrite !exp_ln3 by lra. lra.
Qed.

Lemma derivable_pt_lim_ln3 (x : R) : 0 < x -> derivable_pt_lim ln3 x (/ x).
Proof.
  intros Hx.
  assert (Prf : forall a, ln3 (x / 2) <= a <= ln3 (2 * x) -> derivable_pt exp a)
    by (intros a _; apply derivable_exp).
  assert (Hin : ln3 (x / 2) <= ln3 x <= ln3 (2 * x)) by (split; apply ln3_le; lra).
  pose proof (derivable_pt_lim_recip_interv exp ln3 (x / 2) (2 * x) x Prf
                (continuity_pt_ln3 x Hx) ltac:(lra) ltac:(lra) Hin) as D.
  assert (Hd : derive_pt exp (ln3 x) (Prf (ln3 x) Hin) = exp (ln3 x))
    by (apply derive_pt_eq_0, derivable_pt_lim_exp).
  rewrite exp_ln3 in Hd by exact Hx.
  rewrite Hd in D. replace (/ x) with (1 / x) by (field; lra).
  apply D.
  - intros z Hz. unfold comp, id. apply exp_ln3. lra.
  - lra.
Qed.

Print Assumptions exp_one_plus_lt_pos.
Print Assumptions exp_increasing3.
Print Assumptions exp_le3.
Print Assumptions exp_lt_inv3.
Print Assumptions exp_inj3.
Print Assumptions exp_ln3.
Print Assumptions ln3_exp.
Print Assumptions ln3_unique.
Print Assumptions ln3_1.
Print Assumptions ln3_mult.
Print Assumptions ln3_inv.
Print Assumptions ln3_increasing.
Print Assumptions ln3_le.
Print Assumptions ln3_lt_inv.
Print Assumptions ln3_nonpos.
Print Assumptions continuity_pt_ln3.
Print Assumptions derivable_pt_lim_ln3.
