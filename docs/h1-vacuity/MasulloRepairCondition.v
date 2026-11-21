(* MasulloRepairCondition.v -- what would rescue Masullo's (10.3.1.18)?

   A. M. Masullo, "The Music of the Primes" (draft 2026-11-20), §10.3, p. 451:
   the singular values of the rank-one pieces A_(k,j) satisfy (10.3.1.20)
     sigma_m(A_(k,j)) <= N * C * 2^(N-1) * sum_i |phi^(i)(t_(k,j))|
   with C uniform over all zeros -- which fails at a = 1/2 (upstream
   mccorvie/riemann-masullo#1169; this repo's MarkushevichBoundQEX.v).

   With a zero-dependent constant C_t, nuclearity of A = sum_(k,j) A_(k,j)
   needs   sum_t C_t * |phi_hat(t)|  < infinity.   This file proves the
   summation skeleton of the natural repair condition:

     IF   C_t <= A (1+|t|)^K                  (polynomial growth of C_t)
     AND  |phi_hat(t)| <= B (1+|t|)^-(K+4)    (phi_hat decays faster than any
                                                polynomial: phi in D(C_F))
     AND  #{zeros in dyadic shell j} <= D 4^(j+1)   (crude: N(T) << T^2;
                                                the truth is T log T)
     THEN the partial sums of sum_t C_t |phi_hat(t)| are bounded by
          (16/3) * A * B * D * 2^(K+4)-type constants, uniformly.

   Proved here in abstract dyadic form (Q, no axioms): if shell j has at most
   c_j <= D * 4^(j+1) terms, each <= E * 16^-j, then every partial sum over
   J shells is <= (16/3) * D * E.  (Per-term bound E * 16^-j is what
   C_t |phi_hat(t)| <= A B (1+|t|)^-4 gives on |t| in [2^j, 2^(j+1)).)

   Consequence (reading): since ||psi_t|| >= 1/||eta_t - eta_t'|| and
   ||eta_t - eta_t'|| -> 0 with |t - t'|, a POLYNOMIAL growth bound on C_t is
   essentially a polynomial LOWER bound on gaps between consecutive critical
   zeros (in Masullo's indexing), which is not known unconditionally.  So the
   repair route "make C depend on t" is available exactly when such a gap
   bound is; otherwise a different nuclearity argument is needed.

   Evidence for docs/attacks/2026-11-21-masullo-repair-condition.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import QArith Lqa.
Local Open Scope Q_scope.

Fixpoint qpow (q : Q) (n : nat) : Q :=
  match n with O => 1 | S n' => q * qpow q n' end.

Lemma qpow_pos : forall q n, 0 < q -> 0 < qpow q n.
Proof. intros q n Hq. induction n as [|n IH]; cbn; [lra|]. apply Qmult_lt_0_compat; assumption. Qed.

(* geometric partial sums: sum_{j<J} (1/4)^j <= 4/3 *)
Fixpoint geo (J : nat) : Q := match J with O => 0 | S J' => geo J' + qpow (1 # 4) J' end.

Lemma geo_closed : forall J, geo J + (4 # 3) * qpow (1 # 4) J == 4 # 3.
Proof.
  induction J as [|J IH]; cbn [geo qpow]; [ring|].
  setoid_replace (geo J + qpow (1 # 4) J + (4 # 3) * ((1 # 4) * qpow (1 # 4) J))
    with (geo J + (4 # 3) * qpow (1 # 4) J) by ring.
  exact IH.
Qed.

Lemma geo_bound : forall J, geo J <= 4 # 3.
Proof.
  intros J. pose proof (geo_closed J). pose proof (qpow_pos (1 # 4) J ltac:(lra)). lra.
Qed.

(* 4^(j+1) * 16^-j = 4 * (1/4)^j *)
Lemma shell_identity : forall j, qpow 4 (S j) * qpow (1 # 16) j == 4 * qpow (1 # 4) j.
Proof.
  induction j as [|j IH]; cbn [qpow]; [ring|].
  cbn [qpow] in IH.
  setoid_replace (4 * (4 * qpow 4 j) * ((1 # 16) * qpow (1 # 16) j))
    with ((1 # 4) * (4 * qpow 4 j * qpow (1 # 16) j)) by ring.
  rewrite IH. ring.
Qed.

Section Shells.
Variable D E : Q.
Hypothesis HD : 0 <= D.
Hypothesis HE : 0 <= E.
Variable c : nat -> Q.                 (* number of zeros in shell j *)
Hypothesis c_nonneg : forall j, 0 <= c j.
Hypothesis c_bound : forall j, c j <= D * qpow 4 (S j).
Variable s : nat -> Q.                 (* sum of C_t |phi_hat(t)| over shell j *)
Hypothesis s_nonneg : forall j, 0 <= s j.
Hypothesis s_bound : forall j, s j <= c j * (E * qpow (1 # 16) j).

Fixpoint partial (J : nat) : Q := match J with O => 0 | S J' => partial J' + s J' end.

Lemma shell_le : forall j, s j <= 4 * D * E * qpow (1 # 4) j.
Proof.
  intros j. apply Qle_trans with (c j * (E * qpow (1 # 16) j)); [apply s_bound|].
  assert (H16 : 0 < qpow (1 # 16) j) by (apply qpow_pos; lra).
  apply Qle_trans with (D * qpow 4 (S j) * (E * qpow (1 # 16) j)).
  - apply Qmult_le_compat_r; [apply c_bound | apply Qmult_le_0_compat; lra].
  - setoid_replace (D * qpow 4 (S j) * (E * qpow (1 # 16) j))
      with (D * E * (qpow 4 (S j) * qpow (1 # 16) j)) by ring.
    rewrite shell_identity. lra.
Qed.

Lemma partial_le_geo : forall J, partial J <= 4 * D * E * geo J.
Proof.
  induction J as [|J IH]; cbn [partial geo]; [lra|].
  pose proof (shell_le J). lra.
Qed.

(* the repair skeleton: uniformly bounded partial sums *)
Theorem repair_partial_sums_bounded : forall J, partial J <= (16 # 3) * D * E.
Proof.
  intros J. apply Qle_trans with (4 * D * E * geo J); [apply partial_le_geo|].
  assert (0 <= D * E) by (apply Qmult_le_0_compat; lra).
  pose proof (geo_bound J). nra.
Qed.

End Shells.

Print Assumptions repair_partial_sums_bounded.
