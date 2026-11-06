(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_BezierStability
   ----------------------------------------------------------------------------
   Real-valued side of the binary64 curve-evaluation error bounds, and the
   Horner-vs-de-Casteljau comparison.

   §1  Correctness over R: the exact de Casteljau value `dcR` (the reference
       of B64_DeCasteljau.b64_decasteljau_err) IS the Bernstein-basis sum
       sum_i b_i B_i^n(t), with `bern` the corpus basis of BernsteinBasis.v.

   §2  The comparison family p_n(t) = (1 - 2t)^n.
         Bernstein coefficients  b_j = (-1)^j          (max |b_j| = 1),
         power coefficients      a_i = C(n,i) (-2)^i   (sum_i |a_i| = 3^n).
       Both evaluators target the same real value (`alt_dcR`,
       `horner_binomial`).  The proved bounds then differ by the factor 3^n:
         de Casteljau  main term  gamma_n(kappa_0) * 1     <= 6 n u
         Horner        main term  gamma_{2n} * 3^n        >= 3^n * 2 n u
       (`bezier_vs_horner_bound`: Horner/dC >= 3^n / 3).

   HONESTY NOTE.  This compares the two PROVED UPPER BOUNDS, not the true
   errors of the two algorithms.  It shows the Horner bound loses the
   cancellation-free property that the de Casteljau bound keeps; it does not
   prove Horner is actually that inaccurate.  Measured errors are recorded in
   docs/b64-curve-eval-error-bounds-2026-11.md.

   claimId: s1-b64-bezier-stability.  witness: bezier_vs_horner_bound.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia Psatz ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import BernsteinBasis.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib B64_AbsErr
  B64_Horner B64_HornerGamma B64_DeCasteljau.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  dcR is the Bernstein sum.                                              *)
(* -------------------------------------------------------------------------- *)

Lemma dcR_step_nth : forall s t row i, (S i < length row)%nat ->
  nth i (dcR_step s t row) 0 = s * nth i row 0 + t * nth (S i) row 0.
Proof.
  intros s t row. induction row as [|x row IH]; intros i Hi; [simpl in Hi; lia|].
  destruct row as [|y row]; [simpl in Hi; lia|].
  destruct i as [|i]; [reflexivity|].
  cbn [dcR_step nth]. apply IH. simpl in *. lia.
Qed.

Lemma bz_sum_scal : forall c (f : nat -> R) n,
  sum_f_R0 (fun i => c * f i) n = c * sum_f_R0 f n.
Proof.
  intros c f n. induction n as [|n IH]; [simpl; ring|].
  rewrite !tech5, IH. ring.
Qed.

Theorem dcR_bern : forall n row t, length row = S n ->
  dcR (1 - t) t n row = sum_f_R0 (fun i => nth i row 0 * bern n i t) n.
Proof.
  induction n as [|n IH]; intros row t Hlen.
  - destruct row as [|x [|y r]]; simpl in Hlen; try lia.
    cbn. ring.
  - cbn [dcR].
    assert (Hl : length (dcR_step (1 - t) t row) = S n)
      by (rewrite dcR_step_length, Hlen; reflexivity).
    rewrite (IH _ t Hl).
    transitivity (sum_f_R0 (fun i => (1 - t) * (nth i row 0 * bern n i t)
                                     + t * (nth (S i) row 0 * bern n i t)) n).
    { apply sum_eq. intros i Hi.
      rewrite dcR_step_nth by (rewrite Hlen; lia). ring. }
    rewrite sum_plus, !bz_sum_scal.
    transitivity (sum_f_R0 (fun j => (1 - t) * (nth j row 0 * bern n j t)
        + t * (nth j row 0 * match j with O => 0 | S j' => bern n j' t end)) (S n)).
    2: { apply sum_eq. intros j Hj. rewrite bern_Sn. ring. }
    rewrite sum_plus, !bz_sum_scal.
    rewrite (tech5 (fun j => nth j row 0 * bern n j t) n).
    rewrite (bern_gt n (S n) t) by lia.
    rewrite (decomp_sum (fun j => nth j row 0 * match j with O => 0 | S j' => bern n j' t end) (S n))
      by lia.
    cbn [Nat.pred]. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The comparison family (1 - 2t)^n.                                      *)
(* -------------------------------------------------------------------------- *)

(* Bernstein side: alternating +-c control values. *)
Fixpoint altr (k : nat) (c : R) : list R :=
  match k with
  | O => []
  | S k' => c :: altr k' (- c)
  end.

Lemma altr_step : forall k s t c,
  dcR_step s t (altr (S k) c) = altr k (c * (s - t)).
Proof.
  induction k as [|k IH]; intros s t c; [reflexivity|].
  assert (E1 : dcR_step s t (altr (S (S k)) c)
               = (s * c + t * (- c)) :: dcR_step s t (altr (S k) (- c)))
    by (destruct k; reflexivity).
  rewrite E1, IH.
  cbn [altr]. f_equal; [ring|]. f_equal. ring.
Qed.

Lemma alt_dcR : forall n s t c, dcR s t n (altr (S n) c) = c * (s - t) ^ n.
Proof.
  induction n as [|n IH]; intros s t c; [cbn; ring|].
  cbn [dcR]. rewrite altr_step, IH. rewrite hg_pow_S. ring.
Qed.

(* So de Casteljau of the alternating +-1 net is (1 - 2t)^n. *)
Corollary alt_dcR_unit : forall n t, dcR (1 - t) t n (altr (S n) 1) = (1 - 2 * t) ^ n.
Proof.
  intros n t. rewrite alt_dcR. replace (1 - t - t) with (1 - 2 * t) by ring. ring.
Qed.

(* ... and its Bernstein sum is the same number. *)
Corollary alt_bern_sum : forall n t,
  sum_f_R0 (fun i => nth i (altr (S n) 1) 0 * bern n i t) n = (1 - 2 * t) ^ n.
Proof.
  intros n t. rewrite <- dcR_bern, alt_dcR_unit; [reflexivity|].
  clear t. assert (forall k c, length (altr k c) = k) as H.
  { induction k as [|k IH]; intro c; [reflexivity|]. simpl. rewrite IH. reflexivity. }
  apply H.
Qed.

(* Power side. *)
Lemma hz_polyR_map_seq : forall m (g : nat -> R) k x,
  hz_polyR (map g (seq 0 (S m))) k x = sum_f_R0 (fun i => g i * x ^ (k + i)) m.
Proof.
  induction m as [|m IH]; intros g k x.
  - cbn. rewrite Nat.add_0_r. ring.
  - change (seq 0 (S (S m))) with (0%nat :: seq 1 (S m)).
    rewrite (decomp_sum (fun i => g i * x ^ (k + i)) (S m)) by lia.
    cbn [map hz_polyR].
    rewrite <- seq_shift, map_map.
    rewrite (IH (fun i => g (S i)) (S k) x).
    cbn [Nat.pred]. rewrite Nat.add_0_r.
    f_equal.
    apply sum_eq. intros i _. replace (k + S i)%nat with (S k + i)%nat by lia. reflexivity.
Qed.

Definition hcoef (n : nat) : list R :=
  map (fun i => C n i * (-2) ^ i) (seq 0 (S n)).

Definition hmaj (n : nat) : list R :=
  map (fun i => C n i * 2 ^ i) (seq 0 (S n)).

Lemma hcoef_length : forall n, length (hcoef n) = S n.
Proof. intro n. unfold hcoef. rewrite length_map, length_seq. reflexivity. Qed.

Lemma hmaj_length : forall n, length (hmaj n) = S n.
Proof. intro n. unfold hmaj. rewrite length_map, length_seq. reflexivity. Qed.

(* Horner over R on the power coefficients of (1-2x)^n is (1-2x)^n. *)
Theorem horner_binomial : forall n x, hz_horner_R (hcoef n) x = (1 - 2 * x) ^ n.
Proof.
  intros n x. unfold hcoef.
  rewrite hz_horner_R_sum, hz_polyR_map_seq.
  replace (1 - 2 * x) with (-2 * x + 1) by ring.
  rewrite binomial. apply sum_eq. intros i _.
  rewrite pow1, Rpow_mult_distr. cbn [Nat.add]. ring.
Qed.

(* The magnitude majorant at Z = 1 is 3^n. *)
Theorem hmaj_at_one : forall n, hz_M (hmaj n) 1 = 3 ^ n.
Proof.
  intro n. unfold hmaj. rewrite hz_M_sum, hz_polyR_map_seq.
  replace 3 with (2 + 1) by ring.
  rewrite binomial. apply sum_eq. intros i _.
  rewrite !pow1. cbn [Nat.add]. ring.
Qed.

Lemma C_nonneg : forall n p, 0 <= C n p.
Proof.
  intros n p. unfold C, Rdiv. apply Rmult_le_pos; [apply pos_INR|].
  apply Rlt_le, Rinv_0_lt_compat.
  apply Rmult_lt_0_compat; apply INR_fact_lt_0.
Qed.

Lemma forall2_map_le : forall (g h : nat -> R) (l : list nat),
  (forall i, Rabs (g i) <= h i) ->
  Forall2 (fun c m => Rabs c <= m) (map g l) (map h l).
Proof.
  intros g h l H. induction l as [|i l IH]; constructor; [apply H | exact IH].
Qed.

(* |a_i| <= C(n,i) 2^i: hmaj majorises hcoef coefficientwise. *)
Lemma hmaj_dominates : forall n, Forall2 (fun c m => Rabs c <= m) (hcoef n) (hmaj n).
Proof.
  intro n. unfold hcoef, hmaj. apply forall2_map_le. intro i.
  rewrite Rabs_mult, (Rabs_right (C n i)) by (apply Rle_ge; apply C_nonneg).
  rewrite <- RPow_abs. replace (Rabs (-2)) with 2.
  - lra.
  - symmetry. rewrite Rabs_left by lra. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The bound comparison.                                                  *)
(* -------------------------------------------------------------------------- *)

Definition dc_kappa0 : R := dc_kappa 0.

Lemma dc_kappa0_eq : dc_kappa0 = 2 * b64ae_u + b64ae_u * b64ae_u.
Proof. unfold dc_kappa0, dc_kappa. ring. Qed.

(* main terms of the two proved bounds on p_n = (1-2t)^n, Z = M = 1 *)
Definition dc_main (n : nat) : R :=
  (INR n * dc_kappa0 / (1 - INR n * dc_kappa0)) * 1.

Definition horner_main (n : nat) : R :=
  ((2 * INR n * b64ae_u) / (1 - 2 * INR n * b64ae_u)) * 3 ^ n.

(* horner_main IS the main term of b64_horner_gamma at ms = hmaj n, Z = 1. *)
Lemma horner_main_instance : forall n,
  ((2 * INR (Nat.pred (length (hmaj n))) * b64ae_u)
   / (1 - 2 * INR (Nat.pred (length (hmaj n))) * b64ae_u)) * hz_M (hmaj n) 1
  = horner_main n.
Proof.
  intro n. rewrite hmaj_length, hmaj_at_one. cbn [Nat.pred]. reflexivity.
Qed.

(* de Casteljau main term is <= 6 n u (coefficient-size independent). *)
Lemma dc_main_le : forall n, INR n * dc_kappa0 <= / 2 -> dc_main n <= 3 * (2 * INR n * b64ae_u).
Proof.
  intros n Hn. pose proof b64ae_u_small as [Hu0 Hu1].
  pose proof (pos_INR n) as Hn0. unfold dc_main. rewrite dc_kappa0_eq in *.
  set (a := INR n * (2 * b64ae_u + b64ae_u * b64ae_u)) in *.
  assert (Ha : a = 2 * INR n * b64ae_u + INR n * (b64ae_u * b64ae_u)) by (unfold a; ring).
  assert (Hb : INR n * (b64ae_u * b64ae_u) <= INR n * b64ae_u * / 1000).
  { replace (INR n * b64ae_u * / 1000) with (INR n * (b64ae_u * / 1000)) by ring.
    apply Rmult_le_compat_l; [exact Hn0|]. apply Rmult_le_compat_l; lra. }
  assert (Hnu : 0 <= INR n * b64ae_u) by (apply Rmult_le_pos; lra).
  assert (Ha0 : 0 <= a) by (rewrite Ha; assert (0 <= INR n * (b64ae_u * b64ae_u)) by (apply Rmult_le_pos; [lra | nra]); lra).
  assert (Hq : a / (1 - a) <= 2 * a).
  { apply (Rmult_le_reg_r (1 - a)); [lra|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  rewrite Rmult_1_r.
  lra.
Qed.

(* Horner main term is >= 3^n * 2 n u. *)
Lemma horner_main_ge : forall n, 2 * INR n * b64ae_u < 1 ->
  3 ^ n * (2 * INR n * b64ae_u) <= horner_main n.
Proof.
  intros n Hn. pose proof b64ae_u_small as [Hu0 Hu1].
  pose proof (pos_INR n) as Hn0. unfold horner_main.
  set (b := 2 * INR n * b64ae_u) in *.
  assert (Hb0 : 0 <= b) by (unfold b; repeat apply Rmult_le_pos; lra).
  assert (Hp : 0 <= 3 ^ n) by (apply pow_le; lra).
  assert (Hq : b <= b / (1 - b)).
  { apply (Rmult_le_reg_r (1 - b)); [lra|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  assert (3 ^ n * b <= 3 ^ n * (b / (1 - b))) by (apply Rmult_le_compat_l; assumption).
  lra.
Qed.

(* WITNESS {"claimId":"s1-b64-bezier-stability","topic":"numerics","lemma":"bezier_vs_horner_bound","title":"On the comparison family (1-2t)^n (Bernstein coefficients +-1, power coefficients C(n,i)(-2)^i with sum |a_i| = 3^n) the proved Horner bound main term (gamma_2n * 3^n, the b64_horner_gamma instance) is at least 3^n/3 times the proved de Casteljau main term (<= 6nu); both evaluators target the same real value (1-2t)^n, and dcR is the Bernstein-basis sum. A comparison of upper bounds, not of true errors.","file":"theories-flocq/B64_BezierStability.v","witness":"bezier_vs_horner_bound","board":"ADR-0006"} *)
Theorem bezier_vs_horner_bound : forall n,
  2 * INR n * b64ae_u < 1 -> INR n * dc_kappa0 <= / 2 ->
  dc_main n * 3 ^ n <= 3 * horner_main n.
Proof.
  intros n H1 H2.
  pose proof (dc_main_le n H2). pose proof (horner_main_ge n H1).
  assert (Hp : 0 <= 3 ^ n) by (apply pow_le; lra).
  assert (dc_main n * 3 ^ n <= 3 * (2 * INR n * b64ae_u) * 3 ^ n)
    by (apply Rmult_le_compat_r; assumption).
  lra.
Qed.

Print Assumptions dcR_bern.
Print Assumptions alt_bern_sum.
Print Assumptions horner_binomial.
Print Assumptions hmaj_at_one.
Print Assumptions bezier_vs_horner_bound.
