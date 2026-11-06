(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_HornerGamma
   ----------------------------------------------------------------------------
   Closed-form (gamma_{2n}-style) corollary of the S1 Horner kernel.

   B64_Horner.v proves `b64_horner_err` against the recursive bound `hz_E`.
   This file turns `hz_E` into the classical shape

     |fl(horner cs z) - horner cs z|
        <= gamma_{2n} * sum_i m_i Z^i  +  2^-1075 * hg_R ms Z

   where n = degree = length - 1, gamma_k = k u / (1 - k u), u = 2^-53,
   m_i bound |c_i|, |z| <= Z, and `hz_M ms Z` IS sum_i m_i Z^i (proved:
   `hz_M_is_horner`).  The second term is the absolute underflow floor
   (binary64 has subnormals; the usual "relative model" has none); for
   Z <= 1 it is at most 3 n (1+u)^{2n} 2^-1075 (`hg_R_le_unit`).

   Also: Horner over R IS the power sum (`hz_horner_R_sum`), the "correctness
   over R" rung.

   Derivation (no new floating-point reasoning): with N = hz_M + hz_E the
   `hz_E_cons` recursion collapses to
       N_new = (1+u)^2 Z N + (1+u) m + (2+u) 2^-1075,
   so N_n <= (1+u)^{2(n)} hz_M + 2^-1075 hg_R, and (1+u)^{2n} - 1 <= gamma_{2n}
   by Bernoulli on (1-u).

   claimId: s1-b64-horner-gamma.  witness: b64_horner_gamma.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia Psatz ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib B64_AbsErr B64_Horner.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  Correctness over R: Horner is the power sum.                           *)
(* -------------------------------------------------------------------------- *)

(* c_0 x^k + c_1 x^(k+1) + ... *)
Fixpoint hz_polyR (cs : list R) (k : nat) (x : R) : R :=
  match cs with
  | [] => 0
  | c :: cs' => c * x ^ k + hz_polyR cs' (S k) x
  end.

Lemma hz_horner_R_poly : forall cs k x,
  x ^ k * hz_horner_R cs x = hz_polyR cs k x.
Proof.
  induction cs as [|c cs IH]; intros k x; cbn [hz_horner_R hz_polyR].
  - ring.
  - rewrite <- IH. simpl. ring.
Qed.

(* sum_i c_i x^i, with c_0 the constant term. *)
Lemma hz_horner_R_sum : forall cs x, hz_horner_R cs x = hz_polyR cs 0 x.
Proof. intros. rewrite <- hz_horner_R_poly. simpl. ring. Qed.

(* The magnitude majorant is the same recursion: sum_i m_i Z^i. *)
Lemma hz_M_is_horner : forall ms Z, hz_M ms Z = hz_horner_R ms Z.
Proof. induction ms as [|m ms IH]; intro Z; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma hz_M_sum : forall ms Z, hz_M ms Z = hz_polyR ms 0 Z.
Proof. intros. rewrite hz_M_is_horner. apply hz_horner_R_sum. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The collapsed recursion.                                               *)
(* -------------------------------------------------------------------------- *)

Lemma hg_pow_S : forall (x : R) n, x ^ S n = x * x ^ n.
Proof. reflexivity. Qed.

Definition hg_theta : R := (1 + b64ae_u) * (1 + b64ae_u).

(* Coefficient of the absolute underflow floor 2^-1075. *)
Fixpoint hg_R (ms : list R) (Z : R) : R :=
  match ms with
  | [] => 0
  | [m] => 0
  | m :: ms' => hg_theta * Z * hg_R ms' Z + (2 + b64ae_u)
  end.

Lemma hg_theta_ge : 1 <= hg_theta.
Proof.
  pose proof b64ae_u_small as [Hu _]. unfold hg_theta. nra.
Qed.

Lemma hg_theta_pow_ge : forall n, 1 <= hg_theta ^ n.
Proof.
  pose proof hg_theta_ge as Hg.
  induction n as [|n IH]; [simpl; lra|].
  rewrite hg_pow_S. nra.
Qed.

Lemma hg_R_nonneg : forall ms Z, 0 <= Z -> 0 <= hg_R ms Z.
Proof.
  pose proof b64ae_u_small as [Hu _]. pose proof hg_theta_ge as Hg.
  induction ms as [|m ms IH]; intros Z HZ; [cbn; lra|].
  destruct ms as [|m' ms']; [cbn; lra|].
  change (hg_R (m :: m' :: ms') Z)
    with (hg_theta * Z * hg_R (m' :: ms') Z + (2 + b64ae_u)).
  assert (0 <= hg_theta * Z) by (apply Rmult_le_pos; lra).
  assert (0 <= hg_theta * Z * hg_R (m' :: ms') Z)
    by (apply Rmult_le_pos; [assumption | apply IH; assumption]).
  lra.
Qed.

(* N = M + E collapses: N_n <= theta^n M + 2^-1075 R. *)
Lemma hg_N_bound : forall ms Z, Forall (fun m => 0 <= m) ms -> 0 <= Z ->
  hz_M ms Z + hz_E ms Z
  <= hg_theta ^ Nat.pred (length ms) * hz_M ms Z + b64ae_e0 * hg_R ms Z.
Proof.
  intros ms Z H HZ.
  pose proof b64ae_u_small as [Hu0 Hu1]. pose proof b64ae_e0_small as [He0 He1].
  pose proof hg_theta_ge as Hg.
  induction H as [|m ms Hm Hms IH].
  - cbn. lra.
  - destruct ms as [|m' ms'].
    + cbn. lra.
    + rewrite hz_E_cons.
      change (hz_M (m :: m' :: ms') Z) with (hz_M (m' :: ms') Z * Z + m).
      change (hg_R (m :: m' :: ms') Z)
        with (hg_theta * Z * hg_R (m' :: ms') Z + (2 + b64ae_u)).
      change (Nat.pred (length (m :: m' :: ms'))) with (S (length ms')).
      change (Nat.pred (length (m' :: ms'))) with (length ms') in IH.
      rewrite hg_pow_S.
      set (M' := hz_M (m' :: ms') Z) in *.
      set (E' := hz_E (m' :: ms') Z) in *.
      set (R' := hg_R (m' :: ms') Z) in *.
      set (P := hg_theta ^ length ms') in *.
      pose proof (hg_theta_pow_ge (length ms')) as HP. fold P in HP.
      (* algebraic collapse *)
      assert (Hcol :
        M' * Z + m
        + (Z * E' + b64ae_u * ((M' + E') * Z) + b64ae_e0
           + (b64ae_u * ((M' + E') * Z * (1 + b64ae_u) + b64ae_e0 + m) + b64ae_e0))
        = hg_theta * Z * (M' + E') + (1 + b64ae_u) * m + (2 + b64ae_u) * b64ae_e0).
      { unfold hg_theta. ring. }
      rewrite Hcol.
      assert (Hs1 : hg_theta * Z * (M' + E')
                    <= hg_theta * Z * (P * M' + b64ae_e0 * R')).
      { apply Rmult_le_compat_l; [|exact IH]. apply Rmult_le_pos; lra. }
      assert (Hs2 : (1 + b64ae_u) * m <= hg_theta * P * m).
      { apply Rmult_le_compat_r; [exact Hm|].
        unfold hg_theta in *. nra. }
      assert (Eq : hg_theta * (P * (M' * Z + m)) + b64ae_e0 * (hg_theta * Z * R' + (2 + b64ae_u))
                 = hg_theta * Z * (P * M' + b64ae_e0 * R') + hg_theta * P * m
                   + (2 + b64ae_u) * b64ae_e0) by ring.
      lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Bernoulli: (1+u)^{2j} - 1 <= gamma_{2j}.                               *)
(* -------------------------------------------------------------------------- *)

Lemma hg_bernoulli : forall n w, 0 <= w <= 1 -> 1 - INR n * w <= (1 - w) ^ n.
Proof.
  intros n w [H0 H1].
  induction n as [|n IH]; [simpl; lra|].
  rewrite hg_pow_S, S_INR.
  assert (0 <= INR n * w * w) by (apply Rmult_le_pos; [apply Rmult_le_pos; [apply pos_INR|]|]; lra).
  assert ((1 - w) * (1 - INR n * w) <= (1 - w) * (1 - w) ^ n)
    by (apply Rmult_le_compat_l; lra).
  nra.
Qed.

Lemma hg_pow_le_one : forall n a, 0 <= a <= 1 -> a ^ n <= 1.
Proof.
  intros n a [H0 H1]. induction n as [|n IH]; [simpl; lra|].
  rewrite hg_pow_S. assert (0 <= a ^ n) by (apply pow_le; lra). nra.
Qed.

(* theta^j (1 - 2 j u) <= 1. *)
Lemma hg_theta_pow_inv : forall j,
  hg_theta ^ j * (1 - 2 * INR j * b64ae_u) <= 1.
Proof.
  intro j. pose proof b64ae_u_small as [Hu0 Hu1].
  set (q := (1 - b64ae_u) * (1 - b64ae_u)).
  assert (Hq : 0 <= q <= 1) by (unfold q; split; nra).
  assert (Htq : hg_theta * q <= 1).
  { unfold hg_theta, q.
    replace ((1 + b64ae_u) * (1 + b64ae_u) * ((1 - b64ae_u) * (1 - b64ae_u)))
      with ((1 - b64ae_u * b64ae_u) * (1 - b64ae_u * b64ae_u)) by ring.
    assert (Hw0 : 0 <= b64ae_u * b64ae_u) by nra.
    assert (Hw1 : b64ae_u * b64ae_u <= 1) by nra.
    set (w := b64ae_u * b64ae_u) in *.
    nra. }
  assert (Htq0 : 0 <= hg_theta * q)
    by (apply Rmult_le_pos; [pose proof hg_theta_ge; lra | lra]).
  assert (H1 : (hg_theta * q) ^ j <= 1) by (apply hg_pow_le_one; lra).
  rewrite Rpow_mult_distr in H1.
  assert (Hw : 1 - INR j * (2 * b64ae_u) <= q ^ j).
  { replace q with (1 - (2 * b64ae_u - b64ae_u * b64ae_u)) by (unfold q; ring).
    assert (HB := hg_bernoulli j (2 * b64ae_u - b64ae_u * b64ae_u)).
    assert (0 <= 2 * b64ae_u - b64ae_u * b64ae_u <= 1) by (split; nra).
    specialize (HB H).
    assert (INR j * (2 * b64ae_u) <= INR j * (2 * b64ae_u - b64ae_u * b64ae_u) + INR j * (b64ae_u * b64ae_u))
      by lra.
    assert (0 <= INR j * (b64ae_u * b64ae_u))
      by (apply Rmult_le_pos; [apply pos_INR | nra]).
    replace (1 - (2 * b64ae_u - b64ae_u * b64ae_u)) with q in * by (unfold q; ring).
    lra. }
  assert (Hp : 0 <= hg_theta ^ j) by (apply pow_le; pose proof hg_theta_ge; lra).
  assert (hg_theta ^ j * (1 - 2 * INR j * b64ae_u) <= hg_theta ^ j * q ^ j)
    by (apply Rmult_le_compat_l; [exact Hp | lra]).
  lra.
Qed.

Lemma hg_gamma2 : forall j, 2 * INR j * b64ae_u < 1 ->
  hg_theta ^ j - 1 <= (2 * INR j * b64ae_u) / (1 - 2 * INR j * b64ae_u).
Proof.
  intros j Hj.
  set (D := 1 - 2 * INR j * b64ae_u) in *.
  assert (HD : 0 < D) by (unfold D; lra).
  assert (Hmain := hg_theta_pow_inv j). fold D in Hmain.
  apply (Rmult_le_reg_r D); [exact HD|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
  assert (2 * INR j * b64ae_u = 1 - D) by (unfold D; ring).
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The gamma_{2n} theorem.                                                *)
(* -------------------------------------------------------------------------- *)

Lemma hg_E_le : forall ms Z, Forall (fun m => 0 <= m) ms -> 0 <= Z ->
  hz_E ms Z <= (hg_theta ^ Nat.pred (length ms) - 1) * hz_M ms Z + b64ae_e0 * hg_R ms Z.
Proof.
  intros ms Z H HZ. pose proof (hg_N_bound ms Z H HZ). lra.
Qed.

(* WITNESS {"claimId":"s1-b64-horner-gamma","topic":"numerics","lemma":"b64_horner_gamma","title":"Binary64 Horner evaluation is finite and within gamma_{2n} * sum_i m_i Z^i + 2^-1075 * R of the same polynomial evaluated exactly at the same argument (n = degree, gamma_k = k u/(1 - k u), u = 2^-53), given |z| <= Z, coefficient magnitudes m_i and the hz_safe overflow guard","file":"theories-flocq/B64_HornerGamma.v","witness":"b64_horner_gamma","board":"ADR-0006"} *)
Theorem b64_horner_gamma : forall cs ms z Z,
  hz_coeffs_ok cs ms -> fin z = true -> Rabs (B2R z) <= Z -> 0 <= Z ->
  hz_safe ms Z ->
  2 * INR (Nat.pred (length ms)) * b64ae_u < 1 ->
  fin (b64_horner cs z) = true /\
  Rabs (B2R (b64_horner cs z) - hz_horner_R (map B2R cs) (B2R z))
    <= ((2 * INR (Nat.pred (length ms)) * b64ae_u)
        / (1 - 2 * INR (Nat.pred (length ms)) * b64ae_u)) * hz_M ms Z
       + b64ae_e0 * hg_R ms Z.
Proof.
  intros cs ms z Z H Fz Hz HZ Hsafe Hn.
  destruct (b64_horner_err cs ms z Z H Fz Hz HZ Hsafe) as [Fin Err].
  split; [exact Fin|].
  assert (Hnn := hz_ms_nonneg _ _ H).
  eapply Rle_trans; [exact Err|].
  eapply Rle_trans; [apply hg_E_le; assumption|].
  assert (HM := hz_M_nonneg ms Z Hnn HZ).
  assert (Hg := hg_gamma2 (Nat.pred (length ms)) Hn).
  assert ((hg_theta ^ Nat.pred (length ms) - 1) * hz_M ms Z
          <= ((2 * INR (Nat.pred (length ms)) * b64ae_u)
              / (1 - 2 * INR (Nat.pred (length ms)) * b64ae_u)) * hz_M ms Z)
    by (apply Rmult_le_compat_r; assumption).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Unit-interval simplification of the underflow coefficient.             *)
(* -------------------------------------------------------------------------- *)

Lemma hg_R_le_unit : forall ms Z, 0 <= Z -> Z <= 1 ->
  hg_R ms Z <= 3 * INR (Nat.pred (length ms)) * hg_theta ^ Nat.pred (length ms).
Proof.
  intros ms Z HZ HZ1.
  pose proof b64ae_u_small as [Hu0 Hu1]. pose proof hg_theta_ge as Hg.
  induction ms as [|m ms IH]; [cbn; lra|].
  destruct ms as [|m' ms']; [cbn; lra|].
  change (hg_R (m :: m' :: ms') Z)
    with (hg_theta * Z * hg_R (m' :: ms') Z + (2 + b64ae_u)).
  change (Nat.pred (length (m :: m' :: ms'))) with (S (length ms')).
  change (Nat.pred (length (m' :: ms'))) with (length ms') in IH.
  rewrite hg_pow_S, S_INR.
  set (R' := hg_R (m' :: ms') Z) in *.
  set (P := hg_theta ^ length ms') in *.
  pose proof (hg_theta_pow_ge (length ms')) as HP. fold P in HP.
  assert (HR0 : 0 <= R') by (apply hg_R_nonneg; exact HZ).
  assert (HtZ : hg_theta * Z <= hg_theta) by nra.
  assert (A : hg_theta * Z * R' <= hg_theta * (3 * INR (length ms') * P)).
  { eapply Rle_trans; [apply Rmult_le_compat_r; [exact HR0 | exact HtZ]|].
    apply Rmult_le_compat_l; [lra | exact IH]. }
  assert (0 <= INR (length ms')) by apply pos_INR.
  assert (B : 3 * INR (length ms') * P + 3 <= 3 * (INR (length ms') + 1) * P) by nra.
  assert (C : (2 + b64ae_u) <= 3) by lra.
  assert (D : 3 * INR (length ms') * P * hg_theta
              <= 3 * INR (length ms') * (hg_theta * P) ) by nra.
  nra.
Qed.

Print Assumptions hz_horner_R_sum.
Print Assumptions hz_M_is_horner.
Print Assumptions hg_N_bound.
Print Assumptions hg_gamma2.
Print Assumptions b64_horner_gamma.
Print Assumptions hg_R_le_unit.
