(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Horner
   ----------------------------------------------------------------------------
   S1 of the transcendental programme (docs/transcendental-inventory.tsv):
   the binary64 polynomial kernel.

   `b64_horner [c0; c1; ...; cn] z` evaluates c0 + z (c1 + z (... cn)) with
   one RNE product and one RNE sum per coefficient.  `b64_horner_err` bounds
   it against the SAME coefficients evaluated exactly at the same binary64
   argument:
     |B2R (b64_horner cs z) - hz_horner_R (map B2R cs) (B2R z)| <= hz_E ms Z
   given |B2R z| <= Z and coefficient magnitudes |B2R c_i| <= m_i.  The
   error of rounding the mathematical coefficients, and of the argument z
   itself, is NOT in this bound (separate budget lines, S2.3 / S2.1).

   hz_E is a plain recursive real expression, so an instance gets a concrete
   number by unfolding and lra (B64_SinPoly.v).  Normal and subnormal
   results are both covered (b64ae_round_err: u |x| + e0); finiteness comes
   from the hz_safe magnitude guard.
   claimId: s1-b64-horner.  witness: b64_horner_err.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib B64_AbsErr.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  The evaluator and its exact counterpart.                               *)
(* -------------------------------------------------------------------------- *)

Definition hz_zero : binary64 := Binary.B754_zero prec emax false.

Fixpoint b64_horner (cs : list binary64) (z : binary64) : binary64 :=
  match cs with
  | [] => hz_zero
  | [c] => c
  | c :: cs' => b64_plus (b64_mult (b64_horner cs' z) z) c
  end.

Fixpoint hz_horner_R (cs : list R) (x : R) : R :=
  match cs with
  | [] => 0
  | c :: cs' => hz_horner_R cs' x * x + c
  end.

(* Magnitude bound of the exact polynomial on |x| <= Z. *)
Fixpoint hz_M (ms : list R) (Z : R) : R :=
  match ms with
  | [] => 0
  | m :: ms' => hz_M ms' Z * Z + m
  end.

(* Accumulated evaluation error. *)
Fixpoint hz_E (ms : list R) (Z : R) : R :=
  match ms with
  | [] => 0
  | [m] => 0
  | m :: ms' =>
      Z * hz_E ms' Z + b64ae_u * ((hz_M ms' Z + hz_E ms' Z) * Z) + b64ae_e0
      + (b64ae_u * ((hz_M ms' Z + hz_E ms' Z) * Z * (1 + b64ae_u) + b64ae_e0 + m)
         + b64ae_e0)
  end.

(* No intermediate can overflow. *)
Fixpoint hz_safe (ms : list R) (Z : R) : Prop :=
  match ms with
  | [] => True
  | [m] => True
  | m :: ms' =>
      hz_safe ms' Z /\
      (hz_M ms' Z + hz_E ms' Z) * Z * 2 + m + 1 <= bpow radix2 1000
  end.

Definition hz_coeffs_ok (cs : list binary64) (ms : list R) : Prop :=
  Forall2 (fun c m => fin c = true /\ Rabs (B2R c) <= m) cs ms.

(* -------------------------------------------------------------------------- *)
(* §2  Unfolding lemmas.                                                      *)
(* -------------------------------------------------------------------------- *)

Lemma b64_horner_cons : forall c c' cs z,
  b64_horner (c :: c' :: cs) z = b64_plus (b64_mult (b64_horner (c' :: cs) z) z) c.
Proof. reflexivity. Qed.

Lemma hz_E_cons : forall m m' ms Z,
  hz_E (m :: m' :: ms) Z =
  Z * hz_E (m' :: ms) Z
  + b64ae_u * ((hz_M (m' :: ms) Z + hz_E (m' :: ms) Z) * Z) + b64ae_e0
  + (b64ae_u * ((hz_M (m' :: ms) Z + hz_E (m' :: ms) Z) * Z * (1 + b64ae_u)
                + b64ae_e0 + m) + b64ae_e0).
Proof. reflexivity. Qed.

Lemma hz_ms_nonneg : forall cs ms, hz_coeffs_ok cs ms -> Forall (fun m => 0 <= m) ms.
Proof.
  intros cs ms H. induction H as [|c m cs ms [_ Hm] _ IH]; constructor; [|exact IH].
  eapply Rle_trans; [apply Rabs_pos | exact Hm].
Qed.

Lemma hz_M_nonneg : forall ms Z, Forall (fun m => 0 <= m) ms -> 0 <= Z -> 0 <= hz_M ms Z.
Proof.
  intros ms Z H HZ. induction H as [|m ms Hm _ IH]; cbn; [lra|].
  assert (0 <= hz_M ms Z * Z) by (apply Rmult_le_pos; assumption). lra.
Qed.

Lemma hz_E_nonneg : forall ms Z, Forall (fun m => 0 <= m) ms -> 0 <= Z -> 0 <= hz_E ms Z.
Proof.
  intros ms Z H HZ.
  pose proof b64ae_u_small as [Hu _]. pose proof b64ae_e0_small as [He _].
  induction H as [|m ms Hm Hms IH]; [cbn; lra|].
  destruct ms as [|m' ms']; [cbn; lra|].
  rewrite hz_E_cons.
  assert (HM := hz_M_nonneg _ Z Hms HZ).
  assert (0 <= Z * hz_E (m' :: ms') Z) by (apply Rmult_le_pos; assumption).
  assert (0 <= (hz_M (m' :: ms') Z + hz_E (m' :: ms') Z) * Z)
    by (apply Rmult_le_pos; lra).
  assert (0 <= b64ae_u * ((hz_M (m' :: ms') Z + hz_E (m' :: ms') Z) * Z))
    by (apply Rmult_le_pos; lra).
  assert (0 <= (hz_M (m' :: ms') Z + hz_E (m' :: ms') Z) * Z * (1 + b64ae_u))
    by (apply Rmult_le_pos; lra).
  assert (0 <= b64ae_u * ((hz_M (m' :: ms') Z + hz_E (m' :: ms') Z) * Z * (1 + b64ae_u)
                          + b64ae_e0 + m))
    by (apply Rmult_le_pos; lra).
  lra.
Qed.

(* hz_E is monotone in the suffix bounds: one level at a time, an instance
   checks a small numeric inequality instead of the whole nested expression. *)
Lemma hz_E_cons_le : forall m m' ms Z Mb Eb,
  0 <= Z -> 0 <= hz_M (m' :: ms) Z -> 0 <= hz_E (m' :: ms) Z ->
  hz_M (m' :: ms) Z <= Mb -> hz_E (m' :: ms) Z <= Eb ->
  hz_E (m :: m' :: ms) Z
  <= Z * Eb + b64ae_u * ((Mb + Eb) * Z) + b64ae_e0
     + (b64ae_u * ((Mb + Eb) * Z * (1 + b64ae_u) + b64ae_e0 + m) + b64ae_e0).
Proof.
  intros m m' ms Z Mb Eb HZ HM HE HMb HEb.
  rewrite hz_E_cons.
  set (M := hz_M (m' :: ms) Z) in *. set (E := hz_E (m' :: ms) Z) in *.
  pose proof b64ae_u_small as [Hu0 _].
  assert (A1 : Z * E <= Z * Eb) by (apply Rmult_le_compat_l; assumption).
  assert (A2 : (M + E) * Z <= (Mb + Eb) * Z) by (apply Rmult_le_compat_r; lra).
  assert (A3 : b64ae_u * ((M + E) * Z) <= b64ae_u * ((Mb + Eb) * Z))
    by (apply Rmult_le_compat_l; lra).
  assert (A4 : (M + E) * Z * (1 + b64ae_u) <= (Mb + Eb) * Z * (1 + b64ae_u))
    by (apply Rmult_le_compat_r; lra).
  assert (A5 : b64ae_u * ((M + E) * Z * (1 + b64ae_u) + b64ae_e0 + m)
               <= b64ae_u * ((Mb + Eb) * Z * (1 + b64ae_u) + b64ae_e0 + m))
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

(* The exact polynomial stays within hz_M on |x| <= Z. *)
Lemma hz_horner_R_bound : forall cs ms x Z,
  hz_coeffs_ok cs ms -> Rabs x <= Z ->
  Rabs (hz_horner_R (map B2R cs) x) <= hz_M ms Z.
Proof.
  intros cs ms x Z H Hx.
  induction H as [|c m cs ms [_ Hm] _ IH]; cbn.
  - rewrite Rabs_R0. lra.
  - eapply Rle_trans; [apply Rabs_triang|].
    apply Rplus_le_compat; [|exact Hm].
    apply b64ae_abs_mult_le; assumption.
Qed.

(* Lipschitz constant of the exact polynomial on [-Z, Z]. *)
Fixpoint hz_L (ms : list R) (Z : R) : R :=
  match ms with
  | [] => 0
  | m :: ms' => hz_L ms' Z * Z + hz_M ms' Z
  end.

(* Magnitude bound for a REAL coefficient list. *)
Lemma hz_horner_R_bound_R : forall (cs ms : list R) x Z,
  Forall2 (fun c m => Rabs c <= m) cs ms -> Rabs x <= Z ->
  Rabs (hz_horner_R cs x) <= hz_M ms Z.
Proof.
  intros cs ms x Z H Hx.
  induction H as [|c m cs ms Hm _ IH]; cbn.
  - rewrite Rabs_R0. lra.
  - eapply Rle_trans; [apply Rabs_triang|].
    apply Rplus_le_compat; [|exact Hm].
    apply b64ae_abs_mult_le; assumption.
Qed.

Lemma hz_horner_R_lip : forall (cs ms : list R) x y Z,
  Forall2 (fun c m => Rabs c <= m) cs ms -> Rabs x <= Z -> Rabs y <= Z ->
  Rabs (hz_horner_R cs x - hz_horner_R cs y) <= hz_L ms Z * Rabs (x - y).
Proof.
  intros cs ms x y Z H Hx Hy.
  induction H as [|c m cs ms Hm Hrest IH]; cbn.
  - rewrite Rminus_diag, Rabs_R0. lra.
  - replace (hz_horner_R cs x * x + c - (hz_horner_R cs y * y + c))
      with ((hz_horner_R cs x - hz_horner_R cs y) * x
            + hz_horner_R cs y * (x - y)) by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    assert (HM := hz_horner_R_bound_R cs ms y Z Hrest Hy).
    assert (A : Rabs ((hz_horner_R cs x - hz_horner_R cs y) * x)
                <= hz_L ms Z * Rabs (x - y) * Z)
      by (apply b64ae_abs_mult_le; assumption).
    assert (B : Rabs (hz_horner_R cs y * (x - y)) <= hz_M ms Z * Rabs (x - y))
      by (apply b64ae_abs_mult_le; [exact HM | apply Rle_refl]).
    replace ((hz_L ms Z * Z + hz_M ms Z) * Rabs (x - y))
      with (hz_L ms Z * Rabs (x - y) * Z + hz_M ms Z * Rabs (x - y)) by ring.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The kernel theorem.                                                    *)
(* -------------------------------------------------------------------------- *)

(* One Horner step: from |p - P| <= E, |P| <= M to the next coefficient. *)
Lemma hz_step : forall (p z c : binary64) (P M E Z m : R),
  fin p = true -> fin z = true -> fin c = true ->
  Rabs (B2R p - P) <= E -> Rabs P <= M -> Rabs (B2R z) <= Z -> Rabs (B2R c) <= m ->
  0 <= Z -> 0 <= E ->
  (M + E) * Z * 2 + m + 1 <= bpow radix2 1000 ->
  fin (b64_plus (b64_mult p z) c) = true /\
  Rabs (B2R (b64_plus (b64_mult p z) c) - (P * B2R z + B2R c))
    <= Z * E + b64ae_u * ((M + E) * Z) + b64ae_e0
       + (b64ae_u * ((M + E) * Z * (1 + b64ae_u) + b64ae_e0 + m) + b64ae_e0).
Proof.
  intros p z c P M E Z m Fp Fz Fc Hp HP Hz Hc HZ HE Hsafe.
  pose proof b64ae_u_small as [Hu0 Hu1]. pose proof b64ae_e0_small as [He0 He1].
  assert (HM : 0 <= M) by (eapply Rle_trans; [apply Rabs_pos | exact HP]).
  assert (Hm : 0 <= m) by (eapply Rle_trans; [apply Rabs_pos | exact Hc]).
  assert (Hpb : Rabs (B2R p) <= M + E).
  { replace (B2R p) with ((B2R p - P) + P) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  assert (B1 : Rabs (B2R p * B2R z) <= (M + E) * Z)
    by (apply b64ae_abs_mult_le; assumption).
  assert (HMEZ : 0 <= (M + E) * Z) by (apply Rmult_le_pos; lra).
  assert (B1' : Rabs (B2R p * B2R z) <= bpow radix2 1000) by lra.
  destruct (b64ae_mult_err p z Fp Fz B1') as [Ft Et].
  set (t := b64_mult p z) in *.
  pose proof (b64ae_u_mul_le _ _ B1) as U1.
  (* |p z - P z| <= E Z *)
  assert (D : Rabs (B2R p * B2R z - P * B2R z) <= E * Z).
  { replace (B2R p * B2R z - P * B2R z) with ((B2R p - P) * B2R z) by ring.
    apply b64ae_abs_mult_le; assumption. }
  assert (Tt : Rabs (B2R t - P * B2R z)
               <= Z * E + b64ae_u * ((M + E) * Z) + b64ae_e0).
  { replace (B2R t - P * B2R z)
      with ((B2R t - B2R p * B2R z) + (B2R p * B2R z - P * B2R z)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  assert (Tb : Rabs (B2R t) <= (M + E) * Z * (1 + b64ae_u) + b64ae_e0).
  { replace (B2R t) with ((B2R t - B2R p * B2R z) + B2R p * B2R z) by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    replace ((M + E) * Z * (1 + b64ae_u)) with ((M + E) * Z + b64ae_u * ((M + E) * Z))
      by ring.
    lra. }
  assert (B2 : Rabs (B2R t + B2R c) <= (M + E) * Z * (1 + b64ae_u) + b64ae_e0 + m).
  { eapply Rle_trans; [apply Rabs_triang|]. lra. }
  assert (B2' : Rabs (B2R t + B2R c) <= bpow radix2 1000).
  { eapply Rle_trans; [exact B2|].
    assert ((M + E) * Z * (1 + b64ae_u) <= (M + E) * Z * 2)
      by (apply Rmult_le_compat_l; lra).
    lra. }
  destruct (b64ae_plus_err t c Ft Fc B2') as [Fs Es].
  pose proof (b64ae_u_mul_le _ _ B2) as U2.
  split; [exact Fs|].
  replace (B2R (b64_plus t c) - (P * B2R z + B2R c))
    with ((B2R (b64_plus t c) - (B2R t + B2R c)) + (B2R t - P * B2R z)) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

(* WITNESS {"claimId":"s1-b64-horner","topic":"numerics","lemma":"b64_horner_err","title":"Binary64 Horner evaluation of a polynomial with binary64 coefficients is finite and within the recursive bound hz_E of the same polynomial evaluated exactly at the same argument, given |z| <= Z, coefficient magnitudes and the hz_safe overflow guard (normal and subnormal results)","file":"theories-flocq/B64_Horner.v","witness":"b64_horner_err","board":"ADR-0006"} *)
Theorem b64_horner_err : forall cs ms z Z,
  hz_coeffs_ok cs ms -> fin z = true -> Rabs (B2R z) <= Z -> 0 <= Z ->
  hz_safe ms Z ->
  fin (b64_horner cs z) = true /\
  Rabs (B2R (b64_horner cs z) - hz_horner_R (map B2R cs) (B2R z)) <= hz_E ms Z.
Proof.
  intros cs ms z Z H Fz Hz HZ Hsafe.
  assert (Hnn := hz_ms_nonneg _ _ H).
  induction H as [|c m cs ms [Fc Hc] Hrest IH].
  - cbn. split; [reflexivity|]. rewrite Rminus_0_r, Rabs_R0. lra.
  - destruct Hrest as [|c' m' cs' ms' Hc'm' Hrest'].
    + cbn. split; [exact Fc|].
      replace (B2R c - (0 * B2R z + B2R c)) with 0 by ring.
      rewrite Rabs_R0. lra.
    + inversion Hnn as [|? ? Hm Hnn']. subst.
      destruct Hsafe as [Hsafe' Hguard].
      assert (Hrest : hz_coeffs_ok (c' :: cs') (m' :: ms'))
        by (constructor; assumption).
      destruct (IH Hsafe' Hnn') as [Fp Ep].
      assert (HP := hz_horner_R_bound _ _ (B2R z) Z Hrest Hz).
      assert (HE := hz_E_nonneg _ Z Hnn' HZ).
      rewrite b64_horner_cons, hz_E_cons.
      change (hz_horner_R (map B2R (c :: c' :: cs')) (B2R z))
        with (hz_horner_R (map B2R (c' :: cs')) (B2R z) * B2R z + B2R c).
      apply hz_step; assumption.
Qed.

Print Assumptions hz_E_cons_le.
Print Assumptions hz_horner_R_bound_R.
Print Assumptions hz_horner_R_lip.
Print Assumptions hz_horner_R_bound.
Print Assumptions hz_step.
Print Assumptions b64_horner_err.
