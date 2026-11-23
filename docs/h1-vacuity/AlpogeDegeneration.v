(* AlpogeDegeneration.v -- arithmetic of the degeneration mains.

   Lean (mirror C:\rh, CocoSgt/riemann-hypothesis-lean @ 7cbf7a0),
   folder Development/AbelianVarietyTheory/Proofs/DegenerationProofs.
   Statement files and single-use helpers are folded into the mains.
   The calculations those proofs perform are theories/DegenerationArith.v.
   Scheme elaborations stay hypotheses of the external development;
   this probe does not give them inhabitants.

   Within docs/axiom-allowlist.txt.  No Admitted.  Not a proof of RH.
   Verdict on the external development: PASS-STATIC / PENDING.

   Evidence for docs/attacks/2026-11-23-alpoge-degeneration.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Cursor Grok 4.7
*)
From Stdlib Require Import Reals Lra Lia ZArith List.
From NTS.Proofs Require Import DegenerationArith.
Import ListNotations.
Local Open Scope R_scope.

(* IsThetaPtDown.lean:62 and the ring rewrite at line 50. *)

Lemma theta_down_odd_and_sq (n m : nat) :
  Nat.Odd (n * m)%nat ->
  Nat.Odd m /\ ((n * m) ^ 2 = n * (m ^ 2) * n)%nat.
Proof.
  intros Ho. split.
  - exact (proj2 (proj1 (odd_mul_iff n m) Ho)).
  - apply nm_sq_split.
Qed.

Lemma odd_three_five : Nat.Odd 3%nat /\ Nat.Odd 5%nat.
Proof.
  exact (proj1 (odd_mul_iff 3%nat 5%nat) (ex_intro _ 7%nat eq_refl)).
Qed.

Lemma odd_six_premise_fails : ~ Nat.Odd (3 * 2)%nat.
Proof. intros [k Hk]. lia. Qed.

(* WeilPairingLabelledTorsionUniformTest.lean:16 and
   ThetaSystemSumCharacterOrthogonalEqZero.lean:30 (the `by ring` order). *)

Lemma weil_square_order (r N : nat) :
  (0 < r)%nat -> (0 < N)%nat ->
  (((r * N) ^ 2) / (r * N) = r * N)%nat /\ ((r * N) ^ 2 <> 0)%nat.
Proof.
  intros Hr HN. split.
  - apply sq_div_self. lia.
  - apply sq_mul_ne_zero; assumption.
Qed.

Lemma uniform_exponent_zero (x : R) : x ^ 0 = 1.
Proof. reflexivity. Qed.

(* CharSumInv.charSum_inv, the cancellation after the shift.
   A two-element sign character is the whole identity at order 2.
   Dropping phi <> 1 keeps a nonzero sum. *)

Lemma sign_pair_cancels :
  let S := rsum (1 :: (-1) :: nil) in (-1) * S = S /\ -1 <> 1 /\ S = 0.
Proof.
  cbn. split; [lra |]. split; lra.
Qed.

Lemma trivial_pair_is_card : rsum (repeat 1 2) = INR 2.
Proof. apply rsum_ones. Qed.

Lemma one_shift_keeps_two : 1 * 2 = 2 /\ 2 <> 0.
Proof. split; lra. Qed.

(* prod_cubN_wS, the nlinarith on sum_range_id.  Odd is load-bearing:
   the same half-formula at k = 2 is not the sum. *)

Lemma half_sum_at_three :
  (sum_below 3 = ((3 - 1) / 2) * 3)%nat.
Proof.
  apply sum_range_odd_half. exists 1%nat. reflexivity.
Qed.

Lemma half_sum_at_two_fails :
  (sum_below 2 <> ((2 - 1) / 2) * 2)%nat.
Proof.
  cbn. discriminate.
Qed.

(* exists_linear.  rho^2 evaluates as -d only under the relation. *)

Lemma quad_rho_sq (zeta rho : R) (d : Z) :
  rho * rho = IZR (Z.opp d) ->
  qeval (Qvar true (Qvar true (Qconst 1))) zeta rho = IZR (Z.opp d).
Proof.
  intros H. cbn.
  rewrite <- (Rmult_assoc rho rho (IZR 1)).
  rewrite H.
  rewrite <- (mult_IZR (Z.opp d) 1%Z).
  rewrite Z.mul_1_r. reflexivity.
Qed.

Lemma quad_rho_sq_needs_relation :
  qeval (Qvar true (Qvar true (Qconst 1))) 0 1 = 1 /\ IZR (Z.opp 3) <> 1.
Proof.
  split.
  - cbn. ring.
  - rewrite opp_IZR. cbn. lra.
Qed.

(* norm_unit.  The two bounds <= 1 are load-bearing: 1/2 * 2 = 1 and 1/2 <> 1. *)

Lemma unit_norm_at_one : let a := 1 in a * a = 1 /\ a = 1.
Proof. split; lra. Qed.

Lemma unit_norm_half_escapes : (1 / 2) * 2 = 1 /\ 1 / 2 <> 1.
Proof. split; lra. Qed.

(* nonempty_equiv_of_basis. *)

Lemma root_iter_at_neg_one : ((-1) ^ 3) ^ 2 = 1.
Proof.
  apply pow_iter_of_root. cbn. lra.
Qed.

(* wQ_eq, the odd chart index. *)

Lemma odd_index_at_four : ((2 * 4 + 1 - 1) / 2 = 4)%nat.
Proof. apply odd_pred_half. Qed.

(* exists_prime_unit.  5 does not divide 2, and 5 is not 2. *)

Lemma prime_shift_at_five :
  (5 <> 2)%nat /\ ~ Nat.divide 5 2.
Proof.
  split.
  - apply (shift_ne_two 5 2). lia.
  - apply no_dvd_from_shift. lia. lia.
Qed.

(* isProper_of_unit_in_cosets, the norm-1 step, and the field cancel. *)

Lemma abs_neg_one_nonzero : Rabs (-1) = 1 /\ -1 <> 0.
Proof.
  split.
  - unfold Rabs. destruct (Rcase_abs (-1)) as [Hlt | Hge].
    + lra.
    + exfalso. lra.
  - lra.
Qed.

Lemma div_cancel_at_three : (6 / 3) * 3 = 6.
Proof. apply div_mul_cancel_r. lra. Qed.

Lemma div_cancel_needs_nonzero : (1 / 0) * 0 = 0 /\ 0 <> 1.
Proof.
  split.
  - rewrite Rmult_0_r. reflexivity.
  - lra.
Qed.
