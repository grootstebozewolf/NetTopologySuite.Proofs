(* ============================================================================
   NTS.Proofs.Poly.Horner
   ----------------------------------------------------------------------------
   Univariate core: Horner's scheme equals the monomial (power-sum) form over R.
   Coefficients are ascending: [a0; a1; ...; an] encodes a0 + a1 x + ... + an x^n.
   Pure real arithmetic; no Flocq, no Admitted.
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import Reals Lra Ring.
Import ListNotations.
Local Open Scope R_scope.

(* Nested form:  a0 + x*(a1 + x*(a2 + ...)). *)
Fixpoint horner (c : list R) (x : R) : R :=
  match c with
  | [] => 0
  | a :: c' => a + x * horner c' x
  end.

(* Expanded form, ascending powers starting at exponent i. *)
Fixpoint naive (c : list R) (x : R) (i : nat) : R :=
  match c with
  | [] => 0
  | a :: c' => a * x ^ i + naive c' x (S i)
  end.

Lemma naive_shift : forall c x i, naive c x i = x ^ i * horner c x.
Proof.
  induction c as [|a c IH]; intros x i; simpl.
  - ring.
  - rewrite IH, <- tech_pow_Rmult. ring.
Qed.

Corollary horner_correct : forall c x, horner c x = naive c x 0.
Proof. intros c x. rewrite naive_shift, pow_O. ring. Qed.

(* Reusable linearity facts (used by MultiHorner). *)
Lemma horner_app_scale : forall c x k,
  horner (map (Rmult k) c) x = k * horner c x.
Proof.
  induction c as [|a c IH]; intros x k; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma horner_length_0 : forall x, horner [] x = 0.
Proof. reflexivity. Qed.

Print Assumptions horner_correct.
