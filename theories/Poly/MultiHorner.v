(* ============================================================================
   NTS.Proofs.Poly.MultiHorner
   ----------------------------------------------------------------------------
   [factor v e] collects the monomials of [e] by degree in variable [v] and nests
   them Horner-style.  Coefficients are Expr's in the other variables.
   [factor_sound] is unconditional.  The cost story is split honestly:
     * [factor_cost_le_expanded]: Horner-nesting an already expanded univariate
       polynomial never costs more (from PolyExpr).
     * [factor_cost_not_monotone]: raw [factor] is NOT cost-monotone on all e,
       because it does no constant folding -- a closed counterexample.
   No Admitted.
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import Reals Lra Ring QArith Qreals Lia.
From NTS.Proofs.Poly Require Import Horner PolyExpr.
Import ListNotations.
Local Open Scope nat_scope.

(* A "coefficient list" p = [c0; c1; ...] denotes c0 + x c1 + x^2 c2 ... *)
Definition peval (rho : nat -> R) (x : R) (p : list Expr) : R :=
  horner (map (fun c => denote c rho) p) x.

Fixpoint padd (p q : list Expr) : list Expr :=
  match p, q with
  | [], q => q
  | p, [] => p
  | a :: p', b :: q' => Add a b :: padd p' q'
  end.

Fixpoint pmul (p q : list Expr) : list Expr :=
  match p with
  | [] => []
  | a :: p' => padd (map (Mul a) q) (Const 0 :: pmul p' q)
  end.

Fixpoint ppow (p : list Expr) (n : nat) : list Expr :=
  match n with
  | O => [Const 1]
  | S k => pmul p (ppow p k)
  end.

Lemma peval_nil : forall rho x, peval rho x [] = 0%R.
Proof. reflexivity. Qed.

Lemma peval_cons : forall rho x a p,
  peval rho x (a :: p) = (denote a rho + x * peval rho x p)%R.
Proof. reflexivity. Qed.

Lemma peval_padd : forall rho x p q,
  peval rho x (padd p q) = (peval rho x p + peval rho x q)%R.
Proof.
  intros rho x p. induction p as [|a p IH]; intros q.
  - simpl. unfold peval at 2. simpl. ring.
  - destruct q as [|b q].
    + simpl padd. unfold peval at 3. simpl horner. ring.
    + simpl padd. rewrite !peval_cons, IH. cbn [denote]. ring.
Qed.

Lemma peval_scale : forall rho x a q,
  peval rho x (map (Mul a) q) = (denote a rho * peval rho x q)%R.
Proof.
  intros rho x a q. induction q as [|b q IH].
  - simpl. unfold peval. simpl. ring.
  - simpl map. rewrite !peval_cons, IH. cbn [denote]. ring.
Qed.

Lemma peval_pmul : forall rho x p q,
  peval rho x (pmul p q) = (peval rho x p * peval rho x q)%R.
Proof.
  intros rho x p q. induction p as [|a p IH].
  - simpl. unfold peval. simpl. ring.
  - simpl pmul. rewrite peval_padd, peval_scale, !peval_cons, IH. cbn [denote].
    unfold Q2R. simpl. field.
Qed.

Lemma peval_ppow : forall rho x p n,
  peval rho x (ppow p n) = (peval rho x p ^ n)%R.
Proof.
  intros rho x p n. induction n as [|k IH].
  - simpl. rewrite peval_cons. cbn [denote]. unfold peval. simpl.
    unfold Q2R. simpl. field.
  - simpl ppow. rewrite peval_pmul, IH. simpl. reflexivity.
Qed.

(* Coefficient list of e as a polynomial in variable v. *)
Fixpoint coeffs (v : nat) (e : Expr) : list Expr :=
  match e with
  | Const q => [Const q]
  | Var w => if Nat.eqb w v then [Const 0; Const 1] else [Var w]
  | Add a b => padd (coeffs v a) (coeffs v b)
  | Mul a b => pmul (coeffs v a) (coeffs v b)
  | Pow a n => ppow (coeffs v a) n
  end.

(* Nest coefficients: c0 + v*(c1 + v*(...)). *)
Fixpoint nest (v : nat) (p : list Expr) : Expr :=
  match p with
  | [] => Const 0
  | [c] => c
  | c :: p' => Add c (Mul (Var v) (nest v p'))
  end.

Definition factor (v : nat) (e : Expr) : Expr := nest v (coeffs v e).

Lemma nest_cons : forall v c p, p <> [] ->
  nest v (c :: p) = Add c (Mul (Var v) (nest v p)).
Proof. intros v c [|d p'] H; [congruence|reflexivity]. Qed.

Lemma denote_nest : forall v p rho, denote (nest v p) rho = peval rho (rho v) p.
Proof.
  intros v p rho. induction p as [|c p IH].
  - simpl. unfold peval. simpl. unfold Q2R. simpl. field.
  - destruct p as [|d p'].
    + simpl nest. unfold peval. simpl. ring.
    + rewrite nest_cons by discriminate. cbn [denote]. rewrite IH, peval_cons.
      reflexivity.
Qed.

Lemma peval_coeffs : forall v e rho,
  peval rho (rho v) (coeffs v e) = denote e rho.
Proof.
  intros v e rho. induction e as [q|w|a IHa b IHb|a IHa b IHb|a IHa n]; cbn [coeffs denote].
  - unfold peval. simpl. ring.
  - destruct (Nat.eqb w v) eqn:E.
    + apply Nat.eqb_eq in E. subst w. unfold peval. simpl. unfold Q2R. simpl. field.
    + unfold peval. simpl. ring.
  - rewrite peval_padd, IHa, IHb. reflexivity.
  - rewrite peval_pmul, IHa, IHb. reflexivity.
  - rewrite peval_ppow, IHa. reflexivity.
Qed.

Theorem factor_sound : forall v e rho, denote (factor v e) rho = denote e rho.
Proof.
  intros v e rho. unfold factor. rewrite denote_nest. apply peval_coeffs.
Qed.

(* ---- cost ------------------------------------------------------------------ *)

(* Horner-nesting an already expanded univariate polynomial is never costlier. *)
Corollary factor_cost_le_expanded : forall v c n, length c = S n ->
  mults_pow_naive (horner_expr v c) <= mults_pow_naive (naive_expr v c 0).
Proof. exact horner_le_naive. Qed.

(* Raw [factor] is not cost-monotone: no constant folding.  e = (v + 1)^2 costs
   1 multiplication as written; its factored form costs more. *)
Definition cex_expr : Expr := Pow (Add (Var 0) (Const 1)) 2.

Lemma factor_cost_not_monotone :
  mults_pow_naive cex_expr < mults_pow_naive (factor 0 cex_expr).
Proof. vm_compute. lia. Qed.

(* ... while the semantics is untouched, so only the cost claim needs the
   hypothesis.  Conditional form, as a Section hypothesis. *)
Section ConditionalCost.
  Variable v : nat.
  Variable e : Expr.
  Hypothesis H_no_fold_loss : mults_pow_naive (factor v e) <= mults_pow_naive e.

  Theorem factor_cost_le : forall rho,
    denote (factor v e) rho = denote e rho
    /\ mults_pow_naive (factor v e) <= mults_pow_naive e.
  Proof. intros rho. split; [apply factor_sound | exact H_no_fold_loss]. Qed.
End ConditionalCost.

Print Assumptions factor_sound.
Print Assumptions factor_cost_not_monotone.
