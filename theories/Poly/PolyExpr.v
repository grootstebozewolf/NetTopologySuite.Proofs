(* ============================================================================
   NTS.Proofs.Poly.PolyExpr
   ----------------------------------------------------------------------------
   Expression AST, real and rational denotations, and explicit cost conventions.
   Constants are rationals so closed instances can be decided by vm_compute over
   Q and transferred to R through [denote_Q2R].  No Admitted.

   Cost conventions (the source paper leaves its convention unstated):
     * mults_pow_naive : [Pow e n] costs  mults e + (n-1)   (repeated multiply)
     * mults_pow_sq    : [Pow e n] costs  mults e + sq_cost n (square-multiply)
     * mults_cached v  : one shared table of powers of Var v, charged once.
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import Reals Lra Ring QArith Qreals Lia.
From NTS.Proofs.Poly Require Import Horner.
Import ListNotations.
Local Open Scope nat_scope.

Inductive Expr : Type :=
  | Const : Q -> Expr
  | Var   : nat -> Expr
  | Add   : Expr -> Expr -> Expr
  | Mul   : Expr -> Expr -> Expr
  | Pow   : Expr -> nat -> Expr.

(* ---- denotations --------------------------------------------------------- *)

Fixpoint denote (e : Expr) (rho : nat -> R) : R :=
  match e with
  | Const q => Q2R q
  | Var v => rho v
  | Add a b => (denote a rho + denote b rho)%R
  | Mul a b => (denote a rho * denote b rho)%R
  | Pow a n => (denote a rho ^ n)%R
  end.

Fixpoint qpow (q : Q) (n : nat) : Q :=
  match n with O => 1%Q | S k => (q * qpow q k)%Q end.

Fixpoint denoteQ (e : Expr) (sigma : nat -> Q) : Q :=
  match e with
  | Const q => q
  | Var v => sigma v
  | Add a b => (denoteQ a sigma + denoteQ b sigma)%Q
  | Mul a b => (denoteQ a sigma * denoteQ b sigma)%Q
  | Pow a n => qpow (denoteQ a sigma) n
  end.

Lemma Q2R_qpow : forall q n, Q2R (qpow q n) = (Q2R q ^ n)%R.
Proof.
  intros q n. induction n as [|k IH]; simpl.
  - unfold Q2R. simpl. field.
  - rewrite Q2R_mult, IH. reflexivity.
Qed.

Lemma denote_Q2R : forall e sigma,
  denote e (fun v => Q2R (sigma v)) = Q2R (denoteQ e sigma).
Proof.
  induction e as [q|v|a IHa b IHb|a IHa b IHb|a IHa n]; intros sigma; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite Q2R_plus, IHa, IHb. reflexivity.
  - rewrite Q2R_mult, IHa, IHb. reflexivity.
  - rewrite Q2R_qpow, IHa. reflexivity.
Qed.

(* Decide closed equalities / disequalities by computation over Q. *)
Lemma denote_eq_by_Q : forall e1 e2 sigma,
  Qeq_bool (denoteQ e1 sigma) (denoteQ e2 sigma) = true ->
  denote e1 (fun v => Q2R (sigma v)) = denote e2 (fun v => Q2R (sigma v)).
Proof.
  intros e1 e2 sigma H. rewrite !denote_Q2R.
  apply Qeq_bool_iff in H. apply Qeq_eqR. exact H.
Qed.

Lemma denote_neq_by_Q : forall e1 e2 sigma,
  Qeq_bool (denoteQ e1 sigma) (denoteQ e2 sigma) = false ->
  denote e1 (fun v => Q2R (sigma v)) <> denote e2 (fun v => Q2R (sigma v)).
Proof.
  intros e1 e2 sigma H Heq. rewrite !denote_Q2R in Heq.
  apply Qeq_bool_neq in H. apply H. apply eqR_Qeq. exact Heq.
Qed.

(* ---- costs --------------------------------------------------------------- *)

Fixpoint adds (e : Expr) : nat :=
  match e with
  | Const _ | Var _ => 0
  | Add a b => S (adds a + adds b)
  | Mul a b => adds a + adds b
  | Pow a _ => adds a
  end.

Fixpoint mults_pow_naive (e : Expr) : nat :=
  match e with
  | Const _ | Var _ => 0
  | Add a b => mults_pow_naive a + mults_pow_naive b
  | Mul a b => S (mults_pow_naive a + mults_pow_naive b)
  | Pow a n => mults_pow_naive a + pred n
  end.

(* Multiplications of binary exponentiation x^n, n >= 1 (fuel = n suffices). *)
Fixpoint sq_cost_fuel (fuel n : nat) : nat :=
  match fuel with
  | O => 0
  | S f =>
      if Nat.leb n 1 then 0
      else if Nat.even n then S (sq_cost_fuel f (Nat.div2 n))
      else S (S (sq_cost_fuel f (Nat.div2 n)))
  end.
Definition sq_cost (n : nat) : nat := sq_cost_fuel n n.

Fixpoint mults_pow_sq (e : Expr) : nat :=
  match e with
  | Const _ | Var _ => 0
  | Add a b => mults_pow_sq a + mults_pow_sq b
  | Mul a b => S (mults_pow_sq a + mults_pow_sq b)
  | Pow a n => mults_pow_sq a + sq_cost n
  end.

(* Power-caching convention for single-variable forms: every Pow is free except
   one shared table x^2..x^m costing m-1, m the largest exponent used.  The
   Mul that applies a coefficient is still charged. *)
Fixpoint mults_nopow (e : Expr) : nat :=
  match e with
  | Const _ | Var _ => 0
  | Add a b => mults_nopow a + mults_nopow b
  | Mul a b => S (mults_nopow a + mults_nopow b)
  | Pow a _ => mults_nopow a
  end.

Fixpoint pow_max (e : Expr) : nat :=
  match e with
  | Const _ | Var _ => 0
  | Add a b | Mul a b => Nat.max (pow_max a) (pow_max b)
  | Pow a n => Nat.max n (pow_max a)
  end.

Definition mults_cached (e : Expr) : nat := mults_nopow e + pred (pow_max e).

(* ---- Horner and expanded forms as expressions ------------------------------ *)

(* a0 + x*(a1 + x*(...)) on variable index v. *)
Fixpoint horner_expr (v : nat) (c : list Q) : Expr :=
  match c with
  | [] => Const 0
  | [a] => Const a
  | a :: c' => Add (Const a) (Mul (Var v) (horner_expr v c'))
  end.

(* a_i x^i + a_{i+1} x^{i+1} + ... ; the i = 0 term is the bare constant. *)
Definition term_expr (v : nat) (a : Q) (i : nat) : Expr :=
  match i with O => Const a | _ => Mul (Const a) (Pow (Var v) i) end.

Fixpoint naive_expr (v : nat) (c : list Q) (i : nat) : Expr :=
  match c with
  | [] => Const 0
  | [a] => term_expr v a i
  | a :: c' => Add (term_expr v a i) (naive_expr v c' (S i))
  end.

Lemma horner_expr_cons : forall v a c, c <> [] ->
  horner_expr v (a :: c) = Add (Const a) (Mul (Var v) (horner_expr v c)).
Proof. intros v a [|b c'] H; [congruence|reflexivity]. Qed.

Lemma naive_expr_cons : forall v a c i, c <> [] ->
  naive_expr v (a :: c) i = Add (term_expr v a i) (naive_expr v c (S i)).
Proof. intros v a [|b c'] i H; [congruence|reflexivity]. Qed.

Lemma denote_horner_expr : forall v c rho,
  denote (horner_expr v c) rho = horner (map Q2R c) (rho v).
Proof.
  intros v c rho. induction c as [|a c IH].
  - simpl. unfold Q2R. simpl. field.
  - destruct c as [|b c'].
    + simpl. ring.
    + rewrite horner_expr_cons by discriminate.
      cbn [denote]. rewrite IH. reflexivity.
Qed.

Lemma denote_term_expr : forall v a i rho,
  denote (term_expr v a i) rho = (Q2R a * rho v ^ i)%R.
Proof. intros v a [|i] rho; simpl; ring. Qed.

Lemma denote_naive_expr : forall v c rho i,
  denote (naive_expr v c i) rho = naive (map Q2R c) (rho v) i.
Proof.
  intros v c rho. induction c as [|a c IH]; intros i.
  - simpl. unfold Q2R. simpl. field.
  - destruct c as [|b c'].
    + simpl naive_expr. rewrite denote_term_expr. simpl. ring.
    + rewrite naive_expr_cons by discriminate.
      cbn [denote]. rewrite denote_term_expr, IH.
      reflexivity.
Qed.

(* The two forms agree over R (Horner correctness, lifted to the AST). *)
Corollary horner_expr_correct : forall v c rho,
  denote (horner_expr v c) rho = denote (naive_expr v c 0) rho.
Proof.
  intros. rewrite denote_horner_expr, denote_naive_expr.
  apply horner_correct.
Qed.

(* ---- cost lemmas ----------------------------------------------------------- *)

Lemma horner_mults : forall v c,
  mults_pow_naive (horner_expr v c) = pred (length c)
  /\ mults_pow_sq (horner_expr v c) = pred (length c)
  /\ adds (horner_expr v c) = pred (length c).
Proof.
  intros v c. induction c as [|a c IH]; [repeat split|].
  destruct c as [|b c'].
  - repeat split.
  - rewrite horner_expr_cons by discriminate.
    destruct IH as [H1 [H2 H3]].
    cbn [mults_pow_naive mults_pow_sq adds length] in *.
    repeat split; lia.
Qed.

Lemma term_mults_naive : forall v a i, mults_pow_naive (term_expr v a i) = i.
Proof. intros v a [|i]; reflexivity. Qed.

Lemma naive_mults_aux : forall v c i,
  2 * mults_pow_naive (naive_expr v c i) + length c = length c * (2 * i + length c).
Proof.
  intros v c. induction c as [|a c IH]; intros i; [simpl; lia|].
  destruct c as [|b c'].
  - simpl naive_expr. rewrite term_mults_naive. simpl length. lia.
  - rewrite naive_expr_cons by discriminate.
    cbn [mults_pow_naive]. rewrite term_mults_naive.
    pose proof (IH (S i)) as H. cbn [length] in *. nia.
Qed.

(* n(n+1)/2 multiplications for a degree-n expanded polynomial (pow recompute). *)
Lemma naive_mults : forall v c n, length c = S n ->
  2 * mults_pow_naive (naive_expr v c 0) = n * (n + 1).
Proof.
  intros v c n Hl. pose proof (naive_mults_aux v c 0) as H.
  rewrite Hl in H. nia.
Qed.

Lemma naive_pow_max : forall v c i, 1 <= i -> c <> [] ->
  pow_max (naive_expr v c i) = i + length c - 1.
Proof.
  intros v c. induction c as [|a c IH]; intros i Hi Hc; [congruence|].
  destruct c as [|b c'].
  - destruct i; [lia|]. simpl. lia.
  - rewrite naive_expr_cons by discriminate.
    cbn [pow_max]. rewrite IH by (try lia; discriminate).
    destruct i; [lia|]. cbn [term_expr pow_max length] in *. lia.
Qed.

Lemma naive_nopow : forall v c i, 1 <= i ->
  mults_nopow (naive_expr v c i) = length c.
Proof.
  intros v c. induction c as [|a c IH]; intros i Hi; [reflexivity|].
  destruct c as [|b c'].
  - destruct i; [lia|]. reflexivity.
  - rewrite naive_expr_cons by discriminate.
    cbn [mults_nopow]. rewrite IH by lia.
    destruct i; [lia|]. cbn [term_expr mults_nopow length]. lia.
Qed.

(* 2n-1 multiplications with a shared power table (n >= 1). *)
Lemma naive_mults_cached : forall v a c, c <> [] ->
  mults_cached (naive_expr v (a :: c) 0) = 2 * length c - 1.
Proof.
  intros v a c Hc. rewrite naive_expr_cons by exact Hc.
  unfold mults_cached. cbn [mults_nopow pow_max term_expr].
  rewrite naive_nopow by lia. rewrite naive_pow_max by (try lia; exact Hc).
  destruct c; [congruence|]. cbn [length]. lia.
Qed.

(* Horner never costs more than the expanded form (pow-naive convention). *)
Theorem horner_le_naive : forall v c n, length c = S n ->
  mults_pow_naive (horner_expr v c) <= mults_pow_naive (naive_expr v c 0).
Proof.
  intros v c n Hl.
  destruct (horner_mults v c) as [H1 _]. rewrite H1, Hl.
  pose proof (naive_mults v c n Hl). simpl. nia.
Qed.

Print Assumptions naive_mults.
Print Assumptions naive_mults_cached.
Print Assumptions horner_le_naive.
