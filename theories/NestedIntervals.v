(* ============================================================================
   NetTopologySuite.Proofs.NestedIntervals
   ----------------------------------------------------------------------------
   Nested-interval completeness of R WITHOUT ClassicalDedekindReals.sig_not_dec.

   Stdlib's least-upper-bound `completeness` (and everything built on it:
   `R_complete`, `growing_cv`, sqrt, PI, sin, cos, exp, ln) is proved through
   `CR_sig_lub ... sig_forall_dec sig_not_dec`, so every corpus theorem that
   takes a supremum inherits `sig_not_dec`.  A shrinking nested interval does
   not need a supremum: its left ends are a Cauchy sequence, and the
   constructive Cauchy reals have an axiom-free limit (`Rcauchy_complete`).
   Moving to CReal through `Rrepr` and back through `Rabst` costs only
   `sig_forall_dec` and `functional_extensionality_dep`.

     nested_intervals_limit : a increasing, b decreasing, a n <= b n, and
                              b N - a N eventually below every e > 0
                              -> { c | forall n, a n <= c <= b n }.

   Consumers: JCTParityTransport.invariant_transport_along_path (bisection
   instead of a supremum).

   Pure-R; sig_forall_dec + functional_extensionality_dep only (no sig_not_dec).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia QArith ConstructiveEpsilon.
From Stdlib Require Import ConstructiveCauchyReals ConstructiveCauchyRealsMult
  ConstructiveCauchyAbs ConstructiveRcomplete.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The CReal image of 1/p.                                                *)
(* -------------------------------------------------------------------------- *)

Lemma Rabst_inv_pos : forall p : positive,
  Rabst (inject_Q (1 # p)) = / IPR p.
Proof.
  intro p.
  assert (Hp : 0 < IPR p).
  { pose proof (IZR_lt 0 (Z.pos p) (Pos2Z.is_pos p)) as H. exact H. }
  assert (E : IPR p * Rabst (inject_Q (1 # p)) = 1).
  { apply Rquot1.
    rewrite Rrepr_mult, Rquot2, Rrepr_IPR, Rrepr_1.
    unfold inject_Z. rewrite <- inject_Q_mult.
    apply inject_Q_morph. unfold Qeq; simpl; lia. }
  apply (Rmult_eq_reg_l (IPR p)); [ | lra ].
  rewrite E. field. lra.
Qed.

Lemma Rrepr_inv_pos : forall p : positive,
  CRealEq (Rrepr (/ IPR p)) (inject_Q (1 # p)).
Proof.
  intro p. rewrite <- Rabst_inv_pos. apply Rquot2.
Qed.

Lemma inv_pos_lt : forall e, 0 < e -> exists p : positive, / IPR p < e.
Proof.
  intros e He.
  destruct (archimed (/ e)) as [Hup _].
  assert (Hie : 0 < / e) by (apply Rinv_0_lt_compat; exact He).
  assert (Hz : (0 < up (/ e))%Z) by (apply lt_IZR; lra).
  destruct (up (/ e)) as [|p|p] eqn:Eu; try lia.
  exists p.
  assert (Hp : / e < IPR p) by exact Hup.
  assert (HP : 0 < IPR p) by lra.
  apply (Rmult_lt_reg_l (IPR p)); [ exact HP | ].
  rewrite Rinv_r by lra.
  apply (Rmult_lt_reg_r (/ e)); [ exact Hie | ].
  rewrite Rmult_1_l, Rmult_assoc, Rinv_r by lra. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Monotone sequences, informative witnesses.                             *)
(* -------------------------------------------------------------------------- *)

Lemma incr_le : forall (a : nat -> R), (forall n, a n <= a (S n)) ->
  forall n m, (n <= m)%nat -> a n <= a m.
Proof.
  intros a Ha n m Hnm. induction Hnm as [| m _ IH]; [ lra | ].
  pose proof (Ha m). lra.
Qed.

Lemma decr_le : forall (b : nat -> R), (forall n, b (S n) <= b n) ->
  forall n m, (n <= m)%nat -> b m <= b n.
Proof.
  intros b Hb n m Hnm. induction Hnm as [| m _ IH]; [ lra | ].
  pose proof (Hb m). lra.
Qed.

(* `exists N, w N < e` made informative: Rlt is decidable and N ranges over
   nat (ConstructiveEpsilon, axiom-free). *)
Lemma first_below : forall (w : nat -> R) e,
  (exists N, w N < e) -> { N : nat | w N < e }.
Proof.
  intros w e H.
  apply constructive_indefinite_ground_description_nat; [ | exact H ].
  intro n. destruct (Rlt_dec (w n) e) as [L | L]; [ left | right ]; exact L.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Nested intervals have a common point.                                  *)
(* -------------------------------------------------------------------------- *)

Section Nested.

Variables a b : nat -> R.
Hypothesis Ha : forall n, a n <= a (S n).
Hypothesis Hb : forall n, b (S n) <= b n.
Hypothesis Hab : forall n, a n <= b n.
Hypothesis Hw : forall e, 0 < e -> exists N, b N - a N < e.

Let Hin : forall N i, (N <= i)%nat -> a N <= a i <= b N.
Proof.
  intros N i Hi. split; [ apply incr_le; assumption | ].
  pose proof (Hab i). pose proof (decr_le b Hb N i Hi). lra.
Qed.

Let Hcau_R : forall p : positive, { N : nat | forall i j, (N <= i)%nat -> (N <= j)%nat ->
  - / IPR p <= a i - a j <= / IPR p }.
Proof.
  intro p.
  assert (Hp : 0 < / IPR p).
  { apply Rinv_0_lt_compat. exact (IZR_lt 0 (Z.pos p) (Pos2Z.is_pos p)). }
  destruct (first_below (fun N => b N - a N) (/ IPR p) (Hw _ Hp)) as [N HN].
  exists N. intros i j Hi Hj.
  pose proof (Hin N i Hi). pose proof (Hin N j Hj). cbn in HN. lra.
Qed.

Let Hcau : Un_cauchy_mod (fun n => Rrepr (a n)).
Proof.
  intro p. destruct (Hcau_R p) as [N HN]. exists N. intros i j Hi Hj.
  destruct (HN i j Hi Hj) as [Lo Hi'].
  apply CReal_abs_le. split.
  - apply Rrepr_le in Lo. rewrite Rrepr_opp, Rrepr_minus, Rrepr_inv_pos in Lo.
    exact Lo.
  - apply Rrepr_le in Hi'. rewrite Rrepr_minus, Rrepr_inv_pos in Hi'.
    exact Hi'.
Qed.

Let Hcv : forall (l : CReal), seq_cv (fun n => Rrepr (a n)) l ->
  forall p : positive, exists N, forall i, (N <= i)%nat ->
    - / IPR p <= a i - Rabst l <= / IPR p.
Proof.
  intros l Hl p. destruct (Hl p) as [N HN]. exists N. intros i Hi.
  destruct (CReal_abs_def2 _ _ (HN i Hi)) as [U L]. split.
  - apply Rrepr_le. rewrite Rrepr_opp, Rrepr_minus, Rrepr_inv_pos, Rquot2.
    exact L.
  - apply Rrepr_le. rewrite Rrepr_minus, Rrepr_inv_pos, Rquot2. exact U.
Qed.

Theorem nested_intervals_limit : { c : R | forall n, a n <= c <= b n }.
Proof.
  destruct (Rcauchy_complete _ Hcau) as [l Hl].
  exists (Rabst l). intro n. split.
  - (* a n <= c: otherwise a i stays above a n for i >= n, too far from c. *)
    destruct (Rle_lt_dec (a n) (Rabst l)) as [L | L]; [ exact L | exfalso ].
    destruct (inv_pos_lt (a n - Rabst l) ltac:(lra)) as [p Hp].
    destruct (Hcv l Hl p) as [N HN].
    destruct (HN (max N n) (Nat.le_max_l N n)) as [_ U].
    pose proof (incr_le a Ha n (max N n) (Nat.le_max_r N n)). lra.
  - (* c <= b n: a i <= b n for every i, and a i gets close to c. *)
    destruct (Rle_lt_dec (Rabst l) (b n)) as [L | L]; [ exact L | exfalso ].
    destruct (inv_pos_lt (Rabst l - b n) ltac:(lra)) as [p Hp].
    destruct (Hcv l Hl p) as [N HN].
    destruct (HN (max N n) (Nat.le_max_l N n)) as [Lo _].
    pose proof (Hin n (max N n) (Nat.le_max_r N n)). lra.
Qed.

End Nested.

Print Assumptions nested_intervals_limit.
