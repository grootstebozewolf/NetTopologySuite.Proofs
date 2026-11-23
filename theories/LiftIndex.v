(* ============================================================================
   NetTopologySuite.Proofs.LiftIndex
   ----------------------------------------------------------------------------
   The arithmetic steps of
   Formalism.L2.N.RankZeroOfLevelThree.rank_zero_of_row_conditions
   (mirror C:\rh, CocoSgt/riemann-hypothesis-lean @ 7cbf7a0):
   a lift index j in Icc 1 m is k+1 for k = j-1 < m, and a tail
   x >= max(x0, x1+1) gives x0 <= x and x1 < x.

   The Lean build log (C:\rh\build.log) does not reach this file.  It
   dies with exit 3221226505 (STATUS_STACK_BUFFER_OVERRUN; lines 993,
   191164) and, where `ring` fails, says to use `ring_nf` (line 9683).
   These lemmas are that normal form: `lia` and `lra`, with no instance
   search.  Stdlib `ln` / `Rpower` are not used.

   claimId: none
   No Admitted, no Axiom, no Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ============================================================================ *)
From Stdlib Require Import Arith Lia Reals Lra.

Lemma exists_fin_pred_of_icc (m j : nat) :
  (1 <= j <= m)%nat -> exists k : nat, (k < m)%nat /\ j = S k.
Proof.
  intros Hj. exists (Nat.pred j). split; lia.
Qed.

Lemma icc_zero_excluded (m : nat) : ~ (1 <= 0 <= m)%nat.
Proof. intros H. lia. Qed.

Local Open Scope R_scope.

Lemma rmax_add_one_split (a b x : R) :
  Rmax a (b + 1) <= x -> a <= x /\ b < x.
Proof.
  intros Hx. split.
  - apply Rle_trans with (Rmax a (b + 1)); [apply Rmax_l | exact Hx].
  - assert (Hb : b + 1 <= x).
    { apply Rle_trans with (Rmax a (b + 1)); [apply Rmax_r | exact Hx]. }
    lra.
Qed.

Lemma rmax_pair_split (sel xr x : R) :
  Rmax sel xr <= x -> sel <= x /\ xr <= x.
Proof.
  intros Hx. split.
  - apply Rle_trans with (Rmax sel xr); [apply Rmax_l | exact Hx].
  - apply Rle_trans with (Rmax sel xr); [apply Rmax_r | exact Hx].
Qed.

Print Assumptions exists_fin_pred_of_icc.
Print Assumptions icc_zero_excluded.
Print Assumptions rmax_add_one_split.
Print Assumptions rmax_pair_split.
