(* ============================================================================
   NetTopologySuite.Proofs.NurbsSumBridge
   ----------------------------------------------------------------------------
   Glue the Cox–de Boor prefix sum to the Bernstein sum, without editing
   NurbsBasis or BernsteinBasis:

     sum_first f (S p) = sum_f_R0 f p.

   sum_first adds the terms f 0 .. f (n-1).  sum_f_R0 adds f 0 .. f n.
   One successor lines them up.  NurbsBezierSpan is the consumer.

   No Admitted. No Axiom. No Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lia.
From NTS.Proofs Require Import NurbsBasis.
Local Open Scope R_scope.

Lemma sum_first_sum_f_R0 : forall (f : nat -> R) (p : nat),
  sum_first f (S p) = sum_f_R0 f p.
Proof.
  intros f p. induction p as [|p IH].
  - simpl. ring.
  - transitivity (sum_first f (S p) + f (S p)).
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

Print Assumptions sum_first_sum_f_R0.
