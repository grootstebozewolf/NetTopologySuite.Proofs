(* ============================================================================
   NetTopologySuite.Proofs.LexOrder
   ----------------------------------------------------------------------------
   The lexicographic order on `Point`: order by x, breaking ties by y.

   NTS's `Coordinate.CompareTo` uses exactly this comparison.  Establishing
   the standard properties (irreflexivity, transitivity, asymmetry,
   antisymmetry of the non-strict form, totality) lets every downstream
   sorting / indexing / hashing proof cite a named result.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Strict lexicographic order: smaller x wins, ties broken by smaller y.     *)
(* -------------------------------------------------------------------------- *)

Definition lt_lex (p q : Point) : Prop :=
  px p < px q \/ (px p = px q /\ py p < py q).

Definition le_lex (p q : Point) : Prop :=
  lt_lex p q \/ (px p = px q /\ py p = py q).

(* -------------------------------------------------------------------------- *)
(* Irreflexivity, asymmetry, and transitivity of the strict order.           *)
(* -------------------------------------------------------------------------- *)

Lemma lt_lex_irrefl : forall p, ~ lt_lex p p.
Proof.
  intros p [H | [_ H]]; lra.
Qed.

Lemma lt_lex_asym : forall p q, lt_lex p q -> ~ lt_lex q p.
Proof.
  intros p q Hpq Hqp.
  destruct Hpq as [Hpq | [Hpq1 Hpq2]];
  destruct Hqp as [Hqp | [Hqp1 Hqp2]];
  lra.
Qed.

Lemma lt_lex_trans : forall p q r,
  lt_lex p q -> lt_lex q r -> lt_lex p r.
Proof.
  intros p q r Hpq Hqr.
  destruct Hpq as [Hpq | [Hpq1 Hpq2]];
  destruct Hqr as [Hqr | [Hqr1 Hqr2]].
  - left. lra.
  - left. lra.
  - left. lra.
  - right. split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Non-strict order: reflexivity, antisymmetry (up to coordinate equality),  *)
(* transitivity.                                                              *)
(* -------------------------------------------------------------------------- *)

Lemma le_lex_refl : forall p, le_lex p p.
Proof. intros p. right. split; reflexivity. Qed.

Lemma le_lex_antisym : forall p q,
  le_lex p q -> le_lex q p -> px p = px q /\ py p = py q.
Proof.
  intros p q [Hpq | [Hpq1 Hpq2]] [Hqp | [Hqp1 Hqp2]].
  - exfalso. apply (lt_lex_asym p q Hpq Hqp).
  - destruct Hpq as [Hpq | [Hpq1 Hpq2]]; lra.
  - destruct Hqp as [Hqp | [Hqp1 Hqp2]]; lra.
  - split; lra.
Qed.

Lemma le_lex_trans : forall p q r,
  le_lex p q -> le_lex q r -> le_lex p r.
Proof.
  intros p q r [Hpq | Heqpq] [Hqr | Heqqr].
  - left. apply (lt_lex_trans p q r Hpq Hqr).
  - left. destruct Heqqr as [Hqr1 Hqr2]. destruct Hpq as [Hpq | [Hpq1 Hpq2]].
    + left. lra.
    + right. split; lra.
  - left. destruct Heqpq as [Hpq1 Hpq2]. destruct Hqr as [Hqr | [Hqr1 Hqr2]].
    + left. lra.
    + right. split; lra.
  - right. destruct Heqpq as [H1 H2]. destruct Heqqr as [H3 H4]. split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Totality: for any two points, either p <= q or q <= p (or both, when      *)
(* they are coordinate-equal).  Uses classical decidability of <= on the     *)
(* reals.                                                                     *)
(* -------------------------------------------------------------------------- *)

Lemma le_lex_total : forall p q, le_lex p q \/ le_lex q p.
Proof.
  intros p q.
  destruct (Rtotal_order (px p) (px q)) as [Hxlt | [Hxeq | Hxgt]].
  - left. left. left. exact Hxlt.
  - destruct (Rtotal_order (py p) (py q)) as [Hylt | [Hyeq | Hygt]].
    + left. left. right. split; assumption.
    + left. right. split; assumption.
    + right. left. right. split; [lra | exact Hygt].
  - right. left. left. exact Hxgt.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions lt_lex_trans.
Print Assumptions le_lex_total.
