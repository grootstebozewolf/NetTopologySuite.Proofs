(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Expansion
   ----------------------------------------------------------------------------
   Bounded-length expansion arithmetic for Stage D of `orient2d`.

   First piece of Stage D work that goes BEYOND lifting Pff2Flocq.  An
   expansion is a sequence of binary64 values representing an exact sum;
   for Stage D we need lengths up to 16 (Shewchuk's `orient2dexact`).
   General expansion arithmetic with `compress` / renormalization is the
   multi-month engagement BJMP 2017 published -- we skip that here in
   favor of fixed-length tuples that bypass renormalization entirely.

   This file ships the data structure + non-overlap predicate +
   foundational sum/sign lemmas.  The straight-line composition into
   `b64_orient2d_exact` is a follow-up slice.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.
From Stdlib Require Import List.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq  Require Import Validate_binary64.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Expansion as a list of binary64 values.                                    *)
(*                                                                            *)
(* DESIGN CHOICE: list-of-binary64 vs fixed-length tuple.                    *)
(*                                                                            *)
(* The scout's recommendation: use fixed-length tuples (Record b64_expansion16)
   to avoid the renormalization complexity that drives general expansion
   arithmetic to multi-month proof engagements.                              *)
(*                                                                            *)
(* But for the foundational lemmas (sum, non-overlap structural properties),
   `list binary64` is cleaner: structural induction over the list gives
   us `sum_R nil = 0`, `sum_R (x :: xs) = B2R x + sum_R xs`, etc.            *)
(*                                                                            *)
(* We use `list binary64` for the abstract layer + define a length-bounded
   subtype for Stage D's actual use.  Best of both worlds.                   *)
(* -------------------------------------------------------------------------- *)

Definition b64_expansion : Type := list binary64.

(* Real-valued sum of an expansion: B2R of each component, summed.           *)
Fixpoint expansion_R (e : b64_expansion) : R :=
  match e with
  | nil => 0
  | x :: xs => Binary.B2R prec emax x + expansion_R xs
  end.

(* All components are finite (no NaN, no Inf).                               *)
Fixpoint expansion_finite (e : b64_expansion) : Prop :=
  match e with
  | nil => True
  | x :: xs => Binary.is_finite prec emax x = true /\ expansion_finite xs
  end.

(* -------------------------------------------------------------------------- *)
(* Non-overlapping predicate (Shewchuk Def 2.4, simplified for binary64).    *)
(*                                                                            *)
(* Two binary64 values are non-overlapping when the lower-magnitude one is   *)
(* significantly smaller than the ulp of the higher-magnitude one.  For a    *)
(* fixed-length expansion of length n, the non-overlap chain gives us       *)
(* (n - 1) pairwise constraints, which compose to bound the total magnitude *)
(* spread.                                                                   *)
(*                                                                            *)
(* For Stage D's bounded form, we use a SIMPLIFIED definition: the          *)
(* sequence is strictly magnitude-decreasing, with each successor at most   *)
(* ulp(predecessor) in magnitude.  This is the "strongly non-overlapping"   *)
(* form, slightly stricter than Shewchuk's general definition but matches   *)
(* what TwoSum / Dekker produce by construction.                            *)
(* -------------------------------------------------------------------------- *)

Definition strict_succ_b64 (a b : binary64) : Prop :=
  Rabs (Binary.B2R prec emax b) <=
    ulp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax a) / 2.

Fixpoint nonoverlap_strict (e : b64_expansion) : Prop :=
  match e with
  | nil => True
  | _ :: nil => True
  | a :: (b :: _) as rest => strict_succ_b64 a b /\ nonoverlap_strict rest
  end.

(* -------------------------------------------------------------------------- *)
(* Foundational properties: B2R sum of the empty / singleton / cons cases.   *)
(* These are the structural lemmas a fixed-length composition needs.        *)
(* -------------------------------------------------------------------------- *)

Lemma expansion_R_nil : expansion_R nil = 0.
Proof. reflexivity. Qed.

Lemma expansion_R_singleton :
  forall x : binary64,
    expansion_R (x :: nil) = Binary.B2R prec emax x.
Proof. intros x. simpl. lra. Qed.

Lemma expansion_R_cons :
  forall (x : binary64) (xs : b64_expansion),
    expansion_R (x :: xs) = Binary.B2R prec emax x + expansion_R xs.
Proof. reflexivity. Qed.

Lemma expansion_finite_cons :
  forall (x : binary64) (xs : b64_expansion),
    expansion_finite (x :: xs) <->
    (Binary.is_finite prec emax x = true /\ expansion_finite xs).
Proof. intros x xs; simpl; tauto. Qed.

(* -------------------------------------------------------------------------- *)
(* Sign of an expansion: defined as the sign of the leading non-zero term.   *)
(*                                                                            *)
(* This is the KEY operation for Stage D: after building the exact expansion *)
(* for the determinant, the sign tells us the orientation of the triangle.   *)
(*                                                                            *)
(* Under the non-overlap invariant, the leading non-zero component dominates *)
(* the sum: |sum| >= |leading| - (sum of trailing) >= |leading|/2.  So the   *)
(* sign of the sum equals the sign of the leading non-zero term.            *)
(* -------------------------------------------------------------------------- *)

(* Sign of a binary64: positive, negative, or zero. *)
Inductive expansion_sign : Type :=
| ExpPos
| ExpNeg
| ExpZero.

Fixpoint sign_of_expansion (e : b64_expansion) : expansion_sign :=
  match e with
  | nil => ExpZero
  | x :: xs =>
      match Rcompare (Binary.B2R prec emax x) 0 with
      | Lt => ExpNeg
      | Gt => ExpPos
      | Eq => sign_of_expansion xs
      end
  end.

(* -------------------------------------------------------------------------- *)
(* Foundational sign property: an empty / all-zero expansion has sign Zero. *)
(* -------------------------------------------------------------------------- *)

Lemma sign_of_expansion_nil :
  sign_of_expansion nil = ExpZero.
Proof. reflexivity. Qed.

Lemma sign_of_expansion_zero_head :
  forall (x : binary64) (xs : b64_expansion),
    Binary.B2R prec emax x = 0 ->
    sign_of_expansion (x :: xs) = sign_of_expansion xs.
Proof.
  intros x xs Hzero.
  simpl. rewrite Hzero.
  replace (Rcompare 0 0) with Eq by (symmetry; apply Rcompare_Eq; reflexivity).
  reflexivity.
Qed.

Lemma sign_of_expansion_pos_head :
  forall (x : binary64) (xs : b64_expansion),
    0 < Binary.B2R prec emax x ->
    sign_of_expansion (x :: xs) = ExpPos.
Proof.
  intros x xs Hpos.
  simpl. rewrite Rcompare_Gt by exact Hpos. reflexivity.
Qed.

Lemma sign_of_expansion_neg_head :
  forall (x : binary64) (xs : b64_expansion),
    Binary.B2R prec emax x < 0 ->
    sign_of_expansion (x :: xs) = ExpNeg.
Proof.
  intros x xs Hneg.
  simpl. rewrite Rcompare_Lt by exact Hneg. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions expansion_R_singleton.
Print Assumptions expansion_R_cons.
Print Assumptions sign_of_expansion_zero_head.
Print Assumptions sign_of_expansion_pos_head.
Print Assumptions sign_of_expansion_neg_head.

(* -------------------------------------------------------------------------- *)
(* Deferred to follow-up slices                                               *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* HEADLINE for Stage D: sign_of_expansion_correct                           *)
(*                                                                            *)
(*   Under the non-overlap invariant + finiteness, the sign of the          *)
(*   expansion (leading non-zero) equals the sign of `expansion_R e`.       *)
(*                                                                            *)
(* Theorem sign_of_expansion_correct :                                       *)
(*   forall e : b64_expansion,                                               *)
(*     expansion_finite e ->                                                 *)
(*     nonoverlap_strict e ->                                                *)
(*     match sign_of_expansion e with                                        *)
(*     | ExpPos  => 0 < expansion_R e                                        *)
(*     | ExpNeg  => expansion_R e < 0                                        *)
(*     | ExpZero => expansion_R e = 0                                        *)
(*     end.                                                                  *)
(*                                                                            *)
(* This is the proof that drives Stage D's correctness.  The key lemma is   *)
(* "|expansion_R e| >= |leading non-zero| - sum_remaining, and under non-   *)
(* overlap, sum_remaining < |leading|/2".  Inductive on the expansion       *)
(* structure with magnitude bookkeeping.                                    *)
(*                                                                            *)
(* Realistic effort: 1-2 days with the proof-engineering tax.  This is the  *)
(* GENUINELY NOVEL part of Stage D -- no Pff helper, all our own proof.   *)
(* -------------------------------------------------------------------------- *)
