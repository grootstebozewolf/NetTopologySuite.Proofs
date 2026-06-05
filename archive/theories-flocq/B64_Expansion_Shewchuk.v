(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Expansion_Shewchuk
   ----------------------------------------------------------------------------
   Slice A Pieces 1+2: weakened expansion predicate tolerating internal zeros,
   and the corresponding sign-correctness theorem.

   PIECE 1: nonoverlap_shewchuk
   ----------------------------
   `nonoverlap_shewchuk e := nonoverlap_strict (compress e)` where
   `compress` filters zero components.  The predicate skips zeros and
   applies the half-ulp bound between consecutive non-zero elements only.

   The semantics: zeros may appear anywhere in the list (Shewchuk's
   fast-expansion-sum can produce them at exact-Fast2Sum steps); the
   predicate ignores them for the pairwise check, looking only at the
   non-zero subsequence.

   PIECE 2: sign_of_expansion_correct_shewchuk
   --------------------------------------------
   The existing `sign_of_expansion_correct` (B64_Expansion.v:384) lifts
   to the weakened predicate via two structural compress-invariance
   lemmas: `expansion_R_compress` and `sign_of_expansion_compress`.

   Both `expansion_R` and `sign_of_expansion` ignore zero components by
   construction (zeros contribute 0 to the sum; sign_of_expansion's
   leading-zero branch recurses).  So compressing the list doesn't
   change either output value.

   The composition gives `sign_of_expansion_correct` under the weaker
   precondition `nonoverlap_shewchuk`.

   WHY THIS FILE EXISTS
   --------------------
   Per the Slice A prerequisite check
   (`docs/stage-d-grow-expansion-nonoverlap-tangent.md` §15), the corpus's
   `nonoverlap_strict` is too strong to be preserved by Shewchuk's
   fast-expansion-sum (internal zeros at exact Fast2Sum steps violate
   the predicate).  Two Coq-verified counterexamples in the tangent
   doc establish this.

   The weakened predicate here is what fast-expansion-sum actually
   preserves.  The sign-correctness theorem is what downstream
   consumers (b64_orient2d_exact_sign_correct) actually need.

   This file is Pieces 1+2 of Slice A's 7-piece structure (§15 of the
   tangent doc).  Pieces 3-7 follow: define fast-expansion-sum, prove
   sum-correctness, prove nonoverlap_shewchuk preservation, compose
   into orient2d_exact, headline.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.
From Stdlib Require Import List.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import B64_lib.
From NTS.Proofs.Flocq Require Import B64_Expansion.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* compress: filter zero components.                                          *)
(*                                                                            *)
(* The decision is `Rcompare (B2R x) 0`.  When the comparison returns Eq,    *)
(* the component is dropped; otherwise it is kept.  `Rcompare` evaluates    *)
(* without classical reasoning, so `compress` is computable.                 *)
(* -------------------------------------------------------------------------- *)

Fixpoint compress (xs : list binary64) : list binary64 :=
  match xs with
  | nil => nil
  | x :: xs' =>
      match Rcompare (Binary.B2R prec emax x) 0 with
      | Eq => compress xs'
      | _  => x :: compress xs'
      end
  end.

(* -------------------------------------------------------------------------- *)
(* nonoverlap_shewchuk: the weakened predicate.                              *)
(*                                                                            *)
(* Equivalent to "the compressed list is `nonoverlap_strict`".  Internal     *)
(* zeros are tolerated because compress removes them; the predicate only    *)
(* enforces the half-ulp chain on the non-zero subsequence.                 *)
(* -------------------------------------------------------------------------- *)

Definition nonoverlap_shewchuk (e : list binary64) : Prop :=
  nonoverlap_strict (compress e).

(* -------------------------------------------------------------------------- *)
(* Compress invariance lemmas.                                                *)
(*                                                                            *)
(* expansion_R and sign_of_expansion both ignore zero components by         *)
(* construction.  Hence both are invariant under compress.                  *)
(* -------------------------------------------------------------------------- *)

Lemma expansion_R_compress :
  forall xs : list binary64,
    expansion_R (compress xs) = expansion_R xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl.
    destruct (Rcompare (Binary.B2R prec emax x) 0) eqn:Hc.
    + apply Rcompare_Eq_inv in Hc.
      rewrite IH. lra.
    + simpl. rewrite IH. reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

Lemma sign_of_expansion_compress :
  forall xs : list binary64,
    sign_of_expansion (compress xs) = sign_of_expansion xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl.
    destruct (Rcompare (Binary.B2R prec emax x) 0) eqn:Hc.
    + exact IH.
    + simpl. rewrite Hc. reflexivity.
    + simpl. rewrite Hc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* HEADLINE: sign-of-expansion correctness under the weakened predicate.    *)
(*                                                                            *)
(* Compose the existing `sign_of_expansion_correct` (which takes the         *)
(* stronger `nonoverlap_strict`) with the two compress-invariance lemmas    *)
(* above.  The proof is ~5 lines once the helpers are in place.             *)
(* -------------------------------------------------------------------------- *)

Theorem sign_of_expansion_correct_shewchuk :
  forall e : b64_expansion,
    nonoverlap_shewchuk e ->
    match sign_of_expansion e with
    | ExpPos  => 0 < expansion_R e
    | ExpNeg  => expansion_R e < 0
    | ExpZero => expansion_R e = 0
    end.
Proof.
  intros e Hno.
  unfold nonoverlap_shewchuk in Hno.
  pose proof (sign_of_expansion_correct (compress e) Hno) as Hcorrect.
  rewrite sign_of_expansion_compress in Hcorrect.
  rewrite expansion_R_compress in Hcorrect.
  exact Hcorrect.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions sign_of_expansion_correct_shewchuk.
