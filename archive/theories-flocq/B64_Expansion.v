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
(* sign_of_expansion_correct: attempting the proof.                           *)
(* -------------------------------------------------------------------------- *)

(* Trivial base case. *)
Lemma sign_of_expansion_correct_nil :
  match sign_of_expansion nil with
  | ExpPos  => 0 < expansion_R nil
  | ExpNeg  => expansion_R nil < 0
  | ExpZero => expansion_R nil = 0
  end.
Proof. simpl. reflexivity. Qed.

(* The subnormal-edge lemma the pair proof needs.  Any binary64 with        *)
(* magnitude strictly below bpow emin (= 2^-1074) must be exactly 0,        *)
(* because the smallest non-zero representable value is bpow emin.          *)
Lemma binary64_below_emin_is_zero :
  forall x : binary64,
    Rabs (Binary.B2R prec emax x) < bpow radix2 (3 - emax - prec) ->
    Binary.B2R prec emax x = 0.
Proof.
  intros x Habs.
  pose proof (Binary.generic_format_B2R prec emax x) as Hfmt.
  apply (@FLT_format_generic radix2 (3 - emax - prec)%Z prec prec_gt_0_b64) in Hfmt.
  destruct Hfmt as [f Hf1 Hf2 Hf3].
  rewrite Hf1 in *.
  destruct (Z.eq_dec (Defs.Fnum f) 0) as [Hm0 | Hmne].
  - unfold F2R. simpl. rewrite Hm0. simpl. lra.
  - exfalso.
    assert (Habs_nz : (1 <= Z.abs (Defs.Fnum f))%Z) by lia.
    assert (HFbnd : bpow radix2 (3 - emax - prec) <= Rabs (F2R f)).
    { unfold F2R.
      rewrite Rabs_mult.
      rewrite (Rabs_pos_eq (bpow radix2 (Defs.Fexp f))) by apply bpow_ge_0.
      rewrite <- abs_IZR.
      apply Rle_trans with (1 * bpow radix2 (Defs.Fexp f)).
      - rewrite Rmult_1_l. apply bpow_le. exact Hf3.
      - apply Rmult_le_compat_r; [apply bpow_ge_0|].
        apply IZR_le. exact Habs_nz. }
    lra.
Qed.

(* Length-1 case: sign of single element matches sign of its B2R. *)
Lemma sign_of_expansion_correct_singleton :
  forall x : binary64,
    match sign_of_expansion (x :: nil) with
    | ExpPos  => 0 < expansion_R (x :: nil)
    | ExpNeg  => expansion_R (x :: nil) < 0
    | ExpZero => expansion_R (x :: nil) = 0
    end.
Proof.
  intros x. simpl.
  destruct (Rcompare (Binary.B2R prec emax x) 0) eqn:E.
  - apply Rcompare_Eq_inv in E. lra.
  - apply Rcompare_Lt_inv in E. lra.
  - apply Rcompare_Gt_inv in E. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* When the leading binary64 has B2R = 0, the entire tail cascades to 0      *)
(* via repeated application of the subnormal-edge lemma.  Crucial for the   *)
(* main induction: lets us handle the "leading is zero" case at any depth.  *)
(* -------------------------------------------------------------------------- *)

Lemma nonoverlap_zero_tail :
  forall (xs : b64_expansion) (a : binary64),
    Binary.B2R prec emax a = 0 ->
    nonoverlap_strict (a :: xs) ->
    expansion_R xs = 0 /\ sign_of_expansion xs = ExpZero.
Proof.
  induction xs as [|b bs IH]; intros a Hzero Hno.
  - split; reflexivity.
  - simpl in Hno. destruct Hno as [Hsucc Hno_tail].
    unfold strict_succ_b64 in Hsucc. rewrite Hzero in Hsucc.
    change (SpecFloat.fexp prec emax)
      with (FLT_exp (3 - emax - prec)%Z prec) in Hsucc.
    rewrite (@ulp_FLT_0 radix2 (3 - emax - prec)%Z prec prec_gt_0_b64) in Hsucc.
    assert (Hb_below : Rabs (Binary.B2R prec emax b)
                      < bpow radix2 (3 - emax - prec)).
    { apply Rle_lt_trans with (bpow radix2 (3 - emax - prec) / 2).
      - exact Hsucc.
      - assert (Hpos : 0 < bpow radix2 (3 - emax - prec)) by apply bpow_gt_0.
        lra. }
    pose proof (binary64_below_emin_is_zero b Hb_below) as Hb0.
    specialize (IH b Hb0 Hno_tail). destruct IH as [HsumR HsignR].
    split.
    + simpl. rewrite Hb0, HsumR. lra.
    + simpl. rewrite Hb0.
      replace (Rcompare 0 0) with Eq by (symmetry; apply Rcompare_Eq; reflexivity).
      exact HsignR.
Qed.

(* Magnitude bound: for a non-zero-leading expansion under nonoverlap_strict, *)
(* the absolute sum of the tail is STRICTLY less than the magnitude of the   *)
(* leading element.  Geometric series argument; handles the cascading        *)
(* subnormal edge case via nonoverlap_zero_tail at each step.                *)
Lemma expansion_tail_bounded :
  forall (xs : b64_expansion) (a : binary64),
    Binary.B2R prec emax a <> 0 ->
    nonoverlap_strict (a :: xs) ->
    Rabs (expansion_R xs) < Rabs (Binary.B2R prec emax a).
Proof.
  induction xs as [|b bs IH]; intros a Hane Hno.
  - simpl. rewrite Rabs_R0. apply Rabs_pos_lt. exact Hane.
  - simpl in Hno. destruct Hno as [Hsucc Hno_tail].
    unfold strict_succ_b64 in Hsucc.
    pose proof (Binary.generic_format_B2R prec emax a) as FaR.
    pose proof (ulp_le_abs radix2 (SpecFloat.fexp prec emax)
                  (Binary.B2R prec emax a) Hane FaR) as Hu.
    destruct (Req_dec (Binary.B2R prec emax b) 0) as [Hb0 | Hbne].
    + destruct (nonoverlap_zero_tail bs b Hb0 Hno_tail) as [HsumR _].
      simpl. rewrite Hb0, HsumR.
      replace (0 + 0) with 0 by lra.
      rewrite Rabs_R0. apply Rabs_pos_lt. exact Hane.
    + specialize (IH b Hbne Hno_tail).
      simpl.
      apply Rle_lt_trans
        with (Rabs (Binary.B2R prec emax b) + Rabs (expansion_R bs)).
      * apply Rabs_triang.
      * apply Rlt_le_trans
          with (2 * Rabs (Binary.B2R prec emax b)).
        -- lra.
        -- apply Rle_trans
             with (ulp radix2 (SpecFloat.fexp prec emax)
                        (Binary.B2R prec emax a)).
           ++ lra.
           ++ exact Hu.
Qed.

(* -------------------------------------------------------------------------- *)
(* Length-2 case: now complete via the subnormal-edge lemma above.            *)
(* -------------------------------------------------------------------------- *)

Lemma sign_of_expansion_correct_pair :
  forall (a b : binary64),
    strict_succ_b64 a b ->
    match sign_of_expansion (a :: b :: nil) with
    | ExpPos  => 0 < expansion_R (a :: b :: nil)
    | ExpNeg  => expansion_R (a :: b :: nil) < 0
    | ExpZero => expansion_R (a :: b :: nil) = 0
    end.
Proof.
  intros a b Hsucc. unfold strict_succ_b64 in Hsucc.
  pose proof (Binary.generic_format_B2R prec emax a) as FaR.
  simpl.
  destruct (Rcompare (Binary.B2R prec emax a) 0) eqn:Ea.
  - (* B2R a = 0: ulp(0) = bpow emin, so |B2R b| <= bpow emin / 2 < bpow emin
       => B2R b = 0 by the subnormal-edge lemma. *)
    apply Rcompare_Eq_inv in Ea. rewrite Ea in *.
    assert (Hulp0 : ulp radix2 (SpecFloat.fexp prec emax) 0
                  = bpow radix2 (3 - emax - prec)).
    { apply (@ulp_FLT_0 radix2 (3 - emax - prec)%Z prec prec_gt_0_b64). }
    rewrite Hulp0 in Hsucc.
    assert (Hb_below : Rabs (Binary.B2R prec emax b)
                      < bpow radix2 (3 - emax - prec)).
    { apply Rle_lt_trans with (bpow radix2 (3 - emax - prec) / 2).
      - exact Hsucc.
      - assert (Hpos : 0 < bpow radix2 (3 - emax - prec)) by apply bpow_gt_0.
        lra. }
    pose proof (binary64_below_emin_is_zero b Hb_below) as Hb0.
    rewrite Hb0.
    replace (Rcompare 0 0) with Eq by (symmetry; apply Rcompare_Eq; reflexivity).
    lra.
  - apply Rcompare_Lt_inv in Ea.
    assert (Hne : Binary.B2R prec emax a <> 0) by lra.
    pose proof (ulp_le_abs radix2 (SpecFloat.fexp prec emax)
                  (Binary.B2R prec emax a) Hne FaR) as Hu.
    apply Rabs_le_inv in Hsucc.
    destruct Hsucc as [Hb_lo Hb_hi].
    rewrite Rabs_left in Hu by exact Ea.
    lra.
  - apply Rcompare_Gt_inv in Ea.
    assert (Hne : Binary.B2R prec emax a <> 0) by lra.
    pose proof (ulp_le_abs radix2 (SpecFloat.fexp prec emax)
                  (Binary.B2R prec emax a) Hne FaR) as Hu.
    apply Rabs_le_inv in Hsucc.
    destruct Hsucc as [Hb_lo Hb_hi].
    rewrite Rabs_right in Hu by lra.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* HEADLINE: sign_of_expansion_correct -- the genuinely novel piece of Stage D *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* For any expansion satisfying `nonoverlap_strict`, the sign of the leading *)
(* non-zero element (or Zero if all-zero) equals the sign of the exact sum. *)
(* Proven by induction on the list using:                                    *)
(*   - `nonoverlap_zero_tail`: zero-leading cascades to zero tail.           *)
(*   - `expansion_tail_bounded`: |tail| < |leading| for non-zero leading.    *)
(*   - `ulp_le_abs`: ulp(x) <= |x| for non-zero x (Flocq Core/Ulp.v:167).   *)
(*   - `binary64_below_emin_is_zero`: subnormal edge.                        *)
(*                                                                            *)
(* This is the SOUNDNESS of `sign_of_expansion` for arbitrary-length         *)
(* bounded expansions -- exactly what Stage D needs to extract a definite   *)
(* orient2d sign from a 16-component exact determinant.                      *)
(* -------------------------------------------------------------------------- *)

Theorem sign_of_expansion_correct :
  forall e : b64_expansion,
    nonoverlap_strict e ->
    match sign_of_expansion e with
    | ExpPos  => 0 < expansion_R e
    | ExpNeg  => expansion_R e < 0
    | ExpZero => expansion_R e = 0
    end.
Proof.
  induction e as [|a xs IH]; intros Hno.
  - simpl. reflexivity.
  - simpl.
    destruct (Rcompare (Binary.B2R prec emax a) 0) eqn:Ea.
    + apply Rcompare_Eq_inv in Ea.
      destruct (nonoverlap_zero_tail xs a Ea Hno) as [HsumR HsignR].
      rewrite HsignR. lra.
    + apply Rcompare_Lt_inv in Ea.
      assert (Hane : Binary.B2R prec emax a <> 0) by lra.
      pose proof (expansion_tail_bounded xs a Hane Hno) as Hbnd.
      rewrite (Rabs_left (Binary.B2R prec emax a)) in Hbnd by exact Ea.
      apply Rabs_def2 in Hbnd. destruct Hbnd as [Hbnd_upper _].
      lra.
    + apply Rcompare_Gt_inv in Ea.
      assert (Hane : Binary.B2R prec emax a <> 0) by lra.
      pose proof (expansion_tail_bounded xs a Hane Hno) as Hbnd.
      rewrite (Rabs_right (Binary.B2R prec emax a)) in Hbnd by lra.
      apply Rabs_def2 in Hbnd. destruct Hbnd as [_ Hbnd_lower].
      lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* OLD FRICTION COMMENT (preserved for documentation purposes)                *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* The non-degenerate cases (`B2R a < 0` and `B2R a > 0`) close in ~5 lines  *)
(* each via:                                                                  *)
(*   - `Flocq.Core.Ulp.ulp_le_abs` (`ulp x <= Rabs x` for non-zero x in fmt) *)
(*   - `Binary.generic_format_B2R` (B2R is always in `generic_format`)        *)
(*   - `Rabs_le_inv` + `Rabs_left/right` + `lra`.                             *)
(*                                                                            *)
(* So the standard non-overlap chain (leading non-zero) propagates the sign  *)
(* cleanly.                                                                   *)
(*                                                                            *)
(* The HARD CASE is the SUBNORMAL EDGE: when `B2R a = 0`.                    *)
(*                                                                            *)
(* Under `strict_succ_b64 a b`, we have `Rabs (B2R b) <= ulp(B2R a) / 2`.   *)
(* When `B2R a = 0`, `ulp(0) = bpow emin` (the FLT-format convention).      *)
(* So `Rabs (B2R b) <= bpow emin / 2`.                                       *)
(*                                                                            *)
(* CLAIM: this forces `B2R b = 0` because the smallest non-zero magnitude   *)
(* in the binary64 generic_format is `bpow emin` (the smallest subnormal). *)
(*                                                                            *)
(* PROOF REQUIRED: a lemma                                                   *)
(*     forall x : binary64,                                                  *)
(*       Rabs (B2R x) < bpow radix2 emin ->                                  *)
(*       B2R x = 0.                                                          *)
(*                                                                            *)
(* This is the TANGENT POINT.  Hunting for this in Flocq's `Core/FLT.v`,    *)
(* `Core/Ulp.v`, `IEEE754/Binary.v` does not surface it directly -- it has  *)
(* to be derived from the FLT_format characterisation                       *)
(* (an integer `Fnum` times `bpow Fexp` with `emin <= Fexp` and             *)
(* `Z.abs Fnum < bpow prec`).  The pen-and-paper proof is short:            *)
(*                                                                            *)
(*   Suppose `Rabs (B2R x) < bpow emin` and `B2R x <> 0`.                   *)
(*   By generic_format, B2R x = F2R (Float m e) with emin <= e and          *)
(*   |m| < bpow prec.  Then |F2R| = |m| * bpow e >= bpow emin (since         *)
(*   |m| >= 1 and e >= emin, so |m| * bpow e >= bpow e >= bpow emin).        *)
(*   Contradiction.                                                          *)
(*                                                                            *)
(* The COQ proof is ~15-25 lines:                                            *)
(*   - destruct generic_format witness                                       *)
(*   - case on Fnum (handle 0, +pos, -pos)                                  *)
(*   - bound F2R by bpow emin                                               *)
(*   - lra (or Rle_lt_trans + bpow inequality)                              *)
(*                                                                            *)
(* So the tangent is REAL but BOUNDED.  This is where Stage D's hardness   *)
(* lives empirically:                                                       *)
(*                                                                            *)
(*  - NOT in lifting Pff lemmas (mechanical, ~30 lines each)                 *)
(*  - NOT in Dekker's 16-op bookkeeping (tedious but template-driven)       *)
(*  - NOT in the expansion data structure (clean list induction)             *)
(*  - YES in the SUBNORMAL EDGE CASES of the sign-correctness proof:        *)
(*    a small but finicky Flocq-machinery hunt for the right                *)
(*    `format -> zero-or-bounded-away` lemmas.                              *)
(*                                                                            *)
(* The full `sign_of_expansion_correct` for arbitrary-length expansions     *)
(* would need this subnormal-edge handling at EACH level of the induction. *)
(* The structural induction is fine; the edge-case discharges multiply.    *)
(*                                                                            *)
(* Realistic engagement estimate for `sign_of_expansion_correct` (full):   *)
(*   1-2 days hunting Flocq + writing the subnormal-edge lemmas             *)
(*   + the length-n induction.  ~150-200 lines, all genuinely new.         *)
(*                                                                            *)
(* The pair lemma is deferred to that engagement.  Non-degenerate cases    *)
(* would Qed in ~10 lines (proof shown in this comment as documentation):  *)
(*                                                                            *)
(*   Proof.                                                                  *)
(*     intros a b Hsucc. unfold strict_succ_b64 in Hsucc.                   *)
(*     pose proof (Binary.generic_format_B2R prec emax a) as FaR.            *)
(*     simpl.                                                                *)
(*     destruct (Rcompare (B2R a) 0) eqn:Ea.                                 *)
(*     - apply Rcompare_Eq_inv in Ea.                                        *)
(*       (* Subnormal-edge tangent -- documented above *)                    *)
(*     - apply Rcompare_Lt_inv in Ea.                                        *)
(*       assert (Hne : B2R a <> 0) by lra.                                   *)
(*       pose proof (ulp_le_abs _ _ (B2R a) Hne FaR) as Hu.                  *)
(*       apply Rabs_le_inv in Hsucc. destruct Hsucc.                         *)
(*       rewrite Rabs_left in Hu by exact Ea. lra.                           *)
(*     - apply Rcompare_Gt_inv in Ea.                                        *)
(*       assert (Hne : B2R a <> 0) by lra.                                   *)
(*       pose proof (ulp_le_abs _ _ (B2R a) Hne FaR) as Hu.                  *)
(*       apply Rabs_le_inv in Hsucc. destruct Hsucc.                         *)
(*       rewrite Rabs_right in Hu by lra. lra.                               *)
(*     (* Edge case: leading zero -- needs the subnormal lemma. *)           *)
(*   Qed.                                                                    *)
(*                                                                            *)
(* Two cases close in ~5 lines.  One case opens the tangent.  That's the   *)
(* empirical answer.                                                        *)
(* -------------------------------------------------------------------------- *)

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
