(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Pff_bridge
   ----------------------------------------------------------------------------
   Bridge module between Flocq's `Pff2Flocq` (expansion-arithmetic primitives,
   stated over abstract `(emin prec : Z)` + `(choice : Z -> bool)` parameters)
   and our concrete binary64 instantiation in `Validate_binary64.v`.

   Resolves the obstruction identified by `B64_TwoSum_probe.v`: Pff2Flocq's
   sections are parameterised over a symmetric `choice` function, and
   binary64's `round_mode mode_NE` uses the specific
   `fun x => negb (Z.even x)` choice (ties-to-even).  This module discharges
   the section preconditions for that choice -- the one-time work --
   and exposes `b64_Fast2Sum_correct` as the first Stage D primitive lifted
   via the bridge.

   Once this module is in place, every subsequent Pff2Flocq lift
   (TwoSum, Veltkamp split, Dekker TwoProduct) is a ~30-line wrapper.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.
From Flocq Require Import Pff.Pff2Flocq.

From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import B64_bridge.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Binary64 instantiation of Pff2Flocq's section parameters.                  *)
(* -------------------------------------------------------------------------- *)

Definition b64_emin : Z := (3 - emax - prec)%Z.

Definition b64_choice : Z -> bool := fun x => negb (Z.even x).

(* -------------------------------------------------------------------------- *)
(* Discharges of the section hypotheses.                                      *)
(* -------------------------------------------------------------------------- *)

Lemma b64_precisionNotZero : (1 < prec)%Z.
Proof. unfold prec. lia. Qed.

Lemma b64_emin_neg : (b64_emin <= 0)%Z.
Proof. unfold b64_emin, emax, prec. lia. Qed.

(* The negation symmetry for `Z.even`.  Proof by case on the constructor:    *)
(* every `Z.pos p` and `Z.neg p` has the same `Z.even` by direct case        *)
(* analysis on the structure (matches `xO _` either way).                    *)
Lemma Z_even_opp : forall x : Z, Z.even (- x) = Z.even x.
Proof. intros [|p|p]; reflexivity. Qed.

(* The choice_sym hypothesis for binary64's mode_NE.  Reduces (via           *)
(* negb_involutive + Z_even_opp + Z.even_succ + Z.negb_even) to a            *)
(* one-liner about Z.even.                                                   *)
Lemma b64_choice_sym :
  forall x : Z, b64_choice x = negb (b64_choice (- (x + 1))).
Proof.
  intros x. unfold b64_choice. rewrite negb_involutive.
  rewrite Z_even_opp.
  rewrite Z.add_1_r, Z.even_succ.
  apply Z.negb_even.
Qed.

(* -------------------------------------------------------------------------- *)
(* The Fast2Sum algorithm at binary64.                                        *)
(*                                                                            *)
(* Given inputs x, y : binary64 with `|y| <= |x|`, computes a pair (a, b)   *)
(* such that `B2R a + B2R b = B2R x + B2R y` exactly.  Uses three binary64  *)
(* arithmetic operations.  Foundational primitive for every expansion-       *)
(* arithmetic algorithm in Shewchuk Stages B/C/D.                            *)
(* -------------------------------------------------------------------------- *)

Definition b64_Fast2Sum (x y : binary64) : binary64 * binary64 :=
  let a := b64_plus x y in
  let z := b64_minus x a in
  let b := b64_plus y z in
  (a, b).

(* -------------------------------------------------------------------------- *)
(* Headline: b64_Fast2Sum is exact under the magnitude precondition + the    *)
(* three no-overflow safety predicates (one per op).                          *)
(* -------------------------------------------------------------------------- *)

Theorem b64_Fast2Sum_correct :
  forall x y : binary64,
    Rabs (Binary.B2R prec emax y) <= Rabs (Binary.B2R prec emax x) ->
    b64_safe Rplus x y ->
    b64_safe Rminus x (b64_plus x y) ->
    b64_safe Rplus y (b64_minus x (b64_plus x y)) ->
    let '(a, b) := b64_Fast2Sum x y in
    Binary.B2R prec emax a + Binary.B2R prec emax b
      = Binary.B2R prec emax x + Binary.B2R prec emax y.
Proof.
  intros x y Hmag Hsafe_a Hsafe_z Hsafe_b.
  unfold b64_Fast2Sum.
  pose proof (b64_plus_correct  x y Hsafe_a) as [HBa _].
  pose proof (b64_minus_correct x (b64_plus x y) Hsafe_z) as [HBz _].
  pose proof (b64_plus_correct  y (b64_minus x (b64_plus x y)) Hsafe_b) as [HBb _].
  pose proof (Binary.generic_format_B2R prec emax x) as FxR.
  pose proof (Binary.generic_format_B2R prec emax y) as FyR.
  pose proof (Fast2Sum_correct b64_emin prec b64_choice
                b64_precisionNotZero b64_emin_neg b64_choice_sym
                (Binary.B2R prec emax x) (Binary.B2R prec emax y)
                FxR FyR Hmag) as HFTS.
  (* HFTS is in `round_flt` form (= `round radix2 (FLT_exp b64_emin prec)
     (Znearest b64_choice) ...`).  The goal after the rewrites below is in
     `b64_round` form (= `round radix2 (SpecFloat.fexp prec emax)
     (round_mode mode_b64) ...`).  These are definitionally equal because:
       - SpecFloat.fexp prec emax = fun e => Z.max (e - prec) (3 - emax - prec)
                                 = FLT_exp b64_emin prec   (with b64_emin = 3 - emax - prec)
       - round_mode mode_b64 = ZnearestE = Znearest b64_choice. *)
  rewrite HBb.  (* outer second plus, exposes B2R (b64_minus x (b64_plus x y)) *)
  rewrite HBz.  (* inner minus, exposes B2R (b64_plus x y) inside the round  *)
  rewrite !HBa. (* both occurrences of B2R (b64_plus x y)                    *)
  exact HFTS.
Qed.

(* -------------------------------------------------------------------------- *)
(* The TwoSum algorithm at binary64 (6-op variant; no magnitude precondition).*)
(*                                                                            *)
(* Same expression as Pff2Flocq.TwoSum_correct, instantiated for binary64:    *)
(*   a   = round (x + y)                                                      *)
(*   x'  = round (a - x)                                                      *)
(*   dx  = round (x - round (a - x'))                                         *)
(*   dy  = round (y - x')                                                     *)
(*   b   = round (dx + dy)                                                    *)
(* and `a + b = x + y` exactly.                                               *)
(* -------------------------------------------------------------------------- *)

Definition b64_TwoSum (x y : binary64) : binary64 * binary64 :=
  let a := b64_plus x y in
  let x' := b64_minus a x in
  let dx := b64_minus x (b64_minus a x') in
  let dy := b64_minus y x' in
  let b := b64_plus dx dy in
  (a, b).

(* Six safety preconditions, one per b64 op in the chain.  Same shape as     *)
(* `b64_Fast2Sum_correct`'s preconditions; bookkeeping cost matches the      *)
(* scout's "~30 lines per subsequent Pff lift" estimate.                    *)
Theorem b64_TwoSum_correct :
  forall x y : binary64,
    b64_safe Rplus  x y ->                                       (* a    *)
    b64_safe Rminus (b64_plus x y) x ->                          (* x'   *)
    b64_safe Rminus (b64_plus x y) (b64_minus (b64_plus x y) x) -> (* a-x'  *)
    b64_safe Rminus x
      (b64_minus (b64_plus x y) (b64_minus (b64_plus x y) x)) -> (* dx   *)
    b64_safe Rminus y (b64_minus (b64_plus x y) x) ->            (* dy   *)
    b64_safe Rplus
      (b64_minus x
        (b64_minus (b64_plus x y) (b64_minus (b64_plus x y) x)))
      (b64_minus y (b64_minus (b64_plus x y) x)) ->              (* b    *)
    let '(a, b) := b64_TwoSum x y in
    Binary.B2R prec emax a + Binary.B2R prec emax b
      = Binary.B2R prec emax x + Binary.B2R prec emax y.
Proof.
  intros x y Hsa Hsxp Hsaxp Hsdx Hsdy Hsb.
  unfold b64_TwoSum.
  pose proof (b64_plus_correct  x y                              Hsa)  as [HBa _].
  pose proof (b64_minus_correct (b64_plus x y) x                 Hsxp) as [HBxp _].
  pose proof (b64_minus_correct (b64_plus x y) (b64_minus (b64_plus x y) x) Hsaxp) as [HBaxp _].
  pose proof (b64_minus_correct x (b64_minus (b64_plus x y) (b64_minus (b64_plus x y) x)) Hsdx) as [HBdx _].
  pose proof (b64_minus_correct y (b64_minus (b64_plus x y) x)   Hsdy) as [HBdy _].
  pose proof (b64_plus_correct
                (b64_minus x (b64_minus (b64_plus x y) (b64_minus (b64_plus x y) x)))
                (b64_minus y (b64_minus (b64_plus x y) x)) Hsb) as [HBb _].
  pose proof (Binary.generic_format_B2R prec emax x) as FxR.
  pose proof (Binary.generic_format_B2R prec emax y) as FyR.
  pose proof (TwoSum_correct b64_emin prec b64_choice
                b64_precisionNotZero b64_emin_neg b64_choice_sym
                (Binary.B2R prec emax x) (Binary.B2R prec emax y)
                FxR FyR) as HTS.
  (* Cascade the B2R rewrites from outermost to innermost so each successive *)
  (* rewrite exposes the next b64_op-wrapped argument.                       *)
  rewrite HBb.
  rewrite HBdy.
  rewrite HBdx.
  rewrite HBaxp.
  rewrite !HBxp.
  rewrite !HBa.
  exact HTS.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions Z_even_opp.
Print Assumptions b64_choice_sym.
Print Assumptions b64_Fast2Sum_correct.
Print Assumptions b64_TwoSum_correct.

(* -------------------------------------------------------------------------- *)
(* Next slices on this bridge                                                 *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* With `b64_precisionNotZero`, `b64_emin_neg`, `b64_choice_sym` in place,   *)
(* every Pff2Flocq.* lemma can be instantiated for binary64 by passing the  *)
(* same section parameters.  The next Stage D primitives to lift:           *)
(*                                                                            *)
(* 1. `b64_TwoSum` (6-op variant; no magnitude precondition).                *)
(*    Lifts `Pff2Flocq.TwoSum_correct` (line 200, section TS).               *)
(* 2. `b64_Veltkamp_split` (splits a binary64 into two half-precision        *)
(*    values).  Lifts `Pff2Flocq.Veltkamp` (line 382).                       *)
(* 3. `b64_Dekker` (TwoProduct via Veltkamp split, radix-2 case).            *)
(*    Lifts `Pff2Flocq.Dekker` (line 729).                                   *)
(*                                                                            *)
(* Once those three are in place, the bounded-form Stage D for orient2d     *)
(* compiles out as straight-line composition: ~50 floating-point ops,       *)
(* ≤16-component expansion, sign extracted by inspecting the leading        *)
(* non-zero component.  See `docs/stage-d-feasibility.md` for the scaffold. *)
(* -------------------------------------------------------------------------- *)
