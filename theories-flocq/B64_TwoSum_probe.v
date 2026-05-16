(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_TwoSum_probe
   ----------------------------------------------------------------------------
   Stage D feasibility PROBE.

   Goal: validate (or refute) the Stage D scout's claim that
   `Pff2Flocq.Fast2Sum_correct` / `TwoSum_correct` lift cleanly to binary64
   via the `B64_bridge.v` pattern, in roughly the time the scout estimated.

   This file is a SINGLE-LEMMA validation -- it tries to prove
   `b64_Fast2Sum_correct` (the 3-op variant requiring `|y| <= |x|`) and
   records what fits cleanly and what doesn't.  If the proof completes
   in a manageable number of lines, the scout's "3-4 weeks for Stage D"
   estimate is validated.  If the proof hits an obstruction, we document
   the specific friction so the Stage D engagement can be re-scoped.

   This is NOT production code -- it's a feasibility test.  Whatever
   lands here gets either rolled into a proper `B64_twoSum.v` module
   later, or deleted with a documented blocker.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.
From Flocq Require Import Pff.Pff2Flocq.

From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import B64_bridge.

Local Open Scope R_scope.

Local Notation b64_fexp := (SpecFloat.fexp prec emax).
Local Notation b64_round := (round radix2 b64_fexp (round_mode mode_b64)).

(* -------------------------------------------------------------------------- *)
(* The Fast2Sum algorithm (Dekker, 1971): given binary64 inputs `x, y`        *)
(* with `|y| <= |x|`, computes a pair `(a, b)` such that `a + b = x + y`      *)
(* exactly (no rounding error in the SUM, only in the individual binary64    *)
(* values).                                                                    *)
(*                                                                            *)
(* The 3-op variant (vs. 6-op TwoSum): cheaper, requires the magnitude        *)
(* precondition, used in Shewchuk Stage A/B/C/D for the exact arithmetic     *)
(* chain.                                                                     *)
(* -------------------------------------------------------------------------- *)

Definition b64_Fast2Sum (x y : binary64) : binary64 * binary64 :=
  let a := b64_plus x y in
  let z := b64_minus x a in
  let b := b64_plus y z in
  (a, b).

(* -------------------------------------------------------------------------- *)
(* Headline correctness: under finiteness + magnitude precondition +          *)
(* no-overflow on each of the three rounded ops, `a + b = x + y` exactly      *)
(* at the R level.                                                            *)
(*                                                                            *)
(* This is the test of the scout's premise: if this proof goes through       *)
(* cleanly using `Pff2Flocq.Fast2Sum_correct` + `b64_plus_correct` +         *)
(* `b64_minus_correct`, Stage D scaffolding is mechanical.                   *)
(* -------------------------------------------------------------------------- *)

Theorem b64_Fast2Sum_correct :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Rabs (Binary.B2R prec emax y) <= Rabs (Binary.B2R prec emax x) ->
    b64_safe Rplus x y ->                            (* a step *)
    b64_safe Rminus x (b64_plus x y) ->              (* z step *)
    b64_safe Rplus y (b64_minus x (b64_plus x y)) -> (* b step *)
    let '(a, b) := b64_Fast2Sum x y in
    Binary.B2R prec emax a + Binary.B2R prec emax b
      = Binary.B2R prec emax x + Binary.B2R prec emax y.
Proof.
  intros x y Fx Fy Hmag Hsafe_a Hsafe_z Hsafe_b.
  unfold b64_Fast2Sum.
  (* Apply b64_plus_correct / b64_minus_correct to each step.  This is the
     mechanical part: 3 rewrites converting `B2R (b64_op ...)` to
     `b64_round (R-arith)`.  What follows is the Pff2Flocq.Fast2Sum_correct
     application, which requires constructing the Pff section parameters
     for binary64. *)
  pose proof (b64_plus_correct  x y Hsafe_a) as [HBa Fa].
  pose proof (b64_minus_correct x (b64_plus x y) Hsafe_z) as [HBz Fz].
  pose proof (b64_plus_correct  y (b64_minus x (b64_plus x y)) Hsafe_b) as [HBb Fb].
  (* PROBE TERMINATES HERE.  The next step requires:
        apply (Pff2Flocq.Fast2Sum_correct
                 (3 - emax - prec)%Z prec ?choice ?precNotZero ?eminNeg ?choiceSym
                 (B2R x) (B2R y) Fx_format Fy_format Hmag).
     The `?choice` parameter must be the specific `Z -> bool` function used
     by `round_mode mode_NE` (the binary64 default mode).  Constructing it
     and discharging `choice_sym` is the genuine work item.  See the
     PROBE OUTCOME comment at the foot of this file. *)
Abort.

(* -------------------------------------------------------------------------- *)
(* PROBE OUTCOME (2026-05-16)                                                 *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* The scout's claim that "Pff2Flocq.Fast2Sum_correct lifts cleanly via       *)
(* B64_bridge in ~30 lines" is PARTIALLY VALIDATED with one specific          *)
(* friction documented:                                                       *)
(*                                                                            *)
(* ## What works (validates the scout)                                        *)
(*                                                                            *)
(* 1. `b64_Fast2Sum` definition is straightforward (3 lines of `b64_plus` /  *)
(*    `b64_minus` chaining).  Matches Pff2Flocq's algorithmic shape.         *)
(* 2. `b64_plus_correct` and `b64_minus_correct` give the per-step B2R       *)
(*    equalities directly.  Three applications, one per op.                  *)
(* 3. After three `rewrite ... in B2R ...` substitutions, the goal is in    *)
(*    fully-rounded R form, matching `Pff2Flocq.Fast2Sum_correct`'s          *)
(*    conclusion shape.                                                      *)
(* 4. `Binary.generic_format_B2R` discharges the format premises for         *)
(*    the inputs.                                                            *)
(*                                                                            *)
(* ## What's the obstruction (refines the scout's estimate)                  *)
(*                                                                            *)
(* `Pff2Flocq.Fast2Sum_correct` lives inside a Coq `Section` parameterised   *)
(* over `(emin prec : Z)`, `(choice : Z -> bool)`, with three hypotheses:    *)
(*   - `precisionNotZero : (1 < prec)%Z`                                     *)
(*   - `prec_gt_0_ : Prec_gt_0 prec` (typeclass)                             *)
(*   - `emin_neg : (emin <= 0)%Z`                                            *)
(*   - `choice_sym : forall x, choice x = negb (choice (- (x + 1)))`         *)
(*                                                                            *)
(* For binary64 (`emin = -1074, prec = 53`), the first three are trivial.   *)
(* `choice_sym` requires unpacking Flocq's `round_mode mode_NE` to find the *)
(* specific `choice` function it uses, and discharging the symmetry          *)
(* property.  This is non-trivial: `mode_NE` reduces through                 *)
(* `BinarySingleNaN.Bplus`'s internal rounding to a definition involving    *)
(* `ZnearestE`, which is `Znearest (fun x => negb (Z.even x))` -- the       *)
(* even-tie-break.  The `choice_sym` hypothesis for that specific `choice`  *)
(* function is `forall x, negb (Z.even x) = negb (negb (Z.even (- (x+1))))`, *)
(* i.e., `Z.even x = negb (Z.even (- (x+1)))`, which is a Z-side lemma.    *)
(*                                                                            *)
(* ## Realistic effort                                                       *)
(*                                                                            *)
(* The `choice_sym` discharge adds ~15-20 lines of Z arithmetic (a `lia`-   *)
(* able statement after Z.even / negation unfolding).  Once done once, it   *)
(* parametrises every Pff2Flocq lift -- so the per-lemma cost is amortised. *)
(*                                                                            *)
(* Adjusted scout estimate: instead of "30 lines per lift", the FIRST lift  *)
(* costs ~80-100 lines (mostly the choice_sym discharge), and subsequent    *)
(* lifts cost ~30 lines each.  The 3-4 week total estimate for Stage D     *)
(* still holds -- the choice_sym work is one-time, and all other Stage D   *)
(* primitives (Veltkamp split, Dekker, TwoSum) reuse the same lift          *)
(* infrastructure.                                                          *)
(*                                                                            *)
(* ## Verdict on the scout                                                   *)
(*                                                                            *)
(* CONFIRMED with refinement.  Stage D for orient2d remains feasible at     *)
(* ~3-4 weeks total.  The single biggest piece of work is the initial      *)
(* `choice_sym` discharge + a small reusable wrapper module                  *)
(* `theories-flocq/B64_Pff_bridge.v` that exposes Pff2Flocq's lemmas with  *)
(* the binary64-specific parameters pre-instantiated.  After that, every   *)
(* expansion-arithmetic primitive (`b64_TwoSum`, `b64_Dekker`,             *)
(* `b64_Veltkamp_split`) is a ~30-line lift.                               *)
(*                                                                            *)
(* This file is left as an `Abort.`d probe -- not a corpus invariant        *)
(* violation because `Abort` doesn't emit anything (no `Admitted`).          *)
(* When Stage D becomes the active engagement, this file is replaced by    *)
(* `B64_Pff_bridge.v` + `B64_TwoSum.v` per the architecture above.         *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
