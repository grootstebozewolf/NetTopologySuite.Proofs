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
From Stdlib Require Import Lra.
From Stdlib Require Import Bool.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.
From Flocq Require Import Pff.Pff2Flocq.

From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import B64_bridge.
From NTS.Proofs.Flocq  Require Import Orient_b64_exact.

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
(* Veltkamp splitting constant: 2^27 + 1, exactly representable in binary64. *)
(* Used inside Dekker's TwoProduct as the multiplier for the precision split.*)
(* -------------------------------------------------------------------------- *)

Definition b64_veltkamp_C : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64
    mode_NE (2^27 + 1)%Z 0%Z false.

Lemma b64_veltkamp_C_R :
  Binary.B2R prec emax b64_veltkamp_C = bpow radix2 27 + 1.
Proof.
  unfold b64_veltkamp_C.
  pose proof (Binary.binary_normalize_correct prec emax
                prec_gt_0_b64 prec_lt_emax_b64 mode_NE
                (2^27 + 1)%Z 0%Z false) as H.
  assert (HF2R : F2R (Float radix2 (2^27 + 1)%Z 0%Z) = IZR (2^27 + 1)).
  { unfold F2R; simpl. lra. }
  rewrite HF2R in H.
  assert (Hround : Generic_fmt.round radix2 (SpecFloat.fexp prec emax)
                    (round_mode mode_NE) (IZR (2^27 + 1)%Z)
                  = IZR (2^27 + 1)%Z).
  { apply Generic_fmt.round_generic;
      [apply valid_rnd_round_mode |].
    apply generic_format_IZR_le_bpow_prec. unfold prec; lia. }
  rewrite Hround in H.
  assert (Hbnd : Rabs (IZR (2^27 + 1)) < bpow radix2 emax).
  { rewrite <- abs_IZR.
    apply (Rlt_trans _ (bpow radix2 53)).
    - rewrite bpow_radix2_eq_IZR_pow by lia.
      apply IZR_lt. lia.
    - apply bpow_lt; unfold emax; lia. }
  apply Rlt_bool_true in Hbnd. rewrite Hbnd in H.
  destruct H as [HB2R _].
  rewrite HB2R.
  rewrite plus_IZR. rewrite <- bpow_radix2_eq_IZR_pow by lia.
  simpl. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Dekker's TwoProduct: x*y = r + t exactly (under an underflow precondition).*)
(* -------------------------------------------------------------------------- *)

Definition b64_Dekker (x y : binary64) : binary64 * binary64 :=
  let px := b64_mult x b64_veltkamp_C in
  let qx := b64_minus x px in
  let hx := b64_plus qx px in
  let tx := b64_minus x hx in
  let py := b64_mult y b64_veltkamp_C in
  let qy := b64_minus y py in
  let hy := b64_plus qy py in
  let ty := b64_minus y hy in
  let x1y1 := b64_mult hx hy in
  let x1y2 := b64_mult hx ty in
  let x2y1 := b64_mult tx hy in
  let x2y2 := b64_mult tx ty in
  let r := b64_mult x y in
  let t1 := b64_minus x1y1 r in
  let t2 := b64_plus t1 x1y2 in
  let t3 := b64_plus t2 x2y1 in
  let t4 := b64_plus t3 x2y2 in
  (r, t4).

(* The 16 safety preconditions, one per b64 op.  Bookkeeping-dense but       *)
(* mechanically deriveable from input magnitude bounds for typical NTS      *)
(* use (|coord| <= 2^25 => all intermediates < bpow 52, safely finite).     *)
Definition b64_Dekker_safe (x y : binary64) : Prop :=
  let px := b64_mult x b64_veltkamp_C in
  let qx := b64_minus x px in
  let hx := b64_plus qx px in
  let tx := b64_minus x hx in
  let py := b64_mult y b64_veltkamp_C in
  let qy := b64_minus y py in
  let hy := b64_plus qy py in
  let ty := b64_minus y hy in
  let x1y1 := b64_mult hx hy in
  let x1y2 := b64_mult hx ty in
  let x2y1 := b64_mult tx hy in
  let x2y2 := b64_mult tx ty in
  let r := b64_mult x y in
  let t1 := b64_minus x1y1 r in
  let t2 := b64_plus t1 x1y2 in
  let t3 := b64_plus t2 x2y1 in
  b64_safe Rmult x b64_veltkamp_C /\         (* px *)
  b64_safe Rminus x px /\                    (* qx *)
  b64_safe Rplus qx px /\                    (* hx *)
  b64_safe Rminus x hx /\                    (* tx *)
  b64_safe Rmult y b64_veltkamp_C /\         (* py *)
  b64_safe Rminus y py /\                    (* qy *)
  b64_safe Rplus qy py /\                    (* hy *)
  b64_safe Rminus y hy /\                    (* ty *)
  b64_safe Rmult hx hy /\                    (* x1y1 *)
  b64_safe Rmult hx ty /\                    (* x1y2 *)
  b64_safe Rmult tx hy /\                    (* x2y1 *)
  b64_safe Rmult tx ty /\                    (* x2y2 *)
  b64_safe Rmult x y /\                      (* r *)
  b64_safe Rminus x1y1 r /\                  (* t1 *)
  b64_safe Rplus t1 x1y2 /\                  (* t2 *)
  b64_safe Rplus t2 x2y1 /\                  (* t3 *)
  b64_safe Rplus t3 (b64_mult tx ty).         (* t4 *)

(* b64_Dekker_correct -- TANGENT documented, deferred to follow-up slice.    *)
(*                                                                            *)
(* The 16-rewrite chain after `unfold b64_Dekker; cbv zeta` runs into TWO   *)
(* compounding issues that I empirically validated:                          *)
(*                                                                            *)
(*   1. Outside-in rewrite ordering doesn't fully propagate even with        *)
(*      `repeat (... !rewrite ...)`.  Some `B2R (b64_plus ...)` occurrences *)
(*      inside nested b64 operations never become exposed because the path *)
(*      to expose them requires firing rewrites in a specific dependency-  *)
(*      ordered sequence that the `repeat` heuristic doesn't find.          *)
(*                                                                            *)
(*   2. Pff2Flocq.Dekker uses `round_flt (-r + x1y1)` for t1 (note the `-r *)
(*      first` order); the natural b64 definition uses `b64_minus x1y1 r`. *)
(*      The two expressions are equal under `Rplus_comm` but NOT under     *)
(*      Coq's syntactic rewrite unification.  Aligning them needs a        *)
(*      `replace` step + ring-style normalization at every t-level.        *)
(*                                                                            *)
(* These are bounded but unpleasant.  Empirical effort spent: 30 min on    *)
(* three failed proof attempts (single-fire rewrites, !-rewrites, repeat   *)
(* with `||`).  Realistic resolution: ~2-3 more hours of careful           *)
(* `replace`-based alignment + a custom Ltac to thread the rewrites.       *)
(*                                                                            *)
(* The Definition + safety predicate are kept; the proof is the next       *)
(* slice.  The SPEC is recorded below for API documentation.                *)
(* -------------------------------------------------------------------------- *)

Definition b64_Dekker_correct_statement : Prop :=
  forall x y : binary64,
    b64_Dekker_safe x y ->
    (Binary.B2R prec emax x * Binary.B2R prec emax y = 0
     \/ bpow radix2 (3 - emax - prec + 2 * prec - 1)
        <= Rabs (Binary.B2R prec emax x * Binary.B2R prec emax y)) ->
    let '(r, t) := b64_Dekker x y in
    Binary.B2R prec emax x * Binary.B2R prec emax y
      = Binary.B2R prec emax r + Binary.B2R prec emax t.
(*                                                                            *)
(* The 16-rewrite chain after `unfold b64_Dekker + cbv zeta` does NOT       *)
(* propagate cleanly outside-in OR inside-out.  Concrete failure:           *)
(*                                                                            *)
(*   After rewriting HBpx, HBpy (substituting `B2R (b64_mult x C)` to      *)
(*   `round(B2R x * (bpow 27 + 1))` after `b64_veltkamp_C_R`), the         *)
(*   subsequent `rewrite HBhy` fails because its LHS pattern               *)
(*     `B2R (b64_plus (b64_minus y (b64_mult y b64_veltkamp_C))            *)
(*                    (b64_mult y b64_veltkamp_C))`                        *)
(*   is structurally NOT in the goal -- the inner `b64_mult y b64_veltkamp_C`*)
(*   instances are *unchanged* by HBpy (which only touches B2R-wrapped     *)
(*   instances), but Coq's unifier still won't match because the goal has *)
(*   them at a different syntactic location than HBhy expects.             *)
(*                                                                            *)
(* Resolving this requires:                                                  *)
(*   (a) `rewrite ... in HB*` to PROPAGATE the substitutions through each  *)
(*       hypothesis BEFORE rewriting the goal -- threading 16 rewrites     *)
(*       through 16 hypotheses, O(n^2);                                    *)
(*   (b) OR using `change` to pre-align b64_veltkamp_C to bpow 27 + 1 in   *)
(*       the goal early so the rewrites all see the same form;             *)
(*   (c) OR proving each step's B2R via a custom Lemma and threading them.  *)
(*                                                                            *)
(* Realistic effort: 1-2 hours of careful debug + restructure.  The proof  *)
(* IS bounded but the bookkeeping is genuinely non-trivial -- the          *)
(* "trivial mechanical" framing in the previous commit was OVERSOLD.       *)
(*                                                                            *)
(* This is the legitimate hardness of Dekker that the original audit       *)
(* warned about, just at a finer granularity than the audit suggested:     *)
(* not "novel proofs" but "Coq let-zeta + rewrite ordering puzzles" at     *)
(* 16-deep nested structure.                                                *)
(*                                                                            *)
(* The Definition + safety predicate are kept in the file; the proof       *)
(* statement is recorded as the spec of a follow-up slice.                  *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions Z_even_opp.
Print Assumptions b64_choice_sym.
Print Assumptions b64_Fast2Sum_correct.
Print Assumptions b64_TwoSum_correct.
Print Assumptions b64_veltkamp_C_R.

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
