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

(* b64_Dekker_correct: fourth attempt with `change` + `replace`.            *)

(* Helper: round of (a - b) equals round of (-b + a). *)
Lemma round_b64_minus_swap :
  forall a b : R,
    round radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64) (a - b)
    = round radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64)
        (- b + a).
Proof. intros; f_equal; ring. Qed.

Theorem b64_Dekker_correct :
  forall x y : binary64,
    b64_Dekker_safe x y ->
    (Binary.B2R prec emax x * Binary.B2R prec emax y = 0
     \/ bpow radix2 (3 - emax - prec + 2 * prec - 1)
        <= Rabs (Binary.B2R prec emax x * Binary.B2R prec emax y)) ->
    let '(r, t) := b64_Dekker x y in
    Binary.B2R prec emax x * Binary.B2R prec emax y
      = Binary.B2R prec emax r + Binary.B2R prec emax t.
Proof.
  intros x y Hsafe Hund.
  unfold b64_Dekker. cbv zeta.
  unfold b64_Dekker_safe in Hsafe. cbv zeta in Hsafe.
  destruct Hsafe as
    [Hpx [Hqx [Hhx [Htx [Hpy [Hqy [Hhy [Hty
     [Hx1y1 [Hx1y2 [Hx2y1 [Hx2y2 [Hr [Ht1 [Ht2 [Ht3 Ht4]]]]]]]]]]]]]]]].
  pose proof (b64_mult_correct  _ _ Hpx)  as [HBpx _].
  pose proof (b64_minus_correct _ _ Hqx)  as [HBqx _].
  pose proof (b64_plus_correct  _ _ Hhx)  as [HBhx _].
  pose proof (b64_minus_correct _ _ Htx)  as [HBtx _].
  pose proof (b64_mult_correct  _ _ Hpy)  as [HBpy _].
  pose proof (b64_minus_correct _ _ Hqy)  as [HBqy _].
  pose proof (b64_plus_correct  _ _ Hhy)  as [HBhy _].
  pose proof (b64_minus_correct _ _ Hty)  as [HBty _].
  pose proof (b64_mult_correct  _ _ Hx1y1) as [HBx1y1 _].
  pose proof (b64_mult_correct  _ _ Hx1y2) as [HBx1y2 _].
  pose proof (b64_mult_correct  _ _ Hx2y1) as [HBx2y1 _].
  pose proof (b64_mult_correct  _ _ Hx2y2) as [HBx2y2 _].
  pose proof (b64_mult_correct  _ _ Hr)   as [HBr _].
  pose proof (b64_minus_correct _ _ Ht1)  as [HBt1 _].
  pose proof (b64_plus_correct  _ _ Ht2)  as [HBt2 _].
  pose proof (b64_plus_correct  _ _ Ht3)  as [HBt3 _].
  pose proof (b64_plus_correct  _ _ Ht4)  as [HBt4 _].
  rewrite b64_veltkamp_C_R in HBpx, HBpy.
  rewrite HBpx in HBqx, HBhx.
  rewrite HBpy in HBqy, HBhy.
  rewrite HBqx in HBhx.
  rewrite HBqy in HBhy.
  rewrite HBhx in HBtx, HBx1y1, HBx1y2.
  rewrite HBhy in HBty, HBx1y1, HBx2y1.
  rewrite HBtx in HBx2y1, HBx2y2.
  rewrite HBty in HBx1y2, HBx2y2.
  rewrite HBr in HBt1.
  rewrite HBx1y1 in HBt1.
  (* At this point HBt1 has the t1 in `B2R x1y1 - B2R r` form.  Swap to     *)
  (* match Pff's `- B2R r + B2R x1y1` form via the helper.                 *)
  rewrite round_b64_minus_swap in HBt1.
  rewrite HBt1 in HBt2.
  rewrite HBx1y2 in HBt2.
  rewrite HBt2 in HBt3.
  rewrite HBx2y1 in HBt3.
  rewrite HBt3 in HBt4.
  rewrite HBx2y2 in HBt4.
  rewrite HBt4, HBr.
  pose proof (Binary.generic_format_B2R prec emax x) as FxR.
  pose proof (Binary.generic_format_B2R prec emax y) as FyR.
  pose proof (Dekker radix2 (3 - emax - prec)%Z prec b64_choice
                ltac:(unfold prec; lia) ltac:(unfold prec, emax; lia)
                (Binary.B2R prec emax x) (Binary.B2R prec emax y)
                FxR FyR (or_introl eq_refl)) as [HDekker_exact _].
  specialize (HDekker_exact Hund).
  change (FLT_exp (3 - emax - prec) prec) with (SpecFloat.fexp prec emax) in *.
  change (Znearest b64_choice) with (round_mode mode_b64) in *.
  change (bpow radix2 (prec - Z.div2 prec)) with (bpow radix2 27) in *.
  exact HDekker_exact.
Qed.
(*                                                                            *)
(* Three attempts logged.  The chain-rewrites-in-hypotheses approach WORKS    *)
(* (attempt 3 cleanly built up HBt4 with the fully expanded R-side           *)
(* expression).  The remaining friction is the GOAL-side comparison with    *)
(* Pff's Dekker conclusion.                                                  *)
(*                                                                            *)
(* The b64 chain and the Pff chain differ in ONE specific way:               *)
(*                                                                            *)
(*   t1 in b64:  round_b64 (B2R x1y1 - B2R r)                                *)
(*   t1 in Pff:  round_flt (- B2R r + B2R x1y1)                              *)
(*                                                                            *)
(* (Plus three syntactic name differences that are definitionally equal:    *)
(*  `SpecFloat.fexp prec emax` = `FLT_exp (3 - emax - prec) prec`;          *)
(*  `round_mode mode_b64` = `Znearest b64_choice`;                          *)
(*  `bpow radix2 27` = `bpow radix2 (prec - Z.div2 prec)`.)                 *)
(*                                                                            *)
(* `repeat f_equal` over-peels and creates ~14 nonsense subgoals (because  *)
(* it doesn't know when to stop -- it descends through every round/+ in    *)
(* the chain trying to make things equal).                                  *)
(*                                                                            *)
(* The bounded resolutions:                                                  *)
(*                                                                            *)
(*  Option A.  Define `b64_neg r := Binary.Bopp prec emax nan_h r`, then    *)
(*    redefine `t1 := b64_plus (b64_neg r) x1y1`.  This makes b64 match    *)
(*    Pff exactly at the t1 level.  ~30 line refactor of `b64_Dekker`.    *)
(*                                                                            *)
(*  Option B.  Prove a helper                                                *)
(*    `Lemma round_b64_minus_swap : round (a - b) = round (- b + a)`        *)
(*    by `f_equal; ring`.  Apply it at the t1 occurrence inside the        *)
(*    chain via `rewrite (round_b64_minus_swap (B2R x1y1) (B2R r))`.       *)
(*    Then align FLT_exp/SpecFloat.fexp via `change`.  ~20 lines.          *)
(*                                                                            *)
(*  Option C.  Replace `repeat f_equal` with a CONTROLLED cascade:         *)
(*    `f_equal; [reflexivity | f_equal; [...| f_equal; ring]]`.  Manually  *)
(*    threading through the round nesting.  ~40 lines.                     *)
(*                                                                            *)
(* All three are bounded (~1-2 hours).  Each is its own mini-engagement;    *)
(* dispatching to one of them is the next slice's first decision.          *)
(*                                                                            *)
(* The Definition + safety predicate ARE in this file (they compile).      *)
(* The SPEC of the deferred theorem is recorded below.  This is genuinely  *)
(* where Dekker stops being "trivial bookkeeping" -- the deep nested-round *)
(* alignment with Pff's syntactic forms is REAL friction, not imagined.   *)
(* -------------------------------------------------------------------------- *)

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
(* b64_TwoSum_nonoverlap -- the lemma that unlocks sign_of_expansion_correct  *)
(* for output of actual TwoSum chains in Stage D.                             *)
(*                                                                            *)
(* Without this, sign_of_expansion_correct is unusable on Stage D output:    *)
(* it requires nonoverlap_strict which holds INSIDE the algorithm but isn't  *)
(* provable without a specific magnitude argument about TwoSum's `e`.        *)
(* -------------------------------------------------------------------------- *)

Theorem b64_TwoSum_nonoverlap :
  forall x y : binary64,
    b64_safe Rplus  x y ->
    b64_safe Rminus (b64_plus x y) x ->
    b64_safe Rminus (b64_plus x y) (b64_minus (b64_plus x y) x) ->
    b64_safe Rminus x
      (b64_minus (b64_plus x y) (b64_minus (b64_plus x y) x)) ->
    b64_safe Rminus y (b64_minus (b64_plus x y) x) ->
    b64_safe Rplus
      (b64_minus x
        (b64_minus (b64_plus x y) (b64_minus (b64_plus x y) x)))
      (b64_minus y (b64_minus (b64_plus x y) x)) ->
    let '(s, e) := b64_TwoSum x y in
    Rabs (Binary.B2R prec emax e)
      <= ulp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax s) / 2.
Proof.
  intros x y Hsa Hsxp Hsaxp Hsdx Hsdy Hsb.
  pose proof (b64_TwoSum_correct x y Hsa Hsxp Hsaxp Hsdx Hsdy Hsb) as HTS.
  unfold b64_TwoSum in HTS.
  cbv beta iota zeta in HTS.
  unfold b64_TwoSum. cbv beta iota zeta.
  pose proof (b64_plus_correct x y Hsa) as [HBs _].
  pose proof (@error_le_half_ulp_round radix2 (SpecFloat.fexp prec emax)
                (fexp_correct prec emax prec_gt_0_b64)
                (fexp_monotone prec emax)
                (fun z => negb (Z.even z))
                (Binary.B2R prec emax x + Binary.B2R prec emax y)) as Herr.
  change (Znearest (fun z => negb (Z.even z)))
    with (round_mode mode_b64) in Herr.
  rewrite <- HBs in Herr.
  match goal with
  | |- Rabs ?e <= _ =>
      replace e with
        (Binary.B2R prec emax x + Binary.B2R prec emax y
         - Binary.B2R prec emax (b64_plus x y))
        by lra
  end.
  rewrite Rabs_minus_sym.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* b64_Dekker_nonoverlap.  Parallel to b64_TwoSum_nonoverlap: the error term *)
(* of Dekker's TwoProduct is bounded by half a ulp of the rounded product.  *)
(*                                                                            *)
(* Reuses b64_Dekker_correct's exact equality (x*y = B2R r + B2R t under     *)
(* safety + underflow), so the error term is B2R x * B2R y - B2R r where    *)
(* r = b64_mult x y.  Apply `error_le_half_ulp_round` to that residual:     *)
(* the half-ulp bound holds on the rounded value, which is exactly B2R r.   *)
(* -------------------------------------------------------------------------- *)

Theorem b64_Dekker_nonoverlap :
  forall x y : binary64,
    b64_Dekker_safe x y ->
    (Binary.B2R prec emax x * Binary.B2R prec emax y = 0
     \/ bpow radix2 (3 - emax - prec + 2 * prec - 1)
        <= Rabs (Binary.B2R prec emax x * Binary.B2R prec emax y)) ->
    let '(r, t) := b64_Dekker x y in
    Rabs (Binary.B2R prec emax t)
      <= ulp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax r) / 2.
Proof.
  intros x y Hsafe Hund.
  pose proof (b64_Dekker_correct x y Hsafe Hund) as HDC.
  unfold b64_Dekker in HDC.
  cbv beta iota zeta in HDC.
  unfold b64_Dekker. cbv beta iota zeta.
  destruct Hsafe as
    [_ [_ [_ [_ [_ [_ [_ [_
     [_ [_ [_ [_ [Hr [_ [_ [_ _]]]]]]]]]]]]]]]].
  pose proof (b64_mult_correct x y Hr) as [HBr _].
  pose proof (@error_le_half_ulp_round radix2 (SpecFloat.fexp prec emax)
                (fexp_correct prec emax prec_gt_0_b64)
                (fexp_monotone prec emax)
                (fun z => negb (Z.even z))
                (Binary.B2R prec emax x * Binary.B2R prec emax y)) as Herr.
  change (Znearest (fun z => negb (Z.even z)))
    with (round_mode mode_b64) in Herr.
  rewrite <- HBr in Herr.
  (* From HDC:  B2R x * B2R y = B2R (b64_mult x y) + B2R t.                  *)
  (* So       B2R t = B2R x * B2R y - B2R (b64_mult x y).                    *)
  match goal with
  | |- Rabs ?e <= _ =>
      replace e with
        (Binary.B2R prec emax x * Binary.B2R prec emax y
         - Binary.B2R prec emax (b64_mult x y))
        by lra
  end.
  rewrite Rabs_minus_sym.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* b64_TwoSum_chain3.  Two chained TwoSums representing the exact sum of     *)
(* three binary64 values as a 3-component tuple `(s2, e2, e1)`.              *)
(*                                                                            *)
(* Algorithm:                                                                  *)
(*   (s1, e1) := b64_TwoSum a b   -- s1 + e1 = a + b exactly                 *)
(*   (s2, e2) := b64_TwoSum s1 c  -- s2 + e2 = s1 + c exactly                *)
(*   Result: (s2, e2, e1)          -- s2 + e2 + e1 = a + b + c exactly       *)
(*                                                                            *)
(* This file proves SUM correctness (the equality).  Nonoverlap of the       *)
(* resulting triple `[s2; e2; e1]` is the tangent documented in              *)
(* docs/stage-d-feasibility.md (2026-05-16 update) and is NOT proved here.  *)
(* The triple under naive ordering is not `nonoverlap_strict` in general;   *)
(* establishing nonoverlap requires either an explicit algorithmic           *)
(* re-ordering (Shewchuk's expansion-sum merge) or a magnitude-tracking      *)
(* invariant that this lemma does not need.                                  *)
(* -------------------------------------------------------------------------- *)

Definition b64_TwoSum_chain3 (a b c : binary64) : binary64 * binary64 * binary64 :=
  let '(s1, e1) := b64_TwoSum a b in
  let '(s2, e2) := b64_TwoSum s1 c in
  (s2, e2, e1).

(* Safety predicate for a single `b64_TwoSum x y` -- the six per-operation  *)
(* `b64_safe` conjuncts packaged as one Prop.  Used by the chain_n          *)
(* compositions below to keep their preconditions compact.                    *)
Definition b64_TwoSum_safe (x y : binary64) : Prop :=
  b64_safe Rplus  x y /\
  b64_safe Rminus (b64_plus x y) x /\
  b64_safe Rminus (b64_plus x y) (b64_minus (b64_plus x y) x) /\
  b64_safe Rminus x
    (b64_minus (b64_plus x y) (b64_minus (b64_plus x y) x)) /\
  b64_safe Rminus y (b64_minus (b64_plus x y) x) /\
  b64_safe Rplus
    (b64_minus x
      (b64_minus (b64_plus x y) (b64_minus (b64_plus x y) x)))
    (b64_minus y (b64_minus (b64_plus x y) x)).

(* Chain composition's safety: a TwoSum on `(a, b)` followed by a TwoSum on *)
(* `(s1, c)` where `s1 = b64_plus a b`.                                     *)
Definition b64_TwoSum_chain3_safe (a b c : binary64) : Prop :=
  b64_TwoSum_safe a b /\
  b64_TwoSum_safe (b64_plus a b) c.

Theorem b64_TwoSum_chain3_correct :
  forall a b c : binary64,
    b64_TwoSum_chain3_safe a b c ->
    let '(s2, e2, e1) := b64_TwoSum_chain3 a b c in
    Binary.B2R prec emax s2 + Binary.B2R prec emax e2 + Binary.B2R prec emax e1
      = Binary.B2R prec emax a + Binary.B2R prec emax b + Binary.B2R prec emax c.
Proof.
  intros a b c Hsafe.
  destruct Hsafe as [Hsab Hsbc].
  unfold b64_TwoSum_safe in Hsab, Hsbc.
  destruct Hsab as [Hsa1 [Hsb1 [Hsc1 [Hsd1 [Hse1 Hsf1]]]]].
  destruct Hsbc as [Hsa2 [Hsb2 [Hsc2 [Hsd2 [Hse2 Hsf2]]]]].
  pose proof (b64_TwoSum_correct a b Hsa1 Hsb1 Hsc1 Hsd1 Hse1 Hsf1) as HTS1.
  pose proof (b64_TwoSum_correct (b64_plus a b) c
                Hsa2 Hsb2 Hsc2 Hsd2 Hse2 Hsf2) as HTS2.
  unfold b64_TwoSum in HTS1, HTS2.
  cbv beta iota zeta in HTS1, HTS2.
  unfold b64_TwoSum_chain3. unfold b64_TwoSum. cbv beta iota zeta.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* b64_TwoSum_chain4.  Four-element chain via three TwoSums.  Tests whether *)
(* the chain_n pattern scales mechanically beyond chain3.                   *)
(* -------------------------------------------------------------------------- *)

Definition b64_TwoSum_chain4 (a b c d : binary64)
  : binary64 * binary64 * binary64 * binary64 :=
  let '(s1, e1) := b64_TwoSum a b in
  let '(s2, e2) := b64_TwoSum s1 c in
  let '(s3, e3) := b64_TwoSum s2 d in
  (s3, e3, e2, e1).

Definition b64_TwoSum_chain4_safe (a b c d : binary64) : Prop :=
  b64_TwoSum_safe a b /\
  b64_TwoSum_safe (b64_plus a b) c /\
  b64_TwoSum_safe (b64_plus (b64_plus a b) c) d.

Theorem b64_TwoSum_chain4_correct :
  forall a b c d : binary64,
    b64_TwoSum_chain4_safe a b c d ->
    let '(s3, e3, e2, e1) := b64_TwoSum_chain4 a b c d in
    Binary.B2R prec emax s3 + Binary.B2R prec emax e3
      + Binary.B2R prec emax e2 + Binary.B2R prec emax e1
      = Binary.B2R prec emax a + Binary.B2R prec emax b
        + Binary.B2R prec emax c + Binary.B2R prec emax d.
Proof.
  intros a b c d Hsafe.
  destruct Hsafe as [Hsab [Hsbc Hscd]].
  unfold b64_TwoSum_safe in Hsab, Hsbc, Hscd.
  destruct Hsab as [Hsa1 [Hsb1 [Hsc1 [Hsd1 [Hse1 Hsf1]]]]].
  destruct Hsbc as [Hsa2 [Hsb2 [Hsc2 [Hsd2 [Hse2 Hsf2]]]]].
  destruct Hscd as [Hsa3 [Hsb3 [Hsc3 [Hsd3 [Hse3 Hsf3]]]]].
  pose proof (b64_TwoSum_correct a b Hsa1 Hsb1 Hsc1 Hsd1 Hse1 Hsf1) as HTS1.
  pose proof (b64_TwoSum_correct (b64_plus a b) c
                Hsa2 Hsb2 Hsc2 Hsd2 Hse2 Hsf2) as HTS2.
  pose proof (b64_TwoSum_correct (b64_plus (b64_plus a b) c) d
                Hsa3 Hsb3 Hsc3 Hsd3 Hse3 Hsf3) as HTS3.
  unfold b64_TwoSum in HTS1, HTS2, HTS3.
  cbv beta iota zeta in HTS1, HTS2, HTS3.
  unfold b64_TwoSum_chain4. unfold b64_TwoSum. cbv beta iota zeta.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* b64_Dekker_then_TwoSum.  Compose a Dekker on `(a, b)` with a TwoSum on   *)
(* `(r, c)` where `r` is the Dekker's high component.  Returns the          *)
(* 3-element tuple `(s, e, t)` representing `a*b + c` exactly.              *)
(*                                                                            *)
(* Building block for orient2d_exact's product-plus-scalar steps.           *)
(* SUM correctness only; nonoverlap remains the documented tangent.        *)
(* -------------------------------------------------------------------------- *)

Definition b64_Dekker_then_TwoSum (a b c : binary64)
  : binary64 * binary64 * binary64 :=
  let '(r, t) := b64_Dekker a b in
  let '(s, e) := b64_TwoSum r c in
  (s, e, t).

Definition b64_Dekker_then_TwoSum_safe (a b c : binary64) : Prop :=
  b64_Dekker_safe a b /\
  b64_TwoSum_safe (fst (b64_Dekker a b)) c.

Theorem b64_Dekker_then_TwoSum_correct :
  forall a b c : binary64,
    b64_Dekker_then_TwoSum_safe a b c ->
    (Binary.B2R prec emax a * Binary.B2R prec emax b = 0
     \/ bpow radix2 (3 - emax - prec + 2 * prec - 1)
        <= Rabs (Binary.B2R prec emax a * Binary.B2R prec emax b)) ->
    let '(s, e, t) := b64_Dekker_then_TwoSum a b c in
    Binary.B2R prec emax s + Binary.B2R prec emax e + Binary.B2R prec emax t
      = Binary.B2R prec emax a * Binary.B2R prec emax b
        + Binary.B2R prec emax c.
Proof.
  intros a b c Hsafe Hund.
  destruct Hsafe as [Hdek_safe Hts_safe].
  pose proof (b64_Dekker_correct a b Hdek_safe Hund) as HDC.
  unfold b64_TwoSum_safe in Hts_safe.
  destruct Hts_safe as [Hs1 [Hs2 [Hs3 [Hs4 [Hs5 Hs6]]]]].
  pose proof (b64_TwoSum_correct (fst (b64_Dekker a b)) c Hs1 Hs2 Hs3 Hs4 Hs5 Hs6)
    as HTS.
  unfold b64_Dekker_then_TwoSum.
  (* HDC has b64_Dekker pattern; unfold to expose the pair so the let in the *)
  (* goal can reduce against the explicit constructors.                       *)
  unfold b64_Dekker in HDC. cbv beta iota zeta in HDC.
  unfold b64_TwoSum in HTS. cbv beta iota zeta in HTS.
  unfold b64_Dekker, b64_TwoSum. cbv beta iota zeta.
  simpl fst in HTS.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* TANGENT (2026-05-16):                                                      *)
(* `b64_DekkerPair_sum_correct` -- compose two Dekker TwoProducts with         *)
(* chain4 to get an exact 4-element representation of `a*b + c*d` -- attempted *)
(* and hit a tangent at the closing `lra`.                                   *)
(*                                                                            *)
(* HYPOTHESIS THAT FAILED.  Building on chain3 + chain4 + Dekker_correct, the *)
(* 2-Dekker sum should Qed via two applications of Dekker_correct and one    *)
(* application of chain4_correct, combined with `lra`.  The expected friction *)
(* was just bookkeeping (nested safety preconditions).                        *)
(*                                                                            *)
(* WHAT ACTUALLY FAILED.  `chain4_correct`'s statement has the shape         *)
(*                                                                            *)
(*   forall a b c d, safe -> let '(s3, e3, e2, e1) := chain4 a b c d in ...  *)
(*                                                                            *)
(* When `pose proof`-ed, the resulting hypothesis carries the `let '(...) := *)
(* chain4 X Y Z W in ...` shape with X Y Z W bound to specific Dekker        *)
(* outputs (`fst (b64_Dekker a b)`, etc.).  `lra` cannot see through the     *)
(* unreduced let-pair destructure to extract the equation it needs.          *)
(*                                                                            *)
(* Naive attempts to reduce via `cbv beta iota zeta` / `simpl fst` /          *)
(* `unfold b64_Dekker` produced different normalisation between the          *)
(* hypothesis and the goal, leaving `lra` unable to unify the two            *)
(* expressions even though they are extensionally equal.                     *)
(*                                                                            *)
(* WHY THIS IS A REAL TANGENT, NOT JUST BOOKKEEPING.  The friction is the    *)
(* same shape as the chain-composition nonoverlap tangent already documented *)
(* in stage-d-feasibility.md: composing more than two `let`-pair-returning    *)
(* operations creates a normalisation problem that the current proof recipes *)
(* don't handle uniformly.  For sum-correctness this is provable -- the      *)
(* equation is true mathematically -- but writing the proof requires either  *)
(* (a) `remember`/`destruct` on each Dekker output to bind r/t as free vars  *)
(* before `pose proof`-ing chain4_correct, or (b) a different formulation of *)
(* chain4_correct that returns its equation in `forall`-prefix-with-pair-     *)
(* equation-hypothesis style instead of `let`-shape conclusion.               *)
(*                                                                            *)
(* Either fix is mechanical (~30 lines) but is its own slice of work.  Per   *)
(* the red workflow (stop at first tangent, document, don't grind), leaving  *)
(* it here for a future engagement that can pick (a) or (b).                  *)
(*                                                                            *)
(* The TwoSum-only chain3/chain4 sum-correctness lemmas above remain         *)
(* shippable; their proofs work because chain_n_correct's let-shape          *)
(* destructure resolves cleanly when applied to ABSTRACT inputs.  The        *)
(* problem only appears when the inputs are themselves let-shape pairs        *)
(* (i.e., Dekker outputs).                                                    *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions Z_even_opp.
Print Assumptions b64_choice_sym.
Print Assumptions b64_Fast2Sum_correct.
Print Assumptions b64_TwoSum_correct.
Print Assumptions b64_veltkamp_C_R.
Print Assumptions b64_Dekker_correct.
Print Assumptions b64_TwoSum_nonoverlap.
Print Assumptions b64_Dekker_nonoverlap.
Print Assumptions b64_TwoSum_chain3_correct.
Print Assumptions b64_TwoSum_chain4_correct.
Print Assumptions b64_Dekker_then_TwoSum_correct.

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
