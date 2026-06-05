(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Intersect_b64_exact
   ----------------------------------------------------------------------------
   Phase 1 first slice (Scope A): first-stage bit-exactness for the binary64
   intersection-point computation -- the prefix of the Cramer-rule chain
   that lands BEFORE the dividing step.

   Honest scoping note: the headline
       B2R (b64_intersect_point_x ...) = intersect_x_R ...
   does NOT hold on the nose in the integer regime, because the Cramer
   parameter `s = qp0 / den` is generally a non-dyadic rational (e.g.
   `1/3` when `qp0 = 1, den = 3`).  Round-chain identity (Scope B) and
   forward-error bound (Scope C) are queued as follow-up slices and
   documented at the foot of the file.

   What this file ships:

     - Total binary64 projections `b64_intersect_point_x` /
       `b64_intersect_point_y` (return `binary64`, not `option binary64`).
     - Safety predicate `intersect_point_inputs_int_safe` extending the
       existing `intersect_inputs_int_safe` (eight `coord_int_safe`
       premises) with the R-side denominator-non-zero condition.
     - R-side reference expressions: `intersect_param_s`, `intersect_x_R`,
       `intersect_y_R`.
     - First-stage exactness: the two outer orient2d evaluations
       (`qp0`, `qp1`) and the two coordinate differences (`dx`, `dy`)
       are bit-exact integer-valued binary64.
     - `HasIntersect` typeclass + `BPoint` instance: a minimal interface
       (operations + safety predicate, no proof fields) that future
       curve primitives -- e.g. arc-arc intersection with 3-control-point
       triplets -- can implement without forking the predicate layer.

   What this file does NOT ship (deferred -- see footer):

     - Denominator finite + B2R non-zero.  Needs an explicit no-overflow
       bound on `b64_minus qp0 qp1` (the difference of two cross products
       can hit 2^54, just above the 2^prec=2^53 exact-integer subtraction
       range; a bpow-54 chain via `b64_round_abs_le_bpow` discharges it).
     - Round-chain identity for the full `b64_intersect_point_x/y`
       (Scope B).
     - Forward-error bound (Scope C).

   PROOF STATUS
   ============
   - `intersect_point_inputs_int_safe`  -- safety predicate.
   - `b64_intersect_qp0_R` / `qp1_R`    -- two outer orient2d calls are
                                           bit-exact (cross-product on R).
   - `b64_intersect_dx_R` / `dy_R`      -- two coord differences are
                                           bit-exact integers and finite.
   - `cross_R_BP_int_witness`           -- (Scope B.1) cross_R_BP is an
                                           integer of magnitude <= 2^53.
   - `cross_R_BP_abs_le_bpow_53`        -- (Scope B.1) Rabs <= bpow 53.
   - `b64_intersect_qp0_finite` / `qp1_finite`
                                        -- (Scope B.1) the two outer
                                           orient2d calls are finite.
   - `b64_intersect_den_safe`           -- (Scope B.1) the denominator
                                           subtraction is no-overflow safe.
   - `b64_intersect_den_R_round`        -- (Scope B.1) B2R of the
                                           denominator equals b64_round
                                           of the R cross-product
                                           difference; finite.
   - `b64_intersect_den_B2R_nonzero`    -- (Scope B.1) the denominator's
                                           B2R is non-zero, so
                                           b64_div_correct's R-side
                                           premise is discharged.
   - `HasIntersect` typeclass + `BPoint` instance -- curve-extension hook.

   No `Admitted`, no `Axiom`, no `Parameter`.

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

From NTS.Proofs        Require Import Distance Orientation.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import Orientation_b64.
From NTS.Proofs.Flocq  Require Import B64_bridge.
From NTS.Proofs.Flocq  Require Import Orient_b64_R.
From NTS.Proofs.Flocq  Require Import Orient_b64_sound.
From NTS.Proofs.Flocq  Require Import Orient_b64_exact.
From NTS.Proofs.Flocq  Require Import Intersect_b64.
From NTS.Proofs.Flocq  Require Import B64_lib.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* BPoint -> R-side Point bridge.  Duplicated from Intersect_b64.v one-liner *)
(* so the layer stays independent.                                          *)
(* -------------------------------------------------------------------------- *)

(* `BP2P` is imported from `Intersect_b64.v`; the bridge lemma                 *)
(* `cross_R_BP_eq_cross_BP2P` over there carries the same definition.         *)

(* -------------------------------------------------------------------------- *)
(* R-side Cramer's-rule reference expressions.                                *)
(*                                                                            *)
(* Convention: the segment we parameterise is P0->P1, with `s` the parameter *)
(* along it; the segment we test against is Q0->Q1.  Matches the b64 code:  *)
(*    s := orient(Q0,Q1,P0) / (orient(Q0,Q1,P0) - orient(Q0,Q1,P1))         *)
(* -------------------------------------------------------------------------- *)

Definition intersect_param_s (P0 P1 Q0 Q1 : Point) : R :=
  cross Q0 Q1 P0 / (cross Q0 Q1 P0 - cross Q0 Q1 P1).

Definition intersect_x_R (P0 P1 Q0 Q1 : Point) : R :=
  px P0 + intersect_param_s P0 P1 Q0 Q1 * (px P1 - px P0).

Definition intersect_y_R (P0 P1 Q0 Q1 : Point) : R :=
  py P0 + intersect_param_s P0 P1 Q0 Q1 * (py P1 - py P0).

(* -------------------------------------------------------------------------- *)
(* Dovetail with the clean-lane closed form (theories/Intersect.v).           *)
(*                                                                            *)
(* `Intersect.strict_intersection_point A B C D` (the convex combination of   *)
(* C and D at t = cross A B C / (cross A B C - cross A B D)) is the named      *)
(* closed form of *the* proper-crossing intersection point, proved to equal   *)
(* every shared point by `Intersect.strict_intersection_eq_formula`.          *)
(*                                                                            *)
(* `intersect_x_R` / `intersect_y_R` are the exact R-side targets that        *)
(* `b64_intersect_point_{x,y}_forward_error` bound the rounded binary64        *)
(* projections against (and which the oracle's INTERSECT_POINT_XY mode         *)
(* computes).  Our convention runs along P0->P1 using cross(Q0,Q1,.), so with  *)
(* A:=Q0, B:=Q1, C:=P0, D:=P1 the reference IS that closed form -- and it      *)
(* holds UNCONDITIONALLY (no proper-crossing hypothesis), since both sides are *)
(* the same Cramer expression: a pure `ring` identity in the parameter.       *)
(* Hence the forward-error story is stated against the canonical closed-form   *)
(* intersection point, not an ad-hoc Cramer expression.                       *)
(* -------------------------------------------------------------------------- *)

Lemma intersect_x_R_eq_strict_point :
  forall P0 P1 Q0 Q1 : Point,
    intersect_x_R P0 P1 Q0 Q1
      = px (Intersect.strict_intersection_point Q0 Q1 P0 P1).
Proof.
  intros P0 P1 Q0 Q1.
  unfold intersect_x_R, intersect_param_s,
         Intersect.strict_intersection_point, px.
  simpl. ring.
Qed.

Lemma intersect_y_R_eq_strict_point :
  forall P0 P1 Q0 Q1 : Point,
    intersect_y_R P0 P1 Q0 Q1
      = py (Intersect.strict_intersection_point Q0 Q1 P0 P1).
Proof.
  intros P0 P1 Q0 Q1.
  unfold intersect_y_R, intersect_param_s,
         Intersect.strict_intersection_point, py.
  simpl. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Total binary64 projections.                                                *)
(* -------------------------------------------------------------------------- *)

Definition b64_intersect_point_x (P0 P1 Q0 Q1 : BPoint) : binary64 :=
  let qp0 := b64_orient2d Q0 Q1 P0 in
  let qp1 := b64_orient2d Q0 Q1 P1 in
  let den := b64_minus qp0 qp1 in
  let s   := b64_div qp0 den in
  let dx  := b64_minus (bx P1) (bx P0) in
  b64_plus (bx P0) (b64_mult s dx).

Definition b64_intersect_point_y (P0 P1 Q0 Q1 : BPoint) : binary64 :=
  let qp0 := b64_orient2d Q0 Q1 P0 in
  let qp1 := b64_orient2d Q0 Q1 P1 in
  let den := b64_minus qp0 qp1 in
  let s   := b64_div qp0 den in
  let dy  := b64_minus (by_ P1) (by_ P0) in
  b64_plus (by_ P0) (b64_mult s dy).

(* -------------------------------------------------------------------------- *)
(* Safety predicate.                                                          *)
(*                                                                            *)
(* Extends `intersect_inputs_int_safe` (eight `coord_int_safe` premises, at  *)
(* the 2^25 magnitude bound) with the R-side denominator-non-zero condition. *)
(* Cramer's rule needs the latter; it says the two segments are not parallel *)
(* on the chosen projection axis.                                           *)
(* -------------------------------------------------------------------------- *)

Definition intersect_point_inputs_int_safe (P0 P1 Q0 Q1 : BPoint) : Prop :=
  intersect_inputs_int_safe P0 P1 Q0 Q1 /\
  cross_R_BP Q0 Q1 P0 <> cross_R_BP Q0 Q1 P1.

(* -------------------------------------------------------------------------- *)
(* First-stage exactness lemmas: the prefix of the Cramer chain that lands  *)
(* BEFORE the dividing step is bit-exact in the integer regime.             *)
(* -------------------------------------------------------------------------- *)

Lemma b64_intersect_qp0_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (b64_orient2d Q0 Q1 P0)
    = cross_R_BP Q0 Q1 P0.
Proof.
  intros P0 P1 Q0 Q1 [Hint _].
  apply b64_orient2d_exact_for_small_int.
  apply (intersect_inputs_int_safe_Q0Q1P0 P0 P1 Q0 Q1 Hint).
Qed.

Lemma b64_intersect_qp1_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (b64_orient2d Q0 Q1 P1)
    = cross_R_BP Q0 Q1 P1.
Proof.
  intros P0 P1 Q0 Q1 [Hint _].
  apply b64_orient2d_exact_for_small_int.
  apply (intersect_inputs_int_safe_Q0Q1P1 P0 P1 Q0 Q1 Hint).
Qed.

(* The two coordinate differences are bit-exact integers.  Each              *)
(* `coord_int_safe` value is bounded by 2^25, so each difference is bounded *)
(* by 2^26 << 2^prec = 2^53 and the integer subtraction lifts exactly via   *)
(* `b64_minus_int_exact`.                                                    *)
Lemma b64_intersect_dx_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
    = Binary.B2R prec emax (bx P1) - Binary.B2R prec emax (bx P0)
    /\ Binary.is_finite prec emax (b64_minus (bx P1) (bx P0)) = true.
Proof.
  intros P0 P1 Q0 Q1 [Hint _].
  destruct Hint as (HxP0 & _ & HxP1 & _ & _ & _ & _ & _).
  destruct HxP0 as (FxP0 & nxP0 & HxP0R & HxP0b).
  destruct HxP1 as (FxP1 & nxP1 & HxP1R & HxP1b).
  pose proof (b64_minus_int_exact (bx P1) (bx P0) nxP1 nxP0
                FxP1 FxP0 HxP1R HxP0R) as Hexact.
  rewrite HxP1R, HxP0R, <- minus_IZR.
  apply Hexact.
  apply le_2p26_le_2pprec, diff_bound_2p26; assumption.
Qed.

Lemma b64_intersect_dy_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
    = Binary.B2R prec emax (by_ P1) - Binary.B2R prec emax (by_ P0)
    /\ Binary.is_finite prec emax (b64_minus (by_ P1) (by_ P0)) = true.
Proof.
  intros P0 P1 Q0 Q1 [Hint _].
  destruct Hint as (_ & HyP0 & _ & HyP1 & _ & _ & _ & _).
  destruct HyP0 as (FyP0 & nyP0 & HyP0R & HyP0b).
  destruct HyP1 as (FyP1 & nyP1 & HyP1R & HyP1b).
  pose proof (b64_minus_int_exact (by_ P1) (by_ P0) nyP1 nyP0
                FyP1 FyP0 HyP1R HyP0R) as Hexact.
  rewrite HyP1R, HyP0R, <- minus_IZR.
  apply Hexact.
  apply le_2p26_le_2pprec, diff_bound_2p26; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope B.1: denominator round-chain pieces.                                 *)
(*                                                                            *)
(* The denominator `den = b64_minus qp0 qp1` is the gate between Scope A's   *)
(* bit-exact prefix and the rest of the chain (`b64_div`, `b64_mult`,        *)
(* `b64_plus`).  This sub-slice ships the three lemmas about `den` that     *)
(* `b64_div_correct` needs:                                                  *)
(*                                                                            *)
(*   - `b64_intersect_den_safe`            -- the `b64_minus` is no-overflow. *)
(*   - `b64_intersect_den_R_round`         -- B2R(den) = b64_round of the R  *)
(*                                            cross-product difference;     *)
(*                                            and the result is finite.     *)
(*   - `b64_intersect_den_B2R_nonzero`     -- B2R(den) <> 0 in R, so        *)
(*                                            b64_div_correct's premise     *)
(*                                            is satisfied.                  *)
(*                                                                            *)
(* Scope B.2 (next slice): division, multiplication, and addition round-    *)
(* chain pieces composing into the full headline                            *)
(*   `B2R (b64_intersect_point_x ...)`                                       *)
(*    = `b64_round (B2R (bx P0) + b64_round (b64_round (qp0_R / b64_round  *)
(*       (qp0_R - qp1_R)) * (B2R (bx P1) - B2R (bx P0))))`.                  *)
(*                                                                            *)
(* No `B2R = intersect_x_R` claim anywhere in Scope B -- that's Scope C     *)
(* (forward-error bound), NOT exactness.                                    *)
(* -------------------------------------------------------------------------- *)

(* Witness lemma: the cross product is an integer of magnitude at most 2^53. *)
(* Lifts the existing `diff_bound_2p26` / `prod_bound_2p52` / `outer_bound_2p53` *)
(* chain from `Orient_b64_exact.v` to the R side via the cross_R_BP unfold.  *)
Lemma cross_R_BP_int_witness :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    exists n : Z,
      cross_R_BP P0 P1 Q = IZR n /\ (Z.abs n <= 2 ^ 53)%Z.
Proof.
  intros P0 P1 Q (HxP0 & HyP0 & HxP1 & HyP1 & HxQ & HyQ).
  destruct HxP0 as (_ & nxP0 & HxP0R & HxP0b).
  destruct HyP0 as (_ & nyP0 & HyP0R & HyP0b).
  destruct HxP1 as (_ & nxP1 & HxP1R & HxP1b).
  destruct HyP1 as (_ & nyP1 & HyP1R & HyP1b).
  destruct HxQ  as (_ & nxQ  & HxQR  & HxQb).
  destruct HyQ  as (_ & nyQ  & HyQR  & HyQb).
  exists ((nxP1 - nxP0) * (nyQ - nyP0) - (nxQ - nxP0) * (nyP1 - nyP0))%Z.
  split.
  - unfold cross_R_BP.
    rewrite HxP0R, HyP0R, HxP1R, HyP1R, HxQR, HyQR.
    rewrite minus_IZR, mult_IZR, mult_IZR, minus_IZR, minus_IZR, minus_IZR, minus_IZR.
    reflexivity.
  - apply outer_bound_2p53;
      (apply prod_bound_2p52; apply diff_bound_2p26; assumption).
Qed.

Lemma cross_R_BP_abs_le_bpow_53 :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    Rabs (cross_R_BP P0 P1 Q) <= bpow radix2 53.
Proof.
  intros P0 P1 Q Hsafe.
  destruct (cross_R_BP_int_witness P0 P1 Q Hsafe) as [n [Hne Hbd]].
  rewrite Hne, <- abs_IZR.
  apply (Rle_trans _ (IZR (2 ^ 53))).
  - apply IZR_le. exact Hbd.
  - rewrite <- IZR_Zpower by lia. apply Rle_refl.
Qed.

(* Both outer orient2d evaluations are finite (they appear inside `b64_minus` *)
(* in the denominator, so we need this before the b64_minus_correct step).   *)
Lemma b64_intersect_qp0_finite :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.is_finite prec emax (b64_orient2d Q0 Q1 P0) = true.
Proof.
  intros P0 P1 Q0 Q1 [Hint _].
  pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
  pose proof (orient2d_inputs_int_safe_imp_safe _ _ _ Hint0) as Hsafe0.
  destruct Hsafe0 as (_ & _ & _ & _ & _ & _ & Sdet).
  pose proof (b64_minus_correct _ _ Sdet) as [_ Fdet]. exact Fdet.
Qed.

Lemma b64_intersect_qp1_finite :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.is_finite prec emax (b64_orient2d Q0 Q1 P1) = true.
Proof.
  intros P0 P1 Q0 Q1 [Hint _].
  pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
  pose proof (orient2d_inputs_int_safe_imp_safe _ _ _ Hint1) as Hsafe1.
  destruct Hsafe1 as (_ & _ & _ & _ & _ & _ & Sdet).
  pose proof (b64_minus_correct _ _ Sdet) as [_ Fdet]. exact Fdet.
Qed.

(* Triangle-inequality helper.  Not in stdlib under this exact name.        *)
Lemma Rabs_minus_le_add :
  forall a b : R, Rabs (a - b) <= Rabs a + Rabs b.
Proof.
  intros a b.
  replace (a - b) with (a + - b) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp. apply Rle_refl.
Qed.

(* The denominator subtraction is no-overflow safe.  Magnitude argument:    *)
(* |qp0_R - qp1_R| <= 2 * 2^53 = 2^54, and `b64_round_abs_le_bpow` preserves *)
(* the bpow 54 bound on the rounded result, which is << bpow emax.          *)
Lemma b64_intersect_den_safe :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    b64_safe Rminus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  pose proof (b64_intersect_qp0_finite _ _ _ _ Hsafe) as Fqp0.
  pose proof (b64_intersect_qp1_finite _ _ _ _ Hsafe) as Fqp1.
  pose proof (b64_intersect_qp0_R _ _ _ _ Hsafe) as Hqp0R.
  pose proof (b64_intersect_qp1_R _ _ _ _ Hsafe) as Hqp1R.
  destruct Hsafe as [Hint _].
  pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
  pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
  pose proof (cross_R_BP_abs_le_bpow_53 _ _ _ Hint0) as Bqp0R.
  pose proof (cross_R_BP_abs_le_bpow_53 _ _ _ Hint1) as Bqp1R.
  unfold b64_safe. split; [exact Fqp0 | split; [exact Fqp1 | ]].
  apply Rle_lt_trans with (bpow radix2 54);
    [|apply bpow_lt; unfold emax; lia].
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  rewrite Hqp0R, Hqp1R.
  apply Rle_trans with (Rabs (cross_R_BP Q0 Q1 P0) + Rabs (cross_R_BP Q0 Q1 P1)).
  - apply Rabs_minus_le_add.
  - replace (bpow radix2 54) with (bpow radix2 53 + bpow radix2 53)
      by (simpl; lra).
    apply Rplus_le_compat; assumption.
Qed.

(* Denominator: B2R is the rounded R-side difference, and the result is     *)
(* finite.  Direct application of `b64_minus_correct` under the safety just *)
(* proved.                                                                  *)
Lemma b64_intersect_den_R_round :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax
      (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))
    = b64_round (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
    /\ Binary.is_finite prec emax
        (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1)) = true.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  pose proof (b64_intersect_den_safe _ _ _ _ Hsafe) as Hden_safe.
  pose proof (b64_minus_correct _ _ Hden_safe) as [HB2R Hfin].
  rewrite (b64_intersect_qp0_R _ _ _ _ Hsafe) in HB2R.
  rewrite (b64_intersect_qp1_R _ _ _ _ Hsafe) in HB2R.
  split; assumption.
Qed.

(* Denominator non-zero on R.  Integer-difference argument: `qp0_R - qp1_R`  *)
(* is a non-zero integer (from the safety predicate), and `b64_round` of a  *)
(* non-zero integer with magnitude `<= 2^54` is either the exact integer    *)
(* (when `|.| <= 2^53`) or the rounded-to-even neighbour (when in (2^53,   *)
(* 2^54])).  In both cases the rounded value is non-zero, since the nearest  *)
(* representable to a non-zero integer of magnitude `>= 1` is at least 1.    *)
Lemma b64_intersect_den_B2R_nonzero :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax
      (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1)) <> 0.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R _].
  rewrite HB2R. clear HB2R.
  destruct Hsafe as [Hint Hne].
  pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
  pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
  destruct (cross_R_BP_int_witness _ _ _ Hint0) as [n0 [Hn0 _]].
  destruct (cross_R_BP_int_witness _ _ _ Hint1) as [n1 [Hn1 _]].
  rewrite Hn0, Hn1, <- minus_IZR.
  assert (Hne_n : n0 <> n1).
  { intros Heq. apply Hne. rewrite Hn0, Hn1, Heq. reflexivity. }
  assert (Hne_diff : (n0 - n1)%Z <> 0%Z) by lia.
  (* `1` and `-1` are in the binary64 generic_format, so round fixes them. *)
  assert (Hformat_1 : Generic_fmt.generic_format radix2 b64_fexp 1).
  { change 1 with (bpow radix2 0).
    apply generic_format_bpow_b64. unfold emax; lia. }
  assert (Hround_1 : b64_round 1 = 1).
  { apply Generic_fmt.round_generic;
      [apply valid_rnd_round_mode | exact Hformat_1]. }
  assert (Hformat_neg1 : Generic_fmt.generic_format radix2 b64_fexp (-1)).
  { replace (-1) with (- (1)) by ring.
    apply Generic_fmt.generic_format_opp. exact Hformat_1. }
  assert (Hround_neg1 : b64_round (-1) = -1).
  { apply Generic_fmt.round_generic;
      [apply valid_rnd_round_mode | exact Hformat_neg1]. }
  intros Hround_zero.
  assert (Hround_zero_R : b64_round 0 = 0).
  { apply Generic_fmt.round_0. apply valid_rnd_round_mode. }
  destruct (Z.lt_total (n0 - n1) 0) as [Hlt | [Heq | Hgt]].
  - assert (HIZR_le : IZR (n0 - n1) <= -1) by (apply IZR_le; lia).
    pose proof (Generic_fmt.round_le radix2 b64_fexp (round_mode mode_b64)
                  _ _ HIZR_le) as Hr.
    rewrite Hround_neg1 in Hr.
    rewrite Hround_zero in Hr. lra.
  - exfalso. apply Hne_diff. exact Heq.
  - assert (HIZR_ge : 1 <= IZR (n0 - n1)) by (apply IZR_le; lia).
    pose proof (Generic_fmt.round_le radix2 b64_fexp (round_mode mode_b64)
                  _ _ HIZR_ge) as Hr.
    rewrite Hround_1 in Hr.
    rewrite Hround_zero in Hr. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-prep: safety + B2R-round characterisations for the rest of the *)
(* chain (b64_div, b64_mult, b64_plus).  These compose into the round-chain *)
(* identity that Scope B.2 would have shipped explicitly; we get it as a    *)
(* corollary of the C.2-prep lemmas.                                         *)
(*                                                                            *)
(* The order is dictated by the bound-chain: each step needs the previous   *)
(* step's magnitude bound to discharge its no-overflow obligation.          *)
(* -------------------------------------------------------------------------- *)

(* Stronger version of `b64_intersect_den_B2R_nonzero`: B2R(den) has        *)
(* absolute value at least 1 (since the integer cross-difference does).     *)
(* This is the lower bound that `b64_div_correct` needs (combined with     *)
(* B2R(qp0) <= bpow 53 it bounds the rounded division by bpow 53 too).     *)
Lemma b64_intersect_den_B2R_abs_ge_1 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    1 <= Rabs (Binary.B2R prec emax
                (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R _].
  rewrite HB2R. clear HB2R.
  destruct Hsafe as [Hint Hne].
  pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
  pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
  destruct (cross_R_BP_int_witness _ _ _ Hint0) as [n0 [Hn0 _]].
  destruct (cross_R_BP_int_witness _ _ _ Hint1) as [n1 [Hn1 _]].
  rewrite Hn0, Hn1, <- minus_IZR.
  assert (Hne_n : n0 <> n1).
  { intros Heq. apply Hne. rewrite Hn0, Hn1, Heq. reflexivity. }
  assert (Hne_diff : (n0 - n1)%Z <> 0%Z) by lia.
  (* +/-1 are in format, fixed by round. *)
  assert (Hformat_1 : Generic_fmt.generic_format radix2 b64_fexp 1).
  { change 1 with (bpow radix2 0). apply generic_format_bpow_b64. unfold emax; lia. }
  assert (Hround_1 : b64_round 1 = 1).
  { apply Generic_fmt.round_generic;
      [apply valid_rnd_round_mode | exact Hformat_1]. }
  assert (Hformat_neg1 : Generic_fmt.generic_format radix2 b64_fexp (-1)).
  { replace (-1) with (- (1)) by ring.
    apply Generic_fmt.generic_format_opp. exact Hformat_1. }
  assert (Hround_neg1 : b64_round (-1) = -1).
  { apply Generic_fmt.round_generic;
      [apply valid_rnd_round_mode | exact Hformat_neg1]. }
  destruct (Z.lt_total (n0 - n1) 0) as [Hlt | [Heq | Hgt]]; [|contradiction|].
  - assert (HIZR_le : IZR (n0 - n1) <= -1) by (apply IZR_le; lia).
    pose proof (Generic_fmt.round_le radix2 b64_fexp (round_mode mode_b64)
                  _ _ HIZR_le) as Hr.
    rewrite Hround_neg1 in Hr.
    unfold Rabs; destruct (Rcase_abs (b64_round (IZR (n0 - n1)))); lra.
  - assert (HIZR_ge : 1 <= IZR (n0 - n1)) by (apply IZR_le; lia).
    pose proof (Generic_fmt.round_le radix2 b64_fexp (round_mode mode_b64)
                  _ _ HIZR_ge) as Hr.
    rewrite Hround_1 in Hr.
    unfold Rabs; destruct (Rcase_abs (b64_round (IZR (n0 - n1)))); lra.
Qed.

(* Magnitude bound on B2R(b64_minus qp0 qp1).  By `b64_round_abs_le_bpow`   *)
(* applied to the R-difference (|.| <= 2^54).                              *)
Lemma b64_intersect_den_B2R_abs_le_bpow_54 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
           (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1)))
    <= bpow radix2 54.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R _].
  rewrite HB2R. clear HB2R.
  destruct Hsafe as [Hint _].
  pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
  pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
  pose proof (cross_R_BP_abs_le_bpow_53 _ _ _ Hint0) as B0.
  pose proof (cross_R_BP_abs_le_bpow_53 _ _ _ Hint1) as B1.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  eapply Rle_trans; [apply Rabs_minus_le_add|].
  replace (bpow radix2 54) with (bpow radix2 53 + bpow radix2 53)
    by (simpl; lra).
  apply Rplus_le_compat; assumption.
Qed.

(* The Cramer parameter step.  Safety for `b64_div_correct` is the         *)
(* explicit shape (finite operands + nonzero divisor + bound), so we need *)
(* one lemma per premise + the bundle.                                      *)
Lemma b64_intersect_s_R_round :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    Binary.B2R prec emax (b64_div qp0 den)
    = b64_round (Binary.B2R prec emax qp0 / Binary.B2R prec emax den)
    /\ Binary.is_finite prec emax (b64_div qp0 den) = true.
Proof.
  intros P0 P1 Q0 Q1 Hsafe qp0 qp1 den.
  pose proof (b64_intersect_qp0_finite _ _ _ _ Hsafe) as Fqp0.
  pose proof (b64_intersect_qp1_finite _ _ _ _ Hsafe) as Fqp1.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [Hden_R Fden].
  pose proof (b64_intersect_den_B2R_nonzero _ _ _ _ Hsafe) as Hden_ne.
  pose proof (b64_intersect_den_B2R_abs_ge_1 _ _ _ _ Hsafe) as Hden_ge1.
  pose proof (b64_intersect_qp0_R _ _ _ _ Hsafe) as Hqp0R.
  destruct Hsafe as [Hint _].
  pose proof (cross_R_BP_abs_le_bpow_53 _ _ _
                (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint)) as Bqp0.
  rewrite <- Hqp0R in Bqp0.
  (* Bound the rounded quotient: |b64_round (qp0_R / den_R)| <= bpow 53. *)
  assert (Hquot_bnd :
    Rabs (b64_round (Binary.B2R prec emax qp0 / Binary.B2R prec emax den))
      <= bpow radix2 53).
  { apply b64_round_abs_le_bpow; [unfold emax; lia |].
    unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
    apply Rle_trans with (bpow radix2 53 * 1).
    - apply Rmult_le_compat;
        [apply Rabs_pos
        |apply Rlt_le, Rinv_0_lt_compat, Rabs_pos_lt; exact Hden_ne
        |exact Bqp0
        |].
      rewrite <- Rinv_1.
      apply Rinv_le_contravar; [lra | exact Hden_ge1].
    - rewrite Rmult_1_r. apply Rle_refl. }
  assert (Hbnd_lt_emax :
    Rabs (b64_round (Binary.B2R prec emax qp0 / Binary.B2R prec emax den))
      < bpow radix2 emax).
  { eapply Rle_lt_trans; [exact Hquot_bnd|].
    apply bpow_lt. unfold emax; lia. }
  pose proof (b64_div_correct qp0 den Fqp0 Fden Hden_ne Hbnd_lt_emax)
    as [HB2R Hfin]. split; assumption.
Qed.

(* Magnitude bound on B2R(s) = B2R(b64_div qp0 den).  Follows from         *)
(* `b64_intersect_s_R_round` + the bound on the rounded quotient.          *)
Lemma b64_intersect_s_abs_le_bpow_53 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    Rabs (Binary.B2R prec emax (b64_div qp0 den)) <= bpow radix2 53.
Proof.
  intros P0 P1 Q0 Q1 Hsafe qp0 qp1 den.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [HB2R _].
  fold qp0 qp1 den in HB2R. rewrite HB2R.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [_ Fden].
  pose proof (b64_intersect_den_B2R_nonzero _ _ _ _ Hsafe) as Hden_ne.
  pose proof (b64_intersect_den_B2R_abs_ge_1 _ _ _ _ Hsafe) as Hden_ge1.
  pose proof (b64_intersect_qp0_R _ _ _ _ Hsafe) as Hqp0R.
  destruct Hsafe as [Hint _].
  pose proof (cross_R_BP_abs_le_bpow_53 _ _ _
                (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint)) as Bqp0.
  rewrite <- Hqp0R in Bqp0.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
  apply Rle_trans with (bpow radix2 53 * 1); [|rewrite Rmult_1_r; apply Rle_refl].
  apply Rmult_le_compat;
    [apply Rabs_pos
    |apply Rlt_le, Rinv_0_lt_compat, Rabs_pos_lt; exact Hden_ne
    |exact Bqp0
    |].
  rewrite <- Rinv_1. apply Rinv_le_contravar; [lra | exact Hden_ge1].
Qed.

(* The coordinate-difference magnitude bounds.  Each `coord_int_safe` is   *)
(* at most 2^25, so the difference is at most 2^26.                        *)
Lemma b64_intersect_dx_abs_le_bpow_26 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))
    <= bpow radix2 26.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_dx_R _ _ _ _ Hsafe) as [Hdx _].
  rewrite Hdx.
  destruct Hsafe as [(HxP0 & _ & HxP1 & _ & _ & _ & _ & _) _].
  destruct HxP0 as (_ & nxP0 & HxP0R & HxP0b).
  destruct HxP1 as (_ & nxP1 & HxP1R & HxP1b).
  rewrite HxP1R, HxP0R, <- minus_IZR, <- abs_IZR.
  apply (Rle_trans _ (IZR (2 ^ 26))).
  - apply IZR_le. apply diff_bound_2p26; assumption.
  - rewrite <- IZR_Zpower by lia. apply Rle_refl.
Qed.

Lemma b64_intersect_dy_abs_le_bpow_26 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))
    <= bpow radix2 26.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_dy_R _ _ _ _ Hsafe) as [Hdy _].
  rewrite Hdy.
  destruct Hsafe as [(_ & HyP0 & _ & HyP1 & _ & _ & _ & _) _].
  destruct HyP0 as (_ & nyP0 & HyP0R & HyP0b).
  destruct HyP1 as (_ & nyP1 & HyP1R & HyP1b).
  rewrite HyP1R, HyP0R, <- minus_IZR, <- abs_IZR.
  apply (Rle_trans _ (IZR (2 ^ 26))).
  - apply IZR_le. apply diff_bound_2p26; assumption.
  - rewrite <- IZR_Zpower by lia. apply Rle_refl.
Qed.

(* The multiplication step: `b64_mult s dx`.  Safety from |s| <= 2^53,    *)
(* |dx| <= 2^26, so |product| <= 2^79 << 2^emax.                         *)
Lemma b64_intersect_mult_x_safe :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    b64_safe Rmult s dx.
Proof.
  intros P0 P1 Q0 Q1 Hsafe qp0 qp1 den s dx.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [_ Fs].
  fold qp0 qp1 den s in Fs.
  destruct (b64_intersect_dx_R _ _ _ _ Hsafe) as [_ Fdx].
  fold dx in Fdx.
  pose proof (b64_intersect_s_abs_le_bpow_53 _ _ _ _ Hsafe) as Bs.
  fold qp0 qp1 den s in Bs.
  pose proof (b64_intersect_dx_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdx.
  fold dx in Bdx.
  unfold b64_safe. split; [exact Fs | split; [exact Fdx | ]].
  eapply Rle_lt_trans;
    [|apply (bpow_lt radix2 80 emax); unfold emax; lia].
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  rewrite Rabs_mult.
  apply Rle_trans with (bpow radix2 53 * bpow radix2 26);
    [|rewrite <- bpow_plus; replace (53 + 26)%Z with 79%Z by lia;
      apply bpow_le; lia].
  apply Rmult_le_compat; (apply Rabs_pos || assumption).
Qed.

Lemma b64_intersect_mult_y_safe :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    b64_safe Rmult s dy.
Proof.
  intros P0 P1 Q0 Q1 Hsafe qp0 qp1 den s dy.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [_ Fs].
  fold qp0 qp1 den s in Fs.
  destruct (b64_intersect_dy_R _ _ _ _ Hsafe) as [_ Fdy].
  fold dy in Fdy.
  pose proof (b64_intersect_s_abs_le_bpow_53 _ _ _ _ Hsafe) as Bs.
  fold qp0 qp1 den s in Bs.
  pose proof (b64_intersect_dy_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdy.
  fold dy in Bdy.
  unfold b64_safe. split; [exact Fs | split; [exact Fdy | ]].
  eapply Rle_lt_trans;
    [|apply (bpow_lt radix2 80 emax); unfold emax; lia].
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  rewrite Rabs_mult.
  apply Rle_trans with (bpow radix2 53 * bpow radix2 26);
    [|rewrite <- bpow_plus; replace (53 + 26)%Z with 79%Z by lia;
      apply bpow_le; lia].
  apply Rmult_le_compat; (apply Rabs_pos || assumption).
Qed.

(* Magnitude bound on B2R(b64_mult s dx) after rounding: <= bpow 80.       *)
Lemma b64_intersect_mult_x_abs_le_bpow_80 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dx)) <= bpow radix2 80.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_x_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_intersect_s_abs_le_bpow_53 _ _ _ _ Hsafe) as Bs.
  cbv zeta in Bs.
  pose proof (b64_intersect_dx_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdx.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  rewrite Rabs_mult.
  apply Rle_trans with (bpow radix2 53 * bpow radix2 26);
    [apply Rmult_le_compat; (apply Rabs_pos || assumption) |].
  rewrite <- bpow_plus. replace (53 + 26)%Z with 79%Z by lia.
  apply bpow_le; lia.
Qed.

Lemma b64_intersect_mult_y_abs_le_bpow_80 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dy)) <= bpow radix2 80.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_y_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_intersect_s_abs_le_bpow_53 _ _ _ _ Hsafe) as Bs.
  cbv zeta in Bs.
  pose proof (b64_intersect_dy_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdy.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  rewrite Rabs_mult.
  apply Rle_trans with (bpow radix2 53 * bpow radix2 26);
    [apply Rmult_le_compat; (apply Rabs_pos || assumption) |].
  rewrite <- bpow_plus. replace (53 + 26)%Z with 79%Z by lia.
  apply bpow_le; lia.
Qed.

(* Magnitude bound on a `coord_int_safe` binary64: at most bpow 25.        *)
Lemma coord_int_safe_abs_le_bpow_25 :
  forall x : binary64,
    coord_int_safe x ->
    Rabs (Binary.B2R prec emax x) <= bpow radix2 25.
Proof.
  intros x (_ & n & HxR & Hxb).
  rewrite HxR, <- abs_IZR.
  apply (Rle_trans _ (IZR (2 ^ 25))).
  - apply IZR_le. exact Hxb.
  - rewrite <- IZR_Zpower by lia. apply Rle_refl.
Qed.

(* Final plus step.  Safety from |bx P0| <= 2^25, |b64_mult| <= 2^80,    *)
(* so |sum| <= 2^81 << 2^emax.                                            *)
Lemma b64_intersect_plus_x_safe :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    b64_safe Rplus (bx P0) (b64_mult s dx).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof Hsafe as Hsafe'. destruct Hsafe' as [Hint _].
  destruct Hint as (HxP0 & _ & _ & _ & _ & _ & _ & _).
  pose proof (coord_int_safe_abs_le_bpow_25 _ HxP0) as BxP0.
  destruct HxP0 as (FxP0 & _ & _ & _).
  pose proof (b64_intersect_mult_x_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [_ Fm].
  pose proof (b64_intersect_mult_x_abs_le_bpow_80 _ _ _ _ Hsafe) as Bm.
  cbv zeta in Bm.
  unfold b64_safe. split; [exact FxP0 | split; [exact Fm | ]].
  eapply Rle_lt_trans;
    [|apply (bpow_lt radix2 82 emax); unfold emax; lia].
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  eapply Rle_trans;
    [apply Rabs_triang|].
  apply Rle_trans with (bpow radix2 25 + bpow radix2 80);
    [apply Rplus_le_compat; assumption|].
  replace (bpow radix2 82) with (bpow radix2 81 + bpow radix2 81)
    by (simpl; lra).
  apply Rle_trans with (bpow radix2 81 + bpow radix2 81); [|apply Rle_refl].
  apply Rplus_le_compat; apply bpow_le; lia.
Qed.

Lemma b64_intersect_plus_y_safe :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    b64_safe Rplus (by_ P0) (b64_mult s dy).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof Hsafe as Hsafe'. destruct Hsafe' as [Hint _].
  destruct Hint as (_ & HyP0 & _ & _ & _ & _ & _ & _).
  pose proof (coord_int_safe_abs_le_bpow_25 _ HyP0) as ByP0.
  destruct HyP0 as (FyP0 & _ & _ & _).
  pose proof (b64_intersect_mult_y_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [_ Fm].
  pose proof (b64_intersect_mult_y_abs_le_bpow_80 _ _ _ _ Hsafe) as Bm.
  cbv zeta in Bm.
  unfold b64_safe. split; [exact FyP0 | split; [exact Fm | ]].
  eapply Rle_lt_trans;
    [|apply (bpow_lt radix2 82 emax); unfold emax; lia].
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rle_trans with (bpow radix2 25 + bpow radix2 80);
    [apply Rplus_le_compat; assumption|].
  replace (bpow radix2 82) with (bpow radix2 81 + bpow radix2 81)
    by (simpl; lra).
  apply Rle_trans with (bpow radix2 81 + bpow radix2 81); [|apply Rle_refl].
  apply Rplus_le_compat; apply bpow_le; lia.
Qed.

(* HEADLINE of C.2-prep (also gives Scope B.2's round-chain identity as a *)
(* corollary).  Under the integer safety predicate, B2R of the final x   *)
(* coordinate is exactly the four-nested-round expression.                *)
Theorem b64_intersect_point_x_round_chain :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1)
    = b64_round
        (Binary.B2R prec emax (bx P0)
         + b64_round
             (b64_round (cross_R_BP Q0 Q1 P0
                        / b64_round (cross_R_BP Q0 Q1 P0
                                     - cross_R_BP Q0 Q1 P1))
              * (Binary.B2R prec emax (bx P1)
                 - Binary.B2R prec emax (bx P0)))).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_x.
  pose proof (b64_intersect_plus_x_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R. clear HB2R.
  pose proof (b64_intersect_mult_x_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R_m _].
  rewrite HB2R_m. clear HB2R_m.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [HB2R_s _].
  cbv zeta in HB2R_s.
  rewrite HB2R_s. clear HB2R_s.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R_d _].
  rewrite HB2R_d. clear HB2R_d.
  rewrite (b64_intersect_qp0_R _ _ _ _ Hsafe).
  destruct (b64_intersect_dx_R _ _ _ _ Hsafe) as [Hdx _].
  rewrite Hdx.
  reflexivity.
Qed.

Theorem b64_intersect_point_y_round_chain :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1)
    = b64_round
        (Binary.B2R prec emax (by_ P0)
         + b64_round
             (b64_round (cross_R_BP Q0 Q1 P0
                        / b64_round (cross_R_BP Q0 Q1 P0
                                     - cross_R_BP Q0 Q1 P1))
              * (Binary.B2R prec emax (by_ P1)
                 - Binary.B2R prec emax (by_ P0)))).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_y.
  pose proof (b64_intersect_plus_y_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R. clear HB2R.
  pose proof (b64_intersect_mult_y_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R_m _].
  rewrite HB2R_m. clear HB2R_m.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [HB2R_s _].
  cbv zeta in HB2R_s.
  rewrite HB2R_s. clear HB2R_s.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R_d _].
  rewrite HB2R_d. clear HB2R_d.
  rewrite (b64_intersect_qp0_R _ _ _ _ Hsafe).
  destruct (b64_intersect_dy_R _ _ _ _ Hsafe) as [Hdy _].
  rewrite Hdy.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C polish: API-level corollaries callers can use directly.            *)
(*                                                                            *)
(* Finiteness of the result -- the b64 chain under safety never produces NaN *)
(* or Inf.  Magnitude bound on the result -- proven via the round-chain      *)
(* identity + b64_round_abs_le_bpow with the bpow 81 chain we built up.     *)
(*                                                                            *)
(* The TIGHT condition-aware forward-error theorem                            *)
(*   |B2R(b64_intersect_point_x ...) - intersect_x_R ...| <= K * eps          *)
(* where K is explicit in |denominator_R|, is a separate engagement-level    *)
(* slice (Scope C.2-tight; multi-session Flocq forward-error analysis).      *)
(* The existence form below records the bound is finite without committing  *)
(* to a specific K.                                                          *)
(* -------------------------------------------------------------------------- *)

Theorem b64_intersect_point_x_finite :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.is_finite prec emax (b64_intersect_point_x P0 P1 Q0 Q1) = true.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_x.
  pose proof (b64_intersect_plus_x_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [_ Ffin]. exact Ffin.
Qed.

Theorem b64_intersect_point_y_finite :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.is_finite prec emax (b64_intersect_point_y P0 P1 Q0 Q1) = true.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_y.
  pose proof (b64_intersect_plus_y_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [_ Ffin]. exact Ffin.
Qed.

(* Magnitude bound on the final coordinate.  The magnitude chain bounds:    *)
(*   |coord|  <= 2^25                                                       *)
(*   |s · dx| <= 2^79                                                       *)
(*   final = coord + (s · dx), so |final| pre-round <= 2^81;               *)
(*   round preserves bpow 81 bound.                                         *)
Theorem b64_intersect_point_x_abs_le_bpow_81 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1))
    <= bpow radix2 81.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  pose proof Hsafe as Hsafe'.
  unfold b64_intersect_point_x.
  pose proof (b64_intersect_plus_x_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R. clear HB2R.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  eapply Rle_trans; [apply Rabs_triang|].
  destruct Hsafe as [Hint _].
  destruct Hint as (HxP0 & _ & _ & _ & _ & _ & _ & _).
  pose proof (coord_int_safe_abs_le_bpow_25 _ HxP0) as BxP0.
  pose proof (b64_intersect_mult_x_abs_le_bpow_80 _ _ _ _ Hsafe') as Bm.
  cbv zeta in Bm.
  apply Rle_trans with (bpow radix2 25 + bpow radix2 80);
    [apply Rplus_le_compat; assumption|].
  replace (bpow radix2 81) with (bpow radix2 80 + bpow radix2 80)
    by (simpl; lra).
  apply Rplus_le_compat; [apply bpow_le; lia | apply Rle_refl].
Qed.

Theorem b64_intersect_point_y_abs_le_bpow_81 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1))
    <= bpow radix2 81.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_y.
  pose proof (b64_intersect_plus_y_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R. clear HB2R.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  eapply Rle_trans; [apply Rabs_triang|].
  destruct Hsafe as [Hint Hne].
  pose proof (conj Hint Hne) as Hsafe'.
  destruct Hint as (_ & HyP0 & _ & _ & _ & _ & _ & _).
  pose proof (coord_int_safe_abs_le_bpow_25 _ HyP0) as ByP0.
  pose proof (b64_intersect_mult_y_abs_le_bpow_80 _ _ _ _ Hsafe') as Bm.
  cbv zeta in Bm.
  apply Rle_trans with (bpow radix2 25 + bpow radix2 80);
    [apply Rplus_le_compat; assumption|].
  replace (bpow radix2 81) with (bpow radix2 80 + bpow radix2 80)
    by (simpl; lra).
  apply Rplus_le_compat; [apply bpow_le; lia | apply Rle_refl].
Qed.

(* -------------------------------------------------------------------------- *)
(* Phase 1 -- Returns-Some corollary.                                          *)
(*                                                                            *)
(* Under intersect_point_inputs_int_safe + sign_filtered = IntersectPoint,    *)
(* b64_intersect_point commits to `Some _` (the function does not return      *)
(* None on the IntersectPoint branch's inner `b64_compare den zero` check).  *)
(*                                                                            *)
(* Discharges the den-finite + den-B2R-nonzero side conditions in the         *)
(* IntersectPoint branch by composing b64_intersect_den_safe +                *)
(* b64_minus_correct + b64_intersect_den_B2R_nonzero (all Qed-closed in     *)
(* Scope B.1 above).                                                          *)
(* -------------------------------------------------------------------------- *)

Theorem b64_intersect_point_returns_some_when_point :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    b64_intersect_sign_filtered P0 P1 Q0 Q1 = IntersectPoint ->
    exists X : BPoint, b64_intersect_point P0 P1 Q0 Q1 = Some X.
Proof.
  intros P0 P1 Q0 Q1 Hsafe Hpoint.
  unfold b64_intersect_point.
  rewrite Hpoint.
  pose proof (b64_intersect_den_safe P0 P1 Q0 Q1 Hsafe) as Hden_safe.
  pose proof (b64_minus_correct _ _ Hden_safe) as [Hden_R Fden].
  pose proof (b64_intersect_den_B2R_nonzero P0 P1 Q0 Q1 Hsafe) as Hden_nz.
  set (zero := Binary.B754_zero prec emax false).
  assert (Hzero_finite : Binary.is_finite prec emax zero = true) by reflexivity.
  assert (HzeroR : Binary.B2R prec emax zero = 0) by reflexivity.
  unfold b64_compare.
  rewrite (Binary.Bcompare_correct prec emax _ _ Fden Hzero_finite).
  rewrite HzeroR.
  destruct (Rcompare _ 0) eqn:Hcmp.
  - apply Rcompare_Eq_inv in Hcmp. contradiction.
  - eexists. reflexivity.
  - eexists. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-tight Session 1 -- forward-error bound for layer 1 (denominator).*)
(*                                                                            *)
(* The b64 intersection chain has four nested rounds (from the                *)
(* `b64_intersect_point_x_round_chain` identity):                             *)
(*                                                                            *)
(*   layer 1 -- den   = b64_round (qp0_R - qp1_R)                             *)
(*   layer 2 -- s     = b64_round (qp0_R / den)                               *)
(*   layer 3 -- s*dx  = b64_round (s * (B2R(bx P1) - B2R(bx P0)))             *)
(*   layer 4 -- final = b64_round (B2R(bx P0) + s*dx)                         *)
(*                                                                            *)
(* The Scope C.2-tight goal is the propagated forward-error theorem           *)
(*    |B2R(b64_intersect_point_x ...) - intersect_x_R (BP2P P0) ...|         *)
(*     <= K * eps                                                              *)
(* where `K` is explicit in the input magnitude and the denominator           *)
(* separation.                                                                *)
(*                                                                            *)
(* This session lands LAYER 1: the absolute forward-error bound on the        *)
(* denominator's round.  `qp0_R - qp1_R` is an integer of magnitude <= 2^54,  *)
(* so the round error is bounded by ulp/2 = 2^54 * 2^-52 / 2 = bpow 1.        *)
(* The bound is sharp at the bottom bit: one half-ulp of a maximum-magnitude  *)
(* denominator equals 2 = bpow 1.                                             *)
(* -------------------------------------------------------------------------- *)

(* Shared auxiliary for the Scope C.2-tight cascade: uniform ulp bound at    *)
(* arbitrary magnitude.  Used at n=54 (layer 1), n=53 (layer 2), n=80        *)
(* (layer 3), and n=81 (layer 4).  Subsumes earlier specialised versions     *)
(* introduced during Sessions 1 and 3; subnormal/zero case via ulp_FLT_small,*)
(* normal case via ulp_FLT_le.                                                *)
Lemma b64_ulp_le_at_magnitude_uniform :
  forall (x : R) (n : Z),
    (0 <= n)%Z ->
    Rabs x <= bpow radix2 n ->
    b64_ulp x <= bpow radix2 (n - prec + 1).
Proof.
  intros x n Hn Hle.
  destruct (Rlt_le_dec (Rabs x) (bpow radix2 (b64_emin + prec))) as [Hsmall|Hbig].
  - assert (Hulp_small : b64_ulp x = bpow radix2 b64_emin)
      by (apply (@ulp_FLT_small radix2 b64_emin prec _ x Hsmall)).
    rewrite Hulp_small.
    apply bpow_le. unfold b64_emin, emax, prec; lia.
  - pose proof (ulp_FLT_le radix2 b64_emin prec x) as Hulp.
    assert (Hpre : bpow radix2 (b64_emin + prec - 1) <= Rabs x).
    { apply Rle_trans with (bpow radix2 (b64_emin + prec)); [|exact Hbig].
      apply bpow_le; lia. }
    specialize (Hulp Hpre).
    apply Rle_trans with (Rabs x * bpow radix2 (1 - prec)); [exact Hulp|].
    replace (bpow radix2 (n - prec + 1))
      with (bpow radix2 n * bpow radix2 (1 - prec)).
    + apply Rmult_le_compat_r; [apply bpow_ge_0|exact Hle].
    + rewrite <- bpow_plus. apply f_equal. lia.
Qed.

(* Layer 1 forward-error bound: B2R of the denominator deviates from the     *)
(* exact R-side integer difference by at most bpow 1 = 2.                    *)
Theorem b64_intersect_den_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
            (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))
          - (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= bpow radix2 1.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_error_le_half_ulp_round
                (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)) as Herr.
  eapply Rle_trans; [exact Herr|].
  pose proof (b64_intersect_den_B2R_abs_le_bpow_54 _ _ _ _ Hsafe) as Bden.
  rewrite HB2R in Bden.
  pose proof (b64_ulp_le_at_magnitude_uniform _ 54 ltac:(lia) Bden) as Hulp_le.
  apply Rle_trans
    with (bpow radix2 2 / 2); [|simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra|exact Hulp_le].
Qed.

(* -------------------------------------------------------------------------- *)
(* Tight integer-regime variant of Layer 1.                                   *)
(*                                                                            *)
(* `b64_intersect_den_forward_error` above bounds the denominator rounding   *)
(* error by `bpow 1 = 2` -- derived via output-form half-ulp on a denominator *)
(* with `|den_R| <= bpow 54`, yielding ulp/2 <= bpow 2 / 2 = 2.                *)
(*                                                                            *)
(* The tight integer-regime fact: `qp0_R - qp1_R` is an INTEGER (each         *)
(* cross_R_BP is an integer in the integer regime, per `cross_R_BP_int_witness`),*)
(* with `|.| <= 2^(prec+1) = 2^54`.  Rounding such an integer in binary64    *)
(* introduces an error of at most 1 (exact for |.| <= 2^prec; half-ulp = 1   *)
(* in the strict mid-band; exact at the boundary 2^(prec+1) which is a power *)
(* of 2).  This is 2x tighter than the bpow-1 form above.                    *)
(*                                                                            *)
(* Foundation: `b64_round_IZR_error_le_1` in Orient_b64_exact.v.              *)
(*                                                                            *)
(* The parallel chain below (`_s_carry_error_tight`,                          *)
(* `_mult_x_carry_error_tight`, ..., `_point_x_forward_error_tight`) cites    *)
(* this lemma instead of `b64_intersect_den_forward_error` and propagates    *)
(* the 2x tightening through Layers 2-4 to a tighter headline K constant in  *)
(* the final `_vs_intersect_x_R` corollary.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma b64_intersect_den_error_le_1 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
            (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))
          - (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= 1.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R _].
  rewrite HB2R. clear HB2R.
  destruct Hsafe as [Hint _].
  pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
  pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
  destruct (cross_R_BP_int_witness _ _ _ Hint0) as [n0 [Hn0_eq Hn0_bnd]].
  destruct (cross_R_BP_int_witness _ _ _ Hint1) as [n1 [Hn1_eq Hn1_bnd]].
  rewrite Hn0_eq, Hn1_eq, <- minus_IZR.
  apply b64_round_IZR_error_le_1.
  apply Z.abs_le in Hn0_bnd.
  apply Z.abs_le in Hn1_bnd.
  apply Z.abs_le.
  unfold prec in *. simpl in *. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-tight Session 2 -- denominator-carryover bound for layer 2.      *)
(*                                                                            *)
(* Layer 2 of the b64 intersection chain rounds the EXACT-numerator over     *)
(* ROUNDED-denominator quotient:                                              *)
(*    B2R(s) = b64_round (qp0_R / B2R(den))                                    *)
(*    s_exact = qp0_R / (qp0_R - qp1_R)                                        *)
(*                                                                            *)
(* The full layer-2 forward error decomposes algebraically:                   *)
(*    B2R(s) - s_exact                                                         *)
(*  = (b64_round(qp0_R/den_R) - qp0_R/den_R)              [Delta_round]       *)
(*  + (qp0_R/den_R - qp0_R/den_exact)                      [Delta_carry]       *)
(*                                                                            *)
(* This session lands Delta_carry only -- the pure-R perturbation of the      *)
(* quotient under denominator rounding.  Session 3 lands Delta_round (which   *)
(* needs subnormal-range ulp bookkeeping for b64_round of the division) and  *)
(* composes both into the full layer-2 bound.                                *)
(*                                                                            *)
(* Algebraic identity:                                                        *)
(*    qp0_R / den_R - qp0_R / den_exact                                       *)
(*  = qp0_R * (den_exact - den_R) / (den_R * den_exact)                       *)
(* Bound chain:                                                               *)
(*    |Delta_carry|                                                            *)
(*  <= |qp0_R| * (Session 1 bound) / (|den_R| * |den_exact|)                  *)
(*  <= bpow 53 * bpow 1 / (1 * |den_exact|)                                    *)
(*  =  bpow 54 / |den_exact|.                                                  *)
(*                                                                            *)
(* The 1/|den_exact| factor exposes the classical condition number for the    *)
(* Cramer division step.                                                      *)
(* -------------------------------------------------------------------------- *)

Theorem b64_intersect_s_carry_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (cross_R_BP Q0 Q1 P0
            / Binary.B2R prec emax
                (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= bpow radix2 54
       / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  set (qp0_R := cross_R_BP Q0 Q1 P0).
  set (qp1_R := cross_R_BP Q0 Q1 P1).
  set (den_R := Binary.B2R prec emax
                  (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))).
  set (den_exact := qp0_R - qp1_R).
  (* Step 1: facts about den_R and den_exact. *)
  assert (Hden_exact_ne : den_exact <> 0).
  { unfold den_exact, qp0_R, qp1_R. destruct Hsafe as [_ Hne]. lra. }
  assert (Hden_R_ne : den_R <> 0).
  { unfold den_R. apply (b64_intersect_den_B2R_nonzero _ _ _ _ Hsafe). }
  assert (Hden_R_ge1 : 1 <= Rabs den_R).
  { unfold den_R. apply (b64_intersect_den_B2R_abs_ge_1 _ _ _ _ Hsafe). }
  assert (Hden_exact_ge1 : 1 <= Rabs den_exact).
  { unfold den_exact, qp0_R, qp1_R.
    destruct Hsafe as [Hint Hne].
    pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
    pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
    destruct (cross_R_BP_int_witness _ _ _ Hint0) as [n0 [Hn0 _]].
    destruct (cross_R_BP_int_witness _ _ _ Hint1) as [n1 [Hn1 _]].
    rewrite Hn0, Hn1, <- minus_IZR, <- abs_IZR.
    apply IZR_le.
    assert (Hne_n : n0 <> n1).
    { intros Heq. apply Hne. rewrite Hn0, Hn1, Heq. reflexivity. }
    lia. }
  assert (Hqp0_R_bnd : Rabs qp0_R <= bpow radix2 53).
  { unfold qp0_R.
    destruct Hsafe as [Hint _].
    apply (cross_R_BP_abs_le_bpow_53 _ _ _
             (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint)). }
  assert (Hden_err : Rabs (den_R - den_exact) <= bpow radix2 1).
  { unfold den_R, den_exact, qp0_R, qp1_R.
    apply (b64_intersect_den_forward_error _ _ _ _ Hsafe). }
  (* Step 2: algebraic identity for the perturbation. *)
  assert (Hpos_R : 0 < Rabs den_R) by (apply Rabs_pos_lt; exact Hden_R_ne).
  assert (Hpos_exact : 0 < Rabs den_exact)
    by (apply Rabs_pos_lt; exact Hden_exact_ne).
  replace (qp0_R / den_R - qp0_R / den_exact)
    with (qp0_R * (den_exact - den_R) / (den_R * den_exact))
    by (field; split; assumption).
  (* Step 3: factor Rabs through the division and bound. *)
  unfold Rdiv at 1.
  rewrite Rabs_mult.
  rewrite Rabs_inv.
  rewrite (Rabs_mult qp0_R (den_exact - den_R)).
  rewrite (Rabs_mult den_R den_exact).
  (* Now: |qp0_R| * |den_exact - den_R| / (|den_R| * |den_exact|)               *)
  (*    <= bpow 54 / |den_exact|.                                                *)
  apply Rle_trans
    with ((bpow radix2 53 * bpow radix2 1) / (1 * Rabs den_exact)).
  - apply Rmult_le_compat;
      [ apply Rmult_le_pos; apply Rabs_pos
      | apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; assumption
      |
      | ].
    + (* Numerator: |qp0_R| * |den_exact - den_R| <= bpow 53 * bpow 1. *)
      apply Rmult_le_compat;
        [apply Rabs_pos|apply Rabs_pos|exact Hqp0_R_bnd|].
      replace (Rabs (den_exact - den_R)) with (Rabs (den_R - den_exact))
        by (rewrite <- Rabs_Ropp; f_equal; ring).
      exact Hden_err.
    + (* Denominator inverse: 1/(|den_R| * |den_exact|) <= 1/(1 * |den_exact|). *)
      apply Rinv_le_contravar.
      * rewrite Rmult_1_l. exact Hpos_exact.
      * apply Rmult_le_compat_r; [apply Rlt_le; exact Hpos_exact|exact Hden_R_ge1].
  - (* Simplify constants: bpow 53 * bpow 1 = bpow 54, divide by 1. *)
    rewrite Rmult_1_l.
    apply Rmult_le_compat_r;
      [apply Rlt_le, Rinv_0_lt_compat; exact Hpos_exact|].
    rewrite <- bpow_plus. simpl. apply Rle_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-tight Session 3 -- layer 2 forward-error closure.                *)
(*                                                                            *)
(* Lands Delta_round (the b64_round error on the quotient) and composes it    *)
(* with Session 2's Delta_carry into the full layer-2 forward-error bound.    *)
(*                                                                            *)
(* The Delta_round bound is |b64_round (qp0_R/den_R) - qp0_R/den_R| <= 1.     *)
(* Proof: half-ulp at magnitude <= bpow 53.  Uniform across normal/subnormal  *)
(* /zero regimes via `ulp_FLT_small` (constant ulp = bpow emin in subnormal   *)
(* range and at zero) + `ulp_FLT_le` (relative bound in normal range).        *)
(*                                                                            *)
(* Composition: B2R(b64_div ...) - qp0_R/(qp0_R - qp1_R)                      *)
(*            = Delta_round + Delta_carry                                      *)
(* with |total| <= 1 + bpow 54 / |qp0_R - qp1_R|.                              *)
(* -------------------------------------------------------------------------- *)

(* Delta_round: the b64_round error on the layer-2 quotient.                  *)
Lemma b64_intersect_s_round_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
            (b64_div (b64_orient2d Q0 Q1 P0)
                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                (b64_orient2d Q0 Q1 P1)))
          - cross_R_BP Q0 Q1 P0
            / Binary.B2R prec emax
                (b64_minus (b64_orient2d Q0 Q1 P0)
                           (b64_orient2d Q0 Q1 P1)))
    <= 1.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [HB2R _].
  cbv zeta in HB2R. rewrite HB2R.
  pose proof (b64_intersect_qp0_R _ _ _ _ Hsafe) as Hqp0R.
  rewrite Hqp0R.
  set (qp0_R := cross_R_BP Q0 Q1 P0).
  set (den_R := Binary.B2R prec emax
                  (b64_minus (b64_orient2d Q0 Q1 P0)
                             (b64_orient2d Q0 Q1 P1))).
  pose proof (b64_error_le_half_ulp_round (qp0_R / den_R)) as Herr.
  eapply Rle_trans; [exact Herr|].
  assert (Hbnd : Rabs (b64_round (qp0_R / den_R)) <= bpow radix2 53).
  { pose proof (b64_intersect_s_abs_le_bpow_53 _ _ _ _ Hsafe) as Bs.
    cbv zeta in Bs.
    destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [HB2R2 _].
    cbv zeta in HB2R2.
    rewrite HB2R2 in Bs.
    rewrite (b64_intersect_qp0_R _ _ _ _ Hsafe) in Bs.
    exact Bs. }
  pose proof (b64_ulp_le_at_magnitude_uniform _ 53 ltac:(lia) Hbnd) as Hulp.
  apply Rle_trans with (bpow radix2 1 / 2); [|simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra | exact Hulp].
Qed.

(* Layer 2 full forward-error bound: composition of Delta_round (Session 3)  *)
(* and Delta_carry (Session 2).                                              *)
Theorem b64_intersect_s_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
            (b64_div (b64_orient2d Q0 Q1 P0)
                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                (b64_orient2d Q0 Q1 P1)))
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= 1 + bpow radix2 54
            / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  set (qp0_R := cross_R_BP Q0 Q1 P0).
  set (qp1_R := cross_R_BP Q0 Q1 P1).
  set (den_R := Binary.B2R prec emax
                  (b64_minus (b64_orient2d Q0 Q1 P0)
                             (b64_orient2d Q0 Q1 P1))).
  set (s_R := Binary.B2R prec emax
                (b64_div (b64_orient2d Q0 Q1 P0)
                         (b64_minus (b64_orient2d Q0 Q1 P0)
                                    (b64_orient2d Q0 Q1 P1)))).
  replace (s_R - qp0_R / (qp0_R - qp1_R))
    with ((s_R - qp0_R / den_R) + (qp0_R / den_R - qp0_R / (qp0_R - qp1_R)))
    by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat.
  - apply (b64_intersect_s_round_error _ _ _ _ Hsafe).
  - apply (b64_intersect_s_carry_error _ _ _ _ Hsafe).
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-tight Session 4 -- layer 3 (s * dx) forward error.               *)
(*                                                                            *)
(* Layer 3 of the b64 intersection chain:                                     *)
(*    B2R(b64_mult s dx) = b64_round (B2R(s) * B2R(dx))                       *)
(*                       = b64_round (s_R * dx_R)                              *)
(* where dx_R = B2R(b64_minus (bx P1) (bx P0)) = B2R(bx P1) - B2R(bx P0)      *)
(* (bit-exact under int-safe via `b64_intersect_dx_R`).                       *)
(*                                                                            *)
(* Reference: intersect_param_s * (px P1 - px P0) = s_exact * dx_R            *)
(*    (since px (BP2P P) = B2R(bx P), the same dx_R appears on both sides).   *)
(*                                                                            *)
(* The forward error decomposes:                                              *)
(*    b64_round(s_R * dx_R) - s_exact * dx_R                                  *)
(*  = [b64_round(s_R * dx_R) - s_R * dx_R]              [Delta_round_mul]     *)
(*  + dx_R * (s_R - s_exact)                            [Delta_carry_mul]     *)
(*                                                                            *)
(* Delta_round_mul: half-ulp at magnitude <= bpow 80, so <= bpow 27.          *)
(* Delta_carry_mul: |dx_R| <= bpow 26; Session 3's s_forward_error bound      *)
(*    folds in to give bpow 26 + bpow 80 / |den_exact|.                       *)
(*                                                                            *)
(* Combined: bpow 27 + bpow 26 + bpow 80 / |den_exact|                        *)
(*         <= bpow 28 + bpow 80 / |den_exact|.                                 *)
(* -------------------------------------------------------------------------- *)

(* Delta_round_mul: b64_round error on the layer-3 multiplication. *)
Lemma b64_intersect_mult_x_round_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dx)
          - Binary.B2R prec emax s * Binary.B2R prec emax dx)
    <= bpow radix2 27.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_x_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_error_le_half_ulp_round
                (Binary.B2R prec emax
                   (b64_div (b64_orient2d Q0 Q1 P0)
                            (b64_minus (b64_orient2d Q0 Q1 P0)
                                       (b64_orient2d Q0 Q1 P1)))
                 * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))) as Herr.
  eapply Rle_trans; [exact Herr|].
  assert (Hbnd : Rabs (b64_round
                        (Binary.B2R prec emax
                          (b64_div (b64_orient2d Q0 Q1 P0)
                                   (b64_minus (b64_orient2d Q0 Q1 P0)
                                              (b64_orient2d Q0 Q1 P1)))
                         * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
                 <= bpow radix2 80).
  { pose proof (b64_intersect_mult_x_abs_le_bpow_80 _ _ _ _ Hsafe) as Bm.
    cbv zeta in Bm.
    rewrite HB2R in Bm. exact Bm. }
  pose proof (b64_ulp_le_at_magnitude_uniform _ 80 ltac:(lia) Hbnd) as Hulp.
  apply Rle_trans with (bpow radix2 (80 - prec + 1) / 2);
    [|unfold prec; simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra|exact Hulp].
Qed.

(* Delta_carry_mul: the s-error carried through dx. *)
Lemma b64_intersect_mult_x_carry_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax s * Binary.B2R prec emax dx
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dx)
    <= bpow radix2 26
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  replace (Binary.B2R prec emax
             (b64_div (b64_orient2d Q0 Q1 P0)
                      (b64_minus (b64_orient2d Q0 Q1 P0)
                                 (b64_orient2d Q0 Q1 P1)))
           * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))
    with (Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
          * (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
    by ring.
  rewrite Rabs_mult.
  pose proof (b64_intersect_dx_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdx.
  pose proof (b64_intersect_s_forward_error _ _ _ _ Hsafe) as Bs.
  apply Rle_trans
    with (bpow radix2 26
          * (1 + bpow radix2 54
                 / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Bdx|exact Bs].
  - rewrite Rmult_plus_distr_l, Rmult_1_r.
    apply Rplus_le_compat_l.
    unfold Rdiv.
    rewrite <- Rmult_assoc.
    rewrite <- bpow_plus.
    replace (26 + 54)%Z with 80%Z by lia.
    apply Rle_refl.
Qed.

(* Layer 3 full forward error: composition of Delta_round_mul and             *)
(* Delta_carry_mul, vs the exact reference s_exact * (B2R(bx P1) - B2R(bx P0)).*)
Theorem b64_intersect_mult_x_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dx)
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dx)
    <= bpow radix2 27 + bpow radix2 26
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_x_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_x_carry_error _ _ _ _ Hsafe) as Hcarry.
  cbv zeta in Hcarry.
  replace (Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (bx P1) (bx P0)))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))
    with ((Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (bx P1) (bx P0)))
           - Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))
          + (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rplus_assoc.
  apply Rplus_le_compat; [exact Hround | exact Hcarry].
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-tight Session 5 -- layer 4 (final coordinate) + headline.        *)
(*                                                                            *)
(* Layer 4 of the b64 intersection chain:                                     *)
(*    B2R(b64_intersect_point_x) = b64_round (B2R(bx P0) + B2R(b64_mult s dx)) *)
(*                                                                            *)
(* Reference (the "exact x-coordinate of the intersection point" under        *)
(* int-safe inputs, where px(BP2P P) = B2R(bx P)):                            *)
(*    x_exact := B2R(bx P0) + s_exact * dx_R                                  *)
(* where dx_R = B2R(b64_minus (bx P1) (bx P0)) = B2R(bx P1) - B2R(bx P0).     *)
(*                                                                            *)
(* This equals `intersect_x_R (BP2P P0) ... (BP2P Q1)` up to the bit-exact    *)
(* dx step (Session 6 will link).                                              *)
(*                                                                            *)
(* Decomposition:                                                              *)
(*    B2R(b64_intersect_point_x) - x_exact                                    *)
(*  = b64_round(B2R(bx P0) + mul_R) - (B2R(bx P0) + s_exact * dx_R)           *)
(*  = [b64_round(...) - (B2R(bx P0) + mul_R)]         [Delta_round_plus]      *)
(*  + [mul_R - s_exact * dx_R]                         [Delta_layer3]          *)
(*                                                                            *)
(* Delta_round_plus: half-ulp at magnitude <= bpow 81, so <= bpow 28.         *)
(* Delta_layer3: <= bpow 27 + bpow 26 + bpow 80 / |den_exact|  (Session 4)    *)
(*                                                                            *)
(* Combined: bpow 28 + bpow 27 + bpow 26 + bpow 80 / |den_exact|              *)
(*         <= bpow 29 + bpow 80 / |den_exact|.                                 *)
(*                                                                            *)
(* In K * eps form (eps = bpow(-53)):                                          *)
(*    K(|den_exact|) = bpow 82 + bpow 133 / |den_exact|                       *)
(* deferred to Session 6 (the K * eps restatement + HasIntersect_sound).     *)
(* -------------------------------------------------------------------------- *)

(* Delta_round_plus: b64_round error on the final addition. *)
Lemma b64_intersect_plus_x_round_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax (b64_plus (bx P0) (b64_mult s dx))
          - (Binary.B2R prec emax (bx P0)
             + Binary.B2R prec emax (b64_mult s dx)))
    <= bpow radix2 28.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_plus_x_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_error_le_half_ulp_round
                (Binary.B2R prec emax (bx P0)
                 + Binary.B2R prec emax
                     (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                                   (b64_orient2d Q0 Q1 P1)))
                               (b64_minus (bx P1) (bx P0))))) as Herr.
  eapply Rle_trans; [exact Herr|].
  assert (Hbnd : Rabs (b64_round
                        (Binary.B2R prec emax (bx P0)
                         + Binary.B2R prec emax
                             (b64_mult
                                (b64_div (b64_orient2d Q0 Q1 P0)
                                         (b64_minus (b64_orient2d Q0 Q1 P0)
                                                    (b64_orient2d Q0 Q1 P1)))
                                (b64_minus (bx P1) (bx P0)))))
                 <= bpow radix2 81).
  { pose proof (b64_intersect_point_x_abs_le_bpow_81 _ _ _ _ Hsafe) as Bp.
    unfold b64_intersect_point_x in Bp.
    cbv zeta in Bp.
    rewrite HB2R in Bp. exact Bp. }
  pose proof (b64_ulp_le_at_magnitude_uniform _ 81 ltac:(lia) Hbnd) as Hulp.
  apply Rle_trans with (bpow radix2 (81 - prec + 1) / 2);
    [|unfold prec; simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra|exact Hulp].
Qed.

(* Layer 4 + composition: the headline forward error against the exact       *)
(* reference x_exact = B2R(bx P0) + s_exact * dx_R.                           *)
Theorem b64_intersect_point_x_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1)
          - (Binary.B2R prec emax (bx P0)
             + cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
    <= bpow radix2 29
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_x.
  cbv zeta.
  pose proof (b64_intersect_plus_x_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_x_forward_error _ _ _ _ Hsafe) as Hlayer3.
  cbv zeta in Hlayer3.
  (* Decomposition: result - x_exact = Δ_round_plus + Δ_layer3. *)
  replace (Binary.B2R prec emax
             (b64_plus (bx P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (bx P1) (bx P0))))
           - (Binary.B2R prec emax (bx P0)
              + cross_R_BP Q0 Q1 P0
                / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
                * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
    with ((Binary.B2R prec emax
             (b64_plus (bx P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (bx P1) (bx P0))))
           - (Binary.B2R prec emax (bx P0)
              + Binary.B2R prec emax
                  (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                                (b64_orient2d Q0 Q1 P1)))
                            (b64_minus (bx P1) (bx P0)))))
          + (Binary.B2R prec emax
               (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                  (b64_minus (b64_orient2d Q0 Q1 P0)
                                             (b64_orient2d Q0 Q1 P1)))
                         (b64_minus (bx P1) (bx P0)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
    by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  (* RHS: bpow 29 + bpow 80 / |...| = bpow 28 + (bpow 28 + bpow 80 / |...|). *)
  apply Rle_trans
    with (bpow radix2 28
          + (bpow radix2 27 + bpow radix2 26
             + bpow radix2 80
               / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rplus_le_compat; [exact Hround | exact Hlayer3].
  - (* bpow 28 + bpow 27 + bpow 26 <= bpow 29 *)
    replace (bpow radix2 28
             + (bpow radix2 27 + bpow radix2 26
                + bpow radix2 80
                  / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
      with ((bpow radix2 28 + bpow radix2 27 + bpow radix2 26)
            + bpow radix2 80
              / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
      by ring.
    apply Rplus_le_compat_r.
    simpl; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Y-coordinate mirror of the Scope C.2-tight cascade.                        *)
(*                                                                            *)
(* Layers 1 (den) and 2 (s) are shared with the x cascade -- the denominator *)
(* and Cramer parameter don't depend on whether we're evaluating x or y.     *)
(* Layers 3 (s * dy) and 4 (B2R(by_ P0) + s * dy) mirror the x layers with   *)
(* by_ substituted for bx, reusing the existing _y_safe / _y_abs_le_bpow_*   *)
(* lemmas.                                                                    *)
(* -------------------------------------------------------------------------- *)

(* Delta_round_mul, y: b64_round error on the layer-3 multiplication. *)
Lemma b64_intersect_mult_y_round_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dy)
          - Binary.B2R prec emax s * Binary.B2R prec emax dy)
    <= bpow radix2 27.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_y_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_error_le_half_ulp_round
                (Binary.B2R prec emax
                   (b64_div (b64_orient2d Q0 Q1 P0)
                            (b64_minus (b64_orient2d Q0 Q1 P0)
                                       (b64_orient2d Q0 Q1 P1)))
                 * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))) as Herr.
  eapply Rle_trans; [exact Herr|].
  assert (Hbnd : Rabs (b64_round
                        (Binary.B2R prec emax
                          (b64_div (b64_orient2d Q0 Q1 P0)
                                   (b64_minus (b64_orient2d Q0 Q1 P0)
                                              (b64_orient2d Q0 Q1 P1)))
                         * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
                 <= bpow radix2 80).
  { pose proof (b64_intersect_mult_y_abs_le_bpow_80 _ _ _ _ Hsafe) as Bm.
    cbv zeta in Bm.
    rewrite HB2R in Bm. exact Bm. }
  pose proof (b64_ulp_le_at_magnitude_uniform _ 80 ltac:(lia) Hbnd) as Hulp.
  apply Rle_trans with (bpow radix2 (80 - prec + 1) / 2);
    [|unfold prec; simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra|exact Hulp].
Qed.

(* Delta_carry_mul, y: the s-error carried through dy. *)
Lemma b64_intersect_mult_y_carry_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax s * Binary.B2R prec emax dy
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dy)
    <= bpow radix2 26
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  replace (Binary.B2R prec emax
             (b64_div (b64_orient2d Q0 Q1 P0)
                      (b64_minus (b64_orient2d Q0 Q1 P0)
                                 (b64_orient2d Q0 Q1 P1)))
           * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))
    with (Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
          * (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
    by ring.
  rewrite Rabs_mult.
  pose proof (b64_intersect_dy_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdy.
  pose proof (b64_intersect_s_forward_error _ _ _ _ Hsafe) as Bs.
  apply Rle_trans
    with (bpow radix2 26
          * (1 + bpow radix2 54
                 / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Bdy|exact Bs].
  - rewrite Rmult_plus_distr_l, Rmult_1_r.
    apply Rplus_le_compat_l.
    unfold Rdiv.
    rewrite <- Rmult_assoc.
    rewrite <- bpow_plus.
    replace (26 + 54)%Z with 80%Z by lia.
    apply Rle_refl.
Qed.

(* Layer 3 full forward error, y. *)
Theorem b64_intersect_mult_y_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dy)
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dy)
    <= bpow radix2 27 + bpow radix2 26
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_y_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_y_carry_error _ _ _ _ Hsafe) as Hcarry.
  cbv zeta in Hcarry.
  replace (Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (by_ P1) (by_ P0)))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))
    with ((Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (by_ P1) (by_ P0)))
           - Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))
          + (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rplus_assoc.
  apply Rplus_le_compat; [exact Hround | exact Hcarry].
Qed.

(* Delta_round_plus, y: b64_round error on the final addition. *)
Lemma b64_intersect_plus_y_round_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax (b64_plus (by_ P0) (b64_mult s dy))
          - (Binary.B2R prec emax (by_ P0)
             + Binary.B2R prec emax (b64_mult s dy)))
    <= bpow radix2 28.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_plus_y_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_error_le_half_ulp_round
                (Binary.B2R prec emax (by_ P0)
                 + Binary.B2R prec emax
                     (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                                   (b64_orient2d Q0 Q1 P1)))
                               (b64_minus (by_ P1) (by_ P0))))) as Herr.
  eapply Rle_trans; [exact Herr|].
  assert (Hbnd : Rabs (b64_round
                        (Binary.B2R prec emax (by_ P0)
                         + Binary.B2R prec emax
                             (b64_mult
                                (b64_div (b64_orient2d Q0 Q1 P0)
                                         (b64_minus (b64_orient2d Q0 Q1 P0)
                                                    (b64_orient2d Q0 Q1 P1)))
                                (b64_minus (by_ P1) (by_ P0)))))
                 <= bpow radix2 81).
  { pose proof (b64_intersect_point_y_abs_le_bpow_81 _ _ _ _ Hsafe) as Bp.
    unfold b64_intersect_point_y in Bp.
    cbv zeta in Bp.
    rewrite HB2R in Bp. exact Bp. }
  pose proof (b64_ulp_le_at_magnitude_uniform _ 81 ltac:(lia) Hbnd) as Hulp.
  apply Rle_trans with (bpow radix2 (81 - prec + 1) / 2);
    [|unfold prec; simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra|exact Hulp].
Qed.

(* Headline forward-error theorem, y coordinate. *)
Theorem b64_intersect_point_y_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1)
          - (Binary.B2R prec emax (by_ P0)
             + cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
    <= bpow radix2 29
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_y.
  cbv zeta.
  pose proof (b64_intersect_plus_y_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_y_forward_error _ _ _ _ Hsafe) as Hlayer3.
  cbv zeta in Hlayer3.
  replace (Binary.B2R prec emax
             (b64_plus (by_ P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (by_ P1) (by_ P0))))
           - (Binary.B2R prec emax (by_ P0)
              + cross_R_BP Q0 Q1 P0
                / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
                * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
    with ((Binary.B2R prec emax
             (b64_plus (by_ P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (by_ P1) (by_ P0))))
           - (Binary.B2R prec emax (by_ P0)
              + Binary.B2R prec emax
                  (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                                (b64_orient2d Q0 Q1 P1)))
                            (b64_minus (by_ P1) (by_ P0)))))
          + (Binary.B2R prec emax
               (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                  (b64_minus (b64_orient2d Q0 Q1 P0)
                                             (b64_orient2d Q0 Q1 P1)))
                         (b64_minus (by_ P1) (by_ P0)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
    by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rle_trans
    with (bpow radix2 28
          + (bpow radix2 27 + bpow radix2 26
             + bpow radix2 80
               / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rplus_le_compat; [exact Hround | exact Hlayer3].
  - replace (bpow radix2 28
             + (bpow radix2 27 + bpow radix2 26
                + bpow radix2 80
                  / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
      with ((bpow radix2 28 + bpow radix2 27 + bpow radix2 26)
            + bpow radix2 80
              / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
      by ring.
    apply Rplus_le_compat_r.
    simpl; lra.
Qed.

(*                                                                            *)
(* The `BPoint` instance routes through the total b64 projections defined   *)
(* above.                                                                    *)
(*                                                                            *)
(* CHORD-PARADIGM SCOPE.  See docs/audit-phase4-curves.md.  The 4-point     *)
(* signature `T -> T -> T -> T -> binary64` is chord-paradigm-specific:    *)
(* chord-chord intersection takes two segments, i.e. four endpoints.       *)
(* A future curve-bearing variant does *not* fit this signature: the       *)
(* natural carrier for a curve is bound to the curve family, and a         *)
(* curve-curve intersection takes two *curves*, not four points.  The      *)
(* right shape is therefore a *family* of parallel typeclasses, one per   *)
(* curve family, all coexisting with `HasIntersect` (the chord case).     *)
(*                                                                            *)
(* (1) Arc-arc.  Canonical carrier is the 3-control-point triplet         *)
(*     (start, on-arc, end):                                              *)
(*                                                                            *)
(*     Class HasArcIntersect (T : Type) : Type := {                       *)
(*       arc_intersect_x          : T -> T -> binary64;                   *)
(*       arc_intersect_y          : T -> T -> binary64;                   *)
(*       arc_intersect_inputs_safe : T -> T -> Prop;                      *)
(*     }.                                                                   *)
(*                                                                            *)
(*     A future `HasArcIntersect_ArcTriplet` instance would route through *)
(*     b64 projections built on the unique-circle-through-three-points    *)
(*     Cramer's-rule analog (see Orient_b64_exact.v's dovetail block).   *)
(*                                                                            *)
(* (2) Clothoid-clothoid.  The clothoid (Euler spiral) is a curve with    *)
(*     linearly-varying curvature -- the standard transition primitive   *)
(*     in road / rail geometry.  Canonical carrier is the G^1 Hermite    *)
(*     pair: two endpoints + two endpoint tangent directions + the        *)
(*     chord length L (Bertolazzi-Frego 2015 / 2018):                    *)
(*                                                                            *)
(*     Class HasClothoidIntersect (T : Type) : Type := {                  *)
(*       clothoid_intersect_x         : T -> T -> binary64;               *)
(*       clothoid_intersect_y         : T -> T -> binary64;               *)
(*       clothoid_intersect_inputs_safe : T -> T -> Prop;                 *)
(*     }.                                                                   *)
(*                                                                            *)
(*     Unlike chord-chord and arc-arc, clothoid-clothoid intersection has *)
(*     no closed form: the intersection parameter is the root of a       *)
(*     transcendental residual involving Fresnel integrals.  The         *)
(*     intended implementation is the Halley iteration on the L-form     *)
(*     residual                                                            *)
(*                                                                            *)
(*         f(L) = L^2 * (P(L)^2 + Q(L)^2) - d^2                          *)
(*                                                                            *)
(*     with                                                                 *)
(*                                                                            *)
(*         P(L) = int_0^1 cos (L * psi(tau)) dtau                        *)
(*         Q(L) = int_0^1 sin (L * psi(tau)) dtau                        *)
(*         psi(tau) = kappa_0 * tau + (kappa_1 - kappa_0) * tau^2 / 2.   *)
(*                                                                            *)
(*     The R-side derivative identities                                    *)
(*                                                                            *)
(*         P'(L) = -T(L)        Q'(L) = R(L)                             *)
(*         R'(L) = -S2s(L)      T'(L) = S2c(L)                           *)
(*         f'(L)  = 2 L (P^2 + Q^2) + 2 L^2 (Q R - P T)                  *)
(*         f''(L) = 2 (P^2 + Q^2) + 8 L (Q R - P T)                      *)
(*                  + 2 L^2 (R^2 + T^2 - P S2c - Q S2s)                  *)
(*                                                                            *)
(*     are already formalised in the companion project                    *)
(*     `clothoid-halley-coq` (Merkator Group, 2026) under Coq 8.13.1 /    *)
(*     8.20.1 with Coquelicot 3.x, no `Admitted`, beyond the four         *)
(*     standard Coquelicot axioms.  Cited per repo's academic-citation   *)
(*     licence; not imported (Coquelicot is a separate real-analysis     *)
(*     library from Flocq, and our corpus targets Rocq 9.1.1).            *)
(*                                                                            *)
(*     Porting cost to land a `HasClothoidIntersect_ClothoidL` instance:  *)
(*                                                                            *)
(*       (a) Re-prove the six R-side derivative identities in Flocq's    *)
(*           native `Reals` framework (Coquelicot's `RInt` becomes our   *)
(*           `RiemannInt`, `is_derive` becomes Flocq's derivative        *)
(*           predicate).  ~3-5 days of mechanical translation; the       *)
(*           proof recipes (`auto_derive`, `Derive` rewrites, `ring`)    *)
(*           are tactic-name preserved.                                   *)
(*       (b) Lift the R-side residual to its binary64 evaluator (Stage-A *)
(*           filter over Halley iterates, no-overflow chain across the   *)
(*           per-iterate updates).  Symmetric to b64_orient2d's          *)
(*           treatment but with iteration-bounded composition.            *)
(*       (c) Termination proof: under the monotone-branch precondition  *)
(*           from clothoid-halley-coq's L-form, Halley converges to       *)
(*           machine precision in <= 4 iterations on the empirical 9,058- *)
(*           record corpus (Merkator paper, table 3).  In the corpus     *)
(*           that becomes a *bounded-iteration* termination lemma, not   *)
(*           a fixpoint-domain argument.                                  *)
(*                                                                            *)
(*     Differential-testing oracle: the 9,058-record golden corpus in    *)
(*     clothoid-halley-coq/data/golden_vectors.json -- bit-identical     *)
(*     across Python / C# / Java / TypeScript reference implementations  *)
(*     within 1e-9 m chord-length agreement, matching iteration counts. *)
(*     Symmetric infrastructure to oracle/extracted.ml in our corpus     *)
(*     (see Validate_binary64_extract.v): a future binary64 Halley       *)
(*     implementation can be extracted to OCaml and bit-compared against *)
(*     the golden corpus before any soundness claim is made.              *)
(*                                                                            *)
(* (3) Any further curve family (Bezier, NURBS, ...) gets its own         *)
(*     parallel typeclass on the same template.                          *)
(*                                                                            *)
(* All these typeclasses coexist on the chord layer: `HasIntersect_BPoint`*)
(* below stays as the chord-chord hook, and each future                   *)
(* `Has{Arc,Clothoid,...}Intersect_{Carrier}` is the corresponding curve  *)
(* hook.  Bridging between any curve family and the chord layer          *)
(* (subdivision to N chords with sagitta tolerance) composes refinement   *)
(* bounds with `HasIntersect_BPoint`, not a new instance of either class. *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Phase 1 Session 6 -- reference bridge + soundness typeclass.               *)
(*                                                                            *)
(* The Scope C.2-tight headlines state the forward-error bound against the    *)
(* internal reference `B2R(bx P0) + s_exact * B2R(b64_minus (bx P1) (bx P0))`.*)
(* Under int-safe inputs the `b64_minus` step is bit-exact (Session 1's       *)
(* `b64_intersect_dx_R`) and `cross_R_BP = cross (BP2P ...)` (Intersect_b64's *)
(* `cross_R_BP_eq_cross_BP2P`), so the reference equals                       *)
(* `intersect_x_R (BP2P P0, BP2P P1, BP2P Q0, BP2P Q1)` exactly.              *)
(*                                                                            *)
(* This section threads that bridge, restates the headlines against the       *)
(* canonical `intersect_x_R`/`intersect_y_R` references, and plugs the bound  *)
(* into a `HasIntersect_sound` typeclass layered on `HasIntersect`.           *)
(* -------------------------------------------------------------------------- *)

Lemma c2tight_ref_x_eq_intersect_x_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (bx P0)
    + cross_R_BP Q0 Q1 P0
      / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
      * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
    = intersect_x_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_dx_R _ _ _ _ Hsafe) as [Hdx _].
  rewrite Hdx.
  unfold intersect_x_R, intersect_param_s, BP2P, px.
  rewrite (cross_R_BP_eq_cross_BP2P Q0 Q1 P0).
  rewrite (cross_R_BP_eq_cross_BP2P Q0 Q1 P1).
  unfold BP2P, px.
  reflexivity.
Qed.

Lemma c2tight_ref_y_eq_intersect_y_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (by_ P0)
    + cross_R_BP Q0 Q1 P0
      / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
      * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
    = intersect_y_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_dy_R _ _ _ _ Hsafe) as [Hdy _].
  rewrite Hdy.
  unfold intersect_y_R, intersect_param_s, BP2P, py.
  rewrite (cross_R_BP_eq_cross_BP2P Q0 Q1 P0).
  rewrite (cross_R_BP_eq_cross_BP2P Q0 Q1 P1).
  unfold BP2P, py.
  reflexivity.
Qed.

(* Restated headline against the canonical intersect_x_R reference. *)
Theorem b64_intersect_point_x_forward_error_vs_intersect_x_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1)
          - intersect_x_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1))
    <= bpow radix2 29
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  rewrite <- (c2tight_ref_x_eq_intersect_x_R _ _ _ _ Hsafe).
  apply (b64_intersect_point_x_forward_error _ _ _ _ Hsafe).
Qed.

Theorem b64_intersect_point_y_forward_error_vs_intersect_y_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1)
          - intersect_y_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1))
    <= bpow radix2 29
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  rewrite <- (c2tight_ref_y_eq_intersect_y_R _ _ _ _ Hsafe).
  apply (b64_intersect_point_y_forward_error _ _ _ _ Hsafe).
Qed.

Class HasIntersect (T : Type) : Type := {
  intersect_x          : T -> T -> T -> T -> binary64;
  intersect_y          : T -> T -> T -> T -> binary64;
  intersect_inputs_safe : T -> T -> T -> T -> Prop;
}.

Instance HasIntersect_BPoint : HasIntersect BPoint := {
  intersect_x          := b64_intersect_point_x;
  intersect_y          := b64_intersect_point_y;
  intersect_inputs_safe := intersect_point_inputs_int_safe;
}.

(* Soundness layer: caller-facing forward-error contract.  Each instance      *)
(* supplies a reference value (`intersect_ref_x/y`) and an error bound        *)
(* (`intersect_error_bound`) that depends on the inputs; the two soundness    *)
(* obligations require the b64 result to be within the bound of the          *)
(* reference under the safety predicate.                                      *)
Class HasIntersect_sound (T : Type) `{HasIntersect T} : Type := {
  intersect_ref_x       : T -> T -> T -> T -> R;
  intersect_ref_y       : T -> T -> T -> T -> R;
  intersect_error_bound : T -> T -> T -> T -> R;
  intersect_x_sound :
    forall a b c d : T,
      intersect_inputs_safe a b c d ->
      Rabs (Binary.B2R prec emax (intersect_x a b c d)
            - intersect_ref_x a b c d)
      <= intersect_error_bound a b c d;
  intersect_y_sound :
    forall a b c d : T,
      intersect_inputs_safe a b c d ->
      Rabs (Binary.B2R prec emax (intersect_y a b c d)
            - intersect_ref_y a b c d)
      <= intersect_error_bound a b c d;
}.

Instance HasIntersect_sound_BPoint : HasIntersect_sound BPoint := {
  intersect_ref_x       := fun A B C D =>
                             intersect_x_R (BP2P A) (BP2P B) (BP2P C) (BP2P D);
  intersect_ref_y       := fun A B C D =>
                             intersect_y_R (BP2P A) (BP2P B) (BP2P C) (BP2P D);
  intersect_error_bound := fun A B C D =>
                             bpow radix2 29
                             + bpow radix2 80
                               / Rabs (cross_R_BP C D A - cross_R_BP C D B);
  intersect_x_sound     := b64_intersect_point_x_forward_error_vs_intersect_x_R;
  intersect_y_sound     := b64_intersect_point_y_forward_error_vs_intersect_y_R;
}.

(* ============================================================================
   Parallel tight chain (Scope C.2-tight alternative).
   ----------------------------------------------------------------------------
   The chain above (Layers 1-4 + reference bridge) uses
   `b64_intersect_den_forward_error`'s loose `<= bpow 1 = 2` Step 1 bound.
   The lemmas below mirror Layers 2-4 + the reference bridge with the
   tight `b64_intersect_den_error_le_1` (`<= 1`) substituted at the
   Step 1 cite site.  The tightening propagates through the `bpow 53 * |e1|`
   carryover terms in Layers 2-3 and the final additive composition in
   Layer 4, yielding a 2x reduction in the condition-number-dependent term
   of the K_intersect bound:

       Loose:  K_intersect = bpow 29 + bpow 80 / |den_R|
       Tight:  K_intersect = bpow 29 + bpow 79 / |den_R|.

   The constant term `bpow 29` is unchanged -- it carries the round-to-
   nearest errors of the inner mult and plus steps, which are independent
   of the Step 1 bound.  Only the carryover term (the dominant one when
   `|den_R|` is well-separated from zero is small) tightens.

   Each tight theorem cites the foundation `b64_intersect_den_error_le_1`
   exactly once -- Layer 2 carry.  Downstream tight theorems compose
   inductively through `_s_forward_error_tight` and the y-mirror.

   Round-error lemmas (`_s_round_error`, `_mult_x/y_round_error`,
   `_plus_x/y_round_error`) are reused from main's chain unchanged --
   they don't depend on the Step 1 bound.
   ============================================================================ *)

(* Layer 2 tight: Delta_carry with the tight Step 1 bound. *)
Theorem b64_intersect_s_carry_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (cross_R_BP Q0 Q1 P0
            / Binary.B2R prec emax
                (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= bpow radix2 53
       / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  set (qp0_R := cross_R_BP Q0 Q1 P0).
  set (qp1_R := cross_R_BP Q0 Q1 P1).
  set (den_R := Binary.B2R prec emax
                  (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))).
  set (den_exact := qp0_R - qp1_R).
  assert (Hden_exact_ne : den_exact <> 0).
  { unfold den_exact, qp0_R, qp1_R. destruct Hsafe as [_ Hne]. lra. }
  assert (Hden_R_ne : den_R <> 0).
  { unfold den_R. apply (b64_intersect_den_B2R_nonzero _ _ _ _ Hsafe). }
  assert (Hden_R_ge1 : 1 <= Rabs den_R).
  { unfold den_R. apply (b64_intersect_den_B2R_abs_ge_1 _ _ _ _ Hsafe). }
  assert (Hden_exact_ge1 : 1 <= Rabs den_exact).
  { unfold den_exact, qp0_R, qp1_R.
    destruct Hsafe as [Hint Hne].
    pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
    pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
    destruct (cross_R_BP_int_witness _ _ _ Hint0) as [n0 [Hn0 _]].
    destruct (cross_R_BP_int_witness _ _ _ Hint1) as [n1 [Hn1 _]].
    rewrite Hn0, Hn1, <- minus_IZR, <- abs_IZR.
    apply IZR_le.
    assert (Hne_n : n0 <> n1).
    { intros Heq. apply Hne. rewrite Hn0, Hn1, Heq. reflexivity. }
    lia. }
  assert (Hqp0_R_bnd : Rabs qp0_R <= bpow radix2 53).
  { unfold qp0_R.
    destruct Hsafe as [Hint _].
    apply (cross_R_BP_abs_le_bpow_53 _ _ _
             (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint)). }
  (* Tight substitution: use _le_1 instead of _forward_error for the Step 1 cite. *)
  assert (Hden_err : Rabs (den_R - den_exact) <= 1).
  { unfold den_R, den_exact, qp0_R, qp1_R.
    apply (b64_intersect_den_error_le_1 _ _ _ _ Hsafe). }
  assert (Hpos_R : 0 < Rabs den_R) by (apply Rabs_pos_lt; exact Hden_R_ne).
  assert (Hpos_exact : 0 < Rabs den_exact)
    by (apply Rabs_pos_lt; exact Hden_exact_ne).
  replace (qp0_R / den_R - qp0_R / den_exact)
    with (qp0_R * (den_exact - den_R) / (den_R * den_exact))
    by (field; split; assumption).
  unfold Rdiv at 1.
  rewrite Rabs_mult.
  rewrite Rabs_inv.
  rewrite (Rabs_mult qp0_R (den_exact - den_R)).
  rewrite (Rabs_mult den_R den_exact).
  apply Rle_trans
    with ((bpow radix2 53 * 1) / (1 * Rabs den_exact)).
  - apply Rmult_le_compat;
      [ apply Rmult_le_pos; apply Rabs_pos
      | apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; assumption
      |
      | ].
    + apply Rmult_le_compat;
        [apply Rabs_pos|apply Rabs_pos|exact Hqp0_R_bnd|].
      replace (Rabs (den_exact - den_R)) with (Rabs (den_R - den_exact))
        by (rewrite <- Rabs_Ropp; f_equal; ring).
      exact Hden_err.
    + apply Rinv_le_contravar.
      * rewrite Rmult_1_l. exact Hpos_exact.
      * apply Rmult_le_compat_r; [apply Rlt_le; exact Hpos_exact|exact Hden_R_ge1].
  - rewrite Rmult_1_l, Rmult_1_r. apply Rle_refl.
Qed.

(* Layer 2 tight full forward-error: composition of Delta_round (unchanged)
   with the tight Delta_carry above. *)
Theorem b64_intersect_s_forward_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
            (b64_div (b64_orient2d Q0 Q1 P0)
                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                (b64_orient2d Q0 Q1 P1)))
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= 1 + bpow radix2 53
            / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  set (qp0_R := cross_R_BP Q0 Q1 P0).
  set (qp1_R := cross_R_BP Q0 Q1 P1).
  set (den_R := Binary.B2R prec emax
                  (b64_minus (b64_orient2d Q0 Q1 P0)
                             (b64_orient2d Q0 Q1 P1))).
  set (s_R := Binary.B2R prec emax
                (b64_div (b64_orient2d Q0 Q1 P0)
                         (b64_minus (b64_orient2d Q0 Q1 P0)
                                    (b64_orient2d Q0 Q1 P1)))).
  replace (s_R - qp0_R / (qp0_R - qp1_R))
    with ((s_R - qp0_R / den_R) + (qp0_R / den_R - qp0_R / (qp0_R - qp1_R)))
    by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat.
  - apply (b64_intersect_s_round_error _ _ _ _ Hsafe).
  - apply (b64_intersect_s_carry_error_tight _ _ _ _ Hsafe).
Qed.

(* Layer 3 tight x: Delta_carry_mul with the tight layer-2 forward error. *)
Lemma b64_intersect_mult_x_carry_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax s * Binary.B2R prec emax dx
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dx)
    <= bpow radix2 26
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  replace (Binary.B2R prec emax
             (b64_div (b64_orient2d Q0 Q1 P0)
                      (b64_minus (b64_orient2d Q0 Q1 P0)
                                 (b64_orient2d Q0 Q1 P1)))
           * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))
    with (Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
          * (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
    by ring.
  rewrite Rabs_mult.
  pose proof (b64_intersect_dx_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdx.
  pose proof (b64_intersect_s_forward_error_tight _ _ _ _ Hsafe) as Bs.
  apply Rle_trans
    with (bpow radix2 26
          * (1 + bpow radix2 53
                 / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Bdx|exact Bs].
  - rewrite Rmult_plus_distr_l, Rmult_1_r.
    apply Rplus_le_compat_l.
    unfold Rdiv.
    rewrite <- Rmult_assoc.
    rewrite <- bpow_plus.
    replace (26 + 53)%Z with 79%Z by lia.
    apply Rle_refl.
Qed.

(* Layer 3 tight x forward error: composition of mult_x_round_error (unchanged)
   with the tight Delta_carry_mul. *)
Theorem b64_intersect_mult_x_forward_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dx)
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dx)
    <= bpow radix2 27 + bpow radix2 26
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_x_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_x_carry_error_tight _ _ _ _ Hsafe) as Hcarry.
  cbv zeta in Hcarry.
  replace (Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (bx P1) (bx P0)))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))
    with ((Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (bx P1) (bx P0)))
           - Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))
          + (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rplus_assoc.
  apply Rplus_le_compat; [exact Hround | exact Hcarry].
Qed.

(* Layer 3 tight y: same shape as x with by_ substituted. *)
Lemma b64_intersect_mult_y_carry_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax s * Binary.B2R prec emax dy
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dy)
    <= bpow radix2 26
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  replace (Binary.B2R prec emax
             (b64_div (b64_orient2d Q0 Q1 P0)
                      (b64_minus (b64_orient2d Q0 Q1 P0)
                                 (b64_orient2d Q0 Q1 P1)))
           * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))
    with (Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
          * (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
    by ring.
  rewrite Rabs_mult.
  pose proof (b64_intersect_dy_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdy.
  pose proof (b64_intersect_s_forward_error_tight _ _ _ _ Hsafe) as Bs.
  apply Rle_trans
    with (bpow radix2 26
          * (1 + bpow radix2 53
                 / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Bdy|exact Bs].
  - rewrite Rmult_plus_distr_l, Rmult_1_r.
    apply Rplus_le_compat_l.
    unfold Rdiv.
    rewrite <- Rmult_assoc.
    rewrite <- bpow_plus.
    replace (26 + 53)%Z with 79%Z by lia.
    apply Rle_refl.
Qed.

Theorem b64_intersect_mult_y_forward_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dy)
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dy)
    <= bpow radix2 27 + bpow radix2 26
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_y_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_y_carry_error_tight _ _ _ _ Hsafe) as Hcarry.
  cbv zeta in Hcarry.
  replace (Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (by_ P1) (by_ P0)))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))
    with ((Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (by_ P1) (by_ P0)))
           - Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))
          + (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rplus_assoc.
  apply Rplus_le_compat; [exact Hround | exact Hcarry].
Qed.

(* Layer 4 tight x: composition of plus_x_round_error (unchanged) with the
   tight Layer 3 x forward error. *)
Theorem b64_intersect_point_x_forward_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1)
          - (Binary.B2R prec emax (bx P0)
             + cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
    <= bpow radix2 29
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_x.
  cbv zeta.
  pose proof (b64_intersect_plus_x_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_x_forward_error_tight _ _ _ _ Hsafe) as Hlayer3.
  cbv zeta in Hlayer3.
  replace (Binary.B2R prec emax
             (b64_plus (bx P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (bx P1) (bx P0))))
           - (Binary.B2R prec emax (bx P0)
              + cross_R_BP Q0 Q1 P0
                / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
                * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
    with ((Binary.B2R prec emax
             (b64_plus (bx P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (bx P1) (bx P0))))
           - (Binary.B2R prec emax (bx P0)
              + Binary.B2R prec emax
                  (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                                (b64_orient2d Q0 Q1 P1)))
                            (b64_minus (bx P1) (bx P0)))))
          + (Binary.B2R prec emax
               (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                  (b64_minus (b64_orient2d Q0 Q1 P0)
                                             (b64_orient2d Q0 Q1 P1)))
                         (b64_minus (bx P1) (bx P0)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
    by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rle_trans
    with (bpow radix2 28
          + (bpow radix2 27 + bpow radix2 26
             + bpow radix2 79
               / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rplus_le_compat; [exact Hround | exact Hlayer3].
  - replace (bpow radix2 28
             + (bpow radix2 27 + bpow radix2 26
                + bpow radix2 79
                  / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
      with ((bpow radix2 28 + bpow radix2 27 + bpow radix2 26)
            + bpow radix2 79
              / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
      by ring.
    apply Rplus_le_compat_r.
    simpl; lra.
Qed.

(* Layer 4 tight y: mirror of x with by_ substituted. *)
Theorem b64_intersect_point_y_forward_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1)
          - (Binary.B2R prec emax (by_ P0)
             + cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
    <= bpow radix2 29
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_y.
  cbv zeta.
  pose proof (b64_intersect_plus_y_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_y_forward_error_tight _ _ _ _ Hsafe) as Hlayer3.
  cbv zeta in Hlayer3.
  replace (Binary.B2R prec emax
             (b64_plus (by_ P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (by_ P1) (by_ P0))))
           - (Binary.B2R prec emax (by_ P0)
              + cross_R_BP Q0 Q1 P0
                / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
                * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
    with ((Binary.B2R prec emax
             (b64_plus (by_ P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (by_ P1) (by_ P0))))
           - (Binary.B2R prec emax (by_ P0)
              + Binary.B2R prec emax
                  (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                                (b64_orient2d Q0 Q1 P1)))
                            (b64_minus (by_ P1) (by_ P0)))))
          + (Binary.B2R prec emax
               (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                  (b64_minus (b64_orient2d Q0 Q1 P0)
                                             (b64_orient2d Q0 Q1 P1)))
                         (b64_minus (by_ P1) (by_ P0)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
    by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rle_trans
    with (bpow radix2 28
          + (bpow radix2 27 + bpow radix2 26
             + bpow radix2 79
               / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rplus_le_compat; [exact Hround | exact Hlayer3].
  - replace (bpow radix2 28
             + (bpow radix2 27 + bpow radix2 26
                + bpow radix2 79
                  / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
      with ((bpow radix2 28 + bpow radix2 27 + bpow radix2 26)
            + bpow radix2 79
              / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
      by ring.
    apply Rplus_le_compat_r.
    simpl; lra.
Qed.

(* Reference-bridge restatements against the canonical intersect_x_R /
   intersect_y_R references.  Reuses main's c2tight_ref_x/y_eq_intersect_x/y_R
   bridge lemmas (which don't depend on the Step 1 bound). *)
Theorem b64_intersect_point_x_forward_error_vs_intersect_x_R_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1)
          - intersect_x_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1))
    <= bpow radix2 29
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  rewrite <- (c2tight_ref_x_eq_intersect_x_R _ _ _ _ Hsafe).
  apply (b64_intersect_point_x_forward_error_tight _ _ _ _ Hsafe).
Qed.

Theorem b64_intersect_point_y_forward_error_vs_intersect_y_R_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1)
          - intersect_y_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1))
    <= bpow radix2 29
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  rewrite <- (c2tight_ref_y_eq_intersect_y_R _ _ _ _ Hsafe).
  apply (b64_intersect_point_y_forward_error_tight _ _ _ _ Hsafe).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_intersect_qp0_R.
Print Assumptions b64_intersect_qp1_R.
Print Assumptions b64_intersect_dx_R.
Print Assumptions b64_intersect_dy_R.
Print Assumptions cross_R_BP_int_witness.
Print Assumptions cross_R_BP_abs_le_bpow_53.
Print Assumptions b64_intersect_den_safe.
Print Assumptions b64_intersect_den_R_round.
Print Assumptions b64_intersect_den_B2R_nonzero.
Print Assumptions b64_intersect_point_returns_some_when_point.
Print Assumptions b64_intersect_den_forward_error.
Print Assumptions b64_intersect_s_carry_error.
Print Assumptions b64_intersect_s_round_error.
Print Assumptions b64_intersect_s_forward_error.
Print Assumptions b64_ulp_le_at_magnitude_uniform.
Print Assumptions b64_intersect_mult_x_round_error.
Print Assumptions b64_intersect_mult_x_carry_error.
Print Assumptions b64_intersect_mult_x_forward_error.
Print Assumptions b64_intersect_plus_x_round_error.
Print Assumptions b64_intersect_point_x_forward_error.
Print Assumptions b64_intersect_mult_y_round_error.
Print Assumptions b64_intersect_mult_y_carry_error.
Print Assumptions b64_intersect_mult_y_forward_error.
Print Assumptions b64_intersect_plus_y_round_error.
Print Assumptions b64_intersect_point_y_forward_error.
Print Assumptions c2tight_ref_x_eq_intersect_x_R.
Print Assumptions c2tight_ref_y_eq_intersect_y_R.
Print Assumptions b64_intersect_point_x_forward_error_vs_intersect_x_R.
Print Assumptions b64_intersect_point_y_forward_error_vs_intersect_y_R.
Print Assumptions b64_intersect_den_error_le_1.
Print Assumptions b64_intersect_s_carry_error_tight.
Print Assumptions b64_intersect_s_forward_error_tight.
Print Assumptions b64_intersect_mult_x_carry_error_tight.
Print Assumptions b64_intersect_mult_x_forward_error_tight.
Print Assumptions b64_intersect_mult_y_carry_error_tight.
Print Assumptions b64_intersect_mult_y_forward_error_tight.
Print Assumptions b64_intersect_point_x_forward_error_tight.
Print Assumptions b64_intersect_point_y_forward_error_tight.
Print Assumptions b64_intersect_point_x_forward_error_vs_intersect_x_R_tight.
Print Assumptions b64_intersect_point_y_forward_error_vs_intersect_y_R_tight.

(* -------------------------------------------------------------------------- *)
(* Phase 1 deliverable map                                                    *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* SHIPPED                                                                    *)
(*                                                                            *)
(* 1. Scope B.1 (denominator triple): `b64_intersect_den_safe`,               *)
(*    `b64_intersect_den_R_round`, `b64_intersect_den_B2R_nonzero`,           *)
(*    + magnitude bounds `_abs_le_bpow_54` / `_abs_ge_1`.                     *)
(*                                                                            *)
(* 2. Scope B.2 (round-chain identity, full):                                 *)
(*    `b64_intersect_point_x_round_chain` / `_y_round_chain` give the exact   *)
(*    nested-round identity                                                   *)
(*       B2R(b64_intersect_point_x ...)                                       *)
(*     = b64_round (B2R(bx P0)                                                *)
(*                  + b64_round (b64_round (qp0_R                             *)
(*                                          / b64_round (qp0_R - qp1_R))      *)
(*                              * (B2R(bx P1) - B2R(bx P0)))).                *)
(*    Supporting per-op safety+B2R-round lemmas for div / mult / plus also   *)
(*    in place (see `b64_intersect_s_R_round`, `_mult_*_safe`, `_plus_*_safe`)*)
(*                                                                            *)
(* 3. Scope C (polish + corollaries):                                         *)
(*    `b64_intersect_point_x_finite` / `_y_finite`,                           *)
(*    `_abs_le_bpow_81` / `_y_abs_le_bpow_81` (coarse magnitude),             *)
(*    `b64_intersect_point_returns_some_when_point` (Some-commits under safe).*)
(*                                                                            *)
(* 4. Scope C.2-tight (forward-error decomposition, x + y coordinates):       *)
(*    Four-layer cascade landed in five sessions S1-S5 for x, mirrored to y  *)
(*    in the refactor pass:                                                   *)
(*      Layer 1 (den):     `b64_intersect_den_forward_error`                  *)
(*                         <= bpow 1                                          *)
(*      Layer 2 (s):       `b64_intersect_s_forward_error`                    *)
(*                         <= 1 + bpow 54 / |qp0_R - qp1_R|                   *)
(*      Layer 3 (s*d_):    `b64_intersect_mult_{x,y}_forward_error`           *)
(*                         <= bpow 27 + bpow 26 + bpow 80 / |qp0_R - qp1_R|   *)
(*      Layer 4 (final):   `b64_intersect_point_{x,y}_forward_error`          *)
(*                         <= bpow 29 + bpow 80 / |qp0_R - qp1_R|             *)
(*                                                                            *)
(* 5. Session 6 -- reference bridge + soundness typeclass:                    *)
(*    `b64_intersect_point_{x,y}_forward_error_vs_intersect_{x,y}_R`          *)
(*    state the same bound against the canonical `intersect_{x,y}_R          *)
(*    (BP2P P0) ... (BP2P Q1)` reference via `c2tight_ref_{x,y}_eq_           *)
(*    intersect_{x,y}_R` (bridges through `b64_intersect_d{x,y}_R` and        *)
(*    `cross_R_BP_eq_cross_BP2P`).                                            *)
(*                                                                            *)
(*    `HasIntersect_sound` typeclass layers on top of `HasIntersect` with     *)
(*    three fields (`intersect_ref_x`, `intersect_ref_y`,                     *)
(*    `intersect_error_bound`) and two soundness obligations.                 *)
(*    `HasIntersect_sound_BPoint` instance plugs in the C.2-tight headlines.  *)
(*                                                                            *)
(* OPTIONAL                                                                   *)
(*                                                                            *)
(* A. K * eps restatement.  Rewrite the layer-4 bound as                      *)
(*       |B2R(b64_intersect_point_x ...) - intersect_x_R (BP2P P0) ...|       *)
(*       <= K(|den_exact|) * eps                                              *)
(*    with `K(|d|) = bpow 82 + bpow 133 / |d|` and `eps = bpow(-prec)`.       *)
(*    Equivalent to the current bound; algebraic restatement only.            *)
(* -------------------------------------------------------------------------- *)
