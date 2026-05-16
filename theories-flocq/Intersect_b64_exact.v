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

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* BPoint -> R-side Point bridge.  Duplicated from Intersect_b64.v one-liner *)
(* so the layer stays independent.                                          *)
(* -------------------------------------------------------------------------- *)

Definition BP2P (p : BPoint) : Point :=
  mkPoint (Binary.B2R prec emax (bx p)) (Binary.B2R prec emax (by_ p)).

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
(* `HasIntersect` typeclass: the thin leading wire for future curve          *)
(* primitives.                                                                *)
(*                                                                            *)
(* The interface is deliberately MINIMAL for this slice: operations +        *)
(* safety predicate only, no proof fields.  Once Scope B (round-chain        *)
(* identity) and Scope C (forward-error bound) land, soundness fields can   *)
(* be added without breaking existing instances.                             *)
(*                                                                            *)
(* The `BPoint` instance routes through the total b64 projections defined   *)
(* above.  A future `ArcTriplet` instance (Phase 4 first concrete piece)     *)
(* would implement the same fields with arc-arc Cramer's-rule analogues.    *)
(* -------------------------------------------------------------------------- *)

(* Soundness field is deferred to Scope B (round-chain identity) or Scope C *)
(* (forward-error bound).  Until one of those slices lands, the interface  *)
(* is operations + safety predicate only.                                   *)
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

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_intersect_qp0_R.
Print Assumptions b64_intersect_qp1_R.
Print Assumptions b64_intersect_dx_R.
Print Assumptions b64_intersect_dy_R.

(* -------------------------------------------------------------------------- *)
(* Deferred to follow-up slices                                               *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* 1. Denominator finite + B2R non-zero.                                     *)
(*    The `b64_minus qp0 qp1` step is mostly mechanical: both operands are  *)
(*    integer-valued with magnitude <= 2^53 (via `outer_bound_2p53` applied *)
(*    in cross_R_BP), their R-difference is bounded by 2^54, and the rounded *)
(*    result is bounded by `bpow 54 << bpow emax` via                       *)
(*    `b64_round_abs_le_bpow`.  Non-zero on R follows from the safety       *)
(*    premise + exact integer round.  Pulled out as a follow-up so this    *)
(*    foundations slice ships with a tight, focused set of bit-exact        *)
(*    lemmas only.                                                          *)
(*                                                                            *)
(* 2. Returns-`Some` corollary.                                              *)
(*    Under safety, `b64_intersect_point P0 P1 Q0 Q1 = Some _` (the option- *)
(*    valued variant in Intersect_b64.v commits to `Some`).  Requires       *)
(*    composing the integer-regime decisive theorem for                    *)
(*    `b64_intersect_sign_filtered` with the predicate-dispatch in          *)
(*    `b64_intersect_point`.                                                 *)
(*                                                                            *)
(* 3. Scope B: round-chain identity.                                         *)
(*       B2R (b64_intersect_point_x ...)                                    *)
(*       = b64_round (B2R (bx P0)                                           *)
(*                    + b64_round (b64_round (qp0 / den)                    *)
(*                                  * (B2R (bx P1) - B2R (bx P0)))).        *)
(*    Precise structural identity, no integer-regime claim beyond what's   *)
(*    proved here.                                                         *)
(*                                                                            *)
(* 4. Scope C: forward-error bound.                                         *)
(*       |B2R (b64_intersect_point_x ...) - intersect_x_R (BP2P P0) ...|   *)
(*       <= K * max_coord * eps                                            *)
(*    for an explicit `K` depending on the inputs' magnitude and on the    *)
(*    denominator separation.  This is the "real" usability theorem for    *)
(*    callers and the natural place to plug a `HasIntersect_sound` field   *)
(*    into the typeclass.                                                  *)
(* -------------------------------------------------------------------------- *)
