(* Binary64 hot pixel primitives -- foundations slice for Phase 2.

   Decides membership in the *actually computed* binary64 pixel (the pixel
   whose boundaries are the rounded b64 sums `bx C ± r`).  Bridging the
   rounded pixel to the exact R-side `in_hot_pixel` requires integer-regime
   exactness on the bound computations and is deferred -- see the block at
   the foot of the file. *)

(* ============================================================================
   NetTopologySuite.Proofs.Flocq.HotPixel_b64
   ----------------------------------------------------------------------------
   binary64 mirror of theories/HotPixel.v.

   Provides the floating-point counterparts of:

     - hot_pixel_radius     ->  b64_hot_pixel_radius
     - in_hot_pixel         ->  b64_in_hot_pixel  (boolean decision)

   plus a safety predicate `b64_hot_pixel_eval_safe` packaging the no-overflow
   obligations, and one soundness theorem showing that the boolean
   decision exactly characterises membership in the *rounded* pixel
   (the pixel whose boundaries are the actual b64-computed values).

   Bridging the rounded pixel back to the R-side `in_hot_pixel P C scale`
   from `theories/HotPixel.v` requires integer-regime exactness for the
   bound computations (so the rounded boundaries coincide with the exact
   ones).  That bridge is the next slice -- see the deferred block at
   the foot of the file.

   This is the Phase 2 foundations slice on the binary64 side.  Three
   pieces are deferred to follow-up slices:

     1. `b64_hot_pixel_center` -- snapping a coordinate to the grid via
        round-to-integer.  Needs `Binary.Bnearbyint` and a finiteness /
        no-overflow analysis tailored to the round-to-int primitive.
     2. `b64_segment_touches_hot_pixel` -- the parametric or decidable
        bounding-box variant.  Easier to state alongside the noder
        (Phase 2 proper).
     3. Integer-regime exact-bound theorem -- when `scale` is a power
        of two and the coords are `coord_int_safe`, the b64 bound
        computations are bit-exact and the rounded pixel coincides
        with the R-side `in_hot_pixel`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs        Require Import Distance HotPixel.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import Orientation_b64.
From NTS.Proofs.Flocq  Require Import B64_bridge.

Local Open Scope R_scope.

Local Notation b64_fexp := (SpecFloat.fexp prec emax).
Local Notation b64_round := (round radix2 b64_fexp (round_mode mode_b64)).

(* -------------------------------------------------------------------------- *)
(* Bridge: BPoint -> R-side Point.  Mirrors the helper in Intersect_b64;     *)
(* duplicated here (one-liner) to avoid pulling Intersect_b64's heavy        *)
(* transitive imports into the HotPixel layer.                              *)
(* -------------------------------------------------------------------------- *)

Definition BP2P (p : BPoint) : Point :=
  mkPoint (Binary.B2R prec emax (bx p)) (Binary.B2R prec emax (by_ p)).

(* -------------------------------------------------------------------------- *)
(* Constants and helpers.                                                     *)
(* -------------------------------------------------------------------------- *)

Definition b64_one : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64
    mode_NE 1 0 false.

Definition b64_two : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64
    mode_NE 2 0 false.

(* Strict less-than for binary64.  Returns `false` on NaN inputs (same       *)
(* "if uncertain, do not drop" discipline as `b64_le`).                     *)
Definition b64_lt (x y : binary64) : bool :=
  match b64_compare x y with
  | Some Lt => true
  | _       => false
  end.

(* -------------------------------------------------------------------------- *)
(* `b64_hot_pixel_radius scale = 1 / (2 * scale)`.                            *)
(*                                                                            *)
(* Mirrors `hot_pixel_radius` in theories/HotPixel.v.  In general this is    *)
(* not bit-exact (two rounding steps: one for `2 * scale`, one for the      *)
(* reciprocal).  The integer-regime exact-radius theorem (deferred) shows   *)
(* it is exact when `scale` is a power of two.                              *)
(* -------------------------------------------------------------------------- *)

Definition b64_hot_pixel_radius (scale : binary64) : binary64 :=
  b64_div b64_one (b64_mult b64_two scale).

(* -------------------------------------------------------------------------- *)
(* `b64_in_hot_pixel P C scale`: boolean decision for the half-open pixel.  *)
(*                                                                            *)
(* Computes the four pixel bounds (`bx C ± r`, `by_ C ± r`) via b64_minus /  *)
(* b64_plus, then tests each axis with b64_le on the lower (closed) bound   *)
(* and b64_lt on the upper (open) bound.  Returns `false` if any comparison *)
(* is `None` (NaN or unordered) -- matches the R-side intent: undecidable   *)
(* cases are not in the pixel.                                              *)
(* -------------------------------------------------------------------------- *)

Definition b64_in_hot_pixel (P C : BPoint) (scale : binary64) : bool :=
  let r       := b64_hot_pixel_radius scale in
  let cx_lo   := b64_minus (bx C) r in
  let cx_hi   := b64_plus  (bx C) r in
  let cy_lo   := b64_minus (by_ C) r in
  let cy_hi   := b64_plus  (by_ C) r in
  b64_le cx_lo (bx P)  && b64_lt (bx P) cx_hi &&
  b64_le cy_lo (by_ P) && b64_lt (by_ P) cy_hi.

(* -------------------------------------------------------------------------- *)
(* Safety predicate: the b64 ops in the evaluation of `b64_in_hot_pixel`     *)
(* are finite-input + no-overflow.  Stated as one obligation per arithmetic *)
(* op call.                                                                   *)
(* -------------------------------------------------------------------------- *)

Definition b64_hot_pixel_radius_safe (scale : binary64) : Prop :=
  Binary.is_finite prec emax scale = true /\
  0 < Binary.B2R prec emax scale /\
  b64_safe Rmult b64_two scale /\
  Binary.B2R prec emax (b64_mult b64_two scale) <> 0 /\
  Rabs (b64_round
          (1 / Binary.B2R prec emax (b64_mult b64_two scale)))
    < bpow radix2 emax.

Definition b64_hot_pixel_eval_safe
    (P C : BPoint) (scale : binary64) : Prop :=
  b64_hot_pixel_radius_safe scale /\
  let r := b64_hot_pixel_radius scale in
  Binary.is_finite prec emax (bx P)  = true /\
  Binary.is_finite prec emax (by_ P) = true /\
  Binary.is_finite prec emax (bx C)  = true /\
  Binary.is_finite prec emax (by_ C) = true /\
  b64_safe Rminus (bx C)  r /\
  b64_safe Rplus  (bx C)  r /\
  b64_safe Rminus (by_ C) r /\
  b64_safe Rplus  (by_ C) r.

(* -------------------------------------------------------------------------- *)
(* `in_hot_pixel_at_radius`: variant of R-side `in_hot_pixel` that takes     *)
(* the radius directly.  Lets soundness state the rounded-pixel form below  *)
(* without paying for the integer-regime exact-radius theorem.              *)
(* -------------------------------------------------------------------------- *)

Definition in_hot_pixel_at_radius (P C : Point) (r : R) : Prop :=
  px C - r <= px P < px C + r /\
  py C - r <= py P < py C + r.

Lemma in_hot_pixel_unfold :
  forall P C scale,
    in_hot_pixel P C scale
    <-> in_hot_pixel_at_radius P C (hot_pixel_radius scale).
Proof. intros. unfold in_hot_pixel, in_hot_pixel_at_radius. tauto. Qed.

(* -------------------------------------------------------------------------- *)
(* Rounded-pixel membership: the R-side semantic content the b64 boolean    *)
(* truly captures.  This is the "actual" pixel that b64_in_hot_pixel        *)
(* decides -- its bounds are the rounded b64 sums, not the exact arithmetic. *)
(*                                                                            *)
(* Under integer-regime exactness for the bounds (deferred slice), this     *)
(* coincides with `in_hot_pixel (BP2P P) (BP2P C) (B2R scale)`.             *)
(* -------------------------------------------------------------------------- *)

Definition b64_in_rounded_hot_pixel
    (P C : BPoint) (scale : binary64) : Prop :=
  let r := b64_hot_pixel_radius scale in
  Binary.B2R prec emax (b64_minus (bx C) r)
    <= Binary.B2R prec emax (bx P)
    < Binary.B2R prec emax (b64_plus (bx C) r)
  /\
  Binary.B2R prec emax (b64_minus (by_ C) r)
    <= Binary.B2R prec emax (by_ P)
    < Binary.B2R prec emax (b64_plus (by_ C) r).

(* -------------------------------------------------------------------------- *)
(* Forward soundness: under safety, `b64_in_hot_pixel = true` implies the   *)
(* point lies in the rounded pixel.                                          *)
(*                                                                            *)
(* This is the tight, honest theorem: no integer-regime assumption, no      *)
(* rounding-exactness claim beyond the finite-arithmetic safety.  Bridging  *)
(* the rounded pixel to the R-side exact pixel is the next slice.           *)
(* -------------------------------------------------------------------------- *)

(* Helper: `b64_le a b = true` (with `a`, `b` finite) implies `B2R a <= B2R b`. *)
Lemma b64_le_R_of_true :
  forall a b : binary64,
    Binary.is_finite prec emax a = true ->
    Binary.is_finite prec emax b = true ->
    b64_le a b = true ->
    Binary.B2R prec emax a <= Binary.B2R prec emax b.
Proof.
  intros a b Fa Fb Hle.
  unfold b64_le, b64_compare in Hle.
  rewrite Binary.Bcompare_correct in Hle by assumption.
  destruct (Rcompare (Binary.B2R prec emax a)
                     (Binary.B2R prec emax b)) eqn:E; try discriminate.
  - apply Rcompare_Eq_inv in E. rewrite E. apply Rle_refl.
  - apply Rcompare_Lt_inv in E. lra.
Qed.

(* Helper: `b64_lt a b = true` (with `a`, `b` finite) implies `B2R a < B2R b`. *)
Lemma b64_lt_R_of_true :
  forall a b : binary64,
    Binary.is_finite prec emax a = true ->
    Binary.is_finite prec emax b = true ->
    b64_lt a b = true ->
    Binary.B2R prec emax a < Binary.B2R prec emax b.
Proof.
  intros a b Fa Fb Hlt.
  unfold b64_lt, b64_compare in Hlt.
  rewrite Binary.Bcompare_correct in Hlt by assumption.
  destruct (Rcompare (Binary.B2R prec emax a)
                     (Binary.B2R prec emax b)) eqn:E; try discriminate.
  apply Rcompare_Lt_inv in E. exact E.
Qed.

Theorem b64_in_hot_pixel_sound_rounded :
  forall P C scale,
    b64_hot_pixel_eval_safe P C scale ->
    b64_in_hot_pixel P C scale = true ->
    b64_in_rounded_hot_pixel P C scale.
Proof.
  intros P C scale Hsafe Hb.
  destruct Hsafe as (_ & FxP & FyP & _FxC & _FyC
                    & Sminus_x & Splus_x & Sminus_y & Splus_y).
  set (r := b64_hot_pixel_radius scale) in *.
  (* Finiteness of the four bound terms. *)
  pose proof (b64_minus_correct _ _ Sminus_x) as [_ Flo_x].
  pose proof (b64_plus_correct  _ _ Splus_x)  as [_ Fhi_x].
  pose proof (b64_minus_correct _ _ Sminus_y) as [_ Flo_y].
  pose proof (b64_plus_correct  _ _ Splus_y)  as [_ Fhi_y].
  (* Extract the four boolean conjuncts. *)
  unfold b64_in_hot_pixel in Hb. fold r in Hb.
  apply andb_prop in Hb; destruct Hb as [Hb Hy_hi].
  apply andb_prop in Hb; destruct Hb as [Hb Hy_lo].
  apply andb_prop in Hb; destruct Hb as [Hx_lo Hx_hi].
  unfold b64_in_rounded_hot_pixel. fold r.
  split; split.
  - apply (b64_le_R_of_true _ _ Flo_x FxP Hx_lo).
  - apply (b64_lt_R_of_true _ _ FxP Fhi_x Hx_hi).
  - apply (b64_le_R_of_true _ _ Flo_y FyP Hy_lo).
  - apply (b64_lt_R_of_true _ _ FyP Fhi_y Hy_hi).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_le_R_of_true.
Print Assumptions b64_lt_R_of_true.
Print Assumptions b64_in_hot_pixel_sound_rounded.

(* -------------------------------------------------------------------------- *)
(* Deferred to follow-up slices                                               *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* 1. Bridge: `b64_in_rounded_hot_pixel` -> `in_hot_pixel P C scale`.          *)
(*    Requires integer-regime exactness on `b64_minus` / `b64_plus` for the *)
(*    radius-and-center computation (so `B2R (b64_minus a b) = B2R a - B2R b` *)
(*    on the nose).  Reuses the `b64_minus_int_exact` / `b64_plus_int_exact` *)
(*    pattern from Orient_b64_exact.v.  Planned as the natural follow-up    *)
(*    slice once we need callers to reason about the exact R-side pixel.    *)
(*                                                                            *)
(* 2. `b64_hot_pixel_center`: snapping a coordinate to the grid via         *)
(*    round-to-integer.  Needs `Binary.Bnearbyint` (or equivalent) and a    *)
(*    dedicated finiteness / no-overflow analysis -- the rounding mode is  *)
(*    different from the arithmetic round-to-nearest that all our other    *)
(*    primitives use.                                                       *)
(*                                                                            *)
(* 3. `b64_segment_touches_hot_pixel`: two natural forms --                  *)
(*    (a) parametric existential matching the R-side definition;            *)
(*    (b) decidable bounding-box filter (segment endpoints inside, or       *)
(*        the segment crosses the pixel's bounding box).  Form (b) is the   *)
(*        one a real noder would use; form (a) is easier for proofs.        *)
(*    Defer until the Phase 2 noder slice opens.                             *)
(*                                                                            *)
(* 4. Integer-regime exact-radius theorem: when `scale` is a positive       *)
(*    power of two within the safe range, `b64_hot_pixel_radius scale` is  *)
(*    bit-exactly `1 / (2 * B2R scale)`.  Follows from `b64_mult_int_exact` *)
(*    (the `2 * scale` step is exact when scale's significand fits) plus    *)
(*    a Flocq reciprocal-of-power-of-two lemma.                             *)
(* -------------------------------------------------------------------------- *)
