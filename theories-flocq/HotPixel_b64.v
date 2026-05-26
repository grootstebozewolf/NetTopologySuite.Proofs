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
From NTS.Proofs.Flocq  Require Import Orient_b64_exact.
From NTS.Proofs.Flocq  Require Import B64_bridge.
From NTS.Proofs.Flocq  Require Import B64_lib.

Local Open Scope R_scope.

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

(* ============================================================================
   Slice 1.5: integer-regime bridge to the exact in_hot_pixel.
   ----------------------------------------------------------------------------
   Lifts `b64_in_hot_pixel_sound_rounded` from the rounded R-side model
   (`b64_in_rounded_hot_pixel`) to the exact `in_hot_pixel (BP2P P) (BP2P C)
   (1/2)` predicate.  Specialised to scale = b64_one (the unit-grid pixel)
   where the radius is exactly 1/2 and coord_int_safe coordinates give
   bit-exact bound computations.

   Why scale = b64_one specifically: at scale = 1 the radius is r = 1/2,
   and under coord_int_safe (|n| <= 2^25) the bounds bx +/- 1/2 = (2n +/- 1)/2
   have a 27-bit mantissa at most -- exactly representable in binary64's
   53-bit significand.  Generalising to other scale values requires either
   scale = 1/2 (giving integer-valued r = 1, matching `b64_minus_int_exact`
   directly) or new exactness machinery for dyadic-radius arithmetic; both
   are future slices.
   ============================================================================ *)

(* The binary64 representation of 1/2 = bpow radix2 (-1). *)
Definition b64_half : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64
    mode_NE 1 (-1) false.

(* The three constants b64_one, b64_two, b64_half all have F2R values that
   are powers of 2 well within the emax range, so their binary_normalize is
   bit-exact (round_generic is a no-op).  Proofs follow the
   `b64_veltkamp_C_R` pattern in B64_Pff_bridge.v. *)

(* Helper -- factor out the F2R-in-format round-no-op pattern. *)
Lemma b64_round_F2R_in_format :
  forall m e : Z,
    generic_format radix2 b64_fexp (F2R (Float radix2 m e)) ->
    Generic_fmt.round radix2 b64_fexp (round_mode mode_NE)
                       (F2R (Float radix2 m e))
      = F2R (Float radix2 m e).
Proof.
  intros m e Hfmt. apply b64_round_generic. exact Hfmt.
Qed.

Lemma B2R_and_finite_b64_one :
  Binary.B2R prec emax b64_one = 1
  /\ Binary.is_finite prec emax b64_one = true.
Proof.
  unfold b64_one.
  pose proof (Binary.binary_normalize_correct prec emax
                prec_gt_0_b64 prec_lt_emax_b64 mode_NE 1 0 false) as H.
  assert (HF2R : F2R (Float radix2 1 0) = 1)
    by (unfold F2R; simpl; lra).
  rewrite HF2R in H.
  assert (Hround : Generic_fmt.round radix2 (SpecFloat.fexp prec emax)
                    (round_mode mode_NE) 1 = 1).
  { apply b64_round_generic.
    replace 1 with (bpow radix2 0) by reflexivity.
    apply generic_format_bpow_b64. unfold emax. lia. }
  rewrite Hround in H.
  assert (Hbnd : Rabs 1 < bpow radix2 emax).
  { rewrite Rabs_R1. apply (bpow_lt radix2 0 emax). unfold emax. lia. }
  apply Rlt_bool_true in Hbnd. rewrite Hbnd in H.
  destruct H as (HB2R & Hfin & _).
  split; assumption.
Qed.

Lemma B2R_b64_one : Binary.B2R prec emax b64_one = 1.
Proof. apply B2R_and_finite_b64_one. Qed.

Lemma is_finite_b64_one : Binary.is_finite prec emax b64_one = true.
Proof. apply B2R_and_finite_b64_one. Qed.

Lemma B2R_and_finite_b64_two :
  Binary.B2R prec emax b64_two = 2
  /\ Binary.is_finite prec emax b64_two = true.
Proof.
  unfold b64_two.
  pose proof (Binary.binary_normalize_correct prec emax
                prec_gt_0_b64 prec_lt_emax_b64 mode_NE 2 0 false) as H.
  assert (HF2R : F2R (Float radix2 2 0) = 2)
    by (unfold F2R; simpl; lra).
  rewrite HF2R in H.
  assert (Hround : Generic_fmt.round radix2 (SpecFloat.fexp prec emax)
                    (round_mode mode_NE) 2 = 2).
  { apply b64_round_generic.
    replace 2 with (bpow radix2 1) by (simpl; lra).
    apply generic_format_bpow_b64. unfold emax. lia. }
  rewrite Hround in H.
  assert (Hbnd : Rabs 2 < bpow radix2 emax).
  { rewrite Rabs_pos_eq by lra.
    replace 2 with (bpow radix2 1) by (simpl; lra).
    apply (bpow_lt radix2 1 emax). unfold emax. lia. }
  apply Rlt_bool_true in Hbnd. rewrite Hbnd in H.
  destruct H as (HB2R & Hfin & _).
  split; assumption.
Qed.

Lemma B2R_b64_two : Binary.B2R prec emax b64_two = 2.
Proof. apply B2R_and_finite_b64_two. Qed.

Lemma is_finite_b64_two : Binary.is_finite prec emax b64_two = true.
Proof. apply B2R_and_finite_b64_two. Qed.

Lemma B2R_and_finite_b64_half :
  Binary.B2R prec emax b64_half = / 2
  /\ Binary.is_finite prec emax b64_half = true.
Proof.
  unfold b64_half.
  pose proof (Binary.binary_normalize_correct prec emax
                prec_gt_0_b64 prec_lt_emax_b64 mode_NE 1 (-1) false) as H.
  assert (HF2R : F2R (Float radix2 1 (-1)) = / 2)
    by (unfold F2R; simpl; lra).
  rewrite HF2R in H.
  assert (Hround : Generic_fmt.round radix2 (SpecFloat.fexp prec emax)
                    (round_mode mode_NE) (/ 2) = / 2).
  { apply b64_round_generic.
    replace (/ 2) with (bpow radix2 (-1)) by (simpl; lra).
    apply generic_format_bpow_b64. unfold emax. lia. }
  rewrite Hround in H.
  assert (Hbnd : Rabs (/ 2) < bpow radix2 emax).
  { rewrite Rabs_pos_eq by lra.
    replace (/ 2) with (bpow radix2 (-1)) by (simpl; lra).
    apply (bpow_lt radix2 (-1) emax). unfold emax. lia. }
  apply Rlt_bool_true in Hbnd. rewrite Hbnd in H.
  destruct H as (HB2R & Hfin & _).
  split; assumption.
Qed.

Lemma B2R_b64_half : Binary.B2R prec emax b64_half = / 2.
Proof. apply B2R_and_finite_b64_half. Qed.

Lemma is_finite_b64_half : Binary.is_finite prec emax b64_half = true.
Proof. apply B2R_and_finite_b64_half. Qed.

(* -------------------------------------------------------------------------- *)
(* Radius bit-exactness at scale = b64_one.                                   *)
(*                                                                            *)
(* Step 1 (mult): b64_mult b64_two b64_one computes round(2 * 1) = 2 (in     *)
(* format).  Step 2 (div): b64_div b64_one (...) computes round(1 / 2) = 1/2 *)
(* (in format).  Both rounds are no-ops, giving B2R = 1/2 bit-exactly.        *)
(* -------------------------------------------------------------------------- *)

Lemma b64_hot_pixel_radius_at_one :
  Binary.B2R prec emax (b64_hot_pixel_radius b64_one) = / 2
  /\ Binary.is_finite prec emax (b64_hot_pixel_radius b64_one) = true.
Proof.
  unfold b64_hot_pixel_radius.
  pose proof B2R_b64_one as HoneR.
  pose proof is_finite_b64_one as FoneF.
  pose proof B2R_b64_two as HtwoR.
  pose proof is_finite_b64_two as FtwoF.
  (* Step 1: b64_mult b64_two b64_one = round(2). *)
  assert (Hmult_safe : b64_safe Rmult b64_two b64_one).
  { unfold b64_safe. split; [exact FtwoF | split; [exact FoneF |]].
    rewrite HtwoR, HoneR.
    replace (2 * 1) with 2 by lra.
    assert (Hfmt2 : generic_format radix2 b64_fexp 2).
    { replace 2 with (bpow radix2 1) by (simpl; lra).
      apply generic_format_bpow_b64. unfold emax. lia. }
    rewrite (b64_round_generic _ Hfmt2).
    rewrite Rabs_pos_eq by lra.
    replace 2 with (bpow radix2 1) by (simpl; lra).
    apply (bpow_lt radix2 1 emax). unfold emax. lia. }
  pose proof (b64_mult_correct _ _ Hmult_safe) as [HmultR HmultF].
  rewrite HtwoR, HoneR in HmultR.
  replace (2 * 1) with 2 in HmultR by lra.
  assert (Hfmt2 : generic_format radix2 b64_fexp 2).
  { replace 2 with (bpow radix2 1) by (simpl; lra).
    apply generic_format_bpow_b64. unfold emax. lia. }
  rewrite (b64_round_generic _ Hfmt2) in HmultR.
  (* Step 2: b64_div b64_one (b64_mult b64_two b64_one) = round(1/2). *)
  assert (Hdiv_nonzero : Binary.B2R prec emax (b64_mult b64_two b64_one) <> 0).
  { rewrite HmultR. lra. }
  assert (Hdiv_bnd : Rabs (b64_round
                            (Binary.B2R prec emax b64_one
                             / Binary.B2R prec emax
                                 (b64_mult b64_two b64_one)))
                       < bpow radix2 emax).
  { rewrite HoneR, HmultR.
    replace (1 / 2) with (/ 2) by lra.
    assert (Hfmt_half : generic_format radix2 b64_fexp (/ 2)).
    { replace (/ 2) with (bpow radix2 (-1)) by (simpl; lra).
      apply generic_format_bpow_b64. unfold emax. lia. }
    rewrite (b64_round_generic _ Hfmt_half).
    rewrite Rabs_pos_eq by lra.
    replace (/ 2) with (bpow radix2 (-1)) by (simpl; lra).
    apply (bpow_lt radix2 (-1) emax). unfold emax. lia. }
  pose proof (b64_div_correct _ _ FoneF HmultF Hdiv_nonzero Hdiv_bnd)
    as [HdivR HdivF].
  rewrite HoneR, HmultR in HdivR.
  replace (1 / 2) with (/ 2) in HdivR by lra.
  assert (Hfmt_half : generic_format radix2 b64_fexp (/ 2)).
  { replace (/ 2) with (bpow radix2 (-1)) by (simpl; lra).
    apply generic_format_bpow_b64. unfold emax. lia. }
  rewrite (b64_round_generic _ Hfmt_half) in HdivR.
  split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Bound bit-exactness: under coord_int_safe, b64_minus / b64_plus with the   *)
(* radius 1/2 is bit-exact.  The result `IZR n +/- 1/2 = (2n +/- 1) / 2` has  *)
(* a 27-bit mantissa at most (|n| <= 2^25 implies |2n +/- 1| < 2^27), well   *)
(* within binary64's 53-bit significand.                                      *)
(* -------------------------------------------------------------------------- *)

(* Helper: F2R values with mantissa fitting in 27 bits and exponent -1 are in
   b64_fexp generic_format.  Lower-bounding cexp via the mag bound. *)
Lemma generic_format_F2R_27bit_exp_neg1 :
  forall m : Z,
    (Z.abs m < 2 ^ 27)%Z ->
    generic_format radix2 b64_fexp (F2R (Float radix2 m (-1))).
Proof.
  intros m Hm.
  destruct (Z.eq_dec m 0) as [-> | Hnz].
  - replace (F2R (Float radix2 0 (-1))) with 0
      by (unfold F2R; simpl; lra).
    apply generic_format_0.
  - apply generic_format_F2R. intros _.
    unfold cexp, b64_fexp, SpecFloat.fexp.
    apply Z.max_lub.
    + (* mag(F2R radix2 m -1) = mag(IZR m) - 1, and mag(IZR m) <= 27. *)
      rewrite (mag_F2R radix2 m (-1) Hnz).
      assert (Hmag_m : (mag radix2 (IZR m) <= 27)%Z).
      { apply mag_le_bpow.
        - apply IZR_neq. exact Hnz.
        - rewrite <- abs_IZR.
          rewrite <- (IZR_Zpower radix2 27) by lia.
          apply IZR_lt. exact Hm. }
      unfold prec. lia.
    + unfold SpecFloat.emin, emax, prec. lia.
Qed.

Lemma b64_minus_half_int_exact :
  forall x : binary64,
    coord_int_safe x ->
    Binary.B2R prec emax (b64_minus x b64_half)
      = Binary.B2R prec emax x - / 2
    /\ Binary.is_finite prec emax (b64_minus x b64_half) = true.
Proof.
  intros x (Fx & n & HxR & Hxb).
  pose proof B2R_b64_half as HhalfR.
  pose proof is_finite_b64_half as FhalfF.
  (* Express the exact result as F2R (Float radix2 (2n-1) -1) and show
     it's in generic_format. *)
  assert (Hr_F2R : Binary.B2R prec emax x - / 2
                   = F2R (Float radix2 (2 * n - 1)%Z (-1))).
  { rewrite HxR. unfold F2R, Fnum, Fexp.
    assert (Hbpow : bpow radix2 (-1) = / 2) by (simpl; lra).
    rewrite Hbpow.
    rewrite minus_IZR. rewrite mult_IZR. simpl. lra. }
  assert (Hbnd_m : (Z.abs (2 * n - 1) < 2 ^ 27)%Z).
  { assert (Hn_bnd : (Z.abs n <= 2 ^ 25)%Z) by exact Hxb. lia. }
  assert (Hr_fmt : generic_format radix2 b64_fexp
                     (Binary.B2R prec emax x - / 2)).
  { rewrite Hr_F2R. apply generic_format_F2R_27bit_exp_neg1. exact Hbnd_m. }
  (* Safety: |B2R x - /2| <= |B2R x| + /2 <= 2^25 + /2 << 2^emax. *)
  assert (Hsafe : b64_safe Rminus x b64_half).
  { unfold b64_safe. split; [exact Fx | split; [exact FhalfF |]].
    rewrite HhalfR.
    rewrite (b64_round_generic _ Hr_fmt).
    rewrite HxR.
    apply Z.abs_le in Hxb. destruct Hxb as [Hlo Hhi].
    apply IZR_le in Hlo. apply IZR_le in Hhi.
    rewrite opp_IZR in Hlo.
    assert (Heq25 : IZR (2 ^ 25) = bpow radix2 25).
    { replace (2 ^ 25)%Z with (radix2 ^ 25)%Z by reflexivity.
      apply IZR_Zpower. lia. }
    rewrite Heq25 in Hlo, Hhi.
    assert (Hgap : bpow radix2 25 + 1 < bpow radix2 emax).
    { apply (Rle_lt_trans _ (bpow radix2 26)).
      - assert (Hge1 : 1 <= bpow radix2 25).
        { replace 1 with (bpow radix2 0) by reflexivity.
          apply bpow_le. lia. }
        replace (bpow radix2 26) with (2 * bpow radix2 25).
        + lra.
        + replace 2 with (bpow radix2 1) by (simpl; lra).
          rewrite <- bpow_plus. reflexivity.
      - apply bpow_lt. unfold emax. lia. }
    apply Rabs_def1; lra. }
  pose proof (b64_minus_correct _ _ Hsafe) as [HminusR HminusF].
  rewrite HhalfR in HminusR.
  rewrite (b64_round_generic _ Hr_fmt) in HminusR.
  split; assumption.
Qed.

Lemma b64_plus_half_int_exact :
  forall x : binary64,
    coord_int_safe x ->
    Binary.B2R prec emax (b64_plus x b64_half)
      = Binary.B2R prec emax x + / 2
    /\ Binary.is_finite prec emax (b64_plus x b64_half) = true.
Proof.
  intros x (Fx & n & HxR & Hxb).
  pose proof B2R_b64_half as HhalfR.
  pose proof is_finite_b64_half as FhalfF.
  assert (Hr_F2R : Binary.B2R prec emax x + / 2
                   = F2R (Float radix2 (2 * n + 1)%Z (-1))).
  { rewrite HxR. unfold F2R, Fnum, Fexp.
    assert (Hbpow : bpow radix2 (-1) = / 2) by (simpl; lra).
    rewrite Hbpow.
    rewrite plus_IZR. rewrite mult_IZR. simpl. lra. }
  assert (Hbnd_m : (Z.abs (2 * n + 1) < 2 ^ 27)%Z).
  { assert (Hn_bnd : (Z.abs n <= 2 ^ 25)%Z) by exact Hxb. lia. }
  assert (Hr_fmt : generic_format radix2 b64_fexp
                     (Binary.B2R prec emax x + / 2)).
  { rewrite Hr_F2R. apply generic_format_F2R_27bit_exp_neg1. exact Hbnd_m. }
  assert (Hsafe : b64_safe Rplus x b64_half).
  { unfold b64_safe. split; [exact Fx | split; [exact FhalfF |]].
    rewrite HhalfR.
    rewrite (b64_round_generic _ Hr_fmt).
    rewrite HxR.
    apply Z.abs_le in Hxb. destruct Hxb as [Hlo Hhi].
    apply IZR_le in Hlo. apply IZR_le in Hhi.
    rewrite opp_IZR in Hlo.
    assert (Heq25 : IZR (2 ^ 25) = bpow radix2 25).
    { replace (2 ^ 25)%Z with (radix2 ^ 25)%Z by reflexivity.
      apply IZR_Zpower. lia. }
    rewrite Heq25 in Hlo, Hhi.
    assert (Hgap : bpow radix2 25 + 1 < bpow radix2 emax).
    { apply (Rle_lt_trans _ (bpow radix2 26)).
      - assert (Hge1 : 1 <= bpow radix2 25).
        { replace 1 with (bpow radix2 0) by reflexivity.
          apply bpow_le. lia. }
        replace (bpow radix2 26) with (2 * bpow radix2 25).
        + lra.
        + replace 2 with (bpow radix2 1) by (simpl; lra).
          rewrite <- bpow_plus. reflexivity.
      - apply bpow_lt. unfold emax. lia. }
    apply Rabs_def1; lra. }
  pose proof (b64_plus_correct _ _ Hsafe) as [HplusR HplusF].
  rewrite HhalfR in HplusR.
  rewrite (b64_round_generic _ Hr_fmt) in HplusR.
  split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline bridge: under coord_int_safe on all four point coordinates +     *)
(* the existing eval-safety, `b64_in_hot_pixel P C b64_one = true` implies  *)
(* the exact R-side `in_hot_pixel (BP2P P) (BP2P C) 1`.                      *)
(*                                                                            *)
(* This is the Slice 1.5 deliverable -- the rounded-pixel form proved in    *)
(* `b64_in_hot_pixel_sound_rounded` is lifted to the exact in_hot_pixel     *)
(* predicate by showing the rounded boundaries coincide with the exact      *)
(* IZR n +/- 1/2 boundaries under the integer-coord regime.                  *)
(* -------------------------------------------------------------------------- *)

Theorem b64_in_hot_pixel_sound :
  forall P C : BPoint,
    coord_int_safe (bx P)  ->
    coord_int_safe (by_ P) ->
    coord_int_safe (bx C)  ->
    coord_int_safe (by_ C) ->
    b64_hot_pixel_eval_safe P C b64_one ->
    b64_in_hot_pixel P C b64_one = true ->
    in_hot_pixel (BP2P P) (BP2P C) 1.
Proof.
  intros P C HiPx HiPy HiCx HiCy Hsafe Hb.
  pose proof (b64_in_hot_pixel_sound_rounded _ _ _ Hsafe Hb) as Hrounded.
  unfold b64_in_rounded_hot_pixel in Hrounded.
  pose proof b64_hot_pixel_radius_at_one as [HrR HrF].
  set (r := b64_hot_pixel_radius b64_one) in *.
  (* Rewrite the four bound expressions to their exact integer-plus-half forms. *)
  destruct HiCx as (FxC & ncx & HcxR & Hcxb).
  destruct HiCy as (FyC & ncy & HcyR & Hcyb).
  destruct HiPx as (FxP & npx & HpxR & Hpxb).
  destruct HiPy as (FyP & npy & HpyR & Hpyb).
  destruct Hrounded as [[Hxlo Hxhi] [Hylo Hyhi]].
  unfold in_hot_pixel, BP2P, px, py. simpl.
  unfold hot_pixel_radius.
  replace (/ (2 * 1)) with (/ 2) by lra.
  (* For each of the four bound terms, exactness gives B2R (...) = IZR n +/- /2. *)
  (* Reuses the b64_minus_correct / b64_plus_correct + generic_format reasoning
     from b64_minus_half_int_exact / b64_plus_half_int_exact, instantiated at
     `r` rather than `b64_half` (both have the same B2R = /2). *)
  assert (Hmx_exact : Binary.B2R prec emax (b64_minus (bx C) r)
                        = Binary.B2R prec emax (bx C) - / 2).
  { (* B2R (b64_minus (bx C) r) = b64_round (B2R (bx C) - B2R r) = b64_round (IZR ncx - /2). *)
    assert (Hfmt : generic_format radix2 b64_fexp
                     (Binary.B2R prec emax (bx C) - / 2)).
    { rewrite HcxR.
      assert (Heq : IZR ncx - / 2 = F2R (Float radix2 (2 * ncx - 1)%Z (-1))).
      { unfold F2R, Fnum, Fexp.
        assert (Hbpow : bpow radix2 (-1) = / 2) by (simpl; lra).
        rewrite Hbpow. rewrite minus_IZR. rewrite mult_IZR. simpl. lra. }
      rewrite Heq. apply generic_format_F2R_27bit_exp_neg1. lia. }
    pose proof (proj1 Hsafe) as Hrad_safe.
    destruct Hsafe as (_ & _ & _ & _ & _ & Sminus_x & _).
    pose proof (b64_minus_correct _ _ Sminus_x) as [HmxR _].
    fold r in HmxR. rewrite HmxR, HrR.
    apply b64_round_generic. exact Hfmt. }
  assert (Hpx_exact : Binary.B2R prec emax (b64_plus (bx C) r)
                        = Binary.B2R prec emax (bx C) + / 2).
  { assert (Hfmt : generic_format radix2 b64_fexp
                     (Binary.B2R prec emax (bx C) + / 2)).
    { rewrite HcxR.
      assert (Heq : IZR ncx + / 2 = F2R (Float radix2 (2 * ncx + 1)%Z (-1))).
      { unfold F2R, Fnum, Fexp.
        assert (Hbpow : bpow radix2 (-1) = / 2) by (simpl; lra).
        rewrite Hbpow. rewrite plus_IZR. rewrite mult_IZR. simpl. lra. }
      rewrite Heq. apply generic_format_F2R_27bit_exp_neg1. lia. }
    destruct Hsafe as (_ & _ & _ & _ & _ & _ & Splus_x & _).
    pose proof (b64_plus_correct _ _ Splus_x) as [HpxR' _].
    fold r in HpxR'. rewrite HpxR', HrR.
    apply b64_round_generic. exact Hfmt. }
  assert (Hmy_exact : Binary.B2R prec emax (b64_minus (by_ C) r)
                        = Binary.B2R prec emax (by_ C) - / 2).
  { assert (Hfmt : generic_format radix2 b64_fexp
                     (Binary.B2R prec emax (by_ C) - / 2)).
    { rewrite HcyR.
      assert (Heq : IZR ncy - / 2 = F2R (Float radix2 (2 * ncy - 1)%Z (-1))).
      { unfold F2R, Fnum, Fexp.
        assert (Hbpow : bpow radix2 (-1) = / 2) by (simpl; lra).
        rewrite Hbpow. rewrite minus_IZR. rewrite mult_IZR. simpl. lra. }
      rewrite Heq. apply generic_format_F2R_27bit_exp_neg1. lia. }
    destruct Hsafe as (_ & _ & _ & _ & _ & _ & _ & Sminus_y & _).
    pose proof (b64_minus_correct _ _ Sminus_y) as [HmyR _].
    fold r in HmyR. rewrite HmyR, HrR.
    apply b64_round_generic. exact Hfmt. }
  assert (Hpy_exact : Binary.B2R prec emax (b64_plus (by_ C) r)
                        = Binary.B2R prec emax (by_ C) + / 2).
  { assert (Hfmt : generic_format radix2 b64_fexp
                     (Binary.B2R prec emax (by_ C) + / 2)).
    { rewrite HcyR.
      assert (Heq : IZR ncy + / 2 = F2R (Float radix2 (2 * ncy + 1)%Z (-1))).
      { unfold F2R, Fnum, Fexp.
        assert (Hbpow : bpow radix2 (-1) = / 2) by (simpl; lra).
        rewrite Hbpow. rewrite plus_IZR. rewrite mult_IZR. simpl. lra. }
      rewrite Heq. apply generic_format_F2R_27bit_exp_neg1. lia. }
    destruct Hsafe as (_ & _ & _ & _ & _ & _ & _ & _ & Splus_y).
    pose proof (b64_plus_correct _ _ Splus_y) as [HpyR' _].
    fold r in HpyR'. rewrite HpyR', HrR.
    apply b64_round_generic. exact Hfmt. }
  rewrite Hmx_exact in Hxlo. rewrite Hpx_exact in Hxhi.
  rewrite Hmy_exact in Hylo. rewrite Hpy_exact in Hyhi.
  split; [split | split]; assumption.
Qed.

(* ============================================================================
   Slice 2: b64_segment_touches_hot_pixel_spec -- form (a) parametric
   existential.
   ----------------------------------------------------------------------------
   The proof-friendly form of "segment touches pixel" -- mirrors the R-side
   `segment_touches_hot_pixel` directly via BP2P composition.  Form (b) (a
   decidable bounding-box filter) is a future engagement that will prove
   soundness against THIS predicate; form (a) is the middle layer in the
   soundness chain (b) -> (a) -> R-side.

   The definition is propositionally equivalent to the R-side predicate
   composed with BP2P -- this slice's value is in the three endpoint lemmas
   that bridge from the b64 boolean decision `b64_in_hot_pixel = true` to
   the b64-side existential, citing Slice 1.5's `b64_in_hot_pixel_sound`.
   ============================================================================ *)

Definition b64_segment_touches_hot_pixel_spec (P0 P1 C : BPoint) : Prop :=
  segment_touches_hot_pixel (BP2P P0) (BP2P P1) (BP2P C) 1.

(* Endpoint at P0 (t = 0): if P0 lies in the b64 unit-grid pixel, then the
   segment [P0, P1] touches the pixel.  Bridges from the b64 boolean
   decision via b64_in_hot_pixel_sound (Slice 1.5), then applies the R-side
   segment_touches_hot_pixel_l. *)
Lemma b64_segment_touches_hot_pixel_spec_l :
  forall P0 P1 C : BPoint,
    coord_int_safe (bx P0)  ->
    coord_int_safe (by_ P0) ->
    coord_int_safe (bx C)   ->
    coord_int_safe (by_ C)  ->
    b64_hot_pixel_eval_safe P0 C b64_one ->
    b64_in_hot_pixel P0 C b64_one = true ->
    b64_segment_touches_hot_pixel_spec P0 P1 C.
Proof.
  intros P0 P1 C HiP0x HiP0y HiCx HiCy Hsafe Hb.
  unfold b64_segment_touches_hot_pixel_spec.
  apply segment_touches_hot_pixel_l.
  apply (b64_in_hot_pixel_sound _ _ HiP0x HiP0y HiCx HiCy Hsafe Hb).
Qed.

(* Endpoint at P1 (t = 1): symmetric to _l. *)
Lemma b64_segment_touches_hot_pixel_spec_r :
  forall P0 P1 C : BPoint,
    coord_int_safe (bx P1)  ->
    coord_int_safe (by_ P1) ->
    coord_int_safe (bx C)   ->
    coord_int_safe (by_ C)  ->
    b64_hot_pixel_eval_safe P1 C b64_one ->
    b64_in_hot_pixel P1 C b64_one = true ->
    b64_segment_touches_hot_pixel_spec P0 P1 C.
Proof.
  intros P0 P1 C HiP1x HiP1y HiCx HiCy Hsafe Hb.
  unfold b64_segment_touches_hot_pixel_spec.
  apply segment_touches_hot_pixel_r.
  apply (b64_in_hot_pixel_sound _ _ HiP1x HiP1y HiCx HiCy Hsafe Hb).
Qed.

(* Degenerate segment (P0 = P1): touches iff the single endpoint lies in
   the pixel.  Lifts segment_touches_hot_pixel_degenerate (HotPixel.v:184)
   in the forward direction (in_hot_pixel -> segment_touches). *)
Lemma b64_segment_touches_hot_pixel_spec_degenerate :
  forall P C : BPoint,
    coord_int_safe (bx P)  ->
    coord_int_safe (by_ P) ->
    coord_int_safe (bx C)  ->
    coord_int_safe (by_ C) ->
    b64_hot_pixel_eval_safe P C b64_one ->
    b64_in_hot_pixel P C b64_one = true ->
    b64_segment_touches_hot_pixel_spec P P C.
Proof.
  intros P C HiPx HiPy HiCx HiCy Hsafe Hb.
  unfold b64_segment_touches_hot_pixel_spec.
  apply segment_touches_hot_pixel_degenerate.
  apply (b64_in_hot_pixel_sound _ _ HiPx HiPy HiCx HiCy Hsafe Hb).
Qed.

(* Soundness: the b64-side predicate implies the R-side predicate composed
   with BP2P.  This is the identity unfolding (the spec IS defined as the
   R-side predicate composed with BP2P); stated explicitly so form (b) --
   the decidable bounding-box filter -- can cite it as the middle layer
   of the soundness chain
        (b) decidable BB filter
          \-> b64_segment_touches_hot_pixel_spec       [this slice]
              \-> segment_touches_hot_pixel (R-side)   [via this theorem]   *)
Theorem b64_segment_touches_hot_pixel_sound :
  forall P0 P1 C : BPoint,
    b64_segment_touches_hot_pixel_spec P0 P1 C ->
    segment_touches_hot_pixel (BP2P P0) (BP2P P1) (BP2P C) 1.
Proof.
  intros P0 P1 C H. exact H.
Qed.

(* ============================================================================
   Slice 3 (partial): b64_segment_touches_hot_pixel_endpoints -- form (b)
   endpoint-only decidable filter.
   ----------------------------------------------------------------------------
   Form (b)'s soundness target is form (a) -- the chain (b) -> (a) -> R-side
   requires form (b) to be a STRICT SUBSET of form (a) (no false positives).
   A naive BB-overlap test fails this: BB-overlap is a necessary but not
   sufficient condition for the segment to touch the pixel (counter-example:
   segment (0, 1) -> (2, -1) has BB overlapping pixel-at-(1.5, 0.4)'s BB
   but does not pass through the pixel).

   The full form (b) -- including segment-crosses-pixel-boundary detection --
   requires IVT (Stdlib's `IVT_cor` in Rsqrt_def.v) applied to the linear
   convex-combination function.  That is the next engagement.

   This slice ships the ENDPOINT-ONLY subset under an explicit
   `_endpoints` suffix:
     b64_segment_touches_hot_pixel_endpoints P0 P1 C :=
       b64_in_hot_pixel P0 C b64_one || b64_in_hot_pixel P1 C b64_one

   This is sound against form (a) by Slice 2's `_spec_l` and `_spec_r`
   (witnesses t=0 and t=1).  The unqualified name
   `b64_segment_touches_hot_pixel` is intentionally reserved for when the
   IVT-based crossing test lands -- a future slice extends this with the
   crossing disjunct and ships the full form (b) under the unqualified
   name.
   ============================================================================ *)

Definition b64_segment_touches_hot_pixel_endpoints
    (P0 P1 C : BPoint) : bool :=
  b64_in_hot_pixel P0 C b64_one || b64_in_hot_pixel P1 C b64_one.

(* Endpoint-only soundness: a `true` from the endpoint filter implies the
   form (a) parametric existential.  Case-splits on which disjunct fired
   and cites Slice 2's `_spec_l` (t = 0) or `_spec_r` (t = 1). *)
Theorem b64_segment_touches_hot_pixel_endpoints_sound :
  forall P0 P1 C : BPoint,
    coord_int_safe (bx P0)  -> coord_int_safe (by_ P0) ->
    coord_int_safe (bx P1)  -> coord_int_safe (by_ P1) ->
    coord_int_safe (bx C)   -> coord_int_safe (by_ C)  ->
    b64_hot_pixel_eval_safe P0 C b64_one ->
    b64_hot_pixel_eval_safe P1 C b64_one ->
    b64_segment_touches_hot_pixel_endpoints P0 P1 C = true ->
    b64_segment_touches_hot_pixel_spec P0 P1 C.
Proof.
  intros P0 P1 C HiP0x HiP0y HiP1x HiP1y HiCx HiCy Hsafe0 Hsafe1 Hb.
  unfold b64_segment_touches_hot_pixel_endpoints in Hb.
  apply Bool.orb_true_iff in Hb. destruct Hb as [HbP0 | HbP1].
  - apply (b64_segment_touches_hot_pixel_spec_l _ _ _
             HiP0x HiP0y HiCx HiCy Hsafe0 HbP0).
  - apply (b64_segment_touches_hot_pixel_spec_r _ _ _
             HiP1x HiP1y HiCx HiCy Hsafe1 HbP1).
Qed.

(* Full soundness chain when composed through Slice 2's spec_sound:
       b64_segment_touches_hot_pixel_endpoints P0 P1 C = true
         -> b64_segment_touches_hot_pixel_spec P0 P1 C       [endpoints_sound]
         -> segment_touches_hot_pixel (BP2P P0) (BP2P P1) (BP2P C) 1  [spec_sound]
   This corollary collapses the two steps for callers who want to skip
   the form-(a) middle layer. *)
Corollary b64_segment_touches_hot_pixel_endpoints_sound_R :
  forall P0 P1 C : BPoint,
    coord_int_safe (bx P0)  -> coord_int_safe (by_ P0) ->
    coord_int_safe (bx P1)  -> coord_int_safe (by_ P1) ->
    coord_int_safe (bx C)   -> coord_int_safe (by_ C)  ->
    b64_hot_pixel_eval_safe P0 C b64_one ->
    b64_hot_pixel_eval_safe P1 C b64_one ->
    b64_segment_touches_hot_pixel_endpoints P0 P1 C = true ->
    segment_touches_hot_pixel (BP2P P0) (BP2P P1) (BP2P C) 1.
Proof.
  intros P0 P1 C HiP0x HiP0y HiP1x HiP1y HiCx HiCy Hsafe0 Hsafe1 Hb.
  apply b64_segment_touches_hot_pixel_sound.
  apply (b64_segment_touches_hot_pixel_endpoints_sound _ _ _
           HiP0x HiP0y HiP1x HiP1y HiCx HiCy Hsafe0 Hsafe1 Hb).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_le_R_of_true.
Print Assumptions b64_lt_R_of_true.
Print Assumptions b64_in_hot_pixel_sound_rounded.
Print Assumptions b64_hot_pixel_radius_at_one.
Print Assumptions b64_minus_half_int_exact.
Print Assumptions b64_plus_half_int_exact.
Print Assumptions b64_in_hot_pixel_sound.
Print Assumptions b64_segment_touches_hot_pixel_spec_l.
Print Assumptions b64_segment_touches_hot_pixel_spec_r.
Print Assumptions b64_segment_touches_hot_pixel_spec_degenerate.
Print Assumptions b64_segment_touches_hot_pixel_sound.
Print Assumptions b64_segment_touches_hot_pixel_endpoints_sound.
Print Assumptions b64_segment_touches_hot_pixel_endpoints_sound_R.

(* -------------------------------------------------------------------------- *)
(* Deferred to follow-up slices                                               *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* 1. [LANDED, Slice 1.5] Bridge: `b64_in_rounded_hot_pixel` ->              *)
(*    `in_hot_pixel P C scale`.  Specialised to scale = b64_one (unit-grid *)
(*    pixel, r = 1/2) in `b64_in_hot_pixel_sound`.  Under coord_int_safe   *)
(*    (|n| <= 2^25) on all four point coordinates, the rounded boundaries *)
(*    coincide with the exact integer +/- 1/2 boundaries.  Generalising to *)
(*    arbitrary power-of-two scales remains for a future slice (requires   *)
(*    proving generic_format on `IZR n +/- bpow (-(k+1))` for the          *)
(*    appropriate magnitude regime).                                         *)
(*                                                                            *)
(* 2. `b64_hot_pixel_center`: snapping a coordinate to the grid via         *)
(*    round-to-integer.  Needs `Binary.Bnearbyint` (or equivalent) and a    *)
(*    dedicated finiteness / no-overflow analysis -- the rounding mode is  *)
(*    different from the arithmetic round-to-nearest that all our other    *)
(*    primitives use.                                                       *)
(*                                                                            *)
(* 3. `b64_segment_touches_hot_pixel`: two natural forms --                  *)
(*    (a) [LANDED, Slice 2] parametric existential matching the R-side      *)
(*        definition.  `b64_segment_touches_hot_pixel_spec` composes the   *)
(*        R-side `segment_touches_hot_pixel` with `BP2P`; three endpoint   *)
(*        lemmas (_spec_l/r/degenerate) lift from the boolean              *)
(*        `b64_in_hot_pixel = true` via Slice 1.5's `b64_in_hot_pixel_sound`.*)
(*        `b64_segment_touches_hot_pixel_sound` documents the bridge to   *)
(*        the R-side as the identity unfolding.  Form (a) is the middle   *)
(*        layer in the eventual soundness chain (b) -> (a) -> R-side.     *)
(*    (b) decidable bounding-box filter (segment endpoints inside, or       *)
(*        the segment crosses the pixel's bounding box).                     *)
(*        [PARTIAL, Slice 3] -- the endpoint-only subset has landed as       *)
(*        `b64_segment_touches_hot_pixel_endpoints` (a bool returning       *)
(*        true if either endpoint passes `b64_in_hot_pixel`).  Sound to    *)
(*        form (a) via Slice 2's `_spec_l` and `_spec_r`.  The unqualified *)
(*        name `b64_segment_touches_hot_pixel` is reserved for when the    *)
(*        IVT-based segment-crosses-pixel-boundary test lands and extends  *)
(*        the disjunctive filter; that is the next engagement.  Form (b)  *)
(*        cannot be a pure BB-overlap test -- BB-overlap is necessary but  *)
(*        not sufficient for the segment to touch the pixel; this design  *)
(*        observation is formally certified by                              *)
(*        `bb_overlap_not_sufficient_for_touches` in theories/HotPixel.v   *)
(*        (Slice 4): witness P0=(0,1), P1=(3/2,-1), C=(3/2,1/2) has        *)
(*        BB-overlap on both axes but no t in [0,1] places the convex      *)
(*        combination inside the half-open pixel.  Hence soundness to form *)
(*        (a) requires the actual crossing test via per-edge analysis or  *)
(*        IVT (Stdlib's `IVT_cor` in Rsqrt_def.v); the half-open pixel    *)
(*        semantics complicate the top/right (open) edges, where the      *)
(*        edge-crossing witness lies on the excluded boundary and an      *)
(*        epsilon-shift or midpoint construction is needed.  That is the  *)
(*        next engagement -- this slice ships only the design-observation *)
(*        certificate.                                                      *)
(*                                                                            *)
(* 4. Integer-regime exact-radius theorem: when `scale` is a positive       *)
(*    power of two within the safe range, `b64_hot_pixel_radius scale` is  *)
(*    bit-exactly `1 / (2 * B2R scale)`.  Follows from `b64_mult_int_exact` *)
(*    (the `2 * scale` step is exact when scale's significand fits) plus    *)
(*    a Flocq reciprocal-of-power-of-two lemma.                             *)
(* -------------------------------------------------------------------------- *)
