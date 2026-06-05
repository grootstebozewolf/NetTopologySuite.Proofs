(* ============================================================================
   NetTopologySuite.Proofs.Flocq.SnapRoundingScale_b64
   ----------------------------------------------------------------------------
   C1 power-of-two snap rounding: the scaled binary64 coordinate snap and its
   exact bridge to the R-side `snap_round_coord`.

   `HotPixel_b64.snap_round_coord x scale = round_FIX0 (x * scale) / scale`
   snaps a real to the grid of spacing `1/scale`.  `SnapRounding_b64.v` proves
   the snap-rounding invariants on the UNIT grid only, because its binary64
   snap `b64_snap_coord = Bnearbyint(.)` hard-codes `scale = 1` (the multiply
   and divide are absent).

   This file introduces the SCALED binary64 snap

       b64_snap_coord_scaled x s = b64_div (b64_snap_coord (b64_mult x s)) s

   (multiply by the scale, round to the integer grid, divide back) and proves
   it computes the R-side `snap_round_coord` EXACTLY when the scale `s` is a
   positive power of two `2^k`.  The proof composes the two exactness facts of
   `DivRoundPow2_b64.v`:

     - `b64_mult_pow2_exact`  : the `b64_mult x s` step is exact (B2R x * 2^k),
     - `b64_div_pow2_exact`   : the `b64_div .. s` step is exact (.. * 2^-k),

   sandwiching the unit-grid integer rounding `b64_snap_coord_B2R`.  Because
   both float steps are exact, the binary64 pipeline sees the SAME real
   argument the R-side rounds, so the verdicts coincide on the nose.

   This is the bridge slice; the follow-up lifts `SnapRounding_b64.v`'s
   idempotence and passes-through preservation from `scale = 1` to `2^k`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs        Require Import Distance HotPixel.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import B64_lib.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import DivRoundPow2_b64.

Local Open Scope R_scope.

Local Notation emin := (3 - emax - prec)%Z.

(* -------------------------------------------------------------------------- *)
(* The scaled binary64 coordinate snap.                                       *)
(* -------------------------------------------------------------------------- *)

Definition b64_snap_coord_scaled (x s : binary64) : binary64 :=
  b64_div (b64_snap_coord (b64_mult x s)) s.

(* -------------------------------------------------------------------------- *)
(* Exact bridge: for a power-of-two scale, the scaled binary64 snap computes  *)
(* the R-side `snap_round_coord` on the nose.                                  *)
(*                                                                            *)
(* Premises:                                                                   *)
(*   - `s` is the power of two `2^k` with `k >= 0` (grid at least unit-fine), *)
(*   - `emin <= -k` (snapped values stay in the normal range),                *)
(*   - no overflow on the pre-rounding multiply,                              *)
(*   - the rounded integer fits the safe window `|n| <= 2^prec`.              *)
(* -------------------------------------------------------------------------- *)

Lemma b64_snap_coord_scaled_B2R :
  forall (x s : binary64) (k : Z),
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax s = true ->
    Binary.B2R prec emax s = bpow radix2 k ->
    (0 <= k)%Z ->
    (emin <= - k)%Z ->
    Rabs (Binary.B2R prec emax x * bpow radix2 k) < bpow radix2 emax ->
    (Z.abs (round_mode mode_NE (Binary.B2R prec emax x * bpow radix2 k))
       <= 2 ^ prec)%Z ->
    Binary.B2R prec emax (b64_snap_coord_scaled x s)
      = snap_round_coord (Binary.B2R prec emax x) (Binary.B2R prec emax s).
Proof.
  intros x s k Fx Fs HsR Hk Hkf Hovf Hint.
  unfold b64_snap_coord_scaled.
  set (n := round_mode mode_NE (Binary.B2R prec emax x * bpow radix2 k)).
  (* (1) multiply step is exact *)
  pose proof (b64_mult_pow2_exact x s k Fx Fs HsR Hk Hovf) as [Hmul Hmulfin].
  set (y := b64_mult x s) in *.
  (* (2) integer-rounding step yields the integer IZR n, and stays finite *)
  assert (HsnapZ : Binary.B2R prec emax (b64_snap_coord y) = IZR n).
  { rewrite (b64_snap_coord_B2R y). unfold snap_round_coord.
    rewrite Rmult_1_r, Rdiv_1_r, round_FIX0_IZR, Hmul. reflexivity. }
  assert (Hsnapfin : Binary.is_finite prec emax (b64_snap_coord y) = true).
  { unfold b64_snap_coord.
    rewrite (proj1 (proj2 (Binary.Bnearbyint_correct prec emax
              prec_lt_emax_b64 nearbyint_nan_b64 mode_NE y))).
    exact Hmulfin. }
  (* (3) divide step is exact via the core *)
  pose proof (b64_div_pow2_exact (b64_snap_coord y) s n k
                Hsnapfin Fs HsnapZ HsR Hint Hk Hkf) as [Hdiv _].
  rewrite Hdiv.
  (* RHS: snap_round_coord (B2R x) (2^k) = IZR n / 2^k = IZR n * 2^-k *)
  unfold snap_round_coord. rewrite HsR, round_FIX0_IZR.
  fold n. rewrite div_bpow_eq_mult_bpow_neg. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* R-side snap rounding on a general grid: idempotence + passes-through        *)
(* preservation.  Unlike the bridge above these need only `s <> 0` (no        *)
(* power-of-two restriction): `snap_round_coord r s = IZR n / s`, and          *)
(* re-snapping multiplies back by `s` exactly, rounds an integer to itself,    *)
(* and divides by `s` again -- a no-op.  This is the structural argument the   *)
(* `SnapRounding_b64.v` header anticipated, here generalised off `scale = 1`.  *)
(* -------------------------------------------------------------------------- *)

Lemma snap_round_coord_idem_scale :
  forall (r s : R), s <> 0 ->
    snap_round_coord (snap_round_coord r s) s = snap_round_coord r s.
Proof.
  intros r s Hs. unfold snap_round_coord.
  set (A := round radix2 (FIX_exp 0) (round_mode mode_NE) (r * s)).
  assert (Hinner : round radix2 (FIX_exp 0) (round_mode mode_NE) (A / s * s) = A).
  { replace (A / s * s) with A by (field; exact Hs).
    apply round_generic; auto with typeclass_instances.
    apply generic_format_round; auto with typeclass_instances. }
  rewrite Hinner. reflexivity.
Qed.

Lemma snap_round_idempotent_scale :
  forall (P : Point) (s : R), s <> 0 ->
    snap_round (snap_round P s) s = snap_round P s.
Proof.
  intros P s Hs. unfold snap_round. cbn [px py].
  f_equal; apply snap_round_coord_idem_scale; exact Hs.
Qed.

Theorem snap_round_preserves_passes_through_scale :
  forall (P0 P1 C : Point) (s : R), s <> 0 ->
    passes_through_hot_pixel P0 P1 C s ->
    passes_through_hot_pixel (snap_round P0 s) (snap_round P1 s) C s.
Proof.
  intros P0 P1 C s Hs Hpass.
  unfold passes_through_hot_pixel in *.
  destruct Hpass as [_Htouch Hsnap].
  split.
  - exact Hsnap.
  - rewrite !snap_round_idempotent_scale by exact Hs. exact Hsnap.
Qed.

(* -------------------------------------------------------------------------- *)
(* Exact hot-pixel radius for a power-of-two scale (HotPixel_b64 deferred       *)
(* item 4).  `b64_hot_pixel_radius scale = b64_div b64_one (b64_mult b64_two   *)
(* scale)`.  For `scale = 2^k` the `2 * scale` step is exact (multiply-by-     *)
(* pow2 core) giving `2^(k+1)`, and the reciprocal is exact (divide-by-pow2    *)
(* core) giving `2^-(k+1)` -- so the radius is bit-exactly `1/(2*scale)` with  *)
(* no rounding.  This is the load-bearing fact for generalising the hot-pixel  *)
(* boundaries (and hence `b64_in_hot_pixel`'s soundness) off the unit grid.    *)
(* -------------------------------------------------------------------------- *)

Lemma b64_hot_pixel_radius_pow2_exact :
  forall (scale : binary64) (k : Z),
    Binary.is_finite prec emax scale = true ->
    Binary.B2R prec emax scale = bpow radix2 k ->
    (0 <= k)%Z ->
    (k + 1 < emax)%Z ->
    Binary.B2R prec emax (b64_hot_pixel_radius scale)
      = bpow radix2 (- (k + 1))
    /\ Binary.is_finite prec emax (b64_hot_pixel_radius scale) = true.
Proof.
  intros scale k Fscale HscaleR Hk Hkmax.
  unfold b64_hot_pixel_radius.
  destruct B2R_and_finite_b64_one as [H1R H1fin].
  destruct B2R_and_finite_b64_two as [H2R H2fin].
  assert (Hbpow1 : bpow radix2 (k + 1) = 2 * bpow radix2 k).
  { rewrite bpow_plus, bpow_1. simpl. ring. }
  (* multiply step: B2R (b64_mult b64_two scale) = 2^(k+1), finite *)
  assert (Hovf2 : Rabs (Binary.B2R prec emax b64_two * bpow radix2 k)
                    < bpow radix2 emax).
  { rewrite H2R, <- Hbpow1.
    rewrite Rabs_pos_eq by (apply Rlt_le, bpow_gt_0).
    apply bpow_lt. exact Hkmax. }
  pose proof (b64_mult_pow2_exact b64_two scale k H2fin Fscale HscaleR Hk Hovf2)
    as [HmulR Hmulfin].
  assert (HmulBpow : Binary.B2R prec emax (b64_mult b64_two scale)
                       = bpow radix2 (k + 1)).
  { rewrite HmulR, H2R, Hbpow1. reflexivity. }
  (* divide step: B2R (b64_div b64_one (..)) = IZR 1 * 2^-(k+1) *)
  assert (H1R' : Binary.B2R prec emax b64_one = IZR 1)
    by (rewrite H1R; reflexivity).
  assert (Hbnd1 : (Z.abs 1 <= 2 ^ prec)%Z).
  { assert (0 < 2 ^ prec)%Z
      by (apply Z.pow_pos_nonneg; [lia | unfold prec; lia]).
    simpl Z.abs. lia. }
  pose proof (b64_div_pow2_exact b64_one (b64_mult b64_two scale) 1 (k + 1)
                H1fin Hmulfin H1R' HmulBpow Hbnd1
                ltac:(lia) ltac:(unfold prec, emax in *; lia)) as [HdivR HdivF].
  split.
  - rewrite HdivR.
    replace (IZR 1) with 1%R by reflexivity. rewrite Rmult_1_l. reflexivity.
  - exact HdivF.
Qed.

(* -------------------------------------------------------------------------- *)
(* Shared no-overflow bound: an integer coordinate (|n| <= 2^25) plus or minus *)
(* a unit-or-finer radius (2^-(k+1) <= 1) stays well inside the binary64 range *)
(* (|.| <= 2^25 + 1 << 2^emax).  Both boundary lemmas below discharge their    *)
(* `b64_safe` obligation through this one fact via the triangle inequality.    *)
(* (The format-closure side is `DivRoundPow2_b64.generic_format_F2R_le_pow_     *)
(* prec`, the single boundary-complete dyadic-format lemma.)                    *)
(* -------------------------------------------------------------------------- *)

Lemma int_radius_sum_lt_emax :
  forall (n k : Z),
    (Z.abs n <= 2 ^ 25)%Z ->
    (0 <= k)%Z ->
    Rabs (IZR n) + bpow radix2 (- (k + 1)) < bpow radix2 emax.
Proof.
  intros n k Hn Hk.
  assert (Hr : bpow radix2 (- (k + 1)) <= 1).
  { replace 1 with (bpow radix2 0) by reflexivity. apply bpow_le. lia. }
  assert (Hn' : Rabs (IZR n) <= bpow radix2 25).
  { rewrite <- abs_IZR, (bpow_radix2_eq_IZR_pow 25) by lia. apply IZR_le; exact Hn. }
  assert (Hgap : bpow radix2 25 + 1 < bpow radix2 emax).
  { apply (Rle_lt_trans _ (bpow radix2 26)).
    - replace (bpow radix2 26) with (2 * bpow radix2 25)
        by (replace 2 with (bpow radix2 1) by (simpl; lra);
            rewrite <- bpow_plus; reflexivity).
      assert (1 <= bpow radix2 25)
        by (replace 1 with (bpow radix2 0) by reflexivity; apply bpow_le; lia).
      lra.
    - apply bpow_lt. unfold emax. lia. }
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Boundary exactness at power-of-two scale (HotPixel_b64 deferred item 1).    *)
(* For an integer coordinate `cx = IZR n` (|n| <= 2^25) and a power-of-two     *)
(* grid `scale = 2^k` (k <= 26), the lower/upper hot-pixel boundaries          *)
(* `cx -/+ radius = IZR n -/+ 2^-(k+1)` are computed by `b64_minus`/`b64_plus` *)
(* with NO rounding -- the exact dyadic `n*2^(k+1) -/+ 1` over `2^(k+1)`       *)
(* representable.  This is the load-bearing fact for lifting                    *)
(* `b64_in_hot_pixel`'s soundness off the unit grid; it closes the deferred    *)
(* "generic_format on IZR n +/- bpow(-(k+1))" obligation.                       *)
(* -------------------------------------------------------------------------- *)

(* Common magnitude fact: |n*2^(k+1) -/+ 1| < 2^prec for |n| <= 2^25, k <= 26. *)
Lemma boundary_mantissa_small :
  forall (n k : Z),
    (Z.abs n <= 2 ^ 25)%Z ->
    (0 <= k <= 26)%Z ->
    (Z.abs (n * 2 ^ (k + 1) - 1) < 2 ^ prec)%Z
    /\ (Z.abs (n * 2 ^ (k + 1) + 1) < 2 ^ prec)%Z.
Proof.
  intros n k Hn Hk.
  assert (Hpos : (0 <= 2 ^ (k + 1))%Z) by (apply Z.pow_nonneg; lia).
  assert (Habs : (Z.abs (n * 2 ^ (k + 1)) <= 2 ^ 25 * 2 ^ (k + 1))%Z).
  { rewrite Z.abs_mul, (Z.abs_eq (2 ^ (k + 1))) by exact Hpos.
    apply Z.mul_le_mono_nonneg_r; [exact Hpos | exact Hn]. }
  assert (Hcollapse : (2 ^ 25 * 2 ^ (k + 1) = 2 ^ (26 + k))%Z).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hmono : (2 ^ (26 + k) <= 2 ^ 52)%Z) by (apply Z.pow_le_mono_r; lia).
  rewrite Hcollapse in Habs.
  assert (H53 : (2 ^ prec = 2 ^ 52 + 2 ^ 52)%Z).
  { unfold prec. replace 53%Z with (52 + 1)%Z by lia.
    rewrite Z.pow_add_r by lia. lia. }
  assert (H52pos : (2 <= 2 ^ 52)%Z).
  { apply (Z.le_trans _ (2 ^ 1)); [ lia | apply Z.pow_le_mono_r; lia ]. }
  split; lia.
Qed.

Lemma b64_minus_radius_int_exact :
  forall (x scale : binary64) (n k : Z),
    Binary.is_finite prec emax x = true ->
    Binary.B2R prec emax x = IZR n ->
    Binary.is_finite prec emax scale = true ->
    Binary.B2R prec emax scale = bpow radix2 k ->
    (Z.abs n <= 2 ^ 25)%Z ->
    (0 <= k <= 26)%Z ->
    Binary.B2R prec emax (b64_minus x (b64_hot_pixel_radius scale))
      = IZR n - bpow radix2 (- (k + 1))
    /\ Binary.is_finite prec emax (b64_minus x (b64_hot_pixel_radius scale)) = true.
Proof.
  intros x scale n k Fx HxR Fscale HscaleR Hn Hk.
  destruct (b64_hot_pixel_radius_pow2_exact scale k Fscale HscaleR
              ltac:(lia) ltac:(unfold emax; lia)) as [HrR HrF].
  set (r := b64_hot_pixel_radius scale) in *.
  destruct (boundary_mantissa_small n k Hn Hk) as [Hmlo _].
  assert (HpowKK : bpow radix2 (k + 1) * bpow radix2 (- (k + 1)) = 1).
  { rewrite <- bpow_plus. replace (k + 1 + - (k + 1))%Z with 0%Z by ring.
    reflexivity. }
  (* exact result = F2R (Float (n*2^(k+1) - 1) (-(k+1))) *)
  assert (Hr_F2R : IZR n - bpow radix2 (- (k + 1))
                   = F2R (Float radix2 (n * 2 ^ (k + 1) - 1) (- (k + 1)))).
  { unfold F2R, Fnum, Fexp.
    rewrite minus_IZR, mult_IZR, <- (bpow_radix2_eq_IZR_pow (k + 1)) by lia.
    replace (IZR 1) with 1%R by reflexivity.
    rewrite Rmult_minus_distr_r, Rmult_1_l, Rmult_assoc, HpowKK, Rmult_1_r.
    reflexivity. }
  assert (Hr_fmt : generic_format radix2 b64_fexp
                     (IZR n - bpow radix2 (- (k + 1)))).
  { rewrite Hr_F2R. apply generic_format_F2R_le_pow_prec;
      [lia | unfold emax, prec; lia]. }
  assert (Hbound_lt : Rabs (IZR n - bpow radix2 (- (k + 1))) < bpow radix2 emax).
  { unfold Rminus. eapply Rle_lt_trans; [ apply Rabs_triang | ].
    rewrite Rabs_Ropp, (Rabs_pos_eq (bpow radix2 (- (k + 1))))
      by (apply Rlt_le, bpow_gt_0).
    apply int_radius_sum_lt_emax; [ exact Hn | lia ]. }
  assert (Hsafe : b64_safe Rminus x r).
  { unfold b64_safe. split; [exact Fx | split; [exact HrF |]].
    rewrite HxR, HrR, (b64_round_generic _ Hr_fmt). exact Hbound_lt. }
  pose proof (b64_minus_correct _ _ Hsafe) as [HmR HmF].
  rewrite HxR, HrR, (b64_round_generic _ Hr_fmt) in HmR.
  split; [exact HmR | exact HmF].
Qed.

Lemma b64_plus_radius_int_exact :
  forall (x scale : binary64) (n k : Z),
    Binary.is_finite prec emax x = true ->
    Binary.B2R prec emax x = IZR n ->
    Binary.is_finite prec emax scale = true ->
    Binary.B2R prec emax scale = bpow radix2 k ->
    (Z.abs n <= 2 ^ 25)%Z ->
    (0 <= k <= 26)%Z ->
    Binary.B2R prec emax (b64_plus x (b64_hot_pixel_radius scale))
      = IZR n + bpow radix2 (- (k + 1))
    /\ Binary.is_finite prec emax (b64_plus x (b64_hot_pixel_radius scale)) = true.
Proof.
  intros x scale n k Fx HxR Fscale HscaleR Hn Hk.
  destruct (b64_hot_pixel_radius_pow2_exact scale k Fscale HscaleR
              ltac:(lia) ltac:(unfold emax; lia)) as [HrR HrF].
  set (r := b64_hot_pixel_radius scale) in *.
  destruct (boundary_mantissa_small n k Hn Hk) as [_ Hmhi].
  assert (HpowKK : bpow radix2 (k + 1) * bpow radix2 (- (k + 1)) = 1).
  { rewrite <- bpow_plus. replace (k + 1 + - (k + 1))%Z with 0%Z by ring.
    reflexivity. }
  assert (Hr_F2R : IZR n + bpow radix2 (- (k + 1))
                   = F2R (Float radix2 (n * 2 ^ (k + 1) + 1) (- (k + 1)))).
  { unfold F2R, Fnum, Fexp.
    rewrite plus_IZR, mult_IZR, <- (bpow_radix2_eq_IZR_pow (k + 1)) by lia.
    replace (IZR 1) with 1%R by reflexivity.
    rewrite Rmult_plus_distr_r, Rmult_1_l, Rmult_assoc, HpowKK, Rmult_1_r.
    reflexivity. }
  assert (Hr_fmt : generic_format radix2 b64_fexp
                     (IZR n + bpow radix2 (- (k + 1)))).
  { rewrite Hr_F2R. apply generic_format_F2R_le_pow_prec;
      [lia | unfold emax, prec; lia]. }
  assert (Hbound_lt : Rabs (IZR n + bpow radix2 (- (k + 1))) < bpow radix2 emax).
  { eapply Rle_lt_trans; [ apply Rabs_triang | ].
    rewrite (Rabs_pos_eq (bpow radix2 (- (k + 1)))) by (apply Rlt_le, bpow_gt_0).
    apply int_radius_sum_lt_emax; [ exact Hn | lia ]. }
  assert (Hsafe : b64_safe Rplus x r).
  { unfold b64_safe. split; [exact Fx | split; [exact HrF |]].
    rewrite HxR, HrR, (b64_round_generic _ Hr_fmt). exact Hbound_lt. }
  pose proof (b64_plus_correct _ _ Hsafe) as [HmR HmF].
  rewrite HxR, HrR, (b64_round_generic _ Hr_fmt) in HmR.
  split; [exact HmR | exact HmF].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_snap_coord_scaled_B2R.
Print Assumptions snap_round_preserves_passes_through_scale.
Print Assumptions b64_hot_pixel_radius_pow2_exact.
Print Assumptions b64_minus_radius_int_exact.
Print Assumptions b64_plus_radius_int_exact.
