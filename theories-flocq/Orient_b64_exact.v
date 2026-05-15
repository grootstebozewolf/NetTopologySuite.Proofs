(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_exact
   ----------------------------------------------------------------------------
   Cross-product soundness of `b64_orient_sign_filtered` in the integer-
   coordinate exact regime.

   This is Path 2 from `docs/soundness-strategy.md`.  Restricted regime
   (integer-valued coordinates with `|coord| <= 2^25`), in exchange for an
   end-to-end headline proved Qed-closed today rather than after three
   sessions of forward-error scaffolding.

   The argument.  When every input coordinate is an integer in
   `[-2^25, 2^25]`, every operation in `b64_orient2d` is bit-exact:

     - difference of two coords:   integer in [-2^26, 2^26]   <= 2^53 = exact
     - product of two differences: integer in [-2^52, 2^52]   <= 2^53 = exact
     - outer difference of products: integer in [-2^53, 2^53] <= 2^53 = exact

   Every intermediate value stays within binary64's integer-exactness
   window (`|n| <= 2^53` <=> `IZR n` is in the FLT format), so the
   rounding mode never has anything to round.  The rounded value equals
   the exact mathematical value `cross_R_BP P0 P1 Q` *on the nose*, and
   composing with `b64_orient_sign_filtered_consistent_with_b64` from
   `Orient_b64_sound.v` gives the cross_R headline:

     forall P0 P1 Q,
       orient2d_inputs_int_safe P0 P1 Q ->
       match b64_orient_sign_filtered P0 P1 Q with
       | OrientRPos       => 0 < cross_R_BP P0 P1 Q
       | OrientRNeg       => cross_R_BP P0 P1 Q < 0
       | OrientRZero      => cross_R_BP P0 P1 Q = 0
       | OrientRNan       => True
       | OrientRUncertain => True
       end.

   PROOF STATUS
   ============
   - `generic_format_IZR_le_bpow_prec`  -- integers with `|n| <= 2^prec`
                                           are in the binary64 FLT format
                                           (handles boundary `|n| = 2^prec`
                                           via `generic_format_bpow_b64`).
   - `b64_round_IZR_exact`              -- the rounding function fixes
                                           every such integer.
   - `b64_minus_int_exact`              -- under integer-valued operands
                                           and a bound on the result's
                                           magnitude, `b64_minus` is
                                           bit-exact integer subtraction.
   - `b64_mult_int_exact`               -- analogous for `b64_mult`.
   - `coord_int_safe` predicate         -- input regime.
   - `coord_int_safe_imp_coord_safe`    -- bridges to the magnitude regime
                                           (every int-safe coord is coord-
                                           safe, so we inherit the existing
                                           `b64_orient2d_inputs_safe_imp_safe`
                                           chain to discharge no-overflow).
   - `b64_orient2d_exact_for_small_int` -- `B2R det = cross_R_BP` on the
                                           nose.
   - `b64_orient_sign_filtered_sound_small_int` -- the cross_R-valued
                                           headline.

   No `Admitted`, no `Axiom`, no `Parameter`.

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
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import Orient_b64_R.
From NTS.Proofs.Flocq Require Import Orient_b64_sound.

Local Open Scope R_scope.

Local Notation b64_fexp := (SpecFloat.fexp prec emax).
Local Notation b64_round := (round radix2 b64_fexp (round_mode mode_b64)).

(* -------------------------------------------------------------------------- *)
(* Bridge between Z's `Z.pow 2 e` and Flocq's `bpow radix2 e` on the R side. *)
(* -------------------------------------------------------------------------- *)

Lemma bpow_radix2_eq_IZR_pow :
  forall e : Z, (0 <= e)%Z -> bpow radix2 e = IZR (2 ^ e).
Proof.
  intros e He.
  rewrite IZR_Zpower by exact He.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Integer-format theorem.                                                    *)
(*                                                                            *)
(* Every integer `n` with `Z.abs n <= 2^prec` is in the binary64 FLT format. *)
(* Split into the boundary case `|n| = 2^prec` (handled via                  *)
(* `generic_format_bpow_b64`) and the strict case `|n| < 2^prec` (handled    *)
(* via `generic_format_F2R` with the float `Float radix2 n 0`).               *)
(* -------------------------------------------------------------------------- *)

Lemma generic_format_IZR_le_bpow_prec :
  forall n : Z,
    (Z.abs n <= 2 ^ prec)%Z ->
    generic_format radix2 b64_fexp (IZR n).
Proof.
  intros n Hbound.
  destruct (Z.eq_dec n 0) as [-> | Hn0].
  { simpl. apply generic_format_0. }
  destruct (Z.eq_dec (Z.abs n) (2 ^ prec)) as [Hboundary | Hstrict].
  - (* |n| = 2^prec: n = +/- 2^prec *)
    destruct (Z_lt_le_dec n 0) as [Hneg | Hpos].
    + (* n < 0, so n = -2^prec *)
      assert (Hn_eq : n = - (2 ^ prec))%Z by lia.
      rewrite Hn_eq, opp_IZR.
      apply generic_format_opp.
      rewrite <- bpow_radix2_eq_IZR_pow by (unfold prec; lia).
      apply generic_format_bpow_b64. unfold emax. lia.
    + (* n > 0, so n = 2^prec *)
      assert (Hn_eq : n = 2 ^ prec)%Z by lia.
      rewrite Hn_eq.
      rewrite <- bpow_radix2_eq_IZR_pow by (unfold prec; lia).
      apply generic_format_bpow_b64. unfold emax. lia.
  - (* |n| < 2^prec *)
    assert (Hstrict' : (Z.abs n < 2 ^ prec)%Z) by lia.
    replace (IZR n) with (F2R (Float radix2 n 0)).
    2: { unfold F2R; simpl. rewrite Rmult_1_r. reflexivity. }
    apply generic_format_F2R.
    intros _.
    unfold F2R; simpl. rewrite Rmult_1_r.
    unfold cexp.
    assert (Hmag : (mag radix2 (IZR n) <= prec)%Z).
    { apply mag_le_bpow.
      - intros H. apply Hn0. apply eq_IZR_R0. exact H.
      - rewrite <- abs_IZR.
        rewrite bpow_radix2_eq_IZR_pow by (unfold prec; lia).
        apply IZR_lt. exact Hstrict'. }
    unfold SpecFloat.fexp. apply Z.max_lub.
    + lia.
    + unfold prec, emax. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Rounding fixes integers in the exact-representable window.                 *)
(* -------------------------------------------------------------------------- *)

Lemma b64_round_IZR_exact :
  forall n : Z,
    (Z.abs n <= 2 ^ prec)%Z ->
    b64_round (IZR n) = IZR n.
Proof.
  intros n Hn.
  apply round_generic.
  - apply valid_rnd_N.
  - apply generic_format_IZR_le_bpow_prec. exact Hn.
Qed.

(* -------------------------------------------------------------------------- *)
(* No-overflow check is automatic for integer-valued results within `2^prec`. *)
(* -------------------------------------------------------------------------- *)

Lemma b64_round_IZR_abs_lt_bpow_emax :
  forall n : Z,
    (Z.abs n <= 2 ^ prec)%Z ->
    Rabs (b64_round (IZR n)) < bpow radix2 emax.
Proof.
  intros n Hn.
  rewrite b64_round_IZR_exact by exact Hn.
  rewrite <- abs_IZR.
  apply (Rle_lt_trans _ (bpow radix2 prec)).
  - rewrite bpow_radix2_eq_IZR_pow by (unfold prec; lia).
    apply IZR_le. exact Hn.
  - apply bpow_lt. unfold prec, emax. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Per-op exactness on integer-valued operands.                              *)
(*                                                                            *)
(* The R-side helper `minus_IZR` / `mult_IZR` rewrites `IZR a - IZR b` (resp. *)
(* `IZR a * IZR b`) into `IZR (a - b)` (resp. `IZR (a * b)`), turning the    *)
(* rounded operation into rounding an integer.  Combined with                 *)
(* `b64_round_IZR_exact` and the per-op correctness theorems in B64_bridge,   *)
(* `b64_minus` and `b64_mult` are bit-exact integer arithmetic.              *)
(* -------------------------------------------------------------------------- *)

Lemma b64_minus_int_exact :
  forall x y : binary64,
  forall a b : Z,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax x = IZR a ->
    Binary.B2R prec emax y = IZR b ->
    (Z.abs (a - b) <= 2 ^ prec)%Z ->
    Binary.B2R prec emax (b64_minus x y) = IZR (a - b)
    /\ Binary.is_finite prec emax (b64_minus x y) = true.
Proof.
  intros x y a b Fx Fy HxR HyR Hbnd.
  assert (Hsafe : b64_safe Rminus x y).
  { unfold b64_safe.
    split; [exact Fx | split; [exact Fy | ]].
    rewrite HxR, HyR, <- minus_IZR.
    apply b64_round_IZR_abs_lt_bpow_emax. exact Hbnd. }
  pose proof (b64_minus_correct _ _ Hsafe) as [HB2R Hfin].
  split; [|exact Hfin].
  rewrite HB2R, HxR, HyR, <- minus_IZR.
  apply b64_round_IZR_exact. exact Hbnd.
Qed.

Lemma b64_mult_int_exact :
  forall x y : binary64,
  forall a b : Z,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax x = IZR a ->
    Binary.B2R prec emax y = IZR b ->
    (Z.abs (a * b) <= 2 ^ prec)%Z ->
    Binary.B2R prec emax (b64_mult x y) = IZR (a * b)
    /\ Binary.is_finite prec emax (b64_mult x y) = true.
Proof.
  intros x y a b Fx Fy HxR HyR Hbnd.
  assert (Hsafe : b64_safe Rmult x y).
  { unfold b64_safe.
    split; [exact Fx | split; [exact Fy | ]].
    rewrite HxR, HyR, <- mult_IZR.
    apply b64_round_IZR_abs_lt_bpow_emax. exact Hbnd. }
  pose proof (b64_mult_correct _ _ Hsafe) as [HB2R Hfin].
  split; [|exact Hfin].
  rewrite HB2R, HxR, HyR, <- mult_IZR.
  apply b64_round_IZR_exact. exact Hbnd.
Qed.

(* The plus counterpart: needed for translation invariance below.            *)
(* Translation by a vector V adds two integer-valued binary64s, which is     *)
(* bit-exact when their sum stays within binary64's 53-bit integer window.   *)
Lemma b64_plus_int_exact :
  forall x y : binary64,
  forall a b : Z,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax x = IZR a ->
    Binary.B2R prec emax y = IZR b ->
    (Z.abs (a + b) <= 2 ^ prec)%Z ->
    Binary.B2R prec emax (b64_plus x y) = IZR (a + b)
    /\ Binary.is_finite prec emax (b64_plus x y) = true.
Proof.
  intros x y a b Fx Fy HxR HyR Hbnd.
  assert (Hsafe : b64_safe Rplus x y).
  { unfold b64_safe.
    split; [exact Fx | split; [exact Fy | ]].
    rewrite HxR, HyR, <- plus_IZR.
    apply b64_round_IZR_abs_lt_bpow_emax. exact Hbnd. }
  pose proof (b64_plus_correct _ _ Hsafe) as [HB2R Hfin].
  split; [|exact Hfin].
  rewrite HB2R, HxR, HyR, <- plus_IZR.
  apply b64_round_IZR_exact. exact Hbnd.
Qed.

(* Specialisation for the translation-invariance proof.  If both operands   *)
(* are `coord_int_safe`, their sum is integer-valued with magnitude         *)
(* `<= 2^26 < 2^prec`, hence bit-exact under `b64_plus`.  Returns the        *)
(* R-side identity directly (drops the integer-witness existential).        *)
Lemma b64_plus_B2R_of_coord_int_safe :
  forall x y : binary64,
    coord_int_safe x ->
    coord_int_safe y ->
    Binary.B2R prec emax (b64_plus x y)
      = Binary.B2R prec emax x + Binary.B2R prec emax y.
Proof.
  intros x y (Fx & a & HxR & Hxb) (Fy & b & HyR & Hyb).
  assert (Hbnd : (Z.abs (a + b) <= 2 ^ prec)%Z).
  { apply (Z.le_trans _ (2 ^ 26)).
    - replace (2 ^ 26)%Z with (2 ^ 25 + 2 ^ 25)%Z by lia. lia.
    - unfold prec. lia. }
  pose proof (b64_plus_int_exact x y a b Fx Fy HxR HyR Hbnd) as [HB2R _].
  rewrite HB2R, HxR, HyR. apply plus_IZR.
Qed.

(* -------------------------------------------------------------------------- *)
(* Input regime predicate.                                                    *)
(*                                                                            *)
(* `coord_int_safe x` := x is finite, integer-valued, and `|x| <= 2^25`.     *)
(* The 25-bit bound is what propagates through the orient2d chain to keep    *)
(* every intermediate value within the 53-bit integer-exactness window.       *)
(* -------------------------------------------------------------------------- *)

Definition coord_int_safe (x : binary64) : Prop :=
  Binary.is_finite prec emax x = true /\
  exists n : Z, Binary.B2R prec emax x = IZR n /\ (Z.abs n <= 2 ^ 25)%Z.

Definition orient2d_inputs_int_safe (P0 P1 Q : BPoint) : Prop :=
  coord_int_safe (bx P0)  /\
  coord_int_safe (by_ P0) /\
  coord_int_safe (bx P1)  /\
  coord_int_safe (by_ P1) /\
  coord_int_safe (bx Q)   /\
  coord_int_safe (by_ Q).

(* -------------------------------------------------------------------------- *)
(* Bridge to the magnitude regime: int-safe coords are coord-safe (Flavour B).*)
(* This lets us inherit `b64_orient2d_inputs_safe_imp_safe` for the seven    *)
(* no-overflow `b64_safe` premises of `b64_orient2d_safe`, which            *)
(* `b64_orient_sign_filtered_consistent_with_b64` requires.                   *)
(* -------------------------------------------------------------------------- *)

Lemma coord_int_safe_imp_coord_safe :
  forall x : binary64, coord_int_safe x -> b64_coord_safe x.
Proof.
  intros x (Fx & n & HxR & Hxb).
  unfold b64_coord_safe.
  split; [exact Fx |].
  unfold b64_safe_coord_bound.
  rewrite HxR, <- abs_IZR.
  apply (Rle_trans _ (IZR (2 ^ 25))).
  - apply IZR_le. exact Hxb.
  - rewrite <- bpow_radix2_eq_IZR_pow by lia.
    apply bpow_le. lia.
Qed.

Lemma orient2d_inputs_int_safe_imp_inputs_safe :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_inputs_safe P0 P1 Q.
Proof.
  intros P0 P1 Q (HxP0 & HyP0 & HxP1 & HyP1 & HxQ & HyQ).
  unfold b64_orient2d_inputs_safe.
  repeat split; apply coord_int_safe_imp_coord_safe; assumption.
Qed.

Lemma orient2d_inputs_int_safe_imp_safe :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_safe P0 P1 Q.
Proof.
  intros P0 P1 Q Hint.
  apply b64_orient2d_inputs_safe_imp_safe.
  apply orient2d_inputs_int_safe_imp_inputs_safe. exact Hint.
Qed.

(* -------------------------------------------------------------------------- *)
(* Chain of magnitude bounds for intermediate Z values.                       *)
(* -------------------------------------------------------------------------- *)

Lemma diff_bound_2p26 :
  forall a b : Z, (Z.abs a <= 2 ^ 25)%Z -> (Z.abs b <= 2 ^ 25)%Z ->
    (Z.abs (a - b) <= 2 ^ 26)%Z.
Proof.
  intros a b Ha Hb.
  replace (2 ^ 26)%Z with (2 ^ 25 + 2 ^ 25)%Z by lia. lia.
Qed.

Lemma prod_bound_2p52 :
  forall a b : Z, (Z.abs a <= 2 ^ 26)%Z -> (Z.abs b <= 2 ^ 26)%Z ->
    (Z.abs (a * b) <= 2 ^ 52)%Z.
Proof.
  intros a b Ha Hb.
  rewrite Z.abs_mul.
  replace (2 ^ 52)%Z with (2 ^ 26 * 2 ^ 26)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma outer_bound_2p53 :
  forall p q : Z, (Z.abs p <= 2 ^ 52)%Z -> (Z.abs q <= 2 ^ 52)%Z ->
    (Z.abs (p - q) <= 2 ^ 53)%Z.
Proof.
  intros p q Hp Hq.
  replace (2 ^ 53)%Z with (2 ^ 52 + 2 ^ 52)%Z by lia. lia.
Qed.

Lemma le_2p52_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 52)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. unfold prec. lia. Qed.

Lemma le_2p53_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 53)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. unfold prec. lia. Qed.

Lemma le_2p26_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 26)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. unfold prec. lia. Qed.

(* -------------------------------------------------------------------------- *)
(* Orient2d exactness.                                                        *)
(*                                                                            *)
(* The headline of Path 2: `B2R (b64_orient2d P0 P1 Q) = cross_R_BP P0 P1 Q`  *)
(* on the nose, in the integer regime.  Proof: unfold the chain, apply       *)
(* `b64_minus_int_exact` / `b64_mult_int_exact` four/two/one times to push   *)
(* the integer mantissas through, and finally rewrite the resulting          *)
(* `IZR (...)` expression to match `cross_R_BP`.                              *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_exact_for_small_int :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    Binary.B2R prec emax (b64_orient2d P0 P1 Q) = cross_R_BP P0 P1 Q.
Proof.
  intros P0 P1 Q Hint.
  destruct Hint as (HxP0 & HyP0 & HxP1 & HyP1 & HxQ & HyQ).
  destruct HxP0 as (FxP0 & mxP0 & HxP0R & HxP0b).
  destruct HyP0 as (FyP0 & myP0 & HyP0R & HyP0b).
  destruct HxP1 as (FxP1 & mxP1 & HxP1R & HxP1b).
  destruct HyP1 as (FyP1 & myP1 & HyP1R & HyP1b).
  destruct HxQ  as (FxQ  & mxQ  & HxQR  & HxQb).
  destruct HyQ  as (FyQ  & myQ  & HyQR  & HyQb).
  (* Differences: each is an integer with |.| <= 2^26. *)
  pose proof (diff_bound_2p26 _ _ HxP1b HxP0b) as Bdx1.
  pose proof (diff_bound_2p26 _ _ HyQb  HyP0b) as Bdy1.
  pose proof (diff_bound_2p26 _ _ HxQb  HxP0b) as Bdx2.
  pose proof (diff_bound_2p26 _ _ HyP1b HyP0b) as Bdy2.
  destruct (b64_minus_int_exact _ _ _ _ FxP1 FxP0 HxP1R HxP0R
              (le_2p26_le_2pprec _ Bdx1)) as [Hdx1_R Fdx1].
  destruct (b64_minus_int_exact _ _ _ _ FyQ  FyP0 HyQR  HyP0R
              (le_2p26_le_2pprec _ Bdy1)) as [Hdy1_R Fdy1].
  destruct (b64_minus_int_exact _ _ _ _ FxQ  FxP0 HxQR  HxP0R
              (le_2p26_le_2pprec _ Bdx2)) as [Hdx2_R Fdx2].
  destruct (b64_minus_int_exact _ _ _ _ FyP1 FyP0 HyP1R HyP0R
              (le_2p26_le_2pprec _ Bdy2)) as [Hdy2_R Fdy2].
  (* Products: each is an integer with |.| <= 2^52. *)
  pose proof (prod_bound_2p52 _ _ Bdx1 Bdy1) as Bt1.
  pose proof (prod_bound_2p52 _ _ Bdx2 Bdy2) as Bt2.
  destruct (b64_mult_int_exact _ _ _ _ Fdx1 Fdy1 Hdx1_R Hdy1_R
              (le_2p52_le_2pprec _ Bt1)) as [Ht1_R Ft1].
  destruct (b64_mult_int_exact _ _ _ _ Fdx2 Fdy2 Hdx2_R Hdy2_R
              (le_2p52_le_2pprec _ Bt2)) as [Ht2_R Ft2].
  (* Outer subtraction: integer with |.| <= 2^53. *)
  pose proof (outer_bound_2p53 _ _ Bt1 Bt2) as Bout.
  destruct (b64_minus_int_exact _ _ _ _ Ft1 Ft2 Ht1_R Ht2_R
              (le_2p53_le_2pprec _ Bout)) as [Hout_R _].
  (* Now Hout_R says: B2R (b64_orient2d ...) = IZR (the integer det).       *)
  (* Expand b64_orient2d and equate with cross_R_BP, which is the same      *)
  (* integer expression lifted via IZR.                                     *)
  unfold b64_orient2d, Orientation_b64.b64_orient2d_terms.
  cbn iota.
  rewrite Hout_R.
  unfold cross_R_BP.
  rewrite HxP0R, HyP0R, HxP1R, HyP1R, HxQR, HyQR.
  rewrite <- !minus_IZR.
  rewrite <- !mult_IZR.
  rewrite <- minus_IZR.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cross_R-valued soundness of the Stage A filter in the integer regime.      *)
(*                                                                            *)
(* Compose exactness with decoder consistency: in the integer regime,         *)
(* `B2R det = cross_R_BP`, so the decoder's sign judgement against `B2R det` *)
(* is the same as its judgement against `cross_R_BP`.                         *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient_sign_filtered_sound_small_int :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    match b64_orient_sign_filtered P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hint.
  pose proof (orient2d_inputs_int_safe_imp_safe _ _ _ Hint) as Hsafe.
  pose proof (b64_orient2d_exact_for_small_int _ _ _ Hint) as Hexact.
  pose proof (b64_orient_sign_filtered_consistent_with_b64 _ _ _ Hsafe) as Hcons.
  destruct (b64_orient_sign_filtered P0 P1 Q); rewrite Hexact in Hcons; exact Hcons.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cyclic permutation in the integer regime.                                  *)
(*                                                                            *)
(* `cross_R_BP P0 P1 Q = cross_R_BP P1 Q P0 = cross_R_BP Q P0 P1` is a        *)
(* polynomial identity over `R` (the signed twice-area of a triangle is       *)
(* invariant under cyclic permutation of its vertices) -- `ring` closes it    *)
(* in one tactic.  Lifting via `b64_orient2d_exact_for_small_int` (each       *)
(* binary64 orient2d call equals its R-cross product on the nose in the       *)
(* integer regime) propagates the identity to the binary64 evaluations.       *)
(*                                                                            *)
(* The deferred-cyclic discussion in `Orient_b64_R.v` notes that this is      *)
(* not Provable in general -- the intermediate `b64_minus` / `b64_mult`       *)
(* values differ syntactically between the two calls, and rounding errors    *)
(* don't structurally cancel.  Inside the integer regime, the rounding        *)
(* errors are zero, so the obstruction disappears.                            *)
(* -------------------------------------------------------------------------- *)

Lemma orient2d_inputs_int_safe_cycl :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    orient2d_inputs_int_safe P1 Q P0.
Proof.
  intros P0 P1 Q (HxP0 & HyP0 & HxP1 & HyP1 & HxQ & HyQ).
  repeat split; assumption.
Qed.

Lemma orient2d_inputs_int_safe_cycl2 :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    orient2d_inputs_int_safe Q P0 P1.
Proof.
  intros P0 P1 Q (HxP0 & HyP0 & HxP1 & HyP1 & HxQ & HyQ).
  repeat split; assumption.
Qed.

Theorem b64_orient2d_cyclic_int_R :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    Binary.B2R prec emax (b64_orient2d P0 P1 Q)
      = Binary.B2R prec emax (b64_orient2d P1 Q P0).
Proof.
  intros P0 P1 Q Hint.
  pose proof (b64_orient2d_exact_for_small_int _ _ _ Hint) as H1.
  pose proof (orient2d_inputs_int_safe_cycl _ _ _ Hint) as Hint'.
  pose proof (b64_orient2d_exact_for_small_int _ _ _ Hint') as H2.
  rewrite H1, H2.
  unfold cross_R_BP.
  ring.
Qed.

Theorem b64_orient2d_cyclic2_int_R :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    Binary.B2R prec emax (b64_orient2d P0 P1 Q)
      = Binary.B2R prec emax (b64_orient2d Q P0 P1).
Proof.
  intros P0 P1 Q Hint.
  pose proof (b64_orient2d_exact_for_small_int _ _ _ Hint) as H1.
  pose proof (orient2d_inputs_int_safe_cycl2 _ _ _ Hint) as Hint'.
  pose proof (b64_orient2d_exact_for_small_int _ _ _ Hint') as H2.
  rewrite H1, H2.
  unfold cross_R_BP.
  ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Translation invariance in the integer regime.                              *)
(*                                                                            *)
(* The cross product is translation-invariant in R-arithmetic: shifting all   *)
(* three vertices by the same vector V leaves the signed twice-area           *)
(* unchanged.  This was deferred in `Orient_b64_R.v` for the general          *)
(* binary64 regime because rounding errors in the four `b64_plus` operands    *)
(* don't structurally cancel against the four `b64_minus` operands at the     *)
(* start of `b64_orient2d`.  Inside the integer regime, `b64_plus` is         *)
(* bit-exact (each translated coord stays within the 53-bit integer-          *)
(* exactness window), so the binary64 evaluation matches the R-side           *)
(* identity on the nose.                                                       *)
(*                                                                            *)
(* Precondition shape: caller supplies (a) `orient2d_inputs_int_safe` on the  *)
(* original triple, (b) `coord_int_safe` on each component of the translation *)
(* vector V, AND (c) `orient2d_inputs_int_safe` on the translated triple.     *)
(* Condition (c) is a genuine constraint -- it forces V to be small enough    *)
(* (relative to the originals) that every post-translation coord lands at or  *)
(* under `2^25`.  In practice this is the natural use case: translating to a  *)
(* nearby origin for grid normalisation, where both endpoints of the          *)
(* translation are well inside the integer regime by construction.            *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_translation_int_R :
  forall (P0 P1 Q : BPoint) (vx vy : binary64),
    let P0' := mkBP (b64_plus (bx P0) vx) (b64_plus (by_ P0) vy) in
    let P1' := mkBP (b64_plus (bx P1) vx) (b64_plus (by_ P1) vy) in
    let Q'  := mkBP (b64_plus (bx Q)  vx) (b64_plus (by_ Q)  vy) in
    orient2d_inputs_int_safe P0 P1 Q ->
    coord_int_safe vx ->
    coord_int_safe vy ->
    orient2d_inputs_int_safe P0' P1' Q' ->
    Binary.B2R prec emax (b64_orient2d P0 P1 Q)
      = Binary.B2R prec emax (b64_orient2d P0' P1' Q').
Proof.
  intros P0 P1 Q vx vy P0' P1' Q' Hpre Hvx Hvy Hpost.
  rewrite (b64_orient2d_exact_for_small_int _ _ _ Hpre).
  rewrite (b64_orient2d_exact_for_small_int _ _ _ Hpost).
  unfold cross_R_BP. simpl.
  destruct Hpre as (HxP0 & HyP0 & HxP1 & HyP1 & HxQ & HyQ).
  rewrite (b64_plus_B2R_of_coord_int_safe _ _ HxP0 Hvx).
  rewrite (b64_plus_B2R_of_coord_int_safe _ _ HyP0 Hvy).
  rewrite (b64_plus_B2R_of_coord_int_safe _ _ HxP1 Hvx).
  rewrite (b64_plus_B2R_of_coord_int_safe _ _ HyP1 Hvy).
  rewrite (b64_plus_B2R_of_coord_int_safe _ _ HxQ  Hvx).
  rewrite (b64_plus_B2R_of_coord_int_safe _ _ HyQ  Hvy).
  ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions generic_format_IZR_le_bpow_prec.
Print Assumptions b64_round_IZR_exact.
Print Assumptions b64_minus_int_exact.
Print Assumptions b64_mult_int_exact.
Print Assumptions b64_plus_int_exact.
Print Assumptions b64_plus_B2R_of_coord_int_safe.
Print Assumptions coord_int_safe_imp_coord_safe.
Print Assumptions orient2d_inputs_int_safe_imp_safe.
Print Assumptions b64_orient2d_exact_for_small_int.
Print Assumptions b64_orient_sign_filtered_sound_small_int.
Print Assumptions b64_orient2d_cyclic_int_R.
Print Assumptions b64_orient2d_cyclic2_int_R.
Print Assumptions b64_orient2d_translation_int_R.
