(* ============================================================================
   PassesThrough_b64_grid_exact.v
   ----------------------------------------------------------------------------
   Issue #66, the snap-rounding / passes-through RGR pivot (see
   docs/snap-rounding-rgr-pivot.md and docs/oracle-soundness-finding.md).

   GOAL (C1, "grid exactness").  On the integer / unit grid the ROUNDED compute
   filter agrees bit-for-bit with the EXACT R-spec:

       b64_on_grid P0 -> b64_on_grid P1 ->
         b64_passes_through_hot_pixel_compute P0 P1 C
           = b64_passes_through_hot_pixel P0 P1 C.

   This is the constructive payoff of the pivot: the compute filter is
   machine-checked UNSOUND off the grid (PassesThrough_b64_compute_unsound.v),
   but a snap-rounding noder only ever evaluates it on snapped (grid-aligned)
   coordinates -- and there it coincides with the exact spec, which is sound
   (HotPixel_b64.b64_passes_through_sound).  Strongly evidenced: 0 divergence in
   5,000,000 on-grid cases (docs/oracle-soundness-finding.md).

   THIS FILE lands the REDUCTION layer, Qed-closed: on the grid the
   snap-consistency second conjunct of `passes_through` is vacuous (a grid point
   is a fixed point of `b64_snap`), so the full predicate collapses to a single
   Liang-Barsky touch -- for BOTH the rounded compute filter and the exact spec.
   C1 therefore reduces to the single-touch equivalence
       b64_liang_barsky_touches_compute = b64_liang_barsky_touches  (on grid),
   which isolates the remaining obligation to ONE touch: that the
   round-to-nearest errors in the divide-and-clip t-bounds never flip the
   composite `max(..) <= min(..)` comparison on the grid.  That core is the
   genuinely hard, multi-session step (see the OBLIGATION note at the bottom);
   it is NOT discharged here and NO `Admitted` is introduced -- the file is
   Qed-clean and the open core is stated as a comment, not an axiom.

   Corpus invariant preserved: no Admitted / Axiom / Parameter.
   ============================================================================ *)

From Stdlib Require Import Bool.
From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import B64_lib.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import SnapRounding_b64.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.

(* "On the grid" = a fixed point of the unit-grid snap.  This is exactly the
   regime a snap-rounding noder runs in: by `b64_snap_on_grid` below, every
   snapped coordinate satisfies it. *)
Definition b64_on_grid (P : BPoint) : Prop := b64_snap P = P.

(* Post-snap points are grid-aligned (finite coordinates).  So the grid
   hypotheses of the lemmas below are discharged for any noder input after the
   snap step -- the regime in which the filter is actually consulted. *)
Lemma b64_snap_on_grid :
  forall P : BPoint,
    Binary.is_finite prec emax (bx P)  = true ->
    Binary.is_finite prec emax (by_ P) = true ->
    b64_on_grid (b64_snap P).
Proof.
  intros P Hx Hy. unfold b64_on_grid.
  apply b64_snap_idempotent_finite; assumption.
Qed.

(* On the grid the EXACT-spec passes-through predicate collapses to a single
   Liang-Barsky touch: the snapped endpoints equal the originals, so its
   snap-consistency conjunct repeats the first. *)
Lemma b64_passes_through_collapses_on_grid :
  forall P0 P1 C : BPoint,
    b64_on_grid P0 -> b64_on_grid P1 ->
    b64_passes_through_hot_pixel P0 P1 C = b64_liang_barsky_touches P0 P1 C.
Proof.
  intros P0 P1 C H0 H1.
  unfold b64_passes_through_hot_pixel, b64_on_grid in *.
  rewrite H0, H1. apply Bool.andb_diag.
Qed.

(* Same collapse for the ROUNDED compute filter, using the computational
   `b64_snap` (the very same operator). *)
Lemma b64_passes_through_compute_collapses_on_grid :
  forall P0 P1 C : BPoint,
    b64_on_grid P0 -> b64_on_grid P1 ->
    b64_passes_through_hot_pixel_compute P0 P1 C
      = b64_liang_barsky_touches_compute P0 P1 C.
Proof.
  intros P0 P1 C H0 H1.
  unfold b64_passes_through_hot_pixel_compute, b64_on_grid in *.
  rewrite H0, H1. apply Bool.andb_diag.
Qed.

(* REDUCTION (Qed).  On the grid, full-predicate grid-exactness (C1) is
   EQUIVALENT to the single-touch grid-exactness.  Both snap-consistency
   conjuncts are discharged, so nothing remains but the one rounded-vs-exact
   Liang-Barsky touch. *)
Theorem b64_passes_through_grid_exact_iff_touch :
  forall P0 P1 C : BPoint,
    b64_on_grid P0 -> b64_on_grid P1 ->
    ( b64_passes_through_hot_pixel_compute P0 P1 C
        = b64_passes_through_hot_pixel P0 P1 C
      <->
      b64_liang_barsky_touches_compute P0 P1 C
        = b64_liang_barsky_touches P0 P1 C ).
Proof.
  intros P0 P1 C H0 H1.
  rewrite (b64_passes_through_collapses_on_grid P0 P1 C H0 H1).
  rewrite (b64_passes_through_compute_collapses_on_grid P0 P1 C H0 H1).
  tauto.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 2: the integer grid IS the fixed-point grid.

   The reduction above is stated over `b64_on_grid` (fixed point of b64_snap).
   The dyadic-exactness machinery (Orient_b64_exact.coord_int_safe: finite,
   integer-valued, |.| <= 2^25) lives over the integer regime.  This slice
   connects them: an integer-grid coordinate is a snap fixed point, so the
   reduction's hypothesis is DISCHARGED for genuine integer-grid inputs (the
   noder's snapped coordinates), and the exactness layer can proceed in the
   integer regime.
   ---------------------------------------------------------------------------- *)

Lemma coord_int_safe_snap_id :
  forall x : binary64, coord_int_safe x -> b64_snap_coord x = x.
Proof.
  intros x Hsafe.
  destruct Hsafe as [Hfin [n [Hn _]]].
  destruct (Binary.Bnearbyint_correct prec emax prec_lt_emax_b64
              nearbyint_nan_b64 mode_NE x) as [_ [Hfin2 Hsgn]].
  assert (Hf : Binary.is_finite prec emax (b64_snap_coord x) = true).
  { unfold b64_snap_coord. rewrite Hfin2. exact Hfin. }
  apply Binary.B2R_Bsign_inj.
  - exact Hf.
  - exact Hfin.
  - rewrite b64_snap_coord_B2R. unfold snap_round_coord.
    rewrite Rmult_1_r, Rdiv_1_r, round_FIX0_IZR, Hn.
    f_equal. apply (Zrnd_IZR (round_mode mode_NE)).
  - unfold b64_snap_coord. rewrite Hsgn.
    + reflexivity.
    + apply is_finite_not_nan. exact Hf.
Qed.

(* Point-level integer grid. *)
Definition bpoint_int_safe (P : BPoint) : Prop :=
  coord_int_safe (bx P) /\ coord_int_safe (by_ P).

Lemma bpoint_int_safe_on_grid :
  forall P : BPoint, bpoint_int_safe P -> b64_on_grid P.
Proof.
  intros P [Hx Hy]. unfold b64_on_grid, b64_snap.
  destruct P as [xp yp]; simpl in *.
  f_equal; apply coord_int_safe_snap_id; assumption.
Qed.

(* The reduction, specialised to genuine integer-grid inputs: full-predicate
   grid-exactness reduces to the single Liang-Barsky touch.  This is the form
   the exactness layer will consume. *)
Corollary b64_passes_through_grid_exact_iff_touch_int :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 ->
    ( b64_passes_through_hot_pixel_compute P0 P1 C
        = b64_passes_through_hot_pixel P0 P1 C
      <->
      b64_liang_barsky_touches_compute P0 P1 C
        = b64_liang_barsky_touches P0 P1 C ).
Proof.
  intros P0 P1 C H0 H1.
  apply b64_passes_through_grid_exact_iff_touch;
    apply bpoint_int_safe_on_grid; assumption.
Qed.

(* Comparison bridge (foundation for the slab-guard layer): on finite operands
   the computational equality test reflects exact-real equality. *)
Lemma b64_eqb_true_iff_B2R :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    (b64_eqb x y = true <-> Binary.B2R prec emax x = Binary.B2R prec emax y).
Proof.
  intros x y Fx Fy. unfold b64_eqb, b64_compare.
  rewrite Binary.Bcompare_correct by assumption.
  destruct (Rcompare (Binary.B2R prec emax x) (Binary.B2R prec emax y)) eqn:E.
  - apply Rcompare_Eq_inv in E. split; [intros _; exact E | reflexivity].
  - apply Rcompare_Lt_inv in E. split; [discriminate | intros He; lra].
  - apply Rcompare_Gt_inv in E. split; [discriminate | intros He; lra].
Qed.

(* ----------------------------------------------------------------------------
   SLICE 3: the slab-guard layer (division-free).

   The degenerate (axis-parallel, c1 = c0) guard of the Liang-Barsky touch uses
   only equality / <= comparisons -- NO division -- so the rounded compute guard
   equals the exact-spec guard whenever they read the same B2R values.  This is
   the first of the two non-division layers of the single-touch equivalence.
   ---------------------------------------------------------------------------- *)

(* Boolean form of the b64_le <-> Rle bridge (both directions already in
   HotPixel_b64: b64_le_R_of_true / b64_le_complete). *)
Lemma b64_le_eq_Rle_bool :
  forall a b : binary64,
    Binary.is_finite prec emax a = true ->
    Binary.is_finite prec emax b = true ->
    b64_le a b = Rle_bool (Binary.B2R prec emax a) (Binary.B2R prec emax b).
Proof.
  intros a b Fa Fb. destruct (b64_le a b) eqn:E.
  - symmetry. apply Rle_bool_true. apply b64_le_R_of_true; assumption.
  - symmetry. apply Rle_bool_false.
    destruct (Rle_lt_dec (Binary.B2R prec emax a) (Binary.B2R prec emax b))
      as [Hle | Hlt].
    + apply b64_le_complete in Hle; [ congruence | assumption | assumption ].
    + exact Hlt.
Qed.

(* Slab-guard bridge: the compute degenerate-slab guard on binary64 operands
   equals the exact-spec guard on their B2R values.  Pure comparison bridging;
   no exactness of the slab bounds is needed here (both sides read the SAME
   B2R values). *)
Lemma slab_guard_bridge :
  forall c0 c1 lo hi : binary64,
    Binary.is_finite prec emax c0 = true ->
    Binary.is_finite prec emax c1 = true ->
    Binary.is_finite prec emax lo = true ->
    Binary.is_finite prec emax hi = true ->
    b64_lb_inslab_closed c0 c1 lo hi
      = lb_inslab (Binary.B2R prec emax c0) (Binary.B2R prec emax c1)
                  (Binary.B2R prec emax lo) (Binary.B2R prec emax hi).
Proof.
  intros c0 c1 lo hi F0 F1 Flo Fhi.
  unfold b64_lb_inslab_closed, lb_inslab.
  destruct (Req_dec_T (Binary.B2R prec emax c1) (Binary.B2R prec emax c0))
    as [Heq | Hneq].
  - replace (b64_eqb c1 c0) with true.
    + rewrite (b64_le_eq_Rle_bool lo c0), (b64_le_eq_Rle_bool c0 hi); try assumption.
      reflexivity.
    + symmetry. apply (b64_eqb_true_iff_B2R c1 c0 F1 F0). exact Heq.
  - replace (b64_eqb c1 c0) with false.
    + reflexivity.
    + symmetry. destruct (b64_eqb c1 c0) eqn:E; [ | reflexivity ].
      apply (b64_eqb_true_iff_B2R c1 c0 F1 F0) in E. congruence.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 4: the coordinate-exactness layer.

   On the integer grid every binary64 operation feeding the t-bounds EXCEPT the
   division is exact.  The slab bounds (cx +/- 1/2) are already covered by
   HotPixel_b64.b64_minus_half_int_exact / b64_plus_half_int_exact, and the
   t-bound DENOMINATOR (c1 - c0, integer - integer) by Orient_b64_exact.
   b64_minus_int_exact.  The missing piece is the t-bound NUMERATOR
   (lo - c0): a half-integer slab bound minus an integer endpoint, whose
   magnitude (~2^27) exceeds the existing 27-bit format helper.  This slice adds
   the general half-integer subtraction exactness (any two half-integer-valued
   operands whose mantissa difference is < 2^prec), which covers the numerators
   and subsumes the integer / b64_half special cases.
   ---------------------------------------------------------------------------- *)

(* generic_format of any half-integer m/2 with |m| < 2^prec (the 27-bit helper
   in HotPixel_b64 widened to the full mantissa range). *)
Lemma generic_format_half_prec :
  forall m : Z,
    (Z.abs m < 2 ^ prec)%Z ->
    generic_format radix2 b64_fexp (F2R (Float radix2 m (-1))).
Proof.
  intros m Hm.
  destruct (Z.eq_dec m 0) as [-> | Hnz].
  - replace (F2R (Float radix2 0 (-1))) with 0%R
      by (unfold F2R; simpl; lra).
    apply generic_format_0.
  - apply generic_format_F2R. intros _.
    unfold cexp, b64_fexp, SpecFloat.fexp.
    apply Z.max_lub.
    + rewrite (mag_F2R radix2 m (-1) Hnz).
      assert (Hmag_m : (mag radix2 (IZR m) <= prec)%Z).
      { apply mag_le_bpow.
        - apply IZR_neq. exact Hnz.
        - rewrite <- abs_IZR.
          rewrite <- (IZR_Zpower radix2 prec) by (unfold prec; lia).
          apply IZR_lt. exact Hm. }
      lia.
    + unfold SpecFloat.emin, emax, prec. lia.
Qed.

(* General half-integer subtraction exactness: if B2R x and B2R y are both
   half-integers (IZR _ / 2) and their mantissa difference fits in prec bits,
   b64_minus is exact.  Covers the t-bound numerator (half-integer slab bound
   minus integer endpoint) and the denominator/integer cases. *)
Lemma b64_minus_half_exact :
  forall (x y : binary64) (a b : Z),
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax x = (IZR a / 2)%R ->
    Binary.B2R prec emax y = (IZR b / 2)%R ->
    (Z.abs (a - b) < 2 ^ prec)%Z ->
    Binary.B2R prec emax (b64_minus x y)
      = (Binary.B2R prec emax x - Binary.B2R prec emax y)%R
    /\ Binary.is_finite prec emax (b64_minus x y) = true.
Proof.
  intros x y a b Fx Fy HxR HyR Hbnd.
  assert (Hr_F2R : (Binary.B2R prec emax x - Binary.B2R prec emax y)%R
                   = F2R (Float radix2 (a - b)%Z (-1))).
  { rewrite HxR, HyR. unfold F2R, Fnum, Fexp.
    replace (bpow radix2 (-1)) with (/ 2)%R by (simpl; lra).
    rewrite minus_IZR. lra. }
  assert (Hr_fmt : generic_format radix2 b64_fexp
                     (Binary.B2R prec emax x - Binary.B2R prec emax y)%R).
  { rewrite Hr_F2R. apply generic_format_half_prec. exact Hbnd. }
  assert (Hbnd_R : (Rabs (IZR (a - b)) < bpow radix2 prec)%R).
  { rewrite <- abs_IZR.
    rewrite <- (IZR_Zpower radix2 prec) by (unfold prec; lia).
    apply IZR_lt. exact Hbnd. }
  assert (Hsafe : b64_safe Rminus x y).
  { unfold b64_safe. split; [exact Fx | split; [exact Fy |]].
    rewrite (b64_round_generic _ Hr_fmt), Hr_F2R.
    unfold F2R, Fnum, Fexp.
    replace (bpow radix2 (-1)) with (/ 2)%R by (simpl; lra).
    rewrite Rabs_mult, (Rabs_right (/ 2)%R) by lra.
    apply (Rlt_le_trans _ (bpow radix2 prec * / 2)%R).
    - apply Rmult_lt_compat_r; [lra | exact Hbnd_R].
    - apply (Rle_trans _ (bpow radix2 prec)%R).
      + pose proof (bpow_gt_0 radix2 prec). lra.
      + apply bpow_le. unfold prec, emax. lia. }
  pose proof (b64_minus_correct _ _ Hsafe) as [HB2R Hfin].
  split; [| exact Hfin].
  rewrite HB2R, (b64_round_generic _ Hr_fmt). reflexivity.
Qed.

(* ----------------------------------------------------------------------------
   REMAINING OBLIGATION (the hard, multi-session core -- NOT an axiom).

     Open goal (single-touch grid exactness), strongly evidenced (0/5e6):
       forall P0 P1 C, <P0,P1,C on the integer grid> ->
         b64_liang_barsky_touches_compute P0 P1 C
           = b64_liang_barsky_touches P0 P1 C.

   Why it is hard: on the grid the slab guards and the t-bound NUMERATORS /
   DENOMINATORS (b64_minus of half-integers) are exact, but the t-bounds
   themselves are `b64_div`, which ROUNDS.  Round-to-nearest gives no outward
   guarantee, so the rounded `Rmax 0 (...) <= Rmin 1 (...)` comparison is not
   definitionally the exact one.

   Strategy for the core (next session): rewrite the exact comparison
   `lb_tlo <= lb_thi` etc. by CROSS-MULTIPLYING through the (exact integer)
   denominators, turning each pairwise t-bound comparison into the SIGN of an
   integer determinant -- a decision that does not divide and is exactly
   representable in binary64 on the grid (cf. Orient_b64_exact.v's dyadic
   exactness, b64_minus_int_exact / b64_mult_int_exact).  Then show the rounded
   `b64_div`-based comparison has the same outcome because the integer
   determinant is nonzero-with-gap >= 1 except in the exactly-equal case the
   rounding also preserves.
   ---------------------------------------------------------------------------- *)
