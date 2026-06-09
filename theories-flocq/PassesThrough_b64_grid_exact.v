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

   THIS FILE lands the REDUCTION + EXACTNESS layers, Qed-closed:

     - Slice 1: on the grid the snap-consistency second conjunct of
       `passes_through` is vacuous (a grid point is a fixed point of `b64_snap`),
       so the full predicate collapses to a single Liang-Barsky touch -- for
       BOTH the rounded compute filter and the exact spec.  C1 therefore reduces
       to the single-touch equivalence
           b64_liang_barsky_touches_compute = b64_liang_barsky_touches (on grid).
     - Slices 3-5: the slab guard, the t-bound operands, and the max/min/clip
       composition all bridge bit-exactly between compute and spec on the grid.
     - Slice 6: the only place `b64_div` (which ROUNDS) enters is discharged of
       its safety precondition and rewritten so each compute t-bound equals the
       spec t-bound with each quotient INDIVIDUALLY ROUNDED.
     - Slices 7-8: rounding is monotone, so it commutes past Rmin/Rmax and the
       outer clip -- collapsing every compute t-bound, and the whole clipped
       tmin/tmax, into a single `b64_round` of the exact spec value.
     - Slice 9: ON-GRID COMPLETENESS, Qed -- one of C1's two directions is
       CLOSED.  `spec = true => compute = true` on the grid (the rounded filter
       never DROPS a pass; the noder-safe direction), free from monotonicity.
     - Slice 10: CONDITIONAL grid-exactness, Qed -- the full on-grid
       `compute = spec` equivalence certified modulo ONE named real hypothesis
       (the rounded clip comparison reflects the exact one).  Same honest shape
       as hobby_theorem_4_1_conditional; the gap is a Prop hypothesis, not an
       axiom.
     - Slice 11: rounding-reflection kernel, Qed -- since round-to-nearest moves
       each value by <= half a ulp, the rounded `<=` reflects the exact `<=`
       once the values are ordered or separated beyond the half-ulp band.  This
       discharges Slice 10's rounding hypothesis in favour of the PURE-REALS
       `clip_separated` (no rounding in the statement).
     - Slice 12: determinant-gap kernel, Qed -- two distinct rationals differ by
       >= 1/(|da| |db|) (`rational_gap`), and each grid t-bound is exactly such a
       ratio (`grid_quotient_ratio`).  The LOWER-bound (gap) half of
       `clip_separated`.
     - Slice 13: ulp UPPER bound, Qed -- `|x| <= 2^e => ulp(round x) <=
       2^(e+1-prec)` (`b64_ulp_round_le_bpow`), so bounds in [0,1] give
       ulp(round x) <= 2^-52 (`b64_ulp_round_le_unit`).  The UPPER-bound half of
       `clip_separated`.
     - Slice 14: the bricks COMBINE, Qed -- for two distinct ratios u, v in
       [-1,1] with denominators <= 2^24, `1/2 ulp(round u) + 1/2 ulp(round v)
       < |u - v|` (`grid_ratio_gap_exceeds_ulp_band`): band <= 2^-52 < 2^-48 <=
       gap.  This is EXACTLY `clip_separated`'s right disjunct for the binding
       pair -- the determinant-beats-rounding inequality, done.

   What remains is exactly `clip_separated`, and it is now PURELY STRUCTURAL: the
   analytic content (gap > band) is Slice 14.  The remaining step exhibits
   tmin_e, tmax_e as bounded integer ratios (each `Rmax`/`Rmin` selects one of
   {0,1,tlo_x,tlo_y,thi_x,thi_y}, all ratios via `grid_quotient_ratio`) and
   applies Slice 14.  Its "interval nonempty" half is free (Slice 9
   completeness); only the empty/soundness half is open.  See the OBLIGATION
   note at the bottom; it is NOT discharged here and NO `Admitted` is
   introduced -- the file is Qed-clean and the open core is a comment, not an
   axiom.

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
   SLICE 5: the max / min composition bridge (division-free).

   The t-bound comparison clips with b64_max 0 / b64_min 1 over the per-axis
   bounds.  b64_max / b64_min are operand-selecting (by b64_le), so on finite
   operands they bridge exactly to Rmax / Rmin on the B2R values.  This reduces
   the whole clipped-interval test to a comparison of the REAL values of the
   (rounded) t-bounds -- isolating the division rounding to the per-bound level,
   the last layer before the hard core.
   ---------------------------------------------------------------------------- *)

Lemma is_finite_b64_max :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.is_finite prec emax (b64_max x y) = true.
Proof. intros x y Fx Fy. unfold b64_max. destruct (b64_le x y); assumption. Qed.

Lemma is_finite_b64_min :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.is_finite prec emax (b64_min x y) = true.
Proof. intros x y Fx Fy. unfold b64_min. destruct (b64_le x y); assumption. Qed.

Lemma b64_max_B2R :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax (b64_max x y)
      = Rmax (Binary.B2R prec emax x) (Binary.B2R prec emax y).
Proof.
  intros x y Fx Fy. unfold b64_max. destruct (b64_le x y) eqn:E.
  - symmetry. apply Rmax_right. apply b64_le_R_of_true; assumption.
  - symmetry. apply Rmax_left.
    destruct (Rle_lt_dec (Binary.B2R prec emax x) (Binary.B2R prec emax y))
      as [Hle | Hlt].
    + apply b64_le_complete in Hle; [ congruence | assumption | assumption ].
    + lra.
Qed.

Lemma b64_min_B2R :
  forall x y : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax (b64_min x y)
      = Rmin (Binary.B2R prec emax x) (Binary.B2R prec emax y).
Proof.
  intros x y Fx Fy. unfold b64_min. destruct (b64_le x y) eqn:E.
  - symmetry. apply Rmin_left. apply b64_le_R_of_true; assumption.
  - symmetry. apply Rmin_right.
    destruct (Rle_lt_dec (Binary.B2R prec emax x) (Binary.B2R prec emax y))
      as [Hle | Hlt].
    + apply b64_le_complete in Hle; [ congruence | assumption | assumption ].
    + lra.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 6: the division bridge -- the LAST exactness layer before the core.

   The t-bounds are the only place `b64_div` (which ROUNDS) enters.  This slice
   discharges the division's `b64_div_correct` preconditions on the grid and
   rewrites each per-axis compute t-bound as the spec t-bound with each exact
   quotient INDIVIDUALLY ROUNDED:

       b64_lb_tlo c0 c1 (cc-1/2) (cc+1/2)
         = Rmin (round ((lo - c0)/(c1 - c0))) (round ((hi - c0)/(c1 - c0)))   (Qed)

   (and the Rmax analogue for b64_lb_thi).  Combined with Slices 4-5 (operand
   exactness + max/min bridge), the rounded compute filter now differs from the
   exact spec ONLY by the `round` wrapped around each individual quotient: the
   division is the single, fully-localised residual.  No division-safety obligation
   remains open -- it is discharged here (|num/den| <= |num| <= 2^27 on the grid).
   ---------------------------------------------------------------------------- *)

(* One quotient.  A half-integer numerator over a NONZERO INTEGER denominator
   divides bit-correctly to the rounded exact quotient.  The `b64_div_correct`
   safety bound is discharged from the grid magnitudes: |num/den| <= |num|
   (since |den| >= 1) <= 2^27 < 2^emax. *)
Lemma b64_div_round_half_over_int :
  forall (num den : binary64) (a d : Z),
    Binary.is_finite prec emax num = true ->
    Binary.is_finite prec emax den = true ->
    Binary.B2R prec emax num = (IZR a / 2)%R ->
    Binary.B2R prec emax den = IZR d ->
    (d <> 0)%Z ->
    (Z.abs a < 2 ^ 28)%Z ->
    Binary.B2R prec emax (b64_div num den)
      = b64_round (Binary.B2R prec emax num / Binary.B2R prec emax den)
    /\ Binary.is_finite prec emax (b64_div num den) = true.
Proof.
  intros num den a d Fnum Fden HnumR HdenR Hd Ha.
  assert (Hden_ne : Binary.B2R prec emax den <> 0%R).
  { rewrite HdenR. apply IZR_neq. exact Hd. }
  (* |den| = IZR |d| >= 1 *)
  assert (Hden_ge1 : (1 <= Rabs (Binary.B2R prec emax den))%R).
  { rewrite HdenR, <- abs_IZR.
    replace 1%R with (IZR 1) by (simpl; reflexivity).
    apply IZR_le. lia. }
  (* |num| = IZR |a| / 2 <= bpow 27 *)
  assert (Hnum_le : (Rabs (Binary.B2R prec emax num) <= bpow radix2 28)%R).
  { rewrite HnumR. unfold Rdiv. rewrite Rabs_mult, (Rabs_right (/ 2)%R) by lra.
    rewrite <- abs_IZR.
    assert (Ha28 : (IZR (Z.abs a) < bpow radix2 28)%R).
    { rewrite <- (IZR_Zpower radix2 28) by lia. apply IZR_lt. exact Ha. }
    pose proof (bpow_gt_0 radix2 28). lra. }
  assert (Hbnd : (Rabs (b64_round (Binary.B2R prec emax num
                                    / Binary.B2R prec emax den))
                   < bpow radix2 emax)%R).
  { apply (Rle_lt_trans _ (bpow radix2 28)).
    - apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
      (* Rabs (num/den) = Rabs num / Rabs den <= Rabs num <= bpow 27 *)
      unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
      apply (Rle_trans _ (Rabs (Binary.B2R prec emax num))); [ | exact Hnum_le ].
      rewrite <- (Rmult_1_r (Rabs (Binary.B2R prec emax num))) at 2.
      apply Rmult_le_compat_l; [ apply Rabs_pos | ].
      rewrite <- Rinv_1.
      apply Rinv_le_contravar; [ lra | exact Hden_ge1 ].
    - apply bpow_lt. unfold emax; lia. }
  exact (b64_div_correct num den Fnum Fden Hden_ne Hbnd).
Qed.

(* Operand facts for one (edge, endpoint) pair on the integer grid: the
   numerator `edge - c0` is a half-integer with mantissa < 2^27, computed
   bit-exactly. *)
Lemma grid_numerator_facts :
  forall (edge c0 : binary64) (m n0 : Z),
    Binary.is_finite prec emax edge = true ->
    Binary.is_finite prec emax c0 = true ->
    Binary.B2R prec emax edge = (IZR m / 2)%R ->
    Binary.B2R prec emax c0 = IZR n0 ->
    (Z.abs m < 2 ^ 27)%Z ->
    (Z.abs n0 <= 2 ^ 25)%Z ->
    Binary.B2R prec emax (b64_minus edge c0)
      = (IZR (m - 2 * n0)%Z / 2)%R
    /\ Binary.is_finite prec emax (b64_minus edge c0) = true
    /\ (Z.abs (m - 2 * n0) < 2 ^ 28)%Z
    /\ Binary.B2R prec emax (b64_minus edge c0)
         = (Binary.B2R prec emax edge - Binary.B2R prec emax c0)%R.
Proof.
  intros edge c0 m n0 Fe F0 HeR H0R Hm Hn0.
  assert (H0half : Binary.B2R prec emax c0 = (IZR (2 * n0)%Z / 2)%R).
  { rewrite H0R, mult_IZR. lra. }
  pose proof (b64_minus_half_exact edge c0 m (2 * n0)%Z Fe F0 HeR H0half
                ltac:(unfold prec; lia)) as [HsubR Hsubfin].
  repeat split.
  - rewrite HsubR, HeR, H0half. rewrite minus_IZR, mult_IZR. lra.
  - exact Hsubfin.
  - lia.
  - exact HsubR.
Qed.

(* tlo (lower) per-axis bridge: the compute lower t-bound on the grid is the
   Rmin of the two rounded exact quotients the spec uses. *)
Theorem b64_lb_tlo_eq_rounded_quotients_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.B2R prec emax c1 <> Binary.B2R prec emax c0 ->
    Binary.B2R prec emax
        (b64_lb_tlo c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half))
      = Rmin
          (b64_round ((Binary.B2R prec emax (b64_minus cc b64_half)
                        - Binary.B2R prec emax c0)
                      / (Binary.B2R prec emax c1 - Binary.B2R prec emax c0)))
          (b64_round ((Binary.B2R prec emax (b64_plus cc b64_half)
                        - Binary.B2R prec emax c0)
                      / (Binary.B2R prec emax c1 - Binary.B2R prec emax c0))).
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc Hne.
  pose proof Hc0 as (Fc0 & n0 & H0R & H0b).
  pose proof Hc1 as (Fc1 & n1 & H1R & H1b).
  pose proof Hcc as (Fcc & ncc & HccR & Hccb).
  (* the two pixel edges and their exact half-integer images *)
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR Flo].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR Fhi].
  assert (HloHalf : Binary.B2R prec emax (b64_minus cc b64_half)
                    = (IZR (2 * ncc - 1)%Z / 2)%R).
  { rewrite HloR, HccR. rewrite minus_IZR, mult_IZR. lra. }
  assert (HhiHalf : Binary.B2R prec emax (b64_plus cc b64_half)
                    = (IZR (2 * ncc + 1)%Z / 2)%R).
  { rewrite HhiR, HccR. rewrite plus_IZR, mult_IZR. lra. }
  (* non-degenerate: b64_eqb c1 c0 = false *)
  assert (Heqb : b64_eqb c1 c0 = false).
  { destruct (b64_eqb c1 c0) eqn:E; [ | reflexivity ].
    apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0) in E. contradiction. }
  (* numerator facts *)
  pose proof (grid_numerator_facts (b64_minus cc b64_half) c0 (2*ncc-1) n0
                Flo Fc0 HloHalf H0R ltac:(lia) ltac:(lia))
    as (HnumLoR & HnumLoFin & HnumLoB & HnumLoDiff).
  pose proof (grid_numerator_facts (b64_plus cc b64_half) c0 (2*ncc+1) n0
                Fhi Fc0 HhiHalf H0R ltac:(lia) ltac:(lia))
    as (HnumHiR & HnumHiFin & HnumHiB & HnumHiDiff).
  (* denominator facts: c1 - c0 = IZR (n1 - n0) (and the difference form), nonzero *)
  assert (H1half : Binary.B2R prec emax c1 = (IZR (2 * n1)%Z / 2)%R)
    by (rewrite H1R, mult_IZR; lra).
  assert (H0half : Binary.B2R prec emax c0 = (IZR (2 * n0)%Z / 2)%R)
    by (rewrite H0R, mult_IZR; lra).
  pose proof (b64_minus_half_exact c1 c0 (2*n1) (2*n0) Fc1 Fc0 H1half H0half
                ltac:(unfold prec; lia)) as [HdenDiff HdenFin].
  assert (HdenRv : Binary.B2R prec emax (b64_minus c1 c0) = IZR (n1 - n0)%Z)
    by (rewrite HdenDiff, H1R, H0R, minus_IZR; lra).
  assert (Hdne : (n1 - n0 <> 0)%Z).
  { intro Hz. apply Hne. rewrite H1R, H0R. apply f_equal. lia. }
  (* divide each numerator by the denominator, bit-correctly *)
  pose proof (b64_div_round_half_over_int (b64_minus (b64_minus cc b64_half) c0)
                (b64_minus c1 c0) (2*ncc-1 - 2*n0) (n1 - n0)
                HnumLoFin HdenFin HnumLoR HdenRv Hdne ltac:(lia))
    as [HdivLoR HdivLoFin].
  pose proof (b64_div_round_half_over_int (b64_minus (b64_plus cc b64_half) c0)
                (b64_minus c1 c0) (2*ncc+1 - 2*n0) (n1 - n0)
                HnumHiFin HdenFin HnumHiR HdenRv Hdne ltac:(lia))
    as [HdivHiR HdivHiFin].
  (* assemble: b64_lb_tlo in the non-degenerate branch is b64_min of the divs *)
  unfold b64_lb_tlo. rewrite Heqb.
  rewrite (b64_min_B2R _ _ HdivLoFin HdivHiFin).
  rewrite HdivLoR, HdivHiR.
  rewrite HnumLoDiff, HnumHiDiff, HdenDiff.
  reflexivity.
Qed.

(* thi (upper) per-axis bridge: the compute upper t-bound on the grid is the
   Rmax of the two rounded exact quotients.  Same proof shape as tlo, with
   b64_max / Rmax. *)
Theorem b64_lb_thi_eq_rounded_quotients_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.B2R prec emax c1 <> Binary.B2R prec emax c0 ->
    Binary.B2R prec emax
        (b64_lb_thi c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half))
      = Rmax
          (b64_round ((Binary.B2R prec emax (b64_minus cc b64_half)
                        - Binary.B2R prec emax c0)
                      / (Binary.B2R prec emax c1 - Binary.B2R prec emax c0)))
          (b64_round ((Binary.B2R prec emax (b64_plus cc b64_half)
                        - Binary.B2R prec emax c0)
                      / (Binary.B2R prec emax c1 - Binary.B2R prec emax c0))).
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc Hne.
  pose proof Hc0 as (Fc0 & n0 & H0R & H0b).
  pose proof Hc1 as (Fc1 & n1 & H1R & H1b).
  pose proof Hcc as (Fcc & ncc & HccR & Hccb).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR Flo].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR Fhi].
  assert (HloHalf : Binary.B2R prec emax (b64_minus cc b64_half)
                    = (IZR (2 * ncc - 1)%Z / 2)%R)
    by (rewrite HloR, HccR, minus_IZR, mult_IZR; lra).
  assert (HhiHalf : Binary.B2R prec emax (b64_plus cc b64_half)
                    = (IZR (2 * ncc + 1)%Z / 2)%R)
    by (rewrite HhiR, HccR, plus_IZR, mult_IZR; lra).
  assert (Heqb : b64_eqb c1 c0 = false).
  { destruct (b64_eqb c1 c0) eqn:E; [ | reflexivity ].
    apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0) in E. contradiction. }
  pose proof (grid_numerator_facts (b64_minus cc b64_half) c0 (2*ncc-1) n0
                Flo Fc0 HloHalf H0R ltac:(lia) ltac:(lia))
    as (HnumLoR & HnumLoFin & HnumLoB & HnumLoDiff).
  pose proof (grid_numerator_facts (b64_plus cc b64_half) c0 (2*ncc+1) n0
                Fhi Fc0 HhiHalf H0R ltac:(lia) ltac:(lia))
    as (HnumHiR & HnumHiFin & HnumHiB & HnumHiDiff).
  assert (H1half : Binary.B2R prec emax c1 = (IZR (2 * n1)%Z / 2)%R)
    by (rewrite H1R, mult_IZR; lra).
  assert (H0half : Binary.B2R prec emax c0 = (IZR (2 * n0)%Z / 2)%R)
    by (rewrite H0R, mult_IZR; lra).
  pose proof (b64_minus_half_exact c1 c0 (2*n1) (2*n0) Fc1 Fc0 H1half H0half
                ltac:(unfold prec; lia)) as [HdenDiff HdenFin].
  assert (HdenRv : Binary.B2R prec emax (b64_minus c1 c0) = IZR (n1 - n0)%Z)
    by (rewrite HdenDiff, H1R, H0R, minus_IZR; lra).
  assert (Hdne : (n1 - n0 <> 0)%Z).
  { intro Hz. apply Hne. rewrite H1R, H0R. apply f_equal. lia. }
  pose proof (b64_div_round_half_over_int (b64_minus (b64_minus cc b64_half) c0)
                (b64_minus c1 c0) (2*ncc-1 - 2*n0) (n1 - n0)
                HnumLoFin HdenFin HnumLoR HdenRv Hdne ltac:(lia))
    as [HdivLoR HdivLoFin].
  pose proof (b64_div_round_half_over_int (b64_minus (b64_plus cc b64_half) c0)
                (b64_minus c1 c0) (2*ncc+1 - 2*n0) (n1 - n0)
                HnumHiFin HdenFin HnumHiR HdenRv Hdne ltac:(lia))
    as [HdivHiR HdivHiFin].
  unfold b64_lb_thi. rewrite Heqb.
  rewrite (b64_max_B2R _ _ HdivLoFin HdivHiFin).
  rewrite HdivLoR, HdivHiR.
  rewrite HnumLoDiff, HnumHiDiff, HdenDiff.
  reflexivity.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 7: the t-bounds are the CORRECTLY-ROUNDED exact t-bounds on the grid.

   Rounding is monotone, so Rmin (round a) (round b) = round (Rmin a b) (dually
   for Rmax).  Composing this with Slice 6 collapses each per-axis compute
   t-bound -- an Rmin/Rmax of two ROUNDED quotients -- into a single `b64_round`
   of the exact spec t-bound.  The degenerate (axis-parallel) branch matches
   trivially (0 = round 0, 1 = round 1), so the bridge is UNCONDITIONAL.
   ---------------------------------------------------------------------------- *)

(* b64_zero facts (b64_one's are in HotPixel_b64). *)
Lemma B2R_b64_zero : Binary.B2R prec emax b64_zero = 0%R.
Proof. reflexivity. Qed.

Lemma is_finite_b64_zero : Binary.is_finite prec emax b64_zero = true.
Proof. reflexivity. Qed.

Lemma b64_round_1 : b64_round 1 = 1%R.
Proof.
  apply b64_round_generic.
  assert (H1 : (1)%R = F2R (Float radix2 2 (-1))) by (unfold F2R; simpl; lra).
  rewrite H1. apply generic_format_half_prec. unfold prec; lia.
Qed.

(* Rounding commutes with Rmin / Rmax (monotonicity of round-to-nearest). *)
Lemma round_Rmin :
  forall a b : R, Rmin (b64_round a) (b64_round b) = b64_round (Rmin a b).
Proof.
  intros a b. destruct (Rle_dec a b) as [H | H].
  - rewrite (Rmin_left a b H). apply Rmin_left.
    apply (round_le radix2 b64_fexp (round_mode mode_b64)); exact H.
  - assert (Hb : (b <= a)%R) by lra.
    rewrite (Rmin_right a b Hb). apply Rmin_right.
    apply (round_le radix2 b64_fexp (round_mode mode_b64)); exact Hb.
Qed.

Lemma round_Rmax :
  forall a b : R, Rmax (b64_round a) (b64_round b) = b64_round (Rmax a b).
Proof.
  intros a b. destruct (Rle_dec a b) as [H | H].
  - rewrite (Rmax_right a b H). apply Rmax_right.
    apply (round_le radix2 b64_fexp (round_mode mode_b64)); exact H.
  - assert (Hb : (b <= a)%R) by lra.
    rewrite (Rmax_left a b Hb). apply Rmax_left.
    apply (round_le radix2 b64_fexp (round_mode mode_b64)); exact Hb.
Qed.

(* Clip composition: rounding commutes past the outer max-with-0 / min-with-1. *)
Lemma round_clip_max0 :
  forall a : R, Rmax 0 (b64_round a) = b64_round (Rmax 0 a).
Proof.
  intros a. rewrite <- round_Rmax, (round_0 radix2 b64_fexp (round_mode mode_b64)).
  reflexivity.
Qed.

Lemma round_clip_min1 :
  forall a : R, Rmin 1 (b64_round a) = b64_round (Rmin 1 a).
Proof. intros a. rewrite <- round_Rmin, b64_round_1. reflexivity. Qed.

(* Division finiteness on the grid: one t-bound quotient (half-integer
   numerator over a nonzero integer run) is finite.  Reuses Slice 6's pieces. *)
Lemma b64_div_edge_grid_finite :
  forall (edge c0 c1 : binary64) (m n0 n1 : Z),
    Binary.is_finite prec emax edge = true ->
    Binary.is_finite prec emax c0 = true ->
    Binary.is_finite prec emax c1 = true ->
    Binary.B2R prec emax edge = (IZR m / 2)%R ->
    Binary.B2R prec emax c0 = IZR n0 ->
    Binary.B2R prec emax c1 = IZR n1 ->
    (Z.abs m < 2 ^ 27)%Z ->
    (Z.abs n0 <= 2 ^ 25)%Z ->
    (Z.abs n1 <= 2 ^ 25)%Z ->
    (n1 <> n0)%Z ->
    Binary.is_finite prec emax
      (b64_div (b64_minus edge c0) (b64_minus c1 c0)) = true.
Proof.
  intros edge c0 c1 m n0 n1 Fe F0 F1 HeR H0R H1R Hm Hn0 Hn1 Hne.
  pose proof (grid_numerator_facts edge c0 m n0 Fe F0 HeR H0R Hm Hn0)
    as (HnumR & HnumFin & HnumB & _).
  assert (H0half : Binary.B2R prec emax c0 = (IZR (2 * n0)%Z / 2)%R)
    by (rewrite H0R, mult_IZR; lra).
  assert (H1half : Binary.B2R prec emax c1 = (IZR (2 * n1)%Z / 2)%R)
    by (rewrite H1R, mult_IZR; lra).
  pose proof (b64_minus_half_exact c1 c0 (2*n1) (2*n0) F1 F0 H1half H0half
                ltac:(unfold prec; lia)) as [HdenR HdenFin].
  assert (HdenRv : Binary.B2R prec emax (b64_minus c1 c0) = IZR (n1 - n0)%Z)
    by (rewrite HdenR, H1R, H0R, minus_IZR; lra).
  exact (proj2 (b64_div_round_half_over_int (b64_minus edge c0) (b64_minus c1 c0)
                  (m - 2*n0) (n1 - n0) HnumFin HdenFin HnumR HdenRv
                  ltac:(lia) ltac:(lia))).
Qed.

Lemma b64_lb_tlo_finite_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.is_finite prec emax
      (b64_lb_tlo c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half)) = true.
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc.
  pose proof Hc0 as (Fc0 & n0 & H0R & H0b).
  pose proof Hc1 as (Fc1 & n1 & H1R & H1b).
  pose proof Hcc as (Fcc & ncc & HccR & Hccb).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR Flo].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR Fhi].
  assert (HloHalf : Binary.B2R prec emax (b64_minus cc b64_half) = (IZR (2*ncc-1)%Z / 2)%R)
    by (rewrite HloR, HccR, minus_IZR, mult_IZR; lra).
  assert (HhiHalf : Binary.B2R prec emax (b64_plus cc b64_half) = (IZR (2*ncc+1)%Z / 2)%R)
    by (rewrite HhiR, HccR, plus_IZR, mult_IZR; lra).
  unfold b64_lb_tlo.
  destruct (b64_eqb c1 c0) eqn:Heqb.
  - exact is_finite_b64_zero.
  - assert (Hne : (n1 <> n0)%Z).
    { intro He. assert (Heq : Binary.B2R prec emax c1 = Binary.B2R prec emax c0)
        by (rewrite H1R, H0R, He; reflexivity).
      assert (Ht : b64_eqb c1 c0 = true)
        by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact Heq). congruence. }
    apply is_finite_b64_min.
    + exact (b64_div_edge_grid_finite (b64_minus cc b64_half) c0 c1 (2*ncc-1) n0 n1
               Flo Fc0 Fc1 HloHalf H0R H1R ltac:(lia) ltac:(lia) ltac:(lia) Hne).
    + exact (b64_div_edge_grid_finite (b64_plus cc b64_half) c0 c1 (2*ncc+1) n0 n1
               Fhi Fc0 Fc1 HhiHalf H0R H1R ltac:(lia) ltac:(lia) ltac:(lia) Hne).
Qed.

Lemma b64_lb_thi_finite_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.is_finite prec emax
      (b64_lb_thi c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half)) = true.
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc.
  pose proof Hc0 as (Fc0 & n0 & H0R & H0b).
  pose proof Hc1 as (Fc1 & n1 & H1R & H1b).
  pose proof Hcc as (Fcc & ncc & HccR & Hccb).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR Flo].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR Fhi].
  assert (HloHalf : Binary.B2R prec emax (b64_minus cc b64_half) = (IZR (2*ncc-1)%Z / 2)%R)
    by (rewrite HloR, HccR, minus_IZR, mult_IZR; lra).
  assert (HhiHalf : Binary.B2R prec emax (b64_plus cc b64_half) = (IZR (2*ncc+1)%Z / 2)%R)
    by (rewrite HhiR, HccR, plus_IZR, mult_IZR; lra).
  unfold b64_lb_thi.
  destruct (b64_eqb c1 c0) eqn:Heqb.
  - exact is_finite_b64_one.
  - assert (Hne : (n1 <> n0)%Z).
    { intro He. assert (Heq : Binary.B2R prec emax c1 = Binary.B2R prec emax c0)
        by (rewrite H1R, H0R, He; reflexivity).
      assert (Ht : b64_eqb c1 c0 = true)
        by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact Heq). congruence. }
    apply is_finite_b64_max.
    + exact (b64_div_edge_grid_finite (b64_minus cc b64_half) c0 c1 (2*ncc-1) n0 n1
               Flo Fc0 Fc1 HloHalf H0R H1R ltac:(lia) ltac:(lia) ltac:(lia) Hne).
    + exact (b64_div_edge_grid_finite (b64_plus cc b64_half) c0 c1 (2*ncc+1) n0 n1
               Fhi Fc0 Fc1 HhiHalf H0R H1R ltac:(lia) ltac:(lia) ltac:(lia) Hne).
Qed.

(* tlo: the compute lower t-bound = b64_round of the exact spec t-bound. *)
Theorem b64_lb_tlo_eq_round_exact_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.B2R prec emax (b64_lb_tlo c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half))
      = b64_round (lb_tlo (Binary.B2R prec emax c0) (Binary.B2R prec emax c1)
                          (Binary.B2R prec emax cc - / 2) (Binary.B2R prec emax cc + / 2)).
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc.
  pose proof Hc0 as (Fc0 & _).
  pose proof Hc1 as (Fc1 & _).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR _].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR _].
  destruct (b64_eqb c1 c0) eqn:Heqb.
  - assert (HBeq : Binary.B2R prec emax c1 = Binary.B2R prec emax c0)
      by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact Heqb).
    unfold b64_lb_tlo. rewrite Heqb. rewrite B2R_b64_zero.
    unfold lb_tlo.
    destruct (Req_dec_T (Binary.B2R prec emax c1) (Binary.B2R prec emax c0)) as [_ | Hq];
      [ | contradiction ].
    symmetry. apply (round_0 radix2 b64_fexp (round_mode mode_b64)).
  - assert (Hne : Binary.B2R prec emax c1 <> Binary.B2R prec emax c0).
    { intro He. assert (Ht : b64_eqb c1 c0 = true)
        by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact He). congruence. }
    rewrite (b64_lb_tlo_eq_rounded_quotients_grid c0 c1 cc Hc0 Hc1 Hcc Hne).
    rewrite HloR, HhiR, round_Rmin.
    unfold lb_tlo.
    destruct (Req_dec_T (Binary.B2R prec emax c1) (Binary.B2R prec emax c0)) as [Hq | _];
      [ contradiction | reflexivity ].
Qed.

(* thi: the compute upper t-bound = b64_round of the exact spec t-bound. *)
Theorem b64_lb_thi_eq_round_exact_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.B2R prec emax (b64_lb_thi c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half))
      = b64_round (lb_thi (Binary.B2R prec emax c0) (Binary.B2R prec emax c1)
                          (Binary.B2R prec emax cc - / 2) (Binary.B2R prec emax cc + / 2)).
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc.
  pose proof Hc0 as (Fc0 & _).
  pose proof Hc1 as (Fc1 & _).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR _].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR _].
  destruct (b64_eqb c1 c0) eqn:Heqb.
  - assert (HBeq : Binary.B2R prec emax c1 = Binary.B2R prec emax c0)
      by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact Heqb).
    unfold b64_lb_thi. rewrite Heqb. rewrite B2R_b64_one.
    unfold lb_thi.
    destruct (Req_dec_T (Binary.B2R prec emax c1) (Binary.B2R prec emax c0)) as [_ | Hq];
      [ | contradiction ].
    symmetry. apply b64_round_1.
  - assert (Hne : Binary.B2R prec emax c1 <> Binary.B2R prec emax c0).
    { intro He. assert (Ht : b64_eqb c1 c0 = true)
        by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact He). congruence. }
    rewrite (b64_lb_thi_eq_rounded_quotients_grid c0 c1 cc Hc0 Hc1 Hcc Hne).
    rewrite HloR, HhiR, round_Rmax.
    unfold lb_thi.
    destruct (Req_dec_T (Binary.B2R prec emax c1) (Binary.B2R prec emax c0)) as [Hq | _];
      [ contradiction | reflexivity ].
Qed.

(* ----------------------------------------------------------------------------
   SLICE 8: the clipped tmin / tmax are the correctly-rounded exact ones.

   Pushing the rounding through the outer Rmax-0 / Rmin-1 clip and the per-axis
   Rmax/Rmin (all monotone) gives: on the integer grid, the WHOLE compute t-bound
   numerator/denominator pipeline equals `b64_round` of the exact spec value.
   ---------------------------------------------------------------------------- *)

Theorem b64_tmin_eq_round_exact_grid :
  forall x0 x1 cx y0 y1 cy : binary64,
    coord_int_safe x0 -> coord_int_safe x1 -> coord_int_safe cx ->
    coord_int_safe y0 -> coord_int_safe y1 -> coord_int_safe cy ->
    Binary.B2R prec emax
      (b64_max b64_zero
        (b64_max (b64_lb_tlo x0 x1 (b64_minus cx b64_half) (b64_plus cx b64_half))
                 (b64_lb_tlo y0 y1 (b64_minus cy b64_half) (b64_plus cy b64_half))))
      = b64_round
          (Rmax 0 (Rmax (lb_tlo (Binary.B2R prec emax x0) (Binary.B2R prec emax x1)
                               (Binary.B2R prec emax cx - / 2) (Binary.B2R prec emax cx + / 2))
                        (lb_tlo (Binary.B2R prec emax y0) (Binary.B2R prec emax y1)
                               (Binary.B2R prec emax cy - / 2) (Binary.B2R prec emax cy + / 2)))).
Proof.
  intros x0 x1 cx y0 y1 cy Hx0 Hx1 Hcx Hy0 Hy1 Hcy.
  pose proof (b64_lb_tlo_finite_grid x0 x1 cx Hx0 Hx1 Hcx) as HxF.
  pose proof (b64_lb_tlo_finite_grid y0 y1 cy Hy0 Hy1 Hcy) as HyF.
  rewrite (b64_max_B2R _ _ is_finite_b64_zero (is_finite_b64_max _ _ HxF HyF)).
  rewrite B2R_b64_zero.
  rewrite (b64_max_B2R _ _ HxF HyF).
  rewrite (b64_lb_tlo_eq_round_exact_grid x0 x1 cx Hx0 Hx1 Hcx).
  rewrite (b64_lb_tlo_eq_round_exact_grid y0 y1 cy Hy0 Hy1 Hcy).
  rewrite round_Rmax.
  apply round_clip_max0.
Qed.

Theorem b64_tmax_eq_round_exact_grid :
  forall x0 x1 cx y0 y1 cy : binary64,
    coord_int_safe x0 -> coord_int_safe x1 -> coord_int_safe cx ->
    coord_int_safe y0 -> coord_int_safe y1 -> coord_int_safe cy ->
    Binary.B2R prec emax
      (b64_min b64_one
        (b64_min (b64_lb_thi x0 x1 (b64_minus cx b64_half) (b64_plus cx b64_half))
                 (b64_lb_thi y0 y1 (b64_minus cy b64_half) (b64_plus cy b64_half))))
      = b64_round
          (Rmin 1 (Rmin (lb_thi (Binary.B2R prec emax x0) (Binary.B2R prec emax x1)
                               (Binary.B2R prec emax cx - / 2) (Binary.B2R prec emax cx + / 2))
                        (lb_thi (Binary.B2R prec emax y0) (Binary.B2R prec emax y1)
                               (Binary.B2R prec emax cy - / 2) (Binary.B2R prec emax cy + / 2)))).
Proof.
  intros x0 x1 cx y0 y1 cy Hx0 Hx1 Hcx Hy0 Hy1 Hcy.
  pose proof (b64_lb_thi_finite_grid x0 x1 cx Hx0 Hx1 Hcx) as HxF.
  pose proof (b64_lb_thi_finite_grid y0 y1 cy Hy0 Hy1 Hcy) as HyF.
  rewrite (b64_min_B2R _ _ is_finite_b64_one (is_finite_b64_min _ _ HxF HyF)).
  rewrite B2R_b64_one.
  rewrite (b64_min_B2R _ _ HxF HyF).
  rewrite (b64_lb_thi_eq_round_exact_grid x0 x1 cx Hx0 Hx1 Hcx).
  rewrite (b64_lb_thi_eq_round_exact_grid y0 y1 cy Hy0 Hy1 Hcy).
  rewrite round_Rmin.
  apply round_clip_min1.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 9: ON-GRID COMPLETENESS -- the rounded filter never DROPS a pass on
   the grid (the noder-SAFE direction).

   This CLOSES one of C1's two directions.  Since rounding is monotone, the
   exact comparison `tmin <= tmax` (spec touch true) gives the rounded
   comparison `round tmin <= round tmax` (compute touch true) for free; the slab
   guards are bit-identical on the grid (Slice 3).  The remaining OPEN direction
   is on-grid soundness (compute => spec), which needs the lack-of-outward-
   guarantee argument -- see the OBLIGATION note below.
   ---------------------------------------------------------------------------- *)

(* Slab guard equality on the grid: the compute closed-slab guard equals the
   exact-spec guard (Slice 3 + the exact pixel half-edges). *)
Lemma slab_closed_grid_eq :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    b64_lb_inslab_closed c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half)
      = lb_inslab (Binary.B2R prec emax c0) (Binary.B2R prec emax c1)
                  (Binary.B2R prec emax cc - / 2) (Binary.B2R prec emax cc + / 2).
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc.
  pose proof Hc0 as (Fc0 & _).
  pose proof Hc1 as (Fc1 & _).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR Flo].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR Fhi].
  rewrite (slab_guard_bridge c0 c1 _ _ Fc0 Fc1 Flo Fhi).
  rewrite HloR, HhiR. reflexivity.
Qed.

(* Single-touch on-grid completeness. *)
Theorem b64_liang_barsky_touches_complete_on_grid :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    b64_liang_barsky_touches P0 P1 C = true ->
    b64_liang_barsky_touches_compute P0 P1 C = true.
Proof.
  intros P0 P1 C (Hx0 & Hy0) (Hx1 & Hy1) (Hcx & Hcy) Hspec.
  unfold b64_liang_barsky_touches in Hspec.
  apply Bool.andb_true_iff in Hspec. destruct Hspec as [Hslabs Hcmp].
  apply Bool.andb_true_iff in Hslabs. destruct Hslabs as [HslabX HslabY].
  apply Rle_bool_elim in Hcmp.
  unfold b64_liang_barsky_touches_compute.
  apply Bool.andb_true_iff. split.
  - apply Bool.andb_true_iff. split.
    + rewrite (slab_closed_grid_eq (bx P0) (bx P1) (bx C) Hx0 Hx1 Hcx). exact HslabX.
    + rewrite (slab_closed_grid_eq (by_ P0) (by_ P1) (by_ C) Hy0 Hy1 Hcy). exact HslabY.
  - apply b64_le_complete.
    + apply is_finite_b64_max;
        [ exact is_finite_b64_zero
        | apply is_finite_b64_max;
          [ apply b64_lb_tlo_finite_grid; assumption
          | apply b64_lb_tlo_finite_grid; assumption ] ].
    + apply is_finite_b64_min;
        [ exact is_finite_b64_one
        | apply is_finite_b64_min;
          [ apply b64_lb_thi_finite_grid; assumption
          | apply b64_lb_thi_finite_grid; assumption ] ].
    + rewrite (b64_tmin_eq_round_exact_grid (bx P0)(bx P1)(bx C)(by_ P0)(by_ P1)(by_ C)
                 Hx0 Hx1 Hcx Hy0 Hy1 Hcy).
      rewrite (b64_tmax_eq_round_exact_grid (bx P0)(bx P1)(bx C)(by_ P0)(by_ P1)(by_ C)
                 Hx0 Hx1 Hcx Hy0 Hy1 Hcy).
      apply (round_le radix2 b64_fexp (round_mode mode_b64)).
      exact Hcmp.
Qed.

(* Full passes-through predicate, on the grid: never drops a pass.  Lifts the
   single-touch completeness through the Slice-1 collapse (grid points are snap
   fixed points). *)
Corollary b64_passes_through_complete_on_grid :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    b64_passes_through_hot_pixel P0 P1 C = true ->
    b64_passes_through_hot_pixel_compute P0 P1 C = true.
Proof.
  intros P0 P1 C HP0 HP1 HC Hpass.
  rewrite (b64_passes_through_compute_collapses_on_grid P0 P1 C
             (bpoint_int_safe_on_grid P0 HP0) (bpoint_int_safe_on_grid P1 HP1)).
  rewrite (b64_passes_through_collapses_on_grid P0 P1 C
             (bpoint_int_safe_on_grid P0 HP0) (bpoint_int_safe_on_grid P1 HP1)) in Hpass.
  apply b64_liang_barsky_touches_complete_on_grid; assumption.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 10: the conditional grid-exactness headline.

   Slices 3-9 reduce the whole on-grid `compute = spec` question to ONE real-
   number fact: that rounding both exact clip bounds preserves their <= verdict.
   We name that fact and Qed-certify the entire reduction modulo it -- the same
   honest "conditional headline" shape as hobby_theorem_4_1_conditional and
   overlay_ng_correct_conditional.  No Admitted / Axiom / Parameter: the gap is a
   plain Prop hypothesis of the theorem.

   The hypothesis's `<=`-true direction is FREE (monotonicity; that is exactly
   Slice 9's on-grid completeness), so the only genuinely open content is the
   reverse -- the soundness direction.  See the OBLIGATION note for the gap
   analysis and the coordinate-regime in which it provably holds.
   ---------------------------------------------------------------------------- *)

(* The exact spec clip bounds, named so the remaining obligation is crisp. *)
Definition tmin_exact (P0 P1 C : BPoint) : R :=
  Rmax 0 (Rmax (lb_tlo (Binary.B2R prec emax (bx P0)) (Binary.B2R prec emax (bx P1))
                       (Binary.B2R prec emax (bx C) - / 2) (Binary.B2R prec emax (bx C) + / 2))
               (lb_tlo (Binary.B2R prec emax (by_ P0)) (Binary.B2R prec emax (by_ P1))
                       (Binary.B2R prec emax (by_ C) - / 2) (Binary.B2R prec emax (by_ C) + / 2))).

Definition tmax_exact (P0 P1 C : BPoint) : R :=
  Rmin 1 (Rmin (lb_thi (Binary.B2R prec emax (bx P0)) (Binary.B2R prec emax (bx P1))
                       (Binary.B2R prec emax (bx C) - / 2) (Binary.B2R prec emax (bx C) + / 2))
               (lb_thi (Binary.B2R prec emax (by_ P0)) (Binary.B2R prec emax (by_ P1))
                       (Binary.B2R prec emax (by_ C) - / 2) (Binary.B2R prec emax (by_ C) + / 2))).

(* Single-touch grid exactness, conditional on the rounded clip comparison
   reflecting the exact one (the only remaining gap). *)
Theorem b64_liang_barsky_grid_exact_cond :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    (Rle_bool (b64_round (tmin_exact P0 P1 C)) (b64_round (tmax_exact P0 P1 C))
       = Rle_bool (tmin_exact P0 P1 C) (tmax_exact P0 P1 C)) ->
    b64_liang_barsky_touches_compute P0 P1 C = b64_liang_barsky_touches P0 P1 C.
Proof.
  intros P0 P1 C HP0 HP1 HC Hreflect.
  destruct HP0 as (Hx0 & Hy0). destruct HP1 as (Hx1 & Hy1). destruct HC as (Hcx & Hcy).
  unfold b64_liang_barsky_touches_compute, b64_liang_barsky_touches. cbv zeta.
  rewrite (slab_closed_grid_eq (bx P0) (bx P1) (bx C) Hx0 Hx1 Hcx).
  rewrite (slab_closed_grid_eq (by_ P0) (by_ P1) (by_ C) Hy0 Hy1 Hcy).
  rewrite b64_le_eq_Rle_bool.
  2: { apply is_finite_b64_max;
         [ exact is_finite_b64_zero
         | apply is_finite_b64_max; apply b64_lb_tlo_finite_grid; assumption ]. }
  2: { apply is_finite_b64_min;
         [ exact is_finite_b64_one
         | apply is_finite_b64_min; apply b64_lb_thi_finite_grid; assumption ]. }
  rewrite (b64_tmin_eq_round_exact_grid (bx P0) (bx P1) (bx C) (by_ P0) (by_ P1) (by_ C)
             Hx0 Hx1 Hcx Hy0 Hy1 Hcy).
  rewrite (b64_tmax_eq_round_exact_grid (bx P0) (bx P1) (bx C) (by_ P0) (by_ P1) (by_ C)
             Hx0 Hx1 Hcx Hy0 Hy1 Hcy).
  unfold tmin_exact, tmax_exact in Hreflect.
  rewrite Hreflect. reflexivity.
Qed.

(* Full passes-through predicate, conditional grid exactness (via the Slice-1
   collapse: grid points are snap fixed points). *)
Corollary b64_passes_through_grid_exact_cond :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    (Rle_bool (b64_round (tmin_exact P0 P1 C)) (b64_round (tmax_exact P0 P1 C))
       = Rle_bool (tmin_exact P0 P1 C) (tmax_exact P0 P1 C)) ->
    b64_passes_through_hot_pixel_compute P0 P1 C = b64_passes_through_hot_pixel P0 P1 C.
Proof.
  intros P0 P1 C HP0 HP1 HC Hreflect.
  rewrite (b64_passes_through_compute_collapses_on_grid P0 P1 C
             (bpoint_int_safe_on_grid P0 HP0) (bpoint_int_safe_on_grid P1 HP1)).
  rewrite (b64_passes_through_collapses_on_grid P0 P1 C
             (bpoint_int_safe_on_grid P0 HP0) (bpoint_int_safe_on_grid P1 HP1)).
  apply b64_liang_barsky_grid_exact_cond; assumption.
Qed.

(* The soundness direction the user asked for, as a direct corollary: on the
   grid, compute = true => spec = true, conditional on the same reflection. *)
Corollary b64_passes_through_sound_on_grid_cond :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    (Rle_bool (b64_round (tmin_exact P0 P1 C)) (b64_round (tmax_exact P0 P1 C))
       = Rle_bool (tmin_exact P0 P1 C) (tmax_exact P0 P1 C)) ->
    b64_passes_through_hot_pixel_compute P0 P1 C = true ->
    b64_passes_through_hot_pixel P0 P1 C = true.
Proof.
  intros P0 P1 C HP0 HP1 HC Hreflect Hc.
  rewrite <- (b64_passes_through_grid_exact_cond P0 P1 C HP0 HP1 HC Hreflect).
  exact Hc.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 11: the rounding-reflection kernel -- turn Slice 10's rounding
   hypothesis into a pure-reals SEPARATION fact (no Rle_bool-of-rounds left).

   Round-to-nearest moves each value by at most half a ulp
   (`b64_error_le_half_ulp_round`).  So if `round a <= round b` then
   `a - b <= ulp(round a)/2 + ulp(round b)/2`: rounding can flip a strict `b < a`
   only when the two are within that combined half-ulp band.  Hence the rounded
   `<=` REFLECTS the exact `<=` as soon as the exact values are either ordered or
   separated by more than the band.  This is the general tool that discharges
   Slice 10's `Hreflect`; what remains is purely that `tmin_exact`/`tmax_exact`
   are so separated on the grid (the integer-determinant gap), with NO rounding
   in the statement.
   ---------------------------------------------------------------------------- *)

(* Half-ulp transfer: round a <= round b bounds the exact difference. *)
Lemma round_diff_le_of_round_le :
  forall a b : R,
    (b64_round a <= b64_round b)%R ->
    (a - b <= b64_ulp (b64_round a) / 2 + b64_ulp (b64_round b) / 2)%R.
Proof.
  intros a b Hle.
  pose proof (b64_error_le_half_ulp_round a) as Ha.
  pose proof (b64_error_le_half_ulp_round b) as Hb.
  apply Rabs_le_inv in Ha. apply Rabs_le_inv in Hb. lra.
Qed.

(* Reflection under separation: the rounded `<=` matches the exact `<=` whenever
   the exact values are ordered or separated beyond the combined half-ulp band. *)
Lemma round_reflects_le_of_sep :
  forall a b : R,
    (a <= b \/ b64_ulp (b64_round a) / 2 + b64_ulp (b64_round b) / 2 < a - b)%R ->
    ((b64_round a <= b64_round b)%R <-> (a <= b)%R).
Proof.
  intros a b Hsep. split.
  - intro Hr. destruct Hsep as [Hab | Hgap].
    + exact Hab.
    + exfalso. pose proof (round_diff_le_of_round_le a b Hr). lra.
  - intro Hab. apply (round_le radix2 b64_fexp (round_mode mode_b64)). exact Hab.
Qed.

(* The pure-reals separation predicate for the exact clip bounds.  No Rle_bool
   of rounds: just "interval nonempty, or empty beyond the half-ulp band". *)
Definition clip_separated (P0 P1 C : BPoint) : Prop :=
  (tmin_exact P0 P1 C <= tmax_exact P0 P1 C)%R
  \/ (b64_ulp (b64_round (tmin_exact P0 P1 C)) / 2
       + b64_ulp (b64_round (tmax_exact P0 P1 C)) / 2
     < tmin_exact P0 P1 C - tmax_exact P0 P1 C)%R.

(* Separation discharges Slice 10's reflection hypothesis. *)
Lemma clip_separated_reflects :
  forall P0 P1 C : BPoint,
    clip_separated P0 P1 C ->
    Rle_bool (b64_round (tmin_exact P0 P1 C)) (b64_round (tmax_exact P0 P1 C))
      = Rle_bool (tmin_exact P0 P1 C) (tmax_exact P0 P1 C).
Proof.
  intros P0 P1 C Hsep.
  pose proof (round_reflects_le_of_sep (tmin_exact P0 P1 C) (tmax_exact P0 P1 C) Hsep)
    as Hiff.
  destruct (Rle_bool (b64_round (tmin_exact P0 P1 C)) (b64_round (tmax_exact P0 P1 C)))
    eqn:E1;
    destruct (Rle_bool (tmin_exact P0 P1 C) (tmax_exact P0 P1 C)) eqn:E2;
    try reflexivity.
  - exfalso. apply Rle_bool_elim in E1. apply (proj1 Hiff) in E1.
    rewrite (Rle_bool_true _ _ E1) in E2. discriminate.
  - exfalso. apply Rle_bool_elim in E2. apply (proj2 Hiff) in E2.
    rewrite (Rle_bool_true _ _ E2) in E1. discriminate.
Qed.

(* Grid-exactness under separation -- the rounding hypothesis is GONE, replaced
   by the pure-reals `clip_separated` (the integer-determinant gap). *)
Corollary b64_passes_through_grid_exact_sep :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    clip_separated P0 P1 C ->
    b64_passes_through_hot_pixel_compute P0 P1 C = b64_passes_through_hot_pixel P0 P1 C.
Proof.
  intros P0 P1 C HP0 HP1 HC Hsep.
  apply b64_passes_through_grid_exact_cond; try assumption.
  apply clip_separated_reflects; assumption.
Qed.

Corollary b64_passes_through_sound_on_grid_sep :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    clip_separated P0 P1 C ->
    b64_passes_through_hot_pixel_compute P0 P1 C = true ->
    b64_passes_through_hot_pixel P0 P1 C = true.
Proof.
  intros P0 P1 C HP0 HP1 HC Hsep Hc.
  rewrite <- (b64_passes_through_grid_exact_sep P0 P1 C HP0 HP1 HC Hsep).
  exact Hc.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 12: the rational-gap kernel -- the integer-determinant half of
   `clip_separated`.

   Two DISTINCT rationals with integer numerator/denominator differ by at least
   1 / (|d_a| |d_b|): their difference is `(na db - nb da) / (da db)`, an integer
   over `da db`, and a nonzero integer has absolute value >= 1.  On the grid
   every Liang-Barsky t-bound is exactly such a ratio (numerator a doubled
   half-integer, denominator 2 (c1 - c0)), so this is the lower bound on the
   `tmin_e - tmax_e` gap that the `clip_separated` discharge needs -- the
   "when the determinant is nonzero it is >= 1" fact, made precise and
   reusable.  Pairing it with a ulp UPPER bound (the other half) closes
   `clip_separated` in the bounded coordinate regime (see the OBLIGATION note).
   No grid hypotheses here: it is pure integer/rational arithmetic.
   ---------------------------------------------------------------------------- *)

(* A nonzero integer has |.| >= 1, as a real. *)
Lemma IZR_abs_ge_1 :
  forall n : Z, (n <> 0)%Z -> (1 <= Rabs (IZR n))%R.
Proof.
  intros n Hn. rewrite <- abs_IZR.
  replace 1%R with (IZR 1) by reflexivity.
  apply IZR_le. lia.
Qed.

Lemma rational_gap :
  forall (na da nb db : Z),
    (da <> 0)%Z -> (db <> 0)%Z ->
    (na * db <> nb * da)%Z ->
    (1 / (Rabs (IZR da) * Rabs (IZR db))
       <= Rabs (IZR na / IZR da - IZR nb / IZR db))%R.
Proof.
  intros na da nb db Hda Hdb Hne.
  assert (Hda_r : IZR da <> 0%R) by (apply IZR_neq; exact Hda).
  assert (Hdb_r : IZR db <> 0%R) by (apply IZR_neq; exact Hdb).
  assert (Hden_pos : (0 < Rabs (IZR da) * Rabs (IZR db))%R)
    by (apply Rmult_lt_0_compat; apply Rabs_pos_lt; assumption).
  (* combine into a single fraction over (da*db) *)
  assert (Heq : (IZR na / IZR da - IZR nb / IZR db)%R
                = (IZR (na * db - nb * da) / (IZR da * IZR db))%R)
    by (rewrite minus_IZR, !mult_IZR; field; split; assumption).
  rewrite Heq. unfold Rdiv.
  rewrite Rabs_mult, Rabs_inv, Rabs_mult.
  (* both sides are (_) * / (|da|*|db|); compare numerators 1 <= |num| *)
  apply Rmult_le_compat_r.
  - apply Rlt_le, Rinv_0_lt_compat. exact Hden_pos.
  - apply IZR_abs_ge_1. lia.
Qed.

(* A single grid Liang-Barsky quotient `(edge - c0)/(c1 - c0)`, with edge a
   half-integer `IZR m / 2` and c0, c1 integers, IS the integer ratio
   `IZR (m - 2 n0) / IZR (2 (n1 - n0))`.  This is the shape `rational_gap`
   consumes: two such quotients (the binding pair behind `tmin_e > tmax_e`)
   differ by at least `1 / (|2(x1-x0)| * |2(y1-y0)|)` when distinct. *)
Lemma grid_quotient_ratio :
  forall (c0 c1 e : binary64) (m n0 n1 : Z),
    Binary.B2R prec emax e = (IZR m / 2)%R ->
    Binary.B2R prec emax c0 = IZR n0 ->
    Binary.B2R prec emax c1 = IZR n1 ->
    (n1 <> n0)%Z ->
    ((Binary.B2R prec emax e - Binary.B2R prec emax c0)
       / (Binary.B2R prec emax c1 - Binary.B2R prec emax c0))%R
      = (IZR (m - 2 * n0) / IZR (2 * (n1 - n0)))%R.
Proof.
  intros c0 c1 e m n0 n1 HeR H0R H1R Hne.
  rewrite HeR, H0R, H1R.
  rewrite minus_IZR, !mult_IZR, minus_IZR.
  assert (Hd : (IZR n1 - IZR n0)%R <> 0%R).
  { apply Rminus_eq_contra. intro He. apply Hne. apply eq_IZR. exact He. }
  field. exact Hd.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 13: the ulp UPPER bound -- the other half of `clip_separated`.

   `round x` never exceeds the binade of x, so its ulp is bounded by the binade:
   `|x| <= 2^e  =>  ulp(round x) <= 2^(e+1-prec)`.  Pairing this with Slice 12's
   gap lower bound gives `clip_separated` in the bounded coordinate regime: at
   the tight boundary the clip forces both bounds into [0,1] (ulp <= 2^-52),
   while the determinant keeps the gap >= 2^-(2K+2); for |n| <= 2^23 the gap
   wins.  Reusable; tied to Flocq's `ulp_le` (monotonicity) + `ulp_bpow`.
   ---------------------------------------------------------------------------- *)

Lemma b64_ulp_round_le_bpow :
  forall (x : R) (e : Z),
    (3 - emax <= e + 1)%Z ->
    (Rabs x <= bpow radix2 e)%R ->
    (b64_ulp (b64_round x) <= bpow radix2 (e + 1 - prec))%R.
Proof.
  intros x e He Hx.
  pose proof (b64_round_abs_le_bpow x e He Hx) as Hrx.
  apply (Rle_trans _ (b64_ulp (bpow radix2 e))).
  - apply (ulp_le radix2 b64_fexp).
    rewrite (Rabs_pos_eq (bpow radix2 e)) by (apply Rlt_le, bpow_gt_0).
    exact Hrx.
  - rewrite (ulp_bpow radix2 b64_fexp e).
    apply Req_le. f_equal.
    unfold b64_fexp, SpecFloat.fexp.
    apply Z.max_l. unfold SpecFloat.emin, emax, prec in *. lia.
Qed.

(* The [0,1] instance the clip boundary needs: ulp(round x) <= 2^(1-prec). *)
Lemma b64_ulp_round_le_unit :
  forall x : R, (Rabs x <= 1)%R ->
    (b64_ulp (b64_round x) <= bpow radix2 (1 - prec))%R.
Proof.
  intros x Hx.
  apply (b64_ulp_round_le_bpow x 0).
  - unfold emax. lia.
  - replace (bpow radix2 0) with 1%R by (simpl; lra). exact Hx.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 14: the three bricks combine -- the determinant gap STRICTLY EXCEEDS
   the rounding band for two distinct bounded grid ratios.

   For u = na/da, v = nb/db two DISTINCT ratios that are (i) in [-1,1] and
   (ii) have denominators |da|,|db| <= 2^24 (the tight-regime t-bound shape:
   denominator 2(c1-c0) with |c1-c0| <= 2^24, i.e. |n| <= 2^23):

       1/2 ulp(round u) + 1/2 ulp(round v)  <  |u - v|.

   Proof = Slice 13 (ulp band <= 2^-52, since |u|,|v| <= 1) + Slice 12 (gap
   >= 1/(|da||db|) >= 2^-48) + 2^-52 < 2^-48.  This is EXACTLY the right disjunct
   of `clip_separated` for the binding (tmin_e, tmax_e) pair -- the quantitative
   heart of unconditional on-grid soundness in the tight regime.  What remains
   to assemble `clip_separated` itself is purely structural: exhibit tmin_e /
   tmax_e as such bounded ratios (the Rmax/Rmin selects one element each;
   grid_quotient_ratio gives the ratio form; the clip gives the [-1,1] bound in
   the binding case).
   ---------------------------------------------------------------------------- *)
Lemma grid_ratio_gap_exceeds_ulp_band :
  forall (u v : R) (na da nb db : Z),
    u = (IZR na / IZR da)%R -> v = (IZR nb / IZR db)%R ->
    (da <> 0)%Z -> (db <> 0)%Z ->
    (Z.abs da <= 2 ^ 24)%Z -> (Z.abs db <= 2 ^ 24)%Z ->
    (Rabs u <= 1)%R -> (Rabs v <= 1)%R ->
    u <> v ->
    (b64_ulp (b64_round u) / 2 + b64_ulp (b64_round v) / 2 < Rabs (u - v))%R.
Proof.
  intros u v na da nb db Hu Hv Hda Hdb HdaB HdbB Hu1 Hv1 Hne.
  (* (A) the rounding band is <= bpow (1 - prec) = 2^-52 *)
  pose proof (b64_ulp_round_le_unit u Hu1) as Hulpu.
  pose proof (b64_ulp_round_le_unit v Hv1) as Hulpv.
  assert (Hband : (b64_ulp (b64_round u) / 2 + b64_ulp (b64_round v) / 2
                    <= bpow radix2 (1 - prec))%R) by lra.
  (* (B) distinct ratios cross-multiply distinctly *)
  assert (Hcross : (na * db <> nb * da)%Z).
  { intro Hc. apply Hne. rewrite Hu, Hv.
    field_simplify_eq; [ | split; apply IZR_neq; assumption ].
    rewrite <- !mult_IZR. f_equal. lia. }
  pose proof (rational_gap na da nb db Hda Hdb Hcross) as Hgap.
  rewrite <- Hu, <- Hv in Hgap.
  (* (C) the gap is >= bpow (-48): denominators bounded by bpow 24 *)
  assert (HdaR : (Rabs (IZR da) <= bpow radix2 24)%R).
  { rewrite <- abs_IZR, <- (IZR_Zpower radix2 24) by lia. apply IZR_le. exact HdaB. }
  assert (HdbR : (Rabs (IZR db) <= bpow radix2 24)%R).
  { rewrite <- abs_IZR, <- (IZR_Zpower radix2 24) by lia. apply IZR_le. exact HdbB. }
  assert (Hdapos : (0 < Rabs (IZR da))%R) by (apply Rabs_pos_lt, IZR_neq; assumption).
  assert (Hdbpos : (0 < Rabs (IZR db))%R) by (apply Rabs_pos_lt, IZR_neq; assumption).
  assert (Hprodpos : (0 < Rabs (IZR da) * Rabs (IZR db))%R)
    by (apply Rmult_lt_0_compat; assumption).
  assert (Hprod : (Rabs (IZR da) * Rabs (IZR db) <= bpow radix2 48)%R).
  { replace (bpow radix2 48) with (bpow radix2 24 * bpow radix2 24)%R
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (Hgap48 : (/ bpow radix2 48 <= Rabs (u - v))%R).
  { apply (Rle_trans _ (1 / (Rabs (IZR da) * Rabs (IZR db)))%R); [ | exact Hgap ].
    unfold Rdiv. rewrite Rmult_1_l.
    apply Rinv_le_contravar; [ exact Hprodpos | exact Hprod ]. }
  (* (D) chain: band <= 2^-52 < 2^-48 = / bpow 48 <= gap *)
  assert (Hlt : (bpow radix2 (1 - prec) < / bpow radix2 48)%R).
  { apply (Rmult_lt_reg_r (bpow radix2 48)); [ apply bpow_gt_0 | ].
    rewrite Rinv_l by (apply Rgt_not_eq, bpow_gt_0).
    rewrite <- bpow_plus.
    replace (1 - prec + 48)%Z with (-4)%Z by (unfold prec; lia).
    replace 1%R with (bpow radix2 0) by reflexivity.
    apply bpow_lt. lia. }
  lra.
Qed.

(* ----------------------------------------------------------------------------
   REMAINING OBLIGATION (the hard core -- NOT an axiom).

   With Slices 10-11, the ENTIRE on-grid `compute = spec` equivalence (single-
   touch and full predicate) is Qed-certified modulo ONE PURE-REALS obligation,
   `clip_separated P0 P1 C` (Slice 11) -- no rounding/Rle_bool left in it:

       clip_separated :  tmin_e <= tmax_e
                          \/  /2 ulp(round tmin_e) + /2 ulp(round tmax_e)
                                < tmin_e - tmax_e

   where tmin_e = tmin_exact, tmax_e = tmax_exact are the exact spec clip bounds.
   Slice 11's `round_reflects_le_of_sep` turns this into the Slice-10 hypothesis,
   so `clip_separated` is the only gap left in C1; everything else is discharged.

   What is already free vs. what is open:
     - `=true` (completeness, spec=>compute): FREE by monotonicity of round
       (tmin_e <= tmax_e  =>  round tmin_e <= round tmax_e).  This is Slice 9,
       and it is the reason the `<=`-true half of Hreflect always holds.
     - `=false` (soundness, compute=>spec): the OPEN half.  It needs
       tmin_e > tmax_e  =>  round tmin_e > round tmax_e, i.e. rounding must not
       collapse a strictly-empty clip interval to a non-empty one.

   Gap analysis -- WHAT IS NOW PROVEN vs. what remains.  On the grid every
   t-bound is the integer ratio `IZR (m - 2 n0) / IZR (2 (n1 - n0))`
   (`grid_quotient_ratio`, Slice 12), and any two DISTINCT such ratios differ by
   >= 1 / (|d_a| |d_b|) (`rational_gap`, Slice 12) -- so the binding
   `tmin_e - tmax_e` gap, when nonzero, is >= 1 / (|2(x1-x0)| |2(y1-y0)|).  This
   is the GAP (lower-bound) half of `clip_separated`, Qed.

   The gap-vs-band INEQUALITY is now PROVEN combined (Slice 14,
   `grid_ratio_gap_exceeds_ulp_band`): for two distinct ratios u, v in [-1,1]
   with denominators <= 2^24,
       /2 ulp(round u) + /2 ulp(round v) <= 2^-52 < 2^-48 <= |u - v|,
   i.e. EXACTLY `clip_separated`'s right disjunct for the binding pair.

   ONE purely-STRUCTURAL step remains to assemble `clip_separated`:
     reduce `tmin_e - tmax_e` to a SINGLE binding pair (max of {0,tlo_x,tlo_y}
     minus min of {1,thi_x,thi_y}) -- each `Rmax`/`Rmin` SELECTS one argument
     (`Rmax x y = x \/ = y`), so tmin_e, tmax_e are each one of
     {0,1,tlo_x,tlo_y,thi_x,thi_y}, an integer ratio (`grid_quotient_ratio`,
     with 0 = 0/1, 1 = 1/1) bounded in [-1,1] in the binding case; then apply
     Slice 14 (constant cases 0/1 and axis-degenerate branches folded in).  No
     more analytic content -- the determinant-beats-rounding inequality is done.

   FINDING (recorded): at the full coord_int_safe width |n| <= 2^25 the bound is
   *borderline* (|d_a d_b| can reach ~2^52, gap ~2^-54 < ulp), so a full-width
   unconditional close is NOT a pure forward-error argument -- it needs the exact
   integer-determinant decision (no rounding in the comparison) or a tightened
   coordinate regime.  Recommended next step: assemble (a)+(b) with Slice 12 into
   an UNCONDITIONAL `b64_..._sound_on_grid` for |n| <= 2^23.
   ---------------------------------------------------------------------------- *)
