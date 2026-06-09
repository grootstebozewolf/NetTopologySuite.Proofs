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

   After these slices the remaining obligation is isolated to ONE residual: that
   the round-to-nearest errors in the per-quotient `round` never flip the
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
   REMAINING OBLIGATION (the hard, multi-session core -- NOT an axiom).

   After Slices 1-6 the rounded compute filter and the exact spec differ, ON THE
   GRID, by EXACTLY one thing: a `b64_round` wrapped around each individual
   exact quotient `(lo - c0)/(c1 - c0)` (Slice 6).  Everything else is now
   machine-checked equal: the snap-consistency conjunct (Slice 1), the slab
   guard (Slice 3), the operands (Slice 4), and the max/min/clip composition
   (Slice 5).

     Open goal (single-touch grid exactness), strongly evidenced (0/5e6):
       forall P0 P1 C, <P0,P1,C on the integer grid> ->
         b64_liang_barsky_touches_compute P0 P1 C
           = b64_liang_barsky_touches P0 P1 C.

   reduces (via Slices 3-6) to: the composite clip comparison
       Rle_bool (Rmax 0 (Rmax (round tlo_x) (round tlo_y)))
                (Rmin 1 (Rmin (round thi_x) (round thi_y)))
   equals the same comparison WITHOUT the `round`s.

   Why it is still hard: round-to-nearest gives no outward guarantee, so the
   rounded comparison is not definitionally the exact one.

   Strategy for the core (next session): rewrite the exact comparison
   `lb_tlo <= lb_thi` etc. by CROSS-MULTIPLYING through the (exact integer)
   denominators, turning each pairwise t-bound comparison into the SIGN of an
   integer determinant -- a decision that does not divide and is exactly
   representable in binary64 on the grid (cf. Orient_b64_exact.v's dyadic
   exactness, b64_minus_int_exact / b64_mult_int_exact).  Then show the rounded
   `b64_div`-based comparison (now isolated by Slice 6 to the per-quotient
   `round`) has the same outcome because the integer determinant is
   nonzero-with-gap >= 1 except in the exactly-equal case the rounding also
   preserves.
   ---------------------------------------------------------------------------- *)
