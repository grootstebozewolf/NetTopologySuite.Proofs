(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThroughHalfopen_b64_compute_incomplete
   ----------------------------------------------------------------------------
   MACHINE-CHECKED COUNTEREXAMPLE: the rounded HALF-OPEN computational hot-pixel
   filter is NOT COMPLETE -- it DROPS a real pass (the noder-UNSAFE direction).

   Promotes the adversarial-test finding (oracle/gen_adversarial_tests.sh §D;
   docs/oracle-soundness-finding.md "Half-open compute filter is NOT complete")
   to a Qed theorem:

     exists P0 P1 C,
       b64_passes_through_hot_pixel_halfopen          P0 P1 C = true  /\  (* exact R-spec *)
       b64_passes_through_hot_pixel_halfopen_compute  P0 P1 C = false.    (* rounded compute *)

   Witness: P0 = (-1, 1/2), P1 = (1, 1/2 - 2^-54), C = (0,0).  The segment
   grazes the OPEN top edge y = 1/2 of the unit pixel.  Its clipped-interval
   midpoint (t = 1/2) is the point (0, 1/2 - 2^-55), strictly inside the
   half-open pixel, and the unit-grid snap (-1,0)->(1,0) passes through the
   centre -- so the exact half-open spec is TRUE.  The rounded compute filter
   evaluates the strict-upper midpoint check with b64 rounding, which rounds
   the midpoint's y UP onto the excluded boundary 1/2, and REJECTS -- dropping
   the pass.  (Contrast PassesThrough_b64_compute_unsound.v: the CLOSED filter
   only OVER-accepts.)

   `compute = false` by vm_compute.  `spec = true` is discharged by the corpus
   completeness lemma `b64_liang_barsky_touches_halfopen_complete` from the
   geometric t = 1/2 witness -- no t-bound arithmetic.
   ========================================================================== *)

From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs Require Import Distance HotPixel.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import PassesThroughHalfopen_b64.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute_unsound.  (* Bfin_val *)
Require Import Reals.
Require Import Lia.
Require Import Lra.
Local Open Scope R_scope.

Definition uP0x : binary64 := Binary.B754_finite prec emax true  4503599627370496%positive (-52)%Z eq_refl. (* -1 *)
Definition uP0y : binary64 := Binary.B754_finite prec emax false 4503599627370496%positive (-53)%Z eq_refl. (* 1/2 *)
Definition uP1x : binary64 := Binary.B754_finite prec emax false 4503599627370496%positive (-52)%Z eq_refl. (* 1 *)
Definition uP1y : binary64 := Binary.B754_finite prec emax false 9007199254740991%positive (-54)%Z eq_refl. (* 1/2 - 2^-54 *)
Definition uC  : BPoint := mkBP (Binary.B754_zero prec emax false) (Binary.B754_zero prec emax false).
Definition uP0 : BPoint := mkBP uP0x uP0y.
Definition uP1 : BPoint := mkBP uP1x uP1y.

Lemma compute_false :
  b64_passes_through_hot_pixel_halfopen_compute uP0 uP1 uC = false.
Proof. vm_compute. reflexivity. Qed.

(* Coordinate values as clean reals (bpow-only; no Rinv reasoning). *)
Lemma val_uP0x : Binary.B2R prec emax uP0x = -1.
Proof.
  unfold uP0x. rewrite Bfin_val. cbn [cond_Zopp]. rewrite opp_IZR.
  assert (H1 : bpow radix2 52 * bpow radix2 (-52) = 1)
    by (rewrite <- bpow_plus; reflexivity).
  change (IZR 4503599627370496) with (bpow radix2 52).
  rewrite Ropp_mult_distr_l_reverse, H1. reflexivity.
Qed.
Lemma val_uP1x : Binary.B2R prec emax uP1x = 1.
Proof.
  unfold uP1x. rewrite Bfin_val. cbn [cond_Zopp].
  change (IZR (Z.pos 4503599627370496)) with (bpow radix2 52).
  rewrite <- bpow_plus. reflexivity.
Qed.
Lemma val_uP0y : Binary.B2R prec emax uP0y = / 2.
Proof.
  unfold uP0y. rewrite Bfin_val. cbn [cond_Zopp].
  change (IZR (Z.pos 4503599627370496)) with (bpow radix2 52).
  rewrite <- bpow_plus. reflexivity.
Qed.
Lemma val_uP1y : Binary.B2R prec emax uP1y = / 2 - bpow radix2 (-54).
Proof.
  unfold uP1y. rewrite Bfin_val. cbn [cond_Zopp].
  replace (Z.pos 9007199254740991) with (9007199254740992 - 1)%Z by lia.
  rewrite minus_IZR.
  change (IZR 9007199254740992) with (bpow radix2 53).
  change (IZR 1) with 1.
  rewrite Rmult_minus_distr_r, <- bpow_plus, Rmult_1_l. reflexivity.
Qed.
Lemma val_uCx : Binary.B2R prec emax (bx uC) = 0.  Proof. reflexivity. Qed.
Lemma val_uCy : Binary.B2R prec emax (by_ uC) = 0. Proof. reflexivity. Qed.

(* bpow(-54) bounds for the membership arithmetic. *)
Lemma b54_pos : 0 < bpow radix2 (-54).  Proof. apply bpow_gt_0. Qed.
Lemma b54_le1 : bpow radix2 (-54) <= 1.
Proof. replace 1 with (bpow radix2 0) by reflexivity. apply bpow_le. lia. Qed.

(* Snapping an integer coordinate is the identity at the value level. *)
Lemma snap_round_coord_IZR : forall z : Z, snap_round_coord (IZR z) 1 = IZR z.
Proof.
  intros z. unfold snap_round_coord. rewrite Rmult_1_r, Rdiv_1_r, round_FIX0_IZR.
  f_equal. unfold round_mode. apply Znearest_imp.
  replace (IZR z - IZR z) with 0 by ring. rewrite Rabs_R0. lra.
Qed.

(* y-coordinates (1/2 and 1/2 - 2^-54) both snap to +0; x to -1 / 1. *)
Lemma snap_uP0y : b64_snap_coord uP0y = Binary.B754_zero prec emax false.
Proof. vm_compute. reflexivity. Qed.
Lemma snap_uP1y : b64_snap_coord uP1y = Binary.B754_zero prec emax false.
Proof. vm_compute. reflexivity. Qed.
Lemma snap_x0 : Binary.B2R prec emax (b64_snap_coord uP0x) = -1.
Proof.
  rewrite b64_snap_coord_B2R, val_uP0x.
  replace (-1) with (IZR (-1)) at 1 by reflexivity.
  rewrite snap_round_coord_IZR. reflexivity.
Qed.
Lemma snap_x1 : Binary.B2R prec emax (b64_snap_coord uP1x) = 1.
Proof.
  rewrite b64_snap_coord_B2R, val_uP1x.
  replace 1 with (IZR 1) at 1 by reflexivity.
  rewrite snap_round_coord_IZR. reflexivity.
Qed.
Lemma snap_y0 : Binary.B2R prec emax (b64_snap_coord uP0y) = 0.
Proof. rewrite snap_uP0y. reflexivity. Qed.
Lemma snap_y1 : Binary.B2R prec emax (b64_snap_coord uP1y) = 0.
Proof. rewrite snap_uP1y. reflexivity. Qed.

(* The exact half-open R-spec accepts (the dropped pass). *)
Lemma spec_true :
  b64_passes_through_hot_pixel_halfopen uP0 uP1 uC = true.
Proof.
  assert (Hp := b54_pos). assert (Hl := b54_le1).
  unfold b64_passes_through_hot_pixel_halfopen. apply Bool.andb_true_iff. split.
  - (* original segment: midpoint (0, 1/2 - 2^-55) strictly inside *)
    apply b64_liang_barsky_touches_halfopen_complete.
    unfold b64_segment_touches_hot_pixel_spec, segment_touches_hot_pixel.
    exists (/ 2). split; [ lra | ].
    unfold in_hot_pixel, segment_point, BP2P, px, py, hot_pixel_radius, uP0, uP1.
    cbn [bx by_].
    rewrite val_uP0x, val_uP0y, val_uP1x, val_uP1y, val_uCx, val_uCy.
    repeat split; lra.
  - (* snapped segment (-1,0)->(1,0): midpoint (0,0) strictly inside *)
    apply b64_liang_barsky_touches_halfopen_complete.
    unfold b64_segment_touches_hot_pixel_spec, segment_touches_hot_pixel.
    exists (/ 2). split; [ lra | ].
    unfold in_hot_pixel, segment_point, BP2P, px, py, hot_pixel_radius, uP0, uP1, b64_snap.
    cbn [bx by_].
    rewrite snap_x0, snap_y0, snap_x1, snap_y1, val_uCx, val_uCy.
    repeat split; lra.
Qed.

Theorem b64_passes_through_halfopen_compute_incomplete :
  exists P0 P1 C : BPoint,
    b64_passes_through_hot_pixel_halfopen          P0 P1 C = true /\
    b64_passes_through_hot_pixel_halfopen_compute  P0 P1 C = false.
Proof.
  exists uP0, uP1, uC. split; [ exact spec_true | exact compute_false ].
Qed.

Print Assumptions b64_passes_through_halfopen_compute_incomplete.
