(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThroughHalfopen_b64_compute_unsound
   ----------------------------------------------------------------------------
   MACHINE-CHECKED COUNTEREXAMPLE (half-open mode): the rounded computational
   HALF-OPEN hot-pixel filter is NOT sound against the exact-real half-open
   spec -- the companion to PassesThrough_b64_compute_unsound.v for the
   oracle's `PASSES_THROUGH_HALFOPEN` mode.

   `Theorem b64_passes_through_halfopen_compute_unsound`:
     exists P0 P1 C,
       b64_passes_through_hot_pixel_halfopen_compute P0 P1 C = true /\
       b64_passes_through_hot_pixel_halfopen          P0 P1 C = false.

   Witness = the closed-mode witness with its x-coordinates negated (an exact
   binary64 sign flip).  Negating x reflects the near-tangency from the
   bottom-RIGHT corner (where the closed witness's segment exits, failing the
   half-open strict midpoint test `xmid < xhi`) to the bottom-LEFT, so BOTH
   strict midpoint checks pass and the rounded half-open filter accepts -- yet
   the exact geometry still misses by the SAME sub-ulp gap
   (tlo_x = 2^49/(2^49+1) > thi_y = (2^49-1)/2^49).

   `compute = true` is decided by vm_compute.  For `spec = false` we reuse the
   corpus lemma `b64_liang_barsky_touches_halfopen_implies_closed`: it suffices
   to show the *closed* exact spec is false on this witness (the same
   empty-t-interval argument as the closed mode), and the half-open spec
   falseness follows by contraposition.

   Generic scale/normalisation helpers are imported from
   PassesThrough_b64_compute_unsound; only the x-reflected coordinate values
   and a sign-agnostic fraction comparison are new here.
   ========================================================================== *)

From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import PassesThroughHalfopen_b64.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute_unsound.
Require Import Reals.
Require Import Lia.
Require Import Lra.
Local Open Scope R_scope.

(* Witness: lane-1 witness with x negated (exact sign flip); y and C reused. *)
Definition vP0x : binary64 := Binary.B754_finite prec emax true 4503599627370496 (-52) eq_refl. (* -1 *)
Definition vP1x : binary64 := Binary.B754_finite prec emax true 9007199254740976 (-54) eq_refl.
Definition vP0 : BPoint := mkBP vP0x wP0y.
Definition vP1 : BPoint := mkBP vP1x wP1y.
Definition vC  : BPoint := wC.

Lemma compute_ho_true :
  b64_passes_through_hot_pixel_halfopen_compute vP0 vP1 vC = true.
Proof. vm_compute. reflexivity. Qed.

(* Negated x-coordinates on the common 2^(-54) scale. *)
Lemma val_vP0x : Binary.B2R prec emax vP0x = IZR (-18014398509481984) * C54.
Proof. unfold vP0x. rewrite Bfin_val. cbn [cond_Zopp]. rewrite norm54.
  replace (-52 + 54)%Z with 2%Z by ring. rewrite bpow2_2, <- mult_IZR. reflexivity. Qed.
Lemma val_vP1x : Binary.B2R prec emax vP1x = IZR (-9007199254740976) * C54.
Proof. unfold vP1x. rewrite Bfin_val. cbn [cond_Zopp]. rewrite norm54.
  replace (-54 + 54)%Z with 0%Z by ring. rewrite bpow2_0, <- mult_IZR. reflexivity. Qed.

(* Sign-agnostic fraction comparison: a/b < c/d for any nonzero b,d reduces to
   a single signed Z inequality (b,d here have OPPOSITE signs). *)
Lemma izr_div_neg : forall n m : Z, (n * m < 0)%Z -> IZR n / IZR m < 0.
Proof.
  intros n m H.
  assert (Hm : (m <> 0)%Z) by (intro Hx; subst; rewrite Z.mul_0_r in H; lia).
  assert (Hm0 : IZR m <> 0) by (apply not_0_IZR; exact Hm).
  apply Rmult_lt_reg_r with (IZR m * IZR m).
  { rewrite <- mult_IZR. apply IZR_lt. nia. }
  rewrite Rmult_0_l. unfold Rdiv. rewrite Rmult_assoc.
  replace (/ IZR m * (IZR m * IZR m)) with (IZR m) by (field; exact Hm0).
  rewrite <- mult_IZR. replace 0 with (IZR 0) by reflexivity. apply IZR_lt. exact H.
Qed.

Lemma frac_lt_gen : forall a b c d : Z, (b <> 0)%Z -> (d <> 0)%Z ->
  ((a * d - c * b) * (b * d) < 0)%Z -> IZR a / IZR b < IZR c / IZR d.
Proof.
  intros a b c d Hb Hd H.
  assert (Hb0 : IZR b <> 0) by (apply not_0_IZR; exact Hb).
  assert (Hd0 : IZR d <> 0) by (apply not_0_IZR; exact Hd).
  apply Rminus_lt.
  replace (IZR a / IZR b - IZR c / IZR d) with (IZR (a * d - c * b) / IZR (b * d)).
  2:{ rewrite minus_IZR, !mult_IZR. field. split; assumption. }
  apply izr_div_neg. exact H.
Qed.

(* Four exact t-bounds for the x-reflected witness (x-bounds negated, y reused
   from the closed-mode file). *)
Lemma xa_val_v :
  (Binary.B2R prec emax (bx vC) - / 2 - Binary.B2R prec emax (bx vP0))
    / (Binary.B2R prec emax (bx vP1) - Binary.B2R prec emax (bx vP0))
  = IZR (0 - 9007199254740992 - -18014398509481984)
    / IZR (-9007199254740976 - -18014398509481984).
Proof.
  change (bx vP0) with vP0x. change (bx vP1) with vP1x. change (bx vC) with wCx.
  rewrite val_vP0x, val_vP1x, val_Cx, half_val, three_term, two_term.
  rewrite cancelC by (apply not_0_IZR; vm_compute; discriminate). reflexivity.
Qed.
Lemma xb_val_v :
  (Binary.B2R prec emax (bx vC) + / 2 - Binary.B2R prec emax (bx vP0))
    / (Binary.B2R prec emax (bx vP1) - Binary.B2R prec emax (bx vP0))
  = IZR (0 + 9007199254740992 - -18014398509481984)
    / IZR (-9007199254740976 - -18014398509481984).
Proof.
  change (bx vP0) with vP0x. change (bx vP1) with vP1x. change (bx vC) with wCx.
  rewrite val_vP0x, val_vP1x, val_Cx, half_val, plusminus_term, two_term.
  rewrite cancelC by (apply not_0_IZR; vm_compute; discriminate). reflexivity.
Qed.

Lemma x1_ne_x0_v : Binary.B2R prec emax (bx vP1) <> Binary.B2R prec emax (bx vP0).
Proof.
  change (bx vP0) with vP0x. change (bx vP1) with vP1x.
  rewrite val_vP0x, val_vP1x. assert (HC := C54_pos). nra.
Qed.

(* thi_y < tlo_x: the exact sub-ulp miss (y reuses the closed-mode bounds). *)
Lemma key_lt_v :
  lb_thi (Binary.B2R prec emax (by_ vP0)) (Binary.B2R prec emax (by_ vP1))
         (Binary.B2R prec emax (by_ vC) - / 2) (Binary.B2R prec emax (by_ vC) + / 2)
  < lb_tlo (Binary.B2R prec emax (bx vP0)) (Binary.B2R prec emax (bx vP1))
           (Binary.B2R prec emax (bx vC) - / 2) (Binary.B2R prec emax (bx vC) + / 2).
Proof.
  change (by_ vP0) with (by_ wP0). change (by_ vP1) with (by_ wP1).
  change (by_ vC) with (by_ wC).
  unfold lb_thi, lb_tlo.
  destruct (Req_dec_T (Binary.B2R prec emax (bx vP1)) (Binary.B2R prec emax (bx vP0)))
    as [Ex|Ex]; [ exfalso; apply x1_ne_x0_v; exact Ex | ].
  destruct (Req_dec_T (Binary.B2R prec emax (by_ wP1)) (Binary.B2R prec emax (by_ wP0)))
    as [Ey|Ey]; [ exfalso; apply y1_ne_y0; exact Ey | ].
  rewrite xa_val_v, xb_val_v, ya_val, yb_val.
  apply Rmax_lub_lt.
  - apply Rmin_glb_lt; apply frac_lt_gen; lia.
  - apply Rmin_glb_lt; apply frac_lt_gen; lia.
Qed.

(* The closed exact spec is false on this witness (empty clipped t-interval). *)
Lemma touch_closed_false_v : b64_liang_barsky_touches vP0 vP1 vC = false.
Proof.
  unfold b64_liang_barsky_touches.
  apply Bool.andb_false_intro2. apply Rle_bool_false.
  eapply Rle_lt_trans; [ apply Rmin_r | ].
  eapply Rlt_le_trans; [ | apply Rmax_r ].
  eapply Rle_lt_trans; [ apply Rmin_r | ].
  eapply Rlt_le_trans; [ | apply Rmax_l ].
  apply key_lt_v.
Qed.

(* Hence the half-open exact spec is false (half-open => closed, contrapositive). *)
Lemma touch_ho_false_v : b64_liang_barsky_touches_halfopen vP0 vP1 vC = false.
Proof.
  destruct (b64_liang_barsky_touches_halfopen vP0 vP1 vC) eqn:E; [ | reflexivity ].
  apply b64_liang_barsky_touches_halfopen_implies_closed in E.
  rewrite touch_closed_false_v in E. discriminate.
Qed.

Theorem b64_passes_through_halfopen_compute_unsound :
  exists P0 P1 C : BPoint,
    b64_passes_through_hot_pixel_halfopen_compute P0 P1 C = true /\
    b64_passes_through_hot_pixel_halfopen          P0 P1 C = false.
Proof.
  exists vP0, vP1, vC. split.
  - exact compute_ho_true.
  - unfold b64_passes_through_hot_pixel_halfopen. rewrite touch_ho_false_v. reflexivity.
Qed.

Print Assumptions b64_passes_through_halfopen_compute_unsound.
