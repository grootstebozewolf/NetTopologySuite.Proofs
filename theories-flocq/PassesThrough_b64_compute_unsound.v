(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_compute_unsound
   ----------------------------------------------------------------------------
   MACHINE-CHECKED COUNTEREXAMPLE: the rounded computational hot-pixel
   passes-through filter is NOT sound against the exact-real spec.

   `docs/oracle-soundness-finding.md` established, by 8M-case adversarial
   differential testing, that the `compute => spec` bridge is FALSE: the
   rounded `b64_div` inside the computational Liang-Barsky filter
   (`b64_passes_through_hot_pixel_compute`, PassesThrough_b64_compute.v)
   over-accepts within O(ulp) of tangency, where the exact-real spec
   (`b64_passes_through_hot_pixel`, HotPixel_b64.v) rejects.  That finding
   was oracle-evidenced only.  THIS FILE promotes it to a Rocq-kernel-checked
   theorem: a single `Qed`-closed witness for which `compute = true` while
   `spec = false`.

   The witness is the oracle-confirmed counterexample from the finding (hex-
   float exact bits):
     P0 = (1, -0x1.0000000000002p+1)
     P1 = (0x1.ffffffffffffp-2, -0x1.4000000000002p+1)
     C  = (0, -2).
   The segment misses the closed hot pixel by a sub-ulp margin: the exact
   x-axis lower t-bound is 2^49/(2^49+1) while the exact y-axis upper t-bound
   is (2^49-1)/2^49, and 2^49/(2^49+1) > (2^49-1)/2^49 (an N^2 > N^2-1 gap with
   N = 2^49), so the clipped parameter interval is EMPTY -- the exact spec
   touch is `false`.  The rounded filter, dividing with round-to-nearest,
   closes that gap inward and reports `true`.

   The `compute = true` half is decided by `vm_compute` (the binary64 ops are
   computable).  The `spec = false` half is the exact-real argument above:
   it is intrinsically non-computational (`R`-valued `Rle_bool`/`Rmax`/`Rmin`),
   so it is proved by reducing the final interval comparison to the strict
   rational inequality on the exact dyadic coordinate values.

   This is a Qed theorem, NOT an `Admitted` -- it does not belong in
   `docs/admitted-counterexamples.txt` (which tracks Admitted obligations).
   It is the soundness-disproof the verified-claims index and README refer to:
   soundness vs the sharp closed pixel is now machine-checked false, while
   completeness (`spec => compute`) and the closed-spec soundness
   (`b64_passes_through_sound`) remain Qed-closed elsewhere.
   ========================================================================== *)

From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute.
Require Import Reals.
Require Import Lia.
Require Import Lra.
Local Open Scope R_scope.

Definition wP0x : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition wP0y : binary64 := Binary.B754_finite prec emax true  4503599627370498 (-51) eq_refl.
Definition wP1x : binary64 := Binary.B754_finite prec emax false 9007199254740976 (-54) eq_refl.
Definition wP1y : binary64 := Binary.B754_finite prec emax true  5629499534213122 (-51) eq_refl.
Definition wCx  : binary64 := Binary.B754_zero prec emax false.
Definition wCy  : binary64 := Binary.B754_finite prec emax true  4503599627370496 (-51) eq_refl.

Definition wP0 : BPoint := mkBP wP0x wP0y.
Definition wP1 : BPoint := mkBP wP1x wP1y.
Definition wC  : BPoint := mkBP wCx  wCy.

Lemma compute_true : b64_passes_through_hot_pixel_compute wP0 wP1 wC = true.
Proof. vm_compute. reflexivity. Qed.

Lemma Bfin_val :
  forall s m e (pf : _),
    Binary.B2R prec emax (Binary.B754_finite prec emax s m e pf)
      = IZR (cond_Zopp s (Z.pos m)) * bpow radix2 e.
Proof. intros. reflexivity. Qed.

Lemma norm54 : forall (n e : Z),
  IZR n * bpow radix2 e = (IZR n * bpow radix2 (e + 54)) * bpow radix2 (-54).
Proof.
  intros n e. rewrite Rmult_assoc, <- bpow_plus.
  replace (e + 54 + -54)%Z with e by ring. reflexivity.
Qed.

Lemma bpow2_2 : bpow radix2 2 = IZR 4.   Proof. reflexivity. Qed.
Lemma bpow2_3 : bpow radix2 3 = IZR 8.   Proof. reflexivity. Qed.
Lemma bpow2_0 : bpow radix2 0 = IZR 1.   Proof. reflexivity. Qed.

Notation C54 := (bpow radix2 (-54)).
Lemma C54_pos : 0 < C54.  Proof. apply bpow_gt_0. Qed.
Lemma C54_neq : C54 <> 0. Proof. apply Rgt_not_eq, Rlt_gt, C54_pos. Qed.

(* Six coordinates and 1/2 on the common 2^(-54) scale. *)
Lemma val_P0x : Binary.B2R prec emax wP0x = IZR 18014398509481984 * C54.
Proof. unfold wP0x. rewrite Bfin_val. cbn [cond_Zopp]. rewrite norm54.
  replace (-52 + 54)%Z with 2%Z by ring. rewrite bpow2_2, <- mult_IZR. reflexivity. Qed.
Lemma val_P0y : Binary.B2R prec emax wP0y = IZR (-36028797018963984) * C54.
Proof. unfold wP0y. rewrite Bfin_val. cbn [cond_Zopp]. rewrite norm54.
  replace (-51 + 54)%Z with 3%Z by ring. rewrite bpow2_3, <- mult_IZR. reflexivity. Qed.
Lemma val_P1x : Binary.B2R prec emax wP1x = IZR 9007199254740976 * C54.
Proof. unfold wP1x. rewrite Bfin_val. cbn [cond_Zopp]. rewrite norm54.
  replace (-54 + 54)%Z with 0%Z by ring. rewrite bpow2_0, <- mult_IZR. reflexivity. Qed.
Lemma val_P1y : Binary.B2R prec emax wP1y = IZR (-45035996273704976) * C54.
Proof. unfold wP1y. rewrite Bfin_val. cbn [cond_Zopp]. rewrite norm54.
  replace (-51 + 54)%Z with 3%Z by ring. rewrite bpow2_3, <- mult_IZR. reflexivity. Qed.
Lemma val_Cx : Binary.B2R prec emax wCx = IZR 0 * C54.
Proof. unfold wCx. cbn [Binary.B2R]. rewrite Rmult_0_l. reflexivity. Qed.
Lemma val_Cy : Binary.B2R prec emax wCy = IZR (-36028797018963968) * C54.
Proof. unfold wCy. rewrite Bfin_val. cbn [cond_Zopp]. rewrite norm54.
  replace (-51 + 54)%Z with 3%Z by ring. rewrite bpow2_3, <- mult_IZR. reflexivity. Qed.
Lemma half_val : / 2 = IZR 9007199254740992 * C54.
Proof.
  replace (IZR 9007199254740992) with (bpow radix2 53) by reflexivity.
  rewrite <- bpow_plus. replace (53 + -54)%Z with (-1)%Z by ring. reflexivity.
Qed.

(* Cancellation of the common scale in a quotient. *)
Lemma cancelC : forall s t : R, t <> 0 -> (s * C54) / (t * C54) = s / t.
Proof. intros s t Ht. field. split; [ exact Ht | apply C54_neq ]. Qed.

(* IZR-combine helpers (ring can't merge distinct IZR atoms by itself). *)
Lemma three_term : forall a b c : Z,
  IZR a * C54 - IZR b * C54 - IZR c * C54 = IZR (a - b - c) * C54.
Proof. intros. rewrite !minus_IZR. ring. Qed.
Lemma plusminus_term : forall a b c : Z,
  IZR a * C54 + IZR b * C54 - IZR c * C54 = IZR (a + b - c) * C54.
Proof. intros. rewrite minus_IZR, plus_IZR. ring. Qed.
Lemma two_term : forall a b : Z,
  IZR a * C54 - IZR b * C54 = IZR (a - b) * C54.
Proof. intros. rewrite minus_IZR. ring. Qed.

(* p1/q1 < p2/q2 for same-sign denominators reduces to a Z inequality.
   (Both t-bound denominators c1-c0 here are negative, so this is the form
   actually needed.) *)
Lemma frac_lt : forall a b c d : Z, (0 < b * d)%Z -> (a * d < c * b)%Z ->
  IZR a / IZR b < IZR c / IZR d.
Proof.
  intros a b c d Hbd H.
  assert (Hb : (b <> 0)%Z) by (intro Hx; subst; simpl in Hbd; lia).
  assert (Hd : (d <> 0)%Z) by (intro Hx; subst; rewrite Z.mul_0_r in Hbd; lia).
  assert (Hb0 : IZR b <> 0) by (apply not_0_IZR; exact Hb).
  assert (Hd0 : IZR d <> 0) by (apply not_0_IZR; exact Hd).
  assert (Hbd0 : 0 < IZR b * IZR d) by (rewrite <- mult_IZR; apply IZR_lt; exact Hbd).
  apply Rminus_lt.
  replace (IZR a / IZR b - IZR c / IZR d)
    with ((IZR (a * d) - IZR (c * b)) / (IZR b * IZR d))
    by (rewrite !mult_IZR; field; split; assumption).
  apply Rmult_lt_reg_r with (IZR b * IZR d); [ exact Hbd0 | ].
  rewrite Rmult_0_l. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r
    by (apply Rgt_not_eq, Rlt_gt, Hbd0).
  rewrite <- minus_IZR. replace 0 with (IZR 0) by reflexivity. apply IZR_lt. lia.
Qed.

(* The four exact t-bounds, as rationals (numerator/denominator with the
   common scale already cancelled). *)
Lemma xa_val :
  (Binary.B2R prec emax (bx wC) - / 2 - Binary.B2R prec emax (bx wP0))
    / (Binary.B2R prec emax (bx wP1) - Binary.B2R prec emax (bx wP0))
  = IZR (0 - 9007199254740992 - 18014398509481984)
    / IZR (9007199254740976 - 18014398509481984).
Proof.
  change (bx wP0) with wP0x. change (bx wP1) with wP1x. change (bx wC) with wCx.
  rewrite val_P0x, val_P1x, val_Cx, half_val, three_term, two_term.
  rewrite cancelC by (apply not_0_IZR; vm_compute; discriminate). reflexivity.
Qed.
Lemma xb_val :
  (Binary.B2R prec emax (bx wC) + / 2 - Binary.B2R prec emax (bx wP0))
    / (Binary.B2R prec emax (bx wP1) - Binary.B2R prec emax (bx wP0))
  = IZR (0 + 9007199254740992 - 18014398509481984)
    / IZR (9007199254740976 - 18014398509481984).
Proof.
  change (bx wP0) with wP0x. change (bx wP1) with wP1x. change (bx wC) with wCx.
  rewrite val_P0x, val_P1x, val_Cx, half_val, plusminus_term, two_term.
  rewrite cancelC by (apply not_0_IZR; vm_compute; discriminate). reflexivity.
Qed.
Lemma ya_val :
  (Binary.B2R prec emax (by_ wC) - / 2 - Binary.B2R prec emax (by_ wP0))
    / (Binary.B2R prec emax (by_ wP1) - Binary.B2R prec emax (by_ wP0))
  = IZR (-36028797018963968 - 9007199254740992 - -36028797018963984)
    / IZR (-45035996273704976 - -36028797018963984).
Proof.
  change (by_ wP0) with wP0y. change (by_ wP1) with wP1y. change (by_ wC) with wCy.
  rewrite val_P0y, val_P1y, val_Cy, half_val, three_term, two_term.
  rewrite cancelC by (apply not_0_IZR; vm_compute; discriminate). reflexivity.
Qed.
Lemma yb_val :
  (Binary.B2R prec emax (by_ wC) + / 2 - Binary.B2R prec emax (by_ wP0))
    / (Binary.B2R prec emax (by_ wP1) - Binary.B2R prec emax (by_ wP0))
  = IZR (-36028797018963968 + 9007199254740992 - -36028797018963984)
    / IZR (-45035996273704976 - -36028797018963984).
Proof.
  change (by_ wP0) with wP0y. change (by_ wP1) with wP1y. change (by_ wC) with wCy.
  rewrite val_P0y, val_P1y, val_Cy, half_val, plusminus_term, two_term.
  rewrite cancelC by (apply not_0_IZR; vm_compute; discriminate). reflexivity.
Qed.

(* Non-degeneracy of both axes. *)
Lemma x1_ne_x0 : Binary.B2R prec emax (bx wP1) <> Binary.B2R prec emax (bx wP0).
Proof.
  change (bx wP0) with wP0x. change (bx wP1) with wP1x.
  rewrite val_P0x, val_P1x. assert (HC := C54_pos). nra.
Qed.
Lemma y1_ne_y0 : Binary.B2R prec emax (by_ wP1) <> Binary.B2R prec emax (by_ wP0).
Proof.
  change (by_ wP0) with wP0y. change (by_ wP1) with wP1y.
  rewrite val_P0y, val_P1y. assert (HC := C54_pos). nra.
Qed.

(* The single value fact behind the divergence: exact thi_y < tlo_x. *)
Lemma key_lt :
  lb_thi (Binary.B2R prec emax (by_ wP0)) (Binary.B2R prec emax (by_ wP1))
         (Binary.B2R prec emax (by_ wC) - / 2) (Binary.B2R prec emax (by_ wC) + / 2)
  < lb_tlo (Binary.B2R prec emax (bx wP0)) (Binary.B2R prec emax (bx wP1))
           (Binary.B2R prec emax (bx wC) - / 2) (Binary.B2R prec emax (bx wC) + / 2).
Proof.
  unfold lb_thi, lb_tlo.
  destruct (Req_dec_T (Binary.B2R prec emax (bx wP1)) (Binary.B2R prec emax (bx wP0)))
    as [Ex|Ex]; [ exfalso; apply x1_ne_x0; exact Ex | ].
  destruct (Req_dec_T (Binary.B2R prec emax (by_ wP1)) (Binary.B2R prec emax (by_ wP0)))
    as [Ey|Ey]; [ exfalso; apply y1_ne_y0; exact Ey | ].
  rewrite xa_val, xb_val, ya_val, yb_val.
  apply Rmax_lub_lt.
  - apply Rmin_glb_lt; apply frac_lt; lia.
  - apply Rmin_glb_lt; apply frac_lt; lia.
Qed.

Lemma touch_orig_false : b64_liang_barsky_touches wP0 wP1 wC = false.
Proof.
  unfold b64_liang_barsky_touches.
  apply Bool.andb_false_intro2. apply Rle_bool_false.
  eapply Rle_lt_trans; [ apply Rmin_r | ].
  eapply Rlt_le_trans; [ | apply Rmax_r ].
  eapply Rle_lt_trans; [ apply Rmin_r | ].
  eapply Rlt_le_trans; [ | apply Rmax_l ].
  apply key_lt.
Qed.

Theorem b64_passes_through_compute_unsound :
  exists P0 P1 C : BPoint,
    b64_passes_through_hot_pixel_compute P0 P1 C = true /\
    b64_passes_through_hot_pixel P0 P1 C = false.
Proof.
  exists wP0, wP1, wC. split.
  - exact compute_true.
  - unfold b64_passes_through_hot_pixel. rewrite touch_orig_false. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.  Only the standard classical-reals trio plus the          *)
(* Flocq-inherited `Classical_Prop.classic` (this file references the         *)
(* `Binary`-backed `b64_liang_barsky_touches` spec) -- no new axioms, no      *)
(* `Admitted`.  Registered in `docs/audit-exceptions.txt` alongside           *)
(* HotPixel_b64.v, whose lineage it shares.                                    *)
(* -------------------------------------------------------------------------- *)
Print Assumptions b64_passes_through_compute_unsound.
