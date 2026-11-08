(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_c2_counterexample
   ----------------------------------------------------------------------------
   QEX for the off-grid completeness obligation C2 (`spec => compute`):
   C2 is FALSE.  Concrete binary64 witness with
       b64_passes_through_hot_pixel         P0 P1 C = true     (exact-real spec)
       b64_passes_through_hot_pixel_compute P0 P1 C = false    (rounded compute)

   Witness (hex floats):
     P0 = (-0x1.ad7d2652adcf4p+1, 0x1.86d996d4a2000p+0)   P1 = (0x1.f57d2652adcf4p+4, -0x1.0b6ccb6a51000p+4)   C = (1, 0)
   P1 = -8 P0 + 9 K with K = (1/2, -1/2) the lower-left corner of the closed
   pixel, so the exact line passes THROUGH that corner (a grazing touch):
       exact x lower t-bound  tlo_x = (xlo-x0)/(x1-x0) = 1/9
       exact y upper t-bound  thi_y = (ylo-y0)/(y1-y0) = 1/9
   so tmin = tmax = 1/9 exactly (tangency; the spec interval is a single point).

   Computed path (actual `b64_lb_tlo`/`b64_lb_thi` of PassesThrough_b64_compute):
     x axis: ahat = xlo-x0 EXACT = 0x1.ed7d2652adcf4p+1;  bhat = fl(x1-x0) = 0x1.1596658e81c49p+5 != b
             (b = x1-x0 needs 54+ bits; bhat is a ROUNDED denominator)
             that_x = b64_div ahat bhat = 0x1.c71c71c71c71dp-4  (> round(1/9))
     y axis: ahat = -0x1.036ccb6a51000p+1, bhat = -0x1.23da64d79b200p+4 both exact
             that_y = b64_div ahat bhat = 0x1.c71c71c71c71cp-4  (= fl(1/9))
   Required (tmin <= tmax needs) that_x <= that_y; actual that_x > that_y by one
   ulp.  The snapped touch is true in both spec and compute (snap(P0) = (-3,2),
   snap(P1) = (31,-17)), so the failure is exactly the original-segment touch.

   The compute half is `vm_compute`; the spec half and the exact quotients are
   exact-real arguments over the dyadic coordinate values.  No Admitted.
   ========================================================================== *)
From Stdlib Require Import Reals ZArith Lra Lia.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 HotPixel_b64
  PassesThrough_b64_compute.
Local Open Scope R_scope.

Definition c2_x0 : binary64 := Binary.B754_finite prec emax true 7555648034888948 (-51) eq_refl.
Definition c2_y0 : binary64 := Binary.B754_finite prec emax false 6875905172054016 (-52) eq_refl.
Definition c2_x1 : binary64 := Binary.B754_finite prec emax false 8822285430086900 (-48) eq_refl.
Definition c2_y1 : binary64 := Binary.B754_finite prec emax true 4704589981224960 (-48) eq_refl.
Definition c2_cx : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition c2_cy : binary64 := Binary.B754_zero prec emax false.
Definition c2P0 : BPoint := mkBP c2_x0 c2_y0.
Definition c2P1 : BPoint := mkBP c2_x1 c2_y1.
Definition c2C  : BPoint := mkBP c2_cx c2_cy.

(* ---- compute side: the actual b64 path --------------------------------- *)
Lemma c2_compute_false : b64_passes_through_hot_pixel_compute c2P0 c2P1 c2C = false.
Proof. vm_compute. reflexivity. Qed.

Lemma c2_compute_orig_touch_false :
  b64_liang_barsky_touches_compute c2P0 c2P1 c2C = false.
Proof. vm_compute. reflexivity. Qed.

Lemma c2_compute_snap_touch_true :
  b64_liang_barsky_touches_compute (b64_snap c2P0) (b64_snap c2P1) c2C = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- exact values ------------------------------------------------------- *)
Lemma Bfin_val : forall s m e (pf : _),
  Binary.B2R prec emax (Binary.B754_finite prec emax s m e pf)
    = IZR (cond_Zopp s (Z.pos m)) * bpow radix2 e.
Proof. intros. reflexivity. Qed.

Lemma bpn : forall k : Z, (0 <= k)%Z -> bpow radix2 (-k) = / IZR (2 ^ k).
Proof. intros k Hk. rewrite bpow_opp. f_equal. rewrite <- IZR_Zpower by exact Hk. reflexivity. Qed.

Lemma v_x0 : Binary.B2R prec emax c2_x0 = (-1888912008722237 / 562949953421312).
Proof.
  unfold c2_x0. rewrite Bfin_val. cbn [cond_Zopp]. try rewrite opp_IZR.
  replace (-51)%Z with (-(51))%Z by reflexivity. rewrite bpn by lia.
  replace (2 ^ 51)%Z with 2251799813685248%Z by reflexivity.
  lra.
Qed.
Lemma v_y0 : Binary.B2R prec emax c2_y0 = (839343893073 / 549755813888).
Proof.
  unfold c2_y0. rewrite Bfin_val. cbn [cond_Zopp]. try rewrite opp_IZR.
  replace (-52)%Z with (-(52))%Z by reflexivity. rewrite bpn by lia.
  replace (2 ^ 52)%Z with 4503599627370496%Z by reflexivity.
  lra.
Qed.
Lemma v_x1 : Binary.B2R prec emax c2_x1 = (2205571357521725 / 70368744177664).
Proof.
  unfold c2_x1. rewrite Bfin_val. cbn [cond_Zopp]. try rewrite opp_IZR.
  replace (-48)%Z with (-(48))%Z by reflexivity. rewrite bpn by lia.
  replace (2 ^ 48)%Z with 281474976710656%Z by reflexivity.
  lra.
Qed.
Lemma v_y1 : Binary.B2R prec emax c2_y1 = (-1148581538385 / 68719476736).
Proof.
  unfold c2_y1. rewrite Bfin_val. cbn [cond_Zopp]. try rewrite opp_IZR.
  replace (-48)%Z with (-(48))%Z by reflexivity. rewrite bpn by lia.
  replace (2 ^ 48)%Z with 281474976710656%Z by reflexivity.
  lra.
Qed.
Lemma v_cx : Binary.B2R prec emax c2_cx = (1).
Proof.
  unfold c2_cx. rewrite Bfin_val. cbn [cond_Zopp]. try rewrite opp_IZR.
  replace (-52)%Z with (-(52))%Z by reflexivity. rewrite bpn by lia.
  replace (2 ^ 52)%Z with 4503599627370496%Z by reflexivity.
  lra.
Qed.
Lemma v_cy : Binary.B2R prec emax c2_cy = 0.
Proof. reflexivity. Qed.

Lemma snap_round_coord_1_nearest : forall (x : R) (n : Z),
  Rabs (x - IZR n) < /2 -> snap_round_coord x 1 = IZR n.
Proof.
  intros x n H. unfold snap_round_coord. rewrite Rmult_1_r.
  rewrite round_FIX_IZR. unfold Rdiv. rewrite Rinv_1, Rmult_1_r.
  unfold round_mode.
  rewrite (Znearest_imp (fun z => negb (Z.even z)) x n H). reflexivity.
Qed.

Lemma sn_x0 : Binary.B2R prec emax (b64_snap_coord c2_x0) = -3.
Proof.
  rewrite b64_snap_coord_B2R, v_x0.
  replace (-3) with (IZR (-3)) by (simpl; lra).
  apply snap_round_coord_1_nearest. rewrite <- (Rabs_Ropp). apply Rabs_def1; lra.
Qed.
Lemma sn_y0 : Binary.B2R prec emax (b64_snap_coord c2_y0) = 2.
Proof.
  rewrite b64_snap_coord_B2R, v_y0.
  replace 2 with (IZR 2) by (simpl; lra).
  apply snap_round_coord_1_nearest. apply Rabs_def1; lra.
Qed.
Lemma sn_x1 : Binary.B2R prec emax (b64_snap_coord c2_x1) = 31.
Proof.
  rewrite b64_snap_coord_B2R, v_x1.
  replace 31 with (IZR 31) by (simpl; lra).
  apply snap_round_coord_1_nearest. apply Rabs_def1; lra.
Qed.
Lemma sn_y1 : Binary.B2R prec emax (b64_snap_coord c2_y1) = -17.
Proof.
  rewrite b64_snap_coord_B2R, v_y1.
  replace (-17) with (IZR (-17)) by (simpl; lra).
  apply snap_round_coord_1_nearest. apply Rabs_def1; lra.
Qed.

(* ---- exact-real touch of a segment, all four coordinates numeric -------- *)
Ltac kill_degenerate :=
  repeat match goal with
  | |- context [Req_dec_T ?a ?b] =>
      destruct (Req_dec_T a b) as [?E | ?NE]; [exfalso; lra | ]
  end.

Lemma c2_spec_touch_orig : b64_liang_barsky_touches c2P0 c2P1 c2C = true.
Proof.
  unfold c2P0, c2P1, c2C. unfold b64_liang_barsky_touches. cbv zeta. cbn [bx by_].
  rewrite v_x0, v_y0, v_x1, v_y1, v_cx, v_cy.
  unfold lb_inslab, lb_tlo, lb_thi; kill_degenerate; simpl.
  apply Rle_bool_true.
  apply Rmax_lub.
  - apply Rmin_glb; [lra | apply Rmin_glb];
      unfold Rmin, Rmax; repeat destruct (Rle_dec _ _); lra.
  - apply Rmax_lub; apply Rmin_glb.
    + unfold Rmin, Rmax; repeat destruct (Rle_dec _ _); lra.
    + apply Rmin_glb; unfold Rmin, Rmax; repeat destruct (Rle_dec _ _); lra.
    + unfold Rmin, Rmax; repeat destruct (Rle_dec _ _); lra.
    + apply Rmin_glb; unfold Rmin, Rmax; repeat destruct (Rle_dec _ _); lra.
Qed.

Lemma c2_spec_touch_snap :
  b64_liang_barsky_touches (b64_snap c2P0) (b64_snap c2P1) c2C = true.
Proof.
  unfold c2P0, c2P1, c2C, b64_snap. unfold b64_liang_barsky_touches. cbv zeta. cbn [bx by_].
  rewrite sn_x0, sn_y0, sn_x1, sn_y1, v_cx, v_cy.
  unfold lb_inslab, lb_tlo, lb_thi; kill_degenerate; simpl.
  apply Rle_bool_true.
  apply Rmax_lub.
  - apply Rmin_glb; [lra | apply Rmin_glb];
      unfold Rmin, Rmax; repeat destruct (Rle_dec _ _); lra.
  - apply Rmax_lub; apply Rmin_glb.
    + unfold Rmin, Rmax; repeat destruct (Rle_dec _ _); lra.
    + apply Rmin_glb; unfold Rmin, Rmax; repeat destruct (Rle_dec _ _); lra.
    + unfold Rmin, Rmax; repeat destruct (Rle_dec _ _); lra.
    + apply Rmin_glb; unfold Rmin, Rmax; repeat destruct (Rle_dec _ _); lra.
Qed.

Theorem c2_spec_true : b64_passes_through_hot_pixel c2P0 c2P1 c2C = true.
Proof.
  unfold b64_passes_through_hot_pixel. apply andb_true_intro.
  split; [exact c2_spec_touch_orig | exact c2_spec_touch_snap].
Qed.

(* ---- the QEX: spec true, compute false, so C2 fails ---------------------- *)
Theorem c2_counterexample :
  b64_passes_through_hot_pixel c2P0 c2P1 c2C = true /\
  b64_passes_through_hot_pixel_compute c2P0 c2P1 c2C = false.
Proof. split; [exact c2_spec_true | exact c2_compute_false]. Qed.

Theorem c2_false :
  ~ (forall P0 P1 C : BPoint,
       b64_passes_through_hot_pixel P0 P1 C = true ->
       b64_passes_through_hot_pixel_compute P0 P1 C = true).
Proof.
  intro H. pose proof (H c2P0 c2P1 c2C c2_spec_true) as H1.
  rewrite c2_compute_false in H1. discriminate.
Qed.

(* ---- the report: exact vs computed quotient on the two tangent axes ------ *)
Definition lit_ax : binary64 := Binary.B754_finite prec emax false 8681547941731572 (-51) eq_refl.
Definition lit_bx : binary64 := Binary.B754_finite prec emax false 4883370717224009 (-47) eq_refl.
Definition lit_tx : binary64 := Binary.B754_finite prec emax false 8006399337547549 (-56) eq_refl.
Definition lit_ay : binary64 := Binary.B754_finite prec emax true 4563852492869632 (-51) eq_refl.
Definition lit_by : binary64 := Binary.B754_finite prec emax true 5134334054478336 (-48) eq_refl.
Definition lit_ty : binary64 := Binary.B754_finite prec emax false 8006399337547548 (-56) eq_refl.

Lemma val_ax : Binary.B2R prec emax lit_ax = (2170386985432893 / 562949953421312).
Proof. unfold lit_ax. rewrite Bfin_val. cbn [cond_Zopp]. try rewrite opp_IZR. replace (-51)%Z with (-(51))%Z by reflexivity. rewrite bpn by lia. replace (2 ^ 51)%Z with 2251799813685248%Z by reflexivity. lra. Qed.
Lemma val_bx : Binary.B2R prec emax lit_bx = (4883370717224009 / 140737488355328).
Proof. unfold lit_bx. rewrite Bfin_val. cbn [cond_Zopp]. try rewrite opp_IZR. replace (-47)%Z with (-(47))%Z by reflexivity. rewrite bpn by lia. replace (2 ^ 47)%Z with 140737488355328%Z by reflexivity. lra. Qed.
Lemma val_tx : Binary.B2R prec emax lit_tx = (8006399337547549 / 72057594037927936).
Proof. unfold lit_tx. rewrite Bfin_val. cbn [cond_Zopp]. try rewrite opp_IZR. replace (-56)%Z with (-(56))%Z by reflexivity. rewrite bpn by lia. replace (2 ^ 56)%Z with 72057594037927936%Z by reflexivity. lra. Qed.
Lemma val_ay : Binary.B2R prec emax lit_ay = (-1114221800017 / 549755813888).
Proof. unfold lit_ay. rewrite Bfin_val. cbn [cond_Zopp]. try rewrite opp_IZR. replace (-51)%Z with (-(51))%Z by reflexivity. rewrite bpn by lia. replace (2 ^ 51)%Z with 2251799813685248%Z by reflexivity. lra. Qed.
Lemma val_by : Binary.B2R prec emax lit_by = (-10027996200153 / 549755813888).
Proof. unfold lit_by. rewrite Bfin_val. cbn [cond_Zopp]. try rewrite opp_IZR. replace (-48)%Z with (-(48))%Z by reflexivity. rewrite bpn by lia. replace (2 ^ 48)%Z with 281474976710656%Z by reflexivity. lra. Qed.
Lemma val_ty : Binary.B2R prec emax lit_ty = (2001599834386887 / 18014398509481984).
Proof. unfold lit_ty. rewrite Bfin_val. cbn [cond_Zopp]. try rewrite opp_IZR. replace (-56)%Z with (-(56))%Z by reflexivity. rewrite bpn by lia. replace (2 ^ 56)%Z with 72057594037927936%Z by reflexivity. lra. Qed.

(* x axis (the lower bound that is pushed UP).  Exact: a = xlo-x0, b = x1-x0. *)
Theorem c2_report_x_axis :
  (* exact t = a/b = 1/9 *)
  ((Binary.B2R prec emax c2_cx - / 2 - Binary.B2R prec emax c2_x0)
   / (Binary.B2R prec emax c2_x1 - Binary.B2R prec emax c2_x0) = 1 / 9) /\
  (* ahat = a exactly; bhat is a rounded denominator, bhat <> b *)
  (Binary.B2R prec emax lit_ax
     = Binary.B2R prec emax c2_cx - / 2 - Binary.B2R prec emax c2_x0) /\
  (Binary.B2R prec emax lit_bx
     <> Binary.B2R prec emax c2_x1 - Binary.B2R prec emax c2_x0) /\
  (* the computed values are exactly these literals *)
  b64_compare (b64_minus (b64_minus c2_cx b64_half) c2_x0) lit_ax = Some Eq /\
  b64_compare (b64_minus c2_x1 c2_x0) lit_bx = Some Eq /\
  b64_compare (b64_div lit_ax lit_bx) lit_tx = Some Eq /\
  (* and the computed lower t-bound of the actual compute path is that_x *)
  b64_compare (b64_lb_tlo c2_x0 c2_x1 (b64_minus c2_cx b64_half)
                 (b64_plus c2_cx b64_half)) lit_tx = Some Eq.
Proof.
  repeat apply conj.
  - rewrite v_cx, v_x0, v_x1. lra.
  - rewrite val_ax, v_cx, v_x0. lra.
  - rewrite val_bx, v_x1, v_x0. lra.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(* y axis (the upper bound that stays at round(1/9)). *)
Theorem c2_report_y_axis :
  ((Binary.B2R prec emax c2_cy - / 2 - Binary.B2R prec emax c2_y0)
   / (Binary.B2R prec emax c2_y1 - Binary.B2R prec emax c2_y0) = 1 / 9) /\
  (Binary.B2R prec emax lit_ay
     = Binary.B2R prec emax c2_cy - / 2 - Binary.B2R prec emax c2_y0) /\
  (Binary.B2R prec emax lit_by
     = Binary.B2R prec emax c2_y1 - Binary.B2R prec emax c2_y0) /\
  b64_compare (b64_minus (b64_minus c2_cy b64_half) c2_y0) lit_ay = Some Eq /\
  b64_compare (b64_minus c2_y1 c2_y0) lit_by = Some Eq /\
  b64_compare (b64_div lit_ay lit_by) lit_ty = Some Eq /\
  b64_compare (b64_lb_thi c2_y0 c2_y1 (b64_minus c2_cy b64_half)
                 (b64_plus c2_cy b64_half)) lit_ty = Some Eq.
Proof.
  repeat apply conj.
  - rewrite v_cy, v_y0, v_y1. lra.
  - rewrite val_ay, v_cy, v_y0. lra.
  - rewrite val_by, v_y1, v_y0. lra.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(* required: that_x <= that_y.   actual: that_x > that_y. *)
Theorem c2_ordering_fails :
  b64_compare lit_tx lit_ty = Some Gt /\
  Binary.B2R prec emax lit_ty < Binary.B2R prec emax lit_tx.
Proof.
  split; [vm_compute; reflexivity|].
  rewrite val_tx, val_ty. lra.
Qed.

Print Assumptions c2_false.
Print Assumptions c2_counterexample.
Print Assumptions c2_report_x_axis.
Print Assumptions c2_report_y_axis.
Print Assumptions c2_ordering_fails.
