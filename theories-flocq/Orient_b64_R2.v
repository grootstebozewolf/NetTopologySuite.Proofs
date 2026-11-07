(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_R2
   ----------------------------------------------------------------------------
   R2 attempt (see docs/orient-r2-attempt-2026-11.md).

   With D = cross_R_BP (the exact real determinant) and Dhat = B2R (b64_orient2d):

     1. `sign_of_error_bound`        |Dh - D| <= E /\ E < |D|  ->  sign Dh = sign D
                                     (pure real analysis).
     2. `b64_orient2d_forward_error` under the corpus's own `b64_orient2d_safe`
                                     (derivable from `b64_orient2d_inputs_safe`):
                                     Dhat finite and |Dhat - D| <= o2_E, where
                                       o2_E = 6 u (|A B| + |C Dd|) + 6 e (m + 1),
                                       u = 2^-53, e = 2^-1075 (the absolute
                                       underflow floor, so the bound is TRUE in
                                       the underflow regime), A,B,C,Dd the exact
                                       coordinate differences, m = |A|+|B|+|C|+|Dd|.
                                     Built from `b64ae_round_err` (B64_AbsErr)
                                     + `b64_minus_correct` / `b64_mult_correct`.
                                     Constants are crude, not Shewchuk's tight ones.
     3. `b64_orient2d_R2`            premise 1 discharged: o2_E < |D| -> sign Dhat = sign D.

   4. Premise 2, the separation `o2_E < |D|`, is bracketed, not discharged:
        `o2_separation_tight_grid`      holds on the integer grid |n| <= 2^22
                                        whenever D <> 0 (E < 0.1 < 1 <= |D|);
        `o2_separation_fails_on_int_grid`  fails INSIDE the corpus's own
                                        `orient2d_inputs_int_safe` window |n| <= 2^25:
                                        D = -1 but o2_E >= 1.33.
      So no finiteness / magnitude / int-safe domain implies it.
   No Admitted / Axiom / Parameter.
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 Orientation_b64
  B64_bridge B64_lib B64_AbsErr Orient_b64_R Orient_b64_sound Orient_b64_exact.
Local Open Scope R_scope.
Local Notation B2R := (Binary.B2R prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  The bridge: elementary real analysis.                                  *)
(* -------------------------------------------------------------------------- *)
Lemma sign_of_error_bound : forall Dh D E : R,
  Rabs (Dh - D) <= E -> E < Rabs D -> Rcompare Dh 0 = Rcompare D 0.
Proof.
  intros Dh D E H1 H2.
  pose proof (Rle_lt_trans _ _ _ H1 H2) as H.
  pose proof (Rabs_pos (Dh - D)) as Hp.
  destruct (Rtotal_order D 0) as [Hn | [Hz | Hpos]].
  - rewrite (Rabs_left D Hn) in H.
    destruct (Rabs_def2 _ _ H) as [L _]. 
    rewrite (Rcompare_Lt Dh 0) by lra. rewrite (Rcompare_Lt D 0) by lra. reflexivity.
  - subst D. rewrite Rabs_R0 in H. lra.
  - rewrite (Rabs_right D (Rle_ge _ _ (Rlt_le _ _ Hpos))) in H.
    destruct (Rabs_def2 _ _ H) as [_ R].
    rewrite (Rcompare_Gt Dh 0) by lra. rewrite (Rcompare_Gt D 0) by lra. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Pure-real chain: 4 differences, 2 products, 1 outer difference.        *)
(* -------------------------------------------------------------------------- *)
Section Chain.
  Variables u e : R.
  Hypothesis Hu0 : 0 <= u.   Hypothesis Hu1 : u <= / 1000.
  Hypothesis He0 : 0 <= e.   Hypothesis He1 : e <= / 1000.

  Lemma mul_err : forall a A b B,
    Rabs (a - A) <= u * Rabs A + e -> Rabs (b - B) <= u * Rabs B + e ->
    Rabs (a * b - A * B)
      <= (2*u + u*u) * (Rabs A * Rabs B) + (1+u) * e * (Rabs A + Rabs B) + e*e.
  Proof.
    intros a A b B Ha Hb.
    assert (Eq : a * b - A * B = (a - A) * B + A * (b - B) + (a - A) * (b - B))
      by ring.
    rewrite Eq.
    pose proof (Rabs_pos A) as PA. pose proof (Rabs_pos B) as PB.
    pose proof (Rabs_pos (a - A)) as Pa. pose proof (Rabs_pos (b - B)) as Pb.
    eapply Rle_trans; [apply Rabs_triang|].
    eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang|].
    rewrite !Rabs_mult.
    assert (T1 : Rabs (a - A) * Rabs B <= (u * Rabs A + e) * Rabs B)
      by (apply Rmult_le_compat_r; assumption).
    assert (T2 : Rabs A * Rabs (b - B) <= Rabs A * (u * Rabs B + e))
      by (apply Rmult_le_compat_l; assumption).
    assert (T3 : Rabs (a - A) * Rabs (b - B) <= (u * Rabs A + e) * (u * Rabs B + e))
      by (apply Rmult_le_compat; assumption).
    nra.
  Qed.

  (* One rounded product t of (a b), a ~ A, b ~ B. *)
  Lemma prod_err : forall a A b B t,
    Rabs (a - A) <= u * Rabs A + e -> Rabs (b - B) <= u * Rabs B + e ->
    Rabs (t - a * b) <= u * Rabs (a * b) + e ->
    Rabs (t - A * B) <= 4 * u * (Rabs A * Rabs B) + 2 * e * (Rabs A + Rabs B) + 2 * e.
  Proof.
    intros a A b B t Ha Hb Ht.
    pose proof (mul_err a A b B Ha Hb) as M.
    pose proof (Rabs_pos A) as PA. pose proof (Rabs_pos B) as PB.
    set (P := Rabs A * Rabs B) in *.
    assert (HP : 0 <= P) by (unfold P; apply Rmult_le_pos; assumption).
    set (q := Rabs A + Rabs B) in *.
    assert (Hq : 0 <= q) by (unfold q; lra).
    assert (Hab : Rabs (a * b) <= Rabs (A * B) + Rabs (a * b - A * B)).
    { replace (a * b) with (A * B + (a * b - A * B)) at 1 by ring.
      apply Rabs_triang. }
    assert (HAB : Rabs (A * B) = P) by (unfold P; apply Rabs_mult).
    assert (Htri : Rabs (t - A * B) <= Rabs (t - a * b) + Rabs (a * b - A * B)).
    { replace (t - A * B) with ((t - a * b) + (a * b - A * B)) by ring.
      apply Rabs_triang. }
    set (M1 := (2*u + u*u) * P + (1+u) * e * q + e*e) in *.
    assert (HM1 : 0 <= M1).
    { unfold M1.
      assert (0 <= (2*u + u*u) * P) by (apply Rmult_le_pos; nra).
      assert (0 <= (1+u) * e * q)
        by (apply Rmult_le_pos; [apply Rmult_le_pos; nra | exact Hq]).
      assert (0 <= e * e) by nra.
      lra. }
    assert (Hab2 : Rabs (a * b) <= P + M1) by lra.
    assert (uab : u * Rabs (a * b) <= u * (P + M1))
      by (apply Rmult_le_compat_l; [exact Hu0 | exact Hab2]).
    assert (Hs0 : Rabs (t - A * B) <= u * (P + M1) + e + M1) by lra.
    assert (Hs : Rabs (t - A * B) <= u * P + (1 + u) * M1 + e).
    { eapply Rle_trans; [exact Hs0|]. right. ring. }
    eapply Rle_trans; [exact Hs|].
    unfold M1.
    assert (c1 : 0 <= u * (3 - (1+u)*(2+u))) by nra.
    assert (c2 : 0 <= 2 - (1+u)*(1+u)) by nra.
    assert (c3 : 0 <= 1 - (1+u)*e) by nra.
    assert (f1 : 0 <= P * (u * (3 - (1+u)*(2+u)))) by (apply Rmult_le_pos; assumption).
    assert (f2 : 0 <= (e * q) * (2 - (1+u)*(1+u)))
      by (apply Rmult_le_pos; [apply Rmult_le_pos; assumption | exact c2]).
    assert (f3 : 0 <= e * (1 - (1+u)*e)) by (apply Rmult_le_pos; assumption).
    nra.
  Qed.

  Lemma chain : forall A B C Dd a b c d t1 t2 Dh,
    Rabs (a - A) <= u * Rabs A + e -> Rabs (b - B) <= u * Rabs B + e ->
    Rabs (c - C) <= u * Rabs C + e -> Rabs (d - Dd) <= u * Rabs Dd + e ->
    Rabs (t1 - a * b) <= u * Rabs (a * b) + e ->
    Rabs (t2 - c * d) <= u * Rabs (c * d) + e ->
    Rabs (Dh - (t1 - t2)) <= u * Rabs (t1 - t2) + e ->
    Rabs (Dh - (A * B - C * Dd))
      <= 6 * u * (Rabs (A * B) + Rabs (C * Dd))
         + 6 * e * (Rabs A + Rabs B + Rabs C + Rabs Dd + 1).
  Proof.
    intros A B C Dd a b c d t1 t2 Dh Ha Hb Hc Hd Ht1 Ht2 Ho.
    pose proof (prod_err a A b B t1 Ha Hb Ht1) as R1.
    pose proof (prod_err c C d Dd t2 Hc Hd Ht2) as R2.
    pose proof (Rabs_pos A) as PA. pose proof (Rabs_pos B) as PB.
    pose proof (Rabs_pos C) as PC. pose proof (Rabs_pos Dd) as PD.
    rewrite <- (Rabs_mult A B) in R1. rewrite <- (Rabs_mult C Dd) in R2.
    set (P1 := Rabs (A * B)) in *. set (P2 := Rabs (C * Dd)) in *.
    set (r1 := Rabs (t1 - A * B)) in *. set (r2 := Rabs (t2 - C * Dd)) in *.
    set (q1 := Rabs A + Rabs B) in *. set (q2 := Rabs C + Rabs Dd) in *.
    assert (HP1 : 0 <= P1) by apply Rabs_pos.
    assert (HP2 : 0 <= P2) by apply Rabs_pos.
    assert (Hr1 : 0 <= r1) by apply Rabs_pos.
    assert (Hr2 : 0 <= r2) by apply Rabs_pos.
    (* |(t1 - t2) - D| <= r1 + r2 *)
    assert (Hd1 : Rabs ((t1 - t2) - (A * B - C * Dd)) <= r1 + r2).
    { replace ((t1 - t2) - (A * B - C * Dd))
        with ((t1 - A * B) + - (t2 - C * Dd)) by ring.
      eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. unfold r1, r2. lra. }
    assert (HD : Rabs (A * B - C * Dd) <= P1 + P2).
    { eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. unfold P1, P2. lra. }
    assert (HT : Rabs (t1 - t2) <= P1 + P2 + (r1 + r2)).
    { replace (t1 - t2)
        with ((A * B - C * Dd) + ((t1 - t2) - (A * B - C * Dd))) by ring.
      eapply Rle_trans; [apply Rabs_triang|]. lra. }
    assert (Hmain : Rabs (Dh - (A * B - C * Dd))
                    <= u * (P1 + P2) + (1 + u) * (r1 + r2) + e).
    { replace (Dh - (A * B - C * Dd))
        with ((Dh - (t1 - t2)) + ((t1 - t2) - (A * B - C * Dd))) by ring.
      eapply Rle_trans; [apply Rabs_triang|].
      assert (uT : u * Rabs (t1 - t2) <= u * (P1 + P2 + (r1 + r2)))
        by (apply Rmult_le_compat_l; assumption).
      nra. }
    assert (Hr : (1 + u) * (r1 + r2)
                 <= (1 + u) * (4 * u * (P1 + P2) + 2 * e * (q1 + q2) + 4 * e)).
    { apply Rmult_le_compat_l; [lra|]. lra. }
    set (S := P1 + P2) in *. set (m := q1 + q2) in *.
    assert (HS : 0 <= S) by (unfold S; lra).
    assert (Hm : 0 <= m) by (unfold m, q1, q2; lra).
    assert (a1 : u * (u * S) <= u * S).
    { assert (0 <= u * S) by (apply Rmult_le_pos; assumption).
      nra. }
    assert (a2 : u * (e * m) <= e * m).
    { assert (0 <= e * m) by (apply Rmult_le_pos; assumption). nra. }
    assert (a3 : u * e <= e) by nra.
    assert (HuS : 0 <= u * S) by (apply Rmult_le_pos; assumption).
    assert (Hem : 0 <= e * m) by (apply Rmult_le_pos; assumption).
    unfold m, q1, q2 in *.
    nra.
  Qed.
End Chain.

(* -------------------------------------------------------------------------- *)
(* §3  The binary64 orient2d chain.                                           *)
(* -------------------------------------------------------------------------- *)
Definition o2_A (P0 P1 Q : BPoint) : R := B2R (bx P1) - B2R (bx P0).
Definition o2_B (P0 P1 Q : BPoint) : R := B2R (by_ Q) - B2R (by_ P0).
Definition o2_C (P0 P1 Q : BPoint) : R := B2R (bx Q) - B2R (bx P0).
Definition o2_Dd (P0 P1 Q : BPoint) : R := B2R (by_ P1) - B2R (by_ P0).

Definition o2_E (P0 P1 Q : BPoint) : R :=
  6 * b64ae_u * (Rabs (o2_A P0 P1 Q * o2_B P0 P1 Q)
                 + Rabs (o2_C P0 P1 Q * o2_Dd P0 P1 Q))
  + 6 * b64ae_e0 * (Rabs (o2_A P0 P1 Q) + Rabs (o2_B P0 P1 Q)
                    + Rabs (o2_C P0 P1 Q) + Rabs (o2_Dd P0 P1 Q) + 1).

Lemma cross_R_BP_o2 : forall P0 P1 Q,
  cross_R_BP P0 P1 Q = o2_A P0 P1 Q * o2_B P0 P1 Q - o2_C P0 P1 Q * o2_Dd P0 P1 Q.
Proof. intros. reflexivity. Qed.

Theorem b64_orient2d_forward_error : forall P0 P1 Q : BPoint,
  b64_orient2d_safe P0 P1 Q ->
  (Binary.is_finite prec emax (b64_orient2d P0 P1 Q) = true) /\
  (Rabs (B2R (b64_orient2d P0 P1 Q) - cross_R_BP P0 P1 Q) <= o2_E P0 P1 Q).
Proof.
  intros P0 P1 Q Hs.
  split; [exact (b64_orient2d_finite_of_safe _ _ _ Hs)|].
  destruct Hs as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  destruct (b64_minus_correct _ _ S1) as [E1 _].
  destruct (b64_minus_correct _ _ S2) as [E2 _].
  destruct (b64_minus_correct _ _ S3) as [E3 _].
  destruct (b64_minus_correct _ _ S4) as [E4 _].
  destruct (b64_mult_correct _ _ S5) as [E5 _].
  destruct (b64_mult_correct _ _ S6) as [E6 _].
  destruct (b64_minus_correct _ _ S7) as [E7 _].
  unfold b64_orient2d, Orientation_b64.b64_orient2d_terms. cbn iota.
  set (dx1 := b64_minus (bx P1) (bx P0)) in *.
  set (dy1 := b64_minus (by_ Q) (by_ P0)) in *.
  set (dx2 := b64_minus (bx Q) (bx P0)) in *.
  set (dy2 := b64_minus (by_ P1) (by_ P0)) in *.
  set (t1 := b64_mult dx1 dy1) in *.
  set (t2 := b64_mult dx2 dy2) in *.
  rewrite cross_R_BP_o2.
  destruct b64ae_u_small as [Hu0 Hu1]. destruct b64ae_e0_small as [He0 He1].
  pose proof (chain b64ae_u b64ae_e0 (Rlt_le _ _ Hu0) Hu1 (Rlt_le _ _ He0) He1
    (o2_A P0 P1 Q) (o2_B P0 P1 Q) (o2_C P0 P1 Q) (o2_Dd P0 P1 Q)
    (B2R dx1) (B2R dy1) (B2R dx2) (B2R dy2) (B2R t1) (B2R t2)
    (B2R (b64_minus t1 t2))) as H.
  unfold o2_E.
  apply H.
  - rewrite E1. apply b64ae_round_err.
  - rewrite E2. apply b64ae_round_err.
  - rewrite E3. apply b64ae_round_err.
  - rewrite E4. apply b64ae_round_err.
  - rewrite E5. apply b64ae_round_err.
  - rewrite E6. apply b64ae_round_err.
  - rewrite E7. apply b64ae_round_err.
Qed.

(* R2: premise 1 (forward error) discharged; premise 2 (separation) is the
   remaining hypothesis. *)
Theorem b64_orient2d_R2 : forall P0 P1 Q : BPoint,
  b64_orient2d_safe P0 P1 Q ->
  o2_E P0 P1 Q < Rabs (cross_R_BP P0 P1 Q) ->
  Rcompare (B2R (b64_orient2d P0 P1 Q)) 0 = Rcompare (cross_R_BP P0 P1 Q) 0.
Proof.
  intros P0 P1 Q Hs Hsep.
  destruct (b64_orient2d_forward_error P0 P1 Q Hs) as [_ Herr].
  exact (sign_of_error_bound _ _ _ Herr Hsep).
Qed.

Print Assumptions sign_of_error_bound.
Print Assumptions b64_orient2d_forward_error.
Print Assumptions b64_orient2d_R2.

(* -------------------------------------------------------------------------- *)
(* §4  Premise 2 (separation): where it holds and where it provably fails.   *)
(* -------------------------------------------------------------------------- *)
Lemma o2_u_val : b64ae_u * 9007199254740992 = 1.
Proof.
  unfold b64ae_u.
  assert (H : bpow radix2 (-53) * bpow radix2 53 = 1)
    by (rewrite <- bpow_plus; simpl; reflexivity).
  assert (H2 : bpow radix2 53 = 9007199254740992).
  { rewrite bpow_radix2_eq_IZR_pow by lia. simpl. lra. }
  rewrite <- H2. exact H.
Qed.

Lemma o2_e_small : b64ae_e0 <= / 1000000000000.
Proof.
  unfold b64ae_e0.
  apply Rle_trans with (bpow radix2 (-100)).
  - apply bpow_le. lia.
  - replace (-100)%Z with (-(100))%Z by reflexivity. rewrite bpow_opp.
    assert (H2 : bpow radix2 100 >= 1000000000000)
     by (rewrite bpow_radix2_eq_IZR_pow by lia; simpl; lra).
    apply Rinv_le_contravar; lra.
Qed.

Lemma Zabs_Rabs_le : forall (z B : Z), (Z.abs z <= B)%Z -> Rabs (IZR z) <= IZR B.
Proof. intros. rewrite <- abs_IZR. apply IZR_le. exact H. Qed.

(* Separation holds on the tight integer grid |n| <= 2^22 (so |A|,|B|,|C|,|Dd| <= 2^23). *)
Theorem o2_separation_tight_grid :
  forall (P0 P1 Q : BPoint) (x0 y0 x1 y1 xq yq : Z),
    B2R (bx P0) = IZR x0 -> B2R (by_ P0) = IZR y0 ->
    B2R (bx P1) = IZR x1 -> B2R (by_ P1) = IZR y1 ->
    B2R (bx Q) = IZR xq -> B2R (by_ Q) = IZR yq ->
    (Z.abs x0 <= 4194304)%Z -> (Z.abs y0 <= 4194304)%Z ->
    (Z.abs x1 <= 4194304)%Z -> (Z.abs y1 <= 4194304)%Z ->
    (Z.abs xq <= 4194304)%Z -> (Z.abs yq <= 4194304)%Z ->
    cross_R_BP P0 P1 Q <> 0 ->
    o2_E P0 P1 Q < Rabs (cross_R_BP P0 P1 Q).
Proof.
  intros P0 P1 Q x0 y0 x1 y1 xq yq Hx0 Hy0 Hx1 Hy1 Hxq Hyq Bx0 By0 Bx1 By1 Bxq Byq Hne.
  set (a := (x1 - x0)%Z). set (b := (yq - y0)%Z).
  set (c := (xq - x0)%Z). set (d := (y1 - y0)%Z).
  set (Z := (a * b - c * d)%Z).
  assert (hA : o2_A P0 P1 Q = IZR a)
    by (unfold o2_A, a; rewrite Hx1, Hx0, minus_IZR; reflexivity).
  assert (hB : o2_B P0 P1 Q = IZR b)
    by (unfold o2_B, b; rewrite Hyq, Hy0, minus_IZR; reflexivity).
  assert (hC : o2_C P0 P1 Q = IZR c)
    by (unfold o2_C, c; rewrite Hxq, Hx0, minus_IZR; reflexivity).
  assert (hDd : o2_Dd P0 P1 Q = IZR d)
    by (unfold o2_Dd, d; rewrite Hy1, Hy0, minus_IZR; reflexivity).
  assert (hD : cross_R_BP P0 P1 Q = IZR Z).
  { rewrite cross_R_BP_o2, hA, hB, hC, hDd. unfold Z.
    rewrite minus_IZR, !mult_IZR. reflexivity. }
  rewrite hD in *. unfold o2_E. rewrite hA, hB, hC, hDd.
  assert (Ha : Rabs (IZR a) <= 8388608)
    by (apply (Zabs_Rabs_le a 8388608); unfold a; lia).
  assert (Hb : Rabs (IZR b) <= 8388608)
    by (apply (Zabs_Rabs_le b 8388608); unfold b; lia).
  assert (Hc : Rabs (IZR c) <= 8388608)
    by (apply (Zabs_Rabs_le c 8388608); unfold c; lia).
  assert (Hd : Rabs (IZR d) <= 8388608)
    by (apply (Zabs_Rabs_le d 8388608); unfold d; lia).
  assert (HZ : 1 <= Rabs (IZR Z)).
  { rewrite <- abs_IZR.
    replace 1 with (IZR 1) by reflexivity. apply IZR_le.
    assert (Z <> 0%Z) by (intro H0; apply Hne; rewrite H0; reflexivity).
    lia. }
  pose proof o2_u_val as Hu. pose proof o2_e_small as He.
  pose proof (Rabs_pos (IZR a)) as Pa. pose proof (Rabs_pos (IZR b)) as Pb.
  pose proof (Rabs_pos (IZR c)) as Pc. pose proof (Rabs_pos (IZR d)) as Pd.
  destruct b64ae_u_small as [Hu0 _]. destruct b64ae_e0_small as [He0 _].
  rewrite !Rabs_mult.
  assert (Pab : Rabs (IZR a) * Rabs (IZR b) <= 70368744177664)
    by (replace 70368744177664 with (8388608 * 8388608) by lra;
        apply Rmult_le_compat; lra).
  assert (Pcd : Rabs (IZR c) * Rabs (IZR d) <= 70368744177664)
    by (replace 70368744177664 with (8388608 * 8388608) by lra;
        apply Rmult_le_compat; lra).
  assert (U : b64ae_u * (Rabs (IZR a) * Rabs (IZR b) + Rabs (IZR c) * Rabs (IZR d))
              <= b64ae_u * 140737488355328)
    by (apply Rmult_le_compat_l; lra).
  assert (Em : b64ae_e0 * (Rabs (IZR a) + Rabs (IZR b) + Rabs (IZR c) + Rabs (IZR d) + 1)
               <= / 1000000000000 * 33554433).
  { apply Rmult_le_compat; [lra | lra | exact He | lra]. }
  nra.
Qed.

(* ---- Negative: the separation premise fails at the top of the corpus's own
   integer window |n| <= 2^25 (D = -1, yet o2_E >= 1.49). ---- *)
Definition o2Z (m : Z) : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64
    mode_NE m 0 false.

Lemma o2Z_R : forall m : Z, (Z.abs m <= 2 ^ 53)%Z ->
  B2R (o2Z m) = IZR m /\ Binary.is_finite prec emax (o2Z m) = true.
Proof.
  intros m Hm. unfold o2Z.
  pose proof (Binary.binary_normalize_correct prec emax
                prec_gt_0_b64 prec_lt_emax_b64 mode_NE m 0 false) as H.
  assert (HF2R : F2R (Float radix2 m 0) = IZR m) by (unfold F2R; simpl; lra).
  rewrite HF2R in H.
  assert (Hround : Generic_fmt.round radix2 (SpecFloat.fexp prec emax)
                     (round_mode mode_NE) (IZR m) = IZR m).
  { apply Generic_fmt.round_generic; [apply valid_rnd_round_mode |].
    apply generic_format_IZR_le_bpow_prec. unfold prec; lia. }
  rewrite Hround in H.
  assert (Hbnd : Rabs (IZR m) < bpow radix2 emax).
  { rewrite <- abs_IZR.
    apply (Rle_lt_trans _ (bpow radix2 53)).
    - rewrite bpow_radix2_eq_IZR_pow by lia. apply IZR_le. exact Hm.
    - apply bpow_lt; unfold emax; lia. }
  apply Rlt_bool_true in Hbnd. rewrite Hbnd in H.
  destruct H as [HB2R [Hfin _]]. split; assumption.
Qed.

Lemma o2Z_int_safe : forall m : Z, (Z.abs m <= 2 ^ 25)%Z -> coord_int_safe (o2Z m).
Proof.
  intros m Hm. destruct (o2Z_R m ltac:(lia)) as [HR Hf].
  split; [exact Hf | exists m; split; [exact HR | exact Hm]].
Qed.

Definition w_n : Z := 33554431%Z.
Definition wP0 : BPoint := mkBP (o2Z 0) (o2Z 0).
Definition wP1 : BPoint := mkBP (o2Z w_n) (o2Z (w_n - 1)).
Definition wQ  : BPoint := mkBP (o2Z (w_n - 1)) (o2Z (w_n - 2)).

Theorem o2_separation_fails_on_int_grid :
  orient2d_inputs_int_safe wP0 wP1 wQ /\
  cross_R_BP wP0 wP1 wQ <> 0 /\
  ~ (o2_E wP0 wP1 wQ < Rabs (cross_R_BP wP0 wP1 wQ)).
Proof.
  split.
  { unfold orient2d_inputs_int_safe, wP0, wP1, wQ, w_n; cbn [bx by_].
    repeat split; apply o2Z_int_safe; vm_compute; discriminate. }
  assert (R0 : forall m : Z, (Z.abs m <= 2 ^ 53)%Z -> B2R (o2Z m) = IZR m)
    by (intros m Hm; exact (proj1 (o2Z_R m Hm))).
  assert (hA : o2_A wP0 wP1 wQ = IZR w_n)
    by (unfold o2_A, wP0, wP1, w_n; cbn [bx by_];
        rewrite !R0 by (vm_compute; discriminate); simpl; lra).
  assert (hB : o2_B wP0 wP1 wQ = IZR (w_n - 2))
    by (unfold o2_B, wP0, wQ, w_n; cbn [bx by_];
        rewrite !R0 by (vm_compute; discriminate); simpl; lra).
  assert (hC : o2_C wP0 wP1 wQ = IZR (w_n - 1))
    by (unfold o2_C, wP0, wQ, w_n; cbn [bx by_];
        rewrite !R0 by (vm_compute; discriminate); simpl; lra).
  assert (hDd : o2_Dd wP0 wP1 wQ = IZR (w_n - 1))
    by (unfold o2_Dd, wP0, wP1, w_n; cbn [bx by_];
        rewrite !R0 by (vm_compute; discriminate); simpl; lra).
  assert (hD : cross_R_BP wP0 wP1 wQ = -1).
  { rewrite cross_R_BP_o2, hA, hB, hC, hDd. unfold w_n.
    rewrite <- !mult_IZR, <- minus_IZR. vm_compute. reflexivity. }
  rewrite hD. split.
  - lra.
  - intro H. unfold o2_E in H. rewrite hA, hB, hC, hDd in H.
    pose proof o2_u_val as Hu. destruct b64ae_u_small as [Hu0 _].
    destruct b64ae_e0_small as [He0 _].
    unfold w_n in H.
    assert (E1 : Rabs (-1) = 1) by (rewrite Rabs_left by lra; lra).
    rewrite E1 in H.
    assert (key : (2000000000000000 <=
                   33554431 * (33554431 - 2) + (33554431 - 1) * (33554431 - 1))%Z)
      by (vm_compute; discriminate).
    apply IZR_le in key. rewrite plus_IZR, !mult_IZR in key.
    assert (N1 : 0 <= IZR 33554431) by (apply IZR_le; lia).
    assert (N2 : 0 <= IZR (33554431 - 2)) by (apply IZR_le; lia).
    assert (N3 : 0 <= IZR (33554431 - 1)) by (apply IZR_le; lia).
    rewrite !Rabs_mult, !Rabs_pos_eq in H by assumption.
    assert (Ms : 0 <= b64ae_e0 * (Rabs (IZR 33554431) + Rabs (IZR (33554431 - 2))
                  + Rabs (IZR (33554431 - 1)) + Rabs (IZR (33554431 - 1)) + 1)).
    { apply Rmult_le_pos; [lra|].
      pose proof (Rabs_pos (IZR 33554431)). pose proof (Rabs_pos (IZR (33554431 - 2))).
      pose proof (Rabs_pos (IZR (33554431 - 1))). lra. }
    assert (Us : b64ae_u * 2000000000000000 <=
                 b64ae_u * (IZR 33554431 * IZR (33554431 - 2)
                            + IZR (33554431 - 1) * IZR (33554431 - 1)))
      by (apply Rmult_le_compat_l; lra).
    nra.
Qed.

Print Assumptions o2_separation_tight_grid.
Print Assumptions o2_separation_fails_on_int_grid.
