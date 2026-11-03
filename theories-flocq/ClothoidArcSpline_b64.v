(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ClothoidArcSpline_b64
   ----------------------------------------------------------------------------
   binary64 face of the arc-spline contract of theories/ClothoidArcSpline.v
   (heading-interpolating; the window end is not interpolated, see
   ClothoidArcSpline.cas_end_gap).

   1. Gate (unconditional).  The round-to-nearest-even gate
        fl( fl(fl(L*L)*L) * (1 + 2^-49) ) <= fl(fl(fl(fl(fl(8*A)*A)*n)*n)*eps)
      is sound for L^3 <= 8 A^2 n^2 eps (`cas_b64_gate_sound`).  The margin
      1 + 2^-49 = 1 + 16u absorbs the eight roundings
      ((1 + u)^5 <= (1 + 2^-49) (1 - u)^3, u = 2^-53).  Inputs finite in
      [2^-100, 2^100]; every intermediate stays in [2^-1000, 2^1000], so
      relative_error_N_FLT applies per op.  The bound decreases in A and N,
      so a computed A or n that rounded DOWN may be used:
      B2R A <= A, B2R n <= N (`cas_b64_arc_spline_contract`; two arcs with
      the fixed constant cas_b64_two: `cas_b64_two_arc_contract`).

   2. Points (conditional on an oracle).  The binary64 evaluator shoots
      the spline forward: start(k+1) = frame(start(k), T_k, X_k, Y_k) with
      four RNE products and two RNE sums per step (`cas_b64_frame`).  The
      transcendental inputs are the oracle `CasB64ArcOracle`: the Fresnel
      start P(a) within etaP, node tangents T(x_k) within tau, and the
      local arc coordinates (X, Y) of piece k at lengths x in [0, h] within
      eta.  Given any oracle, every computed point is within
        eps + etaP + N (tau h + (1 + tau) eta + 2 rho)
      of the clothoid, rho = 8 u M + 4 * 2^-1075 the per-step rounding at
      coordinate scale M (`cas_b64_points_contract`): frame rounding and the
      N-step accumulation are proved, not assumed.

   QED / QEX (ticket_0007_clothoid_arc_spline_qed_or_qex): QED for (1) and
   for (2) as a theorem over every oracle.  QEX: no `CasB64ArcOracle`
   inhabitant exists in the corpus -- Flocq has no sin / cos, IEEE 754 does
   not require them correctly rounded, and there is no binary64 Fresnel
   evaluator.  That record is the named missing constructor.
   claimId: 0007-clothoid-arc-spline.  witness: cas_b64_points_contract.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib B64_AbsErr.
From NTS.Proofs Require Import Distance SheetHenClothoidCore ClothoidTangent ClothoidArcSpline.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* Constants.                                                                 *)
(* -------------------------------------------------------------------------- *)

(* 8 = 2^52 * 2^-49. *)
Definition cas_b64_eight : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-49) eq_refl.
(* 1 + 2^-49 = (2^52 + 2^3) * 2^-52. *)
Definition cas_b64_margin : binary64 :=
  Binary.B754_finite prec emax false 4503599627370504 (-52) eq_refl.

Lemma cas_b64_eight_R : B2R cas_b64_eight = 8 /\ fin cas_b64_eight = true.
Proof.
  split; [|reflexivity].
  unfold cas_b64_eight. cbn [Binary.B2R]. unfold F2R. cbn. lra.
Qed.

(* 2 = 2^52 * 2^-51. *)
Definition cas_b64_two : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-51) eq_refl.

Lemma cas_b64_two_R : B2R cas_b64_two = 2 /\ fin cas_b64_two = true.
Proof.
  split; [|reflexivity].
  unfold cas_b64_two. cbn [Binary.B2R]. unfold F2R. cbn. lra.
Qed.

Lemma cas_b64_margin_R :
  B2R cas_b64_margin = 1 + bpow radix2 (-49) /\ fin cas_b64_margin = true.
Proof.
  split; [|reflexivity].
  unfold cas_b64_margin. cbn [Binary.B2R]. unfold F2R. cbn. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* One rounded product of positive normal-range operands.                    *)
(* -------------------------------------------------------------------------- *)

Lemma cas_b64_mult_pos : forall x y ex ey,
  fin x = true -> fin y = true ->
  (0 <= ex)%Z -> (0 <= ey)%Z -> (ex + ey + 1 <= 1000)%Z ->
  bpow radix2 (- ex) <= B2R x <= bpow radix2 ex ->
  bpow radix2 (- ey) <= B2R y <= bpow radix2 ey ->
  fin (b64_mult x y) = true /\
  B2R x * B2R y * (1 - b64ae_u) <= B2R (b64_mult x y)
    <= B2R x * B2R y * (1 + b64ae_u) /\
  bpow radix2 (- (ex + ey + 1)) <= B2R (b64_mult x y)
    <= bpow radix2 (ex + ey + 1).
Proof.
  intros x y ex ey Fx Fy Hex Hey Hsum [Hx0 Hx1] [Hy0 Hy1].
  set (z := B2R x * B2R y).
  assert (Hz0 : bpow radix2 (- (ex + ey)) <= z).
  { unfold z. replace (- (ex + ey))%Z with (- ex + - ey)%Z by lia.
    rewrite bpow_plus. apply Rmult_le_compat; try apply bpow_ge_0; assumption. }
  assert (Hz1 : z <= bpow radix2 (ex + ey)).
  { unfold z. rewrite bpow_plus.
    pose proof (bpow_ge_0 radix2 (- ex)). pose proof (bpow_ge_0 radix2 (- ey)).
    apply Rmult_le_compat; lra. }
  assert (Hzp : 0 < z) by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact Hz0]).
  assert (Habs : Rabs z <= bpow radix2 (ex + ey)) by (rewrite Rabs_pos_eq; lra).
  assert (Hround : Rabs (b64_round z) <= bpow radix2 (ex + ey)).
  { apply b64_round_abs_le_bpow; [unfold emax; lia | exact Habs]. }
  assert (Hsafe : b64_safe Rmult x y).
  { split; [exact Fx|]. split; [exact Fy|].
    eapply Rle_lt_trans; [exact Hround|]. apply bpow_lt. unfold emax. lia. }
  destruct (b64_mult_correct x y Hsafe) as [HB HF].
  fold z in HB.
  assert (Hrel : Rabs (b64_round z - z) <= b64ae_u * Rabs z).
  { assert (Hn : bpow radix2 (3 - emax - prec + prec - 1) <= Rabs z).
    { rewrite Rabs_pos_eq by lra. eapply Rle_trans; [|exact Hz0].
      apply bpow_le. unfold emax, prec. lia. }
    pose proof (relative_error_N_FLT radix2 (3 - emax - prec) prec
                  prec_gt_0_b64 (fun t => negb (Z.even t)) z Hn) as H.
    replace b64ae_u with (/ 2 * bpow radix2 (- prec + 1)).
    - exact H.
    - unfold b64ae_u, prec.
      replace (/ 2) with (bpow radix2 (-1)) by reflexivity.
      rewrite <- bpow_plus. f_equal. }
  rewrite (Rabs_pos_eq z) in Hrel by lra.
  apply Rabs_le_inv in Hrel.
  pose proof b64ae_u_small as Hu.
  split; [exact HF|]. rewrite HB. split; [lra|].
  split.
  - replace (- (ex + ey + 1))%Z with (- (ex + ey) + -1)%Z by lia.
    rewrite bpow_plus.
    assert (E : bpow radix2 (-1) = / 2) by reflexivity.
    rewrite E. nra.
  - rewrite bpow_plus.
    assert (E : bpow radix2 1 = 2) by reflexivity.
    rewrite E. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The gate.                                                                  *)
(* -------------------------------------------------------------------------- *)

Definition cas_b64_gate (L A n eps : binary64) : bool :=
  b64_le
    (b64_mult (b64_mult (b64_mult L L) L) cas_b64_margin)
    (b64_mult (b64_mult (b64_mult (b64_mult (b64_mult cas_b64_eight A) A) n) n)
       eps).

Definition cas_b64_in_range (x : binary64) : Prop :=
  fin x = true /\ bpow radix2 (-100) <= B2R x <= bpow radix2 100.

Lemma cas_round_margin :
  (1 + b64ae_u) * (1 + b64ae_u) * (1 + b64ae_u) * (1 + b64ae_u) * (1 + b64ae_u)
  <= (1 + bpow radix2 (-49)) * ((1 - b64ae_u) * (1 - b64ae_u) * (1 - b64ae_u)).
Proof.
  assert (E : bpow radix2 (-49) = 16 * b64ae_u).
  { unfold b64ae_u. replace (-49)%Z with (4 + -53)%Z by lia.
    rewrite bpow_plus. reflexivity. }
  rewrite E. pose proof b64ae_u_small as [H0 H1].
  assert (Hlo : (1 + 13 * b64ae_u - 51 * (b64ae_u * b64ae_u))
                <= (1 + 16 * b64ae_u) * ((1 - b64ae_u) * (1 - b64ae_u) * (1 - b64ae_u)))
    by nra.
  assert (Hhi : (1 + b64ae_u) * (1 + b64ae_u) * (1 + b64ae_u) * (1 + b64ae_u) * (1 + b64ae_u)
                <= 1 + 5 * b64ae_u + 11 * (b64ae_u * b64ae_u)).
  { assert (Hc : b64ae_u * b64ae_u <= b64ae_u / 1000) by nra.
    assert (Hc2 : b64ae_u * b64ae_u * b64ae_u <= b64ae_u * b64ae_u / 1000) by nra.
    assert (Hc3 : b64ae_u * b64ae_u * b64ae_u * b64ae_u <= b64ae_u * b64ae_u / 1000) by nra.
    assert (Hc4 : b64ae_u * b64ae_u * b64ae_u * b64ae_u * b64ae_u <= b64ae_u * b64ae_u / 1000)
      by nra.
    nra. }
  nra.
Qed.

(* WITNESS {"claimId":"0007-clothoid-arc-spline","topic":"curves","lemma":"cas_b64_gate_sound","title":"The binary64 round-to-nearest tolerance gate fl(L^3 (1 + 2^-49)) <= fl(8 A^2 n^2 eps) implies the real L^3 <= 8 A^2 n^2 eps on finite inputs in [2^-100, 2^100]","file":"theories-flocq/ClothoidArcSpline_b64.v","witness":"cas_b64_gate_sound","board":"ADR-0007"} *)
Theorem cas_b64_gate_sound : forall L A n eps,
  cas_b64_in_range L -> cas_b64_in_range A ->
  cas_b64_in_range n -> cas_b64_in_range eps ->
  cas_b64_gate L A n eps = true ->
  B2R L * B2R L * B2R L <= 8 * (B2R A * B2R A) * (B2R n * B2R n) * B2R eps.
Proof.
  intros L A n eps [FL HL] [FA HA] [Fn Hn] [Fe He] Hg.
  destruct cas_b64_eight_R as [E8 F8].
  destruct cas_b64_margin_R as [EM FM].
  assert (H8 : bpow radix2 (- 3) <= B2R cas_b64_eight <= bpow radix2 3).
  { rewrite E8. cbn. lra. }
  assert (HM : bpow radix2 (- 1) <= B2R cas_b64_margin <= bpow radix2 1).
  { rewrite EM. split.
    - apply Rle_trans with 1;
        [replace (bpow radix2 (-1)) with (/ 2) by reflexivity; lra|].
      pose proof (bpow_ge_0 radix2 (-49)). lra.
    - assert (bpow radix2 (-49) <= 1) by (apply (bpow_le radix2 (-49) 0); lia).
      replace (bpow radix2 1) with 2 by reflexivity. lra. }
  pose proof b64ae_u_small as Hu.
  (* left: ((L*L)*L)*M *)
  destruct (cas_b64_mult_pos L L 100 100 FL FL ltac:(lia) ltac:(lia) ltac:(lia) HL HL)
    as [F1 [R1 B1]].
  destruct (cas_b64_mult_pos _ L 201 100 F1 FL ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(exact B1) HL) as [F2 [R2 B2]].
  destruct (cas_b64_mult_pos _ cas_b64_margin 302 1 F2 FM ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(exact B2) HM) as [F3 [R3 _]].
  (* right: ((((8*A)*A)*n)*n)*eps *)
  destruct (cas_b64_mult_pos cas_b64_eight A 3 100 F8 FA ltac:(lia) ltac:(lia)
              ltac:(lia) H8 HA) as [G1 [S1 C1]].
  destruct (cas_b64_mult_pos _ A 104 100 G1 FA ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(exact C1) HA) as [G2 [S2 C2]].
  destruct (cas_b64_mult_pos _ n 205 100 G2 Fn ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(exact C2) Hn) as [G3 [S3 C3]].
  destruct (cas_b64_mult_pos _ n 306 100 G3 Fn ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(exact C3) Hn) as [G4 [S4 C4]].
  destruct (cas_b64_mult_pos _ eps 407 100 G4 Fe ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(exact C4) He) as [G5 [S5 _]].
  unfold cas_b64_gate in Hg.
  pose proof (b64ae_le_true _ _ F3 G5 Hg) as Hle.
  set (l := B2R L). set (a := B2R A). set (m := B2R n). set (e := B2R eps).
  fold l in R1, R2. fold a in S1, S2. fold m in S3, S4. fold e in S5.
  rewrite E8 in S1. rewrite EM in R3.
  set (v := b64ae_u) in *.
  assert (Hl : 0 < l) by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact (proj1 HL)]).
  assert (Ha : 0 < a) by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact (proj1 HA)]).
  assert (Hm : 0 < m) by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact (proj1 Hn)]).
  assert (He0 : 0 < e) by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact (proj1 He)]).
  set (M := 1 + bpow radix2 (-49)).
  assert (HMp : 0 < M) by (unfold M; pose proof (bpow_gt_0 radix2 (-49)); lra).
  set (q1 := 1 - v). set (p1 := 1 + v).
  assert (Hq1 : 0 < q1) by (unfold q1; lra).
  assert (Hp1 : 0 < p1) by (unfold p1; lra).
  (* lower chain *)
  set (x1 := B2R (b64_mult L L)) in *.
  set (x2 := B2R (b64_mult (b64_mult L L) L)) in *.
  set (x3 := B2R (b64_mult (b64_mult (b64_mult L L) L) cas_b64_margin)) in *.
  assert (Lx1 : l * l * q1 <= x1) by (unfold q1; lra).
  assert (Lx2 : l * l * l * (q1 * q1) <= x2).
  { apply Rle_trans with (x1 * l * q1); [|unfold q1; lra].
    replace (l * l * l * (q1 * q1)) with ((l * l * q1) * l * q1) by ring.
    apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_r; lra. }
  assert (Lx3 : l * l * l * M * (q1 * q1 * q1) <= x3).
  { apply Rle_trans with (x2 * M * q1); [|unfold q1, M; lra].
    replace (l * l * l * M * (q1 * q1 * q1))
      with ((l * l * l * (q1 * q1)) * M * q1) by ring.
    apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_r; lra. }
  (* upper chain *)
  set (y1 := B2R (b64_mult cas_b64_eight A)) in *.
  set (y2 := B2R (b64_mult (b64_mult cas_b64_eight A) A)) in *.
  set (y3 := B2R (b64_mult (b64_mult (b64_mult cas_b64_eight A) A) n)) in *.
  set (y4 := B2R (b64_mult (b64_mult (b64_mult (b64_mult cas_b64_eight A) A) n) n))
    in *.
  set (y5 := B2R (b64_mult (b64_mult (b64_mult (b64_mult (b64_mult cas_b64_eight A)
                  A) n) n) eps)) in *.
  assert (Uy1 : y1 <= 8 * a * p1) by (unfold p1; lra).
  assert (Hy1 : 0 <= y1) by (unfold q1 in *; nra).
  assert (Uy2 : y2 <= 8 * a * a * (p1 * p1)).
  { apply Rle_trans with (y1 * a * p1); [unfold p1; lra|].
    replace (8 * a * a * (p1 * p1)) with ((8 * a * p1) * a * p1) by ring.
    apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_r; lra. }
  assert (Hy2 : 0 <= y2) by (unfold q1 in *; nra).
  assert (Uy3 : y3 <= 8 * a * a * m * (p1 * p1 * p1)).
  { apply Rle_trans with (y2 * m * p1); [unfold p1; lra|].
    replace (8 * a * a * m * (p1 * p1 * p1))
      with ((8 * a * a * (p1 * p1)) * m * p1) by ring.
    apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_r; lra. }
  assert (Hy3 : 0 <= y3) by (unfold q1 in *; nra).
  assert (Uy4 : y4 <= 8 * a * a * m * m * (p1 * p1 * p1 * p1)).
  { apply Rle_trans with (y3 * m * p1); [unfold p1; lra|].
    replace (8 * a * a * m * m * (p1 * p1 * p1 * p1))
      with ((8 * a * a * m * (p1 * p1 * p1)) * m * p1) by ring.
    apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_r; lra. }
  assert (Hy4 : 0 <= y4) by (unfold q1 in *; nra).
  assert (Uy5 : y5 <= 8 * a * a * m * m * e * (p1 * p1 * p1 * p1 * p1)).
  { apply Rle_trans with (y4 * e * p1); [unfold p1; lra|].
    replace (8 * a * a * m * m * e * (p1 * p1 * p1 * p1 * p1))
      with ((8 * a * a * m * m * (p1 * p1 * p1 * p1)) * e * p1) by ring.
    apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_r; lra. }
  (* combine *)
  pose proof cas_round_margin as Hmar. fold v M in Hmar. fold p1 q1 in Hmar.
  set (T := 8 * (a * a) * (m * m) * e).
  assert (HT : 0 < T) by (unfold T; repeat apply Rmult_lt_0_compat; lra).
  assert (Hchain : l * l * l * (M * (q1 * q1 * q1))
                   <= T * (p1 * p1 * p1 * p1 * p1)).
  { replace (l * l * l * (M * (q1 * q1 * q1)))
      with (l * l * l * M * (q1 * q1 * q1)) by ring.
    replace (T * (p1 * p1 * p1 * p1 * p1))
      with (8 * a * a * m * m * e * (p1 * p1 * p1 * p1 * p1)) by (unfold T; ring).
    lra. }
  assert (HK : 0 < M * (q1 * q1 * q1))
    by (apply Rmult_lt_0_compat; [lra | repeat apply Rmult_lt_0_compat; lra]).
  assert (Hlll : l * l * l * (M * (q1 * q1 * q1)) <= T * (M * (q1 * q1 * q1))).
  { eapply Rle_trans; [exact Hchain|].
    apply Rmult_le_compat_l; [lra | exact Hmar]. }
  apply Rmult_le_reg_r in Hlll; [|exact HK].
  exact Hlll.
Qed.


(* -------------------------------------------------------------------------- *)
(* 1. Gate composed with the R contract.                                      *)
(* -------------------------------------------------------------------------- *)

(* The bound decreases in A and N: rounded-down A, n are admissible. *)
Lemma cas_b64_gate_real : forall (c : ClothoidEgg) (a b : R) (N : nat)
    (L A n eps : binary64),
  a <= b ->
  cas_b64_in_range L -> cas_b64_in_range A ->
  cas_b64_in_range n -> cas_b64_in_range eps ->
  b - a <= B2R L -> B2R A <= cloth_A c -> B2R n <= INR N ->
  cas_b64_gate L A n eps = true ->
  (b - a) * (b - a) * (b - a)
    <= 8 * (cloth_A c * cloth_A c) * (INR N * INR N) * B2R eps.
Proof.
  intros c a b N L A n eps Hab RL RA Rn Re HLb HA Hn Hg.
  pose proof (cas_b64_gate_sound L A n eps RL RA Rn Re Hg) as Hs.
  assert (Pa : 0 < B2R A)
    by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact (proj1 (proj2 RA))]).
  assert (Pn : 0 < B2R n)
    by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact (proj1 (proj2 Rn))]).
  assert (Pe : 0 < B2R eps)
    by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact (proj1 (proj2 Re))]).
  assert (H0 : 0 <= b - a) by lra.
  apply Rle_trans with (B2R L * B2R L * B2R L).
  { apply Rmult_le_compat; [nra | lra | |exact HLb].
    apply Rmult_le_compat; lra. }
  eapply Rle_trans; [exact Hs|].
  apply Rmult_le_compat_r; [lra|].
  apply Rmult_le_compat; [nra | nra | |].
  - apply Rmult_le_compat_l; [lra|]. apply Rmult_le_compat; lra.
  - apply Rmult_le_compat; lra.
Qed.

Theorem cas_b64_arc_spline_contract :
  forall (c : ClothoidEgg) (a b : R) (N : nat) (L A n eps : binary64),
    cloth_wf c -> a <= b -> (N <> 0)%nat ->
    cas_b64_in_range L -> cas_b64_in_range A ->
    cas_b64_in_range n -> cas_b64_in_range eps ->
    b - a <= B2R L -> B2R A <= cloth_A c -> B2R n <= INR N ->
    cas_b64_gate L A n eps = true ->
    forall k u, (k < N)%nat ->
      cas_node a (cas_step a b N) k <= u <= cas_node a (cas_step a b N) (S k) ->
      dist (cloth_P c u) (cas_piece c a (cas_step a b N) k u) <= B2R eps.
Proof.
  intros c a b N L A n eps Hwf Hab HN RL RA Rn Re HLb HA Hn Hg k u Hk Hu.
  apply (cas_arc_spline_within_eps c a b N (B2R eps) Hwf Hab HN); [|exact Hk|exact Hu].
  apply (cas_b64_gate_real c a b N L A n eps); assumption.
Qed.

Lemma cas_b64_two_in_range : cas_b64_in_range cas_b64_two.
Proof.
  destruct cas_b64_two_R as [E F]. split; [exact F|]. rewrite E. split.
  - apply Rle_trans with 1; [|lra].
    replace 1 with (bpow radix2 0) by reflexivity. apply bpow_le. lia.
  - replace 2 with (bpow radix2 1) by reflexivity. apply bpow_le. lia.
Qed.

Theorem cas_b64_two_arc_contract :
  forall (c : ClothoidEgg) (a b : R) (L A eps : binary64),
    cloth_wf c -> a <= b ->
    cas_b64_in_range L -> cas_b64_in_range A -> cas_b64_in_range eps ->
    b - a <= B2R L -> B2R A <= cloth_A c ->
    cas_b64_gate L A cas_b64_two eps = true ->
    forall k u, (k < 2)%nat ->
      cas_node a (cas_step a b 2) k <= u <= cas_node a (cas_step a b 2) (S k) ->
      dist (cloth_P c u) (cas_piece c a (cas_step a b 2) k u) <= B2R eps.
Proof.
  intros c a b L A eps Hwf Hab RL RA Re HLb HA Hg.
  apply (cas_b64_arc_spline_contract c a b 2 L A cas_b64_two eps);
    try assumption.
  - lia.
  - exact cas_b64_two_in_range.
  - rewrite (proj1 cas_b64_two_R). cbn. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* 2b. One frame step in binary64.                                            *)
(* -------------------------------------------------------------------------- *)

Definition cas_bp (p : BPoint) : Point := mkPoint (B2R (bx p)) (B2R (by_ p)).

(* S + (tx, ty) * (X + i Y), four RNE products and two RNE sums per axis. *)
Definition cas_b64_frame (S T : BPoint) (X Y : binary64) : BPoint :=
  mkBP (b64_minus (b64_plus (bx S) (b64_mult (bx T) X)) (b64_mult (by_ T) Y))
       (b64_plus (b64_plus (by_ S) (b64_mult (by_ T) X)) (b64_mult (bx T) Y)).

(* Per-step rounding at coordinate scale M. *)
Definition cas_rho (M : R) : R := 8 * b64ae_u * M + 4 * b64ae_e0.

(* One axis: fl(fl(s + fl(t1 X)) +- fl(t2 Y)) against s + t1 X +- t2 Y. *)
Lemma cas_b64_axis : forall (plus : bool) s t1 X t2 Y C H,
  fin s = true -> fin t1 = true -> fin X = true -> fin t2 = true -> fin Y = true ->
  0 <= C -> 0 <= H ->
  Rabs (B2R s) <= C -> Rabs (B2R t1) <= 2 -> Rabs (B2R t2) <= 2 ->
  Rabs (B2R X) <= H -> Rabs (B2R Y) <= H ->
  C + 4 * H + 1 <= bpow radix2 998 ->
  let r := b64_plus s (b64_mult t1 X) in
  let q := b64_mult t2 Y in
  let o := if plus then b64_plus r q else b64_minus r q in
  let z := if plus then B2R s + B2R t1 * B2R X + B2R t2 * B2R Y
           else B2R s + B2R t1 * B2R X - B2R t2 * B2R Y in
  fin o = true /\ Rabs (B2R o - z) <= cas_rho (C + 4 * H + 1).
Proof.
  intros plus s t1 X t2 Y C H Fs Ft1 FX Ft2 FY HC HH Hs Ht1 Ht2 HX HY HM r q o z.
  set (M := C + 4 * H + 1) in *.
  assert (HMd : M = C + 4 * H + 1) by reflexivity.
  pose proof (bpow_gt_0 radix2 998) as Hb0.
  pose proof b64ae_u_small as [Hu0 Hu1]. pose proof b64ae_e0_small as [He0 He1].
  assert (Hb : bpow radix2 998 * 4 <= bpow radix2 1000).
  { replace 4 with (bpow radix2 2) by reflexivity. rewrite <- bpow_plus.
    apply bpow_le. lia. }
  assert (HM1 : 1 <= M) by (unfold M; lra).
  (* p = fl(t1 X) *)
  assert (B1 : Rabs (B2R t1 * B2R X) <= 2 * H) by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err t1 X Ft1 FX ltac:(lra)) as [Fp Ep].
  pose proof (b64ae_u_mul_le _ _ B1) as U1.
  set (p := b64_mult t1 X) in *.
  apply Rabs_le_inv in Ep. apply Rabs_le_inv in B1.
  assert (Hp : Rabs (B2R p) <= 3 * H + 1).
  { apply Rabs_le. assert (b64ae_u * (2 * H) <= H) by nra. lra. }
  (* r = fl(s + p) *)
  assert (B3 : Rabs (B2R s + B2R p) <= M).
  { eapply Rle_trans; [apply Rabs_triang|]. unfold M. lra. }
  destruct (b64ae_plus_err s p Fs Fp ltac:(lra)) as [Fr Er].
  pose proof (b64ae_u_mul_le _ _ B3) as U3.
  fold r in Fr, Er.
  apply Rabs_le_inv in Er.
  assert (Hr : Rabs (B2R r) <= 2 * M).
  { apply Rabs_le. apply Rabs_le_inv in B3. assert (b64ae_u * M <= M / 2) by nra.
    lra. }
  (* q = fl(t2 Y) *)
  assert (B2 : Rabs (B2R t2 * B2R Y) <= 2 * H) by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err t2 Y Ft2 FY ltac:(lra)) as [Fq Eq].
  pose proof (b64ae_u_mul_le _ _ B2) as U2.
  fold q in Fq, Eq.
  apply Rabs_le_inv in Eq. apply Rabs_le_inv in B2.
  assert (Hq : Rabs (B2R q) <= M).
  { apply Rabs_le. assert (b64ae_u * (2 * H) <= H) by nra. unfold M. lra. }
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in Hq.
  unfold o, z, cas_rho. fold M.
  destruct plus.
  - assert (B4 : Rabs (B2R r + B2R q) <= 3 * M)
      by (apply Rabs_le; lra).
    destruct (b64ae_plus_err r q Fr Fq ltac:(lra)) as [Fo Eo].
    pose proof (b64ae_u_mul_le _ _ B4) as U4.
    split; [exact Fo|]. apply Rabs_le_inv in Eo. apply Rabs_le.
    assert (b64ae_u * (2 * H) <= b64ae_u * M) by (apply Rmult_le_compat_l; unfold M; lra).
    assert (0 <= b64ae_u * M) by nra.
    lra.
  - assert (B4 : Rabs (B2R r - B2R q) <= 3 * M)
      by (apply Rabs_le; lra).
    destruct (b64ae_minus_err r q Fr Fq ltac:(lra)) as [Fo Eo].
    pose proof (b64ae_u_mul_le _ _ B4) as U4.
    split; [exact Fo|]. apply Rabs_le_inv in Eo. apply Rabs_le.
    assert (b64ae_u * (2 * H) <= b64ae_u * M) by (apply Rmult_le_compat_l; unfold M; lra).
    assert (0 <= b64ae_u * M) by nra.
    lra.
Qed.

Lemma cas_dist_le_coords : forall p q e, 0 <= e ->
  Rabs (px p - px q) <= e -> Rabs (py p - py q) <= e -> dist p q <= 2 * e.
Proof.
  intros p q e He Hx Hy. unfold dist, dist_sq.
  rewrite <- (sqrt_square (2 * e)) by lra. apply sqrt_le_1_alt.
  pose proof (Rsqr_le_abs_1 _ _ (Rle_trans _ _ _ Hx (Req_le _ _ (eq_sym (Rabs_pos_eq e He))))) as Ax.
  pose proof (Rsqr_le_abs_1 _ _ (Rle_trans _ _ _ Hy (Req_le _ _ (eq_sym (Rabs_pos_eq e He))))) as Ay.
  unfold Rsqr in Ax, Ay. nra.
Qed.

Lemma cas_coord_le_dist : forall p q,
  Rabs (px p - px q) <= dist p q /\ Rabs (py p - py q) <= dist p q.
Proof.
  intros p q. unfold dist, dist_sq.
  split; rewrite <- sqrt_Rsqr_abs; apply sqrt_le_1_alt; unfold Rsqr;
    pose proof (Rle_0_sqr (px p - px q)); pose proof (Rle_0_sqr (py p - py q));
    unfold Rsqr in *; lra.
Qed.

Lemma cas_b64_frame_err : forall S T X Y C H,
  fin (bx S) = true -> fin (by_ S) = true ->
  fin (bx T) = true -> fin (by_ T) = true -> fin X = true -> fin Y = true ->
  0 <= C -> 0 <= H ->
  Rabs (B2R (bx S)) <= C -> Rabs (B2R (by_ S)) <= C ->
  Rabs (B2R (bx T)) <= 2 -> Rabs (B2R (by_ T)) <= 2 ->
  Rabs (B2R X) <= H -> Rabs (B2R Y) <= H ->
  C + 4 * H + 1 <= bpow radix2 998 ->
  fin (bx (cas_b64_frame S T X Y)) = true /\
  fin (by_ (cas_b64_frame S T X Y)) = true /\
  dist (cas_bp (cas_b64_frame S T X Y))
       (cas_frame (cas_bp S) (B2R (bx T)) (B2R (by_ T)) (B2R X) (B2R Y))
    <= 2 * cas_rho (C + 4 * H + 1).
Proof.
  intros S T X Y C H FSx FSy FTx FTy FX FY HC HH HSx HSy HTx HTy HX HY HM.
  destruct (cas_b64_axis false (bx S) (bx T) X (by_ T) Y C H FSx FTx FX FTy FY
              HC HH HSx HTx HTy HX HY HM) as [Fo Eo].
  destruct (cas_b64_axis true (by_ S) (by_ T) X (bx T) Y C H FSy FTy FX FTx FY
              HC HH HSy HTy HTx HX HY HM) as [Fo' Eo'].
  cbn zeta iota in Fo, Eo, Fo', Eo'.
  split; [exact Fo|]. split; [exact Fo'|].
  apply cas_dist_le_coords.
  - unfold cas_rho. pose proof b64ae_u_small. pose proof b64ae_e0_small. nra.
  - exact Eo.
  - exact Eo'.
Qed.

(* -------------------------------------------------------------------------- *)
(* 2c. The oracle (named missing constructor) and the shot spline.            *)
(* -------------------------------------------------------------------------- *)

(* Everything transcendental the binary64 spline needs, with error bounds on
   the domain it is used on: the Fresnel start P(a), the node tangents
   T(x_k) (cos / sin of psi(x_k)), and the local coordinates of piece k at
   lengths in [0, h] (sin (kx) / k and (1 - cos (kx)) / k, curvature kappa_k
   included).  No inhabitant exists in the corpus: this is the QEX. *)
Record CasB64ArcOracle (c : ClothoidEgg) (a h : R) (N : nat) : Type :=
  mkCasB64ArcOracle {
  cao_S0 : BPoint;
  cao_T : nat -> BPoint;
  cao_X : nat -> binary64 -> binary64;
  cao_Y : nat -> binary64 -> binary64;
  cao_etaP : R;
  cao_tau : R;
  cao_eta : R;
  cao_S0_ok : fin (bx cao_S0) = true /\ fin (by_ cao_S0) = true /\
    dist (cas_bp cao_S0) (cloth_P c a) <= cao_etaP;
  cao_T_ok : forall k, (k < N)%nat ->
    fin (bx (cao_T k)) = true /\ fin (by_ (cao_T k)) = true /\
    dist (cas_bp (cao_T k))
         (mkPoint (cloth_vx c (cas_node a h k)) (cloth_vy c (cas_node a h k)))
      <= cao_tau;
  cao_XY_ok : forall k x, (k < N)%nat -> fin x = true -> 0 <= B2R x <= h ->
    fin (cao_X k x) = true /\ fin (cao_Y k x) = true /\
    dist (mkPoint (B2R (cao_X k x)) (B2R (cao_Y k x)))
         (mkPoint (cas_arc_X (cas_kap c (cas_node a h k) h) (B2R x))
                  (cas_arc_Y (cas_kap c (cas_node a h k) h) (B2R x)))
      <= cao_eta
}.

Arguments cao_S0 {c a h N}. Arguments cao_T {c a h N}.
Arguments cao_X {c a h N}. Arguments cao_Y {c a h N}.
Arguments cao_etaP {c a h N}. Arguments cao_tau {c a h N}.
Arguments cao_eta {c a h N}.
Arguments cao_S0_ok {c a h N}. Arguments cao_T_ok {c a h N}.
Arguments cao_XY_ok {c a h N}.

Fixpoint cas_b64_start {c a h N} (orc : CasB64ArcOracle c a h N)
    (hb : binary64) (k : nat) : BPoint :=
  match k with
  | O => cao_S0 orc
  | S j => cas_b64_frame (cas_b64_start orc hb j) (cao_T orc j)
             (cao_X orc j hb) (cao_Y orc j hb)
  end.

(* Point of piece k at local length x. *)
Definition cas_b64_point {c a h N} (orc : CasB64ArcOracle c a h N)
    (hb : binary64) (k : nat) (x : binary64) : BPoint :=
  cas_b64_frame (cas_b64_start orc hb k) (cao_T orc k)
    (cao_X orc k x) (cao_Y orc k x).

(* Error of one step: rounding + start offset + tangent + local coords. *)
Definition cas_step_err {c a h N} (orc : CasB64ArcOracle c a h N) (C0 : R) : R :=
  cao_tau orc * h + (1 + cao_tau orc) * cao_eta orc
  + 2 * cas_rho ((C0 + 1) + 4 * (h + cao_eta orc) + 1).

Section Shot.
Variables (c : ClothoidEgg) (a h : R) (N : nat).
Variable orc : CasB64ArcOracle c a h N.
Variables (hb : binary64) (C0 : R).
Hypothesis Hwf : cloth_wf c.
Hypothesis Hh : 0 <= h.
Hypothesis Hhb : fin hb = true /\ B2R hb = h.
Hypothesis Htau : 0 <= cao_tau orc <= 1.
Hypothesis Heta : 0 <= cao_eta orc.
Hypothesis HC0 : 0 <= C0.
(* the exact spline stays in the coordinate box [-C0, C0]^2 *)
Hypothesis Hbox : forall k, (k <= N)%nat ->
  Rabs (px (cas_start c a h k)) <= C0 /\ Rabs (py (cas_start c a h k)) <= C0.
(* the total budget is at most 1 and the scale is far from overflow *)
Hypothesis Hbudget : cao_etaP orc + INR N * cas_step_err orc C0 <= 1.
Hypothesis Hscale : (C0 + 1) + 4 * (h + cao_eta orc) + 1 <= bpow radix2 998.

Let E (k : nat) : R := cao_etaP orc + INR k * cas_step_err orc C0.

Lemma cas_etaP_nonneg : 0 <= cao_etaP orc.
Proof.
  destruct (cao_S0_ok orc) as [_ [_ HP]].
  pose proof (dist_nonneg (cas_bp (cao_S0 orc)) (cloth_P c a)). lra.
Qed.

Lemma cas_rho_nonneg : forall M, 0 <= M -> 0 <= cas_rho M.
Proof.
  intros M HM. unfold cas_rho. pose proof b64ae_u_small. pose proof b64ae_e0_small. nra.
Qed.

Lemma cas_step_err_nonneg : 0 <= cas_step_err orc C0.
Proof.
  unfold cas_step_err.
  pose proof (cas_rho_nonneg ((C0 + 1) + 4 * (h + cao_eta orc) + 1) ltac:(lra)).
  nra.
Qed.

Lemma cas_E_le_1 : forall k, (k <= N)%nat -> E k <= 1.
Proof.
  intros k Hk. unfold E.
  pose proof cas_step_err_nonneg. pose proof (le_INR _ _ Hk). nra.
Qed.

Lemma cas_dist_origin : forall p, dist p (mkPoint 0 0) = sqrt (px p * px p + py p * py p).
Proof. intro p. unfold dist, dist_sq. cbn. f_equal. ring. Qed.

(* Oracle tangents: coordinates within 2 and length within 1 + tau. *)
Lemma cas_orc_tangent : forall k, (k < N)%nat ->
  Rabs (B2R (bx (cao_T orc k))) <= 2 /\ Rabs (B2R (by_ (cao_T orc k))) <= 2 /\
  sqrt (B2R (bx (cao_T orc k)) * B2R (bx (cao_T orc k))
        + B2R (by_ (cao_T orc k)) * B2R (by_ (cao_T orc k))) <= 1 + cao_tau orc.
Proof.
  intros k Hk.
  destruct (cao_T_ok orc k Hk) as [_ [_ HT]].
  set (T := mkPoint (cloth_vx c (cas_node a h k)) (cloth_vy c (cas_node a h k))) in *.
  set (Tb := cas_bp (cao_T orc k)) in *.
  assert (HT1 : dist T (mkPoint 0 0) = 1).
  { rewrite cas_dist_origin. unfold T. cbn.
    rewrite cloth_tangent_sumsq by (destruct Hwf as [_ [H2 _]]; exact H2).
    apply sqrt_1. }
  pose proof (dist_triangle Tb T (mkPoint 0 0)) as Htri.
  assert (Hn : dist Tb (mkPoint 0 0) <= 1 + cao_tau orc) by lra.
  pose proof (cas_coord_le_dist Tb (mkPoint 0 0)) as [Cx Cy].
  rewrite cas_dist_origin in Hn.
  unfold Tb, cas_bp in Hn, Cx, Cy. cbn in Hn, Cx, Cy.
  rewrite !Rminus_0_r in Cx, Cy.
  rewrite cas_dist_origin in Cx, Cy. cbn in Cx, Cy.
  split; [lra|]. split; [lra|]. exact Hn.
Qed.

(* Oracle local coordinates: within h + eta. *)
Lemma cas_orc_local : forall k x, (k < N)%nat -> fin x = true -> 0 <= B2R x <= h ->
  Rabs (B2R (cao_X orc k x)) <= h + cao_eta orc /\
  Rabs (B2R (cao_Y orc k x)) <= h + cao_eta orc /\
  sqrt (cas_arc_X (cas_kap c (cas_node a h k) h) (B2R x)
        * cas_arc_X (cas_kap c (cas_node a h k) h) (B2R x)
        + cas_arc_Y (cas_kap c (cas_node a h k) h) (B2R x)
        * cas_arc_Y (cas_kap c (cas_node a h k) h) (B2R x)) <= h.
Proof.
  intros k x Hk Fx Hx.
  destruct (cao_XY_ok orc k x Hk Fx Hx) as [_ [_ HXY]].
  set (kk := cas_kap c (cas_node a h k) h) in *.
  set (V := mkPoint (cas_arc_X kk (B2R x)) (cas_arc_Y kk (B2R x))) in *.
  set (Vb := mkPoint (B2R (cao_X orc k x)) (B2R (cao_Y orc k x))) in *.
  assert (HV : sqrt (cas_arc_X kk (B2R x) * cas_arc_X kk (B2R x)
                     + cas_arc_Y kk (B2R x) * cas_arc_Y kk (B2R x)) <= h).
  { eapply Rle_trans; [apply sqrt_le_1_alt; apply cas_arc_chord|].
    rewrite sqrt_square by lra. lra. }
  assert (HVO : dist V (mkPoint 0 0) <= h)
    by (rewrite cas_dist_origin; unfold V; cbn; exact HV).
  pose proof (dist_triangle Vb V (mkPoint 0 0)) as Htri.
  assert (Hn : dist Vb (mkPoint 0 0) <= h + cao_eta orc) by lra.
  pose proof (cas_coord_le_dist Vb (mkPoint 0 0)) as [Cx Cy].
  unfold Vb in Cx, Cy, Hn. cbn in Cx, Cy, Hn. rewrite !Rminus_0_r in Cx, Cy.
  split; [lra|]. split; [lra|]. exact HV.
Qed.

(* One shot step from a start within E k: within E k + one step error. *)
Lemma cas_frame_step_total : forall k x Sb, (k < N)%nat ->
  fin x = true -> 0 <= B2R x <= h ->
  fin (bx Sb) = true -> fin (by_ Sb) = true ->
  dist (cas_bp Sb) (cas_start c a h k) <= E k ->
  fin (bx (cas_b64_frame Sb (cao_T orc k) (cao_X orc k x) (cao_Y orc k x))) = true /\
  fin (by_ (cas_b64_frame Sb (cao_T orc k) (cao_X orc k x) (cao_Y orc k x))) = true /\
  dist (cas_bp (cas_b64_frame Sb (cao_T orc k) (cao_X orc k x) (cao_Y orc k x)))
       (cas_arc_pt (cas_start c a h k)
          (cloth_vx c (cas_node a h k)) (cloth_vy c (cas_node a h k))
          (cas_kap c (cas_node a h k) h) (B2R x))
    <= E k + cas_step_err orc C0.
Proof.
  intros k x Sb Hk Fx Hx FSx FSy HD.
  destruct (cao_T_ok orc k Hk) as [FTx [FTy HT]].
  destruct (cao_XY_ok orc k x Hk Fx Hx) as [FX [FY HXY]].
  destruct (cas_orc_tangent k Hk) as [Tx [Ty Tn]].
  destruct (cas_orc_local k x Hk Fx Hx) as [Xb [Yb Vn]].
  assert (HE1 : E k <= 1) by (apply cas_E_le_1; lia).
  destruct (Hbox k ltac:(lia)) as [Bx By].
  pose proof (cas_coord_le_dist (cas_bp Sb) (cas_start c a h k)) as [Dx Dy].
  change (px (cas_bp Sb)) with (B2R (bx Sb)) in Dx.
  change (py (cas_bp Sb)) with (B2R (by_ Sb)) in Dy.
  assert (HSx : Rabs (B2R (bx Sb)) <= C0 + 1).
  { apply Rabs_le. apply Rabs_le_inv in Dx. apply Rabs_le_inv in Bx. lra. }
  assert (HSy : Rabs (B2R (by_ Sb)) <= C0 + 1).
  { apply Rabs_le. apply Rabs_le_inv in Dy. apply Rabs_le_inv in By. lra. }
  destruct (cas_b64_frame_err Sb (cao_T orc k) (cao_X orc k x) (cao_Y orc k x)
              (C0 + 1) (h + cao_eta orc) FSx FSy FTx FTy FX FY
              ltac:(lra) ltac:(lra) HSx HSy Tx Ty Xb Yb Hscale) as [Fo [Fo' Ho]].
  split; [exact Fo|]. split; [exact Fo'|].
  rewrite cas_arc_pt_frame.
  pose proof (cas_frame_perturb (cas_start c a h k) (cas_bp Sb)
    (cloth_vx c (cas_node a h k)) (cloth_vy c (cas_node a h k))
    (B2R (bx (cao_T orc k))) (B2R (by_ (cao_T orc k)))
    (cas_arc_X (cas_kap c (cas_node a h k) h) (B2R x))
    (cas_arc_Y (cas_kap c (cas_node a h k) h) (B2R x))
    (B2R (cao_X orc k x)) (B2R (cao_Y orc k x))) as Hp.
  pose proof (dist_triangle
    (cas_bp (cas_b64_frame Sb (cao_T orc k) (cao_X orc k x) (cao_Y orc k x)))
    (cas_frame (cas_bp Sb) (B2R (bx (cao_T orc k))) (B2R (by_ (cao_T orc k)))
       (B2R (cao_X orc k x)) (B2R (cao_Y orc k x)))
    (cas_frame (cas_start c a h k)
       (cloth_vx c (cas_node a h k)) (cloth_vy c (cas_node a h k))
       (cas_arc_X (cas_kap c (cas_node a h k) h) (B2R x))
       (cas_arc_Y (cas_kap c (cas_node a h k) h) (B2R x)))) as Htri.
  assert (Ht1 : dist (mkPoint (B2R (bx (cao_T orc k))) (B2R (by_ (cao_T orc k))))
             (mkPoint (cloth_vx c (cas_node a h k)) (cloth_vy c (cas_node a h k)))
             * sqrt (cas_arc_X (cas_kap c (cas_node a h k) h) (B2R x)
                     * cas_arc_X (cas_kap c (cas_node a h k) h) (B2R x)
                     + cas_arc_Y (cas_kap c (cas_node a h k) h) (B2R x)
                     * cas_arc_Y (cas_kap c (cas_node a h k) h) (B2R x))
             <= cao_tau orc * h).
  { apply Rmult_le_compat; [apply dist_nonneg | apply sqrt_pos | exact HT | exact Vn]. }
  assert (Ht2 : sqrt (B2R (bx (cao_T orc k)) * B2R (bx (cao_T orc k))
                      + B2R (by_ (cao_T orc k)) * B2R (by_ (cao_T orc k)))
             * dist (mkPoint (B2R (cao_X orc k x)) (B2R (cao_Y orc k x)))
                 (mkPoint (cas_arc_X (cas_kap c (cas_node a h k) h) (B2R x))
                          (cas_arc_Y (cas_kap c (cas_node a h k) h) (B2R x)))
             <= (1 + cao_tau orc) * cao_eta orc).
  { apply Rmult_le_compat; [apply sqrt_pos | apply dist_nonneg | exact Tn | exact HXY]. }
  unfold cas_step_err. lra.
Qed.

Lemma cas_b64_start_err : forall k, (k <= N)%nat ->
  fin (bx (cas_b64_start orc hb k)) = true /\
  fin (by_ (cas_b64_start orc hb k)) = true /\
  dist (cas_bp (cas_b64_start orc hb k)) (cas_start c a h k) <= E k.
Proof.
  induction k as [|k IH]; intros Hk.
  - destruct (cao_S0_ok orc) as [F1 [F2 HP]].
    cbn [cas_b64_start cas_start]. split; [exact F1|]. split; [exact F2|].
    unfold E. cbn [INR]. lra.
  - destruct (IH ltac:(lia)) as [F1 [F2 HD]].
    destruct Hhb as [Fh Eh].
    destruct (cas_frame_step_total k hb (cas_b64_start orc hb k) ltac:(lia) Fh
                ltac:(rewrite Eh; lra) F1 F2 HD) as [G1 [G2 HG]].
    cbn [cas_b64_start cas_start]. rewrite Eh in HG.
    split; [exact G1|]. split; [exact G2|].
    unfold E in *. rewrite S_INR. lra.
Qed.

(* Every computed point of piece k is within E (k + 1) of the exact piece. *)
Theorem cas_b64_point_err : forall k x, (k < N)%nat ->
  fin x = true -> 0 <= B2R x <= h ->
  fin (bx (cas_b64_point orc hb k x)) = true /\
  fin (by_ (cas_b64_point orc hb k x)) = true /\
  dist (cas_piece c a h k (cas_node a h k + B2R x))
       (cas_bp (cas_b64_point orc hb k x)) <= E (S k).
Proof.
  intros k x Hk Fx Hx.
  destruct (cas_b64_start_err k ltac:(lia)) as [F1 [F2 HD]].
  destruct (cas_frame_step_total k x (cas_b64_start orc hb k) Hk Fx Hx F1 F2 HD)
    as [G1 [G2 HG]].
  split; [exact G1|]. split; [exact G2|].
  rewrite dist_sym. unfold cas_piece, cas_b64_point.
  replace (cas_node a h k + B2R x - cas_node a h k) with (B2R x) by ring.
  unfold E in *. rewrite S_INR. lra.
Qed.

End Shot.

(* -------------------------------------------------------------------------- *)
(* 2d. Points contract: gate + oracle => every computed point near P.        *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-clothoid-arc-spline","topic":"curves","lemma":"cas_b64_points_contract","title":"Binary64 arc-spline points: for every oracle CasB64ArcOracle (Fresnel start within etaP, node tangents within tau, local arc coordinates on [0, h] within eta), when the RNE gate passes for eps, every point computed by the binary64 shot spline (RNE frame steps, N-step accumulation proved) is within eps + etaP + N (tau h + (1 + tau) eta + 2 rho) of the clothoid at its station","file":"theories-flocq/ClothoidArcSpline_b64.v","witness":"cas_b64_points_contract","board":"ADR-0007"} *)
Theorem cas_b64_points_contract :
  forall (c : ClothoidEgg) (a b : R) (N : nat)
         (orc : CasB64ArcOracle c a (cas_step a b N) N)
         (hb : binary64) (C0 : R) (L A n eps : binary64),
    cloth_wf c -> a <= b -> (N <> 0)%nat ->
    fin hb = true /\ B2R hb = cas_step a b N ->
    0 <= cao_tau orc <= 1 -> 0 <= cao_eta orc -> 0 <= C0 ->
    (forall k, (k <= N)%nat ->
       Rabs (px (cas_start c a (cas_step a b N) k)) <= C0 /\
       Rabs (py (cas_start c a (cas_step a b N) k)) <= C0) ->
    cao_etaP orc + INR N * cas_step_err orc C0 <= 1 ->
    (C0 + 1) + 4 * (cas_step a b N + cao_eta orc) + 1 <= bpow radix2 998 ->
    cas_b64_in_range L -> cas_b64_in_range A ->
    cas_b64_in_range n -> cas_b64_in_range eps ->
    b - a <= B2R L -> B2R A <= cloth_A c -> B2R n <= INR N ->
    cas_b64_gate L A n eps = true ->
    forall k x, (k < N)%nat -> fin x = true -> 0 <= B2R x <= cas_step a b N ->
      fin (bx (cas_b64_point orc hb k x)) = true /\
      fin (by_ (cas_b64_point orc hb k x)) = true /\
      dist (cloth_P c (cas_node a (cas_step a b N) k + B2R x))
           (cas_bp (cas_b64_point orc hb k x))
        <= B2R eps + cao_etaP orc + INR N * cas_step_err orc C0.
Proof.
  intros c a b N orc hb C0 L A n eps Hwf Hab HN Hhb Htau Heta HC0 Hbox Hbud Hsc
    RL RA Rn Re HLb HA Hn Hg k x Hk Fx Hx.
  set (h := cas_step a b N) in *.
  assert (Hh : 0 <= h).
  { unfold h, cas_step. apply Rmult_le_pos; [lra|].
    apply Rlt_le, Rinv_0_lt_compat, lt_0_INR. lia. }
  destruct (cas_b64_point_err c a h N orc hb C0 Hwf Hh Hhb Htau Heta HC0 Hbox
              Hbud Hsc k x Hk Fx Hx) as [F1 [F2 Hpt]].
  split; [exact F1|]. split; [exact F2|].
  assert (Hsp : dist (cloth_P c (cas_node a h k + B2R x))
                     (cas_piece c a h k (cas_node a h k + B2R x)) <= B2R eps).
  { apply (cas_b64_arc_spline_contract c a b N L A n eps); try assumption.
    rewrite cas_node_S. fold h. split; lra. }
  pose proof (dist_triangle (cloth_P c (cas_node a h k + B2R x))
                (cas_piece c a h k (cas_node a h k + B2R x))
                (cas_bp (cas_b64_point orc hb k x))) as Htri.
  assert (HSk : INR (S k) <= INR N) by (apply le_INR; lia).
  assert (Hst : 0 <= cas_step_err orc C0).
  { unfold cas_step_err.
    pose proof (cas_rho_nonneg (C0 + 1 + 4 * (h + cao_eta orc) + 1) ltac:(lra)).
    nra. }
  assert (HE : INR (S k) * cas_step_err orc C0 <= INR N * cas_step_err orc C0)
    by (apply Rmult_le_compat_r; assumption).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket.                                                                    *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-clothoid-arc-spline","topic":"curves","lemma":"ticket_0007_clothoid_arc_spline_qed_or_qex","title":"Heading-interpolating arc spline of a clothoid within eps: QED for the R contract (both directions, end gap bounded), the sound binary64 RNE gate, and binary64 points for every CasB64ArcOracle; QEX: no oracle inhabitant (no error-bounded binary64 sin/cos or Fresnel) in the corpus","file":"theories-flocq/ClothoidArcSpline_b64.v","witness":"ticket_0007_clothoid_arc_spline_qed_or_qex","board":"ADR-0007"} *)
Theorem ticket_0007_clothoid_arc_spline_qed_or_qex :
  (* QED: R contract, both directions, for every N >= 1 *)
  (forall c a b N eps, cloth_wf c -> a <= b -> (N <> 0)%nat ->
     (b - a) * (b - a) * (b - a)
       <= 8 * (cloth_A c * cloth_A c) * (INR N * INR N) * eps ->
     (forall k u, (k < N)%nat ->
        cas_node a (cas_step a b N) k <= u <= cas_node a (cas_step a b N) (S k) ->
        dist (cloth_P c u) (cas_piece c a (cas_step a b N) k u) <= eps) /\
     (forall u, a <= u <= b -> exists k, (k < N)%nat /\
        cas_node a (cas_step a b N) k <= u <= cas_node a (cas_step a b N) (S k) /\
        dist (cloth_P c u) (cas_piece c a (cas_step a b N) k u) <= eps) /\
     dist (cloth_P c b) (cas_start c a (cas_step a b N) N) <= eps) /\
  (* QED: the binary64 gate decides it soundly (rounded-down A, n allowed) *)
  (forall c a b N L A n eps, cloth_wf c -> a <= b -> (N <> 0)%nat ->
     cas_b64_in_range L -> cas_b64_in_range A ->
     cas_b64_in_range n -> cas_b64_in_range eps ->
     b - a <= B2R L -> B2R A <= cloth_A c -> B2R n <= INR N ->
     cas_b64_gate L A n eps = true ->
     forall k u, (k < N)%nat ->
       cas_node a (cas_step a b N) k <= u <= cas_node a (cas_step a b N) (S k) ->
       dist (cloth_P c u) (cas_piece c a (cas_step a b N) k u) <= B2R eps).
Proof.
  split.
  - intros c a b N eps Hwf Hab HN Hg.
    split; [exact (cas_arc_spline_within_eps c a b N eps Hwf Hab HN Hg)|].
    split; [exact (cas_arc_spline_cover c a b N eps Hwf Hab HN Hg)|].
    eapply Rle_trans; [apply (cas_end_gap c a b N Hwf Hab HN)|].
    destruct Hwf as [HA _].
    assert (HNp : 0 < INR N) by (apply lt_0_INR; lia).
    assert (Hden : 0 < 8 * (cloth_A c * cloth_A c) * (INR N * INR N))
      by (apply Rmult_lt_0_compat; nra).
    apply Rmult_le_reg_r with (8 * (cloth_A c * cloth_A c) * (INR N * INR N));
      [exact Hden|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
  - exact cas_b64_arc_spline_contract.
Qed.

Print Assumptions cas_b64_mult_pos.
Print Assumptions cas_b64_gate_sound.
Print Assumptions cas_b64_gate_real.
Print Assumptions cas_b64_arc_spline_contract.
Print Assumptions cas_b64_two_arc_contract.
Print Assumptions cas_b64_axis.
Print Assumptions cas_b64_frame_err.
Print Assumptions cas_b64_start_err.
Print Assumptions cas_b64_point_err.
Print Assumptions cas_b64_points_contract.
Print Assumptions ticket_0007_clothoid_arc_spline_qed_or_qex.
