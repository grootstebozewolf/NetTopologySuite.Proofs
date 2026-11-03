(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ClothoidBiarc_b64
   ----------------------------------------------------------------------------
   binary64 face of the biarc / arc-spline contract of
   theories/ClothoidBiarc.v.  Turns the arc-approximation tolerance from a
   heuristic into a contract: the round-to-nearest-even gate
     fl( fl(fl(L*L)*L) * (1 + 2^-49) )  <=  fl(fl(fl(fl(fl(8*A)*A)*n)*n)*eps)
   is sound for the real inequality L^3 <= 8 A^2 n^2 eps
   (`cbi_b64_gate_sound`), so a window of length <= L cut into n arcs is
   within eps of the clothoid whenever the binary64 gate says so
   (`cbi_b64_arc_spline_contract`; biarc n = 2: `cbi_b64_biarc_contract`).
   The margin 1 + 2^-49 = 1 + 16u absorbs the eight roundings
   ((1 + u)^5 <= (1 + 2^-49) (1 - u)^3, u = 2^-53).

   Domain: every input finite and in [2^-100, 2^100] (n >= 1 in the same
   range).  Every intermediate then stays in [2^-1000, 2^1000]: no
   overflow, no subnormal, so Flocq's relative_error_N_FLT applies per op.

   QED / QEX (ticket_0007_clothoid_biarc_qed_or_qex):
     QED  the R contract (cbi_biarc_within_eps) and the binary64 gate that
          decides it, sound under RNE.
     QEX  binary64 evaluation of the arc POINTS.  Each piece point needs
          sin and cos of the piece turn kappa h (and the window start needs
          P(a), a Fresnel value, unless a is the inflection).  Neither
          IEEE 754 nor Flocq gives an error-bounded binary64 sin / cos, and
          the corpus has none.  The missing constructor is named:
          `CbiB64ArcEval` below, the interface such an evaluator must meet.
          No inhabitant is claimed.
   claimId: 0007-clothoid-biarc.  witness: cbi_b64_biarc_contract.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib.
From NTS.Proofs Require Import Distance SheetHenClothoidCore ClothoidBiarc.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* Unit roundoff of binary64 round-to-nearest. *)
Definition cbi_u : R := bpow radix2 (-53).

Lemma cbi_u_small : 0 < cbi_u <= / 1000.
Proof.
  unfold cbi_u. split; [apply bpow_gt_0|].
  apply Rle_trans with (bpow radix2 (-10)).
  - apply bpow_le. lia.
  - cbn. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Constants.                                                                 *)
(* -------------------------------------------------------------------------- *)

(* 8 = 2^52 * 2^-49. *)
Definition cbi_b64_eight : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-49) eq_refl.
(* 1 + 2^-49 = (2^52 + 2^3) * 2^-52. *)
Definition cbi_b64_margin : binary64 :=
  Binary.B754_finite prec emax false 4503599627370504 (-52) eq_refl.

Lemma cbi_b64_eight_R : B2R cbi_b64_eight = 8 /\ fin cbi_b64_eight = true.
Proof.
  split; [|reflexivity].
  unfold cbi_b64_eight. cbn [Binary.B2R]. unfold F2R. cbn. lra.
Qed.

Lemma cbi_b64_margin_R :
  B2R cbi_b64_margin = 1 + bpow radix2 (-49) /\ fin cbi_b64_margin = true.
Proof.
  split; [|reflexivity].
  unfold cbi_b64_margin. cbn [Binary.B2R]. unfold F2R. cbn. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* One rounded product of positive normal-range operands.                    *)
(* -------------------------------------------------------------------------- *)

Lemma cbi_b64_mult_pos : forall x y ex ey,
  fin x = true -> fin y = true ->
  (0 <= ex)%Z -> (0 <= ey)%Z -> (ex + ey + 1 <= 1000)%Z ->
  bpow radix2 (- ex) <= B2R x <= bpow radix2 ex ->
  bpow radix2 (- ey) <= B2R y <= bpow radix2 ey ->
  fin (b64_mult x y) = true /\
  B2R x * B2R y * (1 - cbi_u) <= B2R (b64_mult x y)
    <= B2R x * B2R y * (1 + cbi_u) /\
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
  assert (Hrel : Rabs (b64_round z - z) <= cbi_u * Rabs z).
  { assert (Hn : bpow radix2 (3 - emax - prec + prec - 1) <= Rabs z).
    { rewrite Rabs_pos_eq by lra. eapply Rle_trans; [|exact Hz0].
      apply bpow_le. unfold emax, prec. lia. }
    pose proof (relative_error_N_FLT radix2 (3 - emax - prec) prec
                  prec_gt_0_b64 (fun t => negb (Z.even t)) z Hn) as H.
    replace cbi_u with (/ 2 * bpow radix2 (- prec + 1)).
    - exact H.
    - unfold cbi_u, prec.
      replace (/ 2) with (bpow radix2 (-1)) by reflexivity.
      rewrite <- bpow_plus. f_equal. }
  rewrite (Rabs_pos_eq z) in Hrel by lra.
  apply Rabs_le_inv in Hrel.
  pose proof cbi_u_small as Hu.
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

Definition cbi_b64_gate (L A n eps : binary64) : bool :=
  b64_le
    (b64_mult (b64_mult (b64_mult L L) L) cbi_b64_margin)
    (b64_mult (b64_mult (b64_mult (b64_mult (b64_mult cbi_b64_eight A) A) n) n)
       eps).

Definition cbi_b64_in_range (x : binary64) : Prop :=
  fin x = true /\ bpow radix2 (-100) <= B2R x <= bpow radix2 100.

Lemma cbi_b64_le_R : forall a b, fin a = true -> fin b = true ->
  b64_le a b = true -> B2R a <= B2R b.
Proof.
  intros a b Fa Fb Hle.
  unfold b64_le, b64_compare in Hle.
  pose proof (b64_compare_payload a b Fa Fb) as Hp.
  destruct (Binary.Bcompare prec emax a b) as [[]|]; try discriminate Hle.
  - rewrite Hp. apply Rle_refl.
  - apply Rlt_le. exact Hp.
Qed.

Lemma cbi_round_margin :
  (1 + cbi_u) * (1 + cbi_u) * (1 + cbi_u) * (1 + cbi_u) * (1 + cbi_u)
  <= (1 + bpow radix2 (-49)) * ((1 - cbi_u) * (1 - cbi_u) * (1 - cbi_u)).
Proof.
  assert (E : bpow radix2 (-49) = 16 * cbi_u).
  { unfold cbi_u. replace (-49)%Z with (4 + -53)%Z by lia.
    rewrite bpow_plus. reflexivity. }
  rewrite E. pose proof cbi_u_small as [H0 H1].
  assert (Hlo : (1 + 13 * cbi_u - 51 * (cbi_u * cbi_u))
                <= (1 + 16 * cbi_u) * ((1 - cbi_u) * (1 - cbi_u) * (1 - cbi_u)))
    by nra.
  assert (Hhi : (1 + cbi_u) * (1 + cbi_u) * (1 + cbi_u) * (1 + cbi_u) * (1 + cbi_u)
                <= 1 + 5 * cbi_u + 11 * (cbi_u * cbi_u)).
  { assert (Hc : cbi_u * cbi_u <= cbi_u / 1000) by nra.
    assert (Hc2 : cbi_u * cbi_u * cbi_u <= cbi_u * cbi_u / 1000) by nra.
    assert (Hc3 : cbi_u * cbi_u * cbi_u * cbi_u <= cbi_u * cbi_u / 1000) by nra.
    assert (Hc4 : cbi_u * cbi_u * cbi_u * cbi_u * cbi_u <= cbi_u * cbi_u / 1000)
      by nra.
    nra. }
  nra.
Qed.

(* WITNESS {"claimId":"0007-clothoid-biarc","topic":"curves","lemma":"cbi_b64_gate_sound","title":"The binary64 round-to-nearest tolerance gate fl(L^3 (1 + 2^-49)) <= fl(8 A^2 n^2 eps) implies the real L^3 <= 8 A^2 n^2 eps on finite inputs in [2^-100, 2^100]","file":"theories-flocq/ClothoidBiarc_b64.v","witness":"cbi_b64_gate_sound","board":"ADR-0007"} *)
Theorem cbi_b64_gate_sound : forall L A n eps,
  cbi_b64_in_range L -> cbi_b64_in_range A ->
  cbi_b64_in_range n -> cbi_b64_in_range eps ->
  cbi_b64_gate L A n eps = true ->
  B2R L * B2R L * B2R L <= 8 * (B2R A * B2R A) * (B2R n * B2R n) * B2R eps.
Proof.
  intros L A n eps [FL HL] [FA HA] [Fn Hn] [Fe He] Hg.
  destruct cbi_b64_eight_R as [E8 F8].
  destruct cbi_b64_margin_R as [EM FM].
  assert (H8 : bpow radix2 (- 3) <= B2R cbi_b64_eight <= bpow radix2 3).
  { rewrite E8. cbn. lra. }
  assert (HM : bpow radix2 (- 1) <= B2R cbi_b64_margin <= bpow radix2 1).
  { rewrite EM. split.
    - apply Rle_trans with 1;
        [replace (bpow radix2 (-1)) with (/ 2) by reflexivity; lra|].
      pose proof (bpow_ge_0 radix2 (-49)). lra.
    - assert (bpow radix2 (-49) <= 1) by (apply (bpow_le radix2 (-49) 0); lia).
      replace (bpow radix2 1) with 2 by reflexivity. lra. }
  pose proof cbi_u_small as Hu.
  (* left: ((L*L)*L)*M *)
  destruct (cbi_b64_mult_pos L L 100 100 FL FL ltac:(lia) ltac:(lia) ltac:(lia) HL HL)
    as [F1 [R1 B1]].
  destruct (cbi_b64_mult_pos _ L 201 100 F1 FL ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(exact B1) HL) as [F2 [R2 B2]].
  destruct (cbi_b64_mult_pos _ cbi_b64_margin 302 1 F2 FM ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(exact B2) HM) as [F3 [R3 _]].
  (* right: ((((8*A)*A)*n)*n)*eps *)
  destruct (cbi_b64_mult_pos cbi_b64_eight A 3 100 F8 FA ltac:(lia) ltac:(lia)
              ltac:(lia) H8 HA) as [G1 [S1 C1]].
  destruct (cbi_b64_mult_pos _ A 104 100 G1 FA ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(exact C1) HA) as [G2 [S2 C2]].
  destruct (cbi_b64_mult_pos _ n 205 100 G2 Fn ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(exact C2) Hn) as [G3 [S3 C3]].
  destruct (cbi_b64_mult_pos _ n 306 100 G3 Fn ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(exact C3) Hn) as [G4 [S4 C4]].
  destruct (cbi_b64_mult_pos _ eps 407 100 G4 Fe ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(exact C4) He) as [G5 [S5 _]].
  unfold cbi_b64_gate in Hg.
  pose proof (cbi_b64_le_R _ _ F3 G5 Hg) as Hle.
  set (l := B2R L). set (a := B2R A). set (m := B2R n). set (e := B2R eps).
  fold l in R1, R2. fold a in S1, S2. fold m in S3, S4. fold e in S5.
  rewrite E8 in S1. rewrite EM in R3.
  set (v := cbi_u) in *.
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
  set (x3 := B2R (b64_mult (b64_mult (b64_mult L L) L) cbi_b64_margin)) in *.
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
  set (y1 := B2R (b64_mult cbi_b64_eight A)) in *.
  set (y2 := B2R (b64_mult (b64_mult cbi_b64_eight A) A)) in *.
  set (y3 := B2R (b64_mult (b64_mult (b64_mult cbi_b64_eight A) A) n)) in *.
  set (y4 := B2R (b64_mult (b64_mult (b64_mult (b64_mult cbi_b64_eight A) A) n) n))
    in *.
  set (y5 := B2R (b64_mult (b64_mult (b64_mult (b64_mult (b64_mult cbi_b64_eight A)
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
  pose proof cbi_round_margin as Hmar. fold v M in Hmar. fold p1 q1 in Hmar.
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
(* Composition with the R contract.                                           *)
(* -------------------------------------------------------------------------- *)

Theorem cbi_b64_arc_spline_contract :
  forall (c : ClothoidEgg) (a b : R) (N : nat) (L A n eps : binary64),
    cloth_wf c -> a <= b -> (N <> 0)%nat ->
    cbi_b64_in_range L -> cbi_b64_in_range A ->
    cbi_b64_in_range n -> cbi_b64_in_range eps ->
    b - a <= B2R L -> B2R A = cloth_A c -> B2R n = INR N ->
    cbi_b64_gate L A n eps = true ->
    forall k u, (k < N)%nat ->
      cbi_node a (cbi_step a b N) k <= u <= cbi_node a (cbi_step a b N) (S k) ->
      dist (cloth_P c u) (cbi_piece c a (cbi_step a b N) k u) <= B2R eps.
Proof.
  intros c a b N L A n eps Hwf Hab HN RL RA Rn Re HLb HA Hn Hg k u Hk Hu.
  pose proof (cbi_b64_gate_sound L A n eps RL RA Rn Re Hg) as Hs.
  rewrite HA, Hn in Hs.
  apply (cbi_arc_spline_within_eps c a b N (B2R eps) Hwf Hab HN); [|exact Hk|exact Hu].
  assert (H0 : 0 <= b - a) by lra.
  apply Rle_trans with (B2R L * B2R L * B2R L); [|exact Hs].
  apply Rmult_le_compat; [nra | lra | |exact HLb].
  apply Rmult_le_compat; lra.
Qed.

(* WITNESS {"claimId":"0007-clothoid-biarc","topic":"curves","lemma":"cbi_b64_biarc_contract","title":"Biarc contract in binary64: when the RNE gate fl(L^3 (1 + 2^-49)) <= fl(8 A^2 2^2 eps) passes for a window of length <= L, every point of the biarc of theories/ClothoidBiarc.v is within eps of the clothoid at its station","file":"theories-flocq/ClothoidBiarc_b64.v","witness":"cbi_b64_biarc_contract","board":"ADR-0007"} *)
Theorem cbi_b64_biarc_contract :
  forall (c : ClothoidEgg) (a b : R) (L A two eps : binary64),
    cloth_wf c -> a <= b ->
    cbi_b64_in_range L -> cbi_b64_in_range A ->
    cbi_b64_in_range two -> cbi_b64_in_range eps ->
    b - a <= B2R L -> B2R A = cloth_A c -> B2R two = 2 ->
    cbi_b64_gate L A two eps = true ->
    forall k u, (k < 2)%nat ->
      cbi_node a (cbi_step a b 2) k <= u <= cbi_node a (cbi_step a b 2) (S k) ->
      dist (cloth_P c u) (cbi_piece c a (cbi_step a b 2) k u) <= B2R eps.
Proof.
  intros c a b L A two eps Hwf Hab RL RA R2 Re HLb HA H2 Hg.
  apply (cbi_b64_arc_spline_contract c a b 2 L A two eps); try assumption.
  all: first [lia | rewrite H2; cbn; ring].
Qed.

(* -------------------------------------------------------------------------- *)
(* QEX: the missing constructor for binary64 arc POINTS.                       *)
(* -------------------------------------------------------------------------- *)

(* What a binary64 evaluator of one arc piece must provide for the point
   contract: local coordinates X, Y of the unit-speed arc of curvature k
   after arc length x (ClothoidBiarc.cbi_arc_X / cbi_arc_Y, i.e.
   sin(kx)/k and (1 - cos(kx))/k), within a stated absolute error, on a
   stated domain.  The corpus has no inhabitant: Flocq has no sin / cos,
   IEEE 754 does not require them correctly rounded, and no Taylor
   evaluator with a Flocq error bound exists here yet. *)
Record CbiB64ArcEval : Type := mkCbiB64ArcEval {
  cbe_X : binary64 -> binary64 -> binary64;
  cbe_Y : binary64 -> binary64 -> binary64;
  cbe_eta : R;
  cbe_dom : R -> R -> Prop;
  cbe_X_ok : forall k x, fin k = true -> fin x = true -> cbe_dom (B2R k) (B2R x) ->
    fin (cbe_X k x) = true /\
    Rabs (B2R (cbe_X k x) - cbi_arc_X (B2R k) (B2R x)) <= cbe_eta;
  cbe_Y_ok : forall k x, fin k = true -> fin x = true -> cbe_dom (B2R k) (B2R x) ->
    fin (cbe_Y k x) = true /\
    Rabs (B2R (cbe_Y k x) - cbi_arc_Y (B2R k) (B2R x)) <= cbe_eta
}.

Inductive CbiBiarcB64Status : Type :=
| CbiGateQed          (* tolerance gate sound in binary64: landed *)
| CbiPointsQex.       (* binary64 arc points: missing CbiB64ArcEval *)

Definition cbi_biarc_b64_status : list CbiBiarcB64Status :=
  CbiGateQed :: CbiPointsQex :: nil.

(* WITNESS {"claimId":"0007-clothoid-biarc","topic":"curves","lemma":"ticket_0007_clothoid_biarc_qed_or_qex","title":"Biarc approximation of a clothoid within eps: QED for the R contract and its binary64 RNE tolerance gate; QEX for binary64 arc points, named missing constructor CbiB64ArcEval (no error-bounded binary64 sin/cos)","file":"theories-flocq/ClothoidBiarc_b64.v","witness":"ticket_0007_clothoid_biarc_qed_or_qex","board":"ADR-0007"} *)
Theorem ticket_0007_clothoid_biarc_qed_or_qex :
  (* QED: the R contract, unconditional on the host *)
  (forall c a b eps, cloth_wf c -> a <= b ->
     (b - a) * (b - a) * (b - a) <= 32 * (cloth_A c * cloth_A c) * eps ->
     forall k u, (k < 2)%nat ->
       cbi_node a (cbi_step a b 2) k <= u <= cbi_node a (cbi_step a b 2) (S k) ->
       dist (cloth_P c u) (cbi_piece c a (cbi_step a b 2) k u) <= eps) /\
  (* QED: the binary64 gate decides that contract soundly *)
  (forall c a b L A two eps, cloth_wf c -> a <= b ->
     cbi_b64_in_range L -> cbi_b64_in_range A ->
     cbi_b64_in_range two -> cbi_b64_in_range eps ->
     b - a <= B2R L -> B2R A = cloth_A c -> B2R two = 2 ->
     cbi_b64_gate L A two eps = true ->
     forall k u, (k < 2)%nat ->
       cbi_node a (cbi_step a b 2) k <= u <= cbi_node a (cbi_step a b 2) (S k) ->
       dist (cloth_P c u) (cbi_piece c a (cbi_step a b 2) k u) <= B2R eps) /\
  (* QEX: binary64 points stay parked on the named constructor *)
  In CbiPointsQex cbi_biarc_b64_status /\ ~ In CbiGateQed nil.
Proof.
  split; [|split].
  - intros c a b eps Hwf Hab Hg.
    exact (proj1 (cbi_biarc_within_eps c a b eps Hwf Hab Hg)).
  - exact cbi_b64_biarc_contract.
  - split; [right; left; reflexivity | intro H; exact H].
Qed.

Print Assumptions cbi_b64_mult_pos.
Print Assumptions cbi_b64_gate_sound.
Print Assumptions cbi_b64_arc_spline_contract.
Print Assumptions cbi_b64_biarc_contract.
Print Assumptions ticket_0007_clothoid_biarc_qed_or_qex.
