(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_SegGPolicy
   ----------------------------------------------------------------------------
   T3 prerequisite, rung 4: the intake and the seam.  One signed, total
   evaluator of g(a) = a - sin a with a relative bound on its WHOLE intake
   2^-338 <= |a| <= 10, and a decline outside it:

     mf_seg_g_total   a <= 1: mf_seg_g_poly (B64_SegGRel, 24 u g)
                      a >  1: mf_seg_g      (B64_MarginFilter, absolute 2^-48)
     mf_seg_g_signed  a >= 0: total a;  a < 0: -total(-a)   (g is odd)

   Real fact (no calculus): sgp_g_ge1  1 <= a <= 10 -> 3/20 <= a - sin a, so the
   absolute 2^-48 bound of the old path is relative above the seam:
   2^-48 <= (2^-48 / (3/20)) g <= 2^-45 g = 256 u g.

     sgp_total_rel    floor <= a <= 10 -> finite, 0 < g^,
                      |g^ - g| <= 256 u g                          (u = 2^-53)
     sgp_signed_rel   floor <= |a| <= 10 -> finite, same bound against |g|
     sgp_outcome_*    mf_seg_g_outcome_rel t = SG_Value v only inside the
                      intake and then v is certified (soundness); every finite
                      t with floor <= |t| <= 10 yields SG_Value (completeness:
                      no UNDECIDED inside the intake); outside it SG_Decline.
   The seam a = 1 belongs to the polynomial branch (b64_le a 1), which the
   24 u theorem covers; the 256 u bound is the weaker of the two branches.
   Constants: floor = 2^-338 as in B64_SegGRel (a round value, not a proof limit).

   CONDITIONAL ON THETA exactly as B64_SegGDiv: nothing here certifies where the
   supplied a comes from (libm asin, inventory T1, deferred D3).
   claimId: t3-seg-g-policy.  Evaluation only: no extraction, no oracle mode,
   no port, no division wiring for the total evaluator, no consumer switch.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly B64_Sin B64_SinRel B64_SegGRel B64_MarginFilter.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  Real fact: g >= 3/20 on [1, 10].                                       *)
(* -------------------------------------------------------------------------- *)

Lemma sgp_g_ge1 : forall a, 1 <= a <= 10 -> 3 / 20 <= a - sin a.
Proof.
  intros a Ha.
  destruct (Rle_lt_dec a (6 / 5)) as [Hs|Hl].
  - assert (Hpi : 6 / 5 <= PI) by (pose proof sp_pi_bounds as [H _]; unfold sp_pi_lo in H; lra).
    destruct (sin_bound a 1 ltac:(lra) ltac:(lra)) as [_ H2].
    change (2 * (1 + 1))%nat with 4%nat in H2.
    rewrite sg_sin_approx4 in H2.
    assert (Haa : 1 <= a * a <= 144 / 100) by nra.
    assert (E5 : a ^ 5 = a ^ 3 * (a * a)) by ring.
    assert (E7 : a ^ 7 = a ^ 5 * (a * a)) by ring.
    assert (E9 : a ^ 9 = a ^ 7 * (a * a)) by ring.
    assert (N3 : 1 <= a ^ 3) by (replace (a ^ 3) with (a * (a * a)) by ring; nra).
    assert (N5 : 0 <= a ^ 5) by (apply pow_le; lra).
    assert (N7 : 0 <= a ^ 7) by (apply pow_le; lra).
    assert (B5 : a ^ 5 <= a ^ 3 * (144 / 100)).
    { rewrite E5. apply Rmult_le_compat_l; lra. }
    assert (B9 : a ^ 9 <= a ^ 7 * (144 / 100)).
    { rewrite E9. apply Rmult_le_compat_l; lra. }
    lra.
  - pose proof (SIN_bound a) as [_ Hu]. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Constants and the branch.                                              *)
(* -------------------------------------------------------------------------- *)

Definition sgp_floor : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-390) eq_refl.
Definition sgp_mfloor : binary64 :=
  Binary.B754_finite prec emax true 4503599627370496 (-390) eq_refl.

Lemma sgp_m52 : IZR 4503599627370496 = bpow radix2 52.
Proof.
  replace 4503599627370496%Z with (Zpower_pos 2 52) by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma sgp_floor_R : B2R sgp_floor = bpow radix2 (-338) /\ fin sgp_floor = true.
Proof.
  split; [|reflexivity].
  unfold sgp_floor. cbn [Binary.B2R]. unfold F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp].
  rewrite sgp_m52, <- bpow_plus. reflexivity.
Qed.

Lemma sgp_mfloor_R : B2R sgp_mfloor = - bpow radix2 (-338) /\ fin sgp_mfloor = true.
Proof.
  split; [|reflexivity].
  unfold sgp_mfloor. cbn [Binary.B2R]. unfold F2R. cbn [Fnum Fexp SpecFloat.cond_Zopp].
  rewrite opp_IZR, sgp_m52, <- Ropp_mult_distr_l, <- bpow_plus. reflexivity.
Qed.

Definition mf_seg_g_total (t : binary64) : binary64 :=
  if b64_le t sn_one then mf_seg_g_poly t else mf_seg_g t.

Definition mf_seg_g_signed (t : binary64) : binary64 :=
  if b64_le hz_zero t then mf_seg_g_total t else sn_neg (mf_seg_g_total (sn_neg t)).

(* -------------------------------------------------------------------------- *)
(* §3  The positive half: total evaluator.                                    *)
(* -------------------------------------------------------------------------- *)

Theorem sgp_total_rel : forall t, fin t = true ->
  bpow radix2 (-338) <= B2R t -> B2R t <= 10 ->
  fin (mf_seg_g_total t) = true /\ 0 < B2R (mf_seg_g_total t) /\
  Rabs (B2R (mf_seg_g_total t) - (B2R t - sin (B2R t)))
    <= 256 * (b64ae_u * (B2R t - sin (B2R t))).
Proof.
  intros t Ft Hlo Hhi.
  set (a := B2R t) in *.
  pose proof sp_u_val as Uv.
  assert (Ha : 0 < a) by (pose proof (bpow_gt_0 radix2 (-338)); lra).
  destruct sn_one_R as [E1 F1]. destruct sn_ten_R as [E10 F10].
  unfold mf_seg_g_total.
  destruct (b64_le t sn_one) eqn:L1.
  - apply b64ae_le_true in L1; [|exact Ft|exact F1]. rewrite E1 in L1.
    destruct (mf_seg_g_poly_rel t Ft Hlo L1) as [Fg Eg].
    change (B2R t) with a in Eg.
    pose proof (mf_seg_g_poly_pos t Ft Hlo L1) as Pg.
    assert (La : a <= 1) by exact L1.
    pose proof (sg_g_enclosure a ltac:(split; lra)) as [Gl _].
    assert (HA : 0 < a * (a * a)) by (apply Rmult_lt_0_compat; [lra | nra]).
    assert (Hg : 0 < a - sin a) by lra.
    rewrite Uv in *.
    split; [exact Fg|]. split; [exact Pg|].
    eapply Rle_trans; [exact Eg|].
    assert (0 <= / 9007199254740992 * (a - sin a)) by (apply Rmult_le_pos; lra).
    lra.
  - apply b64ae_le_false in L1; [|exact Ft|exact F1]. rewrite E1 in L1.
    change (B2R t) with a in L1.
    assert (Hacc : sin_accept t = true).
    { unfold sin_accept. rewrite Ft. cbn [andb].
      destruct sn_mten_R as [Em Fm].
      assert (A1 : b64_le sn_mten t = true) by (apply sr_le_true; [exact Fm | exact Ft | rewrite Em; change (B2R t) with a; lra]).
      assert (A2 : b64_le t sn_ten = true) by (apply sr_le_true; [exact Ft | exact F10 | rewrite E10; change (B2R t) with a; lra]).
      rewrite A1, A2. reflexivity. }
    destruct (b64_seg_g_err t Hacc) as [Fg Eg].
    change (B2R t) with a in Eg.
    pose proof (sgp_g_ge1 a ltac:(split; lra)) as G1.
    rewrite Uv.
    set (gh := B2R (mf_seg_g t)) in *.
    assert (Hrel : Rabs (gh - (a - sin a)) <= 256 * (/ 9007199254740992 * (a - sin a))).
    { eapply Rle_trans; [exact Eg|]. lra. }
    split; [exact Fg|]. split; [|exact Hrel].
    apply Rabs_le_inv in Hrel as [Hr1 _]. lra.
Qed.

Lemma sgp_g_pos : forall a, bpow radix2 (-338) <= a -> a <= 10 -> 0 < a - sin a.
Proof.
  intros a Hlo Hhi.
  assert (Ha : 0 < a) by (pose proof (bpow_gt_0 radix2 (-338)); lra).
  destruct (Rle_lt_dec a 1) as [H1|H1].
  - pose proof (sg_g_enclosure a ltac:(split; lra)) as [Gl _].
    assert (0 < a * (a * a)) by (apply Rmult_lt_0_compat; [lra | nra]). lra.
  - pose proof (sgp_g_ge1 a ltac:(split; lra)). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The signed evaluator (g is odd).                                       *)
(* -------------------------------------------------------------------------- *)

Theorem sgp_signed_rel : forall t, fin t = true ->
  bpow radix2 (-338) <= Rabs (B2R t) -> Rabs (B2R t) <= 10 ->
  fin (mf_seg_g_signed t) = true /\
  Rabs (B2R (mf_seg_g_signed t) - (B2R t - sin (B2R t)))
    <= 256 * (b64ae_u * Rabs (B2R t - sin (B2R t))).
Proof.
  intros t Ft Hlo Hhi.
  set (a := B2R t) in *.
  pose proof (Rabs_le_inv _ _ Hhi) as [Hh1 Hh2].
  unfold mf_seg_g_signed.
  destruct (b64_le hz_zero t) eqn:Z0.
  - apply b64ae_le_true in Z0; [|reflexivity|exact Ft].
    replace (B2R hz_zero) with 0 in Z0 by reflexivity.
    change (B2R t) with a in Z0.
    rewrite (Rabs_right a) in Hlo by lra.
    destruct (sgp_total_rel t Ft Hlo Hh2) as [F [_ E]].
    change (B2R t) with a in E.
    pose proof (sgp_g_pos a Hlo Hh2) as Hg.
    rewrite (Rabs_right (a - sin a)) by lra.
    split; [exact F | exact E].
  - apply b64ae_le_false in Z0; [|reflexivity|exact Ft].
    replace (B2R hz_zero) with 0 in Z0 by reflexivity.
    change (B2R t) with a in Z0.
    rewrite (Rabs_left a) in Hlo by lra.
    rewrite (Rabs_left a) in Hhi by lra.
    destruct (sn_neg_ok t Ft) as [Fy Ey].
    assert (Hy1 : bpow radix2 (-338) <= B2R (sn_neg t)) by (rewrite Ey; exact Hlo).
    assert (Hy2 : B2R (sn_neg t) <= 10) by (rewrite Ey; change (B2R t) with a; lra).
    destruct (sgp_total_rel (sn_neg t) Fy Hy1 Hy2) as [Ft' [_ E]].
    rewrite Ey in E. change (B2R t) with a in E.
    pose proof (sgp_g_pos (- a) Hlo ltac:(lra)) as Hg.
    destruct (sn_neg_ok _ Ft') as [Fn En].
    split; [exact Fn|]. rewrite En.
    assert (Hsn : sin (- a) = - sin a) by apply sin_neg.
    rewrite Hsn in E.
    replace (a - sin a) with (- (- a - - sin a)) by ring.
    rewrite Rabs_Ropp, (Rabs_right (- a - - sin a)) by lra.
    replace (- B2R (mf_seg_g_total (sn_neg t)) - - (- a - - sin a))
      with (- (B2R (mf_seg_g_total (sn_neg t)) - (- a - - sin a))) by ring.
    rewrite Rabs_Ropp. exact E.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Intake, decline, and the outcome.                                      *)
(* -------------------------------------------------------------------------- *)

Definition sgp_intake_b (t : binary64) : bool :=
  (b64_le sgp_floor t && b64_le t sn_ten) || (b64_le sn_mten t && b64_le t sgp_mfloor).

Lemma sgp_intake_fin : forall t, sgp_intake_b t = true -> fin t = true.
Proof.
  intros t H. destruct (fin t) eqn:Ft; [reflexivity|]. exfalso.
  destruct t as [s|s|s pl Hpl|s m e Hb]; cbn [Binary.is_finite] in Ft;
    try discriminate Ft; destruct s; unfold sgp_intake_b in H; vm_compute in H; discriminate H.
Qed.

Lemma sgp_intake_sound : forall t, sgp_intake_b t = true ->
  fin t = true /\ bpow radix2 (-338) <= Rabs (B2R t) /\ Rabs (B2R t) <= 10.
Proof.
  intros t H. pose proof (sgp_intake_fin t H) as Ft.
  destruct sgp_floor_R as [Ef Ff]. destruct sgp_mfloor_R as [Em Fm].
  destruct sn_ten_R as [E10 F10]. destruct sn_mten_R as [Em10 Fm10].
  split; [exact Ft|]. unfold sgp_intake_b in H.
  apply orb_true_iff in H as [H|H]; apply andb_true_iff in H as [H1 H2].
  - apply b64ae_le_true in H1; [|exact Ff|exact Ft]. apply b64ae_le_true in H2; [|exact Ft|exact F10].
    rewrite Ef in H1. rewrite E10 in H2. pose proof (bpow_gt_0 radix2 (-338)).
    rewrite (Rabs_right (B2R t)) by lra. split; lra.
  - apply b64ae_le_true in H1; [|exact Fm10|exact Ft]. apply b64ae_le_true in H2; [|exact Ft|exact Fm].
    rewrite Em10 in H1. rewrite Em in H2. pose proof (bpow_gt_0 radix2 (-338)).
    rewrite (Rabs_left (B2R t)) by lra. split; lra.
Qed.

Lemma sgp_intake_complete : forall t, fin t = true ->
  bpow radix2 (-338) <= Rabs (B2R t) -> Rabs (B2R t) <= 10 -> sgp_intake_b t = true.
Proof.
  intros t Ft Hlo Hhi.
  destruct sgp_floor_R as [Ef Ff]. destruct sgp_mfloor_R as [Em Fm].
  destruct sn_ten_R as [E10 F10]. destruct sn_mten_R as [Em10 Fm10].
  pose proof (Rabs_le_inv _ _ Hhi) as [Hh1 Hh2].
  unfold sgp_intake_b.
  destruct (Rle_lt_dec 0 (B2R t)) as [P|N].
  - rewrite (Rabs_right (B2R t)) in Hlo by lra.
    assert (A1 : b64_le sgp_floor t = true) by (apply sr_le_true; [exact Ff | exact Ft | rewrite Ef; exact Hlo]).
    assert (A2 : b64_le t sn_ten = true) by (apply sr_le_true; [exact Ft | exact F10 | rewrite E10; lra]).
    rewrite A1, A2. reflexivity.
  - rewrite (Rabs_left (B2R t)) in Hlo by lra.
    assert (A1 : b64_le sn_mten t = true) by (apply sr_le_true; [exact Fm10 | exact Ft | rewrite Em10; lra]).
    assert (A2 : b64_le t sgp_mfloor = true) by (apply sr_le_true; [exact Ft | exact Fm | rewrite Em; lra]).
    rewrite A1, A2. apply orb_true_r.
Qed.

Inductive sg_outcome : Type := SG_Value (v : binary64) | SG_Decline.

Definition mf_seg_g_outcome_rel (t : binary64) : sg_outcome :=
  if sgp_intake_b t then SG_Value (mf_seg_g_signed t) else SG_Decline.

(* Soundness: a value is only ever produced inside the intake, and is certified. *)
Theorem sgp_outcome_sound : forall t v, mf_seg_g_outcome_rel t = SG_Value v ->
  fin t = true /\ bpow radix2 (-338) <= Rabs (B2R t) /\ Rabs (B2R t) <= 10 /\
  v = mf_seg_g_signed t /\ fin v = true /\
  Rabs (B2R v - (B2R t - sin (B2R t)))
    <= 256 * (b64ae_u * Rabs (B2R t - sin (B2R t))).
Proof.
  intros t v H. unfold mf_seg_g_outcome_rel in H.
  destruct (sgp_intake_b t) eqn:I; [|discriminate H].
  inversion H; subst v. clear H.
  destruct (sgp_intake_sound t I) as [Ft [Hlo Hhi]].
  destruct (sgp_signed_rel t Ft Hlo Hhi) as [F E].
  repeat split; try assumption.
Qed.

(* Completeness: no UNDECIDED inside the intake. *)
Theorem sgp_outcome_complete : forall t, fin t = true ->
  bpow radix2 (-338) <= Rabs (B2R t) -> Rabs (B2R t) <= 10 ->
  mf_seg_g_outcome_rel t = SG_Value (mf_seg_g_signed t).
Proof.
  intros t Ft Hlo Hhi. unfold mf_seg_g_outcome_rel.
  rewrite (sgp_intake_complete t Ft Hlo Hhi). reflexivity.
Qed.

Theorem sgp_outcome_decline : forall t, sgp_intake_b t = false ->
  mf_seg_g_outcome_rel t = SG_Decline.
Proof. intros t H. unfold mf_seg_g_outcome_rel. rewrite H. reflexivity. Qed.

Print Assumptions sgp_g_ge1.
Print Assumptions sgp_total_rel.
Print Assumptions sgp_signed_rel.
Print Assumptions sgp_intake_sound.
Print Assumptions sgp_intake_complete.
Print Assumptions sgp_outcome_sound.
Print Assumptions sgp_outcome_complete.
