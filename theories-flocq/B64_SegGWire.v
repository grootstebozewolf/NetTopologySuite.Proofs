(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_SegGWire
   ----------------------------------------------------------------------------
   T3 prerequisite, rung 5: the division wired to the TOTAL evaluator.  The
   consumer's offset is  n / g  with g = theta - sin theta.  With
   g^ = mf_seg_g_signed theta (B64_SegGPolicy, relative 256 u |g| on the whole
   signed intake 2^-338 <= |theta| <= 10):

     mf_seg_offset_total n theta = fl(n / g^)

     sgw_offset_rel   fin n, fin theta, 2^-338 <= |theta| <= 10,
                      2^-1022 <= |n/g| <= 2^900, g = theta - sin theta ->
                      fin q /\ |q - n/g| <= 260 u |n/g|            (u = 2^-53)

   Budget (units of u |n/g|): relative error of g^ (256 u) through the
   division 256 / (1 - 256 u) ~ 256.03, division rounding ~ 1.0001, absorbed
   underflow 1; total ~ 258.03, stated as 260.  g^ and g have the same sign
   (|g^ - g| <= 256 u |g| < |g|), proved, not assumed.

     mf_seg_offset_outcome n theta = SG_Value q only inside the intake;
     SG_Decline outside (sgw_outcome_decline); inside the intake and under the
     two quotient floors the value is exactly q and certified
     (sgw_outcome_value).

   CONDITIONAL ON THETA exactly as B64_SegGDiv: where the supplied theta comes
   from (libm asin, inventory T1, deferred D3) is not certified, the numerator n
   is any finite binary64, and the bound is relative to the exact quotient of THAT
   n.  The two quotient floors 2^-1022 <= |n/g| <= 2^900 are hypotheses about
   the exact quotient, not runtime checks; a consumer that cannot establish them
   must treat a non-finite or tiny q itself.  The unsigned B64_SegGDiv result
   (poly path only, 28 u) stays as the sharper statement on [2^-338, 1].
   claimId: t3-seg-g-wire.  Evaluation only: no extraction, no oracle mode, no
   port, no corpus run, no consumer switch.  No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly B64_Sin B64_SinRel B64_SegGRel
  B64_SegGDiv B64_SegGPolicy.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  The relative budget for a signed denominator, pure real algebra.       *)
(* -------------------------------------------------------------------------- *)

Lemma sgw_alg : forall (N g gh q e : R),
  g <> 0 -> 0 < g * gh ->
  Rabs (gh - g) <= 256 * (/ 9007199254740992 * Rabs g) ->
  Rabs (q - N / gh) <= / 9007199254740992 * Rabs (N / gh) + e ->
  e <= / 9007199254740992 * Rabs (N / g) ->
  Rabs (q - N / g) <= 260 * (/ 9007199254740992 * Rabs (N / g)).
Proof.
  intros N g gh q e Hg0 Hsame Hrel Hq He.
  set (U := / 9007199254740992) in *.
  assert (HU : 0 < U <= / 1000) by (unfold U; lra).
  assert (Hgh0 : gh <> 0) by (intro H; rewrite H, Rmult_0_r in Hsame; lra).
  set (R := N / g) in *. set (rho := Rabs R) in *.
  assert (Hrho : 0 <= rho) by apply Rabs_pos.
  set (k := g / gh).
  assert (Hk0 : 0 < k).
  { unfold k. replace (g / gh) with ((g * gh) / (gh * gh)) by (field; exact Hgh0).
    pose proof (Rlt_0_sqr gh Hgh0) as Hsq. unfold Rsqr in Hsq.
    apply Rdiv_lt_0_compat; [exact Hsame | exact Hsq]. }
  assert (Hgk : g = gh * k) by (unfold k; field; exact Hgh0).
  assert (Hghp : 0 < Rabs gh) by (apply Rabs_pos_lt; exact Hgh0).
  assert (Hk1 : Rabs (k - 1) <= 256 * U * k).
  { assert (Hm : Rabs (gh - g) = Rabs gh * Rabs (k - 1)).
    { replace (gh - g) with (gh * (1 - k)) by (rewrite Hgk; ring).
      rewrite Rabs_mult, Rabs_minus_sym. reflexivity. }
    assert (Hg' : Rabs g = Rabs gh * k).
    { rewrite Hgk at 1. rewrite Rabs_mult, (Rabs_right k) by lra. reflexivity. }
    rewrite Hm, Hg' in Hrel.
    assert (Rabs gh * Rabs (k - 1) <= Rabs gh * (256 * U * k)) by nra.
    apply Rmult_le_reg_l with (Rabs gh); [exact Hghp | exact H]. }
  pose proof (Rabs_le_inv _ _ Hk1) as [Hk1l Hk1u].
  assert (Hkb : k <= 10001 / 10000) by (unfold U in *; lra).
  assert (HNgh : N / gh = R * k) by (unfold R, k; field; split; assumption).
  assert (Hdiff : Rabs (N / gh - R) <= rho * (256 * U * k)).
  { replace (N / gh - R) with (R * (k - 1)) by (rewrite HNgh; ring).
    rewrite Rabs_mult. apply Rmult_le_compat_l; [exact Hrho | exact Hk1]. }
  assert (Habs : Rabs (N / gh) <= rho * (10001 / 10000)).
  { rewrite HNgh, Rabs_mult, (Rabs_right k) by lra.
    apply Rmult_le_compat_l; [exact Hrho | exact Hkb]. }
  assert (Hd2 : rho * (256 * U * k) <= rho * (256 * U * (10001 / 10000))).
  { apply Rmult_le_compat_l; [exact Hrho|].
    apply Rmult_le_compat_l; [lra | exact Hkb]. }
  assert (Hu2 : U * Rabs (N / gh) <= U * (rho * (10001 / 10000)))
    by (apply Rmult_le_compat_l; [lra | exact Habs]).
  replace (q - R) with ((q - N / gh) + (N / gh - R)) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  assert (HUr : 0 <= U * rho) by (apply Rmult_le_pos; lra).
  lra.
Qed.

(* g is nonzero on the intake, with the sign of theta. *)
Lemma sgw_g_ne0 : forall a, bpow radix2 (-338) <= Rabs a -> Rabs a <= 10 ->
  a - sin a <> 0.
Proof.
  intros a Hlo Hhi H.
  pose proof (Rabs_le_inv _ _ Hhi) as [Hh1 Hh2].
  destruct (Rle_lt_dec 0 a) as [P|N].
  - rewrite (Rabs_right a) in Hlo by lra.
    pose proof (sgp_g_pos a Hlo Hh2). lra.
  - rewrite (Rabs_left a) in Hlo by lra.
    pose proof (sgp_g_pos (- a) Hlo ltac:(lra)) as Hp.
    rewrite sin_neg in Hp. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The division of the total evaluator.                                   *)
(* -------------------------------------------------------------------------- *)

Definition mf_seg_offset_total (n t : binary64) : binary64 :=
  b64_div n (mf_seg_g_signed t).

Theorem sgw_offset_rel : forall n t, fin n = true -> fin t = true ->
  bpow radix2 (-338) <= Rabs (B2R t) -> Rabs (B2R t) <= 10 ->
  bpow radix2 (-1022) <= Rabs (B2R n / (B2R t - sin (B2R t))) ->
  Rabs (B2R n / (B2R t - sin (B2R t))) <= bpow radix2 900 ->
  fin (mf_seg_offset_total n t) = true /\
  Rabs (B2R (mf_seg_offset_total n t) - B2R n / (B2R t - sin (B2R t)))
    <= 260 * (b64ae_u * Rabs (B2R n / (B2R t - sin (B2R t)))).
Proof.
  intros n t Fn Ft Hlo Hhi Hfl Hov.
  set (a := B2R t) in *. set (g := a - sin a) in *.
  pose proof sp_u_val as Uv.
  destruct (sgp_signed_rel t Ft Hlo Hhi) as [Fg Eg].
  change (B2R t) with a in Eg. change (a - sin a) with g in Eg.
  set (gh := B2R (mf_seg_g_signed t)) in *.
  assert (Hg0 : g <> 0) by (unfold g; exact (sgw_g_ne0 a Hlo Hhi)).
  assert (Hgp : 0 < Rabs g) by (apply Rabs_pos_lt; exact Hg0).
  rewrite Uv in Eg.
  assert (Hsmall : 256 * (/ 9007199254740992 * Rabs g) <= Rabs g / 2)
    by (assert (0 <= Rabs g) by apply Rabs_pos; lra).
  pose proof (Rabs_le_inv _ _ Eg) as [Eg1 Eg2].
  assert (Hsame : 0 < g * gh).
  { destruct (Rle_lt_dec 0 g) as [P|N].
    - assert (Hpos : 0 < g)
        by (destruct (Rle_lt_or_eq_dec 0 g P) as [H|H]; [exact H | exfalso; apply Hg0; symmetry; exact H]).
      assert (Hr : Rabs g = g) by (apply Rabs_right; lra).
      rewrite Hr in Eg1. rewrite Hr in Hsmall.
      assert (0 < gh) by lra.
      apply Rmult_lt_0_compat; assumption.
    - assert (Hr : Rabs g = - g) by (apply Rabs_left; exact N).
      rewrite Hr in Eg2. rewrite Hr in Hsmall.
      assert (gh < 0) by lra.
      nra. }
  assert (Hgh0 : gh <> 0) by (intro H; rewrite H, Rmult_0_r in Hsame; lra).
  (* |gh| >= |g|/2, hence |n/gh| <= 2 |n/g| *)
  assert (Hghg : Rabs g / 2 <= Rabs gh).
  { pose proof (Rabs_triang_inv g gh) as T. rewrite Rabs_minus_sym in T.
    pose proof (Rabs_minus_sym g gh). lra. }
  assert (Hq0 : Rabs (B2R n / gh) <= 2 * Rabs (B2R n / g)).
  { replace (B2R n / gh) with ((B2R n / g) * (g / gh)) by (field; split; assumption).
    rewrite Rabs_mult.
    assert (Hr : Rabs (g / gh) <= 2).
    { unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact Hgh0.
      assert (Hp : 0 < Rabs gh) by (apply Rabs_pos_lt; exact Hgh0).
      apply Rmult_le_reg_r with (Rabs gh); [exact Hp|].
      rewrite Rmult_assoc, Rinv_l by lra. lra. }
    assert (0 <= Rabs (B2R n / g)) by apply Rabs_pos. nra. }
  assert (Hb9 : 2 * bpow radix2 900 <= bpow radix2 1000).
  { replace (bpow radix2 1000) with (bpow radix2 1 * bpow radix2 999)
      by (rewrite <- bpow_plus; reflexivity).
    assert (bpow radix2 900 <= bpow radix2 999) by (apply bpow_le; lia).
    replace (bpow radix2 1) with 2 by reflexivity. lra. }
  assert (Hbd : Rabs (B2R n / gh) <= bpow radix2 1000) by lra.
  destruct (b64ae_div_err n (mf_seg_g_signed t) Fn Fg
              ltac:(change (B2R (mf_seg_g_signed t)) with gh; exact Hgh0) Hbd)
    as [Fq Eq].
  split; [exact Fq|].
  change (B2R (mf_seg_g_signed t)) with gh in Eq.
  unfold mf_seg_offset_total. rewrite Uv.
  pose proof (tiny_abs_to_rel (B2R n / g) Hfl) as Tiny. rewrite Uv in Tiny.
  rewrite Uv in Eq.
  exact (sgw_alg (B2R n) g gh (B2R (b64_div n (mf_seg_g_signed t))) b64ae_e0
           Hg0 Hsame Eg Eq Tiny).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The outcome.                                                           *)
(* -------------------------------------------------------------------------- *)

Definition mf_seg_offset_outcome (n t : binary64) : sg_outcome :=
  if sgp_intake_b t then SG_Value (mf_seg_offset_total n t) else SG_Decline.

Theorem sgw_outcome_decline : forall n t, sgp_intake_b t = false ->
  mf_seg_offset_outcome n t = SG_Decline.
Proof. intros n t H. unfold mf_seg_offset_outcome. rewrite H. reflexivity. Qed.

(* A value only inside the intake. *)
Theorem sgw_outcome_sound : forall n t v, mf_seg_offset_outcome n t = SG_Value v ->
  fin t = true /\ bpow radix2 (-338) <= Rabs (B2R t) /\ Rabs (B2R t) <= 10 /\
  v = mf_seg_offset_total n t.
Proof.
  intros n t v H. unfold mf_seg_offset_outcome in H.
  destruct (sgp_intake_b t) eqn:I; [|discriminate H].
  inversion H; subst v. clear H.
  destruct (sgp_intake_sound t I) as [Ft [Hlo Hhi]].
  repeat split; assumption.
Qed.

(* Inside the intake, under the two quotient floors: a certified value. *)
Theorem sgw_outcome_value : forall n t, fin n = true -> fin t = true ->
  bpow radix2 (-338) <= Rabs (B2R t) -> Rabs (B2R t) <= 10 ->
  bpow radix2 (-1022) <= Rabs (B2R n / (B2R t - sin (B2R t))) ->
  Rabs (B2R n / (B2R t - sin (B2R t))) <= bpow radix2 900 ->
  exists v, mf_seg_offset_outcome n t = SG_Value v /\ fin v = true /\
    Rabs (B2R v - B2R n / (B2R t - sin (B2R t)))
      <= 260 * (b64ae_u * Rabs (B2R n / (B2R t - sin (B2R t)))).
Proof.
  intros n t Fn Ft Hlo Hhi Hfl Hov.
  destruct (sgw_offset_rel n t Fn Ft Hlo Hhi Hfl Hov) as [F E].
  exists (mf_seg_offset_total n t). split; [|split; assumption].
  unfold mf_seg_offset_outcome. rewrite (sgp_intake_complete t Ft Hlo Hhi). reflexivity.
Qed.

Print Assumptions sgw_alg.
Print Assumptions sgw_g_ne0.
Print Assumptions sgw_offset_rel.
Print Assumptions sgw_outcome_sound.
Print Assumptions sgw_outcome_value.
