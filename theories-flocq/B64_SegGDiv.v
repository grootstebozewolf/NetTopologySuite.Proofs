(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_SegGDiv
   ----------------------------------------------------------------------------
   T3 prerequisite, rung 3: the division by the segment denominator.  The
   ARC_AREA_CENTROID offset is  n / g  with n = 4/3 r s^3 already computed
   (any finite binary64 numerator) and g = theta - sin theta.  With
   g^ = mf_seg_g_poly theta (B64_SegGRel):

     mf_seg_offset n theta = fl(n / g^)

     mf_seg_offset_rel   fin n, fin theta, 2^-338 <= theta <= 1,
                         2^-1022 <= |n / g| <= 2^900, g = theta - sin theta ->
                         fin (mf_seg_offset n theta) /\
                         |q - n / g| <= 28 u |n / g|               (u = 2^-53)

   Budget (units of u |n/g|): relative error of g^ (24 u) through the
   division 24 / (1 - 24 u) ~ 24.01, the division rounding ~ 1.0001, the
   absorbed underflow term 1; total ~ 26.02, stated as 28.

   CONDITIONAL ON THETA.  The statement is about the binary64 value theta that
   is supplied.  In the driver theta comes from libm asin (inventory T1, deferred
   D3) and is NOT certified here; this module says nothing about the distance
   between that theta and the true arc angle.  Nor does it certify the numerator:
   n is any finite binary64 and the bound is relative to the exact quotient
   n / g of THAT n.  The floors 2^-1022 <= |n/g| (quotient normal) and
   |n/g| <= 2^900 (no overflow) are hypotheses, not claims about the inputs.
   claimId: t3-seg-g-div.  Evaluation only: no extraction, no oracle mode, no
   port, no policy wiring, no consumer switch.  No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly B64_Sin B64_SinRel B64_SegGRel.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  One RNE division, absolute-error form.                                 *)
(* -------------------------------------------------------------------------- *)

Lemma b64ae_div_err : forall x y,
  fin x = true -> fin y = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= bpow radix2 1000 ->
  fin (b64_div x y) = true /\
  Rabs (B2R (b64_div x y) - B2R x / B2R y)
    <= b64ae_u * Rabs (B2R x / B2R y) + b64ae_e0.
Proof.
  intros x y Fx Fy Hy Hb.
  assert (Hr : Rabs (b64_round (B2R x / B2R y)) < bpow radix2 emax).
  { eapply Rle_lt_trans.
    - apply (b64_round_abs_le_bpow _ 1000); [unfold emax; lia | exact Hb].
    - apply bpow_lt. unfold emax. lia. }
  destruct (b64_div_correct x y Fx Fy Hy Hr) as [E F].
  split; [exact F|]. rewrite E. apply b64ae_round_err.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The relative budget as pure real algebra.                              *)
(* -------------------------------------------------------------------------- *)

Lemma sd_alg : forall (N g gh q e : R),
  0 < g -> 0 < gh ->
  Rabs (gh - g) <= 24 * (/ 9007199254740992 * g) ->
  Rabs (q - N / gh) <= / 9007199254740992 * Rabs (N / gh) + e ->
  e <= / 9007199254740992 * Rabs (N / g) ->
  Rabs (q - N / g) <= 28 * (/ 9007199254740992 * Rabs (N / g)).
Proof.
  intros N g gh q e Hg Hgh Hrel Hq He.
  set (U := / 9007199254740992) in *.
  assert (HU : 0 < U <= / 1000) by (unfold U; lra).
  set (R := N / g) in *. set (rho := Rabs R) in *.
  assert (Hrho : 0 <= rho) by apply Rabs_pos.
  set (k := g / gh).
  assert (Hk0 : 0 < k) by (unfold k; apply Rdiv_lt_0_compat; assumption).
  assert (Hgk : gh * k = g) by (unfold k; field; lra).
  (* |k - 1| <= 24 U k *)
  assert (Hk1 : Rabs (k - 1) <= 24 * U * k).
  { assert (Hm : Rabs (gh - g) = gh * Rabs (k - 1)).
    { replace (gh - g) with (gh * (1 - k)) by (rewrite Rmult_minus_distr_l; lra).
      rewrite Rabs_mult, (Rabs_right gh) by lra. rewrite <- (Rabs_Ropp (1 - k)).
      replace (- (1 - k)) with (k - 1) by ring. reflexivity. }
    rewrite Hm in Hrel.
    assert (gh * Rabs (k - 1) <= gh * (24 * U * k)).
    { replace (gh * (24 * U * k)) with (24 * (U * (gh * k))) by ring.
      rewrite Hgk. exact Hrel. }
    apply Rmult_le_reg_l with gh; [exact Hgh | exact H]. }
  pose proof (Rabs_le_inv _ _ Hk1) as [Hk1l Hk1u].
  assert (Hkb : k <= 10001 / 10000) by (unfold U in *; lra).
  assert (HNgh : N / gh = R * k) by (unfold R, k; field; lra).
  assert (Hdiff : Rabs (N / gh - R) <= rho * (24 * U * k)).
  { replace (N / gh - R) with (R * (k - 1)) by (rewrite HNgh; ring).
    rewrite Rabs_mult. apply Rmult_le_compat_l; [exact Hrho | exact Hk1]. }
  assert (Habs : Rabs (N / gh) <= rho * (10001 / 10000)).
  { rewrite HNgh, Rabs_mult, (Rabs_right k) by lra.
    apply Rmult_le_compat_l; [exact Hrho | exact Hkb]. }
  assert (Hd2 : rho * (24 * U * k) <= rho * (24 * U * (10001 / 10000))).
  { apply Rmult_le_compat_l; [exact Hrho|].
    apply Rmult_le_compat_l; [lra | exact Hkb]. }
  assert (Hu2 : U * Rabs (N / gh) <= U * (rho * (10001 / 10000)))
    by (apply Rmult_le_compat_l; [lra | exact Habs]).
  replace (q - R) with ((q - N / gh) + (N / gh - R)) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  assert (HUr : 0 <= U * rho) by (apply Rmult_le_pos; lra).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The division, conditional on the supplied theta.                       *)
(* -------------------------------------------------------------------------- *)

Definition mf_seg_offset (n t : binary64) : binary64 := b64_div n (mf_seg_g_poly t).

(* WITNESS-free: registered in verified-claims.md (claimId t3-seg-g-div). *)
Theorem mf_seg_offset_rel : forall n t, fin n = true -> fin t = true ->
  bpow radix2 (-338) <= B2R t -> B2R t <= 1 ->
  bpow radix2 (-1022) <= Rabs (B2R n / (B2R t - sin (B2R t))) ->
  Rabs (B2R n / (B2R t - sin (B2R t))) <= bpow radix2 900 ->
  fin (mf_seg_offset n t) = true /\
  Rabs (B2R (mf_seg_offset n t) - B2R n / (B2R t - sin (B2R t)))
    <= 28 * (b64ae_u * Rabs (B2R n / (B2R t - sin (B2R t)))).
Proof.
  intros n t Fn Ft Hlo Hhi Hfl Hov.
  set (a := B2R t) in *. set (g := a - sin a) in *.
  pose proof sp_u_val as Uv.
  destruct (mf_seg_g_poly_rel t Ft Hlo Hhi) as [Fg Eg].
  pose proof (mf_seg_g_poly_pos t Ft Hlo Hhi) as Hghpos.
  pose proof (sg_g_enclosure a ltac:(pose proof (bpow_gt_0 radix2 (-338)); lra)) as [Gl _].
  assert (Ha : 0 < a) by (pose proof (bpow_gt_0 radix2 (-338)); lra).
  assert (HA : 0 < a * (a * a)) by (apply Rmult_lt_0_compat; [lra | nra]).
  assert (Hg : 0 < g) by (unfold g; lra).
  set (gh := B2R (mf_seg_g_poly t)) in *.
  assert (Hb9 : bpow radix2 900 <= bpow radix2 1000) by (apply bpow_le; lia).
  (* |n / g^| <= 2^1000: from the relative error of g^ *)
  assert (Hrel : Rabs (gh - g) <= 24 * (b64ae_u * g)) by exact Eg.
  rewrite Uv in Hrel.
  assert (Hgh1 : g / 2 <= gh) by (apply Rabs_le_inv in Hrel; lra).
  assert (Hq0 : Rabs (B2R n / gh) <= 2 * Rabs (B2R n / g)).
  { replace (B2R n / gh) with ((B2R n / g) * (g / gh)) by (field; lra).
    rewrite Rabs_mult, (Rabs_right (g / gh)).
    - assert (g / gh <= 2).
      { apply Rmult_le_reg_r with gh; [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
      assert (0 <= Rabs (B2R n / g)) by apply Rabs_pos. nra.
    - apply Rle_ge. apply Rlt_le. apply Rdiv_lt_0_compat; lra. }
  assert (Hbd : Rabs (B2R n / gh) <= bpow radix2 1000).
  { assert (2 * bpow radix2 900 <= bpow radix2 1000).
    { replace (bpow radix2 1000) with (bpow radix2 1 * bpow radix2 999) by (rewrite <- bpow_plus; reflexivity).
      assert (bpow radix2 900 <= bpow radix2 999) by (apply bpow_le; lia).
      replace (bpow radix2 1) with 2 by reflexivity. lra. }
    lra. }
  destruct (b64ae_div_err n (mf_seg_g_poly t) Fn Fg ltac:(change (B2R (mf_seg_g_poly t)) with gh; lra) Hbd)
    as [Fq Eq].
  split; [exact Fq|].
  change (B2R (mf_seg_g_poly t)) with gh in Eq.
  unfold mf_seg_offset. rewrite Uv.
  pose proof (tiny_abs_to_rel (B2R n / g) Hfl) as Tiny. rewrite Uv in Tiny.
  rewrite Uv in Eq.
  exact (sd_alg (B2R n) g gh (B2R (b64_div n (mf_seg_g_poly t))) b64ae_e0 Hg Hghpos Hrel Eq Tiny).
Qed.

Print Assumptions b64ae_div_err.
Print Assumptions sd_alg.
Print Assumptions mf_seg_offset_rel.
