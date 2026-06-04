(* ============================================================================
   NetTopologySuite.Proofs.BufferMiterAngle
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2b seam: MITER-CAP <-> HALF-ANGLE SOUNDNESS.

   Bridges the algebraic miter-limit test of theories/BufferMiter.v to the
   trigonometric half-angle form of theories/Azimuth.v (see
   docs/buffer-noder-pipeline.md §2.2 / slice S3; JTS#180).

   The miter apex of two edges of direction ein, eout (BufferMiter.miter_apex)
   sits at |V->apex| = d / sin(half-angle of the corner), where the corner
   half-angle is measured between ein and the REVERSED outgoing edge `vneg eout`
   (the actual angle at the vertex between the two segments).  Concretely:

     - `miter_numerator_sin_half`: the offset numerator N times
       (sin_half_turn ein (vneg eout))^2 equals det^2.  Hence
       |V->apex|^2 / d^2 = N / det^2 = 1 / sin_half_turn(ein, vneg eout)^2.

     - `miter_cap_iff_sin_half`: the END-TO-END soundness -- for a positive
       buffer distance and positive limit, the apex lies within the cap
       L*d iff `1 <= L * sin_half_turn ein (vneg eout)`, which is exactly the
       operational BufferParameters miter test
       `Azimuth.miter_ratio_le_iff`.

   So the division-free algebraic cap of `BufferMiter.miter_within_limit_iff`
   and the half-angle cap of `Azimuth` decide the SAME thing.

   Audit footprint.  Imports `theories/Azimuth.v`, whose `sin_half_turn` /
   `miter_ratio_le_iff` are built on `sqrt` only (no `atan`), so this file
   is THREE-AXIOM CLEAN (verified by `Print Assumptions`: no
   `Classical_Prop.classic`).  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Vec Direction Distance BufferOffset BufferMiter Azimuth.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Small bridges.                                                         *)
(* -------------------------------------------------------------------------- *)

(* Azimuth.vmag and BufferOffset.vmag are the same function (both sqrt of
   vmag_sq); convertible. *)
Lemma vmag_az_bo : forall v, Azimuth.vmag v = BufferOffset.vmag v.
Proof. intros v. reflexivity. Qed.

(* Negation does not change magnitude. *)
Lemma vmag_vneg : forall v, Azimuth.vmag (vneg v) = Azimuth.vmag v.
Proof. intros v. unfold Azimuth.vmag. rewrite vmag_sq_neg. reflexivity. Qed.

Lemma vneg_nonzero : forall eout, eout <> vzero -> vneg eout <> vzero.
Proof.
  intros [wx wy] Hout H. apply Hout.
  unfold vneg, vzero in H. injection H as H1 H2.
  apply Vec_eq; simpl; lra.
Qed.

(* BufferOffset.vmag is strictly positive on nonzero vectors. *)
Lemma bo_vmag_pos : forall v, v <> vzero -> 0 < BufferOffset.vmag v.
Proof.
  intros v Hv. unfold BufferOffset.vmag. apply sqrt_lt_R0.
  apply vmag_sq_pos; exact Hv.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The key identity: N * sin_half_turn(ein, vneg eout)^2 = det^2.              *)
(* -------------------------------------------------------------------------- *)

Lemma miter_numerator_sin_half : forall ein eout,
  ein <> vzero -> eout <> vzero ->
  ((BufferOffset.vmag ein * vx eout - BufferOffset.vmag eout * vx ein) ^ 2
   + (BufferOffset.vmag ein * vy eout - BufferOffset.vmag eout * vy ein) ^ 2)
  * (sin_half_turn ein (vneg eout)) ^ 2
  = (miter_det ein eout) ^ 2.
Proof.
  intros ein eout Hin Hout.
  pose proof (vneg_nonzero eout Hout) as Hnw.
  rewrite (sin_half_turn_sq ein (vneg eout) Hin Hnw).
  rewrite vdot_neg_r, vmag_vneg.
  rewrite miter_numerator_cos, miter_det_sq_lagrange.
  (* unfold both vmag's to the common sqrt(vmag_sq _) so they are one atom *)
  unfold Azimuth.vmag, BufferOffset.vmag.
  assert (Hu2 : sqrt (vmag_sq ein) * sqrt (vmag_sq ein) = vmag_sq ein)
    by (apply sqrt_sqrt; apply vmag_sq_nonneg).
  assert (Hw2 : sqrt (vmag_sq eout) * sqrt (vmag_sq eout) = vmag_sq eout)
    by (apply sqrt_sqrt; apply vmag_sq_nonneg).
  assert (HUp : 0 < sqrt (vmag_sq ein))
    by (apply sqrt_lt_R0; apply vmag_sq_pos; exact Hin).
  assert (HWp : 0 < sqrt (vmag_sq eout))
    by (apply sqrt_lt_R0; apply vmag_sq_pos; exact Hout).
  set (U := sqrt (vmag_sq ein)) in *.
  set (W := sqrt (vmag_sq eout)) in *.
  (* eliminate vmag_sq ein/eout in favour of U*U, W*W *)
  rewrite <- Hu2, <- Hw2.
  assert (HU0 : U <> 0) by (apply Rgt_not_eq; exact HUp).
  assert (HW0 : W <> 0) by (apply Rgt_not_eq; exact HWp).
  field_simplify_eq; try ring; try (split; assumption); try assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  End-to-end: the algebraic cap and the half-angle cap agree.            *)
(* -------------------------------------------------------------------------- *)

Theorem miter_cap_iff_sin_half : forall V ein eout d L,
  ein <> vzero -> eout <> vzero -> miter_det ein eout <> 0 ->
  0 < d -> 0 < L ->
  dist_sq V (miter_apex V ein eout d) <= (L * d) ^ 2
  <-> 1 <= L * sin_half_turn ein (vneg eout).
Proof.
  intros V ein eout d L Hin Hout Hdet Hd HL.
  rewrite (miter_within_limit_iff V ein eout d L Hdet Hd).
  pose proof (miter_numerator_sin_half ein eout Hin Hout) as HK.
  set (N := (BufferOffset.vmag ein * vx eout - BufferOffset.vmag eout * vx ein) ^ 2
            + (BufferOffset.vmag ein * vy eout - BufferOffset.vmag eout * vy ein) ^ 2) in *.
  set (s := sin_half_turn ein (vneg eout)) in *.
  assert (Hsnn : 0 <= s) by apply sin_half_turn_nonneg.
  assert (Hdet2 : 0 < (miter_det ein eout) ^ 2).
  { assert (miter_det ein eout <> 0) by exact Hdet. nra. }
  assert (HNnn : 0 <= N)
    by (unfold N; apply Rplus_le_le_0_compat; apply pow2_ge_0).
  (* From HK: N * s^2 = det^2 > 0, with N >= 0, s >= 0 -> N > 0 and s > 0. *)
  assert (HNpos : 0 < N).
  { destruct (Rle_lt_or_eq_dec 0 N HNnn) as [H|H]; [exact H|].
    exfalso. rewrite <- H in HK. rewrite Rmult_0_l in HK. lra. }
  assert (Hspos : 0 < s).
  { destruct (Rle_lt_or_eq_dec 0 s Hsnn) as [H|H]; [exact H|].
    exfalso. rewrite <- H in HK.
    replace (0 ^ 2) with 0 in HK by ring.
    rewrite Rmult_0_r in HK. lra. }
  assert (HLspos : 0 < L * s) by (apply Rmult_lt_0_compat; assumption).
  assert (Hsq : (L * s) ^ 2 = L ^ 2 * s ^ 2) by ring.
  rewrite <- HK.
  split.
  - intro H.
    (* N <= L^2 * (N * s^2)  ->  1 <= L^2 s^2  ->  1 <= L s *)
    assert (HLs2 : 1 <= L ^ 2 * s ^ 2).
    { apply Rmult_le_reg_l with (r := N).
      - exact HNpos.
      - rewrite Rmult_1_r.
        apply Rle_trans with (r2 := L ^ 2 * (N * s ^ 2)); [ exact H | right; ring ]. }
    (* 1 <= (L*s)^2 with 0 < L*s -> 1 <= L*s *)
    assert (HsqLs : 1 <= (L * s) ^ 2) by (rewrite Hsq; exact HLs2).
    nra.
  - intro H.
    (* 1 <= L s  ->  1 <= (L s)^2 = L^2 s^2  ->  N <= L^2 (N s^2) *)
    assert (HLs2 : 1 <= L ^ 2 * s ^ 2).
    { rewrite <- Hsq. nra. }
    apply Rle_trans with (r2 := N * (L ^ 2 * s ^ 2)); [ | right; ring ].
    rewrite <- (Rmult_1_r N) at 1.
    apply Rmult_le_compat_l; [ lra | exact HLs2 ].
Qed.
