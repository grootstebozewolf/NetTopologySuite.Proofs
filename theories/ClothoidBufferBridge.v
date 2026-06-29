(* ============================================================================
   NetTopologySuite.Proofs.ClothoidBufferBridge
   ----------------------------------------------------------------------------
   CLOTHOID-AWARE BUFFER SOUNDNESS: the offset of a clothoid's local osculating
   arc is a valid parallel curve exactly when the buffer distance respects the
   clothoid's MINIMUM radius of curvature.

   A clothoid (ClothoidResidual.v) is a curvature-linear spiral with turning
   angle psi(tau) = k0*tau + (k1-k0)*tau^2/2, hence curvature
       kappa(tau) = psi'(tau) = k0 + (k1 - k0)*tau.
   Its curvature is linear in tau, so over tau in [0,1] the MAXIMUM curvature is
   Rmax k0 k1 (attained at an endpoint) and the MINIMUM radius of curvature is
   1 / Rmax k0 k1.

   A curve-aware buffer linearises a clothoid through its local osculating
   circles (radius 1/kappa); offsetting one is `ArcOffset.arc_offset_point`, and
   `ArcOffset.arc_offset_dist_exact` is its parallel-curve soundness:
       0 <= r -> -r <= d -> (every circle point is >= |d| from the offset, with
       equality at the radial correspondent).
   `ArcOffset.inner_offset_past_center_not_at_distance` shows this FAILS for
   d < -r (the inverted inner-buffer artifact).

   This file connects the two: if the buffer distance satisfies the global
   safety bound `- (1 / Rmax k0 k1) <= d` (i.e. an inner buffer does not exceed
   the clothoid's minimum radius of curvature), then for EVERY tau the local
   osculating-arc offset is sound.  The bite is the INNER buffer (d < 0); outer
   buffers (d >= 0) are trivially safe.

   SCOPE (honest): this is the local osculating-arc soundness -- the standard
   differential-geometry primitive a curve-aware buffer uses -- not a global
   Fresnel-integral offset theorem (the corpus does not materialize the spiral).

   Pure-R; classical-reals trio only (inherits ArcOffset's footprint).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance ArcOffset.

Local Open Scope R_scope.

(* Curvature of the curvature-linear clothoid at arc parameter tau (= psi'(tau),
   the ClothoidResidual turning-angle convention). *)
Definition clothoid_curvature (k0 k1 tau : R) : R := k0 + (k1 - k0) * tau.

(* On tau in [0,1] the curvature is a convex combination of the endpoint
   curvatures: strictly positive and bounded above by their max. *)
Lemma clothoid_curvature_bounds : forall k0 k1 tau,
  0 < k0 -> 0 < k1 -> 0 <= tau <= 1 ->
  0 < clothoid_curvature k0 k1 tau /\ clothoid_curvature k0 k1 tau <= Rmax k0 k1.
Proof.
  intros k0 k1 tau Hk0 Hk1 [Ht0 Ht1].
  assert (Hcombo : clothoid_curvature k0 k1 tau = (1 - tau) * k0 + tau * k1)
    by (unfold clothoid_curvature; ring).
  rewrite Hcombo. split.
  - pose proof (Rmin_l k0 k1) as Hm0. pose proof (Rmin_r k0 k1) as Hm1.
    assert (Hmin : 0 < Rmin k0 k1) by (apply Rmin_glb_lt; assumption).
    assert (A1 : (1 - tau) * Rmin k0 k1 <= (1 - tau) * k0)
      by (apply Rmult_le_compat_l; lra).
    assert (A2 : tau * Rmin k0 k1 <= tau * k1)
      by (apply Rmult_le_compat_l; lra).
    assert (Hid : (1 - tau) * Rmin k0 k1 + tau * Rmin k0 k1 = Rmin k0 k1) by ring.
    lra.
  - pose proof (Rmax_l k0 k1) as HM0. pose proof (Rmax_r k0 k1) as HM1.
    assert (A1 : (1 - tau) * k0 <= (1 - tau) * Rmax k0 k1)
      by (apply Rmult_le_compat_l; lra).
    assert (A2 : tau * k1 <= tau * Rmax k0 k1)
      by (apply Rmult_le_compat_l; lra).
    assert (Hid : (1 - tau) * Rmax k0 k1 + tau * Rmax k0 k1 = Rmax k0 k1) by ring.
    lra.
Qed.

(* The non-vacuous core: respecting the global minimum radius of curvature
   (1 / Rmax k0 k1) forces the local arc-offset safety bound -1/kappa(tau) <= d
   for every tau.  For inner buffers (d < 0) this is the real constraint. *)
Lemma clothoid_min_radius_safe : forall k0 k1 tau d,
  0 < k0 -> 0 < k1 -> 0 <= tau <= 1 ->
  - (1 / Rmax k0 k1) <= d ->
  - (1 / clothoid_curvature k0 k1 tau) <= d.
Proof.
  intros k0 k1 tau d Hk0 Hk1 Htau Hd.
  destruct (clothoid_curvature_bounds k0 k1 tau Hk0 Hk1 Htau) as [Hkpos Hkmax].
  assert (Hinv : 1 / Rmax k0 k1 <= 1 / clothoid_curvature k0 k1 tau).
  { unfold Rdiv. rewrite !Rmult_1_l.
    apply Rinv_le_contravar; [ exact Hkpos | exact Hkmax ]. }
  lra.
Qed.

(* Headline: with the global min-radius safety bound, the offset of the local
   osculating arc (radius 1/kappa(tau)) is a sound parallel curve at distance
   |d| -- every circle point is at least |d| away, attained radially. *)
Theorem clothoid_osculating_offset_sound : forall k0 k1 tau d C theta,
  0 < k0 -> 0 < k1 -> 0 <= tau <= 1 ->
  - (1 / Rmax k0 k1) <= d ->
  (forall X, dist C X = 1 / clothoid_curvature k0 k1 tau ->
     Rabs d <= dist (arc_offset_point C (1 / clothoid_curvature k0 k1 tau) d theta) X)
  /\ dist (arc_offset_point C (1 / clothoid_curvature k0 k1 tau) d theta)
          (circle_point C (1 / clothoid_curvature k0 k1 tau) theta) = Rabs d.
Proof.
  intros k0 k1 tau d C theta Hk0 Hk1 Htau Hd.
  set (r := 1 / clothoid_curvature k0 k1 tau).
  destruct (clothoid_curvature_bounds k0 k1 tau Hk0 Hk1 Htau) as [Hkpos _].
  assert (Hr0 : 0 <= r).
  { unfold r, Rdiv. rewrite Rmult_1_l. left. apply Rinv_0_lt_compat. exact Hkpos. }
  assert (Hsafe : - r <= d).
  { unfold r. apply clothoid_min_radius_safe; assumption. }
  destruct (arc_offset_dist_exact C r d theta Hr0 Hsafe) as [Henc [_ Hatt]].
  split; [ exact Henc | exact Hatt ].
Qed.

Print Assumptions clothoid_curvature_bounds.
Print Assumptions clothoid_min_radius_safe.
Print Assumptions clothoid_osculating_offset_sound.
