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

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance ArcOffset CurveGeometry CurveRingOffset.

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

(* -------------------------------------------------------------------------- *)
(* §2  Lift to a compound clothoid ring: validity of the offset ring.         *)
(*                                                                            *)
(* A curve-aware buffer linearises a clothoid into a chain of osculating arcs *)
(* (radius 1/kappa(tau)).  Each such radius is >= the clothoid minimum radius  *)
(* 1 / Rmax k0 k1 (clothoid_radius_lb), so a clothoid arc-ring is curvature-   *)
(* bounded.  Any curvature-bounded, G1-consistent valid ring offsets to a      *)
(* VALID ring when d respects that minimum radius -- via                       *)
(* CurveRingOffset.curve_ring_offset_valid.                                    *)
(* -------------------------------------------------------------------------- *)

(* Each osculating-arc radius 1/kappa(tau) is at least the clothoid min radius. *)
Lemma clothoid_radius_lb : forall k0 k1 tau,
  0 < k0 -> 0 < k1 -> 0 <= tau <= 1 ->
  1 / Rmax k0 k1 <= 1 / clothoid_curvature k0 k1 tau.
Proof.
  intros k0 k1 tau Hk0 Hk1 Htau.
  destruct (clothoid_curvature_bounds k0 k1 tau Hk0 Hk1 Htau) as [Hkpos Hkmax].
  unfold Rdiv. rewrite !Rmult_1_l.
  apply Rinv_le_contravar; [ exact Hkpos | exact Hkmax ].
Qed.

(* A ring whose every arc has radius >= rmin > 0 is offset-safe for any d > -rmin. *)
Lemma ring_offset_safe_of_radius_lb : forall (r : CurveRing) (rmin d : R),
  0 < rmin -> - rmin < d ->
  Forall (fun s => match s with
                   | CSChord _ _ => True
                   | CSArc a => rmin <= arc_radius a
                   end) r ->
  ring_offset_safe r d.
Proof.
  intros r rmin d Hrmin Hd Hlb.
  unfold ring_offset_safe.
  eapply Forall_impl; [ | exact Hlb ].
  intros s Hs. destruct s as [p q | a]; [ exact I | lra ].
Qed.

(* #1 capstone: a smooth, curvature-bounded clothoid arc-ring offsets to a VALID
   ring when the buffer distance respects the clothoid minimum radius of
   curvature 1 / Rmax k0 k1 (every arc radius is >= that bound, e.g. the
   osculating arcs of a (k0,k1) clothoid via clothoid_radius_lb). *)
Theorem clothoid_ring_offset_valid : forall (r : CurveRing) (k0 k1 d : R),
  0 < k0 -> 0 < k1 ->
  valid_curve_ring r ->
  ring_joins_normals_consistent r ->
  ring_closing_join_normals_consistent r ->
  Forall (fun s => match s with
                   | CSChord _ _ => True
                   | CSArc a => 1 / Rmax k0 k1 <= arc_radius a
                   end) r ->
  - (1 / Rmax k0 k1) < d ->
  valid_curve_ring (curve_ring_offset r d).
Proof.
  intros r k0 k1 d Hk0 Hk1 Hvalid HG1 HG1c Hlb Hd.
  apply curve_ring_offset_valid; try assumption.
  apply (ring_offset_safe_of_radius_lb r (1 / Rmax k0 k1) d); try assumption.
  apply Rdiv_lt_0_compat; [ lra | pose proof (Rmax_l k0 k1); lra ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Sharpness: below the minimum radius the parallel-curve property FAILS. *)
(* The bound `- (1 / Rmax k0 k1) < d` in clothoid_ring_offset_valid is tight:  *)
(* at the tightest arc (radius = the min radius) any d below it inverts the    *)
(* offset (the clothoid-min-radius specialisation of ArcOffset's singularity   *)
(* witness inner_offset_past_center_not_at_distance).  Witness: C origin,       *)
(* X = circle_point C r PI, d = -2r, theta = 0 -> the offset point lands        *)
(* exactly on X (distance 0 < |d| = 2r).                                       *)
(* -------------------------------------------------------------------------- *)
Theorem clothoid_offset_below_min_radius_fails : forall k0 k1,
  0 < k0 -> 0 < k1 ->
  exists (C X : Point) (d theta : R),
    d < - (1 / Rmax k0 k1) /\
    dist C X = 1 / Rmax k0 k1 /\
    dist (arc_offset_point C (1 / Rmax k0 k1) d theta) X < Rabs d.
Proof.
  intros k0 k1 Hk0 Hk1.
  set (r := 1 / Rmax k0 k1).
  assert (Hr : 0 < r)
    by (unfold r; apply Rdiv_lt_0_compat; [ lra | pose proof (Rmax_l k0 k1); lra ]).
  exists (mkPoint 0 0), (circle_point (mkPoint 0 0) r PI), (- (2 * r)), 0.
  split; [ lra | split ].
  - rewrite circle_point_center_dist. apply Rabs_right. lra.
  - unfold arc_offset_point.
    assert (Heq : circle_point (mkPoint 0 0) (r + - (2 * r)) 0
                = circle_point (mkPoint 0 0) r PI).
    { unfold circle_point. cbn [px py].
      rewrite cos_0, sin_0, cos_PI, sin_PI. f_equal; ring. }
    rewrite Heq, dist_refl.
    rewrite Rabs_Ropp, (Rabs_right (2 * r)) by lra. lra.
Qed.

Print Assumptions clothoid_curvature_bounds.
Print Assumptions clothoid_min_radius_safe.
Print Assumptions clothoid_osculating_offset_sound.
Print Assumptions clothoid_radius_lb.
Print Assumptions ring_offset_safe_of_radius_lb.
Print Assumptions clothoid_ring_offset_valid.
Print Assumptions clothoid_offset_below_min_radius_fails.
