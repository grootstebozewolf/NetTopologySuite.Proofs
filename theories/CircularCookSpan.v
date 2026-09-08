(* ============================================================================
   NetTopologySuite.Proofs.CircularCookSpan
   ----------------------------------------------------------------------------
   Core-slice rung after CircularCookHit: span-restricted γ on CircularArc.

   For a valid_arc, γ interpolates the principal signed span from start to
   end (ArcSpanAtan2.arc_angle_from_start / circ_gamma).  This is a
   constructed interpolant — not CircGammaDischarged on the 3-axiom host
   (CircularCook cannot Require this sidecar without importing atan2 /
   Classic).

   QED: γ(0)=start, γ(1)=end, γ(t) on the circumcircle; interior t land in
   the atan2 span when the mid lies on the principal path; retract for
   on-circle points in that span; locked proper-arc Hit on the (0,0)/(7,0)
   r=5 radical pair keeps p+ and rejects p−.

   QEX (host CircGamma): 3-axiom interpolant on CircularArc, or a host-lane
   policy change allowing this sidecar to flip circular_gamma_status.
   Stated as that remaining obligation — not a bool proved by `right`.

   first_cook_scope stays chord–chord.  Not glossary 𝓘.  Not a noder.
   Not OverlayNGCurve / fully_intersected / ticket 523.

   WITNESS topic: core · claimId: 64-circ-span-gamma · witness: 64-circ-span-locked
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import ZArith Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcIntersect
  ArcOffsetThreePoint ArcArcCircles Atan2 AngleBetween ArcSpanAtan2
  CircularCook CircularCookHit.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Span-restricted interpolant on CircularArc.                            *)
(* -------------------------------------------------------------------------- *)

Definition arc_span (a : CircularArc) : R :=
  arc_angle_from_start a (arc_end a).

Definition arc_gamma (a : CircularArc) (t : R) : Point :=
  let O := arc_center a in
  let r := arc_radius a in
  let th0 := circ_angle O (arc_start a) in
  circ_gamma O r ((th0 + t * arc_span a) / (2 * PI)).

Definition arc_t (a : CircularArc) (P : Point) : R :=
  arc_angle_from_start a P / arc_span a.

Definition on_arc_gamma (a : CircularArc) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = arc_gamma a t.

(* Mid lies strictly between 0 and the principal start→end angle. *)
Definition arc_mid_on_principal_span (a : CircularArc) : Prop :=
  0 < arc_angle_from_start a (arc_mid a)
      * (arc_span a - arc_angle_from_start a (arc_mid a)).

(* -------------------------------------------------------------------------- *)
(* §2  Polar helpers (reuse atan2_on_circle / angle_between; no new stack).   *)
(* -------------------------------------------------------------------------- *)

Lemma circ_gamma_at_angle : forall O r alpha,
  circ_gamma O r (alpha / (2 * PI)) =
  mkPoint (px O + r * cos alpha) (py O + r * sin alpha).
Proof.
  intros O r alpha.
  unfold circ_gamma.
  pose proof two_PI_pos as H2.
  replace (2 * PI * (alpha / (2 * PI))) with alpha by (field; lra).
  reflexivity.
Qed.

Lemma arc_gamma_polar : forall a t,
  arc_gamma a t =
  mkPoint (px (arc_center a)
            + arc_radius a * cos (circ_angle (arc_center a) (arc_start a)
                                  + t * arc_span a))
          (py (arc_center a)
            + arc_radius a * sin (circ_angle (arc_center a) (arc_start a)
                                  + t * arc_span a)).
Proof.
  intros a t. unfold arc_gamma. rewrite circ_gamma_at_angle. reflexivity.
Qed.

Lemma start_offset_from_angle : forall a,
  valid_arc a ->
  px (arc_start a) - px (arc_center a)
    = arc_radius a * cos (circ_angle (arc_center a) (arc_start a)) /\
  py (arc_start a) - py (arc_center a)
    = arc_radius a * sin (circ_angle (arc_center a) (arc_start a)).
Proof.
  intros a Hva.
  set (O := arc_center a).
  set (r := arc_radius a).
  set (A := arc_start a).
  assert (Hr : 0 < r) by (apply arc_radius_pos; exact Hva).
  assert (HA : dist_sq O A = r * r).
  { unfold r, O, A, arc_radius, dist.
    rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  assert (Hne := circ_point_ne_of_on_circle O A r Hr HA).
  pose proof (atan2_on_circle (px A - px O) (py A - py O) Hne) as [Hc Hs].
  pose proof (circ_radius_sqrt O A r Hr HA) as Hsr.
  rewrite Hsr in Hc, Hs.
  unfold circ_angle. split; [exact Hc | exact Hs].
Qed.

Lemma rotate_dot_cross_x : forall sx sy ex ey,
  sx * (sx * ex + sy * ey) - sy * (sx * ey - sy * ex)
  = (sx * sx + sy * sy) * ex.
Proof. intros. ring. Qed.

Lemma rotate_dot_cross_y : forall sx sy ex ey,
  sy * (sx * ex + sy * ey) + sx * (sx * ey - sy * ex)
  = (sx * sx + sy * sy) * ey.
Proof. intros. ring. Qed.

Lemma arc_start_dist_sq : forall a,
  dist_sq (arc_center a) (arc_start a) = arc_radius a * arc_radius a.
Proof.
  intros a. unfold arc_radius, dist.
  rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg].
Qed.

Lemma arc_end_dist_sq : forall a,
  valid_arc a ->
  dist_sq (arc_center a) (arc_end a) = arc_radius a * arc_radius a.
Proof.
  intros a Hva.
  rewrite <- (arc_center_dist_end a Hva).
  unfold dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg].
Qed.

Lemma on_circle_offset_from_start_angle : forall a P,
  valid_arc a ->
  dist_sq (arc_center a) P = arc_radius a * arc_radius a ->
  px P - px (arc_center a)
    = arc_radius a
        * cos (circ_angle (arc_center a) (arc_start a)
               + arc_angle_from_start a P) /\
  py P - py (arc_center a)
    = arc_radius a
        * sin (circ_angle (arc_center a) (arc_start a)
               + arc_angle_from_start a P).
Proof.
  intros a P Hva HP.
  set (O := arc_center a).
  set (r := arc_radius a).
  set (A := arc_start a).
  set (th0 := circ_angle O A).
  set (theta := arc_angle_from_start a P).
  assert (Hr : 0 < r) by (apply arc_radius_pos; exact Hva).
  assert (HA : dist_sq O A = r * r) by (apply arc_start_dist_sq).
  pose proof (start_offset_from_angle a Hva) as [Hsx Hsy].
  fold O r A th0 in Hsx, Hsy.
  set (sx := px A - px O) in *.
  set (sy := py A - py O) in *.
  set (ex := px P - px O).
  set (ey := py P - py O).
  assert (HuA := on_circle_vec_nonzero O A r Hr HA).
  assert (HuP := on_circle_vec_nonzero O P r Hr HP).
  fold sx sy in HuA. fold ex ey in HuP.
  pose proof (cos_angle_between sx sy ex ey HuA HuP) as Hcos.
  pose proof (sin_angle_between sx sy ex ey HuA HuP) as Hsin.
  pose proof (on_circle_sqrt_offset O A r Hr HA) as HsrA.
  pose proof (on_circle_sqrt_offset O P r Hr HP) as HsrP.
  fold sx sy in HsrA. fold ex ey in HsrP.
  rewrite HsrA, HsrP in Hcos, Hsin.
  assert (Hth : theta = angle_between sx sy ex ey).
  { unfold theta, arc_angle_from_start, signed_angle_from, A, O, sx, sy, ex, ey.
    reflexivity. }
  rewrite <- Hth in Hcos, Hsin.
  assert (Hrne : r <> 0) by lra.
  assert (Hdot : sx * ex + sy * ey = r * r * cos theta).
  { apply (Rmult_eq_reg_r (/ (r * r))); [ | apply Rinv_neq_0_compat; nra ].
    field_simplify; [ | nra ].
    unfold Rdiv in Hcos. rewrite Hcos. field; nra. }
  assert (Hcross : sx * ey - sy * ex = r * r * sin theta).
  { apply (Rmult_eq_reg_r (/ (r * r))); [ | apply Rinv_neq_0_compat; nra ].
    field_simplify; [ | nra ].
    unfold Rdiv in Hsin. rewrite Hsin. field; nra. }
  assert (Huu : sx * sx + sy * sy = r * r).
  { unfold dist_sq in HA. unfold sx, sy. lra. }
  split.
  - rewrite cos_plus, Hsx, Hsy.
    replace (r * (cos th0 * cos theta - sin th0 * sin theta))
      with (sx * cos theta - sy * sin theta) by (rewrite Hsx, Hsy; field; exact Hrne).
    apply (Rmult_eq_reg_r (r * r)); [ | nra ].
    replace ((sx * cos theta - sy * sin theta) * (r * r))
      with (sx * (r * r * cos theta) - sy * (r * r * sin theta)) by ring.
    rewrite <- Hdot, <- Hcross, rotate_dot_cross_x, Huu.
    unfold ex. ring.
  - rewrite sin_plus, Hsx, Hsy.
    replace (r * (sin th0 * cos theta + cos th0 * sin theta))
      with (sy * cos theta + sx * sin theta) by (rewrite Hsx, Hsy; field; exact Hrne).
    apply (Rmult_eq_reg_r (r * r)); [ | nra ].
    replace ((sy * cos theta + sx * sin theta) * (r * r))
      with (sy * (r * r * cos theta) + sx * (r * r * sin theta)) by ring.
    rewrite <- Hdot, <- Hcross, rotate_dot_cross_y, Huu.
    unfold ey. ring.
Qed.

Lemma end_offset_from_angle : forall a,
  valid_arc a ->
  px (arc_end a) - px (arc_center a)
    = arc_radius a
        * cos (circ_angle (arc_center a) (arc_start a) + arc_span a) /\
  py (arc_end a) - py (arc_center a)
    = arc_radius a
        * sin (circ_angle (arc_center a) (arc_start a) + arc_span a).
Proof.
  intros a Hva.
  unfold arc_span.
  exact (on_circle_offset_from_start_angle a (arc_end a) Hva (arc_end_dist_sq a Hva)).
Qed.

Lemma principal_angle_unique : forall a b,
  - PI < a <= PI ->
  - PI < b <= PI ->
  cos a = cos b ->
  sin a = sin b ->
  a = b.
Proof.
  intros a b Ha Hb Hcos Hsin.
  pose proof PI_RGT_0 as HPI.
  assert (Hcd : cos (a - b) = 1).
  { rewrite cos_minus, Hcos, Hsin. rewrite <- sin2_cos2. unfold Rsqr. ring. }
  assert (Hhalf : 1 - cos (a - b) = 2 * Rsqr (sin ((a - b) / 2))).
  { replace (a - b) with (2 * ((a - b) / 2)) at 1 by lra.
    rewrite cos_2a_sin. unfold Rsqr. ring. }
  rewrite Hcd in Hhalf.
  assert (Hs0 : sin ((a - b) / 2) = 0).
  { unfold Rsqr in Hhalf.
    assert (sin ((a - b) / 2) * sin ((a - b) / 2) = 0) by lra.
    apply Rmult_integral in H. destruct H; [exact H | exact H]. }
  destruct (sin_eq_0_0 _ Hs0) as [k Hk].
  assert (Hdiff : a - b = IZR (2 * k)%Z * PI).
  { replace (a - b) with (2 * ((a - b) / 2)) by lra.
    rewrite Hk, mult_IZR. ring. }
  assert (Hk0 : k = 0%Z).
  { destruct (Z.eq_dec k 0%Z) as [E|E]; [exact E|].
    exfalso.
    assert (Habs : (1 <= Z.abs (2 * k))%Z) by lia.
    apply IZR_le in Habs. rewrite abs_IZR, <- Hdiff in Habs.
    unfold Rabs in Habs. destruct (Rcase_abs (a - b)); lra. }
  rewrite Hk0, Hdiff, IZR_0. ring.
Qed.

Lemma atan2_sin_cos : forall alpha,
  - PI < alpha <= PI ->
  atan2 (sin alpha) (cos alpha) = alpha.
Proof.
  intros alpha Hrng.
  assert (Hne : ~ (cos alpha = 0 /\ sin alpha = 0)).
  { intros [Hc Hs]. pose proof (sin2_cos2 alpha) as H. unfold Rsqr in H. lra. }
  pose proof (atan2_range (cos alpha) (sin alpha) Hne) as Hbeta.
  pose proof (cos_atan2 (cos alpha) (sin alpha) Hne) as Hccos.
  pose proof (sin_atan2 (cos alpha) (sin alpha) Hne) as Hcsin.
  assert (Hr1 : sqrt (cos alpha * cos alpha + sin alpha * sin alpha) = 1).
  { replace (cos alpha * cos alpha + sin alpha * sin alpha)
      with (Rsqr (cos alpha) + Rsqr (sin alpha)) by (unfold Rsqr; ring).
    rewrite sin2_cos2. apply sqrt_1. }
  rewrite Hr1 in Hccos, Hcsin.
  replace (cos alpha / 1) with (cos alpha) in Hccos by field.
  replace (sin alpha / 1) with (sin alpha) in Hcsin by field.
  apply principal_angle_unique; [exact Hbeta | exact Hrng | exact Hccos | exact Hcsin].
Qed.

Lemma atan2_pos_scale : forall k x y,
  0 < k ->
  ~ (x = 0 /\ y = 0) ->
  atan2 (k * y) (k * x) = atan2 y x.
Proof.
  intros k x y Hk Hne.
  assert (Hne' : ~ (k * x = 0 /\ k * y = 0)) by nra.
  pose proof (atan2_range x y Hne) as H1.
  pose proof (atan2_range (k * x) (k * y) Hne') as H2.
  pose proof (cos_atan2 x y Hne) as Hc1.
  pose proof (sin_atan2 x y Hne) as Hs1.
  pose proof (cos_atan2 (k * x) (k * y) Hne') as Hc2.
  pose proof (sin_atan2 (k * x) (k * y) Hne') as Hs2.
  assert (Hrk : sqrt (k * x * (k * x) + k * y * (k * y))
                = k * sqrt (x * x + y * y)).
  { replace (k * x * (k * x) + k * y * (k * y))
      with (k * k * (x * x + y * y)) by ring.
    rewrite sqrt_mult_alt by nra.
    rewrite (sqrt_square k) by lra. ring. }
  rewrite Hrk in Hc2, Hs2.
  assert (Hsp : sqrt (x * x + y * y) <> 0).
  { apply Rgt_not_eq, atan2_r_pos. exact Hne. }
  assert (Hk0 : k <> 0) by lra.
  replace (k * x / (k * sqrt (x * x + y * y))) with (x / sqrt (x * x + y * y))
    in Hc2 by (field; split; [exact Hsp | exact Hk0]).
  replace (k * y / (k * sqrt (x * x + y * y))) with (y / sqrt (x * x + y * y))
    in Hs2 by (field; split; [exact Hsp | exact Hk0]).
  rewrite <- Hc1 in Hc2. rewrite <- Hs1 in Hs2.
  apply principal_angle_unique; [exact H2 | exact H1 | exact Hc2 | exact Hs2].
Qed.

Lemma angle_between_self : forall ux uy,
  ~ (ux = 0 /\ uy = 0) ->
  angle_between ux uy ux uy = 0.
Proof.
  intros ux uy Hne.
  unfold angle_between.
  replace (ux * uy - uy * ux) with 0 by ring.
  assert (Hpos : 0 < ux * ux + uy * uy) by (apply sum_sq_pos; exact Hne).
  unfold atan2.
  destruct (Rlt_dec 0 (ux * ux + uy * uy)) as [_|Hx]; [|lra].
  replace (0 / (ux * ux + uy * uy)) with 0 by (field; lra).
  apply atan_0.
Qed.

Lemma arc_angle_from_start_self : forall a,
  valid_arc a ->
  arc_angle_from_start a (arc_start a) = 0.
Proof.
  intros a Hva.
  unfold arc_angle_from_start, signed_angle_from.
  apply angle_between_self.
  apply (on_circle_vec_nonzero (arc_center a) (arc_start a) (arc_radius a)).
  - apply arc_radius_pos; exact Hva.
  - apply arc_start_dist_sq.
Qed.

Lemma arc_span_range : forall a,
  valid_arc a ->
  - PI < arc_span a <= PI.
Proof.
  intros a Hva.
  unfold arc_span, arc_angle_from_start, signed_angle_from.
  apply angle_between_range.
  - apply (on_circle_vec_nonzero (arc_center a) (arc_start a) (arc_radius a));
      [apply arc_radius_pos; exact Hva | apply arc_start_dist_sq].
  - apply (on_circle_vec_nonzero (arc_center a) (arc_end a) (arc_radius a));
      [apply arc_radius_pos; exact Hva | apply arc_end_dist_sq; exact Hva].
Qed.

Lemma interpolated_span_principal : forall a t,
  valid_arc a ->
  0 <= t <= 1 ->
  - PI < t * arc_span a <= PI.
Proof.
  intros a t Hva Ht.
  pose proof (arc_span_range a Hva) as Hsp.
  pose proof PI_RGT_0 as HPI.
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Endpoints, on-circle, and signed-angle of γ(t).                        *)
(* -------------------------------------------------------------------------- *)

Lemma arc_gamma_on_circle : forall a t,
  dist_sq (arc_center a) (arc_gamma a t) = arc_radius a * arc_radius a.
Proof.
  intros a t.
  rewrite arc_gamma_polar.
  unfold dist_sq. cbn [px py].
  ring_simplify.
  rewrite <- (Rmult_1_r (arc_radius a * arc_radius a)) at 2.
  rewrite <- sin2_cos2.
  unfold Rsqr. ring.
Qed.

Lemma arc_gamma_start : forall a,
  valid_arc a ->
  arc_gamma a 0 = arc_start a.
Proof.
  intros a Hva.
  rewrite arc_gamma_polar.
  pose proof (start_offset_from_angle a Hva) as [Hx Hy].
  replace (circ_angle (arc_center a) (arc_start a) + 0 * arc_span a)
    with (circ_angle (arc_center a) (arc_start a)) by ring.
  apply point_eq_of_coords; cbn [px py]; lra.
Qed.

Lemma arc_gamma_end : forall a,
  valid_arc a ->
  arc_gamma a 1 = arc_end a.
Proof.
  intros a Hva.
  rewrite arc_gamma_polar.
  pose proof (end_offset_from_angle a Hva) as [Hx Hy].
  replace (circ_angle (arc_center a) (arc_start a) + 1 * arc_span a)
    with (circ_angle (arc_center a) (arc_start a) + arc_span a) by ring.
  apply point_eq_of_coords; cbn [px py]; lra.
Qed.

(* WITNESS {"claimId":"64-circ-span-gamma","topic":"core","lemma":"circular_arc_gamma_constructed","title":"valid_arc CircularArc carries constructed gamma:[0,1]->circle with gamma(0)=start and gamma(1)=end","file":"theories/CircularCookSpan.v","witness":"64-circ-span-locked","board":"ADR-0007"} *)

Theorem circular_arc_gamma_constructed :
  forall a : CircularArc,
    valid_arc a ->
    arc_gamma a 0 = arc_start a /\
    arc_gamma a 1 = arc_end a /\
    (forall t, dist_sq (arc_center a) (arc_gamma a t)
               = arc_radius a * arc_radius a).
Proof.
  intros a Hva.
  split; [apply arc_gamma_start; exact Hva|].
  split; [apply arc_gamma_end; exact Hva|].
  intros t. apply arc_gamma_on_circle.
Qed.

Lemma arc_gamma_signed_angle : forall a t,
  valid_arc a ->
  0 <= t <= 1 ->
  arc_angle_from_start a (arc_gamma a t) = t * arc_span a.
Proof.
  intros a t Hva Ht.
  set (O := arc_center a).
  set (r := arc_radius a).
  set (A := arc_start a).
  set (th0 := circ_angle O A).
  assert (Hr : 0 < r) by (apply arc_radius_pos; exact Hva).
  pose proof (start_offset_from_angle a Hva) as [Hsx Hsy].
  rewrite arc_gamma_polar.
  unfold arc_angle_from_start, signed_angle_from, angle_between.
  cbn [px py].
  replace (px O + r * cos (th0 + t * arc_span a) - px O)
    with (r * cos (th0 + t * arc_span a)) by ring.
  replace (py O + r * sin (th0 + t * arc_span a) - py O)
    with (r * sin (th0 + t * arc_span a)) by ring.
  rewrite Hsx, Hsy.
  replace (r * cos th0 * (r * sin (th0 + t * arc_span a))
           - r * sin th0 * (r * cos (th0 + t * arc_span a)))
    with (r * r * sin (t * arc_span a))
    by (rewrite sin_plus, cos_plus; ring).
  replace (r * cos th0 * (r * cos (th0 + t * arc_span a))
           + r * sin th0 * (r * sin (th0 + t * arc_span a)))
    with (r * r * cos (t * arc_span a))
    by (rewrite sin_plus, cos_plus; ring).
  assert (Hne : ~ (sin (t * arc_span a) = 0 /\ cos (t * arc_span a) = 0)).
  { intros [Hs Hc]. pose proof (sin2_cos2 (t * arc_span a)) as H.
    unfold Rsqr in H. lra. }
  rewrite (atan2_pos_scale (r * r) (cos (t * arc_span a))
             (sin (t * arc_span a)) ltac:(nra) Hne).
  apply atan2_sin_cos.
  exact (interpolated_span_principal a t Hva Ht).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Interior parameters land in the atan2 span (principal mid).            *)
(* -------------------------------------------------------------------------- *)

Lemma mid_principal_thetaM_product_neg : forall a,
  valid_arc a ->
  arc_mid_on_principal_span a ->
  let gamma := arc_span a in
  let thetaM := arc_angle_from_start a (arc_mid a) in
  thetaM * (thetaM - gamma) < 0.
Proof.
  intros a Hva Hmid gamma thetaM.
  unfold arc_mid_on_principal_span in Hmid.
  fold gamma thetaM in Hmid.
  nra.
Qed.

Lemma arc_gamma_interior_in_span : forall a t,
  valid_arc a ->
  arc_mid_on_principal_span a ->
  0 < t < 1 ->
  arc_span_contains_atan2 a (arc_gamma a t).
Proof.
  intros a t Hva Hmid Ht.
  pose proof (arc_gamma_signed_angle a t Hva ltac:(lra)) as Hth.
  pose proof (mid_principal_thetaM_product_neg a Hva Hmid) as Hm.
  pose proof (arc_gamma_nonzero a Hva) as Hgnz.
  unfold arc_span_contains_atan2.
  left.
  rewrite Hth.
  unfold arc_span in Hm, Hgnz.
  nra.
Qed.

Lemma arc_gamma_in_span : forall a t,
  valid_arc a ->
  arc_mid_on_principal_span a ->
  0 <= t <= 1 ->
  arc_span_contains_atan2 a (arc_gamma a t).
Proof.
  intros a t Hva Hmid [Hlo Hhi].
  destruct (Rle_lt_or_eq_dec 0 t Hlo) as [H0|He0].
  - destruct (Rle_lt_or_eq_dec t 1 Hhi) as [H1|He1].
    + apply arc_gamma_interior_in_span; [exact Hva|exact Hmid|lra].
    + subst t. rewrite arc_gamma_end by exact Hva.
      unfold arc_span_contains_atan2. right. right. reflexivity.
  - subst t. rewrite arc_gamma_start by exact Hva.
    unfold arc_span_contains_atan2. right. left. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Retract: on-circle + atan2 span ⇒ γ(arc_t a P) = P.                    *)
(* -------------------------------------------------------------------------- *)

Lemma on_circle_eq_arc_gamma_at_angle : forall a P,
  valid_arc a ->
  dist_sq (arc_center a) P = arc_radius a * arc_radius a ->
  P = arc_gamma a (arc_t a P).
Proof.
  intros a P Hva HP.
  pose proof (arc_gamma_nonzero a Hva) as Hgnz.
  rewrite arc_gamma_polar.
  pose proof (on_circle_offset_from_start_angle a P Hva HP) as [Hx Hy].
  unfold arc_t, arc_span.
  replace (circ_angle (arc_center a) (arc_start a)
           + arc_angle_from_start a P / arc_angle_from_start a (arc_end a)
             * arc_angle_from_start a (arc_end a))
    with (circ_angle (arc_center a) (arc_start a) + arc_angle_from_start a P)
    by (field; exact Hgnz).
  apply point_eq_of_coords; cbn [px py]; lra.
Qed.

Lemma arc_t_in_unit : forall a P,
  valid_arc a ->
  arc_mid_on_principal_span a ->
  arc_span_contains_atan2 a P ->
  0 <= arc_t a P <= 1.
Proof.
  intros a P Hva Hmid Hspan.
  pose proof (arc_gamma_nonzero a Hva) as Hgnz.
  unfold arc_span_contains_atan2 in Hspan.
  unfold arc_t, arc_span.
  set (theta := arc_angle_from_start a P) in *.
  set (gamma := arc_angle_from_start a (arc_end a)) in *.
  set (thetaM := arc_angle_from_start a (arc_mid a)) in *.
  pose proof (mid_principal_thetaM_product_neg a Hva Hmid) as Hm.
  fold gamma thetaM in Hm.
  destruct Hspan as [Hprod|[Hs|He]].
  - assert (Hbet : theta * (theta - gamma) < 0) by nra.
    destruct (Rtotal_order gamma 0) as [Hg|[Hgz|Hg]]; [|exfalso; apply Hgnz; exact Hgz|].
    + assert (gamma < theta < 0) by nra.
      unfold Rdiv. nra.
    + assert (0 < theta < gamma) by nra.
      unfold Rdiv. nra.
  - rewrite Hs, (arc_angle_from_start_self a Hva).
    unfold Rdiv. nra.
  - rewrite He. unfold Rdiv.
    replace (gamma / gamma) with 1 by (field; exact Hgnz). lra.
Qed.

Lemma arc_gamma_retract : forall a P,
  valid_arc a ->
  dist_sq (arc_center a) P = arc_radius a * arc_radius a ->
  arc_mid_on_principal_span a ->
  arc_span_contains_atan2 a P ->
  on_arc_gamma a (arc_t a P) P.
Proof.
  intros a P Hva HP Hmid Hspan.
  split.
  - exact (arc_t_in_unit a P Hva Hmid Hspan).
  - symmetry. exact (on_circle_eq_arc_gamma_at_angle a P Hva HP).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Locked proper arcs on the (0,0)/(7,0) r=5 radical pair.                *)
(*     Quarter-circles: mid on the principal path; p+ in both spans; p− not.  *)
(* -------------------------------------------------------------------------- *)

Definition span_arc_A : CircularArc :=
  mkCircularArc (mkPoint 5 0) (mkPoint 3 4) (mkPoint 0 5).

Definition span_arc_B : CircularArc :=
  mkCircularArc (mkPoint 2 0) (mkPoint 4 4) (mkPoint 7 5).

Lemma span_arc_A_valid : valid_arc span_arc_A.
Proof. unfold valid_arc, span_arc_A. cbn [px py arc_start arc_mid arc_end]. lra. Qed.

Lemma span_arc_B_valid : valid_arc span_arc_B.
Proof. unfold valid_arc, span_arc_B. cbn [px py arc_start arc_mid arc_end]. lra. Qed.

Lemma span_O1_equidistant :
  dist_sq locked_O1 (arc_start span_arc_A) = dist_sq locked_O1 (arc_mid span_arc_A) /\
  dist_sq locked_O1 (arc_start span_arc_A) = dist_sq locked_O1 (arc_end span_arc_A).
Proof.
  unfold span_arc_A, locked_O1, dist_sq. cbn [px py arc_start arc_mid arc_end].
  split; lra.
Qed.

Lemma span_O2_equidistant :
  dist_sq locked_O2 (arc_start span_arc_B) = dist_sq locked_O2 (arc_mid span_arc_B) /\
  dist_sq locked_O2 (arc_start span_arc_B) = dist_sq locked_O2 (arc_end span_arc_B).
Proof.
  unfold span_arc_B, locked_O2, dist_sq. cbn [px py arc_start arc_mid arc_end].
  split; lra.
Qed.

Lemma span_arc_A_center : arc_center span_arc_A = locked_O1.
Proof.
  symmetry.
  apply equidistant_point_is_arc_center.
  - exact span_arc_A_valid.
  - apply (proj1 span_O1_equidistant).
  - apply (proj2 span_O1_equidistant).
Qed.

Lemma span_arc_B_center : arc_center span_arc_B = locked_O2.
Proof.
  symmetry.
  apply equidistant_point_is_arc_center.
  - exact span_arc_B_valid.
  - apply (proj1 span_O2_equidistant).
  - apply (proj2 span_O2_equidistant).
Qed.

Lemma span_arc_A_radius : arc_radius span_arc_A = locked_r.
Proof.
  unfold arc_radius. rewrite span_arc_A_center.
  unfold locked_O1, locked_r, span_arc_A, dist, dist_sq.
  cbn [px py arc_start].
  replace ((0 - 5) * (0 - 5) + (0 - 0) * (0 - 0)) with (Rsqr 5)
    by (unfold Rsqr; ring).
  apply sqrt_Rsqr. lra.
Qed.

Lemma span_arc_B_radius : arc_radius span_arc_B = locked_r.
Proof.
  unfold arc_radius. rewrite span_arc_B_center.
  unfold locked_O2, locked_r, span_arc_B, dist, dist_sq.
  cbn [px py arc_start].
  replace ((7 - 2) * (7 - 2) + (0 - 0) * (0 - 0)) with (Rsqr 5)
    by (unfold Rsqr; ring).
  apply sqrt_Rsqr. lra.
Qed.

Lemma span_locked_radical_a :
  radical_axis_a locked_O1 locked_O2 locked_r locked_r = 7 / 2.
Proof.
  unfold radical_axis_a, locked_r.
  rewrite locked_centers_dist. field.
Qed.

Lemma span_locked_radical_ux : radical_axis_ux locked_O1 locked_O2 = 1.
Proof.
  unfold radical_axis_ux. rewrite locked_centers_dist.
  unfold locked_O1, locked_O2. cbn [px py]. field.
Qed.

Lemma span_locked_radical_uy : radical_axis_uy locked_O1 locked_O2 = 0.
Proof.
  unfold radical_axis_uy. rewrite locked_centers_dist.
  unfold locked_O1, locked_O2. cbn [px py]. field.
Qed.

Lemma span_locked_h2 :
  locked_r * locked_r
    - radical_axis_a locked_O1 locked_O2 locked_r locked_r
      * radical_axis_a locked_O1 locked_O2 locked_r locked_r
  = 51 / 4.
Proof.
  rewrite span_locked_radical_a. unfold locked_r. field.
Qed.

Lemma span_locked_h_sq :
  radical_axis_h locked_O1 locked_O2 locked_r locked_r
  * radical_axis_h locked_O1 locked_O2 locked_r locked_r
  = 51 / 4.
Proof.
  unfold radical_axis_h. rewrite span_locked_h2. apply sqrt_sqrt. lra.
Qed.

Lemma span_locked_h_pos :
  0 < radical_axis_h locked_O1 locked_O2 locked_r locked_r.
Proof.
  unfold radical_axis_h. rewrite span_locked_h2. apply sqrt_lt_R0. lra.
Qed.

Lemma span_locked_h_gt_three_halves :
  3 / 2 < radical_axis_h locked_O1 locked_O2 locked_r locked_r.
Proof.
  apply Rnot_le_lt. intro Hle.
  pose proof span_locked_h_pos as Hpos.
  pose proof span_locked_h_sq as Hsq.
  apply (Rmult_le_compat _ _ _ _ Hle Hle) in Hle.
  2: lra.
  2: lra.
  nra.
Qed.

Lemma span_p_plus_coords :
  px locked_p_plus = 7 / 2 /\
  py locked_p_plus = radical_axis_h locked_O1 locked_O2 locked_r locked_r.
Proof.
  unfold locked_p_plus, radical_point_plus.
  rewrite span_locked_radical_a, span_locked_radical_ux, span_locked_radical_uy.
  unfold locked_O1. cbn [px py]. split; ring.
Qed.

Lemma span_p_minus_coords :
  px locked_p_minus = 7 / 2 /\
  py locked_p_minus = - radical_axis_h locked_O1 locked_O2 locked_r locked_r.
Proof.
  unfold locked_p_minus, radical_point_minus.
  rewrite span_locked_radical_a, span_locked_radical_ux, span_locked_radical_uy.
  unfold locked_O1. cbn [px py]. split; ring.
Qed.

Lemma span_p_plus_y_pos : 0 < py locked_p_plus.
Proof.
  destruct span_p_plus_coords as [_ Hy]. rewrite Hy. exact span_locked_h_pos.
Qed.

Lemma span_p_minus_y_neg : py locked_p_minus < 0.
Proof.
  destruct span_p_minus_coords as [_ Hy]. rewrite Hy.
  pose proof span_locked_h_pos. lra.
Qed.

Lemma span_p_plus_on_A :
  dist_sq (arc_center span_arc_A) locked_p_plus
  = arc_radius span_arc_A * arc_radius span_arc_A.
Proof.
  rewrite span_arc_A_center, span_arc_A_radius.
  exact (proj1 locked_radical_on_circles).
Qed.

Lemma span_p_plus_on_B :
  dist_sq (arc_center span_arc_B) locked_p_plus
  = arc_radius span_arc_B * arc_radius span_arc_B.
Proof.
  rewrite span_arc_B_center, span_arc_B_radius.
  exact (proj1 (proj2 locked_radical_on_circles)).
Qed.

Lemma span_p_minus_on_A :
  dist_sq (arc_center span_arc_A) locked_p_minus
  = arc_radius span_arc_A * arc_radius span_arc_A.
Proof.
  rewrite span_arc_A_center, span_arc_A_radius.
  exact (proj1 (proj2 (proj2 locked_radical_on_circles))).
Qed.

Lemma span_arc_A_side_plus :
  0 < arc_side_chord span_arc_A (arc_mid span_arc_A)
      * arc_side_chord span_arc_A locked_p_plus.
Proof.
  unfold arc_side_chord, cross_R_pt, span_arc_A.
  cbn [px py arc_start arc_mid arc_end].
  destruct span_p_plus_coords as [Hx Hy].
  rewrite Hx, Hy.
  pose proof span_locked_h_gt_three_halves as Hh.
  nra.
Qed.

Lemma span_arc_B_side_plus :
  0 < arc_side_chord span_arc_B (arc_mid span_arc_B)
      * arc_side_chord span_arc_B locked_p_plus.
Proof.
  unfold arc_side_chord, cross_R_pt, span_arc_B.
  cbn [px py arc_start arc_mid arc_end].
  destruct span_p_plus_coords as [Hx Hy].
  rewrite Hx, Hy.
  pose proof span_locked_h_pos as Hh.
  nra.
Qed.

Lemma span_arc_A_side_minus_neg :
  arc_side_chord span_arc_A (arc_mid span_arc_A)
  * arc_side_chord span_arc_A locked_p_minus < 0.
Proof.
  unfold arc_side_chord, cross_R_pt, span_arc_A.
  cbn [px py arc_start arc_mid arc_end].
  destruct span_p_minus_coords as [Hx Hy].
  rewrite Hx, Hy.
  pose proof span_locked_h_pos as Hh.
  nra.
Qed.

Lemma span_p_plus_in_A : arc_span_contains_atan2 span_arc_A locked_p_plus.
Proof.
  pose proof span_arc_A_valid as Hva.
  pose proof span_p_plus_on_A as Hon.
  assert (Hinc : inCircle_R (arc_start span_arc_A) (arc_mid span_arc_A)
                            (arc_end span_arc_A) locked_p_plus = 0).
  { apply inCircle_R_zero_of_equidistant; [exact Hva|].
    rewrite arc_start_dist_sq. exact Hon. }
  apply (arc_span_contains_atan2_iff_chord_sign span_arc_A locked_p_plus Hva Hinc).
  unfold arc_span_contains, arc_interior_side.
  left. exact span_arc_A_side_plus.
Qed.

Lemma span_p_plus_in_B : arc_span_contains_atan2 span_arc_B locked_p_plus.
Proof.
  pose proof span_arc_B_valid as Hva.
  pose proof span_p_plus_on_B as Hon.
  assert (Hinc : inCircle_R (arc_start span_arc_B) (arc_mid span_arc_B)
                            (arc_end span_arc_B) locked_p_plus = 0).
  { apply inCircle_R_zero_of_equidistant; [exact Hva|].
    rewrite arc_start_dist_sq. exact Hon. }
  apply (arc_span_contains_atan2_iff_chord_sign span_arc_B locked_p_plus Hva Hinc).
  unfold arc_span_contains, arc_interior_side.
  left. exact span_arc_B_side_plus.
Qed.

Lemma span_p_minus_not_A_ends :
  locked_p_minus <> arc_start span_arc_A /\
  locked_p_minus <> arc_end span_arc_A.
Proof.
  unfold span_arc_A. cbn [arc_start arc_end].
  split; intro H; apply (f_equal py) in H; cbn in H;
    pose proof span_p_minus_y_neg; lra.
Qed.

Lemma span_p_minus_rejected_A :
  ~ arc_span_contains_atan2 span_arc_A locked_p_minus.
Proof.
  pose proof span_arc_A_valid as Hva.
  pose proof span_p_minus_on_A as Hon.
  assert (Hinc : inCircle_R (arc_start span_arc_A) (arc_mid span_arc_A)
                            (arc_end span_arc_A) locked_p_minus = 0).
  { apply inCircle_R_zero_of_equidistant; [exact Hva|].
    rewrite arc_start_dist_sq. exact Hon. }
  intro Hatan.
  apply (arc_span_contains_atan2_iff_chord_sign span_arc_A locked_p_minus Hva Hinc)
    in Hatan.
  unfold arc_span_contains, arc_interior_side in Hatan.
  destruct Hatan as [Hint|[Hs|He]].
  - pose proof span_arc_A_side_minus_neg. lra.
  - apply (proj1 span_p_minus_not_A_ends). exact Hs.
  - apply (proj2 span_p_minus_not_A_ends). exact He.
Qed.

Lemma span_arc_A_angle_end :
  arc_angle_from_start span_arc_A (arc_end span_arc_A) = PI / 2.
Proof.
  unfold arc_angle_from_start, signed_angle_from, angle_between, span_arc_A.
  rewrite span_arc_A_center. unfold locked_O1.
  cbn [px py arc_start arc_end].
  replace (5 * 5 - 0 * 0) with 25 by ring.
  replace (5 * 0 + 0 * 5) with 0 by ring.
  unfold atan2.
  destruct (Rlt_dec 0 0); [lra|].
  destruct (Rlt_dec 0 0); [lra|].
  destruct (Rlt_dec 0 25) as [Hy|Hy]; [|lra].
  reflexivity.
Qed.

Lemma span_arc_A_angle_mid :
  arc_angle_from_start span_arc_A (arc_mid span_arc_A) = atan (4 / 3).
Proof.
  unfold arc_angle_from_start, signed_angle_from, angle_between, span_arc_A.
  rewrite span_arc_A_center. unfold locked_O1.
  cbn [px py arc_start arc_mid].
  replace (5 * 4 - 0 * 3) with 20 by ring.
  replace (5 * 3 + 0 * 4) with 15 by ring.
  unfold atan2.
  destruct (Rlt_dec 0 15) as [Hx|Hx]; [|lra].
  replace (20 / 15) with (4 / 3) by field.
  reflexivity.
Qed.

Lemma span_arc_A_mid_principal : arc_mid_on_principal_span span_arc_A.
Proof.
  unfold arc_mid_on_principal_span, arc_span.
  rewrite span_arc_A_angle_end, span_arc_A_angle_mid.
  pose proof (atan_bound (4 / 3)) as Hb.
  pose proof (atan_gt_0 (4 / 3) ltac:(lra)) as Hpos.
  pose proof PI_RGT_0 as HPI.
  nra.
Qed.

Lemma span_arc_B_angle_end :
  arc_angle_from_start span_arc_B (arc_end span_arc_B) = - (PI / 2).
Proof.
  unfold arc_angle_from_start, signed_angle_from, angle_between, span_arc_B.
  rewrite span_arc_B_center. unfold locked_O2.
  cbn [px py arc_start arc_end].
  replace ((2 - 7) * (5 - 0) - (0 - 0) * (7 - 7)) with (-25) by ring.
  replace ((2 - 7) * (7 - 7) + (0 - 0) * (5 - 0)) with 0 by ring.
  unfold atan2.
  destruct (Rlt_dec 0 0); [lra|].
  destruct (Rlt_dec 0 0); [lra|].
  destruct (Rlt_dec 0 (-25)); [lra|].
  destruct (Rlt_dec (-25) 0) as [Hy|Hy]; [reflexivity | lra].
Qed.

Lemma span_arc_B_angle_mid :
  arc_angle_from_start span_arc_B (arc_mid span_arc_B) = atan (-4 / 3).
Proof.
  unfold arc_angle_from_start, signed_angle_from, angle_between, span_arc_B.
  rewrite span_arc_B_center. unfold locked_O2.
  cbn [px py arc_start arc_mid].
  replace ((2 - 7) * (4 - 0) - (0 - 0) * (4 - 7)) with (-20) by ring.
  replace ((2 - 7) * (4 - 7) + (0 - 0) * (4 - 0)) with 15 by ring.
  unfold atan2.
  destruct (Rlt_dec 0 15) as [Hx|Hx]; [|lra].
  replace ((-20) / 15) with (-4 / 3) by field.
  reflexivity.
Qed.

Lemma span_arc_B_mid_principal : arc_mid_on_principal_span span_arc_B.
Proof.
  unfold arc_mid_on_principal_span, arc_span.
  rewrite span_arc_B_angle_end, span_arc_B_angle_mid.
  rewrite atan_opp.
  pose proof (atan_bound (4 / 3)) as Hb.
  pose proof (atan_gt_0 (4 / 3) ltac:(lra)) as Hpos.
  pose proof PI_RGT_0 as HPI.
  nra.
Qed.

Lemma span_p_plus_on_gamma_A :
  on_arc_gamma span_arc_A (arc_t span_arc_A locked_p_plus) locked_p_plus.
Proof.
  apply arc_gamma_retract.
  - exact span_arc_A_valid.
  - exact span_p_plus_on_A.
  - exact span_arc_A_mid_principal.
  - exact span_p_plus_in_A.
Qed.

Lemma span_p_plus_on_gamma_B :
  on_arc_gamma span_arc_B (arc_t span_arc_B locked_p_plus) locked_p_plus.
Proof.
  apply arc_gamma_retract.
  - exact span_arc_B_valid.
  - exact span_p_plus_on_B.
  - exact span_arc_B_mid_principal.
  - exact span_p_plus_in_B.
Qed.

(* WITNESS {"claimId":"64-circ-span-gamma","topic":"core","lemma":"locked_span_gamma_hit","title":"Locked proper arcs carry span-filtered gamma(t)=p+ and reject p- (QED)","file":"theories/CircularCookSpan.v","witness":"64-circ-span-locked","board":"ADR-0007"} *)

Theorem locked_span_gamma_hit :
  valid_arc span_arc_A /\
  valid_arc span_arc_B /\
  on_arc_gamma span_arc_A (arc_t span_arc_A locked_p_plus) locked_p_plus /\
  on_arc_gamma span_arc_B (arc_t span_arc_B locked_p_plus) locked_p_plus /\
  arc_span_contains_atan2 span_arc_A locked_p_plus /\
  arc_span_contains_atan2 span_arc_B locked_p_plus /\
  ~ arc_span_contains_atan2 span_arc_A locked_p_minus.
Proof.
  repeat split.
  - exact span_arc_A_valid.
  - exact span_arc_B_valid.
  - apply (proj1 span_p_plus_on_gamma_A).
  - apply (proj2 span_p_plus_on_gamma_A).
  - apply (proj1 span_p_plus_on_gamma_B).
  - apply (proj2 span_p_plus_on_gamma_B).
  - exact span_p_plus_in_A.
  - exact span_p_plus_in_B.
  - exact span_p_minus_rejected_A.
Qed.

Lemma circular_still_not_first_cook_scope :
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_not_first_cook_scope.
Qed.

(* Host CircGamma stays CircGammaQEX: 3-axiom CircularCook cannot import
   this atan2 interpolant. Remaining obligation: an atan2-free γ on
   CircularArc, or a host-lane policy change. Not a bool. *)

Lemma circular_gamma_host_still_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  exact circular_gamma_is_qex.
Qed.

Print Assumptions circular_arc_gamma_constructed.
Print Assumptions arc_gamma_retract.
Print Assumptions locked_span_gamma_hit.
Print Assumptions circular_still_not_first_cook_scope.
Print Assumptions circular_gamma_host_still_qex.

