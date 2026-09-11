(* ============================================================================
   NetTopologySuite.Proofs.ArcSpanAtan2
   ----------------------------------------------------------------------------
   Issue #64 ask: arc-span membership via atan2 sector comparison, and its
   equivalence to the existing chord-sign test `ArcIntersect.arc_span_contains`.

   `ArcIntersect.v`'s header claims `arc_span_contains` (the chord cross
   product sign, "Option S") is "correct for arcs with subtended angle < pi ...
   reflex arcs (> pi) not characterised correctly."  A topological argument
   plus a large numerical falsification search suggested this limitation is
   NOT real for on-circle points: a line meets a circle in at most two points,
   so the circle minus {start, end} splits into exactly two open arcs, one of
   which contains `arc_mid` by construction; "same side of the chord as
   arc_mid" identifies that connected arc component regardless of its
   subtended angle.  This file proves that unconditionally.

   `arc_span_contains_atan2` is the atan2-based sector test: for the signed
   angle (via `AngleBetween.angle_between`, principal range (-pi,pi]) from
   `arc_start` to a point X (about `arc_center`), a point P is in the arc's
   sector iff its signed angle `theta` and the end's signed angle `gamma` are
   "on the same side" of the start (0) as the mid's signed angle `thetaM` --
   i.e. `theta*(theta-gamma)` and `thetaM*(thetaM-gamma)` have the same sign.
   This sign-product form is the direct atan2 analogue of the existing
   chord-sign test's own sign-product shape (`arc_interior_side`), and it
   avoids the interval/wraparound case split of an oracle-style CCW-offset
   comparison entirely.

   THE KEY IDENTITY (on-circle cross-product value).  For O, A, C, P all at
   distance r > 0 from O, writing theta := signed angle from A to P (about O)
   and gamma := signed angle from A to C (about O):

     cross_R_pt A C P = r*r * (sin gamma + sin (theta - gamma) - sin theta)
                       = 4 * r*r * sin (gamma/2) * sin (theta/2) * sin ((theta-gamma)/2)

   The first equality is `cross_R_pt_cyclic_sum` (a pure ring identity, lands
   in ArcOrient.v) composed with `cos_angle_between`/`sin_angle_between` and
   the 2-D Lagrange identity `cross_dot_lagrange_2d`.  The second is the
   trigonometric sum-to-product identity `sin_sum_to_product`, closed via
   `nsatz` on the double-angle expansions (same style as
   `ArcOrient.inCircle_R_rotation_invariant`).

   Applying this to P and to `arc_mid` (both on the circumcircle) and taking
   the sign of the product `arc_side_chord a (arc_mid a) * arc_side_chord a P`
   cancels the common positive factor `16*r^4*sin(gamma/2)^2` (gamma <> 0
   since `arc_start a <> arc_end a` under `valid_arc`), leaving exactly the
   atan2 sign-product test -- UNCONDITIONALLY, for every sweep.

   Proved here (4-axiom: inherits `Classical_Prop.classic` transitively via
   `Atan2.atan2`/`AngleBetween.angle_between`, same lineage as
   `RelateArcAnalytic.v` -- see the `docs/audit-exceptions.txt` entry added
   alongside this file):
     `arc_span_contains_atan2_iff_chord_sign` -- the headline: for a valid
     arc and an on-circumcircle point P, `arc_span_contains_atan2 a P <->
     arc_span_contains a P`.  Unconditional in the sweep (no `sweep < pi`
     side hypothesis) -- covering the reflex case the corpus previously
     believed open.

   Item ② / N-AA atan2 discharge (moved from ArcArcQuartic so that file
   can leave the exceptions list as 3-axiom Vieta):
     `arc_arc_intersects_of_atan2_radical_span` plus the four
     radical-point on-circle / atan2-iff helpers.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Nsatz.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcIntersect
  ArcOffsetThreePoint ArcChordApprox ArcArcCircles ArcArcCirclesSpan
  Atan2 AngleBetween.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Definitions.                                                           *)
(* -------------------------------------------------------------------------- *)

(* The signed angle (principal range (-pi,pi]) from the direction O->A to the
   direction O->X, via `angle_between` on the two offset vectors. *)
Definition signed_angle_from (O A X : Point) : R :=
  angle_between (px A - px O) (py A - py O) (px X - px O) (py X - py O).

Definition arc_angle_from_start (a : CircularArc) (P : Point) : R :=
  signed_angle_from (arc_center a) (arc_start a) P.

Lemma arc_angle_from_start_eq :
  forall (a : CircularArc) (X : Point),
    arc_angle_from_start a X = signed_angle_from (arc_center a) (arc_start a) X.
Proof. reflexivity. Qed.

(* atan2 sector membership: P's signed angle from start is "on the same side"
   of 0 relative to gamma (end's signed angle) as thetaM (mid's) is -- the
   atan2 analogue of `arc_interior_side`'s chord-sign product test. *)
Definition arc_span_contains_atan2 (a : CircularArc) (P : Point) : Prop :=
  let theta  := arc_angle_from_start a P in
  let gamma  := arc_angle_from_start a (arc_end a) in
  let thetaM := arc_angle_from_start a (arc_mid a) in
  0 < (theta * (theta - gamma)) * (thetaM * (thetaM - gamma)) \/
  P = arc_start a \/ P = arc_end a.

(* -------------------------------------------------------------------------- *)
(* §2  Pure algebra: the 2-D Lagrange identity and the sine sum-to-product.   *)
(* -------------------------------------------------------------------------- *)

(* For any three planar vectors u, v, w:
     dot(u,v)*cross(u,w) - dot(u,w)*cross(u,v) = cross(v,w) * |u|^2.
   Pure `ring` identity (no geometric hypothesis). *)
Lemma cross_dot_lagrange_2d :
  forall ux uy vx vy wx wy : R,
    (ux * vx + uy * vy) * (ux * wy - uy * wx)
    - (ux * wx + uy * wy) * (ux * vy - uy * vx)
    = (vx * wy - vy * wx) * (ux * ux + uy * uy).
Proof. intros. ring. Qed.

(* sin gamma + sin (theta - gamma) - sin theta = 4 sin(gamma/2) sin(theta/2) sin((theta-gamma)/2). *)
Lemma sin_sum_to_product :
  forall theta gamma : R,
    sin gamma + sin (theta - gamma) - sin theta
    = 4 * sin (gamma / 2) * sin (theta / 2) * sin ((theta - gamma) / 2).
Proof.
  intros theta gamma.
  pose proof (sin2_cos2 (theta / 2)) as Hpyth1. unfold Rsqr in Hpyth1.
  pose proof (sin2_cos2 (gamma / 2)) as Hpyth2. unfold Rsqr in Hpyth2.
  assert (Htheta : sin theta = 2 * sin (theta / 2) * cos (theta / 2)).
  { replace theta with (2 * (theta / 2)) at 1 by lra. apply sin_2a. }
  assert (Hgamma : sin gamma = 2 * sin (gamma / 2) * cos (gamma / 2)).
  { replace gamma with (2 * (gamma / 2)) at 1 by lra. apply sin_2a. }
  assert (Hcostheta : cos theta
                       = cos (theta / 2) * cos (theta / 2) - sin (theta / 2) * sin (theta / 2)).
  { replace theta with (2 * (theta / 2)) at 1 by lra. apply cos_2a. }
  assert (Hcosgamma : cos gamma
                       = cos (gamma / 2) * cos (gamma / 2) - sin (gamma / 2) * sin (gamma / 2)).
  { replace gamma with (2 * (gamma / 2)) at 1 by lra. apply cos_2a. }
  assert (Hhalf : sin ((theta - gamma) / 2)
                  = sin (theta / 2) * cos (gamma / 2) - cos (theta / 2) * sin (gamma / 2)).
  { replace ((theta - gamma) / 2) with (theta / 2 - gamma / 2) by lra.
    apply sin_minus. }
  rewrite (sin_minus theta gamma).
  rewrite Htheta, Hgamma, Hcostheta, Hcosgamma, Hhalf.
  nsatz.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  On-circle helper facts.                                                *)
(* -------------------------------------------------------------------------- *)

Lemma on_circle_vec_nonzero :
  forall (O X : Point) (r : R),
    0 < r -> dist_sq O X = r * r -> ~ (px X - px O = 0 /\ py X - py O = 0).
Proof.
  intros O X r Hr Heq [Hx Hy].
  unfold dist_sq in Heq. nra.
Qed.

Lemma on_circle_sqrt_offset :
  forall (O X : Point) (r : R),
    0 < r -> dist_sq O X = r * r ->
    sqrt ((px X - px O) * (px X - px O) + (py X - py O) * (py X - py O)) = r.
Proof.
  intros O X r Hr Heq.
  replace ((px X - px O) * (px X - px O) + (py X - py O) * (py X - py O))
    with (dist_sq O X) by (unfold dist_sq; ring).
  rewrite Heq. apply sqrt_square. lra.
Qed.

(* Equal-radius points at signed angle 0 from each other coincide. *)
Lemma on_circle_same_direction_eq :
  forall (O A X : Point) (r : R),
    0 < r -> dist_sq O A = r * r -> dist_sq O X = r * r ->
    signed_angle_from O A X = 0 -> px A = px X /\ py A = py X.
Proof.
  intros O A X r Hr HA HX Hang.
  unfold signed_angle_from in Hang.
  assert (HuA := on_circle_vec_nonzero O A r Hr HA).
  assert (HuX := on_circle_vec_nonzero O X r Hr HX).
  pose proof (cos_angle_between (px A - px O) (py A - py O)
                                 (px X - px O) (py X - py O) HuA HuX) as Hcos.
  rewrite Hang, cos_0 in Hcos.
  rewrite (on_circle_sqrt_offset O A r Hr HA) in Hcos.
  rewrite (on_circle_sqrt_offset O X r Hr HX) in Hcos.
  set (dotp := (px A - px O) * (px X - px O) + (py A - py O) * (py X - py O)) in Hcos.
  assert (Hrrne : r * r <> 0) by nra.
  assert (Hrne : r <> 0) by lra.
  assert (Hdot : dotp = r * r).
  { transitivity (dotp / (r * r) * (r * r)).
    - field. exact Hrne.
    - rewrite <- Hcos. ring. }
  (* |u - v|^2 = |u|^2 + |v|^2 - 2 dot = r*r + r*r - 2*r*r = 0. *)
  assert (Hzero : (px A - px X) * (px A - px X) + (py A - py X) * (py A - py X) = 0).
  { unfold dotp in Hdot.
    assert (HuuA : (px A - px O) * (px A - px O) + (py A - py O) * (py A - py O) = r * r)
      by (unfold dist_sq in HA; lra).
    assert (HuuX : (px X - px O) * (px X - px O) + (py X - py O) * (py X - py O) = r * r)
      by (unfold dist_sq in HX; lra).
    nra. }
  split.
  - assert (Hx2 : (px A - px X) * (px A - px X) = 0).
    { pose proof (sqr_nonneg (px A - px X)) as H1.
      pose proof (sqr_nonneg (py A - py X)) as H2. lra. }
    apply sqr_eq_zero in Hx2. lra.
  - assert (Hy2 : (py A - py X) * (py A - py X) = 0).
    { pose proof (sqr_nonneg (px A - px X)) as H1.
      pose proof (sqr_nonneg (py A - py X)) as H2. lra. }
    apply sqr_eq_zero in Hy2. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The on-circle cross-product value, in closed sin form.                 *)
(* -------------------------------------------------------------------------- *)

Lemma cross_on_circle_value :
  forall (O A C P : Point) (r : R),
    0 < r ->
    dist_sq O A = r * r -> dist_sq O C = r * r -> dist_sq O P = r * r ->
    cross_R_pt A C P
    = r * r * (sin (signed_angle_from O A C)
               + sin (signed_angle_from O A P - signed_angle_from O A C)
               - sin (signed_angle_from O A P)).
Proof.
  intros O A C P r Hr HA HC HP.
  unfold signed_angle_from.
  set (ux := px A - px O). set (uy := py A - py O).
  set (vx := px C - px O). set (vy := py C - py O).
  set (wx := px P - px O). set (wy := py P - py O).
  set (gamma := angle_between ux uy vx vy).
  set (theta := angle_between ux uy wx wy).
  assert (HuA := on_circle_vec_nonzero O A r Hr HA).
  assert (HuC := on_circle_vec_nonzero O C r Hr HC).
  assert (HuP := on_circle_vec_nonzero O P r Hr HP).
  fold ux uy in HuA. fold vx vy in HuC. fold wx wy in HuP.
  assert (Hru : sqrt (ux * ux + uy * uy) = r)
    by (unfold ux, uy; apply on_circle_sqrt_offset; assumption).
  assert (Hrv : sqrt (vx * vx + vy * vy) = r)
    by (unfold vx, vy; apply on_circle_sqrt_offset; assumption).
  assert (Hrw : sqrt (wx * wx + wy * wy) = r)
    by (unfold wx, wy; apply on_circle_sqrt_offset; assumption).
  assert (Huu : ux * ux + uy * uy = r * r) by (unfold dist_sq in HA; unfold ux, uy; lra).
  (* cross(u,v) = r*r*sin(gamma), cross(u,w) = r*r*sin(theta). *)
  pose proof (sin_angle_between ux uy vx vy HuA HuC) as Hsg.
  pose proof (cos_angle_between ux uy vx vy HuA HuC) as Hcg.
  pose proof (sin_angle_between ux uy wx wy HuA HuP) as Hst.
  pose proof (cos_angle_between ux uy wx wy HuA HuP) as Hct.
  rewrite Hru, Hrv in Hsg, Hcg.
  rewrite Hru, Hrw in Hst, Hct.
  fold gamma in Hsg, Hcg. fold theta in Hst, Hct.
  assert (Hrrne : r * r <> 0) by nra.
  assert (Hrne : r <> 0) by lra.
  assert (Hcross_uv : ux * vy - uy * vx = r * r * sin gamma).
  { transitivity ((ux * vy - uy * vx) / (r * r) * (r * r)).
    - field. exact Hrne.
    - rewrite <- Hsg. ring. }
  assert (Hcross_uw : ux * wy - uy * wx = r * r * sin theta).
  { transitivity ((ux * wy - uy * wx) / (r * r) * (r * r)).
    - field. exact Hrne.
    - rewrite <- Hst. ring. }
  assert (Hdot_uv : ux * vx + uy * vy = r * r * cos gamma).
  { transitivity ((ux * vx + uy * vy) / (r * r) * (r * r)).
    - field. exact Hrne.
    - rewrite <- Hcg. ring. }
  assert (Hdot_uw : ux * wx + uy * wy = r * r * cos theta).
  { transitivity ((ux * wx + uy * wy) / (r * r) * (r * r)).
    - field. exact Hrne.
    - rewrite <- Hct. ring. }
  (* cross(v,w) via the Lagrange identity and Huu. *)
  pose proof (cross_dot_lagrange_2d ux uy vx vy wx wy) as Hlag.
  rewrite Hdot_uv, Hcross_uw, Hdot_uw, Hcross_uv, Huu in Hlag.
  assert (Hcross_vw : vx * wy - vy * wx = r * r * sin (theta - gamma)).
  { assert (Hkey : (r * r * cos gamma) * (r * r * sin theta)
                   - (r * r * cos theta) * (r * r * sin gamma)
                   = (vx * wy - vy * wx) * (r * r)) by exact Hlag.
    assert (Hexp : (r * r * cos gamma) * (r * r * sin theta)
                   - (r * r * cos theta) * (r * r * sin gamma)
                   = (r * r) * (r * r) * (sin theta * cos gamma - cos theta * sin gamma))
      by ring.
    rewrite Hexp in Hkey.
    rewrite <- (sin_minus theta gamma) in Hkey.
    apply (Rmult_eq_reg_r (r * r)); [ | exact Hrrne].
    nra. }
  (* Assemble via the cyclic-sum identity. *)
  assert (HOAC : cross_R_pt O A C = ux * vy - uy * vx)
    by (unfold cross_R_pt, ux, uy, vx, vy; ring).
  assert (HOCP : cross_R_pt O C P = vx * wy - vy * wx)
    by (unfold cross_R_pt, vx, vy, wx, wy; ring).
  assert (HOPA : cross_R_pt O P A = wx * uy - wy * ux)
    by (unfold cross_R_pt, wx, wy, ux, uy; ring).
  assert (Hcross_wu : wx * uy - wy * ux = - (r * r * sin theta)).
  { rewrite <- Hcross_uw. ring. }
  rewrite (cross_R_pt_cyclic_sum O A C P).
  rewrite HOAC, HOCP, HOPA, Hcross_uv, Hcross_vw, Hcross_wu.
  fold gamma theta. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Sign correspondence: a `same_sign` combinator relating x and sin(x/2), *)
(*     stable under multiplication, so the atan2 sign-product test matches   *)
(*     the sin-product value from §4 directly -- without ever needing to    *)
(*     feed an `iff` fact to `nra`.                                          *)
(* -------------------------------------------------------------------------- *)

Definition same_sign (a b : R) : Prop :=
  (0 < a /\ 0 < b) \/ (a = 0 /\ b = 0) \/ (a < 0 /\ b < 0).

Lemma same_sign_mult :
  forall a a' b b' : R, same_sign a a' -> same_sign b b' -> same_sign (a * b) (a' * b').
Proof.
  intros a a' b b' Ha Hb.
  unfold same_sign in Ha, Hb.
  destruct Ha as [[Ha1 Ha2]|[[Ha1 Ha2]|[Ha1 Ha2]]];
  destruct Hb as [[Hb1 Hb2]|[[Hb1 Hb2]|[Hb1 Hb2]]]; subst;
  unfold same_sign;
  solve [ left; nra | right; left; nra | right; right; nra ].
Qed.

Lemma same_sign_pos_iff : forall a b : R, same_sign a b -> (0 < a <-> 0 < b).
Proof.
  intros a b Ha. unfold same_sign in Ha.
  destruct Ha as [[Ha1 Ha2]|[[Ha1 Ha2]|[Ha1 Ha2]]]; split; intro; lra.
Qed.

Lemma pos_scale_iff : forall K X : R, 0 < K -> (0 < K * X <-> 0 < X).
Proof. intros K X HK; split; intro H; nra. Qed.

(* For x in (-2*PI, 2*PI), x and sin(x/2) have the same sign. *)
Lemma sign_match_sin_half :
  forall x : R, -(2 * PI) < x < 2 * PI -> same_sign x (sin (x / 2)).
Proof.
  intros x [Hlo Hhi]. unfold same_sign.
  destruct (Rtotal_order x 0) as [Hlt | [Heq | Hgt]].
  - right; right. split; [exact Hlt | apply sin_lt_0_var; lra].
  - right; left. split; [exact Heq | subst x; replace (0/2) with 0 by lra; apply sin_0].
  - left. split; [exact Hgt | apply sin_gt_0; lra].
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Non-degeneracy: gamma <> 0 (arc_start <> arc_end under valid_arc).     *)
(* -------------------------------------------------------------------------- *)

Lemma arc_gamma_nonzero :
  forall a : CircularArc,
    valid_arc a -> arc_angle_from_start a (arc_end a) <> 0.
Proof.
  intros a Hva Hcontra.
  assert (Hr := arc_radius_pos a Hva).
  assert (HAeq : dist_sq (arc_center a) (arc_start a) = arc_radius a * arc_radius a).
  { unfold arc_radius, dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  assert (HCeq : dist_sq (arc_center a) (arc_end a) = arc_radius a * arc_radius a).
  { rewrite <- (arc_center_dist_end a Hva). unfold dist.
    rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  destruct (on_circle_same_direction_eq (arc_center a) (arc_start a) (arc_end a)
              (arc_radius a) Hr HAeq HCeq Hcontra) as [Hx Hy].
  unfold valid_arc in Hva. apply Hva.
  assert (Hse : arc_end a = arc_start a).
  { destruct (arc_start a), (arc_end a). cbn in Hx, Hy. subst. reflexivity. }
  rewrite Hse. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Headline: atan2 sector membership = chord-sign membership.            *)
(*     Unconditional in the sweep -- no `sweep < PI` hypothesis.             *)
(* -------------------------------------------------------------------------- *)

Theorem arc_span_contains_atan2_iff_chord_sign :
  forall (a : CircularArc) (P : Point),
    valid_arc a ->
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) P = 0 ->
    (arc_span_contains_atan2 a P <-> arc_span_contains a P).
Proof.
  intros a P Hva Hcirc.
  set (r := arc_radius a).
  set (gamma := arc_angle_from_start a (arc_end a)).
  set (thetaM := arc_angle_from_start a (arc_mid a)).
  set (theta := arc_angle_from_start a P).
  assert (Hr : 0 < r) by (apply arc_radius_pos; exact Hva).
  assert (HA : dist_sq (arc_center a) (arc_start a) = r * r).
  { unfold r, arc_radius, dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  assert (HC : dist_sq (arc_center a) (arc_end a) = r * r).
  { unfold r. rewrite <- (arc_center_dist_end a Hva).
    unfold dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  assert (HM : dist_sq (arc_center a) (arc_mid a) = r * r).
  { unfold r. rewrite <- (arc_center_dist_mid a Hva).
    unfold dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  assert (HP : dist_sq (arc_center a) P = r * r).
  { unfold r. rewrite (inCircle_R_zero_implies_equidistant a P Hva Hcirc).
    unfold arc_radius, dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  assert (HuA := on_circle_vec_nonzero (arc_center a) (arc_start a) r Hr HA).
  assert (HuC := on_circle_vec_nonzero (arc_center a) (arc_end a) r Hr HC).
  assert (HuM := on_circle_vec_nonzero (arc_center a) (arc_mid a) r Hr HM).
  assert (HuP := on_circle_vec_nonzero (arc_center a) P r Hr HP).
  assert (Hgrange : -PI < gamma <= PI)
    by (unfold gamma, arc_angle_from_start, signed_angle_from;
        apply angle_between_range; assumption).
  assert (Hmrange : -PI < thetaM <= PI)
    by (unfold thetaM, arc_angle_from_start, signed_angle_from;
        apply angle_between_range; assumption).
  assert (Htrange : -PI < theta <= PI)
    by (unfold theta, arc_angle_from_start, signed_angle_from;
        apply angle_between_range; assumption).
  (* Closed forms for arc_side_chord at the mid point and at P. *)
  assert (HsideM : arc_side_chord a (arc_mid a)
                   = r * r * (4 * sin (gamma/2) * sin (thetaM/2) * sin ((thetaM-gamma)/2))).
  { unfold arc_side_chord.
    rewrite (cross_on_circle_value (arc_center a) (arc_start a) (arc_end a) (arc_mid a) r Hr HA HC HM).
    rewrite <- (arc_angle_from_start_eq a (arc_end a)), <- (arc_angle_from_start_eq a (arc_mid a)).
    fold gamma thetaM.
    rewrite (sin_sum_to_product thetaM gamma). ring. }
  assert (HsideP : arc_side_chord a P
                   = r * r * (4 * sin (gamma/2) * sin (theta/2) * sin ((theta-gamma)/2))).
  { unfold arc_side_chord.
    rewrite (cross_on_circle_value (arc_center a) (arc_start a) (arc_end a) P r Hr HA HC HP).
    rewrite <- (arc_angle_from_start_eq a (arc_end a)), <- (arc_angle_from_start_eq a P).
    fold gamma theta.
    rewrite (sin_sum_to_product theta gamma). ring. }
  assert (Hgnz : gamma <> 0) by (apply arc_gamma_nonzero; exact Hva).
  assert (Hgsame := sign_match_sin_half gamma ltac:(lra)).
  assert (Hgsin_nz : sin (gamma/2) <> 0).
  { unfold same_sign in Hgsame. intro Hcontra.
    destruct Hgsame as [[_ Hb]|[[Ha _]|[_ Hb]]]; lra. }
  assert (Hrrpos : 0 < r * r) by nra.
  assert (Hgsq_pos : 0 < sin (gamma/2) * sin (gamma/2)).
  { destruct (Rtotal_order (sin (gamma/2)) 0) as [Hlt | [Heq | Hgt]].
    - nra.
    - exfalso. apply Hgsin_nz. exact Heq.
    - nra. }
  assert (Hrr4 : 0 < (r * r) * (r * r)) by nra.
  assert (HK : 0 < 16 * (r * r) * (r * r) * (sin (gamma/2) * sin (gamma/2))) by nra.
  (* Same-sign chain: (thetaM*(thetaM-gamma))*(theta*(theta-gamma))  ~~  the
     product of sines appearing in HsideM * HsideP (up to the positive
     constant 16*r^4*sin(gamma/2)^2). *)
  assert (HsameM1 := sign_match_sin_half thetaM ltac:(lra)).
  assert (HsameM2 := sign_match_sin_half (thetaM - gamma) ltac:(lra)).
  assert (HsameT1 := sign_match_sin_half theta ltac:(lra)).
  assert (HsameT2 := sign_match_sin_half (theta - gamma) ltac:(lra)).
  assert (HsameM := same_sign_mult thetaM (sin (thetaM/2)) (thetaM - gamma)
                       (sin ((thetaM-gamma)/2)) HsameM1 HsameM2).
  assert (HsameT := same_sign_mult theta (sin (theta/2)) (theta - gamma)
                       (sin ((theta-gamma)/2)) HsameT1 HsameT2).
  assert (Hsame := same_sign_mult (theta * (theta - gamma)) (sin (theta/2) * sin ((theta-gamma)/2))
                      (thetaM * (thetaM - gamma)) (sin (thetaM/2) * sin ((thetaM-gamma)/2))
                      HsameT HsameM).
  assert (Hmain : 0 < (theta * (theta - gamma)) * (thetaM * (thetaM - gamma))
                  <-> 0 < (sin (theta/2) * sin ((theta-gamma)/2))
                          * (sin (thetaM/2) * sin ((thetaM-gamma)/2)))
    by (apply same_sign_pos_iff; exact Hsame).
  assert (Hinterior_iff :
    arc_interior_side a P
    <-> 0 < (theta * (theta - gamma)) * (thetaM * (thetaM - gamma))).
  { unfold arc_interior_side.
    rewrite HsideM, HsideP.
    replace (r * r * (4 * sin (gamma/2) * sin (thetaM/2) * sin ((thetaM-gamma)/2))
             * (r * r * (4 * sin (gamma/2) * sin (theta/2) * sin ((theta-gamma)/2))))
      with ((16 * (r * r) * (r * r) * (sin (gamma/2) * sin (gamma/2)))
            * ((sin (theta/2) * sin ((theta-gamma)/2)) * (sin (thetaM/2) * sin ((thetaM-gamma)/2))))
      by ring.
    rewrite (pos_scale_iff _ _ HK).
    rewrite Hmain. tauto. }
  unfold arc_span_contains_atan2, arc_span_contains.
  fold theta gamma thetaM.
  split.
  - intros [Hprod | Hends].
    + left. apply Hinterior_iff. exact Hprod.
    + right. exact Hends.
  - intros [Hint | Hends].
    + left. apply Hinterior_iff. exact Hint.
    + right. exact Hends.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_span_contains_atan2_iff_chord_sign.

(* -------------------------------------------------------------------------- *)
(* §9  N-AA item ②: radical points on both circumcircles + atan2 discharge.  *)
(* Vieta identities stay 3-axiom in ArcArcQuartic.v.                          *)
(* -------------------------------------------------------------------------- *)

Lemma radical_plus_on_circle_a1 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1)
      (radical_point_plus (arc_center a1) (arc_center a2)
                          (arc_radius a1) (arc_radius a2)) = 0.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  destruct (radical_points_on_circles
              (arc_center a1) (arc_center a2) (arc_radius a1) (arc_radius a2)
              (arc_radius_pos a1 Hva1) (arc_radius_pos a2 Hva2)
              Hdpos Hrabs Hdlt)
    as [[HdP1 _] _].
  apply inCircle_R_zero_of_equidistant; [exact Hva1 |].
  assert (Hr1sq : arc_radius a1 * arc_radius a1
                  = dist_sq (arc_center a1) (arc_start a1)).
  { rewrite arc_radius_eq_sqrt. rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }
  lra.
Qed.

Lemma radical_plus_on_circle_a2 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2)
      (radical_point_plus (arc_center a1) (arc_center a2)
                          (arc_radius a1) (arc_radius a2)) = 0.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  destruct (radical_points_on_circles
              (arc_center a1) (arc_center a2) (arc_radius a1) (arc_radius a2)
              (arc_radius_pos a1 Hva1) (arc_radius_pos a2 Hva2)
              Hdpos Hrabs Hdlt)
    as [[_ HdP2] _].
  apply inCircle_R_zero_of_equidistant; [exact Hva2 |].
  assert (Hr2sq : arc_radius a2 * arc_radius a2
                  = dist_sq (arc_center a2) (arc_start a2)).
  { rewrite arc_radius_eq_sqrt. rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }
  lra.
Qed.

Lemma radical_minus_on_circle_a1 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1)
      (radical_point_minus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2)) = 0.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  destruct (radical_points_on_circles
              (arc_center a1) (arc_center a2) (arc_radius a1) (arc_radius a2)
              (arc_radius_pos a1 Hva1) (arc_radius_pos a2 Hva2)
              Hdpos Hrabs Hdlt)
    as [_ [HdM1 _]].
  apply inCircle_R_zero_of_equidistant; [exact Hva1 |].
  assert (Hr1sq : arc_radius a1 * arc_radius a1
                  = dist_sq (arc_center a1) (arc_start a1)).
  { rewrite arc_radius_eq_sqrt. rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }
  lra.
Qed.

Lemma radical_minus_on_circle_a2 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2)
      (radical_point_minus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2)) = 0.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  destruct (radical_points_on_circles
              (arc_center a1) (arc_center a2) (arc_radius a1) (arc_radius a2)
              (arc_radius_pos a1 Hva1) (arc_radius_pos a2 Hva2)
              Hdpos Hrabs Hdlt)
    as [_ [_ HdM2]].
  apply inCircle_R_zero_of_equidistant; [exact Hva2 |].
  assert (Hr2sq : arc_radius a2 * arc_radius a2
                  = dist_sq (arc_center a2) (arc_start a2)).
  { rewrite arc_radius_eq_sqrt. rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }
  lra.
Qed.

Lemma radical_plus_span_iff_a1 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    (arc_span_contains_atan2 a1
       (radical_point_plus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2))
     <->
     arc_span_contains a1
       (radical_point_plus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2))).
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  apply arc_span_contains_atan2_iff_chord_sign; [exact Hva1 |].
  exact (radical_plus_on_circle_a1 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
Qed.

Lemma radical_plus_span_iff_a2 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    (arc_span_contains_atan2 a2
       (radical_point_plus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2))
     <->
     arc_span_contains a2
       (radical_point_plus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2))).
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  apply arc_span_contains_atan2_iff_chord_sign; [exact Hva2 |].
  exact (radical_plus_on_circle_a2 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
Qed.

Lemma radical_minus_span_iff_a1 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    (arc_span_contains_atan2 a1
       (radical_point_minus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2))
     <->
     arc_span_contains a1
       (radical_point_minus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2))).
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  apply arc_span_contains_atan2_iff_chord_sign; [exact Hva1 |].
  exact (radical_minus_on_circle_a1 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
Qed.

Lemma radical_minus_span_iff_a2 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    (arc_span_contains_atan2 a2
       (radical_point_minus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2))
     <->
     arc_span_contains a2
       (radical_point_minus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2))).
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  apply arc_span_contains_atan2_iff_chord_sign; [exact Hva2 |].
  exact (radical_minus_on_circle_a2 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
Qed.

(* WITNESS {"claimId":"64","topic":"arc","lemma":"arc_arc_intersects_of_atan2_radical_span","title":"N-AA atan2 radical-span discharge: atan2 sector on one named radical point for both arcs implies arc_arc_intersects","file":"theories/ArcSpanAtan2.v"} *)

Theorem arc_arc_intersects_of_atan2_radical_span :
  forall a1 a2 : CircularArc,
    valid_arc a1 ->
    valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    ((arc_span_contains_atan2 a1
        (radical_point_plus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2)) /\
      arc_span_contains_atan2 a2
        (radical_point_plus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2)))
     \/
     (arc_span_contains_atan2 a1
        (radical_point_minus (arc_center a1) (arc_center a2)
                             (arc_radius a1) (arc_radius a2)) /\
      arc_span_contains_atan2 a2
        (radical_point_minus (arc_center a1) (arc_center a2)
                             (arc_radius a1) (arc_radius a2)))) ->
    arc_arc_intersects a1 a2.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt Hatan2.
  apply (arc_arc_intersects_of_circles_and_radical_signs
           a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
  destruct Hatan2 as [[H1 H2] | [H1 H2]].
  - left. split.
    + apply (radical_plus_span_iff_a1 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
      exact H1.
    + apply (radical_plus_span_iff_a2 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
      exact H2.
  - right. split.
    + apply (radical_minus_span_iff_a1 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
      exact H1.
    + apply (radical_minus_span_iff_a2 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
      exact H2.
Qed.

Print Assumptions arc_arc_intersects_of_atan2_radical_span.
