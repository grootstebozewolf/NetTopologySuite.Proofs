(* ============================================================================
   NetTopologySuite.Proofs.ArcChordSubdivision
   ----------------------------------------------------------------------------
   Route (B) follow-up: the equal-angle budget discharge.  Closes the
   trigonometric half of ArcChordApprox.v section 6c's deferral ("the
   n-chord trigonometric version needs sin/cos manipulation") at the
   per-sub-arc level.

   ArcChordDensity.v's headline `n_chords_achieve_eps` takes a CHORD
   budget as hypothesis (squared half-chord <= L^2/n^2).  An equal-angle
   subdivision routine naturally produces an ANGLE budget instead: each
   sub-arc subtends at most theta/n.  This file converts one into the
   other and composes:

     chord_half_length_sq a = arc_radius_sq a * (1 - cos phi) / 2
                            = (r * sin(phi/2))^2          (law of cosines,
                                                           half-angle)
                           <= (r * phi / 2)^2             (sin^2 x <= x^2)

   with phi := arc_central_angle a, the signed angle (AngleBetween.v)
   between the center->start and center->end vectors.  The headline
   `equal_angle_chords_achieve_eps` then states: sub-arcs subtending at
   most theta/n have sagitta <= eps whenever n^2*(r*eps) >= (r*theta/2)^2
   -- the angle-budget form of the route-(B) chord-count law, consumable
   by an equal-angle lineariser (cf. PostGIS's segments-per-quadrant).

   Scope honesty.  Statements remain per-sub-arc: the hypothesis "this
   sub-arc subtends at most theta/n" is the contract an equal-angle
   subdivision routine discharges per piece; the routine itself (the
   list-of-arcs construction) is not built here.  The angle premise is
   one-sided (0 <= phi): a CCW sub-arc convention, the mirrored case
   follows by symmetry of the consumer's encoding.

   The axiom footprint is the atan/sin Category-C lineage (Atan2.v /
   AngleBetween.v / ArcLength.v) -- Stdlib's `sin_lt_x` and the atan2
   layer pull `Classical_Prop.classic`, so this file is 4-axiom; see
   docs/audit-exceptions.txt.  No Admitted.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import CurveGeometry.
From NTS.Proofs Require Import ArcChordApprox.
From NTS.Proofs Require Import ArcChordDensity.
From NTS.Proofs Require Import ArcLength.
From NTS.Proofs Require Import AngleBetween.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The central angle of an arc record.                                    *)
(* -------------------------------------------------------------------------- *)

Definition arc_central_angle (a : CircularArc) : R :=
  angle_between
    (px (arc_start a) - px (arc_center a)) (py (arc_start a) - py (arc_center a))
    (px (arc_end a)   - px (arc_center a)) (py (arc_end a)   - py (arc_center a)).

(* -------------------------------------------------------------------------- *)
(* §2  Law of cosines for the chord, against the record's dist_sq.            *)
(*                                                                            *)
(* Pure algebra: |start - end|^2 = |u|^2 + |v|^2 - 2<u,v> for the             *)
(* center-anchored vectors u, v.                                              *)
(* -------------------------------------------------------------------------- *)

Lemma chord_sq_law_of_cosines :
  forall a : CircularArc,
    dist_sq (arc_start a) (arc_end a)
      = dist_sq (arc_center a) (arc_start a)
        + dist_sq (arc_center a) (arc_end a)
        - 2 * ((px (arc_start a) - px (arc_center a))
                 * (px (arc_end a) - px (arc_center a))
               + (py (arc_start a) - py (arc_center a))
                 * (py (arc_end a) - py (arc_center a))).
Proof.
  intros a. unfold dist_sq. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  chord_half_length_sq through the central angle.                        *)
(*                                                                            *)
(* Under valid_arc and a positive radius the center-anchored vectors are      *)
(* nonzero, AngleBetween.cos_angle_between applies, and both norms are        *)
(* sqrt arc_radius_sq -- so the dot product is arc_radius_sq * cos(phi).      *)
(* -------------------------------------------------------------------------- *)

Lemma chord_half_length_sq_central :
  forall a : CircularArc,
    valid_arc a ->
    0 < arc_radius a ->
    chord_half_length_sq a
      = arc_radius_sq a * (1 - cos (arc_central_angle a)) / 2.
Proof.
  intros a Hva Hr.
  assert (Hr2 : arc_radius a * arc_radius a = arc_radius_sq a).
  { rewrite arc_radius_eq_sqrt. apply sqrt_sqrt. apply arc_radius_sq_nonneg. }
  assert (HR : 0 < arc_radius_sq a) by nra.
  set (ux := px (arc_start a) - px (arc_center a)).
  set (uy := py (arc_start a) - py (arc_center a)).
  set (vx := px (arc_end a) - px (arc_center a)).
  set (vy := py (arc_end a) - py (arc_center a)).
  assert (Hu2 : ux * ux + uy * uy = arc_radius_sq a).
  { unfold ux, uy, arc_radius_sq, dist_sq. ring. }
  assert (Hv2 : vx * vx + vy * vy = arc_radius_sq a).
  { unfold vx, vy. rewrite (arc_radius_sq_eq_end a Hva).
    unfold dist_sq. ring. }
  assert (Hu : ~ (ux = 0 /\ uy = 0)).
  { intros [Hx Hy]. rewrite Hx, Hy in Hu2. lra. }
  assert (Hv : ~ (vx = 0 /\ vy = 0)).
  { intros [Hx Hy]. rewrite Hx, Hy in Hv2. lra. }
  pose proof (cos_angle_between ux uy vx vy Hu Hv) as Hcos.
  fold ux uy vx vy in Hcos.
  assert (Hdot : ux * vx + uy * vy
                   = arc_radius_sq a * cos (arc_central_angle a)).
  { unfold arc_central_angle. fold ux uy vx vy. rewrite Hcos.
    rewrite Hu2, Hv2.
    rewrite sqrt_sqrt by lra.
    field. lra. }
  unfold chord_half_length_sq.
  rewrite (chord_sq_law_of_cosines a).
  fold ux uy vx vy.
  unfold arc_radius_sq in *.
  rewrite <- (arc_radius_sq_eq_end a Hva).
  unfold arc_radius_sq.
  rewrite Hdot. field.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  sin^2 x <= x^2 for x >= 0 (case split at 1; SIN_bound above it).       *)
(* -------------------------------------------------------------------------- *)

Lemma sin_sq_le_sq :
  forall x : R, 0 <= x -> sin x * sin x <= x * x.
Proof.
  intros x Hx.
  destruct (Rle_lt_dec x 1) as [Hle | Hgt].
  - assert (Hs0 : 0 <= sin x).
    { apply sin_ge_0; [exact Hx | ].
      pose proof PI2_1. lra. }
    pose proof (sin_le_x x Hx). nra.
  - pose proof (SIN_bound x) as [Hlo Hhi]. nra.
Qed.

(* 1 - cos theta = 2 sin^2(theta/2), via cos(2a) and sin^2+cos^2 = 1. *)
Lemma one_minus_cos_half_angle :
  forall theta : R,
    1 - cos theta = 2 * (sin (theta / 2) * sin (theta / 2)).
Proof.
  intros theta.
  replace theta with (2 * (theta / 2)) at 1 by field.
  rewrite cos_2a.
  pose proof (sin2_cos2 (theta / 2)) as Hsc.
  unfold Rsqr in Hsc. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The angle-budget bound: half-chord^2 <= (r * phi / 2)^2.               *)
(* -------------------------------------------------------------------------- *)

Lemma chord_half_length_sq_le_angle_budget :
  forall a : CircularArc,
    valid_arc a ->
    0 < arc_radius a ->
    0 <= arc_central_angle a ->
    chord_half_length_sq a
      <= (arc_radius a * arc_central_angle a / 2)
         * (arc_radius a * arc_central_angle a / 2).
Proof.
  intros a Hva Hr Hphi.
  assert (Hr2 : arc_radius a * arc_radius a = arc_radius_sq a).
  { rewrite arc_radius_eq_sqrt. apply sqrt_sqrt. apply arc_radius_sq_nonneg. }
  rewrite (chord_half_length_sq_central a Hva Hr).
  rewrite (one_minus_cos_half_angle (arc_central_angle a)).
  set (h := arc_central_angle a / 2).
  assert (Hh : 0 <= h) by (unfold h; lra).
  pose proof (sin_sq_le_sq h Hh) as Hsin.
  replace (arc_radius a * arc_central_angle a / 2)
    with (arc_radius a * h) by (unfold h; field).
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Headline: equal-angle subdivision achieves eps.                        *)
(*                                                                            *)
(* Angle-budget form of ArcChordDensity.n_chords_achieve_eps: a sub-arc       *)
(* subtending at most theta/n on a radius-r circle has sagitta <= eps         *)
(* whenever n^2 * (r * eps) >= (r * theta / 2)^2 -- i.e.                      *)
(* n >= (theta/2) * sqrt(r/eps).                                              *)
(* -------------------------------------------------------------------------- *)

Theorem equal_angle_chords_achieve_eps :
  forall (a : CircularArc) (r theta eps : R) (n : nat),
    valid_arc a ->
    arc_radius a = r ->
    0 < r ->
    0 <= theta ->
    (1 <= n)%nat ->
    0 <= arc_central_angle a ->
    arc_central_angle a <= theta / INR n ->
    (r * theta / 2) * (r * theta / 2) <= INR n * INR n * (r * eps) ->
    sagitta a <= eps.
Proof.
  intros a r theta eps n Hva Hrr Hr Htheta Hn Hphi0 Hphin Hcount.
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  apply (n_chords_achieve_eps a (r * theta / 2) eps n Hva).
  - rewrite Hrr. exact Hr.
  - exact Hn.
  - (* squared half-chord within (r*theta/2)^2 / n^2, via the angle budget *)
    apply Rle_trans with
      ((arc_radius a * arc_central_angle a / 2)
         * (arc_radius a * arc_central_angle a / 2)).
    + apply chord_half_length_sq_le_angle_budget;
        [exact Hva | rewrite Hrr; exact Hr | exact Hphi0].
    + rewrite Hrr.
      (* (r*phi/2)^2 <= (r*(theta/n)/2)^2 = (r*theta/2)^2 / n^2 *)
      apply Rle_trans with
        ((r * (theta / INR n) / 2) * (r * (theta / INR n) / 2)).
      * assert (0 <= r * arc_central_angle a / 2) by nra.
        assert (r * arc_central_angle a / 2 <= r * (theta / INR n) / 2) by nra.
        nra.
      * right. field. lra.
  - rewrite Hrr. exact Hcount.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Category-C atan/sin lineage (4-axiom; see                    *)
(* docs/audit-exceptions.txt).  The pure-algebra lemmas in §2 stay on the     *)
(* 3-axiom allowlist.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions chord_sq_law_of_cosines.
Print Assumptions chord_half_length_sq_central.
Print Assumptions sin_sq_le_sq.
Print Assumptions one_minus_cos_half_angle.
Print Assumptions chord_half_length_sq_le_angle_budget.
Print Assumptions equal_angle_chords_achieve_eps.
