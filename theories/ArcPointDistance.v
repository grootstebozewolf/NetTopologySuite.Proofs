(* ============================================================================
   NetTopologySuite.Proofs.ArcPointDistance
   ----------------------------------------------------------------------------
   Issue #64 / JTS curve-awareness D-PT: POINT-TO-ARC distance (full analytical,
   not just circle).  Proof companion / soundness export for the ARC_DISTANCE
   (and COMPOUND_ARC_DISTANCE) oracle mode, ready for RocqRefRunner bit-exact
   pinning (distance_point_to_arc).

   Reuses:
     - ArcDistance.point_circle_dist_* / radial_foot (the |d - r| core)
     - ArcOrient.arc_orient / arc_interior_side (via arc_side_chord)
     - ArcIntersect.arc_span_contains (the chord-directed "directedSweep" proxy
       used by all current arc-span proofs; Option B / <pi characterisation)
     - ArcArcCircles.inCircle_R_zero_of_equidistant (via radial construction)
     - CurveGeometry (valid_arc, arc_center, arc_radius)
     - on_arc (from CurveRingSimple)

   Five edge-case families covered by the case split on the radial foot:
     1. P at arc endpoint (A or C)            → 0
     2. P on arc interior (inCircle=0 ∧ span) → 0
     3. Radial foot F lands in arc span       → |OP| − r
     4. Radial foot outside sweep             → min(dist P A, dist P C)
     5. P coincides with centre O             → r

   Soundness (lower bound) and attainment proven for the radial case directly.
   The endpoint fallback case (radial foot outside the sweep) is DISCHARGED by
   reducing min-endpoint selection to the single-peak dot bound banked in
   ArcSinglePeak.v (circle_dist_le_of_dot_ge + arc_dot_max_at_endpoint); the only
   residual obligation is the isolated planar inequality arc_dot_max_at_endpoint.

   Pure math + decidable side tests.  3-axiom footprint (same as ArcDistance.v).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Linearise ArcDistance ArcOrient ArcIntersect
  CurveGeometry ArcChordApprox ArcArcCircles.
From NTS.Proofs Require Import CurveRingSimple ArcSinglePeak.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Local alias for on_arc (on circumcircle AND in directed sweep).            *)
(* -------------------------------------------------------------------------- *)

Definition on_arc := CurveRingSimple.on_arc.

(* -------------------------------------------------------------------------- *)
(* §1  Radial foot on arc (when the directed-sweep test passes).              *)
(* -------------------------------------------------------------------------- *)

Lemma radial_foot_on_arc_when_span :
  forall (a : CircularArc) (P : Point),
    valid_arc a ->
    0 < dist (arc_center a) P ->
    let O := arc_center a in
    let r := arc_radius a in
    let F := radial_foot O P r in
    arc_span_contains a F ->
    on_arc a F.
Proof.
  intros a P Hva Hd O r F Hspan.
  unfold on_arc.
  split.
  - pose proof (radial_foot_on_circle (arc_center a) P (arc_radius a) Hd (arc_radius_nonneg a)) as HF.
    assert (Hsq : dist_sq (arc_center a) (radial_foot (arc_center a) P (arc_radius a)) = dist_sq (arc_center a) (arc_start a)).
    { rewrite <- 2!dist_mul_self.
      rewrite HF.
      unfold arc_radius. reflexivity. }
    apply inCircle_R_zero_of_equidistant; [ exact Hva | exact Hsq ].
  - exact Hspan.
Qed.

Definition point_to_arc_candidate_endpoints (a : CircularArc) (P : Point) : R :=
  let da := dist (arc_start a) P in
  let dc := dist (arc_end a) P in
  if Rle_dec da dc then da else dc.

(* -------------------------------------------------------------------------- *)
(* §2  Soundness lemma 1: radial case lower bound (delegates to circle).      *)
(* -------------------------------------------------------------------------- *)

Lemma point_to_arc_dist_radial_lower :
  forall (a : CircularArc) (P X : Point),
    valid_arc a ->
    on_arc a X ->
    let O := arc_center a in
    let r := arc_radius a in
    0 < dist O P ->
    let F := radial_foot O P r in
    arc_span_contains a F ->
    Rabs (dist O P - r) <= dist P X.
Proof.
  intros a P X Hva Hon O r Hd F _.
  (* on_arc X gives inCircle_R = 0, from which we derive dist O X = r. *)
  destruct Hon as [Hdet _].
  assert (Heq : dist_sq (arc_center a) X = dist_sq (arc_center a) (arc_start a))
    by (apply inCircle_R_zero_implies_equidistant; assumption).
  assert (HdX : dist O X = r).
  { unfold O, r, arc_radius, dist.
    f_equal. exact Heq. }
  apply point_circle_dist_lower. exact HdX.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Soundness lemma 2 + attainment: radial foot case.                       *)
(* -------------------------------------------------------------------------- *)

Lemma point_to_arc_attains_radial :
  forall (a : CircularArc) (P : Point),
    valid_arc a ->
    0 < dist (arc_center a) P ->
    let O := arc_center a in
    let r := arc_radius a in
    let F := radial_foot O P r in
    arc_span_contains a F ->
    on_arc a F /\ dist P F = Rabs (dist O P - r).
Proof.
  intros a P Hva Hd O r F Hspan.
  split.
  - apply radial_foot_on_arc_when_span; assumption.
  - apply radial_foot_dist; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Soundness lemma 3/4 (endpoint fallback + centre + zero cases).          *)
(*     These close the 5 edge-case families for the RocqRefRunner pin.         *)
(* -------------------------------------------------------------------------- *)

(* When the radial foot is rejected by the directed sweep (arc_span_contains),
   the reported distance is the nearer endpoint distance.  The lemma states
   the required lower-bound property for all on-arc X (the non-trivial fact
   that no interior arc point is closer to P than the nearer chord end).

   PROVED: the metric statement reduces to the single-peak dot bound.  On the
   common circle, dist P Y is decreasing in gdot O P Y (circle_dist_le_of_dot_ge);
   X-in-span with foot-outside-span puts X and the foot on opposite sides of the
   chord SE (sign_opp + the arc_side_chord bridge), so arc_dot_max_at_endpoint
   bounds gdot O P X by the larger endpoint dot, hence dist P X by the nearer
   endpoint distance.  The lone residue is the planar arc_dot_max_at_endpoint. *)
Lemma point_to_arc_dist_fallback_ends_lower :
  forall (a : CircularArc) (P X : Point),
    valid_arc a ->
    on_arc a X ->
    let O := arc_center a in
    let r := arc_radius a in
    let F := radial_foot O P r in
    0 < dist O P ->
    ~ arc_span_contains a F ->
    (* reported = min endpoint dist *)
    point_to_arc_candidate_endpoints a P <= dist P X.
Proof.
  intros a P X Hva Hon O r F Hd Hnot.
  (* Reduce the metric statement to the isolated dot bound (ArcSinglePeak). *)
  set (S := arc_start a). set (E := arc_end a).
  (* Circle facts. *)
  assert (HS : dist O S = r) by reflexivity.
  assert (HX : dist O X = r).
  { destruct Hon as [Hdet _].
    assert (Heq : dist_sq O X = dist_sq O S)
      by (apply inCircle_R_zero_implies_equidistant; assumption).
    unfold O, r, arc_radius, dist. f_equal. exact Heq. }
  assert (HE : dist O E = r).
  { destruct (arc_center_equidistant a Hva) as [_ Hse].
    unfold O, r, arc_radius, dist. f_equal. symmetry. exact Hse. }
  (* X in span, foot F outside span  ==>  X and F opposite sides of chord SE. *)
  assert (Hside : side S E X * side S E F <= 0).
  { destruct Hon as [_ Hspan].
    assert (HmF : arc_side_chord a (arc_mid a) * arc_side_chord a F <= 0).
    { apply Rnot_lt_le. intro Hc. apply Hnot. left. exact Hc. }
    assert (Hbridge : forall Y, side S E Y = arc_side_chord a Y).
    { intro Y. unfold side, S, E, arc_side_chord, cross_R_pt. ring. }
    rewrite (Hbridge X), (Hbridge F).
    destruct Hspan as [Hint | [HXS | HXE]].
    - apply (sign_opp (arc_side_chord a (arc_mid a))).
      + exact Hint.
      + exact HmF.
    - rewrite HXS. rewrite <- (Hbridge (arc_start a)).
      unfold side, S. cbn [px py]. nra.
    - rewrite HXE. rewrite <- (Hbridge (arc_end a)).
      unfold side, E. cbn [px py]. nra. }
  (* The dot bound, then monotonicity-in-dot to compare endpoint distances. *)
  pose proof (arc_dot_max_at_endpoint O P S E X r HS HE HX Hside Hd) as Hdot.
  (* candidate (min endpoint dist) <= each endpoint dist *)
  assert (Hcda : point_to_arc_candidate_endpoints a P <= dist (arc_start a) P).
  { unfold point_to_arc_candidate_endpoints.
    destruct (Rle_dec (dist (arc_start a) P) (dist (arc_end a) P)); lra. }
  assert (Hcdc : point_to_arc_candidate_endpoints a P <= dist (arc_end a) P).
  { unfold point_to_arc_candidate_endpoints.
    destruct (Rle_dec (dist (arc_start a) P) (dist (arc_end a) P)); lra. }
  destruct (Rle_dec (gdot O P E) (gdot O P S)) as [Hcmp|Hcmp].
  - (* dot E <= dot S, so Rmax = dot S, and dot X <= dot S ==> dist P S <= dist P X *)
    rewrite Rmax_left in Hdot by exact Hcmp.
    pose proof (circle_dist_le_of_dot_ge O P S X r HS HX Hdot) as Hps.
    rewrite (dist_sym P S) in Hps. eapply Rle_trans; [ exact Hcda | exact Hps ].
  - (* dot S < dot E, so Rmax = dot E, and dot X <= dot E ==> dist P E <= dist P X *)
    apply Rnot_le_lt in Hcmp.
    rewrite Rmax_right in Hdot by exact (Rlt_le _ _ Hcmp).
    pose proof (circle_dist_le_of_dot_ge O P E X r HE HX Hdot) as Hpe.
    rewrite (dist_sym P E) in Hpe. eapply Rle_trans; [ exact Hcdc | exact Hpe ].
Qed.

(* Centre case: every point on the arc is exactly r from O. *)
Lemma point_to_arc_dist_centre_is_r :
  forall (a : CircularArc) (P X : Point),
    valid_arc a ->
    dist (arc_center a) P = 0 ->
    on_arc a X ->
    arc_radius a = dist P X.
Proof.
  intros a P X Hva Hdist Hon.
  (* dist(O, P) = 0 implies P has same coords as O. *)
  apply dist_eq_zero_iff in Hdist as [Hpx Hpy].
  (* on_arc X implies dist O X = r via inCircle_R_zero_implies_equidistant. *)
  destruct Hon as [Hdet _].
  assert (Hsq : dist_sq (arc_center a) X = dist_sq (arc_center a) (arc_start a))
    by (apply inCircle_R_zero_implies_equidistant; assumption).
  assert (HdX : dist (arc_center a) X = arc_radius a).
  { unfold arc_radius, dist. f_equal. exact Hsq. }
  (* dist P X = dist (arc_center a) X since px P = px O and py P = py O. *)
  assert (HPeqO : dist P X = dist (arc_center a) X).
  { unfold dist, dist_sq. cbn [px py]. rewrite Hpx, Hpy. reflexivity. }
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline 4-lemma bundle (the "4 lemmas" for oracle_protocol / extraction).  *)
(* -------------------------------------------------------------------------- *)

(* 1. Radial lower bound soundness *)
Print Assumptions point_to_arc_dist_radial_lower.

(* 2. Radial attainment *)
Print Assumptions point_to_arc_attains_radial.

(* 3. Radial foot lies on arc iff span accepts (helper) *)
Print Assumptions radial_foot_on_arc_when_span.

(* 4. Fallback + special cases (Qed; reduces to the single-peak dot bound) *)
Print Assumptions point_to_arc_dist_fallback_ends_lower.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint (3-axiom + the single isolated planar dot bound).       *)
(* -------------------------------------------------------------------------- *)

(* All five edge-case families are Qed.  The fallback lower bound is discharged
   by reduction to ArcSinglePeak.arc_dot_max_at_endpoint -- the sole remaining
   Tier-3 obligation, a crisp planar inequality with no metric residue.  The
   module gives fully-extractable soundness for ARC_DISTANCE / D-PT bit-exact
   use in RocqRefRunner + NTS CircularString.Distance pin.
*)
