(* ============================================================================
   NetTopologySuite.Proofs.ArcDistance
   ----------------------------------------------------------------------------
   Issue #64 / JTS curve-awareness D-PT: POINT-TO-CIRCLE distance, the analytic
   core / proof companion of the oracle ARC_DISTANCE mode.

   For a circle of centre O and radius r, and any external point P, the distance
   to the circle has the closed form |dist O P - r|:

     - LOWER BOUND (`point_circle_dist_lower`): every circle point X
       (dist O X = r) is at least |dist O P - r| from P -- the reverse triangle
       inequality through O.  This is the SOUNDNESS direction: the oracle's
       radial value |dist O P - r| never over-states the true distance.
     - ATTAINMENT (`radial_foot` + `radial_foot_on_circle` / `radial_foot_dist`):
       the radial foot O + (r/|OP|)(P - O) is on the circle and is exactly
       |dist O P - r| from P -- the "radial points" anchor.

   Composed (`point_circle_dist_radial`): the radial foot realises the infimum,
   so the point-to-circle distance IS |dist O P - r|.  This is precisely the
   value ARC_DISTANCE emits for its on-arc (radial-foot) case; the arc's sector
   clamping (foot off-sector -> nearest endpoint) is the deferred follow-up.

   Pure metric algebra (`Distance` + `Linearise.dist_triangle`); the radial foot
   uses `field` (division by |OP| > 0).  THREE-AXIOM (the classical-reals trio --
   no trig / atan2 / sin_lt_x), so no `docs/audit-exceptions.txt` entry.  No
   `Admitted`/`Axiom`/`Parameter`.

   DEFERRED (honest scope): the CircularArc bridge (arc_center / arc_radius and
   the on-arc-sector membership decision -- foot in span vs nearest endpoint),
   matching the oracle's atan2 sector test; and arc-to-arc distance (D-AA).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Linearise.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Lower bound: the circle is at least |dist O P - r| from P.              *)
(*                                                                            *)
(* Reverse triangle inequality through the centre O.  No construction needed;  *)
(* holds for every point X on the circle.                                      *)
(* -------------------------------------------------------------------------- *)

Theorem point_circle_dist_lower :
  forall (O P X : Point) (r : R),
    dist O X = r ->
    Rabs (dist O P - r) <= dist P X.
Proof.
  intros O P X r HX.
  pose proof (dist_triangle O P X) as T1.   (* dist O X <= dist O P + dist P X *)
  pose proof (dist_triangle O X P) as T2.   (* dist O P <= dist O X + dist X P *)
  rewrite (dist_sym X P) in T2.
  rewrite HX in T1, T2.
  apply Rabs_le. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Attainment: the radial foot is on the circle, exactly |dist O P - r|.   *)
(* -------------------------------------------------------------------------- *)

(* The radius-r point on the ray from O toward P (P /= O). *)
Definition radial_foot (O P : Point) (r : R) : Point :=
  mkPoint (px O + r / dist O P * (px P - px O))
          (py O + r / dist O P * (py P - py O)).

(* d^2 = dist_sq, recovered from dist = sqrt dist_sq. *)
Lemma dist_mul_self : forall p q, dist p q * dist p q = dist_sq p q.
Proof.
  intros p q. unfold dist. apply sqrt_sqrt. apply dist_sq_nonneg.
Qed.

(* The radial foot lies on the circle: distance r from O (for r >= 0). *)
Lemma radial_foot_on_circle :
  forall (O P : Point) (r : R),
    0 < dist O P -> 0 <= r ->
    dist O (radial_foot O P r) = r.
Proof.
  intros O P r Hd Hr.
  assert (Hd2 : dist O P * dist O P = dist_sq O P) by apply dist_mul_self.
  (* dist_sq of the foot factors as (r/|OP|)^2 * dist_sq O P -- a pure field
     identity over the coordinates (no metric relation needed yet). *)
  assert (HOF : dist_sq O (radial_foot O P r)
                = r / dist O P * (r / dist O P) * dist_sq O P).
  { unfold dist_sq, radial_foot. simpl. field. lra. }
  assert (Hsq : dist_sq O (radial_foot O P r) = r * r).
  { rewrite HOF, <- Hd2. field. lra. }
  unfold dist. rewrite Hsq.
  replace (r * r) with (Rsqr r) by (unfold Rsqr; ring).
  apply sqrt_Rsqr. exact Hr.
Qed.

(* The radial foot is exactly |dist O P - r| from P -- the attained distance. *)
Lemma radial_foot_dist :
  forall (O P : Point) (r : R),
    0 < dist O P ->
    dist P (radial_foot O P r) = Rabs (dist O P - r).
Proof.
  intros O P r Hd.
  assert (Hd2 : dist O P * dist O P = dist_sq O P) by apply dist_mul_self.
  assert (HPF : dist_sq P (radial_foot O P r)
                = (1 - r / dist O P) * (1 - r / dist O P) * dist_sq O P).
  { unfold dist_sq, radial_foot. simpl. field. lra. }
  assert (Hsq : dist_sq P (radial_foot O P r)
                = (dist O P - r) * (dist O P - r)).
  { rewrite HPF, <- Hd2. field. lra. }
  unfold dist. rewrite Hsq.
  replace ((dist O P - r) * (dist O P - r)) with (Rsqr (dist O P - r))
    by (unfold Rsqr; ring).
  apply sqrt_Rsqr_abs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The point-to-circle distance is |dist O P - r| (infimum, attained).     *)
(* -------------------------------------------------------------------------- *)

Theorem point_circle_dist_radial :
  forall (O P : Point) (r : R),
    0 < dist O P -> 0 <= r ->
    (* the radial foot is on the circle ... *)
    dist O (radial_foot O P r) = r
    (* ... at distance exactly |dist O P - r| from P ... *)
    /\ dist P (radial_foot O P r) = Rabs (dist O P - r)
    (* ... and no circle point is closer. *)
    /\ (forall X, dist O X = r -> Rabs (dist O P - r) <= dist P X).
Proof.
  intros O P r Hd Hr.
  split; [ apply radial_foot_on_circle; assumption | ].
  split; [ apply radial_foot_dist; assumption | ].
  intros X HX. apply (point_circle_dist_lower O P X r HX).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions point_circle_dist_lower.
Print Assumptions radial_foot_on_circle.
Print Assumptions radial_foot_dist.
Print Assumptions point_circle_dist_radial.
