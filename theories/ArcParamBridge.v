(* ============================================================================
   NetTopologySuite.Proofs.ArcParamBridge
   ----------------------------------------------------------------------------
   Issue #508, the "Also owed" bridge: the 3-point CircularArc model meets
   the parameterized-circle model — and through it, the CurveLength spec.

   ArcRectifiable.v proved r·θ is the metric length of the PARAMETERIZED
   circle t ↦ O + r·(cos t, sin t).  The engines and the corpus's CircularArc
   carry arcs as 3 points (start/mid/end) instead, with the central sweep
   `arc_sweep_angle` recovered through atan2 / `angle_between`.  This file
   connects the two: for a `valid_arc`, the principal sweep is REALIZED by a
   parameter interval of the circumscribed circle — the interval's circle
   points are exactly `arc_start`/`arc_end` (in sweep orientation), its width
   is `|arc_sweep_angle|`, and its metric length in the `is_curve_length`
   sense is exactly `arc_length (arc_radius a) (Rabs (arc_sweep_angle a))` —
   the number `ARC_LENGTH` emits and `arc_chord_le_arc_length` bounds.

   Exposed surface (consumed by the major-traversal rung):
     arc_anchor_angle      the start point's atan2 angle on the circle
     arc_anchor_endpoints  circle_pt at the anchor / anchor+sweep are
                           exactly arc_start / arc_end
     realize_sweep         any anchored sweep psi yields the oriented
                           interval + its is_curve_length value

   Proof route (branch-cut-free): anchor the start angle with
   `atan2_on_circle`; rotate onto the end point by `cos_plus`/`sin_plus`
   against the `cos_angle_between`/`sin_angle_between` characterisations —
   the mixed terms cancel through ux(ux·vx + uy·vy) − uy(ux·vy − uy·vx)
   = (ux² + uy²)·vx, so no atan2 difference identity is ever needed.

   Assumption footprint: 3-axiom (IVT atan2; allowlist).  Not exempted.

   Deliberately NOT this file: the mid-point-disambiguated MAJOR traversal
   (`arc_sweep`, |sweep| possibly > π) — that reflex case is the next rung
   (ArcTraversalBridge.v).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcChordApprox
                               Atan2 AngleBetween RelateArcAnalytic
                               ArcLength CurveLength ArcRectifiable.
Local Open Scope R_scope.

(* Surjective pairing for Point. *)
Lemma point_ext : forall p q : Point, px p = px q -> py p = py q -> p = q.
Proof.
  intros [xp yp] [xq yq]; simpl; intros; subst; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* The anchor: arc_start's atan2 angle on the circumscribed circle.           *)
(* -------------------------------------------------------------------------- *)

Definition arc_anchor_angle (a : CircularArc) : R :=
  atan2 (py (arc_start a) - py (arc_center a))
        (px (arc_start a) - px (arc_center a)).

Lemma arc_anchor_endpoints : forall a : CircularArc,
  valid_arc a ->
  circle_pt (arc_center a) (arc_radius a) (arc_anchor_angle a) = arc_start a
  /\ circle_pt (arc_center a) (arc_radius a)
               (arc_anchor_angle a + arc_sweep_angle a) = arc_end a.
Proof.
  intros a Hva.
  destruct (arc_center_vectors_nonzero a Hva) as [Hu Hv].
  destruct (arc_center_equidistant a Hva) as [_ Hse].
  set (ux := px (arc_start a) - px (arc_center a)) in *.
  set (uy := py (arc_start a) - py (arc_center a)) in *.
  set (vx := px (arc_end a) - px (arc_center a)) in *.
  set (vy := py (arc_end a) - py (arc_center a)) in *.
  set (r := arc_radius a) in *.
  set (phi := arc_sweep_angle a) in *.
  set (s := arc_anchor_angle a) in *.
  (* norms: both center-to-endpoint vectors have squared norm r*r *)
  assert (Huv2 : ux * ux + uy * uy = vx * vx + vy * vy).
  { replace (ux * ux + uy * uy)
      with (dist_sq (arc_center a) (arc_start a))
      by (unfold dist_sq, ux, uy; ring).
    replace (vx * vx + vy * vy)
      with (dist_sq (arc_center a) (arc_end a))
      by (unfold dist_sq, vx, vy; ring).
    exact Hse. }
  assert (Hr2u : r * r = ux * ux + uy * uy).
  { unfold r, arc_radius. rewrite dist_mul_self.
    unfold dist_sq, ux, uy. ring. }
  assert (Hupos : 0 < ux * ux + uy * uy) by (apply sum_sq_pos; exact Hu).
  assert (Hr0 : 0 <= r) by (unfold r, arc_radius; apply dist_nonneg).
  assert (Hrpos : 0 < r) by nra.
  (* the anchor angle and the trig facts *)
  assert (Hsqu : sqrt (ux * ux + uy * uy) = r).
  { rewrite <- Hr2u.
    replace (r * r) with (Rsqr r) by (unfold Rsqr; ring).
    apply sqrt_Rsqr; lra. }
  assert (Hsqv : sqrt (vx * vx + vy * vy) = r) by (rewrite <- Huv2; exact Hsqu).
  assert (Hcs : cos s = ux / r).
  { unfold s, arc_anchor_angle. fold uy. fold ux.
    rewrite cos_atan2 by exact Hu. rewrite Hsqu. reflexivity. }
  assert (Hss : sin s = uy / r).
  { unfold s, arc_anchor_angle. fold uy. fold ux.
    rewrite sin_atan2 by exact Hu. rewrite Hsqu. reflexivity. }
  assert (Hcphi : cos phi = (ux * vx + uy * vy) / (r * r)).
  { unfold phi, arc_sweep_angle. cbv zeta.
    fold ux uy vx vy.
    rewrite cos_angle_between by assumption.
    rewrite Hsqu, Hsqv. reflexivity. }
  assert (Hsphi : sin phi = (ux * vy - uy * vx) / (r * r)).
  { unfold phi, arc_sweep_angle. cbv zeta.
    fold ux uy vx vy.
    rewrite sin_angle_between by assumption.
    rewrite Hsqu, Hsqv. reflexivity. }
  split.
  - apply point_ext; unfold circle_pt; cbn [px py].
    + rewrite Hcs. unfold ux. field. lra.
    + rewrite Hss. unfold uy. field. lra.
  - apply point_ext; unfold circle_pt; cbn [px py].
    + rewrite cos_plus, Hcs, Hss, Hcphi, Hsphi.
      assert (Hkey : r * (ux / r * ((ux * vx + uy * vy) / (r * r))
                          - uy / r * ((ux * vy - uy * vx) / (r * r))) = vx).
      { replace (r * (ux / r * ((ux * vx + uy * vy) / (r * r))
                      - uy / r * ((ux * vy - uy * vx) / (r * r))))
          with (((ux * ux + uy * uy) * vx) / (r * r)) by (field; lra).
        rewrite <- Hr2u. field. lra. }
      rewrite Hkey. unfold vx. ring.
    + rewrite sin_plus, Hcs, Hss, Hcphi, Hsphi.
      assert (Hkey : r * (uy / r * ((ux * vx + uy * vy) / (r * r))
                          + ux / r * ((ux * vy - uy * vx) / (r * r))) = vy).
      { replace (r * (uy / r * ((ux * vx + uy * vy) / (r * r))
                      + ux / r * ((ux * vy - uy * vx) / (r * r))))
          with (((ux * ux + uy * uy) * vy) / (r * r)) by (field; lra).
        rewrite <- Hr2u. field. lra. }
      rewrite Hkey. unfold vy. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assembly: an anchored sweep psi yields the oriented interval and its       *)
(* is_curve_length value — shared by the principal and major traversals.      *)
(* -------------------------------------------------------------------------- *)

Lemma realize_sweep : forall (Oc : Point) (r s psi : R) (Ps Pe : Point),
  0 <= r ->
  circle_pt Oc r s = Ps ->
  circle_pt Oc r (s + psi) = Pe ->
  exists s' t' : R,
    s' <= t' /\
    t' - s' = Rabs psi /\
    ((circle_pt Oc r s' = Ps /\ circle_pt Oc r t' = Pe) \/
     (circle_pt Oc r s' = Pe /\ circle_pt Oc r t' = Ps)) /\
    is_curve_length (circle_param Oc r) s' t' (arc_length r (Rabs psi)).
Proof.
  intros Oc r s psi Ps Pe Hr Hs He.
  destruct (Rle_dec 0 psi) as [Hp | Hp].
  - exists s, (s + psi).
    split; [lra |].
    split; [rewrite Rabs_right by lra; ring |].
    split; [left; split; assumption |].
    unfold arc_length. rewrite Rabs_right by lra.
    replace (r * psi) with (r * (s + psi - s)) by ring.
    apply arc_r_theta_is_curve_length; [exact Hr | lra].
  - exists (s + psi), s.
    split; [lra |].
    split; [rewrite Rabs_left by lra; ring |].
    split; [right; split; assumption |].
    unfold arc_length. rewrite Rabs_left by lra.
    replace (r * - psi) with (r * (s - (s + psi))) by ring.
    apply arc_r_theta_is_curve_length; [exact Hr | lra].
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: the principal sweep of a 3-point arc is realized on its          *)
(* circumscribed circle with metric length arc_length r |sweep|.              *)
(* -------------------------------------------------------------------------- *)

Theorem arc_sweep_param_bridge : forall a : CircularArc,
  valid_arc a ->
  exists s t : R,
    s <= t /\
    t - s = Rabs (arc_sweep_angle a) /\
    ((circle_pt (arc_center a) (arc_radius a) s = arc_start a /\
      circle_pt (arc_center a) (arc_radius a) t = arc_end a) \/
     (circle_pt (arc_center a) (arc_radius a) s = arc_end a /\
      circle_pt (arc_center a) (arc_radius a) t = arc_start a)) /\
    is_curve_length (circle_param (arc_center a) (arc_radius a)) s t
                    (arc_length (arc_radius a) (Rabs (arc_sweep_angle a))).
Proof.
  intros a Hva.
  destruct (arc_anchor_endpoints a Hva) as [HA HB].
  assert (Hr0 : 0 <= arc_radius a)
    by (unfold arc_radius; apply dist_nonneg).
  exact (realize_sweep (arc_center a) (arc_radius a) (arc_anchor_angle a)
                       (arc_sweep_angle a) (arc_start a) (arc_end a)
                       Hr0 HA HB).
Qed.

Print Assumptions arc_sweep_param_bridge.
