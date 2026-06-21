(* ============================================================================
   NetTopologySuite.Proofs.ArcChordLength
   ----------------------------------------------------------------------------
   Issue #67 S10b: the law-of-cosines chord-length bridge at `arc_sweep_angle`,
   the analytic gap RelateArcAnalytic.v:16-18 / RelateClothoid.v defer ("the
   law-of-cosines step needs a pose/set transparency seam on vector names").

   Delivers the SQUARED form (avoids the `sqrt` / half-angle sign pitfalls of
   the `2r·sin(θ/2)` chord_subtended form — no sweep-sign guard needed, valid
   for every sweep):

       dist_sq (arc_start a) (arc_end a)
         = 2 · dist_sq (arc_center a) (arc_start a) · (1 − cos (arc_sweep_angle a)).

   i.e. |start − end|² = 2r²(1 − cos θ) with θ the central sweep — the chord²
   identity an analytic curve relate / clothoid lane chains against.

   The core is a provider-agnostic planar law of cosines for two EQUAL-NORM
   vectors, `law_of_cosines_equal_norm`, built directly on
   `AngleBetween.cos_angle_between`.  The arc theorem instantiates it at the
   center-to-endpoint vectors, whose equal norm is `arc_center_equidistant`.

   Assumption footprint: 4-axiom — `cos (angle_between …)` pulls
   `Classical_Prop.classic` through `cos_atan2` / `atan2` (same lineage as
   `theories/AngleBetween.v` and `theories/RelateArcAnalytic.v`).  This file is
   exempted in docs/audit-exceptions.txt accordingly.

   #64 arc length finish: the chord ≤ arc_length bridge is here (Qed via
   ds = c² identity + sqrt_Rsqr + chord_le_arc_length; uses |sweep| and sin_ge_0
   under principal range).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.

From NTS.Proofs Require Import Distance CurveGeometry AngleBetween
                               ArcChordApprox RelateArcAnalytic ArcLength.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Planar law of cosines for two equal-norm vectors (provider-agnostic).  *)
(*                                                                            *)
(* For nonzero u, v with |u|² = |v|²,                                         *)
(*   |u − v|² = 2·|u|²·(1 − cos∠(u,v)),                                        *)
(* with ∠ the signed `angle_between`.  Pure algebra over `cos_angle_between`:  *)
(* the denominator `√|u|²·√|v|² = |u|²` collapses under the equal-norm hyp.    *)
(* -------------------------------------------------------------------------- *)

Lemma law_of_cosines_equal_norm :
  forall ux uy vx vy : R,
    ~ (ux = 0 /\ uy = 0) ->
    ~ (vx = 0 /\ vy = 0) ->
    ux * ux + uy * uy = vx * vx + vy * vy ->
    (ux - vx) * (ux - vx) + (uy - vy) * (uy - vy)
    = 2 * (ux * ux + uy * uy) * (1 - cos (angle_between ux uy vx vy)).
Proof.
  intros ux uy vx vy Hu Hv Heq.
  pose proof (sum_sq_pos ux uy Hu) as Hu'.
  rewrite cos_angle_between by assumption.
  rewrite <- Heq.
  rewrite sqrt_sqrt by lra.
  replace (2 * (ux * ux + uy * uy)
           * (1 - (ux * vx + uy * vy) / (ux * ux + uy * uy)))
    with (2 * (ux * ux + uy * uy) - 2 * (ux * vx + uy * vy)) by (field; lra).
  replace ((ux - vx) * (ux - vx) + (uy - vy) * (uy - vy))
    with ((ux * ux + uy * uy) + (vx * vx + vy * vy) - 2 * (ux * vx + uy * vy))
    by ring.
  rewrite <- Heq. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Arc chord² via the central sweep angle.                                *)
(* -------------------------------------------------------------------------- *)

Theorem arc_chord_dist_sq_via_sweep :
  forall a : CircularArc,
    valid_arc a ->
    dist_sq (arc_start a) (arc_end a)
    = 2 * dist_sq (arc_center a) (arc_start a)
        * (1 - cos (arc_sweep_angle a)).
Proof.
  intros a Hva.
  destruct (arc_center_vectors_nonzero a Hva) as [Hu Hv].
  destruct (arc_center_equidistant a Hva) as [_ Hse].
  (* center-to-endpoint squared norms, in raw-coordinate form *)
  assert (HL : (px (arc_start a) - px (arc_center a)) * (px (arc_start a) - px (arc_center a))
             + (py (arc_start a) - py (arc_center a)) * (py (arc_start a) - py (arc_center a))
             = dist_sq (arc_center a) (arc_start a))
    by (unfold dist_sq; ring).
  assert (HRr : (px (arc_end a) - px (arc_center a)) * (px (arc_end a) - px (arc_center a))
              + (py (arc_end a) - py (arc_center a)) * (py (arc_end a) - py (arc_center a))
              = dist_sq (arc_center a) (arc_end a))
    by (unfold dist_sq; ring).
  assert (Heq : (px (arc_start a) - px (arc_center a)) * (px (arc_start a) - px (arc_center a))
              + (py (arc_start a) - py (arc_center a)) * (py (arc_start a) - py (arc_center a))
              = (px (arc_end a) - px (arc_center a)) * (px (arc_end a) - px (arc_center a))
              + (py (arc_end a) - py (arc_center a)) * (py (arc_end a) - py (arc_center a))).
  { rewrite HL, HRr. exact Hse. }
  pose proof (law_of_cosines_equal_norm
                (px (arc_start a) - px (arc_center a))
                (py (arc_start a) - py (arc_center a))
                (px (arc_end a) - px (arc_center a))
                (py (arc_end a) - py (arc_center a))
                Hu Hv Heq) as Hlc.
  unfold arc_sweep_angle. cbv zeta.
  rewrite <- HL.
  rewrite <- Hlc.
  unfold dist_sq. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions law_of_cosines_equal_norm.
Print Assumptions arc_chord_dist_sq_via_sweep.

Theorem arc_chord_le_arc_length :
  forall a : CircularArc,
    valid_arc a ->
    dist (arc_start a) (arc_end a) <= arc_length (arc_radius a) (Rabs (arc_sweep_angle a)).
Proof.
  intros a Hva.
  pose proof (arc_chord_dist_sq_via_sweep a Hva) as Hsq.
  pose proof (chord_subtended_sq (arc_radius a) (Rabs (arc_sweep_angle a))) as Hcs.
  assert (Hr : 0 <= arc_radius a) by apply arc_radius_nonneg.
  assert (Ht : 0 <= Rabs (arc_sweep_angle a)) by apply Rabs_pos.
  pose proof (chord_le_arc_length (arc_radius a) (Rabs (arc_sweep_angle a)) Hr Ht) as Hcle.
  pose proof (arc_sweep_principal_range a Hva) as Hrange.
  (* ds(start, end) = chord_subtended(r, |theta|)^2 via sq-identity + cos even + r^2 *)
  assert (Hds_eq_csq :
    dist_sq (arc_start a) (arc_end a) =
    chord_subtended (arc_radius a) (Rabs (arc_sweep_angle a)) *
    chord_subtended (arc_radius a) (Rabs (arc_sweep_angle a))).
  { rewrite Hsq.
    assert (Hcos : cos (arc_sweep_angle a) = cos (Rabs (arc_sweep_angle a))).
    { destruct (Rlt_dec (arc_sweep_angle a) 0) as [Hlt | Hge].
      - rewrite (Rabs_left (arc_sweep_angle a) Hlt).
        rewrite cos_neg.
        reflexivity.
      - rewrite (Rabs_right (arc_sweep_angle a) (Rnot_lt_ge (arc_sweep_angle a) 0 Hge)).
        reflexivity.
    }
    rewrite Hcos.
    assert (Hrc2 : dist_sq (arc_center a) (arc_start a) = arc_radius a * arc_radius a).
    { rewrite (arc_radius_eq_sqrt a).
      rewrite sqrt_sqrt by apply arc_radius_sq_nonneg.
      unfold arc_radius_sq.
      reflexivity.
    }
    rewrite Hrc2.
    rewrite <- Hcs.
    reflexivity.
  }
  (* chord_subtended(r, |theta|) >= 0 (r>=0 and sin(|theta|/2)>=0 for |theta|<=PI) *)
  assert (Hcpos : 0 <= chord_subtended (arc_radius a) (Rabs (arc_sweep_angle a))).
  { unfold chord_subtended.
    assert (Hsin : 0 <= sin (Rabs (arc_sweep_angle a) / 2)).
    { apply sin_ge_0.
      + apply Rmult_le_pos; [apply Rabs_pos | lra].
      + destruct Hrange as [Hgt Hle].
        apply Rle_trans with (PI / 2); [| lra].
        apply Rmult_le_compat_r; [lra | ].
        apply Rabs_le; split; [apply Rlt_le; exact Hgt | exact Hle].
    }
    nra.
  }
  unfold dist.
  (* dist = sqrt(ds) = sqrt(c * c) = c (via Rsqr), then chord_le gives <= arcL *)
  rewrite Hds_eq_csq.
  replace (chord_subtended (arc_radius a) (Rabs (arc_sweep_angle a)) *
           chord_subtended (arc_radius a) (Rabs (arc_sweep_angle a)))
    with (Rsqr (chord_subtended (arc_radius a) (Rabs (arc_sweep_angle a))))
    by (unfold Rsqr; ring).
  rewrite sqrt_Rsqr by exact Hcpos.
  exact Hcle.
Qed.

Print Assumptions arc_chord_le_arc_length.


(* Note: this re-uses the scalar chord_le_arc_length and the sq identity.
   The |sweep| ensures the length is non-negative independent of orientation. *)
