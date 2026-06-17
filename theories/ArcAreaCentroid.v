(* ============================================================================
   NetTopologySuite.Proofs.ArcAreaCentroid
   ----------------------------------------------------------------------------
   Option-A arc primitives (issue #64 / #69 C-AREA): the centre of mass of a
   circular SEGMENT (the 2-D region between an arc and its chord) — the
   proof-side foundation for the oracle's missing `ARC_AREA_CENTROID` mode.
   Companion to `ArcCentroid.v` (which handles the 1-D arc curve).

   A circular segment of radius `r` and sweep `theta` has its centroid on the
   bisector, at distance

       segment_centroid_offset r theta := 4 * r * (sin (theta/2))^3
                                          / (3 * (theta - sin theta))

   from the centre (the classic segment first-moment / area formula; the
   denominator `theta - sin theta` is twice the segment area over r^2).

   Headlines (mirroring `ArcCentroid.v`):
     - `segment_area_factor_pos`         : `0 < theta -> 0 < theta - sin theta`
       (the segment-area / division-safety guard — the oracle's denominator);
     - `segment_centroid_offset_semicircle` : at `theta = PI`,  offset = `4r/(3·PI)`
       (the half-disc centroid, the C-AREA semicircle case);
     - `segment_centroid_offset_full_turn`  : at `theta = 2*PI`, offset = `0`;
     - `segment_centroid_offset_nonneg`      : `0 <= offset` for `0 <= theta <= 2*PI`.

   Stated over `(r, theta)` abstractly (no `atan2`).  `segment_area_factor_pos`
   and the nonneg headline use Stdlib `sin_lt_x` (-> `Classical_Prop.classic`),
   so the file is 4-axiom, same lineage as `ArcLength.v` / `ArcCentroid.v`
   (`docs/audit-exceptions.txt`).  No `Admitted`/`Axiom`/`Parameter`.

   The `offset <= r` bound (`4 sin^3(theta/2) <= 3(theta - sin theta)`) is a
   genuinely harder trig inequality (needs monotonicity, not a chord<=arc reuse);
   it is left as the next step, like the Point-valued centroid.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

Require Import Reals.
Require Import Lra.
Local Open Scope R_scope.

(* The circular-segment centroid's signed distance from the centre along the
   bisector. *)
Definition segment_centroid_offset (r theta : R) : R :=
  4 * r * (sin (theta / 2) * sin (theta / 2) * sin (theta / 2))
  / (3 * (theta - sin theta)).

(* The segment-area / division-safety guard: theta - sin theta > 0 for a forward
   sweep.  This is (twice) the circular-segment area over r^2, and the oracle's
   denominator. *)
Lemma segment_area_factor_pos :
  forall theta, 0 < theta -> 0 < theta - sin theta.
Proof.
  intros theta Ht. pose proof (sin_lt_x theta Ht) as H. lra.
Qed.

(* Semicircle (theta = PI): the half-disc centroid is 4r/(3·PI) from the centre. *)
Lemma segment_centroid_offset_semicircle :
  forall r, segment_centroid_offset r PI = 4 * r / (3 * PI).
Proof.
  intros r. unfold segment_centroid_offset.
  rewrite sin_PI2, sin_PI.
  replace (PI - 0) with PI by lra.
  replace (1 * 1 * 1) with 1 by ring.
  rewrite Rmult_1_r. reflexivity.
Qed.

(* Full turn (theta = 2*PI): the centroid coincides with the centre. *)
Lemma segment_centroid_offset_full_turn :
  forall r, segment_centroid_offset r (2 * PI) = 0.
Proof.
  intros r. unfold segment_centroid_offset.
  replace (2 * PI / 2) with PI by lra.
  rewrite sin_PI.
  replace (4 * r * (0 * 0 * 0)) with 0 by ring.
  unfold Rdiv. rewrite Rmult_0_l. reflexivity.
Qed.

(* The offset is nonnegative for a forward sweep up to a full turn. *)
Lemma segment_centroid_offset_nonneg :
  forall r theta, 0 <= r -> 0 <= theta <= 2 * PI ->
    0 <= segment_centroid_offset r theta.
Proof.
  intros r theta Hr [Ht0 Ht2]. unfold segment_centroid_offset.
  destruct (Req_dec theta 0) as [E | E].
  - subst. replace (0 / 2) with 0 by lra. rewrite sin_0.
    replace (4 * r * (0 * 0 * 0)) with 0 by ring.
    unfold Rdiv. rewrite Rmult_0_l. apply Rle_refl.
  - assert (Hpos : 0 < theta) by lra.
    assert (Hsin : 0 <= sin (theta / 2)) by (apply sin_ge_0; lra).
    assert (Hcube : 0 <= sin (theta / 2) * sin (theta / 2) * sin (theta / 2))
      by (apply Rmult_le_pos; [ apply Rmult_le_pos; assumption | exact Hsin ]).
    assert (Hnum : 0 <= 4 * r * (sin (theta / 2) * sin (theta / 2) * sin (theta / 2)))
      by (apply Rmult_le_pos; [ lra | exact Hcube ]).
    assert (Hden : 0 < 3 * (theta - sin theta))
      by (pose proof (segment_area_factor_pos theta Hpos); lra).
    unfold Rdiv. apply Rmult_le_pos; [ exact Hnum | ].
    apply Rlt_le, Rinv_0_lt_compat, Hden.
Qed.

Print Assumptions segment_area_factor_pos.
Print Assumptions segment_centroid_offset_semicircle.
Print Assumptions segment_centroid_offset_full_turn.
Print Assumptions segment_centroid_offset_nonneg.
