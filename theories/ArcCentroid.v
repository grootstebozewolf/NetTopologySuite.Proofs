(* ============================================================================
   NetTopologySuite.Proofs.ArcCentroid
   ----------------------------------------------------------------------------
   Option-A arc primitives (issue #64 / #69 C-LIN): the centre of mass of a
   circular arc — the proof-side foundation for the oracle's missing
   `ARC_CENTROID` mode and for verifying `CircularString.getCentroid()`.

   A circular arc of radius `r` and sweep `theta` has its centroid on the
   bisector, at distance

       arc_centroid_offset r theta := 2 * r * sin (theta / 2) / theta
                                    = chord_subtended r theta / theta

   from the centre (the classic `r·sin(θ/2)/(θ/2)` first-moment / arc-length
   formula).  This file states that scalar offset and proves the load-bearing
   algebraic facts the C-LIN centroid test and the oracle's float boundary need:

     - `arc_centroid_offset_semicircle`  : at `theta = PI`,  offset = `2r/PI`
       (the semicircle → 2R/π case the C-LIN suite checks);
     - `arc_centroid_offset_full_turn`   : at `theta = 2*PI`, offset = `0`
       (a full circle's centroid is its centre);
     - `arc_centroid_offset_nonneg`      : `0 ≤ offset` for `0 ≤ theta ≤ 2*PI`;
     - `arc_centroid_offset_le_radius`   : `offset ≤ r` for `theta > 0`
       (the centroid lies inside the disc — via `ArcLength.chord_le_arc_length`).

   Stated over `(r, theta)` abstractly (no `atan2`), so only `chord_le_arc_length`
   crosses into the `sin_lt_x`/`classic` lane — the file is 4-axiom, same lineage
   as `ArcLength.v` (`docs/audit-exceptions.txt`).  No `Admitted`/`Axiom`/`Parameter`.
   The Point-valued centroid of a `CircularArc` (bisector direction via
   `arc_sweep_angle`) is the natural follow-up.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

Require Import Reals.
Require Import Lra.
From NTS.Proofs Require Import ArcLength.
Local Open Scope R_scope.

(* The centroid's signed distance from the centre along the arc bisector. *)
Definition arc_centroid_offset (r theta : R) : R :=
  2 * r * sin (theta / 2) / theta.

(* Definitional identity: offset = chord / sweep-angle. *)
Lemma arc_centroid_offset_eq_chord_over_angle :
  forall r theta, arc_centroid_offset r theta = chord_subtended r theta / theta.
Proof. reflexivity. Qed.

(* Semicircle (theta = PI): the centroid is 2r/PI from the centre. *)
Lemma arc_centroid_offset_semicircle :
  forall r, arc_centroid_offset r PI = 2 * r / PI.
Proof.
  intros r. unfold arc_centroid_offset. rewrite sin_PI2, Rmult_1_r. reflexivity.
Qed.

(* Full turn (theta = 2*PI): the centroid coincides with the centre. *)
Lemma arc_centroid_offset_full_turn :
  forall r, arc_centroid_offset r (2 * PI) = 0.
Proof.
  intros r. unfold arc_centroid_offset.
  replace (2 * PI / 2) with PI by lra.
  rewrite sin_PI. unfold Rdiv. rewrite Rmult_0_r. apply Rmult_0_l.
Qed.

(* The offset is nonnegative for a forward sweep up to a full turn. *)
Lemma arc_centroid_offset_nonneg :
  forall r theta, 0 <= r -> 0 <= theta <= 2 * PI ->
    0 <= arc_centroid_offset r theta.
Proof.
  intros r theta Hr [Ht0 Ht2]. unfold arc_centroid_offset.
  destruct (Req_dec theta 0) as [E | E].
  - subst. replace (0 / 2) with 0 by lra. rewrite sin_0.
    rewrite Rmult_0_r. unfold Rdiv. rewrite Rmult_0_l. apply Rle_refl.
  - assert (Hpos : 0 < theta) by lra.
    assert (Hsin : 0 <= sin (theta / 2)) by (apply sin_ge_0; lra).
    assert (HX : 0 <= 2 * r * sin (theta / 2))
      by (apply Rmult_le_pos; [ lra | exact Hsin ]).
    unfold Rdiv. apply Rmult_le_pos; [ exact HX | ].
    apply Rlt_le, Rinv_0_lt_compat, Hpos.
Qed.

(* The centroid lies inside the disc: offset <= r (theta > 0).
   Reuses ArcLength.chord_le_arc_length (chord <= arc): 2r·sin(θ/2) <= rθ. *)
Lemma arc_centroid_offset_le_radius :
  forall r theta, 0 <= r -> 0 < theta -> arc_centroid_offset r theta <= r.
Proof.
  intros r theta Hr Ht. unfold arc_centroid_offset.
  apply Rmult_le_reg_r with (r := theta); [ exact Ht | ].
  replace (2 * r * sin (theta / 2) / theta * theta)
    with (2 * r * sin (theta / 2)) by (field; lra).
  pose proof (chord_le_arc_length r theta Hr (Rlt_le _ _ Ht)) as Hc.
  unfold chord_subtended, arc_length in Hc. exact Hc.
Qed.

Print Assumptions arc_centroid_offset_semicircle.
Print Assumptions arc_centroid_offset_full_turn.
Print Assumptions arc_centroid_offset_nonneg.
Print Assumptions arc_centroid_offset_le_radius.
