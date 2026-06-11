(* ============================================================================
   NetTopologySuite.Proofs.RelateArcAnalytic
   ----------------------------------------------------------------------------
   Issue #67 session 10b (S10b): arc×line DE-9IM — Option-A analytic path (4-ax).

   Links `CircularArc` central sweep to `AngleBetween.angle_between` and
   `ArcLength.chord_le_arc_length`, then reuses S10 chord-path DE-9IM witnesses
   under strengthened analytic guards (`valid_arc` + principal sweep range).

   Delivers:

     - `arc_sweep_angle` from center-to-start / center-to-end vectors
     - Analytic-guarded proper-cross soundness (delegates to `RelateArcChord`)

   Chord–arc length bridge (`chord_subtended` at `arc_sweep_angle`) is deferred:
   the law-of-cosines step needs a `pose`/`set` transparency seam on vector
   names; reuse `ArcLength.chord_le_arc_length` once that lemma is closed.

   Honest scoping: minor-arc disambiguation via mid-point is not promoted to a
   full arc-span soundness theorem; `arc_chord_intersect_sound` gap remains.
   Matrix fill via `RelateMatrixArcAnalytic.v`.  Clothoid slice is
   `RelateClothoid.v`.

   Inherits `Classical_Prop.classic` via `Atan2` / `AngleBetween` (4-axiom lane).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance CurveGeometry ArcChordApprox
  AngleBetween RelateArcChord.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Central sweep angle (Option-A).                                            *)
(* -------------------------------------------------------------------------- *)

Definition arc_sweep_angle (a : CircularArc) : R :=
  let c := arc_center a in
  angle_between
    (px (arc_start a) - px c) (py (arc_start a) - py c)
    (px (arc_end a) - px c) (py (arc_end a) - py c).

Definition arc_analytic_minor_guard (a : CircularArc) : Prop :=
  valid_arc a /\ 0 < arc_sweep_angle a /\ arc_sweep_angle a <= PI.

Definition arc_analytic_proper_cross (a : CircularArc) (P Q : Point) : Prop :=
  arc_analytic_minor_guard a /\ arc_chord_proper_cross a P Q.

(* -------------------------------------------------------------------------- *)
(* Vector nonzeroness + principal range.                                      *)
(* -------------------------------------------------------------------------- *)

Lemma arc_start_center_dist_sq_pos :
  forall (a : CircularArc),
    valid_arc a ->
    0 < dist_sq (arc_start a) (arc_center a).
Proof.
  intros a Hva.
  destruct (Rlt_dec 0 (dist_sq (arc_start a) (arc_center a))) as [Hpos|Hnot].
  - exact Hpos.
  - apply Rnot_lt_le in Hnot.
    pose proof (dist_sq_nonneg (arc_start a) (arc_center a)) as Hnn.
    assert (Hds0 : dist_sq (arc_start a) (arc_center a) = 0) by lra.
    destruct (dist_sq_zero_iff_eq (arc_start a) (arc_center a)) as [Hcoord Hds0'].
    destruct (Hcoord Hds0) as [Hx Hy].
    destruct (arc_center_equidistant a Hva) as [Hsm _].
    rewrite dist_sq_sym in Hsm.
    rewrite Hds0 in Hsm.
    assert (Hmid0 : dist_sq (arc_mid a) (arc_center a) = 0).
    { rewrite dist_sq_sym. symmetry. exact Hsm. }
    apply dist_sq_zero_iff_eq in Hmid0.
    destruct Hmid0 as [Hmx Hmy].
    unfold valid_arc in Hva.
    rewrite Hx, Hy, Hmx, Hmy in Hva.
    simpl in Hva. nra.
Qed.

Lemma arc_center_vectors_nonzero :
  forall (a : CircularArc),
    valid_arc a ->
    ~ (px (arc_start a) - px (arc_center a) = 0 /\
       py (arc_start a) - py (arc_center a) = 0) /\
    ~ (px (arc_end a) - px (arc_center a) = 0 /\
       py (arc_end a) - py (arc_center a) = 0).
Proof.
  intros a Hva.
  pose proof (arc_start_center_dist_sq_pos a Hva) as Hstart.
  destruct (arc_center_equidistant a Hva) as [_ Hse].
  split; intro Hzero; destruct Hzero as [Hx Hy].
  - assert (Hsum :
      (px (arc_start a) - px (arc_center a)) *
      (px (arc_start a) - px (arc_center a)) +
      (py (arc_start a) - py (arc_center a)) *
      (py (arc_start a) - py (arc_center a)) = 0).
    { rewrite Hx, Hy. ring. }
    unfold dist_sq in Hstart.
    lra.
  - assert (Hsum :
      (px (arc_end a) - px (arc_center a)) *
      (px (arc_end a) - px (arc_center a)) +
      (py (arc_end a) - py (arc_center a)) *
      (py (arc_end a) - py (arc_center a)) = 0).
    { rewrite Hx, Hy. ring. }
    rewrite dist_sq_sym in Hse.
    unfold dist_sq in Hstart, Hse.
    lra.
Qed.

Lemma arc_sweep_principal_range :
  forall (a : CircularArc),
    valid_arc a ->
    - PI < arc_sweep_angle a <= PI.
Proof.
  intros a Hva.
  unfold arc_sweep_angle.
  destruct (arc_center_vectors_nonzero a Hva) as [Hu Hv].
  apply angle_between_range; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Analytic-guarded DE-9IM soundness (S10 delegate).                          *)
(* -------------------------------------------------------------------------- *)

Theorem arc_analytic_proper_cross_sound :
  forall (a : CircularArc) (P Q : Point),
    arc_analytic_proper_cross a P Q ->
    im_crosses ac_matrix_point_ii /\
    im_intersects ac_matrix_point_ii.
Proof.
  intros a P Q [ _ Hcross].
  exact (arc_chord_proper_cross_sound a P Q Hcross).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_sweep_principal_range.
Print Assumptions arc_analytic_proper_cross_sound.