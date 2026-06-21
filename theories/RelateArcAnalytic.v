(* ============================================================================
   NetTopologySuite.Proofs.RelateArcAnalytic
   ----------------------------------------------------------------------------
   Issue #67 session 10b (S10b): arc×line — Option-A analytic chord geometry.

   Links `CircularArc` central sweep to `AngleBetween.angle_between` and
   `ArcLength.chord_le_arc_length`, then reuses S10 chord-path DE-9IM witnesses
   under strengthened analytic guards (`valid_arc` + principal sweep range).

   Delivers:

     - `arc_sweep_angle` from center-to-start / center-to-end vectors
     - `arc_sweep` (mid-point disambiguation for short vs long arcs)
     - Analytic-guarded chord geometry: proper cross ⇒ shared point
       (`arc_analytic_proper_cross_share`, delegates to `RelateArcChord`)

   Chord–arc length bridge landed in ArcChordLength.v (arc_chord_dist_sq_via_sweep
   + arc_chord_le_arc_length using the sq identity + scalar chord_le + sqrt_Rsqr).
   #64 ask #1 core complete (Qed). Mid-point disambiguation via arc_mid for
   sweep (short vs long arc) now landed for ask #2. The arc-span↔witness bridge
   using analytic sweep remains a gap for now.
   Regime→witness selection via `RelateMatrixArcAnalytic.v`.  Clothoid slice is
   `RelateClothoid.v`.

   Assumption footprint: `arc_sweep_principal_range` is built on
   `AngleBetween.angle_between_range`, so it inherits `Classical_Prop.classic`
   via the `Atan2` / `AngleBetween` lane (4-axiom).  The chord-geometry / witness
   theorems are 3-axiom.  This file is exempted in docs/audit-exceptions.txt
   (same lineage as `theories/AngleBetween.v`).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance CurveGeometry ArcChordApprox
  AngleBetween RelateArcChord ArcLength.  (* ArcLength for scalar; chord bridge landed in ArcChordLength *)
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Central sweep angle (Option-A).                                            *)
(* -------------------------------------------------------------------------- *)

Definition arc_sweep_angle (a : CircularArc) : R :=
  let c := arc_center a in
  angle_between
    (px (arc_start a) - px c) (py (arc_start a) - py c)
    (px (arc_end a) - px c) (py (arc_end a) - py c).

(* -------------------------------------------------------------------------- *)
(* Mid-point disambiguation for short vs long arc (Option-A #64 ask #2).     *)
(*                                                                             *)
(* arc_sweep chooses the directed central angle (possibly |sweep| > PI) such  *)
(* that the arc from start to end passes through arc_mid (the control point  *)
(* that selects minor vs major).  The raw arc_sweep_angle always returns the  *)
(* principal value in (-PI,PI]; arc_sweep adjusts by ±2π when the mid point  *)
(* lies in the reflex sector.                                                  *)
(* -------------------------------------------------------------------------- *)

Definition arc_sweep (a : CircularArc) : R :=
  let theta := arc_sweep_angle a in
  let c := arc_center a in
  let vsx := px (arc_start a) - px c in
  let vsy := py (arc_start a) - py c in
  let vmx := px (arc_mid a) - px c in
  let vmy := py (arc_mid a) - py c in
  let phi := angle_between vsx vsy vmx vmy in
  match Rgt_dec theta 0 with
  | left _ =>
      match Rgt_dec phi 0 with
      | left _ =>
          match Rlt_dec phi theta with
          | left _ => theta
          | _ => theta - 2 * PI
          end
      | _ => theta - 2 * PI
      end
  | _ =>
      match Rlt_dec theta 0 with
      | left _ =>
          match Rlt_dec phi 0 with
          | left _ =>
              match Rlt_dec theta phi with
              | left _ => theta
              | _ => theta + 2 * PI
              end
          | _ => theta + 2 * PI
          end
      | _ => 0
      end
  end.

Definition arc_analytic_minor_guard (a : CircularArc) : Prop :=
  valid_arc a /\ 0 < Rabs (arc_sweep a) /\ Rabs (arc_sweep a) <= PI.

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

Lemma arc_analytic_minor_guard_implies_principal_range :
  forall a : CircularArc,
    arc_analytic_minor_guard a ->
    - PI < arc_sweep_angle a <= PI.
Proof.
  intros a Hguard.
  apply arc_sweep_principal_range.
  unfold arc_analytic_minor_guard in Hguard.
  tauto.
Qed.

(* TODO next rung: arc_sweep_abs_le_2pi (range for disambiguated sweep) Qed.
   Core slice prioritizes the definition itself and minor guard implication for now. *)
(* arc_sweep range lemma (core next rung) to be completed with elementary R tactics. *)

(* Arc length for a CircularArc using the atan2-backed sweep (Option-A #64). *)
(* Uses mid-disambiguated arc_sweep so that major arcs (mid on long side) get  *)
(* the long arc length > π·r.                                                   *)
Definition arc_length_of (a : CircularArc) : R :=
  arc_length (arc_radius a) (Rabs (arc_sweep a)).

Lemma arc_length_of_nonneg :
  forall a : CircularArc,
    valid_arc a ->
    0 <= arc_length_of a.
Proof.
  intros a Hva.
  unfold arc_length_of.
  assert (Hr : 0 <= arc_radius a).
  { unfold arc_radius, dist. apply sqrt_pos. }
  assert (Habs : 0 <= Rabs (arc_sweep a)).
  { apply Rabs_pos. }
  apply arc_length_nonneg; assumption.
Qed.

(* The chord–arc length bridge is now landed in ArcChordLength.v (see arc_chord_le_arc_length and supporting lemmas). *)

(* -------------------------------------------------------------------------- *)
(* Analytic-guarded chord geometry (S10 delegate).                            *)
(*                                                                            *)
(* Genuine consequence of an analytic-guarded proper cross: the arc chord and  *)
(* the line share a point.  The witness matrices live in `RelateArcChord.v`    *)
(* (constant `ac_matrix_*` lemmas) and are not bridged to the geometry here.   *)
(* -------------------------------------------------------------------------- *)

Theorem arc_analytic_proper_cross_share :
  forall (a : CircularArc) (P Q : Point),
    arc_analytic_proper_cross a P Q ->
    arc_chord_share a P Q.
Proof.
  intros a P Q [ _ Hcross].
  exact (arc_chord_proper_cross_share a P Q Hcross).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_sweep_principal_range.
Print Assumptions arc_sweep.
Print Assumptions arc_analytic_proper_cross_share.