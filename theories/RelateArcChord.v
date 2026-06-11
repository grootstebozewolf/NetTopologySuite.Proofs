(* ============================================================================
   NetTopologySuite.Proofs.RelateArcChord
   ----------------------------------------------------------------------------
   Issue #67 session 10 (S10): arc×line — chord geometry + witnesses (3-ax).

   First curve-aware relate slice for issue #67.  Under Option B the arc is
   treated via its chord (`arc_start`–`arc_end`) for line-line regimes, plus
   an arc-native `chord_crosses_arc_circle` regime linked to `ArcIntersectIVT`.

   Two honest layers (no geometry→matrix bridge — see the section comment):
     - Witness: the reused S2 `ll_matrix_*` matrices (as `ac_matrix_*`) satisfy
       their DE-9IM predicates (constant facts).
     - Geometry: the genuine consequence of each chord regime — a shared point
       (proper cross), its absence (rejection), or a circumcircle hit (IVT).

   Honest scoping: subtended angle < π for `arc_span_contains` (Option S);
   promoting circle-cross to full arc-span membership remains quarantined.
   Option-A analytic fill (`Atan2` / `AngleBetween`) is `RelateArcAnalytic.v` /
   `RelateMatrixArcAnalytic.v` (S10b).  Regime→witness selection via
   `RelateMatrixArcChord.v`.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance Segment Intersect CurveGeometry
  ArcOrient ArcIntersect ArcIntersectIVT RelateLineLine.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Chord-as-segment regime predicates.                                        *)
(* -------------------------------------------------------------------------- *)

Definition arc_chord_proper_cross (a : CircularArc) (P Q : Point) : Prop :=
  segments_proper_cross (arc_start a) (arc_end a) P Q.

Definition arc_chord_rejected (a : CircularArc) (P Q : Point) : Prop :=
  segments_rejected (arc_start a) (arc_end a) P Q.

Definition arc_chord_share (a : CircularArc) (P Q : Point) : Prop :=
  segments_share (arc_start a) (arc_end a) P Q.

(* -------------------------------------------------------------------------- *)
(* Canonical witness matrices (S2 reuse).                                     *)
(* -------------------------------------------------------------------------- *)

Definition ac_matrix_disjoint : IntersectionMatrix := ll_matrix_disjoint.
Definition ac_matrix_point_ii : IntersectionMatrix := ll_matrix_point_ii.

Lemma ac_matrix_disjoint_witness :
  im_disjoint ac_matrix_disjoint.
Proof.
  unfold ac_matrix_disjoint. exact ll_matrix_disjoint_witness.
Qed.

Lemma ac_matrix_point_ii_intersects :
  im_intersects ac_matrix_point_ii.
Proof.
  unfold ac_matrix_point_ii. exact ll_matrix_point_ii_intersects.
Qed.

Lemma ac_matrix_point_ii_crosses :
  im_crosses ac_matrix_point_ii.
Proof.
  unfold ac_matrix_point_ii. exact ll_matrix_point_ii_crosses_ll.
Qed.

(* -------------------------------------------------------------------------- *)
(* Genuine chord geometry (S2 delegation).                                    *)
(*                                                                            *)
(* The constant `ac_matrix_*` lemmas above prove the reused witness matrices   *)
(* satisfy their predicates.  The lemmas here prove the genuine geometric      *)
(* consequence of each chord regime (a shared point, its absence, or a circle  *)
(* hit).  They are NOT bridged to the witnesses: which matrix the arc×line     *)
(* configuration's true DE-9IM equals is the deferred RelateNG step.          *)
(* -------------------------------------------------------------------------- *)

Theorem arc_chord_proper_cross_share :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_proper_cross a P Q ->
    arc_chord_share a P Q.
Proof.
  intros a P Q H.
  unfold arc_chord_proper_cross, arc_chord_share in *.
  eapply line_line_proper_cross_geom; exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Arc-native circle-cross regime (IVT).                                      *)
(* -------------------------------------------------------------------------- *)

Theorem arc_circle_chord_cross_on_circle :
  forall (a : CircularArc) (P Q : Point),
    chord_crosses_arc_circle a P Q ->
    exists X : Point,
      between P Q X /\
      inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0.
Proof.
  intros a P Q H.
  exact (chord_crosses_arc_circle_implies_circle_intersection a P Q H).
Qed.

Lemma arc_chord_proper_cross_not_rejected :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_proper_cross a P Q ->
    ~ arc_chord_rejected a P Q.
Proof.
  intros a P Q [Hab Hcd] Hrej.
  unfold arc_chord_rejected, segments_rejected in Hrej.
  unfold arc_chord_proper_cross, segments_proper_cross in *.
  destruct Hrej as [Habpos | Hcdpos]; lra.
Qed.

Lemma arc_chord_rejected_not_share :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_rejected a P Q ->
    ~ arc_chord_share a P Q.
Proof.
  intros a P Q Hrej Hshare.
  unfold arc_chord_rejected, arc_chord_share in *.
  exact (line_line_rejected_not_share (arc_start a) (arc_end a) P Q Hrej Hshare).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_chord_proper_cross_share.
Print Assumptions arc_chord_rejected_not_share.
Print Assumptions arc_circle_chord_cross_on_circle.
Print Assumptions ac_matrix_point_ii_intersects.