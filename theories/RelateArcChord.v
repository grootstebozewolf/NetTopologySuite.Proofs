(* ============================================================================
   NetTopologySuite.Proofs.RelateArcChord
   ----------------------------------------------------------------------------
   Issue #67 session 10 (S10): arc×line DE-9IM soundness — chord path (3-ax).

   First curve-aware relate slice for issue #67.  Under Option B the arc is
   treated via its chord (`arc_start`–`arc_end`) for line-line regimes, plus
   an arc-native `chord_crosses_arc_circle` regime linked to `ArcIntersectIVT`.

   Delivers canonical witness matrices (reusing S2 `ll_matrix_*` footprints)
   and regime soundness:

     - chord-as-segment proper cross / rejection / share (delegates to S2)
     - external chord `PQ` crosses arc circumcircle (IVT existence)
     - `arc_chord_intersects` witness-level `Intersects` (span+circle hit)

   Honest scoping: subtended angle < π for `arc_span_contains` (Option S);
   promoting circle-cross to full arc-span soundness remains quarantined
   (`arc_chord_intersect_sound` gap).  Option-A analytic fill (`Atan2` /
   `AngleBetween`) is `RelateArcAnalytic.v` / `RelateMatrixArcAnalytic.v` (S10b).
   Matrix fill via `RelateMatrixArcChord.v`.

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
(* Chord-as-segment soundness (S2 delegation).                                *)
(* -------------------------------------------------------------------------- *)

Theorem arc_chord_proper_cross_sound :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_proper_cross a P Q ->
    im_crosses ac_matrix_point_ii /\
    im_intersects ac_matrix_point_ii.
Proof.
  intros a P Q H.
  unfold arc_chord_proper_cross in H.
  unfold ac_matrix_point_ii.
  exact (line_line_proper_cross_sound (arc_start a) (arc_end a) P Q H).
Qed.

Theorem arc_chord_rejected_disjoint_sound :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_rejected a P Q ->
    im_disjoint ac_matrix_disjoint.
Proof.
  intros a P Q H.
  unfold arc_chord_rejected in H.
  unfold ac_matrix_disjoint.
  destruct (line_line_rejection_disjoint_sound (arc_start a) (arc_end a) P Q H) as [Hdisj _].
  exact Hdisj.
Qed.

Theorem arc_chord_share_intersects_sound :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_share a P Q ->
    im_intersects ac_matrix_point_ii.
Proof.
  intros a P Q H.
  unfold arc_chord_share in H.
  unfold ac_matrix_point_ii.
  exact (line_line_share_intersects_sound (arc_start a) (arc_end a) P Q H).
Qed.

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

Theorem arc_circle_chord_cross_intersects_sound :
  forall (a : CircularArc) (P Q : Point),
    chord_crosses_arc_circle a P Q ->
    im_intersects ac_matrix_point_ii.
Proof.
  intros. exact ac_matrix_point_ii_intersects.
Qed.

Theorem arc_chord_intersects_witness :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_intersects a P Q ->
    im_intersects ac_matrix_point_ii.
Proof.
  intros. exact ac_matrix_point_ii_intersects.
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
  destruct (line_line_rejection_disjoint_sound (arc_start a) (arc_end a) P Q Hrej) as [_ Hnoshare].
  exact (Hnoshare Hshare).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_chord_proper_cross_sound.
Print Assumptions arc_chord_rejected_disjoint_sound.
Print Assumptions arc_chord_share_intersects_sound.
Print Assumptions arc_circle_chord_cross_on_circle.
Print Assumptions arc_circle_chord_cross_intersects_sound.