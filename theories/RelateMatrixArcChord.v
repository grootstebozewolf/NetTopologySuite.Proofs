(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixArcChord
   ----------------------------------------------------------------------------
   Issue #67 session 10 (S10): arc×line matrix fill — chord path (3-ax).

   Fourth computed DE-9IM matrix-fill API in the Relate arc (first curve-aware
   fill): regime-indexed `arc_chord_fill` whose outputs equal the S10 witness
   matrices from `RelateArcChord.v`.

   Delivers:

     - `ArcChordRegime` + `arc_chord_fill`
     - `classify_arc_chord` linking regimes to S10 geometry guards
     - Fill = witness equalities
     - Compute-path soundness (rewrite to S10 predicate lemmas)
     - Mutual-exclusion lemmas for chord rejection vs proper cross / share

   Honest scoping: chord path only; Option-A analytic regimes are S10b+.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance CurveGeometry ArcIntersect
  RelateArcChord.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Regime enum + matrix fill.                                                 *)
(* -------------------------------------------------------------------------- *)

Inductive ArcChordRegime : Type :=
| ACR_ChordDisjoint
| ACR_ChordProperCross
| ACR_ChordShare
| ACR_CircleCross.

Definition arc_chord_fill (r : ArcChordRegime) : IntersectionMatrix :=
  match r with
  | ACR_ChordDisjoint     => ac_matrix_disjoint
  | ACR_ChordProperCross  => ac_matrix_point_ii
  | ACR_ChordShare        => ac_matrix_point_ii
  | ACR_CircleCross       => ac_matrix_point_ii
  end.

Lemma arc_chord_fill_disjoint_eq :
  arc_chord_fill ACR_ChordDisjoint = ac_matrix_disjoint.
Proof. reflexivity. Qed.

Lemma arc_chord_fill_proper_cross_eq :
  arc_chord_fill ACR_ChordProperCross = ac_matrix_point_ii.
Proof. reflexivity. Qed.

Lemma arc_chord_fill_share_eq :
  arc_chord_fill ACR_ChordShare = ac_matrix_point_ii.
Proof. reflexivity. Qed.

Lemma arc_chord_fill_circle_cross_eq :
  arc_chord_fill ACR_CircleCross = ac_matrix_point_ii.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Classifier — mirrors S10 guards.                                           *)
(* -------------------------------------------------------------------------- *)

Definition classify_arc_chord (a : CircularArc) (P Q : Point)
    (r : ArcChordRegime) : Prop :=
  match r with
  | ACR_ChordDisjoint    => arc_chord_rejected a P Q
  | ACR_ChordProperCross => arc_chord_proper_cross a P Q
  | ACR_ChordShare       => arc_chord_share a P Q
  | ACR_CircleCross      => chord_crosses_arc_circle a P Q
  end.

Lemma chord_proper_cross_not_rejected :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_proper_cross a P Q ->
    ~ arc_chord_rejected a P Q.
Proof.
  intros a P Q Hcross Hrej.
  exact (arc_chord_proper_cross_not_rejected a P Q Hcross Hrej).
Qed.

Lemma chord_rejected_not_share :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_rejected a P Q ->
    ~ arc_chord_share a P Q.
Proof.
  intros a P Q Hrej Hshare.
  exact (arc_chord_rejected_not_share a P Q Hrej Hshare).
Qed.

Lemma chord_proper_cross_not_rejected_fill :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_proper_cross a P Q ->
    ~ classify_arc_chord a P Q ACR_ChordDisjoint.
Proof.
  intros a P Q Hcross H. unfold classify_arc_chord in H.
  exact (chord_proper_cross_not_rejected a P Q Hcross H).
Qed.

(* -------------------------------------------------------------------------- *)
(* Compute-path soundness.                                                    *)
(* -------------------------------------------------------------------------- *)

Theorem arc_fill_chord_disjoint_sound :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_rejected a P Q ->
    im_disjoint (arc_chord_fill ACR_ChordDisjoint).
Proof.
  intros a P Q Hrej.
  rewrite arc_chord_fill_disjoint_eq.
  exact (arc_chord_rejected_disjoint_sound a P Q Hrej).
Qed.

Theorem arc_fill_chord_proper_cross_sound :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_proper_cross a P Q ->
    im_crosses (arc_chord_fill ACR_ChordProperCross) /\
    im_intersects (arc_chord_fill ACR_ChordProperCross).
Proof.
  intros a P Q Hcross.
  rewrite arc_chord_fill_proper_cross_eq.
  exact (arc_chord_proper_cross_sound a P Q Hcross).
Qed.

Theorem arc_fill_chord_share_sound :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_share a P Q ->
    im_intersects (arc_chord_fill ACR_ChordShare).
Proof.
  intros a P Q Hshare.
  rewrite arc_chord_fill_share_eq.
  exact (arc_chord_share_intersects_sound a P Q Hshare).
Qed.

Theorem arc_fill_circle_cross_sound :
  forall (a : CircularArc) (P Q : Point),
    chord_crosses_arc_circle a P Q ->
    im_intersects (arc_chord_fill ACR_CircleCross).
Proof.
  intros a P Q Hcross.
  rewrite arc_chord_fill_circle_cross_eq.
  exact (arc_circle_chord_cross_intersects_sound a P Q Hcross).
Qed.

Theorem classify_chord_disjoint_fill_sound :
  forall (a : CircularArc) (P Q : Point),
    classify_arc_chord a P Q ACR_ChordDisjoint ->
    im_disjoint (arc_chord_fill ACR_ChordDisjoint).
Proof.
  intros a P Q H. unfold classify_arc_chord in H.
  exact (arc_fill_chord_disjoint_sound a P Q H).
Qed.

Theorem classify_chord_proper_cross_fill_sound :
  forall (a : CircularArc) (P Q : Point),
    classify_arc_chord a P Q ACR_ChordProperCross ->
    im_crosses (arc_chord_fill ACR_ChordProperCross) /\
    im_intersects (arc_chord_fill ACR_ChordProperCross).
Proof.
  intros a P Q H. unfold classify_arc_chord in H.
  exact (arc_fill_chord_proper_cross_sound a P Q H).
Qed.

Theorem classify_chord_share_fill_sound :
  forall (a : CircularArc) (P Q : Point),
    classify_arc_chord a P Q ACR_ChordShare ->
    im_intersects (arc_chord_fill ACR_ChordShare).
Proof.
  intros a P Q H. unfold classify_arc_chord in H.
  exact (arc_fill_chord_share_sound a P Q H).
Qed.

Theorem classify_circle_cross_fill_sound :
  forall (a : CircularArc) (P Q : Point),
    classify_arc_chord a P Q ACR_CircleCross ->
    im_intersects (arc_chord_fill ACR_CircleCross).
Proof.
  intros a P Q H. unfold classify_arc_chord in H.
  exact (arc_fill_circle_cross_sound a P Q H).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_fill_chord_disjoint_sound.
Print Assumptions arc_fill_chord_proper_cross_sound.
Print Assumptions arc_fill_chord_share_sound.
Print Assumptions arc_fill_circle_cross_sound.