(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixArcChord
   ----------------------------------------------------------------------------
   Issue #67 session 10 (S10): arc×line regime→witness selection — chord path.

   Regime-indexed `arc_chord_fill` that SELECTS (does not compute from
   geometry) one of the S10 witness matrices from `RelateArcChord.v` per
   `ArcChordRegime`.

   Delivers:

     - `ArcChordRegime` + `arc_chord_fill` (regime → witness matrix)
     - `classify_arc_chord` recording which S10 geometry guard names each regime
     - Fill = witness equalities
     - `*_fill_witness`: the selected witness satisfies the regime's predicate
       (constant facts; the regime hypothesis is NOT consumed)
     - Mutual-exclusion lemmas (genuine geometry) for chord rejection vs proper
       cross / share

   Honest scoping: chord path only; Option-A analytic regimes are S10b+.
   Proving a witness is a configuration's true DE-9IM is the deferred RelateNG
   step.

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
(* Witness facts: the selected witness satisfies the regime's predicate.      *)
(*                                                                            *)
(* Constant facts about `arc_chord_fill`; no geometry hypothesis, no          *)
(* geometry→matrix claim.  (`ACR_ChordShare` and `ACR_CircleCross` select the *)
(* same point witness as `ACR_ChordProperCross`; only `Intersects` is claimed *)
(* for them, not `Crosses`.)                                                  *)
(* -------------------------------------------------------------------------- *)

Theorem arc_fill_chord_disjoint_witness :
  im_disjoint (arc_chord_fill ACR_ChordDisjoint).
Proof.
  rewrite arc_chord_fill_disjoint_eq. exact ac_matrix_disjoint_witness.
Qed.

Theorem arc_fill_chord_proper_cross_witness :
  im_crosses (arc_chord_fill ACR_ChordProperCross) /\
  im_intersects (arc_chord_fill ACR_ChordProperCross).
Proof.
  rewrite arc_chord_fill_proper_cross_eq.
  split; [exact ac_matrix_point_ii_crosses | exact ac_matrix_point_ii_intersects].
Qed.

Theorem arc_fill_chord_share_witness :
  im_intersects (arc_chord_fill ACR_ChordShare).
Proof.
  rewrite arc_chord_fill_share_eq. exact ac_matrix_point_ii_intersects.
Qed.

Theorem arc_fill_circle_cross_witness :
  im_intersects (arc_chord_fill ACR_CircleCross).
Proof.
  rewrite arc_chord_fill_circle_cross_eq. exact ac_matrix_point_ii_intersects.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_fill_chord_disjoint_witness.
Print Assumptions arc_fill_chord_proper_cross_witness.
Print Assumptions arc_fill_chord_share_witness.
Print Assumptions arc_fill_circle_cross_witness.