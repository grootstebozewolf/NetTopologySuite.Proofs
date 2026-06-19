(* ============================================================================
   NetTopologySuite.Proofs.RelateBezier3
   ----------------------------------------------------------------------------
   Esri 300 Bezier3Curve (cubic Bezier) support (chord seed, following
   Clothoid S10b pattern).

   Minimal cubic Bezier relate carrier for the chord path: the curve is
   represented for relate purposes by the straight chord between its
   endpoints (start and end control points).  Controls affect shape but are
   not required for the chord-delegate regime work.

   Delivers (no geometry→matrix bridge):

     - `Bezier3Chord` + chord-as-segment regime predicates
     - Hand-specified witness matrices (S2 reuse) + lemmas
     - Genuine chord geometry consequences

   Honest scoping: chord only for now; full Bezier evaluation, intersection,
   and b64 are future.  Regime→witness via `RelateMatrixBezier3.v`.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted (Grok), human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance Segment Intersect RelateLineLine.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Minimal Bezier3 chord carrier (start–end).                                 *)
(* -------------------------------------------------------------------------- *)

Record Bezier3Chord : Type := mkBezier3Chord {
  b3c_start : Point;
  b3c_end   : Point
}.

Definition bezier3_chord_proper_cross (c : Bezier3Chord) (P Q : Point) : Prop :=
  segments_proper_cross (b3c_start c) (b3c_end c) P Q.

Definition bezier3_chord_rejected (c : Bezier3Chord) (P Q : Point) : Prop :=
  segments_rejected (b3c_start c) (b3c_end c) P Q.

Definition bezier3_chord_share (c : Bezier3Chord) (P Q : Point) : Prop :=
  segments_share (b3c_start c) (b3c_end c) P Q.

(* -------------------------------------------------------------------------- *)
(* Witness matrices (S2 reuse).                                               *)
(* -------------------------------------------------------------------------- *)

Definition b3c_matrix_disjoint : IntersectionMatrix := ll_matrix_disjoint.
Definition b3c_matrix_point_ii : IntersectionMatrix := ll_matrix_point_ii.

Lemma b3c_matrix_disjoint_witness :
  im_disjoint b3c_matrix_disjoint.
Proof.
  unfold b3c_matrix_disjoint. exact ll_matrix_disjoint_witness.
Qed.

Lemma b3c_matrix_point_ii_intersects :
  im_intersects b3c_matrix_point_ii.
Proof.
  unfold b3c_matrix_point_ii. exact ll_matrix_point_ii_intersects.
Qed.

Lemma b3c_matrix_point_ii_crosses :
  im_crosses b3c_matrix_point_ii.
Proof.
  unfold b3c_matrix_point_ii. exact ll_matrix_point_ii_crosses_ll.
Qed.

(* -------------------------------------------------------------------------- *)
(* Genuine chord geometry.                                                    *)
(* -------------------------------------------------------------------------- *)

Theorem bezier3_chord_proper_cross_share :
  forall (c : Bezier3Chord) (P Q : Point),
    bezier3_chord_proper_cross c P Q ->
    bezier3_chord_share c P Q.
Proof.
  intros c P Q H.
  unfold bezier3_chord_proper_cross, bezier3_chord_share in *.
  eapply line_line_proper_cross_geom; exact H.
Qed.

Lemma bezier3_chord_rejected_not_share :
  forall (c : Bezier3Chord) (P Q : Point),
    bezier3_chord_rejected c P Q ->
    ~ bezier3_chord_share c P Q.
Proof.
  intros c P Q Hrej Hshare.
  unfold bezier3_chord_rejected, bezier3_chord_share in *.
  exact (line_line_rejected_not_share (b3c_start c) (b3c_end c) P Q Hrej Hshare).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions bezier3_chord_proper_cross_share.
Print Assumptions bezier3_chord_rejected_not_share.
