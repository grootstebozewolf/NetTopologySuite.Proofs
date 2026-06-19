(* ============================================================================
   NetTopologySuite.Proofs.RelateEllipticArc
   ----------------------------------------------------------------------------
   Esri 300 EllipticArc support (chord seed, following Clothoid S10b pattern).

   Minimal elliptic arc relate carrier for the chord path (Option B style):
   the ellipse is represented for relate purposes by the straight chord between
   its endpoints.  This enables immediate DE-9IM chord-regime work while
   richer elliptic analytic predicates remain future work.

   Delivers (no geometry→matrix bridge — see the section comment):

     - `EllipticArcChord` + chord-as-segment regime predicates
     - Hand-specified witness matrices (S2 `ll_matrix_*` reuse) with their
       constant predicate lemmas
     - Genuine chord geometry: proper cross ⇒ shared point; rejection ⇒ no
       shared point

   Honest scoping: chord only; full elliptic-arc analytic, arc-arc, and b64
   mirrors are future slices.  Regime→witness selection via
   `RelateMatrixEllipticArc.v`.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted (Grok), human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance Segment Intersect RelateLineLine.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Minimal elliptic arc chord carrier.                                        *)
(* -------------------------------------------------------------------------- *)

Record EllipticArcChord : Type := mkEllipticArcChord {
  eac_start : Point;
  eac_end   : Point
}.

Definition elliptic_arc_chord_proper_cross (c : EllipticArcChord) (P Q : Point) : Prop :=
  segments_proper_cross (eac_start c) (eac_end c) P Q.

Definition elliptic_arc_chord_rejected (c : EllipticArcChord) (P Q : Point) : Prop :=
  segments_rejected (eac_start c) (eac_end c) P Q.

Definition elliptic_arc_chord_share (c : EllipticArcChord) (P Q : Point) : Prop :=
  segments_share (eac_start c) (eac_end c) P Q.

(* -------------------------------------------------------------------------- *)
(* Witness matrices (S2 reuse).                                               *)
(* -------------------------------------------------------------------------- *)

Definition eac_matrix_disjoint : IntersectionMatrix := ll_matrix_disjoint.
Definition eac_matrix_point_ii : IntersectionMatrix := ll_matrix_point_ii.

Lemma eac_matrix_disjoint_witness :
  im_disjoint eac_matrix_disjoint.
Proof.
  unfold eac_matrix_disjoint. exact ll_matrix_disjoint_witness.
Qed.

Lemma eac_matrix_point_ii_intersects :
  im_intersects eac_matrix_point_ii.
Proof.
  unfold eac_matrix_point_ii. exact ll_matrix_point_ii_intersects.
Qed.

Lemma eac_matrix_point_ii_crosses :
  im_crosses eac_matrix_point_ii.
Proof.
  unfold eac_matrix_point_ii. exact ll_matrix_point_ii_crosses_ll.
Qed.

(* -------------------------------------------------------------------------- *)
(* Genuine chord geometry (S2 delegate).                                      *)
(*                                                                            *)
(* The constant `eac_matrix_*` lemmas above prove the reused witnesses satisfy
   their predicates.  The lemmas here prove the genuine geometric consequence
   of a chord proper cross (a shared point); rejection's absence-of-share is
   `elliptic_arc_chord_rejected_not_share` below.  Neither is bridged to a
   witness matrix — that link is the deferred RelateNG step.                 *)
(* -------------------------------------------------------------------------- *)

Theorem elliptic_arc_chord_proper_cross_share :
  forall (c : EllipticArcChord) (P Q : Point),
    elliptic_arc_chord_proper_cross c P Q ->
    elliptic_arc_chord_share c P Q.
Proof.
  intros c P Q H.
  unfold elliptic_arc_chord_proper_cross, elliptic_arc_chord_share in *.
  eapply line_line_proper_cross_geom; exact H.
Qed.

Lemma elliptic_arc_chord_rejected_not_share :
  forall (c : EllipticArcChord) (P Q : Point),
    elliptic_arc_chord_rejected c P Q ->
    ~ elliptic_arc_chord_share c P Q.
Proof.
  intros c P Q Hrej Hshare.
  unfold elliptic_arc_chord_rejected, elliptic_arc_chord_share in *.
  exact (line_line_rejected_not_share (eac_start c) (eac_end c) P Q Hrej Hshare).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions elliptic_arc_chord_proper_cross_share.
Print Assumptions elliptic_arc_chord_rejected_not_share.
